//! M1 differential harness — the direct THIR lane's SHADOW verdicts against
//! the MIR lane's verdicts for the SAME bodies, both solved through the SAME
//! native trust-mc CHC entry (`docs/design/DIRECT-LANE-PROOF-AUTHORITY.md`,
//! milestone M1; Step 4 residual (b)).
//!
//! WHAT THIS IS AND IS NOT. Everything in this module is `#[cfg(test)]` by
//! construction (the `mod` declaration in `lib.rs` is gated `all(test, ...)`),
//! and every verdict it obtains is DIFFERENTIAL EVIDENCE:
//!
//! * `grants_proof_authority()` and `emits_native_verification_requests()`
//!   are untouched and false — no compiler call site exists for any of this;
//! * nothing here writes a verdict back into any module. That is not
//!   discipline, it is the types: the solve entry is
//!   `solve_bundle_native_proof_grade(&self, bundle: &NativeVerificationBundle)`
//!   — an immutable borrow (a write-back does not compile; measured E0596) —
//!   and the evidence rows it returns carry no module reference to mutate.
//!   The belt over the types is `shadow_solve_writes_nothing_back`, which
//!   pins the bundle digest AND the module's recomputed digest byte-identical
//!   across the solve and every row still `Pending`;
//! * the shadow bundle enters the trust-mc-driver RUNNER entry
//!   (`NativeTrustIrChcPdrRunner::solve_bundle_native_proof_grade`) — the
//!   same entry the MIR lane's bundles take inside `verifier_api.rs::
//!   native_trust_ir_chc_pdr_proof_transports_with_optional_source_authority`
//!   — NOT the `TrustMcVerifierApiAdapter` evidence path. The adapter path is
//!   structurally closed to shadow bundles today for named, deliberate
//!   reasons (the `trust-mc-native-admission-contract-v1` stamps the shadow
//!   planner honestly does not wear, and the absent public
//!   `TrustContractBundle` inventory; see the design doc's M1 section), and
//!   the shadow planner's own HARNESS CONFINEMENT note says a shadow bundle
//!   must only enter a verifier's DIAGNOSTIC path. The runner method is named
//!   "proof_grade" after its VALIDATION profile (full safety checks, no
//!   disabled obligations), not after what its output may be used for; this
//!   harness consumes that output as evidence only, which is exactly the
//!   in-band contract `DIRECT_SHADOW_WIRE_DISCLOSURE` states. The tension is
//!   stated here rather than resolved by relabelling.
//!
//! FIXTURES. `tests/fixtures/direct_shadow/` holds real production-driver
//! artifacts for one probe crate (`m1probe.rs`; commands and driver revision
//! in the README there): the direct lane's emitted module — born Pending
//! obligation rows, spans, sites and `target_info` all the finalizer's own
//! output, consumed exactly as emitted — and the MIR lane's
//! `VerifiableFunction` dumps of the same bodies. The MIR module is rebuilt
//! offline through the bridge's production lowering
//! (`lower_functions_to_trust_ir`) plus exactly the two enrichments
//! production performs upstream of the planner, each documented at its site
//! in [`mir_lane_bundle`].
//!
//! GAP 5 (whole-function verdict granularity) applies to everything below:
//! `trust_ir_function_to_chc_translation_output` translates the WHOLE
//! function per request, so the N per-obligation requests of one function are
//! N solves of the same whole-body error-reachability VC — one refutable
//! assert makes every sibling row of that function non-proved. The probe
//! fixture therefore keeps each expected verdict in its own function, and the
//! differential below compares per-obligation rows while knowing their
//! granularity is per-function.

use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;

use sha2::Digest as _;
use trust_ir::{
    Module, NativeVerificationBundle, ProofDigest, ProofId, ProofStatus, PublicObligationIdentity,
    SourceGenerationAuthority,
};

/// Per-request solve timeout. The whole battery is a handful of one-function
/// CHC solves over tiny acyclic bodies; existing native-bundle tests in
/// `verifier_api.rs` use the same order of magnitude.
const SOLVE_TIMEOUT: Duration = Duration::from_secs(10);

fn fixture_dir(probe: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/direct_shadow").join(probe)
}

/// The direct module EXACTLY as the production driver emitted it — the
/// checked-in binary artifact, decoded through the ratified codec. No
/// enrichment happens here.
fn load_direct_module(probe: &str) -> Module {
    let path = fixture_dir(probe).join("module.trust-ir.bin");
    let bytes = fs::read(&path)
        .unwrap_or_else(|error| panic!("read direct-module fixture {}: {error}", path.display()));
    trust_ir::binary::deserialize_module(&bytes)
        .unwrap_or_else(|error| panic!("decode direct-module fixture: {error:?}"))
}

/// The MIR lane's `VerifiableFunction` dumps with their raw bytes (the bytes
/// are the owner source-digest input), sorted by file name so `FuncId`
/// assignment is deterministic.
fn load_mir_functions(probe: &str) -> Vec<(Vec<u8>, trust_types::VerifiableFunction)> {
    let dir = fixture_dir(probe).join("mir");
    let mut paths: Vec<PathBuf> = fs::read_dir(&dir)
        .unwrap_or_else(|error| panic!("read MIR fixture dir {}: {error}", dir.display()))
        .map(|entry| entry.expect("fixture dir entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "json"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "no MIR fixtures found in {}", dir.display());
    paths
        .into_iter()
        .map(|path| {
            let bytes =
                fs::read(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
            let function: trust_types::VerifiableFunction = serde_json::from_slice(&bytes)
                .unwrap_or_else(|error| panic!("parse {}: {error}", path.display()));
            (bytes, function)
        })
        .collect()
}

/// Build the direct lane's SHADOW bundle from the checked-in artifact: the
/// Step 4 sibling planner, then the one typed exit that acknowledges the
/// unanchored lineage. The disclosure counts are asserted here so a fixture
/// regression (fewer born rows, a rangeless row) fails loudly at build time,
/// not as a silent shrink of the differential.
fn direct_shadow_bundle(probe: &str, expected_rows: usize) -> NativeVerificationBundle {
    let shadow =
        trust_ir_bridge::direct_shadow_verification_bundle_from_module(load_direct_module(probe))
            .expect("the real direct-lane artifact plans a shadow bundle");
    assert_eq!(
        shadow.disclosure.obligations_planned, expected_rows,
        "{probe} births {expected_rows} direct rows, all ranged, all requestable"
    );
    assert_eq!(shadow.disclosure.obligations_unrequestable_missing_range, 0);
    shadow.acknowledge_unanchored_lineage()
}

/// Build the MIR lane's bundle OFFLINE from the checked-in
/// `VerifiableFunction` dumps, through the bridge's own production lowering
/// and the byte-untouched MIR-compatibility planner.
///
/// Two enrichments stand between `lower_functions_to_trust_ir` output and
/// what the planner demands, and both are things PRODUCTION does upstream of
/// the planner (in `trust_verify.rs`), not shims invented here:
///
/// * `target_info` — the compiler stamps the session target onto the module;
///   the offline lowering has no session, so the harness copies the value the
///   SAME driver stamped into the direct artifact of the SAME compilation
///   (`aarch64-unknown-linux-gnu`, pointer size 8). Without it the runner
///   refuses ("proof-grade CHC translation requires an explicit 64-bit
///   target profile").
/// * per-row `PublicObligationIdentity` — production mints the public pair at
///   the `trust_verify.rs` obligation mint. The harness mints a test-local
///   pair per row: `obligation_id = "m1-mirlane:" + the row's own assertion
///   id` (already canonical-transport spelling) and `semantic_digest` = the
///   canonical trust-verifier-api recipe over the same minimal projection the
///   shadow planner uses, so neither lane's digest is a weaker fabrication
///   than the other's.
///
/// The owner list carries one SHA-256 per function over the exact dump bytes
/// the body was rebuilt from — a real, recomputable binding to the checked-in
/// MIR artifact (production binds to its `rust-mir.v1` body digest here; the
/// dump bytes are the offline stand-in and are what this harness can honestly
/// attest).
///
/// The bundle needs the `SourceGenerationAuthority` production mints at this
/// same seam (`trust_verify.rs::
/// mint_source_generation_authority_for_live_native_bundle`, invoked
/// immediately after the live bridge lowering): the MIR bridge emits
/// `Inst::Assume` nodes of its own (e.g. the post-assert success-path assume),
/// and the runner's proof-grade gate admits an Assume ONLY under an authority
/// minted for this exact in-process bundle — without it every Assume-bearing
/// MIR body is refused as an unauthenticated import. That mint is the same
/// in-process seam: the Assumes were emitted moments earlier by this process's
/// own bridge lowering, not read from bytes (the checked-in dump carries MIR,
/// and MIR has no Assume vocabulary — precedent:
/// `verifier_api.rs::root_adapter_threads_only_exact_source_authority_to_trust_mc`).
/// What the authority does NOT do: it licenses no verdict and mints no claim —
/// it is an admission key for the Assume gate, and the evidence produced over
/// this bundle stays differential evidence exactly like the shadow lane's.
/// The SHADOW lane, by contrast, deliberately never mints one (its planner's
/// HARNESS CONFINEMENT note), which is why the direct fixtures must carry no
/// Assume — and measured, they carry none.
///
/// The mint call itself lives in `tests::mir_lane_bundle_with_authority`, NOT
/// here: `verifier_api.rs::
/// root_source_authority_issuer_is_unique_and_legacy_marker_is_absent` is a
/// static census that the whole tree carries exactly ONE PRODUCTION issuer,
/// and it recognizes test code by the `#[cfg(test)] mod tests` marker — this
/// file's body is compiled only under `cfg(test)` (the lib.rs gate), but the
/// census reads source, so the issuer call must sit where the census can see
/// its test-ness.
fn mir_lane_bundle(probe: &str) -> NativeVerificationBundle {
    let functions = load_mir_functions(probe);
    let funcs: Vec<&trust_types::VerifiableFunction> =
        functions.iter().map(|(_, function)| function).collect();
    let mut module =
        trust_ir_bridge::lower_functions_to_trust_ir(probe, funcs).expect("MIR fixtures lower");

    module.target_info = load_direct_module(probe).target_info;
    assert!(
        module.target_info.as_ref().is_some_and(|target| target.pointer_size == 8),
        "the direct artifact carries the 64-bit target profile the runner demands"
    );

    // Public-identity enrichment, computed immutably first (the digest recipe
    // reads `module.files` while rows are borrowed), then installed.
    let minted: Vec<(ProofId, PublicObligationIdentity)> = module
        .proof_obligations
        .iter()
        .map(|obligation| {
            let source = obligation
                .source
                .as_ref()
                .unwrap_or_else(|| panic!("bridge row {:?} carries a source", obligation.id));
            let public_obligation_id = format!("m1-mirlane:{}", source.assertion_id);
            assert!(
                trust_ir::proof::is_canonical_public_obligation_id(&public_obligation_id),
                "minted public id must be canonical: {public_obligation_id:?}"
            );
            let location = source
                .range
                .as_ref()
                .map(|range| trust_verifier_api::SourceLocation {
                    file: module.files.get(range.file as usize).cloned(),
                    line: Some(range.start_line),
                    column: Some(range.start_col),
                    end_line: Some(range.end_line),
                    end_column: Some(range.end_col),
                })
                .unwrap_or_default();
            let projection = trust_verifier_api::TrustObligation {
                obligation_id: public_obligation_id.clone(),
                kind: match obligation.kind {
                    trust_ir::ObligationKind::ArithmeticSafety => {
                        trust_verifier_api::ObligationKind::ArithmeticSafety
                    }
                    trust_ir::ObligationKind::BoundsCheck => {
                        trust_verifier_api::ObligationKind::BoundsCheck
                    }
                    ref other => panic!(
                        "MIR fixture minted unexpected obligation kind {other:?}; extend the \
                         harness deliberately"
                    ),
                },
                contract_id: None,
                proof_item_id: None,
                source: location,
                description: obligation.description.clone(),
                required_strength: None,
                summary_facts: Vec::new(),
                metadata: Vec::new(),
            };
            let hex = projection
                .canonical_semantic_digest_sha256()
                .expect("canonical semantic digest for MIR-lane row");
            let mut digest = [0_u8; 32];
            for (index, pair) in hex.as_bytes().chunks_exact(2).enumerate() {
                let value = u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16)
                    .expect("canonical digest is hex");
                digest[index] = value;
            }
            (
                obligation.id,
                PublicObligationIdentity {
                    obligation_id: public_obligation_id,
                    semantic_digest: ProofDigest::sha256(digest),
                },
            )
        })
        .collect();
    for (id, public) in minted {
        let obligation = module
            .proof_obligations
            .iter_mut()
            .find(|obligation| obligation.id == id)
            .expect("row exists");
        obligation.source.as_mut().expect("checked above").public = Some(public);
    }

    // One owner per row-owning function, ascending FuncId (first = root), each
    // digest-bound to the exact dump bytes its body was rebuilt from.
    let mut owner_ids: Vec<trust_ir::FuncId> = module
        .proof_obligations
        .iter()
        .filter_map(|obligation| obligation.function)
        .collect();
    owner_ids.sort();
    owner_ids.dedup();
    let owners: Vec<trust_ir_bridge::NativeBundleOwner> = owner_ids
        .into_iter()
        .map(|function| {
            let name = &module.function_by_id(function).expect("owner resolves").name;
            let (bytes, _) = functions
                .iter()
                .find(|(_, candidate)| &candidate.name == name)
                .unwrap_or_else(|| panic!("no MIR dump bytes for owner {name}"));
            let digest: [u8; 32] = sha2::Sha256::digest(bytes).into();
            trust_ir_bridge::NativeBundleOwner { function, source_digest: ProofDigest::sha256(digest) }
        })
        .collect();

    trust_ir_bridge::native_verification_bundle_from_module_owners(module, &owners)
        .expect("the MIR-compatibility planner accepts the offline-rebuilt module")
}

fn runner() -> trust_mc_driver::NativeTrustIrChcPdrRunner {
    trust_mc_driver::NativeTrustIrChcPdrRunner::with_solve_options(
        trust_mc_core::ChcPdrSolveOptions::default()
            .with_engine(trust_mc_core::ChcPdrEngine::AdaptivePortfolio)
            .with_timeout(SOLVE_TIMEOUT),
    )
}

/// Solve the SHADOW bundle through the SAME trust-mc entry the MIR lane's
/// production adapter uses (`verifier_api.rs:2150` constructs exactly this
/// runner and calls exactly this method) — WITHOUT source-generation
/// authority, which the shadow lane never mints (by design; see the planner's
/// HARNESS CONFINEMENT note). Every fail-closed gate that keys on authority
/// therefore stays closed for this lane.
fn solve(bundle: &NativeVerificationBundle) -> trust_mc_driver::NativeTrustIrChcPdrBundleEvidence {
    runner()
        .solve_bundle_native_proof_grade(bundle)
        .expect("bundle solve runs (structural failures are harness defects)")
}

/// Solve the MIR-lane bundle with the authority its production path carries
/// (`verifier_api.rs:2160` — the `Some(authority)` arm of the same entry).
fn solve_with_authority(
    bundle: &NativeVerificationBundle,
    authority: &SourceGenerationAuthority,
) -> trust_mc_driver::NativeTrustIrChcPdrBundleEvidence {
    runner()
        .solve_bundle_native_proof_grade_with_source_authority(bundle, authority)
        .expect("bundle solve runs (structural failures are harness defects)")
}

/// The safety class of one obligation row — the third pairing axis (function
/// and LO position alone collide for signed division, where the div-by-zero
/// and MIN/-1 rows share one span; see Step 1 of the design doc).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum ObligationClass {
    Overflow,
    DivByZero,
    RemByZero,
    Bounds,
}

/// Cross-lane pairing key: (bare function name, class, LO line, LO col).
/// Both lanes derive LO from the same surface span — measured on the fixture:
/// direct `#L2C46` == MIR `start_line 2, start_col 46` — and the class axis
/// disambiguates the one shared-LO pair (`arith` L2C61: div-by-zero vs
/// MIN/-1 overflow). Uniqueness per lane is asserted at map build; a
/// collision fails the harness rather than silently merging rows.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ObligationKey {
    function: String,
    class: ObligationClass,
    line: u32,
    col: u32,
}

impl core::fmt::Display for ObligationKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}@L{}C{} {:?}", self.function, self.line, self.col, self.class)
    }
}

/// One lane's verdict for one obligation row, as delivered on the runner's
/// three typed channels. `RefutedWitnessed` is the bounded-unroll
/// machine-checked-witness channel; a refutation may equally arrive as
/// `NotProved` whose reason names the refutation (the acyclic-lane shape),
/// which is why [`refutation_stated`] accepts both.
#[derive(Debug, Clone, PartialEq, Eq)]
enum LaneVerdict {
    Proved,
    RefutedWitnessed,
    NotProved { reason: String },
}

impl LaneVerdict {
    fn proved(&self) -> bool {
        matches!(self, LaneVerdict::Proved)
    }
}

/// The transport-refusal reason the runner emits when the underlying CHC
/// solve produced a COUNTEREXAMPLE but no bounded-unroll machine-checked
/// witness: the proof-grade path refuses to seal a counterexample as proof,
/// and (deliberately — see the routing comment in `native.rs::
/// solve_bundle_native_proof_grade_inner`) a witnessless refutation rides the
/// `not_proved` channel, whose rows carry no typed solve outcome. This string
/// is therefore the wire form of "refutation stated" for acyclic bodies, and
/// it is pinned VERBATIM by the M1 battery: if trust-mc rewords it, the
/// refutation pin below fails and this classifier is updated consciously,
/// never silently.
const COUNTEREXAMPLE_NOT_A_PROOF: &str = "counterexample evidence is not a proof";

/// Does this verdict STATE a refutation (as opposed to mere inconclusiveness)?
/// Both delivery channels count: a machine-checked bounded-unroll witness on
/// `refuted`, or a stated counterexample on `not_proved`.
fn refutation_stated(verdict: &LaneVerdict) -> bool {
    match verdict {
        LaneVerdict::RefutedWitnessed => true,
        LaneVerdict::NotProved { reason } => {
            reason.contains("refuted") || reason.contains(COUNTEREXAMPLE_NOT_A_PROOF)
        }
        LaneVerdict::Proved => false,
    }
}

/// Parse a direct assertion id's `...#L{line}C{col}#{slug}#o{occ}` tail from
/// the END (a def-path may itself contain `#`, e.g. `{closure#0}`).
fn direct_class_and_occ(assertion_id: &str) -> (ObligationClass, u32) {
    let mut parts = assertion_id.rsplit('#');
    let occ = parts
        .next()
        .and_then(|part| part.strip_prefix('o'))
        .and_then(|part| part.parse::<u32>().ok())
        .unwrap_or_else(|| panic!("direct assertion id has no #o<occ> tail: {assertion_id}"));
    let slug = parts.next().unwrap_or_else(|| panic!("no slug in {assertion_id}"));
    let class = match slug {
        "overflow" | "overflow_neg" => ObligationClass::Overflow,
        "div_by_zero" => ObligationClass::DivByZero,
        "rem_by_zero" => ObligationClass::RemByZero,
        "bounds_check" => ObligationClass::Bounds,
        other => panic!("unmapped direct slug {other:?} in {assertion_id}; extend deliberately"),
    };
    (class, occ)
}

/// Classify a MIR-lane row by its bridge description. Fail-closed: an
/// unrecognized description is a harness-extension event, never a wildcard.
fn mir_class(description: &str) -> ObligationClass {
    if description.starts_with("overflow on ") {
        ObligationClass::Overflow
    } else if description == "division by zero" {
        ObligationClass::DivByZero
    } else if description == "remainder by zero" {
        ObligationClass::RemByZero
    } else if description == "array bounds check" {
        ObligationClass::Bounds
    } else {
        panic!("unmapped MIR-lane obligation description {description:?}; extend deliberately")
    }
}

/// Key every obligation row of a bundle's module, refusing collisions.
fn key_rows(
    bundle: &NativeVerificationBundle,
    class_of: impl Fn(&trust_ir::ProofObligation) -> ObligationClass,
) -> BTreeMap<ProofId, ObligationKey> {
    let mut keys = BTreeMap::new();
    let mut seen: BTreeMap<ObligationKey, ProofId> = BTreeMap::new();
    for obligation in &bundle.module.proof_obligations {
        let function = obligation.function.expect("every fixture row is function-scoped");
        let name = bundle
            .module
            .function_by_id(function)
            .expect("row owner resolves")
            .name
            .clone();
        let range = obligation
            .source
            .as_ref()
            .and_then(|source| source.range.as_ref())
            .expect("every fixture row is ranged");
        let key = ObligationKey {
            function: name,
            class: class_of(obligation),
            line: range.start_line,
            col: range.start_col,
        };
        if let Some(first) = seen.insert(key.clone(), obligation.id) {
            panic!(
                "pairing-key collision within one lane: {key} claimed by {first:?} and {:?}; \
                 the key needs an occurrence axis before this fixture is usable",
                obligation.id
            );
        }
        keys.insert(obligation.id, key);
    }
    keys
}

/// Key one lane's solved evidence for pairing. Every requested row must come
/// back on exactly one channel; a row on none (or two) is a harness defect and
/// fails here.
fn lane_verdicts(
    evidence: &trust_mc_driver::NativeTrustIrChcPdrBundleEvidence,
    keys: &BTreeMap<ProofId, ObligationKey>,
) -> BTreeMap<ObligationKey, LaneVerdict> {
    let mut verdicts: BTreeMap<ObligationKey, LaneVerdict> = BTreeMap::new();
    let mut record = |proof_ids: &[ProofId], verdict: LaneVerdict| {
        assert_eq!(
            proof_ids.len(),
            1,
            "both planners emit one obligation per trust-mc request; got {proof_ids:?}"
        );
        let key = keys
            .get(&proof_ids[0])
            .unwrap_or_else(|| panic!("verdict for unknown row {:?}", proof_ids[0]))
            .clone();
        if let Some(previous) = verdicts.insert(key.clone(), verdict.clone()) {
            panic!("row {key} came back on two channels: {previous:?} and {verdict:?}");
        }
    };
    for row in &evidence.obligations {
        record(&row.translated.obligations, LaneVerdict::Proved);
    }
    for row in &evidence.refuted {
        record(&row.translated.obligations, LaneVerdict::RefutedWitnessed);
    }
    for row in &evidence.not_proved {
        record(
            &row.translated.obligations,
            LaneVerdict::NotProved { reason: row.reason.clone() },
        );
    }
    verdicts
}

/// The differential's typed outcome: verdict disagreements over SHARED
/// obligations separated from per-lane coverage differences, every entry an
/// ENUMERATED statement, never a count or an average.
#[derive(Debug, Default)]
struct Differential {
    /// Both lanes state a verdict for the key and they differ on the one axis
    /// that matters (proved vs not-proved). Refutation delivery channel
    /// (witnessed vs stated-in-reason) is NOT a disagreement.
    disagreements: Vec<String>,
    /// Keys only the direct-shadow lane states a verdict on.
    only_direct: Vec<String>,
    /// Keys only the MIR lane states a verdict on.
    only_mir: Vec<String>,
}

/// The differential proper: for every key either lane states a verdict on,
/// compare. PROVED on one lane and non-proved on the other is a disagreement;
/// both-non-proved rows agree regardless of refutation delivery channel.
fn differential(
    direct: &BTreeMap<ObligationKey, LaneVerdict>,
    mir: &BTreeMap<ObligationKey, LaneVerdict>,
) -> Differential {
    let mut out = Differential::default();
    let keys: std::collections::BTreeSet<&ObligationKey> =
        direct.keys().chain(mir.keys()).collect();
    for key in keys {
        match (direct.get(key), mir.get(key)) {
            (Some(direct_verdict), Some(mir_verdict)) => {
                if direct_verdict.proved() != mir_verdict.proved() {
                    out.disagreements.push(format!(
                        "{key}: direct-shadow says {direct_verdict:?}, MIR lane says \
                         {mir_verdict:?}"
                    ));
                }
            }
            (Some(only), None) => {
                out.only_direct.push(format!("{key}: {only:?}"));
            }
            (None, Some(only)) => {
                out.only_mir.push(format!("{key}: {only:?}"));
            }
            (None, None) => unreachable!("key came from one of the maps"),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The harness's ONE `SourceGenerationAuthority` mint, deliberately inside
    /// `mod tests` so the tree-wide production-issuer census
    /// (`verifier_api.rs::
    /// root_source_authority_issuer_is_unique_and_legacy_marker_is_absent`)
    /// keeps counting exactly one production issuer. See `mir_lane_bundle`'s
    /// docs for why the mint is honest at this seam and what it does NOT
    /// license.
    fn mir_lane_bundle_with_authority(
        probe: &str,
    ) -> (NativeVerificationBundle, SourceGenerationAuthority) {
        let mut bundle = mir_lane_bundle(probe);
        let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle)
            .expect("the freshly planned in-process MIR-lane bundle mints authority");
        (bundle, authority)
    }

    fn direct_key_class(obligation: &trust_ir::ProofObligation) -> ObligationClass {
        let source = obligation.source.as_ref().expect("direct rows carry sources");
        let (class, occ) = direct_class_and_occ(&source.assertion_id);
        assert_eq!(occ, 0, "fixture has no repeated (slug,line,col); key needs occ if so");
        class
    }

    /// Solve one probe through both lanes and deliver keyed verdicts:
    /// (direct-shadow verdicts, MIR-lane verdicts).
    fn solved_probe(
        probe: &str,
        expected_rows: usize,
    ) -> (BTreeMap<ObligationKey, LaneVerdict>, BTreeMap<ObligationKey, LaneVerdict>) {
        let direct_bundle = direct_shadow_bundle(probe, expected_rows);
        let (mir_bundle, mir_authority) = mir_lane_bundle_with_authority(probe);
        let direct_keys = key_rows(&direct_bundle, direct_key_class);
        let mir_keys = key_rows(&mir_bundle, |obligation| mir_class(&obligation.description));
        let direct = lane_verdicts(&solve(&direct_bundle), &direct_keys);
        let mir = lane_verdicts(&solve_with_authority(&mir_bundle, &mir_authority), &mir_keys);
        (direct, mir)
    }

    fn expect(
        verdicts: &BTreeMap<ObligationKey, LaneVerdict>,
        lane: &str,
        function: &str,
        class: ObligationClass,
        line: u32,
        col: u32,
    ) -> LaneVerdict {
        let key =
            ObligationKey { function: function.to_string(), class, line, col };
        verdicts
            .get(&key)
            .unwrap_or_else(|| {
                panic!("{lane} lane states no verdict for {key}; stated: {verdicts:?}")
            })
            .clone()
    }

    /// THE M1 BATTERY (docs/design/DIRECT-LANE-PROOF-AUTHORITY.md, milestone
    /// M1): the direct THIR lane's shadow bundle SOLVES through the same
    /// native trust-mc CHC entry the MIR lane uses, per-obligation verdicts
    /// agree with the MIR lane's wherever both lanes state one, disagreements
    /// are enumerated (and asserted empty for these fixtures), and the lane
    /// demonstrably SOLVES rather than merely translating: a genuinely
    /// refutable obligation is refuted and a genuinely safe one is proved,
    /// through the shadow lane, with the expected verdict DIRECTION pinned
    /// per obligation. Prints the scorecard under `--nocapture`.
    #[test]
    fn m1_differential_scorecard_agrees_and_pins_both_verdict_directions() {
        let mut shadow_refutations_stated = 0usize;
        let mut shadow_proofs = 0usize;
        let mut solved: BTreeMap<
            &str,
            (BTreeMap<ObligationKey, LaneVerdict>, BTreeMap<ObligationKey, LaneVerdict>),
        > = BTreeMap::new();
        for (probe, rows) in [("m1probe", 8), ("m1shift", 1)] {
            let (direct, mir) = solved_probe(probe, rows);
            eprintln!(
                "=== M1 differential scorecard {probe} ({} direct rows, {} MIR rows) ===",
                direct.len(),
                mir.len()
            );
            for (key, verdict) in &direct {
                eprintln!("direct  {key}: {verdict:?}");
            }
            for (key, verdict) in &mir {
                eprintln!("mir     {key}: {verdict:?}");
            }

            // Mission point 4 — the differential. Disagreements and coverage
            // gaps are ENUMERATED; for these fixtures both lists must be
            // empty, and a failure prints every enumerated row.
            let differential = differential(&direct, &mir);
            assert!(
                differential.disagreements.is_empty(),
                "{probe}: per-obligation verdict disagreements between the lanes:\n{}",
                differential.disagreements.join("\n")
            );
            assert!(
                differential.only_direct.is_empty() && differential.only_mir.is_empty(),
                "{probe}: the fixture set is built for full cross-lane coverage, but rows \
                 paired to only one lane:\nonly direct-shadow: {:?}\nonly MIR: {:?}",
                differential.only_direct,
                differential.only_mir,
            );

            shadow_refutations_stated +=
                direct.values().filter(|verdict| refutation_stated(verdict)).count();
            shadow_proofs += direct.values().filter(|verdict| verdict.proved()).count();
            solved.insert(probe, (direct, mir));
        }

        // Mission point 5 — the M1 pin, DIRECTION BY DIRECTION on the shadow
        // lane, each against a named obligation of the checked-in probe:
        //
        //  * `remu(a, b) = a % b` — `b` is unconstrained, so rem-by-zero is
        //    GENUINELY refutable; the shadow lane must state the refutation
        //    (acyclic body, so it arrives as the pinned counterexample
        //    transport-refusal reason, not as a bounded-unroll witness);
        //  * `arith`'s `a / b` div-by-zero — same direction, second class;
        //  * `remu_safe(a, b) = a % (b | 1)` / `divu_safe(a, b) = a / (b | 1)`
        //    — the divisor is provably nonzero, and the shadow lane must
        //    PROVE it (sealed proof-grade transport, the `obligations`
        //    channel);
        //  * `sh_safe(a, k) = a << (k & 31)` — the masked shift is provably
        //    in range: the second probe's single row, proved.
        let (direct_probe, mir_probe) = &solved["m1probe"];
        for (function, class, line, col) in [
            ("remu", ObligationClass::RemByZero, 3, 37),
            ("arith", ObligationClass::DivByZero, 2, 61),
        ] {
            let verdict = expect(direct_probe, "direct-shadow", function, class, line, col);
            assert!(
                refutation_stated(&verdict),
                "M1 pin: the genuinely refutable {function}@L{line}C{col} {class:?} must be \
                 REFUTED through the shadow lane; got {verdict:?}"
            );
            // The oracle side of the differential is pinned too: the MIR lane
            // states the same refutation for the same obligation.
            let mir_verdict = expect(mir_probe, "MIR", function, class, line, col);
            assert!(refutation_stated(&mir_verdict), "MIR oracle drifted: {mir_verdict:?}");
        }
        for (function, class, line, col) in [
            ("remu_safe", ObligationClass::RemByZero, 4, 42),
            ("divu_safe", ObligationClass::DivByZero, 5, 42),
        ] {
            let verdict = expect(direct_probe, "direct-shadow", function, class, line, col);
            assert_eq!(
                verdict,
                LaneVerdict::Proved,
                "M1 pin: the genuinely safe {function}@L{line}C{col} {class:?} must be PROVED \
                 through the shadow lane"
            );
        }
        let (direct_shift, _) = &solved["m1shift"];
        assert_eq!(
            expect(direct_shift, "direct-shadow", "sh_safe", ObligationClass::Overflow, 2, 40),
            LaneVerdict::Proved,
            "M1 pin: the masked shift is provably in range and must be PROVED"
        );

        // Belt over the counters: at least one stated refutation and at least
        // one proof arrived through the shadow lane across the battery.
        assert!(shadow_refutations_stated >= 1, "no refutation was stated through the shadow lane");
        assert!(shadow_proofs >= 1, "no obligation was proved through the shadow lane");
        eprintln!(
            "M1 pin: shadow lane stated {shadow_refutations_stated} refutation(s) and proved \
             {shadow_proofs} obligation(s)"
        );
    }

    /// HARD BOUNDARY (mission): verdicts are EVIDENCE — nothing writes back
    /// into any module. The types already forbid it (`solve_bundle_native_
    /// proof_grade(&self, bundle: &NativeVerificationBundle)` takes an
    /// immutable borrow, and the evidence rows own their data with no module
    /// back-reference); this is the belt over the types: the bundle's stable
    /// digest is byte-identical across the solve, every obligation row is
    /// still `Pending`, and no certificate appeared anywhere.
    #[test]
    fn shadow_solve_writes_nothing_back() {
        let bundle = direct_shadow_bundle("m1probe", 8);
        let digest_before = bundle.stable_digest();
        // The bundle digest FRAMES the stored module digest rather than
        // recomputing it (measured: mutating a row's status moved neither),
        // so the module belt must be the module's own recomputed digest.
        let module_digest_before = bundle.module.stable_digest();
        let evidence = solve(&bundle);
        assert!(
            !evidence.obligations.is_empty(),
            "the belt must cover a solve that actually produced proof evidence"
        );
        assert_eq!(
            bundle.stable_digest(),
            digest_before,
            "solving must not change one byte of the bundle"
        );
        assert_eq!(
            bundle.module.stable_digest(),
            module_digest_before,
            "solving must not change one byte of the module the bundle carries"
        );
        assert!(
            bundle
                .module
                .proof_obligations
                .iter()
                .all(|obligation| obligation.status == ProofStatus::Pending),
            "every obligation row must still be Pending after the solve"
        );
        assert!(bundle.module.proof_certificates.is_empty(), "no certificate may be minted");
        assert!(bundle.evidence_bundles.is_empty(), "no evidence may be attached to the bundle");
    }

    /// NAMED BLOCKER, pinned so it can only move consciously: the bounds
    /// probe (`pick`/`pick_safe`, `m1bounds`) PLANS through the shadow
    /// planner — the direct lane births real BoundsCheck rows and the sibling
    /// requests them — but trust-mc's proof-grade admission gate refuses
    /// `Inst::ExtractElement` unconditionally (`native.rs`: "uses
    /// ExtractElement without an internally bound bounds derivation"), so
    /// NEITHER lane's array-index body can be solved through this entry
    /// today. This is the validator doing its job on a shape nobody has
    /// modeled yet, not a defect in the shadow planner; per the mission's
    /// boundary it is recorded, not shimmed. When trust-mc gains a bounds
    /// derivation for ExtractElement, this test fails and the probe joins the
    /// solved battery above.
    #[test]
    fn bounds_probe_is_refused_by_the_extract_element_gate_on_both_lanes() {
        let direct_bundle = direct_shadow_bundle("m1bounds", 2);
        let direct_refusal = runner()
            .solve_bundle_native_proof_grade(&direct_bundle)
            .expect_err("the ExtractElement gate refuses the direct bounds probe");
        let (mir_bundle, mir_authority) = mir_lane_bundle_with_authority("m1bounds");
        let mir_refusal = runner()
            .solve_bundle_native_proof_grade_with_source_authority(&mir_bundle, &mir_authority)
            .expect_err("the ExtractElement gate refuses the MIR bounds probe");
        for (lane, refusal) in [("direct-shadow", direct_refusal), ("MIR", mir_refusal)] {
            let text = refusal.to_string();
            assert!(
                text.contains("uses ExtractElement without an internally bound bounds derivation"),
                "{lane}: expected the ExtractElement admission refusal, got: {text}"
            );
        }
    }

    /// The shadow lane's authority asymmetry, pinned: the SHADOW bundle is
    /// solved with NO source-generation authority (the planner never mints
    /// one — HARNESS CONFINEMENT), which is only honest because the direct
    /// modules carry no `Inst::Assume` for the gate to admit. Measured here
    /// so a future direct-lane Assume shows up as a conscious decision about
    /// authority, not a silent solve failure.
    #[test]
    fn direct_fixtures_carry_no_assume_so_the_shadow_lane_needs_no_authority() {
        for probe in ["m1probe", "m1shift", "m1bounds"] {
            let module = load_direct_module(probe);
            for function in &module.functions {
                for (index, node) in function.instructions().enumerate() {
                    assert!(
                        !matches!(node.inst, trust_ir::Inst::Assume { .. }),
                        "{probe}: direct fn `{}` instruction {index} is an Assume; the shadow \
                         lane solves WITHOUT authority and would fail closed on it — decide \
                         the authority question deliberately before widening the fixture",
                        function.name
                    );
                }
            }
        }
    }
}
