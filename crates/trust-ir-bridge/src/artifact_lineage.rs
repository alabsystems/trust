//! Artifact-lineage attestation — the keystone that makes the digest A1 pins
//! and the artifact A6 flips be the SAME OBJECT (job L1 / A-LIN of
//! `clean/designs/2026-07-29-crystal-deployed-kernel-bridge.md` §3).
//!
//! # The defect this closes
//!
//! Three distinct objects exist in the trust-ir lane today, and **no digest
//! connects them**:
//!
//! 1. the per-body mini-`Module` + callee ledger `record_green` snapshots
//!    (`trust_thir_lower::flip_registry`) — what the flip consumes;
//! 2. the assembled crate-level artifact (`trust_thir_lower::crate_module`) —
//!    what a proof pins and what `R` reads. Assembly SORTS bodies, assigns new
//!    dense `FuncId`s, re-interns types, and rewrites callees, and registration
//!    even lifts the function out of the per-body module first;
//! 3. the `mir::Body` freshly re-derived at the flip
//!    (`rustc_mir_transform::trust_ir_flip`).
//!
//! So a theorem pinned against (2) and a flip event observed on (1)→(3) were
//! statements about *different artifacts*. The flip log carried only a `DefId`
//! and tallies: evidence that selection occurred, not that the **proved**
//! artifact was selected.
//!
//! # What this module provides
//!
//! A three-link digest chain, each link domain-separated and
//! length-prefix-framed so no concatenation can alias another:
//!
//! ```text
//!   BuildIdentity ──digest──┐
//!   Module::stable_digest ──┤
//!   callee ledger ──────────┴──> BodyLineage.body_digest        (object 1)
//!                                      │
//!            assembled FuncId + name + callee remap
//!                                      ▼
//!                                RemapCertificate.remap_digest  (1 ↦ 2)
//!                                      │
//!         all certificates, def_index-ordered, + assembled module digest
//!                                      ▼
//!                                CrateLineage.root_digest       (object 2)
//! ```
//!
//! At the flip, [`verify_flip_lineage`] recomputes `body_digest` from the module
//! actually taken from the registry and compares it to the recorded value. A
//! divergence in ANY component returns a typed error naming that component, and
//! the caller must decline the flip — so object (3) is provably derived from the
//! same bytes `body_digest` covers.
//!
//! # Determinism is the acceptance gate
//!
//! Two clean builds must reproduce every digest here. Therefore: no timestamps,
//! no paths outside the pinned identity, no hash-map iteration order, and no
//! floating-point. Every collection is a `BTreeMap`/sorted `Vec`, every render
//! has fixed key order, and [`CrateLineage::to_canonical_json`] is hand-rolled —
//! the same discipline `crate_module`'s coverage writer already states.
//!
//! # What this does NOT establish
//!
//! Stated plainly, because the surrounding program is precise about it: this
//! binds ARTIFACT IDENTITY. It does not prove the comparator, the trust-ir→MIR
//! shim, later MIR/LLVM/codegen/linking semantics, or any refinement. It removes
//! exactly one gap — "the proof and the flip concerned different objects" — and
//! nothing else.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: MIT OR Apache-2.0

use std::collections::BTreeMap;

use trust_ir::Module;
use trust_ir::proof::ProofDigest;

/// Domain tag for the build-identity digest.
const DOMAIN_IDENTITY: &str = "trust.lineage.identity.v1";
/// Domain tag for the callee-ledger digest.
const DOMAIN_CALLEES: &str = "trust.lineage.callees.v1";
/// Domain tag for the per-body lineage digest (object 1).
const DOMAIN_BODY: &str = "trust.lineage.body.v1";
/// Domain tag for the remapping certificate (object 1 ↦ object 2).
const DOMAIN_REMAP: &str = "trust.lineage.remap.v1";
/// Domain tag for the crate-level root digest (object 2).
const DOMAIN_ROOT: &str = "trust.lineage.root.v1";

/// Length-prefix-framed byte accumulator.
///
/// Every field is written as an 8-byte big-endian length followed by its bytes,
/// so no two distinct field sequences can produce the same material. Naive
/// concatenation would let `("ab", "c")` and `("a", "bc")` collide — which for a
/// digest whose whole job is artifact identity would be a silent aliasing hole.
#[derive(Default)]
struct Framed {
    bytes: Vec<u8>,
}

impl Framed {
    fn with_capacity(capacity: usize) -> Self {
        Self { bytes: Vec::with_capacity(capacity) }
    }

    fn str_field(&mut self, value: &str) -> &mut Self {
        self.raw(value.as_bytes())
    }

    fn display_field(&mut self, value: &impl std::fmt::Display) -> &mut Self {
        use std::fmt::Write;
        struct VecWriter<'a>(&'a mut Vec<u8>);
        impl std::fmt::Write for VecWriter<'_> {
            fn write_str(&mut self, s: &str) -> std::fmt::Result {
                self.0.extend_from_slice(s.as_bytes());
                Ok(())
            }
        }
        let header_pos = self.bytes.len();
        self.bytes.extend_from_slice(&[0u8; 8]);
        let start = self.bytes.len();
        let _ = write!(VecWriter(&mut self.bytes), "{value}");
        let len = u64::try_from(self.bytes.len() - start).unwrap_or(u64::MAX);
        self.bytes[header_pos..header_pos + 8].copy_from_slice(&len.to_be_bytes());
        self
    }

    fn u32_field(&mut self, value: u32) -> &mut Self {
        self.raw(&value.to_be_bytes())
    }

    fn bool_field(&mut self, value: bool) -> &mut Self {
        self.raw(&[u8::from(value)])
    }

    fn raw(&mut self, value: &[u8]) -> &mut Self {
        let len = u64::try_from(value.len()).unwrap_or(u64::MAX);
        self.bytes.extend_from_slice(&len.to_be_bytes());
        self.bytes.extend_from_slice(value);
        self
    }

    fn finish(&self, domain: &str) -> ProofDigest {
        ProofDigest::sha256_domain(domain, &self.bytes)
    }
}

/// The build configuration a lineage digest is bound to.
///
/// A1 requires the pinned artifact to name its configuration, and §2.1 of the
/// crystal design is why that is mandatory rather than hygiene: `infer_type` is
/// literally two programs (`debug_assertions` splits it), so a digest that did
/// not carry the configuration could hash one program and be cited for the
/// other. `debuginfo` is here for a second, independent reason: the flip only
/// fires at `-Cdebuginfo=0`, so a lineage record from a debuginfo build can
/// never legitimately match a flip event.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
// NOT `#[non_exhaustive]`: the producer of these values is ANOTHER CRATE
// (`trust-thir-lower`, at `record_green` / `record` / `assemble`), and a
// cross-crate struct literal on a `#[non_exhaustive]` type is error[E0639].
// The in-crate tests cannot catch that — they are inside the defining crate,
// where the attribute has no effect. Adding a field here is therefore a
// deliberate breaking change to the consumer, which for an attestation type
// is the RIGHT default: a silently-ignored new identity field would weaken
// the digest without any call site failing.
pub struct BuildIdentity {
    /// Compiler version string including its commit hash.
    pub compiler: String,
    /// The crate being compiled.
    pub crate_name: String,
    /// Target triple.
    pub target: String,
    /// Optimization level, as the session reports it.
    pub opt_level: String,
    /// Debug-info level. The flip requires `None`; see the type docs.
    pub debuginfo: String,
    /// Panic strategy.
    pub panic_strategy: String,
    /// Whether coverage instrumentation is on (the flip refuses it).
    pub instrument_coverage: bool,
    /// `--cfg` values, SORTED by the constructor.
    pub cfgs: Vec<String>,
    /// Enabled crate features, SORTED by the constructor.
    pub features: Vec<String>,
}

impl BuildIdentity {
    /// Canonicalize: sort the multi-valued fields so two sessions that computed
    /// them in different orders still agree.
    #[must_use]
    pub fn canonicalized(mut self) -> Self {
        self.cfgs.sort_unstable();
        self.cfgs.dedup();
        self.features.sort_unstable();
        self.features.dedup();
        self
    }

    /// The identity digest. Field order is fixed and every field is framed.
    #[must_use]
    pub fn digest(&self) -> ProofDigest {
        thread_local! {
            static LAST_IDENTITY_DIGEST: std::cell::RefCell<Option<(BuildIdentity, ProofDigest)>> =
                const { std::cell::RefCell::new(None) };
        }
        LAST_IDENTITY_DIGEST.with(|slot| {
            if let Some((cached_id, cached_digest)) = slot.borrow().as_ref()
                && cached_id == self
            {
                return cached_digest.clone();
            }
            let computed = self.compute_digest();
            *slot.borrow_mut() = Some((self.clone(), computed.clone()));
            computed
        })
    }

    fn compute_digest(&self) -> ProofDigest {
        let approx_bytes = 96
            + self.compiler.len()
            + self.crate_name.len()
            + self.target.len()
            + self.opt_level.len()
            + self.debuginfo.len()
            + self.panic_strategy.len()
            + self.cfgs.iter().map(|c| 8 + c.len()).sum::<usize>()
            + self.features.iter().map(|feat| 8 + feat.len()).sum::<usize>();
        let mut f = Framed::with_capacity(approx_bytes);
        f.str_field(&self.compiler)
            .str_field(&self.crate_name)
            .str_field(&self.target)
            .str_field(&self.opt_level)
            .str_field(&self.debuginfo)
            .str_field(&self.panic_strategy)
            .bool_field(self.instrument_coverage)
            .u32_field(u32::try_from(self.cfgs.len()).unwrap_or(u32::MAX));
        for cfg in &self.cfgs {
            f.str_field(cfg);
        }
        f.u32_field(u32::try_from(self.features.len()).unwrap_or(u32::MAX));
        for feature in &self.features {
            f.str_field(feature);
        }
        f.finish(DOMAIN_IDENTITY)
    }
}

/// The lineage-relevant projection of one `trust_thir_lower::CalleeRef`.
///
/// A pure mirror: `CalleeRef` carries `rustc_span::def_id::DefId` values, which
/// cannot appear in this crate. `def_krate` + `def_index` reconstruct the full
/// `DefId` identity that `def_index` alone loses for a cross-crate callee, and
/// `force_havoc` is included because it CHANGES what assembly links (a forced
/// havoc becomes a bodyless declaration even when a clean local body exists) —
/// omitting it would let two materially different assemblies share a digest.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
// NOT `#[non_exhaustive]`: the producer of these values is ANOTHER CRATE
// (`trust-thir-lower`, at `record_green` / `record` / `assemble`), and a
// cross-crate struct literal on a `#[non_exhaustive]` type is error[E0639].
// The in-crate tests cannot catch that — they are inside the defining crate,
// where the attribute has no effect. Adding a field here is therefore a
// deliberate breaking change to the consumer, which for an attestation type
// is the RIGHT default: a silently-ignored new identity field would weaken
// the digest without any call site failing.
pub struct CalleeIdentity {
    /// The `FuncId` exactly as emitted into `Inst::Call { callee }`.
    pub func_id: u32,
    /// Whether the callee is in the crate being compiled.
    pub is_local: bool,
    /// The callee's `DefIndex`.
    pub def_index: u32,
    /// The callee `DefId`'s crate number — without it a cross-crate identity is
    /// ambiguous.
    pub def_krate: u32,
    /// `tcx.def_path_str` of the callee.
    pub def_path: String,
    /// Forced to a bodyless havoc declaration at assembly.
    pub force_havoc: bool,
}

impl CalleeIdentity {
    fn frame(&self, f: &mut Framed) {
        f.u32_field(self.func_id)
            .bool_field(self.is_local)
            .u32_field(self.def_index)
            .u32_field(self.def_krate)
            .str_field(&self.def_path)
            .bool_field(self.force_havoc);
    }
}

/// Digest of a callee ledger.
///
/// The ledger is digested in the caller's EMISSION order, not sorted.
///
/// **Corrected rationale.** An earlier version of this comment said the order is
/// load-bearing because `func_id` is positional at emission. That is FALSE:
/// `func_id` is `DefIndex`-derived (`trust-thir-lower/src/lib.rs:1692`,
/// `FuncId::new(def_id.index.as_u32())`) and `to_mir` resolves a ledgered
/// `FuncId` with a position-INDEPENDENT filter (`to_mir.rs:3290`, stated at
/// `:3286`). So a reordering is *not* semantically different.
///
/// Emission order is nonetheless the right thing to digest, for a fail-closed
/// reason rather than a semantic one: digesting the sequence as given makes a
/// reorder OVER-key, i.e. the flip-time re-check misses and the body falls back
/// to built MIR. Sorting first would make the digest blind to a reordering that
/// *did* turn out to matter. Over-keying costs a fallback; under-keying would
/// cost a false accept, and only one of those is acceptable here.
///
/// Note also that `CalleeIdentity.func_id` and `.def_index` are provably always
/// equal (`lib.rs:1692` vs `:1726`, enforced at `to_mir.rs:3297-3301`), so this
/// frames the same `u32` twice. Harmless, but they are not independent identity
/// components and must not be counted as two.
#[must_use]
pub fn callee_ledger_digest(callees: &[CalleeIdentity]) -> ProofDigest {
    let mut f = Framed::with_capacity(12 + callees.len().saturating_mul(96));
    f.u32_field(u32::try_from(callees.len()).unwrap_or(u32::MAX));
    for callee in callees {
        callee.frame(&mut f);
    }
    f.finish(DOMAIN_CALLEES)
}

/// Attestation for ONE green body, computed where the body is recorded.
///
/// This is object (1) of the module docs: exactly the bytes the flip will later
/// consume, bound to the configuration that produced them.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct BodyLineage {
    /// `DefIndex` of the body — the registry key and the sort key.
    pub def_index: u32,
    /// `tcx.def_path_str` of the body.
    pub def_path: String,
    /// `Module::stable_digest()` of the per-body module.
    pub module_digest: ProofDigest,
    /// Digest of the callee-identity ledger.
    pub callee_digest: ProofDigest,
    /// Digest of the build configuration.
    pub identity_digest: ProofDigest,
    /// The composite binding all of the above — the value the flip event must
    /// carry and re-verify.
    pub body_digest: ProofDigest,
}

impl BodyLineage {
    /// Compute the attestation for a green body.
    #[must_use]
    pub fn compute(
        def_index: u32,
        def_path: &str,
        module: &Module,
        callees: &[CalleeIdentity],
        identity: &BuildIdentity,
    ) -> Self {
        let module_digest = module.stable_digest();
        let callee_digest = callee_ledger_digest(callees);
        let identity_digest = identity.digest();
        let body_digest =
            Self::bind(def_index, def_path, &module_digest, &callee_digest, &identity_digest);
        Self {
            def_index,
            def_path: def_path.to_string(),
            module_digest,
            callee_digest,
            identity_digest,
            body_digest,
        }
    }

    fn bind(
        def_index: u32,
        def_path: &str,
        module_digest: &ProofDigest,
        callee_digest: &ProofDigest,
        identity_digest: &ProofDigest,
    ) -> ProofDigest {
        let mut f = Framed::with_capacity(264 + def_path.len());
        f.u32_field(def_index)
            .str_field(def_path)
            .display_field(module_digest)
            .display_field(callee_digest)
            .display_field(identity_digest);
        f.finish(DOMAIN_BODY)
    }
}

/// One callee edge as ASSEMBLY resolved it: the per-body ledger identity and the
/// `FuncId` it became in the assembled module.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
// NOT `#[non_exhaustive]`: the producer of these values is ANOTHER CRATE
// (`trust-thir-lower`, at `record_green` / `record` / `assemble`), and a
// cross-crate struct literal on a `#[non_exhaustive]` type is error[E0639].
// The in-crate tests cannot catch that — they are inside the defining crate,
// where the attribute has no effect. Adding a field here is therefore a
// deliberate breaking change to the consumer, which for an attestation type
// is the RIGHT default: a silently-ignored new identity field would weaken
// the digest without any call site failing.
pub struct CalleeRemap {
    /// The per-body `FuncId` the instruction stream carried.
    pub body_func_id: u32,
    /// The `FuncId` in the assembled module — a defined function's dense pass-1
    /// id, or the id of the fail-closed bodyless declaration.
    pub assembled_func_id: u32,
    /// The callee's `def_path`, so the row is legible without the module.
    pub def_path: String,
    /// Whether assembly resolved this edge to a DEFINED body (`true`) or
    /// fail-closed it to a bodyless declaration (`false`).
    pub resolved_to_body: bool,
}

/// Certifies the canonical remapping of one per-body module into the assembled
/// crate artifact — the (1) ↦ (2) link.
///
/// Assembly sorts bodies, assigns dense `FuncId`s, re-interns types and rewrites
/// callees. Without this certificate, "the assembled artifact contains the body
/// I digested" is an assumption. With it, the remapping is recorded content and
/// a changed mapping changes the digest.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct RemapCertificate {
    /// The per-body attestation this certificate remaps.
    pub body: BodyLineage,
    /// The `FuncId` this body received in the assembled module.
    pub assembled_func_id: u32,
    /// The name it was renamed to (its `def_path_str`, unique within the crate).
    pub assembled_name: String,
    /// Every callee edge's resolution, SORTED by `body_func_id` — the map is a
    /// set of edges, so its digest must not depend on discovery order.
    pub callee_remap: Vec<CalleeRemap>,
    /// The certificate digest.
    pub remap_digest: ProofDigest,
}

impl RemapCertificate {
    /// Build a certificate. `callee_remap` is sorted here, so callers need not
    /// pre-sort and cannot accidentally make the digest order-dependent.
    #[must_use]
    pub fn new(
        body: BodyLineage,
        assembled_func_id: u32,
        assembled_name: &str,
        mut callee_remap: Vec<CalleeRemap>,
    ) -> Self {
        callee_remap.sort();
        let mut f = Framed::with_capacity(
            128 + assembled_name.len() + callee_remap.len().saturating_mul(72),
        );
        f.display_field(&body.body_digest)
            .u32_field(assembled_func_id)
            .str_field(assembled_name)
            .u32_field(u32::try_from(callee_remap.len()).unwrap_or(u32::MAX));
        for row in &callee_remap {
            f.u32_field(row.body_func_id)
                .u32_field(row.assembled_func_id)
                .str_field(&row.def_path)
                .bool_field(row.resolved_to_body);
        }
        let remap_digest = f.finish(DOMAIN_REMAP);
        Self {
            body,
            assembled_func_id,
            assembled_name: assembled_name.to_string(),
            callee_remap,
            remap_digest,
        }
    }
}

/// The crate-level lineage ledger — object (2), and what A1 pins.
///
/// `root_digest` binds the build identity, every per-body certificate in
/// `def_index` order, and the assembled module's own `stable_digest`. A proof
/// citing `root_digest` and a flip event carrying a `body_digest` that appears
/// in it are provably about the same artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct CrateLineage {
    /// The build configuration every certificate is bound to.
    pub identity: BuildIdentity,
    /// Certificates by `def_index` — a `BTreeMap`, so iteration is sorted and
    /// the root digest cannot depend on insertion order.
    pub certificates: BTreeMap<u32, RemapCertificate>,
    /// `Module::stable_digest()` of the ASSEMBLED module.
    pub assembled_module_digest: ProofDigest,
    /// The root digest.
    pub root_digest: ProofDigest,
}

impl CrateLineage {
    /// Assemble the crate-level ledger from per-body certificates.
    #[must_use]
    pub fn new(
        identity: BuildIdentity,
        certificates: BTreeMap<u32, RemapCertificate>,
        assembled: &Module,
    ) -> Self {
        let assembled_module_digest = assembled.stable_digest();
        let identity_digest = identity.digest();
        let mut f = Framed::with_capacity(192 + certificates.len().saturating_mul(92));
        f.display_field(&identity_digest)
            .display_field(&assembled_module_digest)
            .u32_field(u32::try_from(certificates.len()).unwrap_or(u32::MAX));
        for (def_index, cert) in &certificates {
            f.u32_field(*def_index).display_field(&cert.remap_digest);
        }
        let root_digest = f.finish(DOMAIN_ROOT);
        Self { identity, certificates, assembled_module_digest, root_digest }
    }

    /// Look up the certificate a flip event's body belongs to.
    #[must_use]
    pub fn certificate_for(&self, def_index: u32) -> Option<&RemapCertificate> {
        self.certificates.get(&def_index)
    }

    /// Deterministic sidecar rendering: fixed key order, sorted rows, no
    /// timestamps — two clean builds produce byte-identical output.
    #[must_use]
    pub fn to_canonical_json(&self) -> String {
        use std::fmt::Write;
        let mut out = String::with_capacity(512 + self.certificates.len().saturating_mul(256));
        out.push_str("{\n  \"schema\": \"trust.artifact-lineage.v1\",\n");
        let _ = writeln!(out, "  \"root_digest\": \"{}\",", self.root_digest);
        let _ = writeln!(
            out,
            "  \"assembled_module_digest\": \"{}\",",
            self.assembled_module_digest
        );
        let _ = writeln!(out, "  \"identity_digest\": \"{}\",", self.identity.digest());
        out.push_str("  \"identity\": {\n    \"compiler\": ");
        write_json_str(&mut out, &self.identity.compiler);
        out.push_str(",\n    \"crate_name\": ");
        write_json_str(&mut out, &self.identity.crate_name);
        out.push_str(",\n    \"target\": ");
        write_json_str(&mut out, &self.identity.target);
        out.push_str(",\n    \"opt_level\": ");
        write_json_str(&mut out, &self.identity.opt_level);
        out.push_str(",\n    \"debuginfo\": ");
        write_json_str(&mut out, &self.identity.debuginfo);
        out.push_str(",\n    \"panic_strategy\": ");
        write_json_str(&mut out, &self.identity.panic_strategy);
        let _ = writeln!(
            out,
            ",\n    \"instrument_coverage\": {},",
            self.identity.instrument_coverage
        );
        out.push_str("    \"cfgs\": ");
        write_json_str_array(&mut out, &self.identity.cfgs);
        out.push_str(",\n    \"features\": ");
        write_json_str_array(&mut out, &self.identity.features);
        out.push_str("\n  },\n  \"bodies\": [\n");
        let mut first = true;
        for (def_index, cert) in &self.certificates {
            if !first {
                out.push_str(",\n");
            }
            first = false;
            let _ = write!(out, "    {{\"def_index\": {def_index}, \"def_path\": ");
            write_json_str(&mut out, &cert.body.def_path);
            let _ = write!(out, ", \"assembled_func_id\": {}, \"assembled_name\": ", cert.assembled_func_id);
            write_json_str(&mut out, &cert.assembled_name);
            let _ = write!(
                out,
                ", \"module_digest\": \"{}\", \"callee_digest\": \"{}\", \
                 \"body_digest\": \"{}\", \"remap_digest\": \"{}\", \"callees\": [",
                cert.body.module_digest,
                cert.body.callee_digest,
                cert.body.body_digest,
                cert.remap_digest
            );
            let mut first_callee = true;
            for row in &cert.callee_remap {
                if !first_callee {
                    out.push_str(", ");
                }
                first_callee = false;
                let _ = write!(
                    out,
                    "{{\"body_func_id\": {}, \"assembled_func_id\": {}, \"def_path\": ",
                    row.body_func_id, row.assembled_func_id
                );
                write_json_str(&mut out, &row.def_path);
                let _ = write!(out, ", \"resolved_to_body\": {}}}", row.resolved_to_body);
            }
            out.push_str("]}");
        }
        out.push_str("\n  ]\n}\n");
        out
    }
}

/// Why a flip-time lineage verification failed. Every variant means the same
/// operational thing: **do not flip**.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum LineageError {
    /// The module taken from the registry is not the one that was digested.
    #[error(
        "trust-ir lineage: module digest mismatch for `{def_path}` (def index {def_index}): \
         recorded {recorded}, recomputed {actual}"
    )]
    ModuleDigestMismatch {
        /// The body's def index.
        def_index: u32,
        /// The body's def path.
        def_path: String,
        /// Digest recorded at `record_green`.
        recorded: String,
        /// Digest recomputed at the flip.
        actual: String,
    },
    /// The callee ledger changed between recording and the flip.
    #[error(
        "trust-ir lineage: callee ledger digest mismatch for `{def_path}` (def index \
         {def_index}): recorded {recorded}, recomputed {actual}"
    )]
    CalleeDigestMismatch {
        /// The body's def index.
        def_index: u32,
        /// The body's def path.
        def_path: String,
        /// Digest recorded at `record_green`.
        recorded: String,
        /// Digest recomputed at the flip.
        actual: String,
    },
    /// The build configuration at the flip differs from the recorded one.
    #[error(
        "trust-ir lineage: build identity mismatch for `{def_path}` (def index {def_index}): \
         recorded {recorded}, recomputed {actual}"
    )]
    IdentityMismatch {
        /// The body's def index.
        def_index: u32,
        /// The body's def path.
        def_path: String,
        /// Digest recorded at `record_green`.
        recorded: String,
        /// Digest recomputed at the flip.
        actual: String,
    },
    /// The composite disagrees although every component matched — a binding
    /// bug, not a content change. Kept as its own variant so it can never be
    /// mistaken for an ordinary perturbation.
    #[error(
        "trust-ir lineage: composite body digest mismatch for `{def_path}` (def index \
         {def_index}) although all components agreed: recorded {recorded}, recomputed {actual}"
    )]
    BodyDigestMismatch {
        /// The body's def index.
        def_index: u32,
        /// The body's def path.
        def_path: String,
        /// Digest recorded at `record_green`.
        recorded: String,
        /// Digest recomputed at the flip.
        actual: String,
    },
    /// The def index the flip is verifying is not the one recorded.
    #[error("trust-ir lineage: def index mismatch — recorded {recorded}, flipping {actual}")]
    DefIndexMismatch {
        /// Def index recorded at `record_green`.
        recorded: u32,
        /// Def index presented at the flip.
        actual: u32,
    },
    /// The flip event's body does not appear in the crate lineage ledger, so no
    /// pinned artifact covers it.
    #[error(
        "trust-ir lineage: no remap certificate for def index {def_index} — the flipped body \
         is not covered by the pinned crate artifact"
    )]
    MissingCertificate {
        /// The body's def index.
        def_index: u32,
    },
}

/// Re-verify a recorded attestation against the module actually taken at the
/// flip. **Fail-closed**: any `Err` means the caller must keep built MIR.
///
/// Components are checked before the composite so the error names the object
/// that actually changed rather than only reporting that something did.
pub fn verify_flip_lineage(
    recorded: &BodyLineage,
    def_index: u32,
    module_at_flip: &Module,
    callees_at_flip: &[CalleeIdentity],
    identity_at_flip: &BuildIdentity,
) -> Result<ProofDigest, LineageError> {
    if recorded.def_index != def_index {
        return Err(LineageError::DefIndexMismatch {
            recorded: recorded.def_index,
            actual: def_index,
        });
    }
    let module_digest = module_at_flip.stable_digest();
    if module_digest != recorded.module_digest {
        return Err(LineageError::ModuleDigestMismatch {
            def_index,
            def_path: recorded.def_path.clone(),
            recorded: recorded.module_digest.to_string(),
            actual: module_digest.to_string(),
        });
    }
    let callee_digest = callee_ledger_digest(callees_at_flip);
    if callee_digest != recorded.callee_digest {
        return Err(LineageError::CalleeDigestMismatch {
            def_index,
            def_path: recorded.def_path.clone(),
            recorded: recorded.callee_digest.to_string(),
            actual: callee_digest.to_string(),
        });
    }
    let identity_digest = identity_at_flip.digest();
    if identity_digest != recorded.identity_digest {
        return Err(LineageError::IdentityMismatch {
            def_index,
            def_path: recorded.def_path.clone(),
            recorded: recorded.identity_digest.to_string(),
            actual: identity_digest.to_string(),
        });
    }
    let body_digest = BodyLineage::bind(
        def_index,
        &recorded.def_path,
        &module_digest,
        &callee_digest,
        &identity_digest,
    );
    if body_digest != recorded.body_digest {
        return Err(LineageError::BodyDigestMismatch {
            def_index,
            def_path: recorded.def_path.clone(),
            recorded: recorded.body_digest.to_string(),
            actual: body_digest.to_string(),
        });
    }
    Ok(body_digest)
}

/// Confirm the flipped body is covered by the pinned crate artifact: the
/// certificate must exist AND carry the same `body_digest` the flip verified.
///
/// This is the check that makes A1's hash and A6's flip the same object. Without
/// it, a body could verify against its own recording while being absent from —
/// or differently mapped in — the artifact a proof actually pinned.
pub fn verify_covered_by_artifact(
    lineage: &CrateLineage,
    def_index: u32,
    verified_body_digest: &ProofDigest,
) -> Result<(), LineageError> {
    let cert =
        lineage.certificate_for(def_index).ok_or(LineageError::MissingCertificate { def_index })?;
    if &cert.body.body_digest != verified_body_digest {
        return Err(LineageError::BodyDigestMismatch {
            def_index,
            def_path: cert.body.def_path.clone(),
            recorded: cert.body.body_digest.to_string(),
            actual: verified_body_digest.to_string(),
        });
    }
    Ok(())
}

fn write_json_str(out: &mut String, value: &str) {
    use std::fmt::Write;
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

fn write_json_str_array(out: &mut String, values: &[String]) {
    out.push('[');
    let mut first = true;
    for value in values {
        if !first {
            out.push_str(", ");
        }
        first = false;
        write_json_str(out, value);
    }
    out.push(']');
}

#[cfg(test)]
#[path = "artifact_lineage_tests.rs"]
mod tests;
