//! Direct-lane obligation birth (Step 2) and the tier-aware authority
//! inventory (Step 3) — the PURE half, deliberately rustc-free.
//!
//! Design of record: `docs/design/DIRECT-LANE-PROOF-AUTHORITY.md` (Step 2/3),
//! executed under the owner directive of 2026-08-30 ("execute step two") on
//! the `structural-parity-only-v1 -> obligation-bearing-pending-v2` rung of
//! the ladder in `docs/design/2026-08-27-two-language-direct-to-trust-ir.md`.
//!
//! WHAT A ROW IS. Every obligation this module installs is a CLAIM, never a
//! verdict: `ProofStatus::Pending`, no formula, no certificate, and no
//! `PublicObligationIdentity` — the frontend precedent's reason verbatim
//! ("no PublicObligationIdentity — that demands a real semantic digest, and
//! there is nothing here to digest it from",
//! `first-party/trust-ir/frontend/src/mir_lower.rs`). The public `vc:` pair
//! is minted only when a tier whose `emits_native_verification_requests()`
//! is true exists (Step 4/6), with the CANONICAL trust-verifier-api digest
//! recipe, so no recompute-and-compare consumer can ever be handed a
//! non-canonical digest by this lane.
//!
//! IDENTITY (source-shape, bound at EMISSION — Step 1's lesson: structural,
//! never re-derived by matching afterwards):
//!
//! ```text
//! source_id    trust-thir-lower/direct-assert@1
//! assertion_id {crate}::{def_path}#L{line}C{col}#{slug}#o{occ}
//! ```
//!
//! * `{crate}::{def_path}` — definition-site, pre-mono (no `Instance` exists
//!   on this lane); the same non-injectivity residual trust-mir-extract
//!   documents, disclosed rather than hidden.
//! * `L{line}C{col}` — the LO line/col of the trust-ir `SourceSpan` stamped
//!   on the `Assert` node by `push_node` (`cur_span` at the push), i.e. the
//!   artifact's own `#loc` clause and the LO triple the cross-lane pin
//!   (`crates/trust-types/tests/obligation_key_divergence_pin.rs`, pin 5)
//!   measures as agreeing across lanes. Fallback when no span exists: L0C0,
//!   disclosed, separated by `occ`.
//! * `{slug}` — frontend vocabulary (`overflow`, `overflow_neg`,
//!   `div_by_zero`, `rem_by_zero`, `bounds_check`). The measured signed-div
//!   pair (one source span, two checks) separates on this axis.
//! * `o{occ}` — per-function occurrence ordinal within identical
//!   `(slug, file, line, col)`, THIR-emission order, ALWAYS rendered.
//!   Required by measurement: pin 4/5 show `add3`'s two `no_overflow`
//!   asserts share ONE LO triple in both lanes, so `(slug, line, col)` alone
//!   is not injective. Within a collided class, identity stability honestly
//!   degrades to emission-order stability; everywhere else it is pure source
//!   shape — block/instruction indexes appear ONLY in the positional
//!   [`ObligationSite`], never in the identity.
//!
//! NON-BIJECTION (Step 0's finding, stated here because every consumer will
//! be tempted to assume otherwise): an identity names a SOURCE CHECK and a
//! site names ONE instruction; NEITHER implies any correspondence with
//! solver error rules. Measured: 4 asserts became 6 CHC error rules — the
//! translator invents rules of its own (`sdiv` safety, block-parameter
//! equalities), and it is entitled to.
//!
//! WHY INSTALL AT THE FINALIZER. The per-body mini-module always carries the
//! body as `FuncId(0)`; dense ids exist only after `assemble` pass 1, and
//! `crate_module::record` DROPS the mini-module's obligation table by
//! construction. Rows are therefore recorded per body at emission (this
//! module's [`DirectObligationRecord`]), carried in a session-scoped
//! [`DirectObligationRegistry`] keyed by `def_index` (the same key
//! `BodyRecord` rides under), and installed into `module.proof_obligations`
//! at the crate finalizer — never via `Function.proofs`, whose population
//! `Module::add_function` would turn into synthesized function-level claims
//! and which the authority tripwire rightly counts as claims.
//!
//! The `(BlockId, inst_index)` captured at emission stays valid verbatim in
//! the assembled module: `seal_with` moves the open block wholesale,
//! `finish_body` reorders only WHOLE blocks (ids untouched), and assemble's
//! `certify_remap_shape` pins block set / instruction sequence / proof
//! annotations across the splice with an EXECUTABLE certificate. The
//! installer still refuses to trust that argument alone: it re-resolves
//! every site and requires the recorded `Inst::Assert` with the recorded
//! `ProofAnnotation` at that exact position (fail closed, mutation-proved).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::collections::BTreeMap;
use std::collections::btree_map::Entry;

use trust_ir::{
    BlockId, FuncId, Inst, Module, ObligationKind, ObligationSite, ProofAnnotation, ProofId,
    ProofObligation, ProofObligationSourceIdentity, ProofObligationSourceRange, ProofStatus,
    SourceSpan, PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES,
};

/// The stable, versioned `source_id` every direct-lane obligation carries.
/// A consumer can tell this schema from the MIR frontend's
/// (`trust-ir-frontend/mir-assert@1`) and from any future revision of ours.
pub const DIRECT_ASSERT_SOURCE_ID: &str = "trust-thir-lower/direct-assert@1";

/// Assertion-id slugs — the frontend vocabulary
/// (`mir_lower.rs::assert_obligation_class`), verbatim, so the class axis of
/// the cross-lane differential never needs a translation table.
pub const SLUG_OVERFLOW: &str = "overflow";
pub const SLUG_OVERFLOW_NEG: &str = "overflow_neg";
pub const SLUG_DIV_BY_ZERO: &str = "div_by_zero";
pub const SLUG_REM_BY_ZERO: &str = "rem_by_zero";
/// Step 5: the array-index bounds check. Verbatim the frontend's slug —
/// `mir_lower.rs::assert_obligation_class` mints
/// `AssertKind::BoundsCheck { .. } => (Kind::BoundsCheck, "bounds_check",
/// "index is in bounds")` — so the cross-lane class axis pairs without a
/// translation table.
pub const SLUG_BOUNDS_CHECK: &str = "bounds_check";

/// Human phrase per slug — frontend vocabulary, verbatim. An unknown slug
/// (a future emission site added without extending this table) degrades to a
/// generic phrase rather than failing the install: the phrase is
/// human-facing description text, not identity.
fn phrase_for_slug(slug: &str) -> &'static str {
    match slug {
        SLUG_OVERFLOW => "arithmetic does not overflow",
        SLUG_OVERFLOW_NEG => "negation does not overflow",
        SLUG_DIV_BY_ZERO => "divisor is nonzero",
        SLUG_REM_BY_ZERO => "remainder divisor is nonzero",
        SLUG_BOUNDS_CHECK => "index is in bounds",
        _ => "the asserted panic-guard condition holds",
    }
}

/// Slug -> `trust_ir::ObligationKind`, the SOLE kind authority for the
/// installer's mint (a [`DirectObligationRecord`] carries no kind field — the
/// slug is the kind carrier). Exhaustive over this module's slug consts:
/// `bounds_check` -> `BoundsCheck`, the four arithmetic slugs ->
/// `ArithmeticSafety`. An UNKNOWN slug is an install-time error, never a
/// wildcard default — `phrase_for_slug`'s degrade-to-generic precedent does
/// not transfer, because a phrase is human-facing description text while kind
/// is routed vocabulary (the tier arm and the Step 4 sibling both gate on it).
pub fn obligation_kind_for_slug(slug: &str) -> Result<ObligationKind, String> {
    match slug {
        SLUG_BOUNDS_CHECK => Ok(ObligationKind::BoundsCheck),
        SLUG_OVERFLOW | SLUG_OVERFLOW_NEG | SLUG_DIV_BY_ZERO | SLUG_REM_BY_ZERO => {
            Ok(ObligationKind::ArithmeticSafety)
        }
        unknown => Err(format!(
            "no ObligationKind mapping for slug {unknown:?}; a new emission site must extend \
             obligation_kind_for_slug in the same reviewed change that introduces its slug \
             (fail closed, never a wildcard kind)"
        )),
    }
}

/// The rustc-span extent rendered AT EMISSION (both endpoints), in the same
/// convention `to_source_span` uses: 1-based lines, 0-based cols. The FILE is
/// deliberately absent — file indexes are re-interned at the crate-assembly
/// splice, so the installer reads the file from the recorded `Assert` node's
/// own (post-splice) span instead, and never interns-on-miss.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DirectSourceRange {
    pub start_line: u32,
    pub start_col: u32,
    pub end_line: u32,
    pub end_col: u32,
}

/// Step 6, increment 1 (docs/design/DIRECT-LANE-PROOF-AUTHORITY.md, design of
/// record 2026-08-31): the typed L0 safety-formula outcome for one direct
/// assert, minted ONCE at emission by
/// `trust_ir_bridge::safety_formulas::mint_direct_safety_formula` and carried
/// as SESSION STATE ONLY — no serde, zero artifact bytes at any wire format.
/// Rows stay formula-free: the installer counts these outcomes into
/// [`DirectInstallOutcome`] and NEVER copies a formula onto a row; the
/// non-frozen tier arm's "carries a formula" violation remains the live gate
/// (pinned below by `install_never_copies_a_minted_formula_onto_a_row` and
/// `a_formula_bearing_row_is_still_an_inventory_error`).
///
/// The (identity, formula) pair is assembled at the same emission point that
/// mints the positional binding — each half minted exactly once, nothing
/// recomputed downstream (the id/digest "never inferred or updated
/// independently" rule; deliberately NO digest this increment, because the
/// bytes are self-comparable and a digest adds exactly the recompute hazard
/// that rule forbids).
#[derive(Debug, Clone, PartialEq)]
pub enum DirectFormulaOutcome {
    /// The mint produced the typed violation formula (+ its once-rendered
    /// json/smtlib derivatives).
    Minted(trust_ir_bridge::safety_formulas::MintedDirectFormula),
    /// The mint declined with a named, fix-carrying reason
    /// (`FormulaDecline::code()`), or the capture could not supply an
    /// in-envelope operand (`opaque-operand`).
    Withheld { reason: &'static str },
    /// No mint was attempted (pre-Step-6 recording path, or a test record).
    NotMinted,
}

/// One direct-lane `Inst::Assert`, recorded AT EMISSION by the `.with_proof`
/// sites in `lib.rs` — the instruction position is captured structurally
/// (the node just pushed), never re-derived by span matching afterwards.
#[derive(Debug, Clone, PartialEq)]
pub struct DirectObligationRecord {
    /// Identity slug (see module docs). `&'static str` because every legal
    /// value is a compile-time constant of this module.
    pub slug: &'static str,
    /// The `ProofAnnotation` the assert node carries (`NoOverflow`,
    /// `DivNonZero`, `ShiftInRange`). Used by the install-time structural
    /// self-check; NOT part of the identity.
    pub annotation: ProofAnnotation,
    /// The node's own stamped span at the push (`cur_span`), i.e. the
    /// artifact `#loc` clause: mini-module file index + LO line/col.
    /// Identity's `L{line}C{col}` axis; `None` degrades to `L0C0`.
    pub loc: Option<SourceSpan>,
    /// Block under construction at the push. Positional, NON-identity.
    pub block: BlockId,
    /// Index of the assert within that block's body (`cur.len() - 1`
    /// immediately after the push). Positional, NON-identity.
    pub inst_index: u32,
    /// Emission-rendered rustc-span extent for `ProofObligationSourceRange`.
    /// `None` (dummy/degenerate span) is a counted disclosure, never a
    /// fabricated range.
    pub range: Option<DirectSourceRange>,
    /// Step 6: the session-state formula outcome (see
    /// [`DirectFormulaOutcome`]). NOT identity, NOT row content — the
    /// installer only counts it.
    pub formula: DirectFormulaOutcome,
}

/// Everything one lowered body contributes: its registry key (`def_index`,
/// the same key `BodyRecord` rides under), its `def_path_str` rendering, and
/// the emission-ordered records.
#[derive(Debug, Clone, PartialEq)]
pub struct DirectBodyObligations {
    pub def_index: u32,
    /// `tcx.def_path_str` rendering (crate name NOT included; the installer
    /// prepends it) — the same spelling `Function.name`/`BodyRecord` use.
    pub def_path: String,
    pub records: Vec<DirectObligationRecord>,
}

/// Session-scoped carry from the per-body lowering to the crate finalizer,
/// keyed by `def_index` — the same mechanism and key discipline as
/// `CrateModuleRegistry`. Duplicate registrations are RETAINED as a defect
/// ledger (never silently merged); the installer fails closed on them.
#[derive(Debug, Default)]
pub struct DirectObligationRegistry {
    pub bodies: BTreeMap<u32, DirectBodyObligations>,
    pub duplicate_def_indices: Vec<u32>,
}

impl DirectObligationRegistry {
    pub fn insert(&mut self, body: DirectBodyObligations) {
        match self.bodies.entry(body.def_index) {
            Entry::Occupied(_) => self.duplicate_def_indices.push(body.def_index),
            Entry::Vacant(slot) => {
                slot.insert(body);
            }
        }
    }

    pub fn is_empty(&self) -> bool {
        self.bodies.is_empty() && self.duplicate_def_indices.is_empty()
    }
}

/// Make an arbitrary string safe as a `ProofObligation` source/assertion id:
/// control chars become `_`, trimmed, truncated to the format's byte cap on
/// a char boundary, empty degrades to `fallback`. Replica of the frontend's
/// `clamp_proof_text_id` — keeps `InvalidProofObligationSourceTextId`
/// unconstructible whatever a def path contains.
fn clamp_proof_text_id(value: &str, fallback: &'static str) -> String {
    let cleaned: String =
        value.chars().map(|c| if c.is_control() { '_' } else { c }).collect();
    let trimmed = cleaned.trim();
    let mut out = String::new();
    for (offset, ch) in trimmed.char_indices() {
        if offset + ch.len_utf8() > PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES {
            break;
        }
        out.push(ch);
    }
    let out = out.trim().to_string();
    if out.is_empty() { fallback.to_string() } else { out }
}

/// Keep an obligation `description` one-line and free of the text format's
/// string delimiters (frontend replica).
fn clamp_proof_description(value: &str) -> String {
    value
        .chars()
        .map(|c| match c {
            '"' | '\\' => '\'',
            c if c.is_control() => ' ',
            c => c,
        })
        .collect()
}

/// Build the direct-lane `assertion_id`, clamped WITHOUT losing the suffix
/// that makes it unique — a suffix-preserving replica of the frontend's
/// `assert_assertion_id`: the `{crate}::{def_path}` head is clamped to the
/// byte cap, the `#L..C..#{slug}#o{occ}` tail is ALWAYS kept.
pub fn direct_assertion_id(
    crate_name: &str,
    def_path: &str,
    line: u32,
    col: u32,
    slug: &str,
    occ: u32,
) -> String {
    let max = PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES;
    let suffix = format!("#L{line}C{col}#{slug}#o{occ}");
    if suffix.len() >= max {
        return clamp_proof_text_id(&suffix, "direct-assert");
    }
    let budget = max - suffix.len();
    let head_raw = format!("{crate_name}::{def_path}");
    let cleaned: String =
        head_raw.chars().map(|c| if c.is_control() { '_' } else { c }).collect();
    let mut head = String::new();
    for (offset, ch) in cleaned.trim().char_indices() {
        if offset + ch.len_utf8() > budget {
            break;
        }
        head.push(ch);
    }
    clamp_proof_text_id(&format!("{}{suffix}", head.trim_end()), "direct-assert")
}

/// The human description for one direct row. States a CLAIM, names no solver
/// rule (Step 0: the translator invents rules; a description promising a
/// rule would be a lie some sessions later).
pub fn direct_obligation_description(
    crate_name: &str,
    def_path: &str,
    line: u32,
    col: u32,
    slug: &str,
) -> String {
    clamp_proof_description(&format!(
        "direct THIR Assert ({slug}) at L{line}C{col} of `{crate_name}::{def_path}`: {phrase}. \
         RECORDED BY THE LOWERING, NOT PROVED.",
        phrase = phrase_for_slug(slug),
    ))
}

/// What [`install_direct_obligations`] did — counts are DISCLOSURES, the
/// `errors` the caller collected are the gate.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct DirectInstallOutcome {
    /// Rows appended to `module.proof_obligations`.
    pub installed: usize,
    /// Registered bodies whose `def_index` resolved to a spliced `FuncId`.
    pub bodies_installed: usize,
    /// Registered bodies with NO spliced function (splice refusal, huge-body
    /// tag, fixpoint refusal, …). Their records are dropped, disclosed here:
    /// an installed row for a refused body would dangle.
    pub bodies_skipped_unspliced: usize,
    /// Rows installed without a `ProofObligationSourceRange` (dummy span,
    /// missing node span, degenerate extent, out-of-table file index). The
    /// validator's nonzero-line/file rules are never fabricated around.
    pub rows_without_range: usize,
    /// Step 6 disclosure counters over the records of SPLICED bodies (the
    /// ones the installer walks): how many carried a minted session formula,
    /// a named withhold, or no mint attempt. ADDITIVE — the frozen run-4
    /// block reads only the four fields above by name — and pure disclosure:
    /// no formula reaches any row whatever these counts say.
    pub formulas_minted: usize,
    /// See [`Self::formulas_minted`].
    pub formulas_withheld: usize,
    /// See [`Self::formulas_minted`].
    pub formulas_not_minted: usize,
}

/// Install the recorded direct-lane obligations into the ASSEMBLED crate
/// module. Call AFTER the third pre-birth tripwire run (post clean-origin
/// append + IR-5 link), so the three existing zero-check sites keep their
/// meaning verbatim at both tiers.
///
/// * `assigned` — assemble pass 1's dense `def_index -> FuncId` map
///   (`Assembled::assigned`), sorted by `def_index`.
/// * Every failure pushes into `errors` (the caller's fail-closed channel)
///   AND withholds the row — a partial install never ships silently.
pub fn install_direct_obligations(
    module: &mut Module,
    crate_name: &str,
    assigned: &[(u32, FuncId)],
    registry: DirectObligationRegistry,
    errors: &mut Vec<String>,
) -> DirectInstallOutcome {
    let mut outcome = DirectInstallOutcome::default();

    // Step 6 increment 2, item 1 (docs/design/DIRECT-LANE-PROOF-AUTHORITY.md):
    // the env-gated PRODUCTION dump of the real per-record
    // `DirectFormulaOutcome`s, closing increment 1's model-vs-real gap. Read
    // FRESH per call via `var_os` — deliberately no `OnceLock` (the
    // per-test-env constraint) — so unset costs one env read, no allocation,
    // no IO. The dump is DISCLOSURE, not authority: rows stay formula-free,
    // module bytes and `DirectInstallOutcome` are byte-identical either way,
    // and an IO failure warns on stderr but NEVER pushes into `errors` (a
    // diagnostic dump must not fail semantic finalization; fail-closed lives
    // at the READER — `trust_ir_bridge::direct_formula_dump::
    // parse_direct_formula_dump`, the v6/D1 spec_cli precedent).
    let dump_dir: Option<std::path::PathBuf> = std::env::var_os(
        trust_ir_bridge::direct_formula_dump::TRUST_DIRECT_FORMULA_DUMP_ENV,
    )
    .map(std::path::PathBuf::from);
    let mut dump_rows: Vec<trust_ir_bridge::direct_formula_dump::DumpedDirectRecord> =
        Vec::new();

    if !registry.duplicate_def_indices.is_empty() {
        errors.push(format!(
            "direct-obligation install: duplicate per-body registrations for def indices {:?}; \
             a body lowered twice cannot contribute obligation rows (fix the registration \
             wiring, not this gate)",
            registry.duplicate_def_indices
        ));
        return outcome;
    }

    // Belt: (source_id, assertion_id) uniqueness across the whole module.
    // Unreachable while `occ` is part of the identity — which is exactly why
    // it is checked: this is the mutation tripwire for an occ removal.
    let mut seen_identities: BTreeMap<(String, String), ()> = module
        .proof_obligations
        .iter()
        .filter_map(|o| o.source.as_ref())
        .map(|s| ((s.source_id.clone(), s.assertion_id.clone()), ()))
        .collect();

    for (def_index, body) in &registry.bodies {
        let function = assigned
            .binary_search_by_key(def_index, |(d, _)| *d)
            .ok()
            .map(|i| assigned[i].1);
        let Some(fid) = function else {
            // Not spliced: a refusal upstream (splice_ok, huge-body cap,
            // fixpoint). Rows for it would dangle — drop and disclose.
            outcome.bodies_skipped_unspliced += 1;
            continue;
        };
        if !body.records.is_empty() {
            outcome.bodies_installed += 1;
        }

        // Per-function occurrence ordinals within identical
        // (slug, file, line, col), THIR-emission order.
        let mut occ_counters: BTreeMap<(String, i64, u32, u32), u32> = BTreeMap::new();

        for record in &body.records {
            // Step 6 disclosure counters — counted for every walked record,
            // BEFORE any withhold path, so the counts describe what the
            // lowering minted rather than what survived installation. The
            // formula itself is read by NOTHING here: rows ship formula-free
            // at this tier (the arm's "carries a formula" violation is the
            // live gate).
            match &record.formula {
                DirectFormulaOutcome::Minted(_) => outcome.formulas_minted += 1,
                DirectFormulaOutcome::Withheld { .. } => outcome.formulas_withheld += 1,
                DirectFormulaOutcome::NotMinted => outcome.formulas_not_minted += 1,
            }
            let (line, col, file_key) = match record.loc {
                Some(loc) => (loc.line, loc.col, i64::from(loc.file)),
                None => (0, 0, -1),
            };
            let occ_key = (record.slug.to_string(), file_key, line, col);
            let occ = *occ_counters
                .entry(occ_key)
                .and_modify(|n| *n += 1)
                .or_insert(0);

            // The identity mint is HOISTED above the structural self-check so
            // the dump row below and the obligation row share ONE minted
            // identity (`direct_assertion_id` is pure; the belt that consumes
            // it stays exactly where it was).
            let assertion_id =
                direct_assertion_id(crate_name, &body.def_path, line, col, record.slug, occ);

            // Dump hook — immediately after the occ computation, at the same
            // point the disclosure counters fired and BEFORE any withhold
            // path: the dump describes what the LOWERING minted, not what
            // survived installation (a self-check-withheld row is still a
            // real record of the lowering). Unspliced bodies never reach this
            // loop and are NOT dumped; the grader enumerates their MIR
            // asserts fail-closed.
            if dump_dir.is_some() {
                use trust_ir_bridge::direct_formula_dump as dfd;
                let dumped_outcome = match &record.formula {
                    DirectFormulaOutcome::Minted(minted) => {
                        // VERBATIM bytes of the once-rendered derivatives —
                        // never `to_string(&minted.formula)` here (the
                        // minted-once rule, kill-mutation W1's target).
                        dfd::DumpedOutcome::minted_verbatim(
                            &minted.formula_json,
                            &minted.smtlib,
                        )
                    }
                    DirectFormulaOutcome::Withheld { reason } => {
                        dfd::DumpedOutcome::Withheld { reason: (*reason).to_string() }
                    }
                    DirectFormulaOutcome::NotMinted => dfd::DumpedOutcome::NotMinted(true),
                };
                dump_rows.push(dfd::DumpedDirectRecord {
                    v: dfd::DIRECT_FORMULA_DUMP_VERSION.to_string(),
                    krate: crate_name.to_string(),
                    def_path: body.def_path.clone(),
                    def_index: *def_index,
                    slug: record.slug.to_string(),
                    line,
                    col,
                    occ,
                    assertion_id: assertion_id.clone(),
                    block: record.block.index(),
                    inst_index: record.inst_index,
                    outcome: dumped_outcome,
                });
            }

            // Install-time structural self-check: the recorded site must
            // resolve to the recorded `Inst::Assert` carrying the recorded
            // `ProofAnnotation`. Anything else is a carry defect and the row
            // is withheld, fail closed.
            let node = module
                .functions
                .iter()
                .find(|f| f.id == fid)
                .and_then(|f| f.blocks.iter().find(|b| b.id == record.block))
                .and_then(|b| b.body.get(record.inst_index as usize));
            let node = match node {
                Some(node)
                    if matches!(node.inst, Inst::Assert { .. })
                        && node.proofs.contains(&record.annotation) =>
                {
                    node
                }
                _ => {
                    errors.push(format!(
                        "direct-obligation install: structural self-check failed for \
                         `{crate_name}::{def_path}` {slug} at block {block}, inst {index}: the \
                         recorded position does not hold the recorded Assert/annotation; the \
                         emission-time binding did not survive the carry, so the row is \
                         withheld (fail closed)",
                        def_path = body.def_path,
                        slug = record.slug,
                        block = record.block.index(),
                        index = record.inst_index,
                    ));
                    continue;
                }
            };

            // Range: file index from the node's own (post-splice re-interned)
            // span; extent from the emission-rendered rustc span. Any miss or
            // degenerate combination omits the range with a counted
            // disclosure — never a fabricated coordinate.
            let range = match (node.span, record.range) {
                (Some(node_span), Some(extent))
                    if (node_span.file as usize) < module.files.len()
                        && extent.start_line != 0
                        && extent.end_line != 0
                        && (extent.end_line, extent.end_col)
                            >= (extent.start_line, extent.start_col) =>
                {
                    Some(ProofObligationSourceRange {
                        file: node_span.file,
                        start_line: extent.start_line,
                        start_col: extent.start_col,
                        end_line: extent.end_line,
                        end_col: extent.end_col,
                    })
                }
                _ => None,
            };
            if range.is_none() {
                outcome.rows_without_range += 1;
            }

            let identity_key = (DIRECT_ASSERT_SOURCE_ID.to_string(), assertion_id.clone());
            if seen_identities.insert(identity_key, ()).is_some() {
                errors.push(format!(
                    "direct-obligation install: duplicate obligation identity \
                     ({DIRECT_ASSERT_SOURCE_ID}, {assertion_id}); the occ ordinal makes this \
                     unreachable, so its appearance means the identity scheme regressed — \
                     row withheld (fail closed)"
                ));
                continue;
            }

            // Kind from the slug — the record's sole kind carrier. An unknown
            // slug withholds the row with an error (fail closed, counted via
            // the caller's error channel), never a defaulted kind.
            let kind = match obligation_kind_for_slug(record.slug) {
                Ok(kind) => kind,
                Err(detail) => {
                    errors.push(format!(
                        "direct-obligation install: `{crate_name}::{def_path}`: {detail}; \
                         row withheld (fail closed)",
                        def_path = body.def_path,
                    ));
                    continue;
                }
            };

            let Ok(next_id) = u32::try_from(module.proof_obligations.len()) else {
                errors.push(
                    "direct-obligation install: obligation table exceeds u32 — refusing to mint"
                        .to_string(),
                );
                return outcome;
            };
            let mut source =
                ProofObligationSourceIdentity::new(DIRECT_ASSERT_SOURCE_ID, assertion_id);
            if let Some(range) = range {
                source = source.with_range(range);
            }
            module.proof_obligations.push(
                ProofObligation::new(
                    ProofId::new(next_id),
                    kind,
                    ProofStatus::Pending,
                    direct_obligation_description(
                        crate_name,
                        &body.def_path,
                        line,
                        col,
                        record.slug,
                    ),
                )
                .with_function(fid)
                .with_source(source)
                .with_site(ObligationSite::new(fid, record.block, record.inst_index)),
            );
            outcome.installed += 1;
        }
    }

    // Seal + atomic publish (O_EXCL temp, rename) — one complete sealed file
    // per crate, last-writer-wins under a concurrent double-build. Loud on
    // failure, NEVER an install error.
    if let Some(dir) = dump_dir {
        if let Err(err) = trust_ir_bridge::direct_formula_dump::write_direct_formula_dump(
            &dir, crate_name, &dump_rows,
        ) {
            eprintln!(
                "warning: {env}={dir}: failed to write the direct-formula dump for crate \
                 `{crate_name}`: {err} (diagnostic disclosure only; the install outcome and \
                 module bytes are unaffected)",
                env = trust_ir_bridge::direct_formula_dump::TRUST_DIRECT_FORMULA_DUMP_ENV,
                dir = dir.display(),
            );
        }
    }
    outcome
}

/// The direct-lane capability ladder, tier by tier. Mirrors (and is mapped
/// from) `crate_module::DirectObligationCapability`; lives here so the
/// tier-aware inventory below is unit-testable outside the rustc graph.
///
/// BOTH tiers refuse proof authority and native verification requests —
/// obligations may exist without being authority, and nothing below the
/// authority flip (Step 7) may loosen either answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DirectObligationTier {
    /// Structural lowering and differential parity only; every proof channel
    /// of the emitted module is empty.
    StructuralParityOnly,
    /// The module may carry direct-assert obligation rows — every one
    /// `Pending`, claim-free, formula-free, public-identity-free — and
    /// NOTHING else: certificates, diagnostics, function claims, summaries,
    /// spec proof bindings and Linked spec modules all remain rejected.
    ObligationBearingPending,
}

impl DirectObligationTier {
    /// Stable spelling for `coverage.json` and tracing output.
    pub const fn marker(self) -> &'static str {
        match self {
            Self::StructuralParityOnly => "structural-parity-only-v1",
            Self::ObligationBearingPending => "obligation-bearing-pending-v2",
        }
    }

    /// Whether this artifact may be treated as source-proof authority.
    /// FALSE at every tier this enum has; the authority flip is Step 7,
    /// owner-signed, and adds a new variant rather than editing an answer.
    pub const fn grants_proof_authority(self) -> bool {
        match self {
            Self::StructuralParityOnly => false,
            Self::ObligationBearingPending => false,
        }
    }

    /// Whether this producer can build direct native verification requests.
    /// FALSE at both tiers: a Pending claim-row is not a request payload,
    /// and the `vc:` public identity pair is deliberately NOT minted here.
    pub const fn emits_native_verification_requests(self) -> bool {
        match self {
            Self::StructuralParityOnly => false,
            Self::ObligationBearingPending => false,
        }
    }

    /// Whether the finalizer may run the obligation install at all.
    pub const fn admits_pending_obligation_rows(self) -> bool {
        match self {
            Self::StructuralParityOnly => false,
            Self::ObligationBearingPending => true,
        }
    }
}

/// Tier-aware authority inventory.
///
/// * At [`DirectObligationTier::StructuralParityOnly`] this is BYTE-IDENTICAL
///   to the historical `crate_module::direct_authority_inventory_errors` —
///   same counters, same single error string — so the three PRE-BIRTH run
///   sites (pre-seam, post-disclosures, post clean-origin append) keep their
///   zero-check meaning verbatim at BOTH tiers, and rollback of the tier
///   const restores the old behaviour exactly.
/// * At [`DirectObligationTier::ObligationBearingPending`] the obligation
///   table may be non-empty, but every row must be a conforming direct-assert
///   claim: `Pending`, no formula, no public identity, our `source_id`, a
///   function scope and a site. Everything else — certificates, diagnostics,
///   function claims, summaries, spec proof bindings, Linked spec modules —
///   is rejected exactly as before. A `Discharged`/`Trusted`/`Certified`
///   status is an inventory error, not an upgrade.
pub fn inventory_errors_at_tier(module: &Module, tier: DirectObligationTier) -> Vec<String> {
    let obligations = module.proof_obligations.len();
    let certificates = module.proof_certificates.len();
    let diagnostics = module.obligation_diagnostics.len();
    let function_claims: usize =
        module.functions.iter().map(|function| function.proofs.len()).sum();
    let function_summaries =
        module.functions.iter().filter(|function| function.summary.is_some()).count();
    let spec_proofs: usize = module.spec_modules.iter().map(|spec| spec.proofs.len()).sum();
    let linked_specs = module
        .spec_modules
        .iter()
        .filter(|spec| spec.enforcement == trust_ir::SpecEnforcementMode::Linked)
        .count();

    match tier {
        DirectObligationTier::StructuralParityOnly => {
            if obligations == 0
                && certificates == 0
                && diagnostics == 0
                && function_claims == 0
                && function_summaries == 0
                && spec_proofs == 0
                && linked_specs == 0
            {
                return Vec::new();
            }

            vec![format!(
                "direct-THIR structural-parity-only authority tripwire: obligations {obligations}, \
                 certificates {certificates}, obligation diagnostics {diagnostics}, function claims \
                 {function_claims}, function summaries {function_summaries}, spec proof bindings \
                 {spec_proofs}, linked spec modules {linked_specs}; direct artifacts cannot carry \
                 proof/contract authority until exact source-contract, SSA-state, and \
                 obligation-ownership wiring exists"
            )]
        }
        DirectObligationTier::ObligationBearingPending => {
            let mut errors = Vec::new();
            if certificates != 0
                || diagnostics != 0
                || function_claims != 0
                || function_summaries != 0
                || spec_proofs != 0
                || linked_specs != 0
            {
                errors.push(format!(
                    "direct-THIR obligation-bearing-pending authority tripwire: certificates \
                     {certificates}, obligation diagnostics {diagnostics}, function claims \
                     {function_claims}, function summaries {function_summaries}, spec proof \
                     bindings {spec_proofs}, linked spec modules {linked_specs}; the \
                     obligation-bearing-pending-v2 tier admits Pending direct-assert obligation \
                     rows and NOTHING else — every other proof/contract channel remains \
                     authority-bearing and must stay empty"
                ));
            }
            for (index, obligation) in module.proof_obligations.iter().enumerate() {
                let mut violations: Vec<String> = Vec::new();
                if obligation.status != ProofStatus::Pending {
                    violations
                        .push(format!("status {} (must be pending)", obligation.status));
                }
                // Trust (Step 3 landing, smuggle lens S6): the kind axis was
                // measurably unbound — a Pending `Postcondition` wearing the
                // direct source_id passed this arm while its doc claimed
                // "conforming direct-assert claim". The arm binds the kind set
                // to EXACTLY the installer's mint range. Trust (Step 5,
                // docs/design/DIRECT-LANE-PROOF-AUTHORITY.md): that range
                // widened from {ArithmeticSafety} to {ArithmeticSafety,
                // BoundsCheck} when the dynamic-index bounds Assert landed —
                // the S6 closure property is allowlist == mint range, not
                // |set| == 1, and both sides move here in one reviewed change.
                if !matches!(
                    obligation.kind,
                    ObligationKind::ArithmeticSafety | ObligationKind::BoundsCheck
                ) {
                    violations.push(format!(
                        "kind {:?} (the direct lane mints ArithmeticSafety and BoundsCheck only)",
                        obligation.kind
                    ));
                }
                if obligation.formula.is_some() {
                    violations.push("carries a formula".to_string());
                }
                match &obligation.source {
                    None => violations.push("has no source identity".to_string()),
                    Some(source) => {
                        if source.source_id != DIRECT_ASSERT_SOURCE_ID {
                            violations.push(format!(
                                "has foreign source_id {:?}",
                                source.source_id
                            ));
                        }
                        if source.public.is_some() {
                            violations.push(
                                "carries a public obligation identity".to_string(),
                            );
                        }
                    }
                }
                if obligation.function.is_none() {
                    violations.push("has no owning-function scope".to_string());
                }
                if obligation.site.is_none() {
                    violations.push("has no obligation site".to_string());
                }
                if !violations.is_empty() {
                    errors.push(format!(
                        "direct-THIR obligation-bearing-pending authority tripwire: obligation \
                         {index} {violations}; every direct row must be a claim-free Pending \
                         direct-assert record (status Pending, no formula, no public identity, \
                         source_id {DIRECT_ASSERT_SOURCE_ID:?}, function and site bound)",
                        violations = violations.join(", "),
                    ));
                }
            }
            errors
        }
    }
}

/// Trust (Step 2/3 landing): a minimal module carrying exactly ONE conforming
/// Pending direct-assert row, for `crate_module`'s post-birth pin
/// `a_conforming_pending_row_passes_only_the_recorded_tier`. Built through the
/// same field vocabulary the installer uses, so the pin exercises the real
/// row shape rather than a hand-rolled twin. Test builds only.
#[cfg(test)]
pub(crate) fn module_with_conforming_pending_row_for_tests() -> Module {
    let mut module = Module::new("post_birth_pin");
    let ty = module
        .add_func_type(trust_ir::FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let fid = FuncId::new(0);
    let mut function = trust_ir::Function::new(fid, "post_birth_pin_fn", ty, BlockId::new(0));
    let mut block = trust_ir::Block::new(BlockId::new(0));
    block.body.push(
        trust_ir::node::InstrNode::new(Inst::Assert {
            cond: trust_ir::ValueId::new(0),
            kind: trust_ir::AssertKind::DivByZero,
            site: None,
        })
        .with_proof(ProofAnnotation::DivNonZero),
    );
    function.blocks.push(block);
    module.try_add_function(function).expect("Module::try_add_function: test fixture");
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::ArithmeticSafety,
            ProofStatus::Pending,
            "post-birth pin row".to_string(),
        )
        .with_function(fid)
        .with_source(ProofObligationSourceIdentity::new(
            DIRECT_ASSERT_SOURCE_ID,
            "post_birth_pin::f#L1C1#div_zero#o0".to_string(),
        ))
        .with_site(ObligationSite::new(fid, BlockId::new(0), 0)),
    );
    module
}

// ===================== cross-lane correlation (instrument) ===================

/// Check-class vocabulary shared by both lanes — the same classes Step 1's
/// `(range, class)` capture recovers from MIR descriptions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DirectCheckClass {
    Overflow,
    DivZero,
    RemZero,
    Bounds,
}

/// Slug -> class. Total over this module's slugs; a future slug added
/// without extending this table correlates as unclassified (disclosed).
pub fn check_class_for_slug(slug: &str) -> Option<DirectCheckClass> {
    match slug {
        SLUG_OVERFLOW | SLUG_OVERFLOW_NEG => Some(DirectCheckClass::Overflow),
        SLUG_DIV_BY_ZERO => Some(DirectCheckClass::DivZero),
        SLUG_REM_BY_ZERO => Some(DirectCheckClass::RemZero),
        // Step 5: closes the designed-in hole — `Bounds` was reachable only
        // from the MIR-description side until the direct lane minted its own
        // bounds rows; `correlate()` now pairs the lanes on this class.
        SLUG_BOUNDS_CHECK => Some(DirectCheckClass::Bounds),
        _ => None,
    }
}

/// MIR-lane class recovery from the vcgen description text — the SAME
/// vocabulary Step 1's snapshot capture matches on. Fail-closed: an
/// unrecognized description is unclassified (disclosed), never guessed.
pub fn check_class_from_mir_description(description: &str) -> Option<DirectCheckClass> {
    if description.contains("division by zero") {
        Some(DirectCheckClass::DivZero)
    } else if description.contains("remainder by zero") {
        Some(DirectCheckClass::RemZero)
    } else if description.contains("index out of bounds")
        || description.contains("bounds check")
    {
        Some(DirectCheckClass::Bounds)
    } else if description.contains("overflow") {
        Some(DirectCheckClass::Overflow)
    } else {
        None
    }
}

/// One direct-lane row offered to the correlator: the scope is
/// `{crate}::{def_path}` (identity head), position is the identity's LO.
#[derive(Debug, Clone, PartialEq)]
pub struct DirectCorrelationRow {
    pub scope: String,
    pub slug: String,
    pub line: u32,
    pub col: u32,
}

/// One MIR-lane public row: the `vc:` textual id, the vcgen description the
/// class is recovered from, and the row's LO position.
#[derive(Debug, Clone, PartialEq)]
pub struct MirCorrelationRow {
    pub obligation_id: String,
    pub description: String,
    pub line: u32,
    pub col: u32,
}

/// The function component of a `vc:{fn}:{kind}:{n}` textual id, fail-closed.
fn vc_id_function_component(obligation_id: &str) -> Option<&str> {
    let rest = obligation_id.strip_prefix("vc:")?;
    let mut parts = rest.rsplitn(3, ':');
    let _n = parts.next()?;
    let _kind = parts.next()?;
    let function = parts.next()?;
    if function.is_empty() { None } else { Some(function) }
}

/// Verdict per `(function, class)` group. NEVER ordinal-aligned, never
/// site-compared across modules: sites are positions inside ONE module and
/// ordinals are two independent derivations whose agreement is coincidence
/// (the shortcut Step 1 deliberately rejected).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LaneCorrelation {
    /// Exactly one row on each side, at the same LO position.
    Unique,
    /// Both lanes populate the class but no unique position pairing exists —
    /// the measured shapes: add3 2<->2 (one shared LO), one direct division
    /// vs two MIR divzero rows.
    ClassOnly { direct: usize, mir: usize },
    /// Only the direct lane populates the class.
    DirectOnly { direct: usize },
    /// Only the MIR lane populates the class.
    MirOnly { mir: usize },
}

#[derive(Debug, Clone, PartialEq)]
pub struct CorrelationGroup {
    /// Canonical function component (`trust_types::canonical_artifact_id_component`
    /// of the direct scope; the `vc:` id's own component on the MIR side).
    pub function: String,
    pub class: DirectCheckClass,
    pub verdict: LaneCorrelation,
}

/// Fail-closed disclosure alongside the groups: rows neither lane could
/// classify are counted, never silently dropped into a wrong group.
#[derive(Debug, Clone, PartialEq)]
pub struct CorrelationReport {
    pub groups: Vec<CorrelationGroup>,
    pub unclassified_direct: usize,
    pub unclassified_mir: usize,
}

/// Correlate the two lanes' obligation surfaces on the three axes the
/// measurements support: function (canonical artifact component), class
/// (slug / description vocabulary), position (LO line:col — pin 5's measured
/// cross-lane agreement). Instrument only: nothing is wired to consume this
/// in the same change that introduces it, and `differential.rs` (frozen) is
/// deliberately untouched.
pub fn correlate(
    direct: &[DirectCorrelationRow],
    mir: &[MirCorrelationRow],
) -> CorrelationReport {
    let mut unclassified_direct = 0usize;
    let mut unclassified_mir = 0usize;
    let mut groups: BTreeMap<(String, DirectCheckClass), (Vec<(u32, u32)>, Vec<(u32, u32)>)> =
        BTreeMap::new();

    for row in direct {
        let Some(class) = check_class_for_slug(&row.slug) else {
            unclassified_direct += 1;
            continue;
        };
        let function = trust_types::canonical_artifact_id_component(&row.scope);
        groups.entry((function, class)).or_default().0.push((row.line, row.col));
    }
    for row in mir {
        let (Some(function), Some(class)) = (
            vc_id_function_component(&row.obligation_id),
            check_class_from_mir_description(&row.description),
        ) else {
            unclassified_mir += 1;
            continue;
        };
        groups
            .entry((function.to_string(), class))
            .or_default()
            .1
            .push((row.line, row.col));
    }

    let groups = groups
        .into_iter()
        .map(|((function, class), (direct_rows, mir_rows))| {
            let verdict = match (direct_rows.len(), mir_rows.len()) {
                (1, 1) if direct_rows[0] == mir_rows[0] => LaneCorrelation::Unique,
                (0, m) => LaneCorrelation::MirOnly { mir: m },
                (d, 0) => LaneCorrelation::DirectOnly { direct: d },
                (d, m) => LaneCorrelation::ClassOnly { direct: d, mir: m },
            };
            CorrelationGroup { function, class, verdict }
        })
        .collect();

    CorrelationReport { groups, unclassified_direct, unclassified_mir }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{
        Constant, FuncTy, Function, ICmpOp, InstrNode, Ty, ValueId,
    };

    const FIXTURE_CRATE: &str = "fixture";
    const FIXTURE_PATH: &str = "arith::checked";

    /// One function, one block, FOUR proof-guard asserts on one source line
    /// (LO 15:4) — the measured worst case: a signed-div-shaped
    /// div_by_zero+overflow pair (slug axis) plus a second overflow
    /// (occ axis), i.e. pin 4's add3 collision inside one body — PLUS a
    /// Step 5 bounds assert, so the fixture is a MIXED arith+bounds body and
    /// every install test exercises the kind-per-slug mint.
    ///
    /// Block body (inst_index):
    ///   0 Const   1 ICmp   2 Assert(DivNonZero)   3 Assert(NoOverflow)
    ///   4 Assert(NoOverflow)   5 Assert(InBounds)   6 Return
    fn fixture_module() -> (Module, DirectObligationRegistry, Vec<(u32, FuncId)>) {
        let mut module = Module::new(FIXTURE_CRATE);
        module.files.push("src/arith.rs".to_string());
        let ty = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let fid = FuncId::new(0);
        let mut function =
            Function::new(fid, format!("{FIXTURE_CRATE}::{FIXTURE_PATH}"), ty, BlockId::new(0));
        let mut block = trust_ir::Block::new(BlockId::new(0));
        block.params.push((ValueId::new(0), Ty::I32));
        let span = SourceSpan { file: 0, line: 15, col: 4 };
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(0) })
                .with_result(ValueId::new(1)),
        );
        block.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I32,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
        );
        for annotation in [
            ProofAnnotation::DivNonZero,
            ProofAnnotation::NoOverflow,
            ProofAnnotation::NoOverflow,
            ProofAnnotation::InBounds,
        ] {
            let mut node = InstrNode::new(Inst::Assert {
                cond: ValueId::new(2),
                kind: trust_ir::AssertKind::Unspecified,
                site: None,
            })
            .with_proof(annotation);
            node.span = Some(span);
            block.body.push(node);
        }
        block.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
        function.blocks.push(block);
        module.try_add_function(function).expect("Module::try_add_function: test fixture");

        let loc = Some(span);
        let range = Some(DirectSourceRange {
            start_line: 15,
            start_col: 4,
            end_line: 15,
            end_col: 11,
        });
        let records = vec![
            DirectObligationRecord {
                slug: SLUG_DIV_BY_ZERO,
                annotation: ProofAnnotation::DivNonZero,
                loc,
                block: BlockId::new(0),
                inst_index: 2,
                range,
                formula: DirectFormulaOutcome::NotMinted,
            },
            DirectObligationRecord {
                slug: SLUG_OVERFLOW,
                annotation: ProofAnnotation::NoOverflow,
                loc,
                block: BlockId::new(0),
                inst_index: 3,
                range,
                formula: DirectFormulaOutcome::NotMinted,
            },
            DirectObligationRecord {
                slug: SLUG_OVERFLOW,
                annotation: ProofAnnotation::NoOverflow,
                loc,
                block: BlockId::new(0),
                inst_index: 4,
                range,
                formula: DirectFormulaOutcome::NotMinted,
            },
            DirectObligationRecord {
                slug: SLUG_BOUNDS_CHECK,
                annotation: ProofAnnotation::InBounds,
                loc,
                block: BlockId::new(0),
                inst_index: 5,
                range,
                formula: DirectFormulaOutcome::NotMinted,
            },
        ];
        let mut registry = DirectObligationRegistry::default();
        registry.insert(DirectBodyObligations {
            def_index: 7,
            def_path: FIXTURE_PATH.to_string(),
            records,
        });
        (module, registry, vec![(7, fid)])
    }

    fn obligation_validation_errors(module: &Module) -> Vec<String> {
        trust_ir_build::validate_module(module)
            .into_iter()
            .map(|e| format!("{e:?}"))
            .filter(|e| {
                e.contains("Obligation") || e.contains("ProofObligation") || e.contains("Site")
            })
            .collect()
    }

    /// The hard boundary, pinned per tier and per axis: NO tier of this
    /// ladder grants proof authority or emits native verification requests.
    #[test]
    fn no_tier_grants_proof_authority_or_native_requests() {
        for tier in [
            DirectObligationTier::StructuralParityOnly,
            DirectObligationTier::ObligationBearingPending,
        ] {
            assert!(!tier.grants_proof_authority(), "{tier:?} must not grant authority");
            assert!(
                !tier.emits_native_verification_requests(),
                "{tier:?} must not emit native verification requests"
            );
        }
        assert_eq!(
            DirectObligationTier::StructuralParityOnly.marker(),
            "structural-parity-only-v1"
        );
        assert_eq!(
            DirectObligationTier::ObligationBearingPending.marker(),
            "obligation-bearing-pending-v2"
        );
        assert!(!DirectObligationTier::StructuralParityOnly.admits_pending_obligation_rows());
        assert!(DirectObligationTier::ObligationBearingPending.admits_pending_obligation_rows());
    }

    /// B1 (Step 5): kind-map totality over every slug const — bounds_check ->
    /// BoundsCheck, the four arithmetic slugs -> ArithmeticSafety — and an
    /// unknown slug takes the FAIL-CLOSED path (an error, never a defaulted
    /// ArithmeticSafety).
    #[test]
    fn kind_map_is_total_over_the_slug_consts_and_fails_closed_on_unknown() {
        assert_eq!(
            obligation_kind_for_slug(SLUG_BOUNDS_CHECK),
            Ok(ObligationKind::BoundsCheck)
        );
        for slug in [SLUG_OVERFLOW, SLUG_OVERFLOW_NEG, SLUG_DIV_BY_ZERO, SLUG_REM_BY_ZERO] {
            assert_eq!(
                obligation_kind_for_slug(slug),
                Ok(ObligationKind::ArithmeticSafety),
                "{slug} must map to ArithmeticSafety"
            );
        }
        let err = obligation_kind_for_slug("some_future_slug")
            .expect_err("an unknown slug must never default to a kind");
        assert!(err.contains("some_future_slug"), "{err}");
        assert!(err.contains("fail closed"), "{err}");
    }

    /// B1 companion: an unknown-slug record reaching the INSTALLER withholds
    /// the row with an install-time error — the fail-closed path is live at
    /// the mint, not only in the map's signature.
    #[test]
    fn install_withholds_a_row_whose_slug_has_no_kind_mapping() {
        let (mut module, _, assigned) = fixture_module();
        let mut registry = DirectObligationRegistry::default();
        registry.insert(DirectBodyObligations {
            def_index: 7,
            def_path: FIXTURE_PATH.to_string(),
            records: vec![DirectObligationRecord {
                slug: "some_future_slug",
                annotation: ProofAnnotation::DivNonZero,
                loc: Some(SourceSpan { file: 0, line: 15, col: 4 }),
                block: BlockId::new(0),
                inst_index: 2,
                range: None,
                formula: DirectFormulaOutcome::NotMinted,
            }],
        });
        let mut errors = Vec::new();
        let outcome =
            install_direct_obligations(&mut module, FIXTURE_CRATE, &assigned, registry, &mut errors);
        assert_eq!(outcome.installed, 0);
        assert!(module.proof_obligations.is_empty(), "the unmapped row must be withheld");
        assert_eq!(errors.len(), 1);
        assert!(errors[0].contains("no ObligationKind mapping"), "{}", errors[0]);
    }

    /// The structural-parity arm must stay BYTE-IDENTICAL to the frozen
    /// `crate_module::direct_authority_inventory_errors`: same zero
    /// condition, same single error string. The expected text below is a
    /// verbatim copy of the frozen format string — if either side moves, the
    /// pre-birth zero-check and this staged implementation have diverged.
    #[test]
    fn structural_parity_arm_is_byte_identical_to_the_frozen_tripwire() {
        let mut module = Module::new("parity");
        assert!(inventory_errors_at_tier(&module, DirectObligationTier::StructuralParityOnly)
            .is_empty());

        let ty = module
            .add_func_type(FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "direct", ty, BlockId::new(0));
        function.proofs.push(ProofAnnotation::NoOverflow);
        function.summary = Some(trust_ir::FunctionSummary::new());
        module.try_add_function(function).expect("Module::try_add_function: test fixture");
        module.spec_modules.push(trust_ir::SpecModule::linked("claimed_machine"));

        let errors =
            inventory_errors_at_tier(&module, DirectObligationTier::StructuralParityOnly);
        assert_eq!(
            errors,
            vec![
                "direct-THIR structural-parity-only authority tripwire: obligations 1, \
                 certificates 0, obligation diagnostics 0, function claims 1, function \
                 summaries 1, spec proof bindings 0, linked spec modules 1; direct artifacts \
                 cannot carry proof/contract authority until exact source-contract, SSA-state, \
                 and obligation-ownership wiring exists"
                    .to_string()
            ],
        );
    }

    /// End-to-end install over the collision fixture: every row Pending and
    /// claim-free, identities separate on the slug and occ axes, sites
    /// resolve to the exact recorded Assert nodes, the new tier's tripwire
    /// accepts the module, and the trust-ir validator raises no
    /// obligation-class error.
    #[test]
    fn install_mints_pending_claim_free_rows_with_slug_and_occ_separation() {
        let (mut module, registry, assigned) = fixture_module();
        let mut errors = Vec::new();
        let outcome =
            install_direct_obligations(&mut module, FIXTURE_CRATE, &assigned, registry, &mut errors);

        assert_eq!(errors, Vec::<String>::new());
        assert_eq!(outcome.installed, 4);
        assert_eq!(outcome.bodies_installed, 1);
        assert_eq!(outcome.bodies_skipped_unspliced, 0);
        assert_eq!(outcome.rows_without_range, 0);
        // Step 6 disclosure counters over the fixture's NotMinted records.
        assert_eq!(outcome.formulas_minted, 0);
        assert_eq!(outcome.formulas_withheld, 0);
        assert_eq!(outcome.formulas_not_minted, 4);

        let ids: Vec<&str> = module
            .proof_obligations
            .iter()
            .map(|o| o.source.as_ref().expect("source identity").assertion_id.as_str())
            .collect();
        assert_eq!(
            ids,
            vec![
                "fixture::arith::checked#L15C4#div_by_zero#o0",
                "fixture::arith::checked#L15C4#overflow#o0",
                "fixture::arith::checked#L15C4#overflow#o1",
                "fixture::arith::checked#L15C4#bounds_check#o0",
            ],
        );

        for obligation in &module.proof_obligations {
            assert_eq!(obligation.status, ProofStatus::Pending);
            // B4 (Step 5): kind-per-slug — each installed row's kind is the
            // map of the slug its own identity carries, over a MIXED
            // arith+bounds body. Never a blanket single-kind assertion again.
            let slug = obligation
                .source
                .as_ref()
                .unwrap()
                .assertion_id
                .rsplitn(3, '#')
                .nth(1)
                .expect("identity carries #slug#occ");
            assert_eq!(
                obligation.kind,
                obligation_kind_for_slug(slug).expect("installed slug maps"),
                "row kind must equal the map of its slug ({slug})"
            );
            assert!(obligation.formula.is_none(), "no formula below Step 6");
            let source = obligation.source.as_ref().unwrap();
            assert_eq!(source.source_id, DIRECT_ASSERT_SOURCE_ID);
            assert!(source.public.is_none(), "no public identity below the request tier");
            assert_eq!(source.range.unwrap().file, 0);
            assert!(
                obligation.description.contains("RECORDED BY THE LOWERING, NOT PROVED"),
                "description must state a claim: {}",
                obligation.description
            );
            // The site must resolve to the recorded Assert (independent
            // re-resolution — the installer's own self-check is not trusted
            // to grade itself).
            let site = obligation.site.expect("site bound at emission");
            assert_eq!(Some(site.function), obligation.function);
            let node = module
                .functions
                .iter()
                .find(|f| f.id == site.function)
                .and_then(|f| f.blocks.iter().find(|b| b.id == site.block))
                .and_then(|b| b.body.get(site.inst_index as usize))
                .expect("site resolves");
            assert!(
                matches!(node.inst, Inst::Assert { .. }),
                "site must name the Assert, found {:?}",
                node.inst
            );
        }

        // B2 (Step 5): the bounds row specifically — kind BoundsCheck, the
        // frontend's phrase verbatim, `#bounds_check#o0` identity (asserted in
        // the ids vec above), and the tier arm accepts the mixed module below.
        let bounds_row = module.proof_obligations.last().unwrap();
        assert_eq!(bounds_row.kind, ObligationKind::BoundsCheck);
        assert!(
            bounds_row.description.contains("index is in bounds"),
            "the bounds phrase must be the frontend's, verbatim: {}",
            bounds_row.description
        );

        assert_eq!(
            inventory_errors_at_tier(&module, DirectObligationTier::ObligationBearingPending),
            Vec::<String>::new(),
        );
        // ... while the OLD tier's zero-check still refuses the module — the
        // pre-birth semantics did not silently move with the new tier.
        assert_eq!(
            inventory_errors_at_tier(&module, DirectObligationTier::StructuralParityOnly).len(),
            1
        );
        assert_eq!(obligation_validation_errors(&module), Vec::<String>::new());
    }

    /// IDENTITY STABILITY (the design decision under test): re-record the
    /// same three source checks at DIFFERENT block/instruction positions —
    /// an unrelated statement permutation / lowering change — and the minted
    /// identities must be unchanged, because block/inst indexes are
    /// positional (site) data, never identity.
    #[test]
    fn identity_is_stable_when_unrelated_statements_permute() {
        let (mut base_module, base_registry, assigned) = fixture_module();
        let mut errors = Vec::new();
        install_direct_obligations(
            &mut base_module,
            FIXTURE_CRATE,
            &assigned,
            base_registry,
            &mut errors,
        );
        assert_eq!(errors, Vec::<String>::new());
        let base_ids: Vec<String> = base_module
            .proof_obligations
            .iter()
            .map(|o| o.source.as_ref().unwrap().assertion_id.clone())
            .collect();

        // Same source checks, permuted lowering: two padding instructions
        // inserted ahead, asserts shifted to 4/5/6, block renumbered to 3.
        let (mut module, _, _) = fixture_module();
        {
            let function = &mut module.functions[0];
            let block = &mut function.blocks[0];
            block.id = BlockId::new(3);
            function.entry = BlockId::new(3);
            let pad0 = InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(7) })
                .with_result(ValueId::new(3));
            let pad1 = InstrNode::new(Inst::Const { ty: Ty::I32, value: Constant::Int(9) })
                .with_result(ValueId::new(4));
            block.body.insert(0, pad1);
            block.body.insert(0, pad0);
        }
        let loc = Some(SourceSpan { file: 0, line: 15, col: 4 });
        let range = Some(DirectSourceRange {
            start_line: 15,
            start_col: 4,
            end_line: 15,
            end_col: 11,
        });
        let mut registry = DirectObligationRegistry::default();
        registry.insert(DirectBodyObligations {
            def_index: 7,
            def_path: FIXTURE_PATH.to_string(),
            records: [
                (SLUG_DIV_BY_ZERO, ProofAnnotation::DivNonZero, 4u32),
                (SLUG_OVERFLOW, ProofAnnotation::NoOverflow, 5u32),
                (SLUG_OVERFLOW, ProofAnnotation::NoOverflow, 6u32),
                (SLUG_BOUNDS_CHECK, ProofAnnotation::InBounds, 7u32),
            ]
            .into_iter()
            .map(|(slug, annotation, inst_index)| DirectObligationRecord {
                slug,
                annotation,
                loc,
                block: BlockId::new(3),
                inst_index,
                range,
                formula: DirectFormulaOutcome::NotMinted,
            })
            .collect(),
        });
        let mut errors = Vec::new();
        install_direct_obligations(&mut module, FIXTURE_CRATE, &assigned, registry, &mut errors);
        assert_eq!(errors, Vec::<String>::new());
        let permuted_ids: Vec<String> = module
            .proof_obligations
            .iter()
            .map(|o| o.source.as_ref().unwrap().assertion_id.clone())
            .collect();

        assert_eq!(
            base_ids, permuted_ids,
            "identity must be stable across lowering-position changes; only the \
             ObligationSite may move"
        );
        // And the sites DID move — the permutation was real.
        assert_eq!(module.proof_obligations[0].site.unwrap().inst_index, 4);
        assert_eq!(module.proof_obligations[0].site.unwrap().block, BlockId::new(3));
    }

    /// Two checks on one line: distinct identities. The same-slug pair
    /// separates on the occ ordinal alone; the cross-slug pair separates on
    /// the slug axis. This is the axis the measured signed-div pair and
    /// pin 4's add3 pair require.
    #[test]
    fn two_checks_on_one_line_get_distinct_identities() {
        let (mut module, registry, assigned) = fixture_module();
        let mut errors = Vec::new();
        install_direct_obligations(&mut module, FIXTURE_CRATE, &assigned, registry, &mut errors);
        assert_eq!(errors, Vec::<String>::new());
        let ids: Vec<String> = module
            .proof_obligations
            .iter()
            .map(|o| o.source.as_ref().unwrap().assertion_id.clone())
            .collect();
        let mut deduped = ids.clone();
        deduped.sort();
        deduped.dedup();
        assert_eq!(deduped.len(), ids.len(), "same-line checks must not collide: {ids:?}");
        assert!(ids[1].ends_with("#o0") && ids[2].ends_with("#o1"));
    }

    /// Re-running the install over an already-installed module must refuse
    /// every row on the duplicate-identity belt — the fail-closed check that
    /// also serves as the mutation tripwire for an occ removal.
    #[test]
    fn reinstalling_the_same_registry_is_refused_as_duplicate_identity() {
        let (mut module, registry, assigned) = fixture_module();
        let mut errors = Vec::new();
        install_direct_obligations(&mut module, FIXTURE_CRATE, &assigned, registry, &mut errors);
        assert_eq!(errors, Vec::<String>::new());

        let (_, registry_again, _) = fixture_module();
        let outcome = install_direct_obligations(
            &mut module,
            FIXTURE_CRATE,
            &assigned,
            registry_again,
            &mut errors,
        );
        assert_eq!(outcome.installed, 0);
        assert_eq!(errors.len(), 4);
        assert!(errors[0].contains("duplicate obligation identity"), "{}", errors[0]);
    }

    /// A row whose status is not Pending — or that carries a formula or a
    /// public identity, or a foreign source id — fails the NEW tier's
    /// tripwire. Certificates stay rejected outright. This is the tier's
    /// fail-closed half: obligations may exist, verdicts may not.
    #[test]
    fn discharged_or_decorated_rows_fail_the_new_tier_tripwire() {
        let (mut module, registry, assigned) = fixture_module();
        let mut errors = Vec::new();
        install_direct_obligations(&mut module, FIXTURE_CRATE, &assigned, registry, &mut errors);
        assert_eq!(errors, Vec::<String>::new());

        // Discharged.
        let mut poisoned = module.clone();
        poisoned.proof_obligations[0].status = ProofStatus::Discharged;
        let errors =
            inventory_errors_at_tier(&poisoned, DirectObligationTier::ObligationBearingPending);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].contains("status discharged (must be pending)"), "{}", errors[0]);

        // Certified.
        let mut poisoned = module.clone();
        poisoned.proof_obligations[1].status = ProofStatus::Certified;
        assert!(
            inventory_errors_at_tier(&poisoned, DirectObligationTier::ObligationBearingPending)
                [0]
            .contains("status certified"),
        );

        // Formula.
        let mut poisoned = module.clone();
        poisoned.proof_obligations[0].formula =
            Some(trust_ir::ProofFormula::new("smtlib2", "(assert true)"));
        assert!(
            inventory_errors_at_tier(&poisoned, DirectObligationTier::ObligationBearingPending)
                [0]
            .contains("carries a formula"),
        );

        // Public identity.
        let mut poisoned = module.clone();
        poisoned.proof_obligations[0].source.as_mut().unwrap().public =
            Some(trust_ir::PublicObligationIdentity {
                obligation_id: "vc:fixture__arith__checked:arithmetic_safety:0".to_string(),
                semantic_digest: trust_ir::ProofDigest::sha256([0x51; 32]),
            });
        assert!(
            inventory_errors_at_tier(&poisoned, DirectObligationTier::ObligationBearingPending)
                [0]
            .contains("public obligation identity"),
        );

        // Foreign source id.
        let mut poisoned = module.clone();
        poisoned.proof_obligations[0].source.as_mut().unwrap().source_id =
            "trust-ir-frontend/mir-assert@1".to_string();
        assert!(
            inventory_errors_at_tier(&poisoned, DirectObligationTier::ObligationBearingPending)
                [0]
            .contains("foreign source_id"),
        );

        // A certificate — rejected at BOTH tiers.
        let mut poisoned = module.clone();
        poisoned.proof_certificates.push(trust_ir::ProofCertificate {
            obligation: ProofId::new(0),
            prover: "manual".to_string(),
            evidence: trust_ir::ProofEvidence::Trusted("manual".to_string()),
            assurance: None,
        });
        assert!(
            inventory_errors_at_tier(&poisoned, DirectObligationTier::ObligationBearingPending)
                [0]
            .contains("certificates 1"),
        );
    }

    /// B3 (Step 5, the M-THIRD-KIND pin): the tier arm's kind allowlist is
    /// EXACTLY {ArithmeticSafety, BoundsCheck} — no wider. A Pending
    /// `Postcondition` and a Pending `PanicFreedom` (the nearest-neighbour
    /// kind a careless widening would admit — bounds checks ROUTE like
    /// panic-freedom, but the direct lane does not mint it) each fire exactly
    /// the kind violation under the direct source_id, while both admitted
    /// kinds pass.
    #[test]
    fn tier_arm_kind_allowlist_is_exactly_the_two_minted_kinds() {
        let (mut module, registry, assigned) = fixture_module();
        let mut errors = Vec::new();
        install_direct_obligations(&mut module, FIXTURE_CRATE, &assigned, registry, &mut errors);
        assert_eq!(errors, Vec::<String>::new());
        // Baseline: the mixed ArithmeticSafety+BoundsCheck module passes.
        assert_eq!(
            inventory_errors_at_tier(&module, DirectObligationTier::ObligationBearingPending),
            Vec::<String>::new(),
        );

        for foreign in [ObligationKind::Postcondition, ObligationKind::PanicFreedom] {
            let mut poisoned = module.clone();
            poisoned.proof_obligations[0].kind = foreign.clone();
            let errors = inventory_errors_at_tier(
                &poisoned,
                DirectObligationTier::ObligationBearingPending,
            );
            assert_eq!(errors.len(), 1, "{foreign:?} must fire exactly one row violation");
            assert!(
                errors[0]
                    .contains("the direct lane mints ArithmeticSafety and BoundsCheck only"),
                "{foreign:?}: {}",
                errors[0]
            );
            assert!(
                errors[0].contains(&format!("kind {foreign:?}")),
                "the violation must name the foreign kind: {}",
                errors[0]
            );
        }
    }

    /// Step 6 pin 1: a record carrying a MINTED session formula installs a
    /// row that is still formula-free, the new tier's tripwire still accepts
    /// the module, and the mint is visible ONLY through the disclosure
    /// counters. This is the "rows stay formula-free" half of the design of
    /// record — the (identity, formula) pair lives in session state, never on
    /// the artifact.
    #[test]
    fn install_never_copies_a_minted_formula_onto_a_row() {
        let (mut module, _, assigned) = fixture_module();
        let minted = trust_ir_bridge::safety_formulas::mint_direct_safety_formula(
            &trust_ir_bridge::safety_formulas::DirectFormulaClass::DivByZero,
            32,
            true,
            &[trust_ir_bridge::safety_formulas::DirectFormulaOperand::Named {
                name: "divisor".to_string(),
            }],
        )
        .expect("a named-divisor div-zero mint is in-envelope");
        let mut registry = DirectObligationRegistry::default();
        registry.insert(DirectBodyObligations {
            def_index: 7,
            def_path: FIXTURE_PATH.to_string(),
            records: vec![
                DirectObligationRecord {
                    slug: SLUG_DIV_BY_ZERO,
                    annotation: ProofAnnotation::DivNonZero,
                    loc: Some(SourceSpan { file: 0, line: 15, col: 4 }),
                    block: BlockId::new(0),
                    inst_index: 2,
                    range: None,
                    formula: DirectFormulaOutcome::Minted(minted),
                },
                DirectObligationRecord {
                    slug: SLUG_OVERFLOW,
                    annotation: ProofAnnotation::NoOverflow,
                    loc: Some(SourceSpan { file: 0, line: 15, col: 4 }),
                    block: BlockId::new(0),
                    inst_index: 3,
                    range: None,
                    formula: DirectFormulaOutcome::Withheld { reason: "opaque-operand" },
                },
            ],
        });
        let mut errors = Vec::new();
        let outcome = install_direct_obligations(
            &mut module,
            FIXTURE_CRATE,
            &assigned,
            registry,
            &mut errors,
        );
        assert_eq!(errors, Vec::<String>::new());
        assert_eq!(outcome.installed, 2);
        assert_eq!(outcome.formulas_minted, 1);
        assert_eq!(outcome.formulas_withheld, 1);
        assert_eq!(outcome.formulas_not_minted, 0);
        for obligation in &module.proof_obligations {
            assert!(
                obligation.formula.is_none(),
                "a minted session formula must NEVER be copied onto a row"
            );
        }
        assert_eq!(
            inventory_errors_at_tier(&module, DirectObligationTier::ObligationBearingPending),
            Vec::<String>::new(),
            "the formula-free rows must still pass the tier arm"
        );
    }

    /// Step 6 pin 2 (re-assert of the live gate, named per the design of
    /// record): a row that DOES carry a formula — however it got there — is
    /// an inventory error at the obligation-bearing tier. The tier arm, not
    /// installer politeness, is what keeps the module formula-free.
    #[test]
    fn a_formula_bearing_row_is_still_an_inventory_error() {
        let (mut module, registry, assigned) = fixture_module();
        let mut errors = Vec::new();
        install_direct_obligations(&mut module, FIXTURE_CRATE, &assigned, registry, &mut errors);
        assert_eq!(errors, Vec::<String>::new());

        module.proof_obligations[0].formula =
            Some(trust_ir::ProofFormula::new("smtlib2", "(assert true)"));
        let errors =
            inventory_errors_at_tier(&module, DirectObligationTier::ObligationBearingPending);
        assert_eq!(errors.len(), 1, "exactly the formula violation: {errors:?}");
        assert!(errors[0].contains("carries a formula"), "{}", errors[0]);
    }

    /// A dangling site must fail `validate_module` — the format-level belt
    /// underneath the installer's own self-check.
    #[test]
    fn a_dangling_site_fails_validate_module() {
        let (mut module, registry, assigned) = fixture_module();
        let mut errors = Vec::new();
        install_direct_obligations(&mut module, FIXTURE_CRATE, &assigned, registry, &mut errors);
        assert_eq!(errors, Vec::<String>::new());
        assert_eq!(obligation_validation_errors(&module), Vec::<String>::new());

        module.proof_obligations[2].site.as_mut().unwrap().inst_index = 99;
        let validation = obligation_validation_errors(&module);
        assert!(
            validation.iter().any(|e| e.contains("ObligationSiteOutOfRange")),
            "a dangling site must be a hard validation error: {validation:?}"
        );
    }

    /// The installer's structural self-check: a record whose position does
    /// not hold the recorded Assert/annotation withholds the row with an
    /// error — a wrong binding never ships as a plausible-looking row.
    #[test]
    fn install_self_check_refuses_a_position_that_is_not_the_recorded_assert() {
        let (mut module, _, assigned) = fixture_module();
        let mut registry = DirectObligationRegistry::default();
        registry.insert(DirectBodyObligations {
            def_index: 7,
            def_path: FIXTURE_PATH.to_string(),
            records: vec![DirectObligationRecord {
                slug: SLUG_DIV_BY_ZERO,
                annotation: ProofAnnotation::DivNonZero,
                loc: Some(SourceSpan { file: 0, line: 15, col: 4 }),
                block: BlockId::new(0),
                // Points at the ICmp, not the Assert.
                inst_index: 1,
                range: None,
                formula: DirectFormulaOutcome::NotMinted,
            }],
        });
        let mut errors = Vec::new();
        let outcome =
            install_direct_obligations(&mut module, FIXTURE_CRATE, &assigned, registry, &mut errors);
        assert_eq!(outcome.installed, 0);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].contains("structural self-check failed"), "{}", errors[0]);
        assert!(module.proof_obligations.is_empty());
    }

    /// Wrong-annotation at the right position is ALSO a self-check failure:
    /// the annotation is part of the recorded binding, not decoration.
    #[test]
    fn install_self_check_requires_the_recorded_annotation() {
        let (mut module, _, assigned) = fixture_module();
        let mut registry = DirectObligationRegistry::default();
        registry.insert(DirectBodyObligations {
            def_index: 7,
            def_path: FIXTURE_PATH.to_string(),
            records: vec![DirectObligationRecord {
                slug: SLUG_OVERFLOW,
                annotation: ProofAnnotation::ShiftInRange,
                loc: Some(SourceSpan { file: 0, line: 15, col: 4 }),
                block: BlockId::new(0),
                inst_index: 3, // a real Assert, but it carries NoOverflow
                range: None,
                formula: DirectFormulaOutcome::NotMinted,
            }],
        });
        let mut errors = Vec::new();
        let outcome =
            install_direct_obligations(&mut module, FIXTURE_CRATE, &assigned, registry, &mut errors);
        assert_eq!(outcome.installed, 0);
        assert!(errors[0].contains("structural self-check failed"));
    }

    /// Unspliced bodies are skipped with a counted disclosure (their rows
    /// would dangle); span-less records degrade to L0C0 and stay separated
    /// by occ; range misses are counted, never fabricated.
    #[test]
    fn unspliced_bodies_and_missing_spans_are_disclosed_not_guessed() {
        let (mut module, mut registry, assigned) = fixture_module();
        // A second body that never spliced (no assigned entry).
        registry.insert(DirectBodyObligations {
            def_index: 9,
            def_path: "arith::refused".to_string(),
            records: vec![DirectObligationRecord {
                slug: SLUG_OVERFLOW,
                annotation: ProofAnnotation::NoOverflow,
                loc: None,
                block: BlockId::new(0),
                inst_index: 0,
                range: None,
                formula: DirectFormulaOutcome::NotMinted,
            }],
        });
        let mut errors = Vec::new();
        let outcome =
            install_direct_obligations(&mut module, FIXTURE_CRATE, &assigned, registry, &mut errors);
        assert_eq!(errors, Vec::<String>::new());
        assert_eq!(outcome.bodies_skipped_unspliced, 1);
        assert_eq!(outcome.installed, 4, "the refused body contributed nothing");

        // Span-less records: L0C0 with occ separation, no range.
        let (mut module, _, assigned) = fixture_module();
        let mut registry = DirectObligationRegistry::default();
        registry.insert(DirectBodyObligations {
            def_index: 7,
            def_path: FIXTURE_PATH.to_string(),
            records: vec![
                DirectObligationRecord {
                    slug: SLUG_OVERFLOW,
                    annotation: ProofAnnotation::NoOverflow,
                    loc: None,
                    block: BlockId::new(0),
                    inst_index: 3,
                    range: None,
                    formula: DirectFormulaOutcome::NotMinted,
                },
                DirectObligationRecord {
                    slug: SLUG_OVERFLOW,
                    annotation: ProofAnnotation::NoOverflow,
                    loc: None,
                    block: BlockId::new(0),
                    inst_index: 4,
                    range: None,
                    formula: DirectFormulaOutcome::NotMinted,
                },
            ],
        });
        let mut errors = Vec::new();
        let outcome =
            install_direct_obligations(&mut module, FIXTURE_CRATE, &assigned, registry, &mut errors);
        assert_eq!(errors, Vec::<String>::new());
        assert_eq!(outcome.rows_without_range, 2);
        let ids: Vec<String> = module
            .proof_obligations
            .iter()
            .map(|o| o.source.as_ref().unwrap().assertion_id.clone())
            .collect();
        assert_eq!(
            ids,
            vec![
                "fixture::arith::checked#L0C0#overflow#o0",
                "fixture::arith::checked#L0C0#overflow#o1",
            ],
        );
        assert!(module.proof_obligations.iter().all(|o| o
            .source
            .as_ref()
            .unwrap()
            .range
            .is_none()));
    }

    /// A duplicate per-body registration is a wiring defect and fails the
    /// whole install closed — mirroring the body-inventory discipline.
    #[test]
    fn duplicate_body_registration_fails_closed() {
        let (mut module, mut registry, assigned) = fixture_module();
        let (_, second, _) = fixture_module();
        registry.insert(second.bodies.into_values().next().unwrap());
        assert_eq!(registry.duplicate_def_indices, vec![7]);
        let mut errors = Vec::new();
        let outcome =
            install_direct_obligations(&mut module, FIXTURE_CRATE, &assigned, registry, &mut errors);
        assert_eq!(outcome.installed, 0);
        assert!(errors[0].contains("duplicate per-body registrations"), "{}", errors[0]);
    }

    /// The clamp keeps the disambiguating suffix whatever the def path's
    /// length — the frontend's suffix-preservation property, replicated.
    #[test]
    fn assertion_id_clamp_preserves_the_identity_suffix() {
        let long_path = "segment::".repeat(400);
        let id = direct_assertion_id("fixture", &long_path, 15, 4, SLUG_OVERFLOW, 1);
        assert!(id.len() <= PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES);
        assert!(id.ends_with("#L15C4#overflow#o1"), "suffix must survive the clamp: {id}");
        assert!(trust_ir::is_valid_proof_obligation_source_text_id(&id));
    }

    /// Correlation instrument — the measured shapes from the divergence pin:
    /// a Unique 1:1 division pair, add3's 2<->2 ClassOnly overflow group
    /// (one shared LO), and a direct-only group when the MIR side is absent.
    #[test]
    fn correlate_reports_the_measured_cross_lane_shapes() {
        let direct = vec![
            DirectCorrelationRow {
                scope: "fixture::contract_div_index".to_string(),
                slug: SLUG_DIV_BY_ZERO.to_string(),
                line: 7,
                col: 4,
            },
            DirectCorrelationRow {
                scope: "fixture::add3".to_string(),
                slug: SLUG_OVERFLOW.to_string(),
                line: 15,
                col: 4,
            },
            DirectCorrelationRow {
                scope: "fixture::add3".to_string(),
                slug: SLUG_OVERFLOW.to_string(),
                line: 15,
                col: 4,
            },
            DirectCorrelationRow {
                scope: "fixture::macro_div".to_string(),
                slug: SLUG_DIV_BY_ZERO.to_string(),
                line: 26,
                col: 4,
            },
        ];
        let mir = vec![
            MirCorrelationRow {
                obligation_id: "vc:fixture__contract_div_index:arithmetic_safety:1".to_string(),
                description: "division by zero".to_string(),
                line: 7,
                col: 4,
            },
            MirCorrelationRow {
                obligation_id: "vc:fixture__add3:arithmetic_safety:0".to_string(),
                description: "arithmetic overflow (Add)".to_string(),
                line: 15,
                col: 4,
            },
            MirCorrelationRow {
                obligation_id: "vc:fixture__add3:arithmetic_safety:1".to_string(),
                description: "arithmetic overflow (Add)".to_string(),
                line: 15,
                col: 4,
            },
            MirCorrelationRow {
                obligation_id: "not-a-vc-id".to_string(),
                description: "division by zero".to_string(),
                line: 1,
                col: 1,
            },
        ];
        let report = correlate(&direct, &mir);
        assert_eq!(report.unclassified_mir, 1, "the malformed id is disclosed, not guessed");
        assert_eq!(report.unclassified_direct, 0);

        let by_key: BTreeMap<(String, DirectCheckClass), LaneCorrelation> = report
            .groups
            .into_iter()
            .map(|g| ((g.function, g.class), g.verdict))
            .collect();
        assert_eq!(
            by_key[&("fixture__contract_div_index".to_string(), DirectCheckClass::DivZero)],
            LaneCorrelation::Unique,
        );
        assert_eq!(
            by_key[&("fixture__add3".to_string(), DirectCheckClass::Overflow)],
            LaneCorrelation::ClassOnly { direct: 2, mir: 2 },
            "two positions sharing one LO can never be Unique — ordinal alignment is refused"
        );
        assert_eq!(
            by_key[&("fixture__macro_div".to_string(), DirectCheckClass::DivZero)],
            LaneCorrelation::DirectOnly { direct: 1 },
        );
    }

    // ================== Step 6 increment 2: the dump seam ==================
    // Committed pins for the env-gated production dump (run here via the
    // crate's own test target, and in this workflow via the dl_harness
    // scratchpad that #[path]-mounts this file). Env mutation is serialized
    // by ENV_LOCK; each test uses its own crate name so concurrent installs
    // from unrelated tests cannot collide on a dump filename.

    fn env_lock() -> &'static std::sync::Mutex<()> {
        static LOCK: std::sync::OnceLock<std::sync::Mutex<()>> = std::sync::OnceLock::new();
        LOCK.get_or_init(|| std::sync::Mutex::new(()))
    }

    #[allow(unused_unsafe)]
    fn set_dump_env(dir: &std::path::Path) {
        // SAFETY: serialized by env_lock(); the only env mutation in this
        // test binary. (`unsafe` is required on edition 2024; redundant —
        // and allowed — under the edition-2021 harness mount.)
        unsafe {
            std::env::set_var(
                trust_ir_bridge::direct_formula_dump::TRUST_DIRECT_FORMULA_DUMP_ENV,
                dir,
            );
        }
    }

    #[allow(unused_unsafe)]
    fn clear_dump_env() {
        // SAFETY: see set_dump_env.
        unsafe {
            std::env::remove_var(
                trust_ir_bridge::direct_formula_dump::TRUST_DIRECT_FORMULA_DUMP_ENV,
            );
        }
    }

    fn dump_temp_dir(tag: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir()
            .join(format!("direct-dump-seam-{}-{tag}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        dir
    }

    /// A registry whose first record carries a DOCTORED minted formula_json —
    /// valid JSON, whitespace-perturbed away from the canonical render — so
    /// the verbatim-bytes assertion is LOAD-BEARING (kill-mutation W1: a
    /// writer that re-rendered `&minted.formula` would emit canonical bytes
    /// and fail it), plus a withheld and a not-minted record.
    fn doctored_registry() -> (DirectObligationRegistry, String) {
        let minted = trust_ir_bridge::safety_formulas::mint_direct_safety_formula(
            &trust_ir_bridge::safety_formulas::DirectFormulaClass::DivByZero,
            32,
            true,
            &[trust_ir_bridge::safety_formulas::DirectFormulaOperand::Named {
                name: "divisor".to_string(),
            }],
        )
        .expect("named-divisor div-zero mint is in-envelope");
        let doctored_json = minted.formula_json.replacen('[', " [", 1);
        assert_ne!(doctored_json, minted.formula_json, "perturbation must change bytes");
        let doctored = trust_ir_bridge::safety_formulas::MintedDirectFormula {
            formula: minted.formula.clone(),
            formula_json: doctored_json.clone(),
            smtlib: minted.smtlib.clone(),
        };
        let loc = Some(SourceSpan { file: 0, line: 15, col: 4 });
        let mut registry = DirectObligationRegistry::default();
        registry.insert(DirectBodyObligations {
            def_index: 7,
            def_path: FIXTURE_PATH.to_string(),
            records: vec![
                DirectObligationRecord {
                    slug: SLUG_DIV_BY_ZERO,
                    annotation: ProofAnnotation::DivNonZero,
                    loc,
                    block: BlockId::new(0),
                    inst_index: 2,
                    range: None,
                    formula: DirectFormulaOutcome::Minted(doctored),
                },
                DirectObligationRecord {
                    slug: SLUG_OVERFLOW,
                    annotation: ProofAnnotation::NoOverflow,
                    loc,
                    block: BlockId::new(0),
                    inst_index: 3,
                    range: None,
                    formula: DirectFormulaOutcome::Withheld { reason: "opaque-operand" },
                },
                DirectObligationRecord {
                    slug: SLUG_OVERFLOW,
                    annotation: ProofAnnotation::NoOverflow,
                    loc,
                    block: BlockId::new(0),
                    inst_index: 4,
                    range: None,
                    formula: DirectFormulaOutcome::NotMinted,
                },
            ],
        });
        (registry, doctored_json)
    }

    /// The composite seam pin: strictly opt-in (no file when unset — and the
    /// env is re-read per call, so unset-after-set writes nothing: W4),
    /// verbatim bytes (W1), row/identity parity with the installed rows, and
    /// byte-identical module + outcome with the var SET vs UNSET.
    #[test]
    fn dump_is_opt_in_writes_verbatim_bytes_and_changes_no_module_bytes() {
        let _guard = env_lock().lock().unwrap();
        let crate_name = "dumpseam_w1";
        let dir = dump_temp_dir("w1");
        let dump_path = dir.join(format!("{crate_name}.direct-formulas.jsonl"));
        let _ = std::fs::remove_file(&dump_path);

        // Run 1: var UNSET — no file, baseline bytes.
        clear_dump_env();
        let (mut module_off, _, assigned) = fixture_module();
        let (registry, doctored_json) = doctored_registry();
        let mut errors = Vec::new();
        let outcome_off = install_direct_obligations(
            &mut module_off,
            crate_name,
            &assigned,
            registry,
            &mut errors,
        );
        assert_eq!(errors, Vec::<String>::new());
        assert!(!dump_path.exists(), "unset env must write nothing");
        let bytes_off = trust_ir::binary::serialize_module(&module_off);

        // Run 2: var SET — file appears; module/outcome unmoved.
        set_dump_env(&dir);
        let (mut module_on, _, assigned) = fixture_module();
        let (registry, _) = doctored_registry();
        let mut errors = Vec::new();
        let outcome_on = install_direct_obligations(
            &mut module_on,
            crate_name,
            &assigned,
            registry,
            &mut errors,
        );
        assert_eq!(errors, Vec::<String>::new());
        assert_eq!(outcome_on, outcome_off, "the dump must not move the outcome");
        assert_eq!(
            trust_ir::binary::serialize_module(&module_on),
            bytes_off,
            "the dump must change no module bytes"
        );

        let text = std::fs::read_to_string(&dump_path).expect("dump file written");
        let records = trust_ir_bridge::direct_formula_dump::parse_direct_formula_dump(&text)
            .expect("the production writer must produce a parseable sealed file");
        assert_eq!(
            records.len(),
            outcome_on.formulas_minted
                + outcome_on.formulas_withheld
                + outcome_on.formulas_not_minted,
            "one dump row per walked record — the counters' own N"
        );
        // W1 load-bearing: the doctored bytes must survive VERBATIM.
        let trust_ir_bridge::direct_formula_dump::DumpedOutcome::Minted { formula, .. } =
            &records[0].outcome
        else {
            panic!("first record must be the minted one");
        };
        assert_eq!(
            formula.get(),
            doctored_json,
            "dump must embed formula_json verbatim, never a re-render"
        );
        // Identity parity: dumped (occ, assertion_id) match the installed
        // rows one-to-one, in order.
        let installed_ids: Vec<&str> = module_on
            .proof_obligations
            .iter()
            .map(|o| o.source.as_ref().unwrap().assertion_id.as_str())
            .collect();
        let dumped_ids: Vec<&str> =
            records.iter().map(|r| r.assertion_id.as_str()).collect();
        assert_eq!(dumped_ids, installed_ids, "one minted identity, shared by dump and row");
        assert_eq!(
            records.iter().map(|r| r.occ).collect::<Vec<_>>(),
            vec![0, 0, 1],
            "dumped occ is the installed occ, verbatim"
        );

        // Run 3 (W4): var UNSET AGAIN — a fresh install writes nothing. An
        // env value cached through a OnceLock would still write here.
        std::fs::remove_file(&dump_path).expect("remove run-2 file");
        clear_dump_env();
        let (mut module_again, _, assigned) = fixture_module();
        let (registry, _) = doctored_registry();
        let mut errors = Vec::new();
        install_direct_obligations(
            &mut module_again,
            crate_name,
            &assigned,
            registry,
            &mut errors,
        );
        assert_eq!(errors, Vec::<String>::new());
        assert!(
            !dump_path.exists(),
            "the env must be re-read per call: unset-after-set writes NOTHING"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// W2 hook placement: a record whose structural self-check FAILS (row
    /// withheld, install error) is still dumped — the dump describes what the
    /// lowering minted, so its row count is the counters' N, not the
    /// installed N-1.
    #[test]
    fn dump_covers_walked_records_including_self_check_withheld_rows() {
        let _guard = env_lock().lock().unwrap();
        let crate_name = "dumpseam_w2";
        let dir = dump_temp_dir("w2");
        let dump_path = dir.join(format!("{crate_name}.direct-formulas.jsonl"));
        let _ = std::fs::remove_file(&dump_path);

        set_dump_env(&dir);
        let (mut module, _, assigned) = fixture_module();
        let loc = Some(SourceSpan { file: 0, line: 15, col: 4 });
        let mut registry = DirectObligationRegistry::default();
        registry.insert(DirectBodyObligations {
            def_index: 7,
            def_path: FIXTURE_PATH.to_string(),
            records: vec![
                DirectObligationRecord {
                    slug: SLUG_DIV_BY_ZERO,
                    annotation: ProofAnnotation::DivNonZero,
                    loc,
                    block: BlockId::new(0),
                    inst_index: 2,
                    range: None,
                    formula: DirectFormulaOutcome::NotMinted,
                },
                DirectObligationRecord {
                    slug: SLUG_OVERFLOW,
                    annotation: ProofAnnotation::NoOverflow,
                    loc,
                    block: BlockId::new(0),
                    // Points at the ICmp — the self-check withholds this row.
                    inst_index: 1,
                    range: None,
                    formula: DirectFormulaOutcome::NotMinted,
                },
            ],
        });
        let mut errors = Vec::new();
        let outcome = install_direct_obligations(
            &mut module,
            crate_name,
            &assigned,
            registry,
            &mut errors,
        );
        clear_dump_env();
        assert_eq!(outcome.installed, 1, "the self-check withheld one row");
        assert_eq!(errors.len(), 1);
        assert!(errors[0].contains("structural self-check failed"), "{}", errors[0]);

        let text = std::fs::read_to_string(&dump_path).expect("dump file written");
        let records = trust_ir_bridge::direct_formula_dump::parse_direct_formula_dump(&text)
            .expect("parseable");
        assert_eq!(
            records.len(),
            2,
            "BOTH walked records dumped — the withheld row included (W2: a dump emit \
             below the self-check `continue` would drop it)"
        );
        assert!(records[1].assertion_id.contains("#overflow#o0"), "{}", records[1].assertion_id);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// B5 (Step 5): the bounds class pairs across the lanes. The slug maps to
    /// `Bounds`, the MIR vcgen description ("index out of bounds ...") already
    /// recovered it, and `correlate()` grades a matching-position pair Unique
    /// — the designed-in hole (`Bounds` reachable from the MIR side only) is
    /// closed.
    #[test]
    fn bounds_class_correlates_across_the_lanes() {
        assert_eq!(check_class_for_slug(SLUG_BOUNDS_CHECK), Some(DirectCheckClass::Bounds));
        assert_eq!(
            check_class_from_mir_description("index out of bounds: the length is move _4"),
            Some(DirectCheckClass::Bounds)
        );

        let direct = vec![DirectCorrelationRow {
            scope: "fixture::read_at".to_string(),
            slug: SLUG_BOUNDS_CHECK.to_string(),
            line: 9,
            col: 4,
        }];
        let mir = vec![MirCorrelationRow {
            obligation_id: "vc:fixture__read_at:bounds_check:0".to_string(),
            description: "index out of bounds: the length is move _4".to_string(),
            line: 9,
            col: 4,
        }];
        let report = correlate(&direct, &mir);
        assert_eq!(report.unclassified_direct, 0);
        assert_eq!(report.unclassified_mir, 0);
        assert_eq!(report.groups.len(), 1);
        assert_eq!(report.groups[0].class, DirectCheckClass::Bounds);
        assert_eq!(report.groups[0].verdict, LaneCorrelation::Unique);
    }

    /// M2 — the FIXED constant-index arm's train + record
    /// (`const_index_bounds.rs::emit_and_record_const_index_bounds`),
    /// replicated node for node in the order the helper pushes (the Step-5
    /// oracle style: build the emission's exact module shape, install, then
    /// RESOLVE — never trust `is_some()`):
    ///
    ///   0 Const Usize K   1 Const Usize N   2 ICmp Ult(K, N)
    ///   3 Assert(InBounds)   4 Return          record at inst_index 3
    ///
    /// Pins, each load-bearing: install births exactly one Pending
    /// `BoundsCheck` row with the `#bounds_check#o0` identity; the recorded
    /// site resolves to the `Assert` (installer self-check, re-resolved here
    /// independently); the assert's condition chain names the RIGHT len —
    /// `Ult`'s rhs is `Const Usize N` with N == the array length — and the
    /// RIGHT index (K, in bounds). The vacuity guards run the two designed
    /// mutations in-test: a len-skewed train fails the len oracle, and a
    /// site-drifted record fails the installer's structural self-check.
    #[test]
    fn m2_const_index_bounds_train_installs_and_names_the_right_len() {
        const K: i128 = 3;
        const N: i128 = 7;

        // Build the helper's exact emission over a minimal valid function.
        let build = |len_const: i128, assert_index: u32| {
            let mut module = Module::new("cidx");
            module.files.push("src/cidx.rs".to_string());
            let ty = module
                .add_func_type(FuncTy {
                    params: vec![],
                    returns: Vec::new(),
                    is_vararg: false,
                    abi: None,
                })
                .expect("Module::add_func_type: test fixture");
            let fid = FuncId::new(0);
            let mut function = Function::new(fid, "cidx::read3".to_string(), ty, BlockId::new(0));
            let mut block = trust_ir::Block::new(BlockId::new(0));
            let span = SourceSpan { file: 0, line: 2, col: 35 };
            let mut push = |block: &mut trust_ir::Block, mut node: InstrNode| {
                node.span = Some(span);
                block.body.push(node);
            };
            push(
                &mut block,
                InstrNode::new(Inst::Const { ty: Ty::Usize, value: Constant::Int(K) })
                    .with_result(ValueId::new(0)),
            );
            push(
                &mut block,
                InstrNode::new(Inst::Const { ty: Ty::Usize, value: Constant::Int(len_const) })
                    .with_result(ValueId::new(1)),
            );
            push(
                &mut block,
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ult,
                    ty: Ty::Usize,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
            );
            push(
                &mut block,
                InstrNode::new(Inst::Assert {
                    cond: ValueId::new(2),
                    kind: trust_ir::AssertKind::BoundsCheck {
                        index: ValueId::new(0),
                        len: ValueId::new(1),
                    },
                    site: None,
                })
                .with_proof(ProofAnnotation::InBounds),
            );
            block.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
            function.blocks.push(block);
            module.try_add_function(function).expect("Module::try_add_function: test fixture");

            let mut registry = DirectObligationRegistry::default();
            registry.insert(DirectBodyObligations {
                def_index: 3,
                def_path: "read3".to_string(),
                records: vec![DirectObligationRecord {
                    slug: SLUG_BOUNDS_CHECK,
                    annotation: ProofAnnotation::InBounds,
                    loc: Some(span),
                    block: BlockId::new(0),
                    inst_index: assert_index,
                    range: Some(DirectSourceRange {
                        start_line: 2,
                        start_col: 35,
                        end_line: 2,
                        end_col: 39,
                    }),
                    formula: DirectFormulaOutcome::NotMinted,
                }],
            });
            (module, registry, vec![(3u32, fid)])
        };

        // The len oracle: resolve the assert's condition chain and return
        // the (index, len) constants it compares — `None` if any link of the
        // designed shape is missing.
        let resolve_bounds_operands = |module: &Module| -> Option<(i128, i128)> {
            let function = module.functions.first()?;
            let block = function.blocks.first()?;
            let assert_cond = block.body.iter().find_map(|node| match &node.inst {
                Inst::Assert { cond, .. } if node.proofs.contains(&ProofAnnotation::InBounds) => {
                    Some(*cond)
                }
                _ => None,
            })?;
            let (lhs, rhs) = block.body.iter().find_map(|node| match &node.inst {
                Inst::ICmp { op: ICmpOp::Ult, ty: Ty::Usize, lhs, rhs }
                    if node.results.contains(&assert_cond) =>
                {
                    Some((*lhs, *rhs))
                }
                _ => None,
            })?;
            let const_of = |value: trust_ir::ValueId| {
                block.body.iter().find_map(|node| match &node.inst {
                    Inst::Const { ty: Ty::Usize, value: Constant::Int(v) }
                        if node.results.contains(&value) =>
                    {
                        Some(*v)
                    }
                    _ => None,
                })
            };
            Some((const_of(lhs)?, const_of(rhs)?))
        };

        // POSITIVE: the train installs and names the right index and len.
        let (mut module, registry, assigned) = build(N, 3);
        let mut errors = Vec::new();
        let outcome =
            install_direct_obligations(&mut module, "cidx", &assigned, registry, &mut errors);
        assert_eq!(errors, Vec::<String>::new());
        assert_eq!(outcome.installed, 1);
        assert_eq!(module.proof_obligations.len(), 1);
        let row = &module.proof_obligations[0];
        assert_eq!(row.status, ProofStatus::Pending);
        assert_eq!(row.kind, ObligationKind::BoundsCheck);
        assert_eq!(
            row.source.as_ref().unwrap().assertion_id,
            "cidx::read3#L2C35#bounds_check#o0"
        );
        let (k, n) = resolve_bounds_operands(&module).expect("the designed train must resolve");
        assert_eq!((k, n), (K, N), "the assert must compare the RIGHT index against the RIGHT len");
        assert!(k < n, "the emission is caller-gated to the in-bounds residue");

        // VACUITY GUARD 1 — len skew: a train whose len constant is not the
        // array length is caught by the oracle, so the oracle can fail.
        let (skewed, _, _) = build(N + 1, 3);
        let (_, skewed_n) = resolve_bounds_operands(&skewed).expect("shape resolves");
        assert_ne!(skewed_n, N, "the len oracle must distinguish a skewed len constant");

        // VACUITY GUARD 2 — site drift (+1): the installer's structural
        // self-check withholds the row, fail closed.
        let (mut drifted, registry, assigned) = build(N, 4);
        let mut errors = Vec::new();
        let outcome =
            install_direct_obligations(&mut drifted, "cidx", &assigned, registry, &mut errors);
        assert_eq!(outcome.installed, 0);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].contains("structural self-check failed"),
            "the drifted site must fail the self-check: {}",
            errors[0]
        );
    }
}
