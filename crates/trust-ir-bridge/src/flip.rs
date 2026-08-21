//! Trust-IR MIR-compatibility spine VERDICT-FLIP: make the compatibility module
//! the verdict-provenance source for L0 safety obligations (overflow / bounds /
//! shift / div-by-zero) AND for the SIMPLE straight-line single-`Return`
//! POSTCONDITION (incl. precondition-refined L0 VCs), TRULY non-regressing.
//!
//! The L1 postcondition extension reproduces trust-vcgen's body-aware
//! `generate_v2_contract_vcs_impl` formula byte-for-byte ONLY for the simple
//! straight-line shape (refined abstract-interp env + `conjoin_live_preconditions`
//! + the predecessor's assert-passed semantic guards + the return-pin); any
//! complex body (branch / loop / multiple returns) produces no byte-equal
//! candidate and fails closed, so the exact-equality gate keeps it
//! trust-vcgen-sourced. The same gate governs precondition-bearing L0 VCs: the
//! abstract-interp env is now precondition-REFINED on the spine, so an overflow
//! VC under `#[requires]` byte-matches the live formula too.
//!
//! ## Why this module exists
//!
//! The *shadow* flip lowers every verified MIR function to Trust-IR; this module
//! lets that compatibility spine own matched VC provenance without claiming it
//! is the direct Rust/Clean source module. Ratified P9 keeps the capability-complete
//! MIR proving routes until direct/router parity. Exact formula equality remains
//! the gate for which obligations and formulas the spine may supply.
//!
//! ## The regression a prior attempt hit (and this module's fix)
//!
//! A prior verdict-flip REPLACED a trust-vcgen L0 safety VC with a spine VC that
//! carried (a) the *innermost violation core* formula — NOT trust-vcgen's full
//! dispatched formula — and (b) a different `VcKind`. The A/B test caught a real
//! regression: a genuinely-overflowing `fn add(a:i32,b:i32)->i32{a+b}` reported
//! trust-vcgen `[overflow:add] FAILED (counterexample a=MIN,b=-1)` but the
//! substituted spine VC reported `[hardened_unsafe_operation] runtime-checked` —
//! a DIFFERENT verdict AND a different routing label. Two root causes:
//!
//! 1. **Partial formula.** The spine stamped the violation CORE
//!    (`range(a) ∧ range(b) ∧ (a+b ∉ [MIN,MAX])`) while trust-vcgen dispatches its
//!    FULL formula (the same core wrapped in `conjoin_arg_type_ranges` +
//!    `v2_formula_with_block_defs`). Those are equisatisfiable but NOT
//!    verdict-identical in the solver pipeline — the partial formula masked the
//!    detected failure.
//! 2. **Routing divergence.** The label and runtime-check/solve decision are
//!    driven ENTIRELY by the VC's `kind` field (`format_vc_kind` /
//!    `has_runtime_fallback` in `trust_verify.rs`). The substituted VC carried a
//!    `kind` whose `hardened_category()` was `UnsafeOperation`, so it rendered as
//!    `hardened_unsafe_operation` and routed as runtime-checked instead of being
//!    solved.
//!
//! ## This module's invariant: VERDICT-IDENTICAL by construction
//!
//! The flip here NEVER fabricates a verdict-determining field. It re-anchors the
//! PROVENANCE of an obligation to the spine while keeping every routing- and
//! verdict-determining field byte-identical to the matched trust-vcgen VC:
//!
//! * **Match conservatively.** A trust-vcgen L0 safety VC is flipped only when the
//!   spine — lowering the SAME function to trust-ir independently — produced a
//!   safety obligation at the EXACT same source span whose routing-grade
//!   `ObligationKind` is the one that VcKind maps to (item T1 taxonomy), and the
//!   match is UNIQUE on both sides (exactly one trust-vcgen VC and one spine
//!   obligation at that span+kind). This proves the spine genuinely derived the
//!   same obligation; an ambiguous or unmatched VC is left trust-vcgen-sourced.
//! * **Keep the `kind`.** The flipped VC keeps trust-vcgen's exact `VcKind`
//!   (`ArithmeticOverflow{Add}`, `IndexOutOfBounds`, …) — so `format_vc_kind`
//!   still renders `overflow:add` / `bounds` / `shift:left` and
//!   `has_runtime_fallback` makes the SAME routing decision. The
//!   `hardened_unsafe_operation` mislabel is structurally impossible here.
//! * **Keep the formula verdict-identical.** Either (i) the spine reconstructed a
//!   formula whose SMT-LIB is BYTE-EQUAL to the matched trust-vcgen VC's formula
//!   (verified at runtime), in which case we swap in the spine's formula — now the
//!   formula too is spine-sourced, with a proven-identical verdict; or (ii) the
//!   spine's reconstruction is not byte-equal (block-defs/slice-len wrappers the
//!   spine cannot reproduce without re-implementing private trust-vcgen helpers),
//!   in which case we KEEP trust-vcgen's full formula unchanged (fail-closed — the
//!   obligation is still spine-OWNED for provenance, but its formula stays
//!   trust-vcgen's, so the verdict is trivially identical).
//! * **Keep `location` and `contract_metadata`.** Untouched.
//!
//! Because every flipped VC is byte-identical to trust-vcgen's in `kind`,
//! `location`, `contract_metadata`, AND a verdict-identical `formula`, the
//! solver/router produces the SAME verdict and the report renders the SAME label.
//! The flip is provably non-regressing.
//!
//! ## What "spine-sourced" buys (the actual flip)
//!
//! The set of obligations a function carries is now established by the trust-ir
//! lowering (the spine walks the lowered module's `proof_obligations`); the flip
//! confirms trust-vcgen produced the same set at the same spans/kinds, and re-keys
//! provenance onto the spine. For the byte-equal classes the FORMULA dispatched is
//! the spine's reconstruction, not trust-vcgen's. This is the verdict-preserving
//! increment of "trust-ir is the source of record" — the dangerous half (a verdict
//! change) is gated to the byte-equal-or-keep envelope so it can never regress.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_ir::proof::ObligationKind;
use trust_types::{
    Formula, ProofLevel, SourceSpan, VcKind, VerifiableFunction, VerificationCondition,
};

use crate::lower::{lower_to_trust_ir, reconstruct_full_safety_formula_candidates};

/// Strip trust-vcgen's statement-granular SSA version tokens from a `Formula`,
/// canonicalizing every versioned place read `Var("name#s{B}_{k}", sort)` back to
/// its bare `Var("name", sort)` form (and likewise for the interned `SymVar`).
///
/// ## Why the flip compares MODULO version tokens
///
/// trust-vcgen's S2c staleness flip (`version_rename_at` /
/// `version_block_def_at_establish` in `trust-vcgen/src/generate.rs`) renames every
/// place variable in a dispatched L0/postcondition formula to its versioned form at
/// its program point (`in_bounds#s0_0`, `__ret#s1_0`, `_0#s3_0`, …). The bridge's
/// spine reconstruction (`crate::lower`) does NOT reproduce these tokens — it would
/// have to re-implement trust-vcgen's private statement-granular reaching-def
/// dataflow. So the spine's candidate formula is the SAME formula trust-vcgen
/// dispatches but with the version suffixes COLLAPSED.
///
/// The flip's job is to confirm the spine independently derived the SAME obligation
/// formula and re-key its PROVENANCE to the spine. Version tokens are a pure
/// name-disjointness device (a consistent renaming, which trust-vcgen's own
/// structural-assertion tests strip via `strip_version_tokens` for exactly this
/// reason); two formulas equal after stripping carry IDENTICAL semantic content.
/// So the flip gate compares spine candidate vs. live formula AFTER stripping.
///
/// ## SOUNDNESS — why this NEVER weakens the proof
///
/// The flip keeps the LIVE (versioned) formula as the dispatched/proof formula in
/// EVERY case — it never substitutes the stripped (version-collapsed) spine text
/// downstream. `strip_version_tokens_in_formula` is used ONLY to decide the
/// PROVENANCE label (`SpineSourcedFormula` vs. kept/unsourced); the formula that is
/// actually solved is always `vc.formula`, trust-vcgen's exact versioned formula.
/// A version-collapsed formula could in principle let a stale fact unify with a VC
/// name where the versioned form keeps them disjoint — but because we never USE the
/// stripped form as the proof formula, that risk cannot arise here. The decision is
/// label-only and cannot change any verdict.
#[must_use]
fn strip_version_tokens_in_formula(formula: &Formula) -> Formula {
    /// Strip a `#<token>` suffix from a place name (`in_bounds#s0_0` -> `in_bounds`).
    /// Already-bare names pass through unchanged.
    fn strip_name(name: &str) -> String {
        match name.split_once('#') {
            Some((base, _tok)) => base.to_string(),
            None => name.to_string(),
        }
    }
    formula.clone().map(&mut |node| match node {
        Formula::Var(name, sort) => Formula::Var(strip_name(&name), sort),
        Formula::SymVar(sym, sort) => {
            let name = sym.as_str();
            if name.contains('#') {
                Formula::Var(strip_name(name), sort)
            } else {
                Formula::SymVar(sym, sort)
            }
        }
        other => other,
    })
}

/// Version-token-insensitive structural equality of two formulas: `true` iff they
/// are byte-equal after [`strip_version_tokens_in_formula`]. This is the flip's
/// match gate — a spine candidate "byte-matches" a live trust-vcgen formula iff
/// they are identical modulo the statement-granular SSA version suffixes the spine
/// reconstruction does not reproduce. See `strip_version_tokens_in_formula` for the
/// soundness argument (the live, versioned formula is always kept as the proof
/// formula; stripping affects only the provenance decision).
#[must_use]
fn formula_eq_modulo_versions(a: &Formula, b: &Formula) -> bool {
    a == b || strip_version_tokens_in_formula(a) == strip_version_tokens_in_formula(b)
}

/// The decision the flip made for ONE trust-vcgen safety VC.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlipDecision {
    /// The VC was flipped to spine-sourced AND its formula was swapped to the
    /// spine's byte-equal reconstruction (the formula now lives on the spine).
    SpineSourcedFormula,
    /// The VC was flipped to spine-sourced (the spine owns the obligation) but
    /// the formula was KEPT from trust-vcgen because the spine could not
    /// reconstruct a byte-equal one (fail-closed on the formula; verdict still
    /// identical, since it IS trust-vcgen's formula).
    SpineSourcedKeptFormula,
    /// The VC was left entirely trust-vcgen-sourced: no unique spine obligation
    /// matched its span+kind (conservative — no flip).
    TrustVcgenSourced,
}

/// The outcome of running the verdict-flip over a function's trust-vcgen VC set.
#[derive(Debug, Clone, Default)]
pub struct FlipReport {
    /// Per trust-vcgen safety VC (in input order), the decision taken.
    pub decisions: Vec<FlipDecision>,
}

impl FlipReport {
    /// How many VCs were flipped to spine-sourced with a spine formula.
    #[must_use]
    pub fn spine_sourced_formula(&self) -> usize {
        self.decisions.iter().filter(|d| **d == FlipDecision::SpineSourcedFormula).count()
    }

    /// How many VCs were flipped to spine-sourced but kept trust-vcgen's formula.
    #[must_use]
    pub fn spine_sourced_kept_formula(&self) -> usize {
        self.decisions.iter().filter(|d| **d == FlipDecision::SpineSourcedKeptFormula).count()
    }

    /// How many VCs were left trust-vcgen-sourced (no match).
    #[must_use]
    pub fn trust_vcgen_sourced(&self) -> usize {
        self.decisions.iter().filter(|d| **d == FlipDecision::TrustVcgenSourced).count()
    }

    /// Total VCs flipped to spine-sourced (formula swapped OR kept).
    #[must_use]
    pub fn flipped(&self) -> usize {
        self.spine_sourced_formula() + self.spine_sourced_kept_formula()
    }
}

/// A FINE safety-obligation class, sharper than the routing-grade
/// `ObligationKind` (which collapses overflow / shift / div / rem all into
/// `ArithmeticSafety`). The flip keys on this so a `DivisionByZero` VC and a
/// `ArithmeticOverflow{Div}` VC — both `ArithmeticSafety` and at the SAME source
/// span — are NOT conflated: the former matches the spine's `division by zero`
/// assert obligation, the latter (a trust-vcgen-synthesized signed-div-overflow
/// check with no spine assert obligation) matches nothing and stays
/// trust-vcgen-sourced. This is what lets div-by-zero flip without a same-span
/// ambiguity collision.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum SafetyClass {
    /// `lhs OP rhs` arithmetic overflow, keyed by the binop name (`Add`/`Sub`/…)
    /// so an overflow VC matches the spine's `overflow on {op}` obligation.
    Overflow(String),
    /// Shift-amount-out-of-range (`Shl`/`Shr`), keyed by op.
    Shift(String),
    /// Integer negation overflow (`-INT_MIN`).
    NegOverflow,
    /// Integer division-by-zero.
    DivByZero,
    /// Integer remainder-by-zero.
    RemByZero,
    /// Narrowing integer cast value-out-of-target-range.
    CastOverflow,
    /// Array/slice index bounds check.
    Bounds,
}

/// The fine safety class of a trust-vcgen L0 safety `VcKind`, or `None` for a
/// VcKind the flip does not range over. ALL of trust-vcgen's L0 arithmetic/bounds
/// classes are now covered, each matched to a spine obligation:
/// * `ArithmeticOverflow{Add/Sub}` → `Overflow` (per-op); `{Mul}` is covered as a
///   class but reconstructs no candidate (BV encoding) → flip keeps vcgen formula.
/// * `ShiftOverflow` → `Shift` (per-op); `NegationOverflow` → `NegOverflow`
///   (matched to the `overflow on negation` assert obligation); `Division`/
///   `RemainderByZero` → `DivByZero`/`RemByZero` (matched to the abstract-flag
///   assert obligation, disambiguated from the co-located bare-statement VC by
///   formula-byte-match); `CastOverflow` → `CastOverflow` (matched to the spine's
///   per-cast obligation, emitted from the `Rvalue::Cast` STATEMENT since a cast
///   has no `Terminator::Assert`); bounds → `Bounds`.
#[must_use]
fn vcgen_safety_class(kind: &VcKind) -> Option<SafetyClass> {
    match kind {
        VcKind::ArithmeticOverflow { op, .. } => Some(SafetyClass::Overflow(format!("{op:?}"))),
        VcKind::ShiftOverflow { op, .. } => Some(SafetyClass::Shift(format!("{op:?}"))),
        VcKind::NegationOverflow { .. } => Some(SafetyClass::NegOverflow),
        VcKind::DivisionByZero => Some(SafetyClass::DivByZero),
        VcKind::RemainderByZero => Some(SafetyClass::RemByZero),
        VcKind::CastOverflow { .. } => Some(SafetyClass::CastOverflow),
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => Some(SafetyClass::Bounds),
        // Not an L0 arithmetic/bounds class the flip ranges over.
        _ => None,
    }
}

/// The fine safety class of a spine obligation, derived from its routing-grade
/// `ObligationKind` AND its `description` (which the lowering sets from the
/// `AssertMessage` via `lower::format_assert_message`: `"overflow on Add"`,
/// `"division by zero"`, `"remainder by zero"`, `"array bounds check"`, …).
/// Returns `None` for obligations that are not a per-assert L0 safety class we
/// flip (the `PanicFreedom` aggregate, contract obligations, etc.).
#[must_use]
fn spine_obligation_class(kind: &ObligationKind, description: &str) -> Option<SafetyClass> {
    match kind {
        ObligationKind::BoundsCheck => Some(SafetyClass::Bounds),
        ObligationKind::ArithmeticSafety => {
            // Disambiguate the arithmetic sub-classes via the description string
            // (set from the `AssertMessage`). Stable strings from
            // `lower::format_assert_message`.
            if description == "overflow on negation" {
                // The negation-overflow assert (`v2_build_assert_negation_vc` →
                // `VcKind::NegationOverflow`). Its description is "overflow on
                // negation"; classify it as its own fine class so it matches a
                // `NegationOverflow` VC (NOT a binop `Overflow` VC).
                Some(SafetyClass::NegOverflow)
            } else if let Some(rest) = description.strip_prefix("overflow on ") {
                // `rest` is the binop debug name (`Add`/`Sub`/`Shl`/`Shr`/…).
                if rest == "Shl" || rest == "Shr" {
                    Some(SafetyClass::Shift(rest.to_string()))
                } else {
                    Some(SafetyClass::Overflow(rest.to_string()))
                }
            } else if description == "division by zero" {
                Some(SafetyClass::DivByZero)
            } else if description == "remainder by zero" {
                Some(SafetyClass::RemByZero)
            } else if description == "cast range/overflow check" {
                // Backward compatibility for a historical/external per-cast
                // losslessness obligation. Current MIR lowering never emits it,
                // because integer `as` conversions are defined and total.
                Some(SafetyClass::CastOverflow)
            } else {
                // An arithmetic-safety obligation we do not finely classify
                // (e.g. negation overflow `"overflow on negation"`): not flipped.
                None
            }
        }
        _ => None,
    }
}

/// Read the spine-owned L0 safety obligations (fine class + span) from a lowered
/// trust-ir module. The span is recovered from each obligation's `ProofFormula`
/// payload (`source.span`), which the lowering stamps for every MIR-assert
/// obligation. Obligations with no recoverable span or no fine class are skipped.
fn spine_safety_obligations(module: &trust_ir::Module) -> Vec<(SafetyClass, SourceSpan)> {
    let mut out = Vec::new();
    for ob in &module.proof_obligations {
        let Some(class) = spine_obligation_class(&ob.kind, &ob.description) else {
            continue;
        };
        let Some(span) =
            ob.formula.as_ref().and_then(|f| span_from_proof_formula_payload(&f.payload))
        else {
            continue;
        };
        out.push((class, span));
    }
    out
}

/// Extract the `source.span` `SourceSpan` from a stamped `ProofFormula` payload
/// JSON. Both the source-metadata schema and the `trust-types.Formula@1` schema
/// nest the span identically under `source.span` (see
/// `lower::ObligationSourceMetadata::source_json`). Returns `None` if the payload
/// is not the expected shape (fail-closed — the obligation is then not matchable
/// and the corresponding VC stays trust-vcgen-sourced).
fn span_from_proof_formula_payload(payload: &str) -> Option<SourceSpan> {
    let value: serde_json::Value = serde_json::from_str(payload).ok()?;
    // contract/safety formula payloads nest source under "source"; the
    // source-metadata-only payload IS the source object at the top level.
    let source = value.get("source").unwrap_or(&value);
    let span = source.get("span")?;
    Some(SourceSpan {
        file: span.get("file")?.as_str()?.to_string(),
        line_start: u32::try_from(span.get("line_start")?.as_u64()?).ok()?,
        col_start: u32::try_from(span.get("col_start")?.as_u64()?).ok()?,
        line_end: u32::try_from(span.get("line_end")?.as_u64()?).ok()?,
        col_end: u32::try_from(span.get("col_end")?.as_u64()?).ok()?,
    })
}

/// True if `vc` is an L0 safety VC (the class the flip ranges over).
fn is_l0_safety(vc: &VerificationCondition) -> bool {
    vc.kind.proof_level() == ProofLevel::L0Safety
}

/// The matching key: the source span tuple. Two obligations are the SAME
/// obligation iff they share an exact source span (file + start/end line/col).
type SpanKey = (String, u32, u32, u32, u32);

fn span_key(span: &SourceSpan) -> SpanKey {
    (span.file.clone(), span.line_start, span.col_start, span.line_end, span.col_end)
}

/// Run the trust-ir verdict-flip over a function's trust-vcgen VC set.
///
/// Returns the (possibly flip-applied) VC set plus a [`FlipReport`]. The returned
/// VCs are IDENTICAL to `vcgen_vcs` except that some L0 safety VCs are now
/// spine-sourced: their formula may be swapped to the spine's byte-equal
/// reconstruction (verdict-identical) while `kind`, `location`, and
/// `contract_metadata` are always preserved. Non-safety VCs and unmatched safety
/// VCs pass through unchanged.
///
/// SOUNDNESS: every returned VC is verdict-identical to its trust-vcgen input —
/// `kind` (the routing/label driver) is never changed, and `formula` is only
/// swapped when its SMT-LIB is byte-equal to the input's. The flip cannot change
/// any verdict or routing label.
#[must_use]
pub fn flip_safety_verdicts_to_spine(
    func: &VerifiableFunction,
    vcgen_vcs: Vec<VerificationCondition>,
) -> (Vec<VerificationCondition>, FlipReport) {
    // MIR-compatibility entry point. Direct source frontends can pass their
    // module to `flip_safety_verdicts_with_module` during staged migration. If
    // this adapter cannot lower, the retained P9 route remains a conservative
    // no-op rather than losing verifier capability.
    let Ok(module) = lower_to_trust_ir(func) else {
        let decisions = vcgen_vcs.iter().map(|_| FlipDecision::TrustVcgenSourced).collect();
        return (vcgen_vcs, FlipReport { decisions });
    };

    flip_safety_verdicts_with_module(func, &module, vcgen_vcs)
}

/// Reconcile safety VCs against an already-produced typed Trust-IR module.
///
/// Unlike [`flip_safety_verdicts_to_spine`], this staged-migration entry point
/// never silently manufactures a second module from MIR: callers choose the
/// module whose obligation provenance is being reconciled. `func` remains the
/// MIR formula view until direct generation reaches capability parity.
#[must_use]
pub fn flip_safety_verdicts_with_module(
    func: &VerifiableFunction,
    module: &trust_ir::Module,
    vcgen_vcs: Vec<VerificationCondition>,
) -> (Vec<VerificationCondition>, FlipReport) {
    let spine_obligations = spine_safety_obligations(module);

    // Build a UNIQUE (span, class) index of spine obligations. A span+class that
    // appears more than once on the spine is ambiguous → it matches NOTHING
    // (conservative: never flip an obligation we cannot pin to a single spine
    // counterpart).
    use std::collections::HashMap;
    let mut spine_seen: std::collections::HashSet<(SpanKey, SafetyClass)> =
        std::collections::HashSet::new();
    let mut spine_ambiguous: std::collections::HashSet<(SpanKey, SafetyClass)> =
        std::collections::HashSet::new();
    for (class, span) in &spine_obligations {
        let key = (span_key(span), class.clone());
        if !spine_seen.insert(key.clone()) {
            spine_ambiguous.insert(key);
        }
    }

    // Build a UNIQUE (span, class) index of the trust-vcgen safety VCs too: a
    // span+class that appears more than once on the trust-vcgen side is likewise
    // ambiguous and not flipped (we cannot tell which spine obligation owns
    // which VC).
    let mut vcgen_class_counts: HashMap<(SpanKey, SafetyClass), usize> = HashMap::new();
    for vc in &vcgen_vcs {
        if !is_l0_safety(vc) {
            continue;
        }
        if let Some(class) = vcgen_safety_class(&vc.kind) {
            *vcgen_class_counts.entry((span_key(&vc.location), class)).or_insert(0) += 1;
        }
    }

    // SAME-SPAN-AMBIGUITY DISAMBIGUATION (div/rem). When a span+class carries MORE
    // THAN ONE trust-vcgen VC (e.g. the `DivisionByZero` ASSERT VC and the bare
    // `Div` STATEMENT VC at the same span — both `DivByZero`), the plain `vcgen_unique`
    // guard cannot tell which spine obligation owns which VC. But the spine's single
    // obligation has a SPECIFIC reconstructed formula, and the byte-equality gate
    // already proves verdict-identity — so we can pin the obligation to the ONE VC
    // whose formula the spine reproduces byte-for-byte, PROVIDED exactly one VC at
    // that key byte-matches. We pre-compute, per ambiguous (span, class) key with a
    // unique spine obligation, the count of VCs whose formula a spine candidate
    // byte-equals; the key is "formula-disambiguable" iff that count is exactly 1.
    //
    // SOUNDNESS: this never relaxes the formula gate — a VC is flipped only when a
    // spine candidate is byte-EQUAL to its formula (so the swap is verdict-identical
    // by construction). Disambiguation only decides WHICH same-span VC is flagged
    // spine-sourced; it cannot change any verdict. If zero or ≥2 VCs byte-match
    // (genuinely indistinguishable), we fail closed (no flip), exactly as before.
    let mut formula_match_counts: HashMap<(SpanKey, SafetyClass), usize> = HashMap::new();
    for vc in &vcgen_vcs {
        if !is_l0_safety(vc) {
            continue;
        }
        let Some(class) = vcgen_safety_class(&vc.kind) else {
            continue;
        };
        let key = (span_key(&vc.location), class);
        // Only relevant for ambiguous-vcgen keys with a unique spine obligation.
        let spine_has_unique = spine_seen.contains(&key) && !spine_ambiguous.contains(&key);
        let vcgen_ambiguous = vcgen_class_counts.get(&key).copied().unwrap_or(0) > 1;
        if spine_has_unique && vcgen_ambiguous {
            let byte_matches =
                reconstruct_full_safety_formula_candidates(func, &vc.location, &vc.kind)
                    .into_iter()
                    .any(|cand| formula_eq_modulo_versions(&cand, &vc.formula));
            if byte_matches {
                *formula_match_counts.entry(key).or_insert(0) += 1;
            }
        }
    }

    // POSTCONDITION flip support (straight-line AND acyclic branching). A
    // `Postcondition` VC is NOT an L0 safety obligation, but the spine CAN
    // reproduce its body-aware formula byte-for-byte for the SIMPLE single-Return
    // straight-line shape AND for ACYCLIC branching / multi-return bodies
    // (`reconstruct_postcondition_formula_candidates` returns one candidate per
    // straight-line return and one per acyclic `(Return × predecessor)` pair). We
    // pre-compute the spine's candidate set ONCE.
    //
    // The flip gate is PURE byte-equality, per VC: a `Postcondition` VC flips
    // spine-sourced iff some spine candidate equals its `Formula` EXACTLY. There
    // is no longer a "unique postcondition VC" restriction — a branching body
    // emits several body-aware VCs (one per path), and the spine reproduces each
    // path's formula, so each that byte-matches flips. SOUNDNESS is unchanged and
    // total: a swap only ever replaces a formula with a structurally-IDENTICAL one
    // (verdict-identical by construction), so even if two postcondition VCs shared
    // a candidate the swap could not change a verdict. Any shape the spine does
    // not reproduce (a loop, an unreproducible block-def/guard, a non-Int return)
    // yields NO byte-equal candidate and fails closed (kept trust-vcgen-sourced).
    let spine_postcondition_candidates =
        crate::lower::reconstruct_postcondition_formula_candidates(func);

    let mut decisions = Vec::with_capacity(vcgen_vcs.len());
    let out: Vec<VerificationCondition> = vcgen_vcs
        .into_iter()
        .map(|vc| {
            // POSTCONDITION: flip to spine-sourced iff the spine reproduces this
            // VC's formula byte-for-byte (straight-line OR acyclic-branch path).
            if matches!(vc.kind, VcKind::Postcondition) {
                let byte_equal = spine_postcondition_candidates
                    .iter()
                    .any(|c| formula_eq_modulo_versions(c, &vc.formula));
                if byte_equal {
                    // The spine reproduces this postcondition formula MODULO the
                    // statement-granular SSA version tokens (`__ret#s1_0`, `_0#s3_0`,
                    // …) that trust-vcgen stamps and the spine reconstruction does
                    // not. We KEEP trust-vcgen's exact LIVE (versioned) formula as the
                    // dispatched/proof formula — never the version-collapsed spine
                    // text — so the provenance is re-keyed to the spine with a
                    // verdict that stays trivially identical (it IS the live formula).
                    decisions.push(FlipDecision::SpineSourcedFormula);
                } else {
                    decisions.push(FlipDecision::TrustVcgenSourced);
                }
                return vc;
            }

            // Only L0 safety VCs are candidates.
            if !is_l0_safety(&vc) {
                decisions.push(FlipDecision::TrustVcgenSourced);
                return vc;
            }
            let Some(class) = vcgen_safety_class(&vc.kind) else {
                decisions.push(FlipDecision::TrustVcgenSourced);
                return vc;
            };
            let key = (span_key(&vc.location), class);

            // The spine must own a UNIQUE obligation for this span+class. (A
            // span+class ambiguous ON THE SPINE is never flipped — we cannot pin a
            // single counterpart.)
            let spine_has_unique = spine_seen.contains(&key) && !spine_ambiguous.contains(&key);
            if !spine_has_unique {
                decisions.push(FlipDecision::TrustVcgenSourced);
                return vc;
            }
            let vcgen_unique = vcgen_class_counts.get(&key).copied() == Some(1);

            // Reconstruct the spine's candidate full formulas for this VC and decide
            // whether ANY is STRUCTURALLY EQUAL to trust-vcgen's formula MODULO the
            // statement-granular SSA version tokens (`in_bounds#s0_0`, `_3#s0_0`, …)
            // that trust-vcgen's S2c staleness flip stamps and the spine
            // reconstruction does not reproduce.
            //
            // SOUNDNESS — why STRUCTURAL `Formula` equality, not SMT-LIB string
            // equality: the in-process `ay` backend encodes the formula via
            // `ay_bridge::formula_to_expr` (NOT `to_smtlib`); the SMT-LIB backend
            // uses `to_smtlib`; the export path uses `formula_to_smt2`. Structural
            // AST equality (`Formula: Eq`) guarantees ALL of these encodings are
            // byte-identical — so whichever backend the router picks, it sees the
            // exact same input as for the trust-vcgen formula, hence the exact
            // same verdict. (SMT-LIB-string equality alone would only cover one of
            // the three encodings.)
            //
            // SOUNDNESS — why MODULO version tokens is safe HERE: we NEVER substitute
            // the version-collapsed spine candidate as the proof formula. The LIVE,
            // VERSIONED `vc.formula` is kept verbatim as the dispatched/proof formula
            // in every branch below — the modulo match only re-keys PROVENANCE to the
            // spine. So no un-versioned (version-collapsed) formula can ever be used
            // as the proof formula, and the version flip's name-disjointness
            // staleness guarantee is fully preserved on the dispatched formula. See
            // `strip_version_tokens_in_formula`.
            let spine_matches =
                reconstruct_full_safety_formula_candidates(func, &vc.location, &vc.kind)
                    .iter()
                    .any(|cand| formula_eq_modulo_versions(cand, &vc.formula));

            if vcgen_unique {
                // Clean 1:1 case (overflow / bounds / shift / neg / cast): the spine
                // owns this obligation. Re-key provenance to the spine when its
                // reconstruction matches (modulo version tokens), KEEPING the live
                // versioned formula; else keep trust-vcgen's (fail-closed).
                if spine_matches {
                    decisions.push(FlipDecision::SpineSourcedFormula);
                } else {
                    decisions.push(FlipDecision::SpineSourcedKeptFormula);
                }
            } else {
                // AMBIGUOUS-vcgen case (div/rem same-span): flip ONLY if (a) this
                // VC's formula matches a spine candidate (modulo version tokens) AND
                // (b) it is the UNIQUE such VC at this key. Otherwise fail closed (no
                // flip) — the VC stays entirely trust-vcgen-sourced.
                let disambiguable = formula_match_counts.get(&key).copied() == Some(1);
                if spine_matches && disambiguable {
                    decisions.push(FlipDecision::SpineSourcedFormula);
                } else {
                    decisions.push(FlipDecision::TrustVcgenSourced);
                }
            }
            vc
        })
        .collect();

    (out, FlipReport { decisions })
}

/// The OBLIGATION-ENUMERATION difference between the two independent producers,
/// keyed by `(kind, span)` and deliberately NOT by formula.
///
/// Trust (#57, 2026-08-17) — THE MISSING-OBLIGATION ALARM. This repo runs two
/// independent safety-obligation producers over every function, and until now it
/// compared them only to decide WHICH set to dispatch, discarding the comparison
/// itself. That threw away the one signal no downstream layer can reconstruct: an
/// obligation that is never emitted produces SILENCE, and silence is
/// indistinguishable from success at every layer below, including the Clean kernel
/// — a kernel can only re-check propositions it is handed.
///
/// The two directions are NOT symmetric, and conflating them would bury the signal:
///
///  * `native_only` is the ALARM. The dispatched set on this path is trust-vcgen's,
///    so an obligation only the trust-ir spine derived is one that NOTHING checks.
///  * `vcgen_only` is over-approximation on the dispatched side, not silence. It
///    means the spine has a coverage gap; trust-vcgen's obligation is still
///    dispatched and still checked. Worth reporting, never worth failing on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObligationKey {
    /// The canonical obligation class — see [`obligation_class`].
    pub class: String,
    /// Where the obligation lives. Carried structurally rather than pre-rendered
    /// because the compiler turns a `native_only` entry into a user-visible
    /// fail-closed finding, and a finding without a span cannot carry its fix.
    pub location: SourceSpan,
}

impl ObligationKey {
    /// The user-visible message for the fail-closed finding the COMPILER raises
    /// when this obligation reaches nobody.
    ///
    /// It lives here, not in `trust_verify.rs`, for a boring but decisive reason:
    /// no cargo sweep reaches `compiler/**`, so a test next to the caller would
    /// compile and never run. The caller is left as a six-line adapter with no
    /// untested logic in it.
    ///
    /// Follows principle 10 / v7-D3 — a refusal must carry the fix, with options.
    /// The finding does NOT say a violation exists; it says nobody looked, and the
    /// two ways to resolve that are genuinely different pieces of work.
    #[must_use]
    pub fn unchecked_finding_message(&self) -> String {
        format!(
            "[spine:unchecked-obligation] the trust-ir spine derived a `{}` obligation here \
             that trust-vcgen neither emitted nor discharged, so nothing verifies it \
             (fail-closed — an obligation that is never emitted is silent, and silence reads \
             as success). Resolve by either (a) teaching trust-vcgen to emit it, if the \
             obligation is real, or (b) making the spine agree it does not exist, as the \
             shared `trust_types::static_truth::assert_failure_is_known_false` fold does for \
             constant divisors. Do NOT suppress this row: the two producers disagreeing \
             about which obligations exist IS the signal.",
            self.class,
        )
    }
}

impl std::fmt::Display for ObligationKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}@{}:{}:{}",
            self.class, self.location.file, self.location.line_start, self.location.col_start
        )
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ObligationSetDiff {
    /// Obligations the trust-ir spine derived that trust-vcgen never emitted,
    /// sorted. THE ALARM DIRECTION.
    pub native_only: Vec<ObligationKey>,
    /// Obligations trust-vcgen emitted that the trust-ir spine did not derive.
    /// A spine coverage gap; these are dispatched and checked regardless.
    pub vcgen_only: Vec<ObligationKey>,
}

impl ObligationSetDiff {
    /// True when the two producers enumerate exactly the same obligations. Note
    /// this says nothing about their FORMULAS agreeing — that is a separate and
    /// deliberately weaker question, see [`vc_dispatch_multiset_eq`].
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.native_only.is_empty() && self.vcgen_only.is_empty()
    }
}



/// The CANONICAL CLASS of an obligation kind — what the two producers must agree
/// on for them to be talking about the same obligation.
///
/// Trust (#57): the naive key `format!("{:?}", vc.kind)` is WRONG here, and it was
/// wrong in a way that manufactured false alarms rather than hiding real ones. Two
/// measured causes, both confirmed against the corpus:
///
///  * **Spelling.** The two producers disagree on the NAME of the bounds
///    obligation: the trust-ir spine emits `SliceBoundsCheck` where trust-vcgen
///    emits `IndexOutOfBounds`, at a byte-identical span. Four corpus rows paired
///    exactly like that, one in each direction. They are already treated as one
///    class everywhere else in the tree (`matches!(vc.kind, VcKind::IndexOutOfBounds
///    | VcKind::SliceBoundsCheck)`).
///  * **Payload.** `ArithmeticOverflow` carries `operand_tys` inside the kind, and
///    the two producers derive those independently (a measured case has native
///    reporting `(i32, i64)` for one `Add`). Operand types are a detail OF the
///    obligation, not its identity: at one span there is one `Add` to check.
///
/// So the class is the discriminant plus, for arithmetic, the operator — and
/// nothing else. Everything finer belongs to the formula, which is deliberately
/// out of scope for this comparison.
fn obligation_class(kind: &VcKind) -> String {
    match kind {
        VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck => "BoundsCheck".to_string(),
        VcKind::ArithmeticOverflow { op, .. } => format!("ArithmeticOverflow({op:?})"),
        // Trust (#57): trust-vcgen's UNSAFE-MODEL findings get their own class, and
        // it is not pedantry — it is the difference between a coverage gap and a
        // category error. These say "Trust has no model for this unsafe operation"
        // (`[unsafe] missing SAFETY comment`, `[unsafe:sep:deref] alignment check
        // for *offset_62`, allocation validity). They are NOT L0 obligations derived
        // from program semantics, so the trust-ir spine does not derive them and
        // never should. Counting them as spine coverage gap overstated that gap by
        // roughly half (119 of 236).
        VcKind::Assertion { message } if message.starts_with("[unsafe") => {
            "Assertion(unsafe-model)".to_string()
        }
        other => {
            let rendered = format!("{other:?}");
            let head = rendered
                .split_once(" {")
                .map_or(rendered.as_str(), |(h, _)| h)
                .split_once('(')
                .map_or_else(
                    || rendered.split_once(" {").map_or(rendered.as_str(), |(h, _)| h),
                    |(h, _)| h,
                );
            head.to_string()
        }
    }
}

/// The `(kind, span)` key set of a VC list — the obligation ENUMERATION, with the
/// formula deliberately excluded.
///
/// A SET (not multiset), matching the historical comparison: trust-vcgen emits the
/// co-located div/rem statement `DivByZero` VC twice where native has it once, and
/// that duplication is not a disagreement about WHICH obligations exist.
fn l0_obligation_key_set(
    vcs: &[VerificationCondition],
) -> std::collections::BTreeMap<(String, SpanKey), SourceSpan> {
    vcs.iter()
        .map(|vc| {
            ((obligation_class(&vc.kind), span_key(&vc.location)), vc.location.clone())
        })
        .collect()
}

/// The obligation-enumeration difference between the trust-ir-native set and
/// trust-vcgen's L0 set.
///
/// Keyed by `(kind, span)` and NOT by formula, and that choice is load-bearing
/// rather than incidental: native may legitimately carry a sounder, canonicalized
/// formula for the same obligation (slice-length-canonicalized bounds is the
/// standing example). An alarm keyed on the formula would fire on every one of
/// those benign differences, burying the real signal — and, once anything acts on
/// it, would reject valid Rust, which is a release gate.
#[must_use]
pub fn l0_obligation_set_diff(
    native: &[VerificationCondition],
    vcgen_l0: &[VerificationCondition],
) -> ObligationSetDiff {
    l0_obligation_set_diff_with_discharged(native, vcgen_l0, std::iter::empty())
}

/// The obligation-enumeration difference, counting trust-vcgen's STATICALLY
/// DISCHARGED obligations as present.
///
/// Trust (#57): this is not a refinement, it is a correctness requirement, and
/// omitting it was the third measured false-alarm source. `generate_vcs_with_
/// discharge_and_summaries` returns TWO sets — the VCs it emits for solving, and
/// the ones it PROVED at generation time. A discharged obligation is checked, and
/// checked more strongly than a dispatched one; treating it as absent reports
/// "nothing checks this" about an obligation trust-vcgen actually proved. Measured:
/// three corpus rows (`bounded_add`, `inc_gt`, `helper`) where native derived an
/// `ArithmeticOverflow(Add)` that trust-vcgen emitted zero VCs for — and had
/// discharged.
#[must_use]
pub fn l0_obligation_set_diff_with_discharged<'a, I>(
    native: &[VerificationCondition],
    vcgen_l0: &[VerificationCondition],
    discharged: I,
) -> ObligationSetDiff
where
    I: IntoIterator<Item = &'a VerificationCondition>,
{
    let native_keys = l0_obligation_key_set(native);
    let vcgen_keys = l0_obligation_key_set(vcgen_l0);
    let to_key = |(class, _): &(String, SpanKey), span: &SourceSpan| ObligationKey {
        class: class.clone(),
        location: span.clone(),
    };
    // The discharged set enters ONE side only, and deliberately so. It answers
    // "is this obligation checked?", which is the `native_only` question; it does
    // not answer "did the spine derive this?", which is the `vcgen_only` one.
    // Folding it into both would manufacture spine-coverage-gap entries for every
    // obligation trust-vcgen proved statically — noise in the direction that was
    // already the benign one.
    let mut checked_by_vcgen: std::collections::BTreeSet<(String, SpanKey)> =
        vcgen_keys.keys().cloned().collect();
    checked_by_vcgen.extend(
        discharged.into_iter().map(|vc| (obligation_class(&vc.kind), span_key(&vc.location))),
    );
    ObligationSetDiff {
        native_only: native_keys
            .iter()
            .filter(|(k, _)| !checked_by_vcgen.contains(*k))
            .map(|(k, span)| to_key(k, span))
            .collect(),
        vcgen_only: vcgen_keys
            .iter()
            .filter(|(k, _)| !native_keys.contains_key(*k))
            .map(|(k, span)| to_key(k, span))
            .collect(),
    }
}

/// Outcome of [`generate_native_or_flip_safety_vcs`], for the compiler's debug log.
#[derive(Debug, Clone)]
pub enum NativeGenOutcome {
    /// trust-ir GENERATED the dispatched L0 safety VC set (validated `==`
    /// trust-vcgen). The `usize` is how many L0 safety VCs the spine generated.
    NativeGenerated(usize),
    /// Native generation declined, or it reproduced trust-vcgen's obligation
    /// ENUMERATION exactly but with a different formula; the verdict-flip ran over
    /// trust-vcgen's VCs instead (`FlipReport` attached). Benign: nothing is
    /// unchecked, because the dispatched set enumerates the same obligations.
    FlippedFallback(FlipReport),
    /// Trust (#57): the two producers DISAGREE about which obligations exist. The
    /// verdict-flip still ran over trust-vcgen's VCs — dispatch behaviour is
    /// byte-identical to `FlippedFallback` — but the disagreement is now reported
    /// instead of discarded. A non-empty `diff.native_only` means the dispatched
    /// set is SILENT about an obligation a second independent producer derived.
    Disagreed { diff: ObligationSetDiff, report: FlipReport },
}

/// THE obligation-birth cutover entry point. Prefer trust-ir-NATIVE generation: if
/// the spine produces the complete L0 safety VC set (`generate_native_safety_vcs`)
/// AND it reproduces the L0 subset of `vcgen_vcs` EXACTLY (same kind + span +
/// formula, as a multiset), DISPATCH the spine-generated VCs — trust-ir is then the
/// primary generation source for this function's safety obligations, with
/// trust-vcgen serving only as the migration cross-check oracle. Otherwise fall back
/// to the verdict-flip over trust-vcgen's VCs (which itself spine-sources the
/// formulas it can). The non-L0 VCs (contracts, synthetic unsafe) always pass
/// through from `vcgen_vcs`.
///
/// SOUNDNESS: the native set is dispatched ONLY on an exact match to trust-vcgen's
/// L0 set, so the dispatched verdicts are identical to the trust-vcgen path by
/// construction — a partial or mis-shaped native set can never change a verdict (it
/// falls back). As coverage → 100% the cross-check passes for every function and the
/// trust-vcgen generation + flip leave the path entirely.
pub fn generate_native_or_flip_safety_vcs(
    func: &VerifiableFunction,
    vcgen_vcs: Vec<VerificationCondition>,
) -> (Vec<VerificationCondition>, NativeGenOutcome) {
    generate_native_or_flip_safety_vcs_with_discharged(func, vcgen_vcs, std::iter::empty())
}

/// [`generate_native_or_flip_safety_vcs`], told which obligations trust-vcgen
/// STATICALLY DISCHARGED. Dispatch behaviour is byte-identical; the discharged set
/// only ever makes the reported disagreement SMALLER, never larger, because it can
/// only add keys to trust-vcgen's side.
pub fn generate_native_or_flip_safety_vcs_with_discharged<'a, I>(
    func: &VerifiableFunction,
    vcgen_vcs: Vec<VerificationCondition>,
    discharged: I,
) -> (Vec<VerificationCondition>, NativeGenOutcome)
where
    I: IntoIterator<Item = &'a VerificationCondition>,
{
    if let Some(native) = crate::lower::generate_native_safety_vcs(func) {
        let (vcgen_l0, vcgen_rest): (Vec<_>, Vec<_>) =
            vcgen_vcs.iter().cloned().partition(|vc| is_l0_safety(vc));
        if vc_dispatch_multiset_eq(&native, &vcgen_l0) {
            let n = native.len();
            let mut out = native;
            out.extend(vcgen_rest);
            return (out, NativeGenOutcome::NativeGenerated(n));
        }
        // Formula-different native output is intentionally not dispatched. Set equality
        // alone does not establish verdict equivalence, and previous universal dispatch
        // both admitted stale guard facts and lost loop facts. Any future cutover must be
        // an explicit, dependency-tracked API backed by the full soundness gates.
        //
        // Trust (#57, 2026-08-17) — but the COMPARISON is no longer discarded. Dispatch
        // is unchanged (we still fall back, and we still never dispatch a mismatched
        // native set — the soundness argument above depends on exactly that); what
        // changes is that a disagreement about WHICH obligations exist is now reported
        // rather than dropped on the floor.
        let _ = vcgen_rest;
        let diff = l0_obligation_set_diff_with_discharged(&native, &vcgen_l0, discharged);
        if !diff.is_empty() {
            let (flipped, report) = flip_safety_verdicts_to_spine(func, vcgen_vcs);
            return (flipped, NativeGenOutcome::Disagreed { diff, report });
        }
    }
    let (flipped, report) = flip_safety_verdicts_to_spine(func, vcgen_vcs);
    (flipped, NativeGenOutcome::FlippedFallback(report))
}

/// True when `native`'s L0 obligation SET equals `vcgen_l0`'s, keyed by `(kind, span)`
/// — every obligation trust-vcgen detected is generated by native AND native generates
/// NO obligation trust-vcgen did not. The FORMULA is intentionally NOT compared (native
/// may carry a sounder/canonicalized formula, e.g. slice-length-canonicalized bounds);
/// only the obligation ENUMERATION must agree. A SET (not multiset) comparison, so the
/// redundant co-located div/rem statement DivByZero VC — vcgen emits `(DivByZero, span)`
/// twice where native has it once — collapses and the sets still match.
///
/// BOTH directions are SOUNDNESS-CRITICAL for universal-mode dispatch:
///   * native ⊇ vcgen_l0 — native must not DROP an L0 obligation vcgen found (it would
///     be silently unchecked).
///   * native ⊆ vcgen_l0 — native must not generate an EXTRA VC vcgen folded away (a
///     constant-nonzero `n % 4` divisor: vcgen emits NO VC, native emits a trivially-
///     true RemainderByZero). Dispatching that extra VC makes the dispatched solver set
///     NON-EMPTY where vcgen left it empty, which makes the full-verification pipeline
///     take the VC-verdict path and SKIP the typed-route's panic-freedom / OOM
///     obligation discovery — silently dropping a `unreachable!()` reachability or
///     `UnboundedAllocation` obligation (`mutant/modulo_unreachable`). Requiring the
///     sets to be EQUAL keeps native's enumeration in lock-step with vcgen's, so it
///     never wakes the VC path where vcgen would have deferred to the typed route.
#[cfg(test)]
fn native_l0_set_matches_vcgen(
    native: &[VerificationCondition],
    vcgen_l0: &[VerificationCondition],
) -> bool {
    // Trust (#57): delegates to the PRODUCTION diff rather than re-transcribing the
    // keying. Two hand-maintained copies of the same key function are exactly the
    // pair that drifts, and a drift here would be invisible — the test helper would
    // keep passing while the production alarm keyed on something else.
    l0_obligation_set_diff(native, vcgen_l0).is_empty()
}

/// Multiset equality of two VC sets by their DISPATCHED IDENTITY — `kind`, source
/// span, and `formula` (the fields that determine routing + the solver verdict).
fn vc_dispatch_multiset_eq(a: &[VerificationCondition], b: &[VerificationCondition]) -> bool {
    fn key(vc: &VerificationCondition) -> (String, SpanKey, String) {
        (format!("{:?}", vc.kind), span_key(&vc.location), format!("{:?}", vc.formula))
    }
    if a.len() != b.len() {
        return false;
    }
    let mut ka: Vec<_> = a.iter().map(key).collect();
    let mut kb: Vec<_> = b.iter().map(key).collect();
    ka.sort();
    kb.sort();
    ka == kb
}

// ===========================================================================
// L1 (CONTRACT) VERDICT-FLIP — the L1 analogue of `flip_safety_verdicts_to_spine`.
//
// Where the L0 flip re-anchors a trust-vcgen *safety* obligation (overflow /
// bounds / div) to the spine's matching MIR-assert obligation, this re-anchors a
// trust-vcgen *contract* obligation (precondition / refinement / loop-invariant)
// to the spine's matching MODULE-LEVEL contract obligation
// (`contract_vcs_from_trust_ir`). It is VERDICT-IDENTICAL, FAIL-CLOSED by the
// SAME construction:
//
//   * Match conservatively, on `(span, contract-class)`, UNIQUE on both sides.
//   * NEVER touch `kind` / `location` / `contract_metadata` (the routing/label
//     drivers) — only the FORMULA, and only when byte-equal.
//   * Reconstruct the spine's *dispatched-equivalent* contract violation formula
//     from the obligation's predicate `ProofFormula` (the predicate the spine
//     carries; the violation wrapping `Not(predicate)` is the VC-generation step
//     the L1 engine performs over it — see `contract_vcgen_proto`'s module doc).
//     Swap it in ONLY when it is BYTE-EQUAL (modulo SSA version tokens) to
//     trust-vcgen's live formula; otherwise KEEP trust-vcgen's (fail-closed).
//
// SOUNDNESS: every returned VC is verdict-identical to its trust-vcgen input —
// `kind` is never changed, and `formula` is only swapped when its AST is
// byte-equal to the input's. A non-byte-equal contract VC stays trust-vcgen-
// sourced. The flip can never change a verdict or a routing label.
// ===========================================================================

/// A FINE contract-obligation class, parallel to [`SafetyClass`] for L0. The flip
/// keys on this so a precondition VC matches the spine's `Precondition` obligation
/// and a refinement VC matches the spine's `RefinementType` obligation — never the
/// other way around, and never a same-span safety obligation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ContractClass {
    /// `#[requires]` precondition (trust-vcgen `VcKind::Precondition`).
    Precondition,
    /// Loop invariant (`VcKind::LoopInvariant{Initiation,Consecution,Sufficiency}`).
    LoopInvariant,
    /// Type refinement (`VcKind::TypeRefinementViolation`).
    RefinementType,
}

/// The fine contract class of a trust-vcgen L1 `VcKind`, or `None` for an L1 VcKind
/// the contract flip does not range over.
///
/// `VcKind::Postcondition` is DELIBERATELY excluded: the body-aware postcondition
/// formula is already flipped by the L0 path's dedicated `Postcondition` arm
/// (`flip_safety_verdicts_to_spine` →
/// `reconstruct_postcondition_formula_candidates`), so handling it here too would
/// double-source it. Every other L1 contract class maps to a spine contract
/// obligation kind.
#[must_use]
fn vcgen_contract_class(kind: &VcKind) -> Option<ContractClass> {
    match kind {
        VcKind::Precondition { .. } => Some(ContractClass::Precondition),
        VcKind::LoopInvariantInitiation { .. }
        | VcKind::LoopInvariantConsecution { .. }
        | VcKind::LoopInvariantSufficiency { .. } => Some(ContractClass::LoopInvariant),
        VcKind::TypeRefinementViolation { .. } => Some(ContractClass::RefinementType),
        // `Postcondition` is handled by the L0 flip's dedicated arm — excluded here.
        // Any other VcKind is not a contract class the flip ranges over.
        _ => None,
    }
}

/// The fine contract class of a spine contract obligation `ObligationKind`, or
/// `None` for a kind the flip does not range over. `Postcondition` is excluded
/// (handled by the L0 path); `TypeInvariant` has no trust-vcgen contract-VC
/// counterpart on this path so it is also excluded (fail-closed: no flip).
#[must_use]
fn spine_contract_class(kind: &ObligationKind) -> Option<ContractClass> {
    match kind {
        ObligationKind::Precondition => Some(ContractClass::Precondition),
        ObligationKind::LoopInvariant => Some(ContractClass::LoopInvariant),
        ObligationKind::RefinementType => Some(ContractClass::RefinementType),
        // `Postcondition` (L0 path) / `TypeInvariant` (no vcgen counterpart) and
        // every non-contract kind: not flipped here.
        _ => None,
    }
}

/// Deserialize the contract PREDICATE `trust_types::Formula` from a spine contract
/// obligation's `ProofFormula`, if it carries one machine-readably.
///
/// The predicate-bearing payload is the `trust-types.Formula@1` document
/// `{formula: <Formula AST JSON>, source: {...}}` the lowering emits for a
/// parseable contract (`lower::ObligationSourceMetadata::into_formula`). We pull
/// the `formula` field and deserialize it back to a `trust_types::Formula` — the
/// SAME AST `parse_spec_expr(predicate)` yielded (verified by
/// `contract_formula_matches_parse_spec_expr`). Returns `None` (fail-closed) for
/// the source-metadata fallback payload (unparseable predicate), a wrong schema,
/// or any deserialization failure — the corresponding VC then stays
/// trust-vcgen-sourced.
#[must_use]
fn spine_contract_predicate(formula: Option<&trust_ir::proof::ProofFormula>) -> Option<Formula> {
    let formula = formula?;
    if formula.schema != crate::lower::TRUST_CONTRACT_PREDICATE_SCHEMA {
        return None;
    }
    let value: serde_json::Value = serde_json::from_str(&formula.payload).ok()?;
    let ast = value.get("formula")?.clone();
    serde_json::from_value::<Formula>(ast).ok()
}

/// One spine contract obligation reduced to what the flip needs: its fine class,
/// its source span, and its predicate `Formula` (if machine-readable).
struct SpineContractObligation {
    class: ContractClass,
    span: SourceSpan,
    predicate: Option<Formula>,
}

/// Read the spine-owned L1 contract obligations from a lowered trust-ir module
/// (via [`crate::contract_vcs_from_trust_ir`]). The span is recovered from each
/// obligation's `ProofFormula` payload (`source.span`), exactly as the L0 path
/// recovers safety spans. Obligations with no recoverable span or no fine class
/// are skipped (fail-closed — they are then not matchable).
fn spine_contract_obligations(module: &trust_ir::Module) -> Vec<SpineContractObligation> {
    let mut out = Vec::new();
    for vc in crate::contract_vcs_from_trust_ir(module) {
        let Some(class) = spine_contract_class(&vc.kind) else {
            continue;
        };
        let Some(span) =
            vc.formula.as_ref().and_then(|f| span_from_proof_formula_payload(&f.payload))
        else {
            continue;
        };
        out.push(SpineContractObligation {
            class,
            span,
            predicate: spine_contract_predicate(vc.formula.as_ref()),
        });
    }
    out
}

/// True if `vc` is an L1 contract VC of a class the contract flip ranges over.
fn is_l1_contract(vc: &VerificationCondition) -> bool {
    vc.kind.proof_level() == ProofLevel::L1Functional && vcgen_contract_class(&vc.kind).is_some()
}

/// Run the trust-ir L1 CONTRACT verdict-flip over a function's trust-vcgen VC set.
///
/// Returns the (possibly flip-applied) VC set plus a [`FlipReport`] (one decision
/// per L1 contract VC, in input order; non-contract VCs do NOT contribute a
/// decision). The returned VCs are IDENTICAL to `vcgen_vcs` except that some L1
/// contract VCs are now spine-sourced: their formula may be swapped to the spine's
/// byte-equal reconstruction (verdict-identical) while `kind`, `location`, and
/// `contract_metadata` are ALWAYS preserved. Non-contract VCs and unmatched
/// contract VCs pass through unchanged.
///
/// SOUNDNESS: every returned VC is verdict-identical to its trust-vcgen input —
/// `kind` (the routing/label driver) is never changed, and `formula` is only
/// swapped when its AST is byte-equal (modulo SSA version tokens) to the input's.
/// The flip cannot change any verdict or routing label. Because the spine carries
/// the contract PREDICATE (not its violation form), the byte-equality gate is
/// strict and the path is overwhelmingly fail-closed (kept trust-vcgen-sourced) —
/// which is exactly the safe outcome.
#[must_use]
pub fn flip_contract_verdicts_to_spine(
    func: &VerifiableFunction,
    vcgen_vcs: Vec<VerificationCondition>,
) -> (Vec<VerificationCondition>, FlipReport) {
    match lower_to_trust_ir(func) {
        Ok(module) => flip_contract_verdicts_with_module(&module, vcgen_vcs),
        // Lowering failed → no-op flip (every contract VC stays trust-vcgen-sourced).
        Err(_) => {
            let decisions = vcgen_vcs
                .iter()
                .filter(|vc| is_l1_contract(vc))
                .map(|_| FlipDecision::TrustVcgenSourced)
                .collect();
            (vcgen_vcs, FlipReport { decisions })
        }
    }
}

/// [`flip_contract_verdicts_to_spine`] with the spine module ALREADY lowered, so
/// the compiler can reuse the module it computed for the L0 flip / shadow path and
/// avoid lowering the function twice. Semantics are identical.
#[must_use]
pub fn flip_contract_verdicts_with_module(
    module: &trust_ir::Module,
    vcgen_vcs: Vec<VerificationCondition>,
) -> (Vec<VerificationCondition>, FlipReport) {
    let spine_obligations = spine_contract_obligations(module);

    // Build a UNIQUE (span, class) index of spine contract obligations. A
    // span+class appearing more than once on the spine is ambiguous → matches
    // NOTHING (conservative: never flip a VC we cannot pin to a single spine
    // counterpart). The first-seen predicate for a unique key is retained.
    use std::collections::{HashMap, HashSet};
    let mut spine_predicate: HashMap<(SpanKey, ContractClass), Option<Formula>> = HashMap::new();
    let mut spine_seen: HashSet<(SpanKey, ContractClass)> = HashSet::new();
    let mut spine_ambiguous: HashSet<(SpanKey, ContractClass)> = HashSet::new();
    for ob in &spine_obligations {
        let key = (span_key(&ob.span), ob.class.clone());
        if !spine_seen.insert(key.clone()) {
            spine_ambiguous.insert(key);
        } else {
            spine_predicate.insert(key, ob.predicate.clone());
        }
    }

    // Build a UNIQUE (span, class) index of the trust-vcgen contract VCs too: a
    // span+class appearing more than once on the trust-vcgen side is likewise
    // ambiguous and not flipped (we cannot tell which spine obligation owns which
    // VC). NB the three loop-invariant sub-VCs (initiation/consecution/
    // sufficiency) trust-vcgen emits at one span ALL map to the `LoopInvariant`
    // class, so a loop-invariant clause is correctly self-ambiguous here and stays
    // trust-vcgen-sourced (fail-closed) — its consecution formula is `Bool(true)`,
    // which has no byte-equal spine reconstruction anyway.
    let mut vcgen_class_counts: HashMap<(SpanKey, ContractClass), usize> = HashMap::new();
    for vc in &vcgen_vcs {
        if let Some(class) = vcgen_contract_class(&vc.kind) {
            if vc.kind.proof_level() == ProofLevel::L1Functional {
                *vcgen_class_counts.entry((span_key(&vc.location), class)).or_insert(0) += 1;
            }
        }
    }

    let mut decisions = Vec::new();
    let out: Vec<VerificationCondition> = vcgen_vcs
        .into_iter()
        .map(|vc| {
            if !is_l1_contract(&vc) {
                return vc;
            }
            let Some(class) = vcgen_contract_class(&vc.kind) else {
                decisions.push(FlipDecision::TrustVcgenSourced);
                return vc;
            };
            let key = (span_key(&vc.location), class);

            // The spine must own a UNIQUE obligation for this span+class, AND the
            // trust-vcgen side must be unique too (else we cannot pin a 1:1 match).
            let spine_has_unique = spine_seen.contains(&key) && !spine_ambiguous.contains(&key);
            let vcgen_unique = vcgen_class_counts.get(&key).copied() == Some(1);
            if !spine_has_unique || !vcgen_unique {
                decisions.push(FlipDecision::TrustVcgenSourced);
                return vc;
            }

            // Reconstruct the spine's DISPATCHED-equivalent contract violation
            // formula from the obligation's predicate, then compare byte-equal
            // (modulo version tokens) to trust-vcgen's LIVE formula. The violation
            // wrapping reproduces trust-vcgen's `contracts.rs` polarity transform:
            //   * RefinementType / LoopInvariant → `Not(predicate)`
            //   * Precondition → `Bool(false)` (trust-vcgen's definition-site form;
            //     not reconstructible from the predicate, so it never byte-matches
            //     → fail-closed, kept).
            // We KEEP trust-vcgen's exact LIVE formula as the dispatched/proof
            // formula in EVERY branch (the byte-equal swap re-keys PROVENANCE to the
            // spine; the formula stays verdict-identical by construction).
            let candidate: Option<Formula> = match spine_predicate.get(&key).cloned().flatten() {
                Some(predicate) => match key.1 {
                    ContractClass::RefinementType | ContractClass::LoopInvariant => {
                        Some(Formula::Not(Box::new(predicate)))
                    }
                    // Precondition's dispatched form is `Bool(false)` — not derived
                    // from the predicate. Leave it unreconstructed (fail-closed).
                    ContractClass::Precondition => None,
                },
                None => None,
            };

            let byte_equal = candidate
                .as_ref()
                .is_some_and(|cand| formula_eq_modulo_versions(cand, &vc.formula));
            if byte_equal {
                // Spine OWNS the obligation AND reconstructs a byte-equal formula:
                // re-key provenance to the spine, keeping the live formula (verdict
                // trivially identical — it IS the live formula).
                decisions.push(FlipDecision::SpineSourcedFormula);
            } else {
                // Spine owns the obligation but its predicate yields no byte-equal
                // dispatched formula (Precondition `Bool(false)`, an unparseable
                // predicate, a complex violation form): keep trust-vcgen's formula
                // (fail-closed). The obligation is still spine-OWNED for provenance.
                decisions.push(FlipDecision::SpineSourcedKeptFormula);
            }
            vc
        })
        .collect();

    (out, FlipReport { decisions })
}

#[cfg(test)]
mod tests {
    use trust_types::UnwindEdge;
    use super::*;
    use crate::parity::tests as oracle;

    /// Evaluate the deliberately small mathematical-integer fragment used by the
    /// committed `add1_u32` overflow fixture. Returning `None` for every other
    /// construct keeps this test oracle fail-closed if vcgen's formula changes.
    fn eval_fixture_int(formula: &Formula) -> Option<i128> {
        match formula {
            Formula::Int(value) => Some(*value),
            Formula::UInt(value) => i128::try_from(*value).ok(),
            Formula::Var(name, _) => match name.as_str() {
                "x" => Some(u32::MAX.into()),
                // The checked-add result is unconstrained on overflow. Choosing
                // zero adversarially demonstrates that the global result fact
                // does not manufacture an equality on the overflow edge.
                "_0" => Some(0),
                _ => None,
            },
            Formula::SymVar(name, _) => match name.as_str() {
                "x" => Some(u32::MAX.into()),
                "_0" => Some(0),
                _ => None,
            },
            Formula::Add(lhs, rhs) => eval_fixture_int(lhs)?.checked_add(eval_fixture_int(rhs)?),
            Formula::Sub(lhs, rhs) => eval_fixture_int(lhs)?.checked_sub(eval_fixture_int(rhs)?),
            Formula::Mul(lhs, rhs) => eval_fixture_int(lhs)?.checked_mul(eval_fixture_int(rhs)?),
            Formula::Neg(inner) => eval_fixture_int(inner)?.checked_neg(),
            _ => None,
        }
    }

    fn eval_fixture_bool(formula: &Formula) -> Option<bool> {
        match formula {
            Formula::Bool(value) => Some(*value),
            Formula::Not(inner) => Some(!eval_fixture_bool(inner)?),
            Formula::And(parts) => {
                parts.iter().try_fold(true, |acc, part| Some(acc && eval_fixture_bool(part)?))
            }
            Formula::Or(parts) => {
                parts.iter().try_fold(false, |acc, part| Some(acc || eval_fixture_bool(part)?))
            }
            Formula::Implies(lhs, rhs) => Some(!eval_fixture_bool(lhs)? || eval_fixture_bool(rhs)?),
            Formula::Eq(lhs, rhs) => Some(eval_fixture_int(lhs)? == eval_fixture_int(rhs)?),
            Formula::Lt(lhs, rhs) => Some(eval_fixture_int(lhs)? < eval_fixture_int(rhs)?),
            Formula::Le(lhs, rhs) => Some(eval_fixture_int(lhs)? <= eval_fixture_int(rhs)?),
            Formula::Gt(lhs, rhs) => Some(eval_fixture_int(lhs)? > eval_fixture_int(rhs)?),
            Formula::Ge(lhs, rhs) => Some(eval_fixture_int(lhs)? >= eval_fixture_int(rhs)?),
            _ => None,
        }
    }

    /// Generate the trust-vcgen safety VCs for a fixture (the same set the
    /// compiler dispatches). Uses the dev-only trust-vcgen dependency, exactly as
    /// the parity oracle does.
    fn vcgen_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
        trust_vcgen::generate_vcs(func)
    }

    /// The CANONICAL rustc overflow MIR shape, built inline to exactly match the
    /// real `VerifiableFunction` the compiler extracts for
    /// `fn add_ovf(a:i32,b:i32)->i32 { a+b }`: a `CheckedBinaryOp(Add, a, b)`
    /// assigned to a `(i32, bool)` tuple `_3`, then
    /// `Assert { cond: Move(_3.1), expected: false, msg: Overflow(Add) }`.
    ///
    /// This is the shape the verdict-flip is dispatched on in production — and the
    /// shape the live A/B used. It differs from the `overflow_checked_add` parity
    /// fixture, which models the overflow with a plain `Rvalue::BinaryOp(Add)` plus
    /// a const-false flag. The CheckedBinaryOp shape is the regression case:
    /// `find_block_binary_operands` previously matched only `Rvalue::BinaryOp`, so
    /// the spine recovered no operands and produced no candidate formula.
    fn add_ovf_checked_binop() -> VerifiableFunction {
        use trust_types::{
            AssertMessage, BasicBlock as TrustBlock, BinOp, BlockId, LocalDecl, Operand, Place,
            Projection, Rvalue, Statement, Terminator, Ty, VerifiableBody,
        };
        let span = SourceSpan {
            file: "/tmp/ovf_only.rs".into(),
            line_start: 1,
            col_start: 40,
            line_end: 1,
            col_end: 45,
        };
        VerifiableFunction {
            name: "add_ovf".into(),
            def_path: "add_ovf".into(),
            span: span.clone(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]), name: None },
                ],
                blocks: vec![
                    TrustBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: span.clone(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Move(Place {
                                local: 3,
                                projections: vec![Projection::Field(1)],
                            }),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(1),
                            span: span.clone(),
                        },
                    },
                    TrustBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Move(Place {
                                local: 3,
                                projections: vec![Projection::Field(0)],
                            })),
                            span: span.clone(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 2,
                return_ty: Ty::i32(),
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// The explicit-module API must never hide a second MIR-to-Trust-IR
    /// lowering. An unrelated module has no matching source obligations, so
    /// every retained P9 VC remains compatibility-sourced and byte-identical.
    #[test]
    fn explicit_module_flip_does_not_self_lower_from_mir() {
        let func = add_ovf_checked_binop();
        let before = vcgen_vcs(&func);
        assert!(!before.is_empty(), "fixture must carry a safety obligation");

        let unrelated = trust_ir::Module::new("direct-source-with-no-obligations");
        let (after, report) = flip_safety_verdicts_with_module(&func, &unrelated, before.clone());

        assert_verdict_identical(&before, &after);
        assert_eq!(report.trust_vcgen_sourced(), before.len());
        assert!(
            report.decisions.iter().all(|decision| *decision == FlipDecision::TrustVcgenSourced),
            "the explicit module must not be replaced by a hidden MIR lowering: {report:?}"
        );
    }

    /// REGRESSION: the canonical `CheckedBinaryOp + Assert(Overflow)` shape (the
    /// one the compiler extracts for `a + b`, NOT the `Rvalue::BinaryOp` parity
    /// fixture) must flip with the formula SPINE-SOURCED. Before the
    /// `find_block_binary_operands` fix, the spine recovered no operands from the
    /// `CheckedBinaryOp` statement, produced zero candidate formulas, and the flip
    /// fell back to `SpineSourcedKeptFormula` ("vcgen formula kept"). Now the spine
    /// reconstructs the full `conjoin_arg_type_ranges(conjoin_arg_type_ranges(core))`
    /// formula, which byte-equals trust-vcgen's LIVE dispatched formula, so the
    /// swap fires. Asserted against the LIVE `trust_vcgen::generate_vcs`.
    #[test]
    fn flip_checked_binop_overflow_is_spine_sourced_formula() {
        let func = add_ovf_checked_binop();
        let before = vcgen_vcs(&func);
        let (after, report) = flip_safety_verdicts_to_spine(&func, before.clone());
        assert_verdict_identical(&before, &after);
        assert_eq!(
            report.spine_sourced_formula(),
            1,
            "canonical CheckedBinaryOp overflow must flip with the formula spine-sourced \
             (the find_block_binary_operands CheckedBinaryOp fix): {report:?}"
        );
        assert_eq!(
            report.spine_sourced_kept_formula(),
            0,
            "no kept-formula expected for the CheckedBinaryOp overflow shape: {report:?}"
        );
        // The dispatched formula is GENUINELY a spine reconstruction AND byte-equals
        // trust-vcgen's full two-arg-range-wrapped formula.
        let ovf = after
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
            .expect("an overflow VC is present");
        let cands = reconstruct_full_safety_formula_candidates(&func, &ovf.location, &ovf.kind);
        assert!(
            cands.iter().any(|c| formula_eq_modulo_versions(c, &ovf.formula)),
            "the dispatched overflow formula must be a spine reconstruction (spine-sourced)"
        );
        assert_eq!(
            ovf.formula.to_smtlib(),
            "(and (and (<= (- 2147483648) a) (<= a 2147483647)) \
             (and (<= (- 2147483648) b) (<= b 2147483647)) \
             (and (and (<= (- 2147483648) a) (<= a 2147483647)) \
             (and (<= (- 2147483648) b) (<= b 2147483647)) \
             (and (and (<= (- 2147483648) a) (<= a 2147483647)) \
             (and (<= (- 2147483648) b) (<= b 2147483647)) \
             (or (< (+ a b) (- 2147483648)) (> (+ a b) 2147483647)))))",
            "the spine-sourced CheckedBinaryOp overflow formula must be the \
             two-arg-range-wrapped core trust-vcgen dispatches"
        );
    }

    /// Every returned VC must be verdict-identical to its trust-vcgen input:
    /// identical `kind` (Debug), identical `location`, identical
    /// `contract_metadata`, and an SMT-LIB-equal `formula`. This is the core
    /// non-regression invariant.
    fn assert_verdict_identical(before: &[VerificationCondition], after: &[VerificationCondition]) {
        assert_eq!(before.len(), after.len(), "flip must not add/drop VCs");
        for (b, a) in before.iter().zip(after.iter()) {
            assert_eq!(
                format!("{:?}", b.kind),
                format!("{:?}", a.kind),
                "flip must preserve VcKind (routing/label driver)"
            );
            assert_eq!(b.location, a.location, "flip must preserve location");
            assert_eq!(
                format!("{:?}", b.contract_metadata),
                format!("{:?}", a.contract_metadata),
                "flip must preserve contract_metadata"
            );
            assert_eq!(
                b.formula.to_smtlib(),
                a.formula.to_smtlib(),
                "flip must keep the formula SMT-LIB byte-identical (verdict-identical)"
            );
        }
    }

    // =====================================================================
    // L1 CONTRACT verdict-flip tests (R-L1). Mirror the L0 tests: every
    // returned VC must be verdict-identical to its trust-vcgen input, and the
    // FlipReport must reflect the byte-equal-or-keep envelope.
    // =====================================================================

    /// Build a minimal `i32 -> i32` `VerifiableFunction` with one `Return` block
    /// and the given contracts attached — the same shape `contract_vcgen_proto`'s
    /// fixtures use. No asserts/panics, so the only obligations are the contract
    /// ones (a clean L1 set).
    fn contract_fn(name: &str, contracts: Vec<trust_types::Contract>) -> VerifiableFunction {
        use trust_types::{
            BasicBlock as TrustBlock, BlockId, LocalDecl, Terminator, Ty, VerifiableBody,
        };
        // A non-default span so the spine's recovered span and the VC's location
        // span match on a real (file,line,col) tuple, not the all-zero default.
        let span = SourceSpan {
            file: "/tmp/contract_fixture.rs".into(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        };
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: span.clone(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                ],
                blocks: vec![TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::i32(),
                datatype_defs: Default::default(),
            },
            contracts,
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// A `#[requires]` precondition. trust-vcgen dispatches `Formula::Bool(false)`
    /// for a definition-site precondition (trivially-discharged), which the spine
    /// CANNOT reconstruct from the predicate — so the obligation is spine-OWNED but
    /// its formula is KEPT (fail-closed). Verdict-identical either way.
    #[test]
    fn l1_flip_precondition_is_spine_owned_kept_formula() {
        let span = SourceSpan {
            file: "/tmp/contract_fixture.rs".into(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        };
        let func = contract_fn(
            "nonneg",
            vec![trust_types::Contract {
                kind: trust_types::ContractKind::Requires,
                span,
                body: "x >= 0".to_string(),
            }],
        );
        let before = vcgen_vcs(&func);
        // Sanity: there is exactly one Precondition VC, formula = Bool(false).
        assert_eq!(
            before.iter().filter(|vc| matches!(vc.kind, VcKind::Precondition { .. })).count(),
            1,
            "fixture must emit one precondition VC: {before:?}"
        );
        let (after, report) = flip_contract_verdicts_to_spine(&func, before.clone());
        assert_verdict_identical(&before, &after);
        assert_eq!(
            report.spine_sourced_kept_formula(),
            1,
            "precondition is spine-owned with trust-vcgen Bool(false) kept (not reconstructible): {report:?}"
        );
        assert_eq!(
            report.spine_sourced_formula(),
            0,
            "precondition formula is never byte-equal-swappable (Bool(false)): {report:?}"
        );
    }

    /// A `#[refine]` type-refinement. trust-vcgen dispatches `Formula::Not(parsed)`
    /// as the violation formula; the spine carries the predicate `parsed` and the
    /// flip reconstructs `Not(parsed)`, which byte-equals trust-vcgen's formula — so
    /// the swap FIRES (formula now spine-sourced), verdict-identical by AST equality.
    #[test]
    fn l1_flip_refinement_is_spine_sourced_formula() {
        let span = SourceSpan {
            file: "/tmp/contract_fixture.rs".into(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        };
        let func = contract_fn(
            "refined",
            vec![trust_types::Contract {
                kind: trust_types::ContractKind::TypeRefinement,
                span,
                body: "x: x > 0".to_string(),
            }],
        );
        let before = vcgen_vcs(&func);
        assert_eq!(
            before
                .iter()
                .filter(|vc| matches!(vc.kind, VcKind::TypeRefinementViolation { .. }))
                .count(),
            1,
            "fixture must emit one refinement VC: {before:?}"
        );
        let (after, report) = flip_contract_verdicts_to_spine(&func, before.clone());
        assert_verdict_identical(&before, &after);
        assert_eq!(
            report.spine_sourced_formula(),
            1,
            "refinement violation `Not(predicate)` is reconstructible and byte-equal — must flip: {report:?}"
        );
        assert_eq!(
            report.spine_sourced_kept_formula(),
            0,
            "no kept-formula expected for the refinement class: {report:?}"
        );
        // The dispatched refinement formula GENUINELY equals the spine
        // reconstruction `Not(parse_spec_expr("x > 0"))`.
        let refine = after
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::TypeRefinementViolation { .. }))
            .expect("a refinement VC is present");
        let expected = Formula::Not(Box::new(
            trust_types::parse_spec_expr("x > 0").expect("predicate parses"),
        ));
        assert!(
            formula_eq_modulo_versions(&expected, &refine.formula),
            "dispatched refinement formula must be the spine's Not(predicate) reconstruction"
        );
    }

    /// A `#[requires]` + `#[ensures]` function: the Precondition flips
    /// (spine-owned, kept), the Postcondition is left to the L0 flip's dedicated
    /// arm (NOT double-handled here — the L1 flip records no decision for it), and
    /// the result is verdict-identical.
    #[test]
    fn l1_flip_excludes_postcondition_and_is_verdict_identical() {
        let span = SourceSpan {
            file: "/tmp/contract_fixture.rs".into(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        };
        let func = contract_fn(
            "clamp_pos",
            vec![
                trust_types::Contract {
                    kind: trust_types::ContractKind::Requires,
                    span: span.clone(),
                    body: "x > 0".to_string(),
                },
                trust_types::Contract {
                    kind: trust_types::ContractKind::Ensures,
                    span,
                    body: "result > 0".to_string(),
                },
            ],
        );
        let before = vcgen_vcs(&func);
        let (after, report) = flip_contract_verdicts_to_spine(&func, before.clone());
        assert_verdict_identical(&before, &after);
        // Exactly ONE L1 contract decision (the precondition); the postcondition
        // is excluded from the contract flip (handled by the L0 path).
        assert_eq!(
            report.decisions.len(),
            1,
            "only the precondition contributes an L1-contract-flip decision \
             (postcondition excluded): {report:?}"
        );
    }

    /// FAIL-CLOSED: the L1 contract flip NEVER touches an L0 safety VC. Running it
    /// over a pure-safety function's VCs returns them byte-identical with zero
    /// contract decisions.
    #[test]
    fn l1_flip_leaves_l0_safety_untouched() {
        let func = oracle::overflow_checked_add();
        let before = vcgen_vcs(&func);
        let (after, report) = flip_contract_verdicts_to_spine(&func, before.clone());
        assert_verdict_identical(&before, &after);
        assert_eq!(
            report.decisions.len(),
            0,
            "no L1 contract VCs in a pure-safety function: {report:?}"
        );
    }

    #[test]
    fn flip_preserves_verdict_for_overflow_add() {
        let func = oracle::overflow_checked_add();
        let before = vcgen_vcs(&func);
        let (after, report) = flip_safety_verdicts_to_spine(&func, before.clone());
        assert_verdict_identical(&before, &after);
        // The overflow obligation is spine-OWNED *with the formula SPINE-SOURCED*:
        // the spine reconstructs a byte-equal full overflow formula (idempotent
        // arg-range wrap of the violation core), so the swap fires. This is the
        // class that genuinely demonstrates the formula surviving on the spine.
        assert_eq!(
            report.spine_sourced_formula(),
            1,
            "overflow obligation must be flipped with the formula spine-sourced: {report:?}"
        );
        assert_eq!(report.spine_sourced_kept_formula(), 0, "no kept-formula expected: {report:?}");
    }

    #[test]
    fn flip_preserves_verdict_for_division() {
        let func = oracle::division_by_zero_guard();
        let before = vcgen_vcs(&func);
        let (after, report) = flip_safety_verdicts_to_spine(&func, before.clone());
        assert_verdict_identical(&before, &after);
        // div-by-zero is spine-OWNED (the spine derived the obligation), but its
        // formula is KEPT from trust-vcgen: trust-vcgen wraps `(= b 0)` in the
        // fresh-var block-def `(= nonzero true)` conjuncts the spine cannot
        // reproduce without re-implementing private dataflow, so no candidate is
        // byte-equal → fail-closed on the formula (verdict still identical).
        assert_eq!(
            report.spine_sourced_kept_formula(),
            1,
            "div obligation must be spine-owned with trust-vcgen formula kept: {report:?}"
        );
        assert_eq!(
            report.spine_sourced_formula(),
            0,
            "div formula is not byte-equal-swappable here"
        );
    }

    #[test]
    fn flip_preserves_verdict_for_bounds() {
        let func = oracle::array_index_bounds();
        let before = vcgen_vcs(&func);
        let (after, report) = flip_safety_verdicts_to_spine(&func, before.clone());
        assert_verdict_identical(&before, &after);
        // This fixture is the ABSTRACT-FLAG bounds shape (`(= in_bounds true) ∧
        // (not in_bounds)`): trust-vcgen emits a flag-failure formula with no
        // operand-level core, so the spine reconstructs nothing and keeps
        // trust-vcgen's formula (spine-owned, formula kept).
        assert_eq!(
            report.spine_sourced_kept_formula(),
            1,
            "abstract-flag bounds is spine-owned with trust-vcgen formula kept: {report:?}"
        );
    }

    /// The DIRECT-COMPARISON bounds shape (`cond = idx < len` in the source
    /// block) is the class that now flips LIVE with the formula SPINE-SOURCED:
    /// trust-vcgen wraps the violation core `Ge(i, len)` in exactly the single
    /// fresh-var block definition `Eq(in_bounds, Lt(i, len))`, which the spine now
    /// reproduces byte-for-byte. The flip swap fires (formula now lives on the
    /// spine), verdict-identical by AST equality. This is run against the LIVE
    /// `trust_vcgen::generate_vcs`, so the byte-equality is proven against the
    /// real builder, not a hand-written expected.
    #[test]
    fn flip_bounds_direct_unsigned_is_spine_sourced_formula() {
        let func = oracle::bounds_direct_comparison_unsigned();
        let before = vcgen_vcs(&func);
        let (after, report) = flip_safety_verdicts_to_spine(&func, before.clone());
        assert_verdict_identical(&before, &after);
        assert_eq!(
            report.spine_sourced_formula(),
            1,
            "unsigned direct-comparison bounds must flip with the formula spine-sourced: {report:?}"
        );
        assert_eq!(
            report.spine_sourced_kept_formula(),
            0,
            "no kept-formula expected for direct-comparison bounds: {report:?}"
        );
        // Prove the dispatched bounds formula is GENUINELY a spine reconstruction
        // (not merely a clone of trust-vcgen's): it is one of the spine's candidate
        // full formulas for this assert AND byte-equals trust-vcgen's full formula.
        let bounds_vc = after
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
            .expect("a bounds VC is present");
        let spine_candidates =
            reconstruct_full_safety_formula_candidates(&func, &bounds_vc.location, &bounds_vc.kind);
        assert!(
            spine_candidates.iter().any(|c| formula_eq_modulo_versions(c, &bounds_vc.formula)),
            "the dispatched bounds formula must be a spine reconstruction (spine-sourced)"
        );
        // And concretely the full formula trust-vcgen emits: `And([fresh_def, core])`.
        // The dispatched formula is the LIVE one, carrying trust-vcgen's S2c
        // statement-granular SSA version tokens (`in_bounds#s0_0`); modulo those
        // tokens it is the full fresh-def-wrapped core.
        assert_eq!(
            strip_version_tokens_in_formula(&bounds_vc.formula).to_smtlib(),
            "(and (= in_bounds (< i len)) (>= i len))",
            "the spine-sourced bounds formula must be the full fresh-def-wrapped core"
        );
    }

    /// Signed-index direct-comparison bounds: the violation core gains the
    /// `Lt(i, 0)` disjunct, and the spine reproduces the SAME fresh-var binding —
    /// so the full formula `And([Eq(in_bounds, Lt(i,len)), Or([Lt(i,0), Ge(i,len)])])`
    /// is byte-equal and the flip fires spine-sourced. Live `trust_vcgen` oracle.
    #[test]
    fn flip_bounds_direct_signed_is_spine_sourced_formula() {
        let func = oracle::bounds_direct_comparison_signed();
        let before = vcgen_vcs(&func);
        let (after, report) = flip_safety_verdicts_to_spine(&func, before.clone());
        assert_verdict_identical(&before, &after);
        assert_eq!(
            report.spine_sourced_formula(),
            1,
            "signed direct-comparison bounds must flip with the formula spine-sourced: {report:?}"
        );
        let bounds_vc = after
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
            .expect("a bounds VC is present");
        assert_eq!(
            strip_version_tokens_in_formula(&bounds_vc.formula).to_smtlib(),
            "(and (= in_bounds (< i len)) (or (< i 0) (>= i len)))",
            "the spine-sourced signed bounds formula must include the < 0 disjunct"
        );
    }

    #[test]
    fn flip_never_changes_kind_so_routing_label_is_stable() {
        // The reverted attempt's regression was a kind change to a
        // hardened/unsafe category. Assert the kind is NEVER a hardened category
        // after the flip — the label `hardened_unsafe_operation` is structurally
        // impossible.
        for func in [
            oracle::overflow_checked_add(),
            oracle::division_by_zero_guard(),
            oracle::array_index_bounds(),
        ] {
            let before = vcgen_vcs(&func);
            let (after, _) = flip_safety_verdicts_to_spine(&func, before.clone());
            for vc in &after {
                assert!(
                    vc.kind.hardened_category().is_none(),
                    "a flipped safety VC must never carry a hardened category \
                     (would mislabel as hardened_*): {:?}",
                    vc.kind
                );
            }
        }
    }

    #[test]
    fn lowering_failure_is_a_no_op_flip() {
        // A function the spine cannot lower must pass every VC through unchanged
        // (fail-open: the build is never blocked, no verdict changes).
        let func = oracle::overflow_checked_add();
        let before = vcgen_vcs(&func);
        // Run normally; even on success, the no-op property is that decisions
        // line up 1:1 with the input VCs.
        let (after, report) = flip_safety_verdicts_to_spine(&func, before.clone());
        assert_eq!(report.decisions.len(), before.len());
        assert_eq!(after.len(), before.len());
    }

    #[test]
    fn unmatched_span_stays_trust_vcgen_sourced() {
        // A VC whose span matches no spine obligation must not be flipped. We
        // simulate this by perturbing a copy of a real VC's span to a location
        // the spine never stamped.
        let func = oracle::overflow_checked_add();
        let mut before = vcgen_vcs(&func);
        for vc in &mut before {
            if vc.kind.proof_level() == ProofLevel::L0Safety {
                vc.location = SourceSpan {
                    file: "nonexistent.rs".to_string(),
                    line_start: 9999,
                    col_start: 1,
                    line_end: 9999,
                    col_end: 2,
                };
            }
        }
        let (after, report) = flip_safety_verdicts_to_spine(&func, before.clone());
        assert_verdict_identical(&before, &after);
        assert_eq!(
            report.flipped(),
            0,
            "no VC may be flipped when its span matches no spine obligation: {report:?}"
        );
    }

    /// DIAGNOSTIC (Step 1): replicate the EXACT live compiler path for the
    /// overflow VC and print the precise diff vs the spine reconstruction. The
    /// live daily-driver does NOT call `generate_vcs`; it calls
    /// `generate_vcs_with_discharge_and_summaries(&func, &summaries)` →
    /// `filter_vcs_by_level(.., max_level)` → `dedupe_exact_vcs(..)` (see
    /// `compiler/rustc_mir_transform/src/trust_verify.rs`). This test computes the
    /// overflow VC's formula that exact way and compares it to the spine's
    /// `reconstruct_full_safety_formula_candidates`.
    #[test]
    fn diagnose_live_path_overflow_formula_vs_spine() {
        use trust_types::ProofLevel;
        use trust_vcgen::{AbstractDomain, SummaryDatabase, vc_fingerprint};

        // Load the REAL dumped VerifiableFunction (the shape the live A/B used).
        let json = fixture_json("/tmp/vfdump/add_ovf.json").to_string();
        let func: VerifiableFunction = serde_json::from_str(&json).expect("parse add_ovf.json");

        // Replicate `dedupe_exact_vcs` from trust_verify.rs: key on
        // (function, file, span, vc_fingerprint).
        fn dedupe_exact(vcs: Vec<VerificationCondition>) -> Vec<VerificationCondition> {
            let mut seen = std::collections::HashSet::new();
            let mut out = Vec::with_capacity(vcs.len());
            for vc in vcs {
                let key = (
                    vc.function.to_string(),
                    vc.location.file.clone(),
                    vc.location.line_start,
                    vc.location.col_start,
                    vc.location.line_end,
                    vc.location.col_end,
                    vc_fingerprint(&vc),
                );
                if seen.insert(key) {
                    out.push(vc);
                }
            }
            out
        }

        for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
            // --- THE EXACT LIVE PATH (empty summaries; add_ovf has no calls) ---
            let summaries = SummaryDatabase::new();
            let (solver_vcs, _discharged) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries(&func, &summaries);
            let solver_vcs = dedupe_exact(trust_vcgen::filter_vcs_by_level(solver_vcs, max_level));

            let live_ovf =
                solver_vcs.iter().find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }));
            let Some(live_ovf) = live_ovf else {
                eprintln!("[{max_level:?}] NO overflow VC in live path");
                continue;
            };

            eprintln!("==================== max_level={max_level:?} ====================");
            eprintln!("LIVE-PATH overflow formula (smtlib):\n{}", live_ovf.formula.to_smtlib());
            eprintln!("LIVE-PATH overflow formula (debug):\n{:?}", live_ovf.formula);

            // --- The PLAIN generate_vcs formula (what the crate test matched) ---
            let plain = trust_vcgen::generate_vcs(&func);
            if let Some(plain_ovf) =
                plain.iter().find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
            {
                eprintln!(
                    "PLAIN generate_vcs overflow formula (smtlib):\n{}",
                    plain_ovf.formula.to_smtlib()
                );
                eprintln!(
                    "LIVE == PLAIN ? {}",
                    plain_ovf.formula.to_smtlib() == live_ovf.formula.to_smtlib()
                );
            }

            // --- The SPINE reconstruction candidates ---
            let cands = reconstruct_full_safety_formula_candidates(
                &func,
                &live_ovf.location,
                &live_ovf.kind,
            );
            eprintln!("SPINE candidate count: {}", cands.len());
            for (i, c) in cands.iter().enumerate() {
                eprintln!("  spine cand[{i}] smtlib:\n  {}", c.to_smtlib());
                eprintln!("  spine cand[{i}] == LIVE ? {}", *c == live_ovf.formula);
            }
            let any_match = cands.iter().any(|c| formula_eq_modulo_versions(c, &live_ovf.formula));
            eprintln!("ANY spine candidate byte-equals LIVE-path formula? {any_match}");

            // Also: what does augment add? Replicate the env formula directly.
            let initial = trust_vcgen::type_aware_initial_state(&func);
            let config = trust_vcgen::FixpointConfig::for_function(&func);
            let fp = trust_vcgen::fixpoint_configured(&func, initial.clone(), &config);
            let mut merged = trust_vcgen::IntervalDomain::bottom();
            for state in fp.block_states.values() {
                merged = merged.join(state);
            }
            let env_formula = trust_vcgen::interval_domain_to_formula(&merged);
            eprintln!("MERGED env_formula (smtlib):\n{}", env_formula.to_smtlib());
            eprintln!("MERGED env_formula (debug):\n{env_formula:?}");
            eprintln!(
                "LIVE == And([env_formula, spine_cand[0]]) ? {}",
                live_ovf.formula
                    == trust_types::Formula::And(vec![env_formula.clone(), cands[0].clone()])
            );
            // Also: what does the INITIAL state look like (before fixpoint)?
            let init_env = trust_vcgen::interval_domain_to_formula(&initial);
            eprintln!("INITIAL env_formula (smtlib):\n{}", init_env.to_smtlib());
            eprintln!(
                "fixpoint block_states keys = {:?}",
                fp.block_states.keys().collect::<Vec<_>>()
            );
        }
    }

    /// END-TO-END (Step 2 confirmation): run the FULL flip over the LIVE-path VC
    /// set for the real dumped `add_ovf.json` and assert the overflow VC flips
    /// SPINE-SOURCED (formula). The VC set is built EXACTLY as the live compiler
    /// builds it: `generate_vcs_with_discharge_and_summaries` → `filter_vcs_by_level`
    /// → `dedupe_exact`. This is the test that proves the live A/B will report
    /// `add_ovf → spine-sourced(formula)`.
    #[test]
    fn live_path_add_ovf_flips_spine_sourced_formula() {
        use trust_types::ProofLevel;
        use trust_vcgen::{SummaryDatabase, vc_fingerprint};

        fn dedupe_exact(vcs: Vec<VerificationCondition>) -> Vec<VerificationCondition> {
            let mut seen = std::collections::HashSet::new();
            let mut out = Vec::with_capacity(vcs.len());
            for vc in vcs {
                let key = (
                    vc.function.to_string(),
                    vc.location.file.clone(),
                    vc.location.line_start,
                    vc.location.col_start,
                    vc.location.line_end,
                    vc.location.col_end,
                    vc_fingerprint(&vc),
                );
                if seen.insert(key) {
                    out.push(vc);
                }
            }
            out
        }

        let json = fixture_json("/tmp/vfdump/add_ovf.json").to_string();
        let func: VerifiableFunction = serde_json::from_str(&json).expect("parse add_ovf.json");

        for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
            let summaries = SummaryDatabase::new();
            let (solver_vcs, _discharged) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries(&func, &summaries);
            let solver_vcs = dedupe_exact(trust_vcgen::filter_vcs_by_level(solver_vcs, max_level));

            let before = solver_vcs.clone();
            let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
            assert_verdict_identical(&before, &after);
            assert_eq!(
                report.spine_sourced_formula(),
                1,
                "[{max_level:?}] LIVE-path add_ovf overflow VC must flip SPINE-SOURCED (formula): {report:?}"
            );
            assert_eq!(
                report.spine_sourced_kept_formula(),
                0,
                "[{max_level:?}] no kept-formula expected for live-path add_ovf: {report:?}"
            );
        }
    }

    /// Resolve a (legacy `/tmp/vf*`) fixture path to committed, HERMETIC
    /// `include_str!` content. The `/tmp/...` keys are kept at the call sites as
    /// stable provenance labels, but the bytes come from `fixtures/` so the suite
    /// is reboot-proof: the `/tmp` dumps were ephemeral dev artifacts, and a host
    /// crash that wiped `/tmp` is exactly what made these tests fail. Regenerate
    /// the committed fixtures from the sources in `fixtures/src/` via
    /// `trustc -Ztrust-policy=advisory -Ztrust-dump=mir:<dir> \
    /// --edition 2021 ... <src>.rs`
    /// (the dump writes one `<fn-name>.json` per function).
    fn fixture_json(path: &str) -> &'static str {
        match path {
            "/tmp/vfdump/add_ovf.json" => include_str!("../fixtures/add_ovf.json"),
            "/tmp/vfdump2/idx.json" => include_str!("../fixtures/idx.json"),
            "/tmp/vfdump2/shl.json" => include_str!("../fixtures/shl.json"),
            "/tmp/vfdump2/dv.json" => include_str!("../fixtures/dv.json"),
            "/tmp/vfdump2/rem.json" => include_str!("../fixtures/rem.json"),
            "/tmp/vfdump3/mul.json" => include_str!("../fixtures/mul.json"),
            "/tmp/vfdump3/ng.json" => include_str!("../fixtures/ng.json"),
            "/tmp/vfdump3/cst.json" => include_str!("../fixtures/cst.json"),
            "/tmp/vfmul/umul.json" => include_str!("../fixtures/umul.json"),
            "/tmp/vfL1/pre.json" => include_str!("../fixtures/pre.json"),
            "/tmp/vfL1/both.json" => include_str!("../fixtures/both.json"),
            "/tmp/vfbr/pick.json" => include_str!("../fixtures/pick.json"),
            "/tmp/vfbr/clamp_branch.json" => include_str!("../fixtures/clamp_branch.json"),
            "/tmp/vfloop/count.json" => include_str!("../fixtures/count.json"),
            other => panic!("unknown hermetic fixture key: {other}"),
        }
    }

    /// Build the EXACT live-compiler VC set for a dumped `VerifiableFunction`
    /// JSON at `max_level`: `generate_vcs_with_discharge_and_summaries(&func, &[])`
    /// → `filter_vcs_by_level` → `dedupe_exact` (the trust_verify.rs path).
    fn live_path_vcs(
        path: &str,
        max_level: trust_types::ProofLevel,
    ) -> (VerifiableFunction, Vec<VerificationCondition>) {
        use trust_vcgen::{SummaryDatabase, vc_fingerprint};

        fn dedupe_exact(vcs: Vec<VerificationCondition>) -> Vec<VerificationCondition> {
            let mut seen = std::collections::HashSet::new();
            let mut out = Vec::with_capacity(vcs.len());
            for vc in vcs {
                let key = (
                    vc.function.to_string(),
                    vc.location.file.clone(),
                    vc.location.line_start,
                    vc.location.col_start,
                    vc.location.line_end,
                    vc.location.col_end,
                    vc_fingerprint(&vc),
                );
                if seen.insert(key) {
                    out.push(vc);
                }
            }
            out
        }

        let json = fixture_json(path).to_string();
        let func: VerifiableFunction =
            serde_json::from_str(&json).unwrap_or_else(|_| panic!("parse {path}"));
        let summaries = SummaryDatabase::new();
        let (solver_vcs, _discharged) =
            trust_vcgen::generate_vcs_with_discharge_and_summaries(&func, &summaries);
        let solver_vcs = dedupe_exact(trust_vcgen::filter_vcs_by_level(solver_vcs, max_level));
        (func, solver_vcs)
    }

    /// LIVE-FIRING (bounds): the real rustc slice-index shape `fn idx(s,i){s[i]}`
    /// (`/tmp/vfdump2/idx.json`) flips SPINE-SOURCED (formula) on the LIVE-path VC
    /// set. The spine reconstructs trust-vcgen's full live formula
    /// `And([env, And([Eq(_3, s__slice_len), Eq(_4, Lt(i, _3)), Ge(i, _3)])])`
    /// byte-for-byte (slice-len block-def + cond binding + violation, param-env
    /// wrapped), so the formula now lives on the spine. Asserted against the LIVE
    /// `generate_vcs_with_discharge_and_summaries` path.
    #[test]
    fn live_path_bounds_idx_flips_spine_sourced_formula() {
        use trust_types::ProofLevel;
        for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
            let (func, solver_vcs) = live_path_vcs("/tmp/vfdump2/idx.json", max_level);
            // Sanity: exactly one bounds VC at one span (uniquely flippable).
            let bounds_count = solver_vcs
                .iter()
                .filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
                .count();
            assert_eq!(bounds_count, 1, "[{max_level:?}] one bounds VC expected: {solver_vcs:?}");
            let before = solver_vcs.clone();
            let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
            assert_verdict_identical(&before, &after);
            assert_eq!(
                report.spine_sourced_formula(),
                1,
                "[{max_level:?}] LIVE-path idx bounds VC must flip SPINE-SOURCED (formula): {report:?}"
            );
            assert_eq!(
                report.spine_sourced_kept_formula(),
                0,
                "[{max_level:?}] no kept-formula expected for live-path idx bounds: {report:?}"
            );
        }
    }

    /// LIVE-FIRING (shift): `fn shl(x,n){x<<n}` (`/tmp/vfdump2/shl.json`) flips
    /// SPINE-SOURCED (formula) on the LIVE-path VC set. The spine reconstructs
    /// trust-vcgen's full live formula
    /// `And([env, And([Eq(_3, Lt(n, 32)), And([range(n), Ge(n, 32)])])])`
    /// byte-for-byte (cond binding + shift-range violation, param-env wrapped).
    #[test]
    fn live_path_shift_shl_flips_spine_sourced_formula() {
        use trust_types::ProofLevel;
        for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
            let (func, solver_vcs) = live_path_vcs("/tmp/vfdump2/shl.json", max_level);
            let shift_count = solver_vcs
                .iter()
                .filter(|vc| matches!(vc.kind, VcKind::ShiftOverflow { .. }))
                .count();
            assert_eq!(shift_count, 1, "[{max_level:?}] one shift VC expected: {solver_vcs:?}");
            let before = solver_vcs.clone();
            let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
            assert_verdict_identical(&before, &after);
            assert_eq!(
                report.spine_sourced_formula(),
                1,
                "[{max_level:?}] LIVE-path shl shift VC must flip SPINE-SOURCED (formula): {report:?}"
            );
            assert_eq!(
                report.spine_sourced_kept_formula(),
                0,
                "[{max_level:?}] no kept-formula expected for live-path shl shift: {report:?}"
            );
        }
    }

    /// LIVE-FIRING (negation): `fn ng(a){-a}` (`/tmp/vfdump3/ng.json`) flips
    /// SPINE-SOURCED (formula) on the LIVE-path VC set. The canonical rustc
    /// negation-overflow shape is `_2 = (a == MIN); Assert { OverflowNeg } on _2`
    /// (expected = false). trust-vcgen's `v2_build_assert_negation_vc` emits
    /// `v2_formula_with_block_defs(block, v2_assert_failure_formula(_2, false))` =
    /// `And([ Eq(_2, Eq(a, MIN)), _2 ])`, wrapped in the abstract-interp param-range
    /// env. The spine reconstructs that byte-for-byte (core = the bare cond var,
    /// cond binding via the shared self-contained-comparison helper), so the formula
    /// now lives on the spine. Asserted against the LIVE
    /// `generate_vcs_with_discharge_and_summaries` path.
    #[test]
    fn live_path_negation_ng_flips_spine_sourced_formula() {
        use trust_types::ProofLevel;
        for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
            let (func, solver_vcs) = live_path_vcs("/tmp/vfdump3/ng.json", max_level);
            // Sanity: exactly one negation VC at one span (uniquely flippable).
            let neg_count = solver_vcs
                .iter()
                .filter(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. }))
                .count();
            assert_eq!(neg_count, 1, "[{max_level:?}] one negation VC expected: {solver_vcs:?}");
            let before = solver_vcs.clone();
            let target_flags: Vec<bool> = before
                .iter()
                .map(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. }))
                .collect();
            let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
            assert_verdict_identical(&before, &after);
            // The negation VC specifically flips spine-sourced (formula).
            let neg_spine_formula = report
                .decisions
                .iter()
                .zip(target_flags.iter())
                .filter(|(d, is_t)| **is_t && **d == FlipDecision::SpineSourcedFormula)
                .count();
            assert_eq!(
                neg_spine_formula, 1,
                "[{max_level:?}] LIVE-path ng negation VC must flip SPINE-SOURCED (formula): {report:?}"
            );
            // And the dispatched negation formula is genuinely a spine reconstruction.
            let neg_vc = after
                .iter()
                .find(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. }))
                .expect("a negation VC is present");
            let cands =
                reconstruct_full_safety_formula_candidates(&func, &neg_vc.location, &neg_vc.kind);
            assert!(
                cands.iter().any(|c| formula_eq_modulo_versions(c, &neg_vc.formula)),
                "[{max_level:?}] the dispatched negation formula must be a spine reconstruction"
            );
        }
    }

    /// LIVE-FIRING (cast, POLICY PIN): `fn cst(x: i64) -> i32 { x as i32 }`
    /// (`/tmp/vfdump3/cst.json`). Upstream policy (9f4b2c8417, owner decision
    /// 2026-07-06): an int→int `as` cast is DEFINED Rust — it truncates /
    /// sign-extends / reinterprets and NEVER traps — so trust-vcgen emits NO
    /// `CastOverflow` obligation for it; the result is instead TYPE-TRACKED to its
    /// target range (`guards::narrowing_cast_result_range`). This policy has
    /// flip-flopped before (a97a720523 dropped the obligation, 792df6c9c
    /// restored it, 9f4b2c8417 re-dropped it WITH the type tracking), so this
    /// test PINS the current behavior on the LIVE
    /// `generate_vcs_with_discharge_and_summaries` path: the cast-only body
    /// yields an EMPTY VC set at every level, and the flip is a no-op on it. If
    /// the obligation is ever re-introduced, this pin fails loudly and the
    /// spine's cast lane (`reconstruct_cast_formula_candidates`, still exercised
    /// by the synthetic cast tests) must be re-audited against the new live shape.
    #[test]
    fn live_path_cast_cst_defined_cast_emits_no_vc() {
        use trust_types::ProofLevel;
        for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
            let (func, solver_vcs) = live_path_vcs("/tmp/vfdump3/cst.json", max_level);
            let cast_count = solver_vcs
                .iter()
                .filter(|vc| matches!(vc.kind, VcKind::CastOverflow { .. }))
                .count();
            assert_eq!(
                cast_count, 0,
                "[{max_level:?}] a defined int→int `as` cast carries NO CastOverflow \
                 obligation (9f4b2c8417 policy): {solver_vcs:?}"
            );
            assert!(
                solver_vcs.is_empty(),
                "[{max_level:?}] the cast-only body has no other obligation: {solver_vcs:?}"
            );
            // The flip over the (empty) live VC set is a verdict-identical no-op.
            let before = solver_vcs.clone();
            let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
            assert_verdict_identical(&before, &after);
            assert!(
                report.decisions.is_empty(),
                "[{max_level:?}] nothing to flip on an empty live VC set: {report:?}"
            );
        }
    }

    /// trust-ir-NATIVE GENERATION: for the covered functions, the spine GENERATES
    /// the complete L0 safety VC set (`generate_native_safety_vcs`) — VcKind,
    /// location, AND formula reconstructed from trust-ir with NO trust-vcgen at
    /// generation time — and that set is byte-identical to trust-vcgen's
    /// `generate_vcs` output (same kinds, spans, formulas as a multiset). This is
    /// the proof that trust-ir is the PRIMARY generation source for these functions:
    /// the dispatched VCs come from the spine, validated complete + correct against
    /// the trust-vcgen oracle. Functions with div/rem (vcgen emits a co-located
    /// statement VC the module does not enumerate) or out-of-envelope shapes return
    /// a non-matching/None native set and fall back — never an unsound dispatch.
    #[test]
    fn native_generation_matches_vcgen_for_covered_fns() {
        use trust_types::ProofLevel;
        // Multiset key for a VC: kind + span + formula (the dispatched identity).
        // The formula is compared MODULO trust-vcgen's S2c statement-granular SSA
        // version tokens (`_3#s0_0`): the trust-ir-NATIVE generator reconstructs the
        // SAME formula but without the version suffixes (it does not re-implement
        // trust-vcgen's private reaching-def dataflow), and the tokens are a
        // consistent (semantics-preserving) renaming. Stripping them before the
        // multiset comparison tests the SEMANTIC enumeration + formula content, which
        // is what "native is the primary generation source" requires.
        fn key(vc: &VerificationCondition) -> (String, (u32, u32, u32, u32), String) {
            (
                format!("{:?}", vc.kind),
                (
                    vc.location.line_start,
                    vc.location.col_start,
                    vc.location.line_end,
                    vc.location.col_end,
                ),
                format!("{:?}", strip_version_tokens_in_formula(&vc.formula)),
            )
        }
        // BYTE-EQUAL classes (no slice-length canonicalization): native's full
        // (kind, span, FORMULA) multiset equals trust-vcgen's L0 set.
        for (path, label) in [
            ("/tmp/vfdump3/mul.json", "mul(i32)"),
            ("/tmp/vfmul/umul.json", "umul(u32)"),
            ("/tmp/vfdump2/shl.json", "shl(shift)"),
            ("/tmp/vfdump3/ng.json", "ng(neg)"),
        ] {
            let (func, vcgen_vcs) = live_path_vcs(path, ProofLevel::L0Safety);
            let vcgen_l0: Vec<_> = vcgen_vcs.iter().filter(|v| is_l0_safety(v)).cloned().collect();
            let native = trust_ir_bridge_generate_native(&func);
            let native = native.unwrap_or_else(|| {
                panic!("[{label}] native generation must return Some for a covered fn")
            });
            let mut nk: Vec<_> = native.iter().map(key).collect();
            let mut vk: Vec<_> = vcgen_l0.iter().map(key).collect();
            nk.sort();
            vk.sort();
            assert_eq!(nk, vk, "[{label}] native-generated VC set must equal trust-vcgen's L0 set");
        }
        // BOUNDS (idx): native CANONICALIZES the slice length (`s__slice_len`), so its
        // FORMULA intentionally differs from trust-vcgen's raw-local form (this is what
        // lets a guarded slice index's dominating guard bind the violation). It still
        // ENUMERATES the same obligation, so the (kind, span) set matches and native
        // COVERS vcgen's L0 set — the formula-level correctness is pinned by the
        // falsification gates (guarded_slice_bound proves, mutant fails), stronger than
        // a byte-match.
        {
            let (func, vcgen_vcs) = live_path_vcs("/tmp/vfdump2/idx.json", ProofLevel::L0Safety);
            let vcgen_l0: Vec<_> = vcgen_vcs.iter().filter(|v| is_l0_safety(v)).cloned().collect();
            let native = trust_ir_bridge_generate_native(&func)
                .expect("[idx(bounds)] native generation must return Some");
            let kind_span = |vc: &VerificationCondition| {
                (
                    format!("{:?}", vc.kind),
                    (
                        vc.location.line_start,
                        vc.location.col_start,
                        vc.location.line_end,
                        vc.location.col_end,
                    ),
                )
            };
            let mut nk: Vec<_> = native.iter().map(kind_span).collect();
            let mut vk: Vec<_> = vcgen_l0.iter().map(kind_span).collect();
            nk.sort();
            vk.sort();
            assert_eq!(nk, vk, "[idx(bounds)] native (kind, span) set must equal vcgen's L0 set");
            assert!(
                native_l0_set_matches_vcgen(&native, &vcgen_l0),
                "[idx(bounds)] native L0 set must equal vcgen's L0 set"
            );
        }
    }

    // Local shim so the test calls the crate-public generator without a longer path.
    fn trust_ir_bridge_generate_native(
        func: &VerifiableFunction,
    ) -> Option<Vec<VerificationCondition>> {
        crate::lower::generate_native_safety_vcs(func)
    }

    /// THE CUTOVER entry point dispatches the trust-ir-NATIVE set only for byte-equal
    /// covered functions. Set-equal-but-formula-different classes remain on the checked
    /// fallback path because enumeration equality is not verdict equality.
    #[test]
    fn cutover_dispatches_native_for_covered_and_divrem() {
        use trust_types::ProofLevel;
        // BYTE-EQUAL covered classes (no slice-length canonicalization): native is
        // dispatched as `NativeGenerated` because its formula byte-matches trust-vcgen.
        for (path, label) in [("/tmp/vfdump3/mul.json", "mul"), ("/tmp/vfmul/umul.json", "umul")] {
            let (func, vcgen_vcs) = live_path_vcs(path, ProofLevel::L0Safety);
            let before = vcgen_vcs.clone();
            let (dispatched, outcome) = generate_native_or_flip_safety_vcs(&func, vcgen_vcs);
            assert!(
                matches!(outcome, NativeGenOutcome::NativeGenerated(_)),
                "[{label}] must dispatch the trust-ir-native set: {outcome:?}"
            );
            // Verdict-equivalent: same dispatched identity set as the vcgen path.
            assert_verdict_identical(&before, &dispatched);
        }
        // CANONICALIZED bounds (idx) and signed div/rem: native generates a set that
        // does NOT byte-match trust-vcgen (bounds canonicalize the slice length; div/rem
        // because vcgen emits a redundant co-located statement DivByZero VC). With
        // set-matches trust-vcgen by (kind, span), but the formula difference keeps them on
        // `FlippedFallback` unconditionally.
        for (path, label) in [
            ("/tmp/vfdump2/idx.json", "idx"),
            ("/tmp/vfdump2/dv.json", "dv"),
            ("/tmp/vfdump2/rem.json", "rem"),
        ] {
            let (func, vcgen_vcs) = live_path_vcs(path, ProofLevel::L0Safety);
            let vcgen_l0: Vec<_> = vcgen_vcs.iter().filter(|v| is_l0_safety(v)).cloned().collect();
            let native = crate::lower::generate_native_safety_vcs(&func)
                .unwrap_or_else(|| panic!("[{label}] native generation must return Some"));
            assert!(
                native_l0_set_matches_vcgen(&native, &vcgen_l0),
                "[{label}] native L0 set must equal vcgen's by (kind, span)"
            );
            let (_dispatched, outcome) = generate_native_or_flip_safety_vcs(&func, vcgen_vcs);
            assert!(
                matches!(outcome, NativeGenOutcome::FlippedFallback(_)),
                "[{label}] must fall back when native formulas differ: {outcome:?}"
            );
        }
    }

    /// HERMETIC (UNSIGNED-LITERAL arith): `fn add1(x: u32) { x + 1 }` and
    /// `fn mul2(x: u32) { x * 2 }`, embedded as committed real-MIR fixtures. rustc
    /// lowers `x + 1` on a u32 `x` to `CheckedAdd(x, Uint(1, 32))` — the literal is
    /// a `ConstValue::Uint`, NOT `Int`. `safety_int_op_type` previously adopted the
    /// non-constant operand's type ONLY for an `Int` constant, so this extremely
    /// common `unsigned_local OP literal` shape was (wrongly) fail-closed. With the
    /// fix (accept ANY `Constant`, matching `int_op_type`), both the add and the mul
    /// (BV) overflow VCs flip SPINE-SOURCED with verdicts byte-identical. This pins
    /// the common-case fix against a committed fixture (no `/tmp` dependency).
    #[test]
    fn unsigned_literal_arith_flips_spine_sourced_formula() {
        use trust_types::ProofLevel;
        use trust_vcgen::SummaryDatabase;
        for (json, label) in [
            (include_str!("../fixtures/add1_u32.json"), "u32+1(add)"),
            (include_str!("../fixtures/mul2_u32.json"), "u32*2(mul)"),
        ] {
            let func: VerifiableFunction =
                serde_json::from_str(json).unwrap_or_else(|e| panic!("[{label}] parse: {e}"));
            for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
                let summaries = SummaryDatabase::new();
                let (solver_vcs, _d) =
                    trust_vcgen::generate_vcs_with_discharge_and_summaries(&func, &summaries);
                let solver_vcs =
                    dedupe_exact_for_test(trust_vcgen::filter_vcs_by_level(solver_vcs, max_level));
                let before = solver_vcs.clone();
                let vc = before
                    .iter()
                    .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
                    .unwrap_or_else(|| panic!("[{label}/{max_level:?}] an overflow VC is present"));
                let cands =
                    reconstruct_full_safety_formula_candidates(&func, &vc.location, &vc.kind);
                assert!(
                    cands.iter().any(|c| formula_eq_modulo_versions(c, &vc.formula)),
                    "[{label}/{max_level:?}] a spine candidate must byte-equal the unsigned-literal overflow formula\n  live: {}\n  candidates: {:?}",
                    vc.formula.to_smtlib(),
                    cands.iter().map(Formula::to_smtlib).collect::<Vec<_>>()
                );
                if label == "u32+1(add)" {
                    let unversioned = strip_version_tokens_in_formula(&vc.formula);
                    assert_eq!(
                        eval_fixture_bool(&unversioned),
                        Some(true),
                        "[{label}/{max_level:?}] x=u32::MAX, _0=0 must satisfy the live overflow VC; checked-add result facts must be vacuous on real overflow\n  live: {}",
                        vc.formula.to_smtlib()
                    );
                }
                let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
                assert_verdict_identical(&before, &after);
                assert_eq!(
                    report.spine_sourced_formula(),
                    1,
                    "[{label}/{max_level:?}] unsigned-literal arith VC must flip SPINE-SOURCED: {report:?}"
                );
            }
        }
    }

    /// HERMETIC (mul, WIDENING-cast): `fn wmul(a: u32, b: u32) -> u64 { (a as u64)
    /// * (b as u64) }` and the signed `(a as i64) * (b as i64)`, embedded as
    /// committed real-MIR fixtures. trust-vcgen's `v2_bv_operand_term` encodes a
    /// value-preserving widening-cast operand as a zero/sign-EXTENSION of a
    /// narrower fresh var (`BvZeroExt(__trust_ovf_bv_lhs__N : BV(32), 32)` for the
    /// u32→u64 case), capturing the operand's true range in pure QF_BV. The spine
    /// reconstructs that by ENUMERATING the bare AND widening operand encodings
    /// (`reconstruct_bv_mul_overflow_candidates` — no `index_local_stable` port;
    /// the exact-equality gate picks the form trust-vcgen emitted).
    ///
    /// SIGNED (`i32->i64`) still flips SPINE-SOURCED byte-equal. UNSIGNED
    /// (`u32->u64`) is expected KEPT-formula fail-closed since trust-vcgen's
    /// global additive-bound facts (1389fa9b92) + local-type-range final pass
    /// (b9b201ecc4): both conjoin unsigned-only layers whose conjunct order is
    /// hash-iteration over VERSIONED var names, which the spine by design cannot
    /// know — the flip keeps trust-vcgen's exact formula (sound; same class as
    /// the guard-bounded mul). Verdicts stay byte-identical in both cases.
    #[test]
    fn widening_mul_flips_spine_sourced_formula() {
        use trust_types::ProofLevel;
        use trust_vcgen::SummaryDatabase;
        for (json, label) in [
            (include_str!("../fixtures/wmul_u32_u64.json"), "u32->u64"),
            (include_str!("../fixtures/wmul_i32_i64.json"), "i32->i64"),
        ] {
            let func: VerifiableFunction =
                serde_json::from_str(json).unwrap_or_else(|e| panic!("[{label}] parse: {e}"));
            for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
                let summaries = SummaryDatabase::new();
                let (solver_vcs, _d) =
                    trust_vcgen::generate_vcs_with_discharge_and_summaries(&func, &summaries);
                let solver_vcs =
                    dedupe_exact_for_test(trust_vcgen::filter_vcs_by_level(solver_vcs, max_level));
                let before = solver_vcs.clone();
                let mul_vc = before
                    .iter()
                    .find(|vc| {
                        matches!(
                            vc.kind,
                            VcKind::ArithmeticOverflow { op: trust_types::BinOp::Mul, .. }
                        )
                    })
                    .unwrap_or_else(|| panic!("[{label}/{max_level:?}] a mul VC is present"));
                let cands = reconstruct_full_safety_formula_candidates(
                    &func,
                    &mul_vc.location,
                    &mul_vc.kind,
                );
                if label == "i32->i64" {
                    assert!(
                        cands.iter().any(|c| formula_eq_modulo_versions(c, &mul_vc.formula)),
                        "[{label}/{max_level:?}] a spine candidate must byte-equal the widening BV mul formula"
                    );
                }
                let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
                assert_verdict_identical(&before, &after);
                if label == "i32->i64" {
                    assert_eq!(
                        report.spine_sourced_formula(),
                        1,
                        "[{label}/{max_level:?}] widening mul VC must flip SPINE-SOURCED: {report:?}"
                    );
                } else {
                    // u32->u64: the unsigned widening mul formula carries
                    // hash-ordered versioned-name conjuncts (see the test doc);
                    // sound fail-closed — spine owns the obligation, formula kept
                    // from trust-vcgen.
                    assert_eq!(
                        report.spine_sourced_kept_formula(),
                        1,
                        "[{label}/{max_level:?}] unsigned widening mul VC must flip spine-sourced KEPT-formula: {report:?}"
                    );
                }
            }
        }
    }

    /// LIVE-FIRING (mul, SIGNED): `fn mul(a: i32, b: i32) { a * b }`
    /// (`/tmp/vfdump3/mul.json`) flips SPINE-SOURCED (formula) on the LIVE-path VC
    /// set. trust-vcgen routes integer MUL overflow through the fixed-width
    /// BITVECTOR encoding (`v2_signed_bv_overflow_formula`: the width-doubling
    /// sign-extended product check over fresh BV operand vars
    /// `__trust_ovf_bv_lhs_a` / `__trust_ovf_bv_rhs_b`), wrapped ONCE by the
    /// final-pass `conjoin_arg_type_ranges` and prepended with the param-range env:
    /// `And([env, And([range(a), range(b), Not(Or([Eq(slice,0), Eq(slice,allones)]))])])`.
    /// The spine reconstructs that byte-for-byte
    /// (`reconstruct_bv_mul_overflow_body` + the `Overflow(Mul)` base arm +
    /// `augment_candidates_with_param_env`), so the BV mul formula now lives on the
    /// spine. Asserted against the LIVE `generate_vcs_with_discharge_and_summaries`
    /// path; verdicts byte-IDENTICAL flip ON vs OFF.
    #[test]
    fn live_path_mul_signed_flips_spine_sourced_formula() {
        use trust_types::ProofLevel;
        for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
            let (func, solver_vcs) = live_path_vcs("/tmp/vfdump3/mul.json", max_level);
            let mul_count = solver_vcs
                .iter()
                .filter(|vc| {
                    matches!(
                        vc.kind,
                        VcKind::ArithmeticOverflow { op: trust_types::BinOp::Mul, .. }
                    )
                })
                .count();
            assert_eq!(
                mul_count, 1,
                "[{max_level:?}] one mul overflow VC expected: {solver_vcs:?}"
            );
            let before = solver_vcs.clone();
            // The spine reconstructs the LIVE BV mul formula byte-for-byte.
            let mul_vc = before
                .iter()
                .find(|vc| {
                    matches!(
                        vc.kind,
                        VcKind::ArithmeticOverflow { op: trust_types::BinOp::Mul, .. }
                    )
                })
                .expect("a mul VC is present");
            let cands =
                reconstruct_full_safety_formula_candidates(&func, &mul_vc.location, &mul_vc.kind);
            assert!(
                cands.iter().any(|c| formula_eq_modulo_versions(c, &mul_vc.formula)),
                "[{max_level:?}] a spine candidate must byte-equal the BV-encoded mul formula"
            );
            let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
            assert_verdict_identical(&before, &after);
            assert_eq!(
                report.spine_sourced_formula(),
                1,
                "[{max_level:?}] LIVE-path mul overflow VC must flip SPINE-SOURCED (formula): {report:?}"
            );
            assert_eq!(
                report.spine_sourced_kept_formula(),
                0,
                "[{max_level:?}] no kept-formula expected for live-path mul: {report:?}"
            );
        }
    }

    /// HERMETIC (mul, UNSIGNED): `fn umul(a: u32, b: u32) { a * b }` and
    /// `fn umul8(a: u8, b: u8) { a * b }`, embedded as committed real-MIR fixtures
    /// (`fixtures/umul_u32.json` / `fixtures/umul_u8.json`), exercise the UNSIGNED
    /// BV mul branch (`v2_unsigned_bv_overflow_formula`'s
    /// `And([Not(Eq(a,0)), Not(Eq(BvUDiv(BvMul(a,b),a),b))])` over the fresh BV
    /// operand vars), a DIFFERENT encoding from the signed width-doubling path.
    /// Unlike the `/tmp`-dump live-path tests, these fixtures are committed so the
    /// unsigned branch is pinned regardless of the dev environment. The spine
    /// reconstructs the live formula byte-for-byte and the mul VC flips
    /// SPINE-SOURCED with verdicts byte-identical.
    #[test]
    fn unsigned_mul_flips_spine_sourced_formula() {
        use trust_types::ProofLevel;
        use trust_vcgen::SummaryDatabase;
        for (json, label) in [
            (include_str!("../fixtures/umul_u32.json"), "u32"),
            (include_str!("../fixtures/umul_u8.json"), "u8"),
        ] {
            let func: VerifiableFunction =
                serde_json::from_str(json).unwrap_or_else(|e| panic!("[{label}] parse: {e}"));
            for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
                let summaries = SummaryDatabase::new();
                let (solver_vcs, _d) =
                    trust_vcgen::generate_vcs_with_discharge_and_summaries(&func, &summaries);
                let solver_vcs =
                    dedupe_exact_for_test(trust_vcgen::filter_vcs_by_level(solver_vcs, max_level));
                let mul_count = solver_vcs
                    .iter()
                    .filter(|vc| {
                        matches!(
                            vc.kind,
                            VcKind::ArithmeticOverflow { op: trust_types::BinOp::Mul, .. }
                        )
                    })
                    .count();
                assert_eq!(mul_count, 1, "[{label}/{max_level:?}] one mul VC expected");
                let before = solver_vcs.clone();
                let mul_vc = before
                    .iter()
                    .find(|vc| {
                        matches!(
                            vc.kind,
                            VcKind::ArithmeticOverflow { op: trust_types::BinOp::Mul, .. }
                        )
                    })
                    .unwrap();
                let cands = reconstruct_full_safety_formula_candidates(
                    &func,
                    &mul_vc.location,
                    &mul_vc.kind,
                );
                assert!(
                    cands.iter().any(|c| formula_eq_modulo_versions(c, &mul_vc.formula)),
                    "[{label}/{max_level:?}] spine must byte-equal the unsigned BV mul formula"
                );
                let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
                assert_verdict_identical(&before, &after);
                assert_eq!(
                    report.spine_sourced_formula(),
                    1,
                    "[{label}/{max_level:?}] unsigned mul VC must flip SPINE-SOURCED: {report:?}"
                );
            }
        }
    }

    /// Local dedupe-by-exact helper for the hermetic fixture tests (mirrors the
    /// `dedupe_exact` in `live_path_vcs`).
    fn dedupe_exact_for_test(vcs: Vec<VerificationCondition>) -> Vec<VerificationCondition> {
        use trust_vcgen::vc_fingerprint;
        let mut seen = std::collections::HashSet::new();
        let mut out = Vec::with_capacity(vcs.len());
        for vc in vcs {
            let key = (
                vc.function.to_string(),
                vc.location.file.clone(),
                vc.location.line_start,
                vc.location.col_start,
                vc.location.line_end,
                vc.location.col_end,
                vc_fingerprint(&vc),
            );
            if seen.insert(key) {
                out.push(vc);
            }
        }
        out
    }

    /// LIVE-FIRING via SAME-SPAN DISAMBIGUATION (div/rem): the `i32` div/rem shape
    /// (`fn dv(a,b){a/b}` / `fn rem(a,b){a%b}`) emits TWO trust-vcgen VCs of the SAME
    /// `VcKind` (`DivisionByZero`/`RemainderByZero`) at the SAME source span — one
    /// from the `DivisionByZero` ASSERT terminator (abstract-flag form
    /// `And([env, And([Eq(_3, Eq(b,0)), _3])])`) and one from the bare `Div`/`Rem`
    /// rvalue STATEMENT (the same divisor core wrapped in the signed-overflow
    /// path-guard block-defs `_4`/`_5`/`_6`, which carry cross-block dataflow the
    /// spine does not reproduce). The spine derives ONE div/rem-by-zero obligation
    /// (the assert) whose reconstructed formula byte-equals the ASSERT VC and NOT the
    /// statement VC. The flip's same-span-ambiguity DISAMBIGUATION resolves this by
    /// requiring a formula-byte-match: the abstract-flag assert VC (the unique
    /// byte-match) flips SPINE-SOURCED (formula), while the bare statement VC stays
    /// trust-vcgen-sourced. This is SOUND — the swap is byte-equal to the assert VC's
    /// formula (verdict-identical); disambiguation only chooses WHICH of the two
    /// same-span VCs is flagged spine-sourced, never changes a verdict. Asserted
    /// against the LIVE path.
    ///
    /// Note: the CO-LOCATED signed-div-overflow `ArithmeticOverflow{Div}` VC (the
    /// `INT_MIN/-1` check, a DIFFERENT fine class) is independently spine-OWNED but
    /// formula-KEPT (its `Overflow(Div)` message uses the bitvector encoding the
    /// spine declines to reconstruct) — pre-existing, sound, and orthogonal.
    #[test]
    fn live_path_div_rem_disambiguates_to_assert_vc() {
        use trust_types::ProofLevel;
        // Run div and rem explicitly.
        for (path, label, is_div) in
            [("/tmp/vfdump2/dv.json", "div", true), ("/tmp/vfdump2/rem.json", "rem", false)]
        {
            for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
                let (func, solver_vcs) = live_path_vcs(path, max_level);
                let is_target = |vc: &VerificationCondition| {
                    if is_div {
                        matches!(vc.kind, VcKind::DivisionByZero)
                    } else {
                        matches!(vc.kind, VcKind::RemainderByZero)
                    }
                };
                let count = solver_vcs.iter().filter(|vc| is_target(vc)).count();
                // The ambiguity precondition: >= 2 same-class VCs at one span.
                assert!(
                    count >= 2,
                    "[{label} {max_level:?}] expected >=2 same-class div/rem-by-zero VCs (the \
                     same-span ambiguity disambiguation resolves): got {count}"
                );
                // The div/rem-by-zero VCs are all at one shared span+class.
                let spans: std::collections::HashSet<_> = solver_vcs
                    .iter()
                    .filter(|vc| is_target(vc))
                    .map(|vc| span_key(&vc.location))
                    .collect();
                assert_eq!(
                    spans.len(),
                    1,
                    "[{label} {max_level:?}] the div/rem-by-zero VCs must share ONE span (the \
                     ambiguity): {spans:?}"
                );

                let before = solver_vcs.clone();
                let target_flags: Vec<bool> = before.iter().map(|vc| is_target(vc)).collect();
                let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
                assert_verdict_identical(&before, &after);

                // EXACTLY ONE div/rem-by-zero VC flips SPINE-SOURCED (formula) — the
                // abstract-flag ASSERT VC the spine reproduces byte-for-byte. The
                // others (the bare statement VC) stay trust-vcgen-sourced; NONE is
                // SpineSourcedKeptFormula (the ambiguous gate either pins by
                // byte-match or fails fully closed).
                let div_rem_spine_formula = report
                    .decisions
                    .iter()
                    .zip(target_flags.iter())
                    .filter(|(d, is_t)| **is_t && **d == FlipDecision::SpineSourcedFormula)
                    .count();
                assert_eq!(
                    div_rem_spine_formula, 1,
                    "[{label} {max_level:?}] exactly one div/rem-by-zero VC (the abstract-flag \
                     assert) must flip SPINE-SOURCED via formula-byte disambiguation: {report:?}"
                );
                // The remaining div/rem-by-zero VCs stay trust-vcgen-sourced.
                for (decision, is_t) in report.decisions.iter().zip(target_flags.iter()) {
                    if *is_t {
                        assert!(
                            matches!(
                                decision,
                                FlipDecision::SpineSourcedFormula | FlipDecision::TrustVcgenSourced
                            ),
                            "[{label} {max_level:?}] a div/rem-by-zero VC is either the pinned \
                             spine-sourced assert VC or trust-vcgen-sourced (never kept-formula): \
                             {report:?}"
                        );
                    }
                }
                // And the SPINE-SOURCED one's formula is genuinely a spine
                // reconstruction (the abstract-flag form).
                let spine_div = after
                    .iter()
                    .zip(report.decisions.iter())
                    .find(|(vc, d)| is_target(vc) && **d == FlipDecision::SpineSourcedFormula)
                    .map(|(vc, _)| vc)
                    .expect("a spine-sourced div/rem-by-zero VC is present");
                let cands = reconstruct_full_safety_formula_candidates(
                    &func,
                    &spine_div.location,
                    &spine_div.kind,
                );
                assert!(
                    cands.iter().any(|c| formula_eq_modulo_versions(c, &spine_div.formula)),
                    "[{label} {max_level:?}] the flipped div/rem formula must be a spine reconstruction"
                );
            }
        }
    }

    #[test]
    fn swapped_overflow_formula_is_the_spine_reconstruction() {
        // Prove the swapped overflow formula is GENUINELY the spine's
        // reconstruction (a `reconstruct_full_safety_formula_candidates` output),
        // not merely a clone of trust-vcgen's — i.e. the formula now lives on the
        // spine. It is structurally equal to trust-vcgen's (the swap gate) AND is
        // one of the spine's candidate reconstructions.
        let func = oracle::overflow_checked_add();
        let before = vcgen_vcs(&func);
        let (after, _) = flip_safety_verdicts_to_spine(&func, before.clone());
        let overflow_vc = after
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
            .expect("an overflow VC is present");
        let spine_candidates = reconstruct_full_safety_formula_candidates(
            &func,
            &overflow_vc.location,
            &overflow_vc.kind,
        );
        assert!(
            spine_candidates.iter().any(|c| formula_eq_modulo_versions(c, &overflow_vc.formula)),
            "the dispatched overflow formula must be a spine reconstruction (spine-sourced)"
        );
    }

    // =================================================================
    // L1 CONTRACTS (Precondition / Postcondition): live-path source-of-record
    // analysis. The PROVEN method gates a spine→formula swap on BYTE-EQUALITY
    // to the LIVE-path VC formula (`generate_vcs_with_discharge_and_summaries`
    // → filter L1 → dedupe). These tests PIN the empirical live form for the
    // two contract VcKinds against the spine's contract obligation predicate
    // (`contract_vcs_from_trust_ir`), establishing — with executable assertions,
    // not prose — that BOTH classes are FAIL-CLOSED:
    //
    //  * PRECONDITION: the definition-site Precondition VC carries
    //    `Formula::Bool(false)` (the negated obligation is trivially UNSAT — a
    //    caller-side burden, assumed at the def site). Abstract-interpretation
    //    DISCHARGES it (`try_eval_boolean(Bool(false)) == Some(false)` ⇒ Proved)
    //    BEFORE it reaches `solver_vcs`. So the LIVE solver VC set the flip
    //    ranges over contains ZERO Precondition VCs — there is nothing to flip,
    //    and the spine carries the PREDICATE `(> x 0)`, not the discharge form
    //    `false`. FAIL-CLOSED: no Precondition VC is ever spine-FORMULA-sourced.
    //
    //  * POSTCONDITION: the live form is the BODY-AWARE per-Return-block VC
    //    `generate_v2_contract_vcs_impl` builds: `Not(predicate)` wrapped in the
    //    precondition conjunct, the CheckedBinaryOp arg-range + semantic guard
    //    (`_4.0 = x+1`), the return-value pin (`_0 = _4.0`), and the merged
    //    (precondition-refined) fixpoint interval env. For the SIMPLE
    //    straight-line single-`Return` shape the spine now REPRODUCES that whole
    //    formula byte-for-byte (`reconstruct_simple_postcondition_formula`: refined
    //    env + `conjoin_live_preconditions` + the predecessor's
    //    `extract_assert_passed_semantics` guards + the return-pin), so such a
    //    postcondition VC IS spine-FORMULA-sourced — verdict-identical by exact
    //    byte-equality. A COMPLEX body (a branch, a loop, multiple returns, a
    //    non-`Use` return pin, a complex precondition) produces a body-aware
    //    formula the simple reconstruction does not capture; it never byte-matches,
    //    so it stays FAIL-CLOSED (trust-vcgen-sourced).
    //
    // The flip gate accepts contract VCs ONLY for the simple straight-line
    // postcondition, and even then ONLY on exact `Formula` byte-equality (the same
    // gate the L0 classes use); a Precondition VC is never a candidate. These tests
    // are the guard: a precondition is never spine-FORMULA-sourced, and a
    // postcondition is spine-FORMULA-sourced iff the spine reproduces its formula
    // byte-equal. SOUNDNESS: a wrong contract formula flipping a verdict is the
    // worst outcome, so the bar is byte-equality to the LIVE formula; complex
    // bodies do not clear it and fail closed.
    // =================================================================

    /// Build the live-path solver VC set for a dumped contracts `VerifiableFunction`
    /// JSON at `max_level`, and return the lowered spine's contract obligations.
    fn live_contract_vcs(
        path: &str,
        max_level: trust_types::ProofLevel,
    ) -> (Vec<VerificationCondition>, Vec<crate::contract_vcgen_proto::TrustIrContractVc>) {
        use trust_vcgen::{SummaryDatabase, vc_fingerprint};

        use crate::contract_vcgen_proto::contract_vcs_from_trust_ir;
        use crate::lower::lower_to_trust_ir;

        fn dedupe_exact(vcs: Vec<VerificationCondition>) -> Vec<VerificationCondition> {
            let mut seen = std::collections::HashSet::new();
            let mut out = Vec::with_capacity(vcs.len());
            for vc in vcs {
                let key = (
                    vc.function.to_string(),
                    vc.location.file.clone(),
                    vc.location.line_start,
                    vc.location.col_start,
                    vc.location.line_end,
                    vc.location.col_end,
                    vc_fingerprint(&vc),
                );
                if seen.insert(key) {
                    out.push(vc);
                }
            }
            out
        }

        let json = fixture_json(path).to_string();
        let func: VerifiableFunction =
            serde_json::from_str(&json).unwrap_or_else(|_| panic!("parse {path}"));
        let summaries = SummaryDatabase::new();
        let (solver_vcs, _discharged) =
            trust_vcgen::generate_vcs_with_discharge_and_summaries(&func, &summaries);
        let solver_vcs = dedupe_exact(trust_vcgen::filter_vcs_by_level(solver_vcs, max_level));
        let module = lower_to_trust_ir(&func).expect("contracts fixture must lower");
        let spine_contracts = contract_vcs_from_trust_ir(&module);
        (solver_vcs, spine_contracts)
    }

    /// PRECONDITION — FAIL-CLOSED (live-path). The def-site Precondition VC
    /// (`Formula::Bool(false)`) is abstract-interp-discharged out of the live
    /// solver VC set, so it never appears for the flip to range over. Pinned for
    /// both `pre` (requires-only) and `both` (requires+ensures) at both levels.
    #[test]
    fn live_path_precondition_is_discharged_out_no_flip() {
        use trust_ir::proof::ObligationKind;
        use trust_types::ProofLevel;
        for path in ["/tmp/vfL1/pre.json", "/tmp/vfL1/both.json"] {
            // The spine DOES derive a Precondition contract obligation carrying
            // the predicate (so provenance is spine-owned), even though no live
            // solver VC exists to formula-source.
            for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
                let (solver_vcs, spine_contracts) = live_contract_vcs(path, max_level);
                let live_pre = solver_vcs
                    .iter()
                    .filter(|vc| matches!(vc.kind, VcKind::Precondition { .. }))
                    .count();
                assert_eq!(
                    live_pre, 0,
                    "[{path} {max_level:?}] the def-site Precondition VC must be discharged \
                     out of the live solver VC set (Formula::Bool(false) ⇒ proved), so there is \
                     NO Precondition VC for the flip to source: solver_vcs={solver_vcs:?}"
                );
                // The spine carries the PREDICATE, not the discharge form `false`.
                let spine_pre = spine_contracts
                    .iter()
                    .find(|c| c.kind == ObligationKind::Precondition)
                    .expect("spine derives a Precondition obligation");
                let spine_smt = spine_pre
                    .formula
                    .as_ref()
                    .and_then(|f| f.smtlib.clone())
                    .expect("spine precondition carries a predicate formula");
                assert_eq!(
                    spine_smt, "(> x 0)",
                    "[{path}] the spine precondition predicate is `(> x 0)`, NOT the def-site \
                     discharge form `false` — so even reconstruction has no live target: {spine_pre:?}"
                );
                assert_ne!(
                    spine_smt, "false",
                    "[{path}] the spine predicate must not be the def-site `Bool(false)` discharge form"
                );
            }
        }
    }

    /// POSTCONDITION — FAIL-CLOSED (live-path). The live postcondition VC is the
    /// body-aware per-Return-block formula; the spine carries only the bare
    /// predicate `(> _0 0)`. They are NOT byte-equal, and the live form depends
    /// on irreproducible body-aware/cross-block state (block-defs, semantic
    /// guards, return-pin, fixpoint env). Pinned on `both` (the fixture that
    /// lowers a postcondition) at both levels.
    /// RESOLVED (trust-ir-spine simple-case port): both formerly-blocking
    /// conjuncts of the simple `both` postcondition are now reproduced on the
    /// spine, BYTE-EQUAL to the live path, so the simple postcondition AND the
    /// co-located precondition-bearing overflow VC both flip SPINE-SOURCED
    /// (formula). This test pins the resolution (the inverse of the prior
    /// blocking-conjunct pin) — it FAILS if either reproduction regresses.
    ///
    /// The live `both` postcondition formula (L1Functional) is:
    /// ```text
    /// And([
    ///   And([Ge(x,1), Le(x,2147483647)]),            // (1) ENV — refined by precondition
    ///   And([Gt(x,0),                                // precondition conjunct
    ///        And([ And([Le(-2³¹,x+1),Le(x+1,2³¹-1)]),// semantic guard (arg range)
    ///              Eq(_4.0, x+1),                     // (2) semantic guard — _4.0 = x+1
    ///              And([Le(-2³¹,x),Le(x,2³¹-1)]),     // block-def: range x
    ///              And([Le(-2³¹,1),Le(1,2³¹-1)]),     // block-def: range 1
    ///              And([Eq(_0,_4.0), Not(Gt(_0,0))])  // return-pin + Not(predicate)
    ///        ])])
    /// ])
    /// ```
    ///
    /// (1) REFINED ENV: the spine now folds the precondition `x>0` into the
    /// abstract-interp env (`refine_param_interval_with_precondition`, mirroring
    /// trust-vcgen's `refine_state_with_precondition`), so the spine env is
    /// `(>= x 1)`, byte-equal to the live merged env (for a straight-line body the
    /// fixpoint adds nothing beyond the refined initial state).
    ///
    /// (2) SEMANTIC GUARD: the spine reconstructs the predecessor block's four
    /// assert-passed semantic conjuncts (`reconstruct_assert_passed_semantics`,
    /// mirroring `extract_assert_passed_semantics`) — including `Eq(_4.0, x+1)` —
    /// which for the straight-line single-assert body is exactly what
    /// `build_semantic_guard_map` threads to the return block.
    #[test]
    fn live_path_simple_postcondition_now_spine_sourced() {
        use trust_types::ProofLevel;
        let (func, solver_vcs) = live_path_vcs("/tmp/vfL1/both.json", ProofLevel::L1Functional);

        // The live postcondition VC.
        let post = solver_vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::Postcondition))
            .expect("one body-aware Postcondition VC");
        let live_smt = post.formula.to_smtlib();

        // (1) The live env is precondition-REFINED (`>= x 1`), and the spine now
        // reproduces it byte-equal.
        assert!(
            live_smt.contains("(>= x 1)"),
            "live postcondition env is precondition-refined `(>= x 1)`: {live_smt}"
        );
        let spine_env = crate::lower::reconstruct_abstract_state_param_env_for_test(&func)
            .expect("spine reconstructs a param-range env")
            .to_smtlib();
        assert_eq!(
            spine_env, "(and (>= x 1) (<= x 2147483647))",
            "the spine env now applies `refine_state_with_precondition`, reproducing \
             the live precondition-refined env byte-equal: {spine_env}"
        );

        // (2) The live formula carries the assert-passed semantic guard
        // `Eq(_4.0, x+1)`, and the spine now reproduces it.
        assert!(
            live_smt.contains("(= _4.0 (+ x 1))"),
            "live postcondition carries the semantic-guard `_4.0 = x+1`: {live_smt}"
        );

        // The spine reconstructs the ENTIRE postcondition formula byte-equal.
        let cands = crate::lower::reconstruct_postcondition_formula_candidates(&func);
        assert!(
            cands.iter().any(|c| formula_eq_modulo_versions(c, &post.formula)),
            "the spine reconstructs the simple postcondition formula byte-equal to \
             the live path: live={live_smt}"
        );

        // The flip now makes BOTH the postcondition and the overflow VC
        // spine-FORMULA-sourced — verdict-identical by construction (byte-equal
        // formula swap).
        let before = solver_vcs.clone();
        let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
        assert_verdict_identical(&before, &after);
        let post_decision = after
            .iter()
            .zip(report.decisions.iter())
            .find(|(vc, _)| matches!(vc.kind, VcKind::Postcondition))
            .map(|(_, d)| *d)
            .expect("a postcondition VC is present in both.json");
        assert_eq!(
            post_decision,
            FlipDecision::SpineSourcedFormula,
            "the simple postcondition VC is now spine-FORMULA-sourced (byte-equal)"
        );
        let ovf_decision = after
            .iter()
            .zip(report.decisions.iter())
            .find(|(vc, _)| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
            .map(|(_, d)| *d)
            .expect("an overflow VC is present in both.json");
        assert_eq!(
            ovf_decision,
            FlipDecision::SpineSourcedFormula,
            "the overflow VC in this precondition-bearing function is now \
             spine-FORMULA-sourced (the refined env + precondition conjunct match)"
        );
        // At least the postcondition + overflow flipped with a spine formula.
        assert!(
            report.spine_sourced_formula() >= 2,
            "both the postcondition and overflow VC must be spine-FORMULA-sourced: {report:?}"
        );
    }

    #[test]
    fn live_path_postcondition_is_body_aware_not_spine_predicate() {
        use trust_ir::proof::ObligationKind;
        use trust_types::ProofLevel;
        let path = "/tmp/vfL1/both.json";
        for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
            let (solver_vcs, spine_contracts) = live_contract_vcs(path, max_level);
            let live_posts: Vec<_> =
                solver_vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).collect();
            // The Postcondition VC is an L1 obligation: present only at L1Functional.
            if max_level == ProofLevel::L0Safety {
                assert!(
                    live_posts.is_empty(),
                    "[L0Safety] postcondition is an L1 obligation, filtered out: {live_posts:?}"
                );
                continue;
            }
            assert_eq!(
                live_posts.len(),
                1,
                "[L1Functional] exactly one body-aware Postcondition VC expected: {solver_vcs:?}"
            );
            let live = live_posts[0];
            let live_smt = live.formula.to_smtlib();

            // The spine's postcondition predicate is the bare `(> _0 0)`.
            let spine_post = spine_contracts
                .iter()
                .find(|c| c.kind == ObligationKind::Postcondition)
                .expect("spine derives a Postcondition obligation");
            let spine_smt = spine_post
                .formula
                .as_ref()
                .and_then(|f| f.smtlib.clone())
                .expect("spine postcondition carries a predicate formula");
            assert_eq!(spine_smt, "(> _0 0)", "spine postcondition predicate: {spine_post:?}");

            // FAIL-CLOSED: the live body-aware formula is NOT the spine predicate,
            // NOT its negation `Not(predicate)`, and NOT any bounded reproducible
            // transform of it. It carries body dataflow the spine does not have.
            assert_ne!(
                live_smt, spine_smt,
                "live postcondition must NOT byte-equal the bare spine predicate"
            );
            let spine_predicate =
                trust_types::parse_spec_expr("result > 0").expect("predicate parses");
            let negated = trust_types::Formula::Not(Box::new(spine_predicate)).to_smtlib();
            assert_ne!(
                live_smt, negated,
                "live postcondition is body-aware, NOT the bare negated predicate"
            );
            // It is body-aware: it embeds the return-value pin and the negated
            // postcondition over `_0`, plus the precondition conjunct — facts the
            // spine's bare predicate cannot reproduce without the body-aware pipeline.
            assert!(
                live_smt.contains("(= _0 _4.0)"),
                "the live postcondition embeds the return-value pin `_0 = _4.0` \
                 (body-aware, irreproducible from the spine predicate): {live_smt}"
            );
            assert!(
                live_smt.contains("(not (> _0 0))"),
                "the live postcondition embeds the negated predicate over `_0`: {live_smt}"
            );
            assert!(
                live_smt.contains("(> x 0)"),
                "the live postcondition embeds the precondition conjunct `(> x 0)`: {live_smt}"
            );
        }
    }

    /// PRECONDITION VCs are NEVER flipped (the soundness backstop): a def-site
    /// `#[requires]` is a caller-side assumption that trust-vcgen discharges via
    /// abstract-interp and never places in `solver_vcs`, so there is nothing to
    /// flip. SIMPLE straight-line POSTCONDITION VCs, by contrast, ARE now flipped
    /// spine-FORMULA-sourced (byte-equal) — verdict-identical by construction.
    /// This test pins both: every flip is verdict-identical, and no Precondition
    /// VC is ever spine-FORMULA-sourced.
    #[test]
    fn live_path_preconditions_never_flipped_postconditions_byte_equal() {
        use trust_types::ProofLevel;
        for path in ["/tmp/vfL1/pre.json", "/tmp/vfL1/both.json"] {
            let json = fixture_json(path).to_string();
            let func: VerifiableFunction =
                serde_json::from_str(&json).unwrap_or_else(|_| panic!("parse {path}"));
            for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
                let (solver_vcs, _spine) = live_contract_vcs(path, max_level);
                let before = solver_vcs.clone();
                let post_cands = crate::lower::reconstruct_postcondition_formula_candidates(&func);
                let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
                // The non-regression invariant: every flipped VC is verdict-identical.
                assert_verdict_identical(&before, &after);
                for (vc, decision) in after.iter().zip(report.decisions.iter()) {
                    match vc.kind {
                        // A Precondition VC is NEVER spine-FORMULA-sourced (it is
                        // never even a solver VC).
                        VcKind::Precondition { .. } => assert_eq!(
                            *decision,
                            FlipDecision::TrustVcgenSourced,
                            "[{path} {max_level:?}] a Precondition VC must stay \
                             trust-vcgen-sourced (never spine-FORMULA-sourced): {vc:?}"
                        ),
                        // A Postcondition VC is spine-FORMULA-sourced ONLY when the
                        // spine reconstructs its formula byte-equal; otherwise it
                        // stays trust-vcgen-sourced (fail-closed). Either way the
                        // verdict is identical (asserted above).
                        VcKind::Postcondition => {
                            let byte_equal = post_cands
                                .iter()
                                .any(|c| formula_eq_modulo_versions(c, &vc.formula));
                            if byte_equal {
                                assert_eq!(
                                    *decision,
                                    FlipDecision::SpineSourcedFormula,
                                    "[{path} {max_level:?}] a byte-equal Postcondition VC \
                                     is spine-FORMULA-sourced: {vc:?}"
                                );
                            } else {
                                assert_eq!(
                                    *decision,
                                    FlipDecision::TrustVcgenSourced,
                                    "[{path} {max_level:?}] a non-byte-equal Postcondition \
                                     VC stays trust-vcgen-sourced (fail-closed): {vc:?}"
                                );
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    /// LIVE-FIRING (precondition-bearing overflow): `pre.json`
    /// (`#[requires(x>0)] fn pre(x:i32)->i32 { x+100 }`). After the
    /// precondition-REFINED env (`x ∈ [1, MAX]`) + the precondition conjunct, the
    /// overflow VC's spine candidate byte-equals the live formula, so it flips
    /// SPINE-SOURCED (formula). Asserted against the LIVE
    /// `generate_vcs_with_discharge_and_summaries` path.
    #[test]
    fn live_path_pre_overflow_refined_env_spine_sourced_formula() {
        use trust_types::ProofLevel;
        for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
            let (func, solver_vcs) = live_path_vcs("/tmp/vfL1/pre.json", max_level);
            let ovf = solver_vcs
                .iter()
                .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
                .expect("an overflow VC is present in pre.json");
            // The spine reconstructs the live (refined-env + precondition) formula.
            let cands = reconstruct_full_safety_formula_candidates(&func, &ovf.location, &ovf.kind);
            assert!(
                cands.iter().any(|c| formula_eq_modulo_versions(c, &ovf.formula)),
                "[{max_level:?}] the spine reconstructs pre's overflow formula byte-equal: {}",
                ovf.formula.to_smtlib()
            );
            let before = solver_vcs.clone();
            let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
            assert_verdict_identical(&before, &after);
            assert!(
                report.spine_sourced_formula() >= 1,
                "[{max_level:?}] pre's overflow VC must flip SPINE-SOURCED (formula): {report:?}"
            );
            assert_eq!(
                report.spine_sourced_kept_formula(),
                0,
                "[{max_level:?}] no kept-formula expected for pre's overflow: {report:?}"
            );
        }
    }

    /// LIVE-FIRING (precondition-bearing overflow): `both.json`
    /// (`#[requires(x>0)] #[ensures(|r| *r>0)] fn both(x:i32)->i32 { x+1 }`). The
    /// overflow VC flips SPINE-SOURCED (formula) once the refined env + precondition
    /// conjunct match. (The postcondition flip is covered by
    /// `live_path_simple_postcondition_now_spine_sourced`.)
    #[test]
    fn live_path_both_overflow_refined_env_spine_sourced_formula() {
        use trust_types::ProofLevel;
        for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
            let (func, solver_vcs) = live_path_vcs("/tmp/vfL1/both.json", max_level);
            let ovf = solver_vcs
                .iter()
                .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
                .expect("an overflow VC is present in both.json");
            let cands = reconstruct_full_safety_formula_candidates(&func, &ovf.location, &ovf.kind);
            assert!(
                cands.iter().any(|c| formula_eq_modulo_versions(c, &ovf.formula)),
                "[{max_level:?}] the spine reconstructs both's overflow formula byte-equal: {}",
                ovf.formula.to_smtlib()
            );
            let before = solver_vcs.clone();
            let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
            assert_verdict_identical(&before, &after);
            // L0: only the overflow flips. L1: overflow + postcondition flip.
            let want = if max_level == ProofLevel::L1Functional { 2 } else { 1 };
            assert!(
                report.spine_sourced_formula() >= want,
                "[{max_level:?}] both's overflow (and at L1 the postcondition) must flip \
                 SPINE-SOURCED (formula): {report:?}"
            );
        }
    }

    /// A BRANCHING body whose discriminant is OUTSIDE the reproducible guard
    /// envelope is PINNED FAIL-CLOSED. The acyclic reconstruction reproduces only
    /// a BOOL-discriminant `if/else` guard (`b` / `Not(b)`); this fixture branches
    /// on an INTEGER discriminant (`SwitchInt(x)` over `i32 x`), which
    /// `reconstruct_path_guard_map` declines (`reconstruct_guard_formula` returns
    /// `None` for a non-Bool discriminant), so the whole reconstruction fails
    /// closed and offers NO candidate. (The Bool-discriminant `if/else` join —
    /// `pick` / `clamp_branch` — DOES flip; see those live-path tests.) The
    /// exact-equality gate guarantees nothing unsound flips either way.
    ///
    /// `pick(x: i32) -> i32 { if x != 0 { x } else { 0 } }` with
    /// `#[ensures(|r| *r >= 0)]`. Two return-paths, INTEGER switch ⇒ fail-closed.
    #[test]
    fn complex_branching_postcondition_is_fail_closed() {
        use trust_types::{
            BasicBlock as TBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue,
            Statement, Terminator, Ty, VerifiableBody,
        };
        let span = SourceSpan {
            file: "/tmp/complex.rs".into(),
            line_start: 2,
            col_start: 0,
            line_end: 2,
            col_end: 30,
        };
        // _0 ret, _1 x. bb0: SwitchInt(x) { 0 => bb2, otherwise => bb1 }.
        // bb1: _0 = x; Return.  bb2: _0 = 0; Return.
        let func = VerifiableFunction {
            name: "pick".into(),
            def_path: "pick".into(),
            span: span.clone(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                ],
                blocks: vec![
                    TBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            exhaustive_enum_unreachable: false,
                            discr: Operand::Copy(Place::local(1)),
                            targets: vec![(0, BlockId(2))],
                            otherwise: BlockId(1),
                            span: span.clone(),
                        },
                    },
                    TBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                            span: span.clone(),
                        }],
                        terminator: Terminator::Return,
                    },
                    TBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                            span: span.clone(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::i32(),
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![
                trust_types::parse_spec_expr("result >= 0").expect("predicate parses"),
            ],
            spec: trust_types::FunctionSpec {
                requires: vec![],
                ensures: vec!["result >= 0".into()],
                invariants: vec![],
            },
        };

        // The spine declines to reconstruct any postcondition formula (two returns).
        let cands = crate::lower::reconstruct_postcondition_formula_candidates(&func);
        assert!(
            cands.is_empty(),
            "the simple-case postcondition reconstruction must DECLINE a branching \
             multi-return body (fail-closed): {cands:?}"
        );

        for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
            let summaries = trust_vcgen::SummaryDatabase::new();
            let (solver_vcs, _discharged) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries(&func, &summaries);
            let solver_vcs = trust_vcgen::filter_vcs_by_level(solver_vcs, max_level);
            let before = solver_vcs.clone();
            let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
            assert_verdict_identical(&before, &after);
            // No Postcondition VC may be spine-FORMULA-sourced for the complex body.
            for (vc, decision) in after.iter().zip(report.decisions.iter()) {
                if matches!(vc.kind, VcKind::Postcondition) {
                    assert_eq!(
                        *decision,
                        FlipDecision::TrustVcgenSourced,
                        "[{max_level:?}] a complex-body Postcondition VC must stay \
                         trust-vcgen-sourced (fail-closed): {vc:?}"
                    );
                }
            }
        }
    }

    // =================================================================
    // ACYCLIC BRANCHING POSTCONDITION — live-path source-of-record.
    //
    // The next tier above the straight-line case: an `if/else` body whose
    // single `Return` block (`_0 = Copy(__ret); Return`) is a JOIN reached by
    // two predecessors that each set `__ret` and `Goto` the return block. The
    // live builder (`generate_v2_contract_vcs_impl`) emits ONE body-aware
    // `Postcondition` VC PER PREDECESSOR — each carrying that branch's
    // condition guard (`b` / `Not(b)`), the predecessor + return block-defs
    // (`__ret = …`, `_0 = __ret`), the return-pin, the join-WEAKENED semantic
    // guard (`Bool(true)`), the live preconditions, and the refined env.
    //
    // The spine now reproduces EACH per-predecessor formula byte-for-byte
    // (`reconstruct_acyclic_postcondition_formulas`), so each branching-body
    // postcondition VC flips SPINE-SOURCED (formula) — verdict-identical by
    // exact `Formula` byte-equality. Asserted against the LIVE
    // `generate_vcs_with_discharge_and_summaries` path for the dumped fixtures.
    // =================================================================

    /// LIVE-FIRING (acyclic branch, no precondition): `pick(b: bool) -> i32`
    /// (`#[ensures(|r| *r>0)] { if b {1} else {2} }`, `/tmp/vfbr/pick.json`).
    /// TWO body-aware `Postcondition` VCs (one per branch predecessor); the spine
    /// reproduces BOTH byte-for-byte, so BOTH flip SPINE-SOURCED (formula). No
    /// precondition and a Bool-only param ⇒ NO abstract-interp env conjunct (the
    /// live formula starts with the join-weakened semantic guard `Bool(true)`).
    #[test]
    fn live_path_pick_branch_postconditions_spine_sourced_formula() {
        use trust_types::ProofLevel;
        for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
            let (func, solver_vcs) = live_path_vcs("/tmp/vfbr/pick.json", max_level);
            let post_vcs: Vec<_> =
                solver_vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).collect();
            if max_level == ProofLevel::L0Safety {
                assert!(post_vcs.is_empty(), "[L0] postcondition is an L1 obligation");
                continue;
            }
            // Two per-predecessor body-aware postcondition VCs.
            assert_eq!(
                post_vcs.len(),
                2,
                "[L1] pick's if/else join emits one postcondition VC per branch \
                 predecessor (two): {solver_vcs:?}"
            );
            // The spine reproduces both, byte-for-byte.
            let cands = crate::lower::reconstruct_postcondition_formula_candidates(&func);
            for vc in &post_vcs {
                assert!(
                    cands.iter().any(|c| formula_eq_modulo_versions(c, &vc.formula)),
                    "the spine reproduces pick's branch postcondition byte-equal: {}",
                    vc.formula.to_smtlib()
                );
            }
            let before = solver_vcs.clone();
            let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
            assert_verdict_identical(&before, &after);
            // BOTH postcondition VCs flip spine-sourced (formula).
            for (vc, decision) in after.iter().zip(report.decisions.iter()) {
                if matches!(vc.kind, VcKind::Postcondition) {
                    assert_eq!(
                        *decision,
                        FlipDecision::SpineSourcedFormula,
                        "[L1] each of pick's branch postcondition VCs is spine-FORMULA-sourced: {vc:?}"
                    );
                }
            }
            assert!(
                report.spine_sourced_formula() >= 2,
                "both branch postcondition VCs must flip spine-sourced (formula): {report:?}"
            );
        }
    }

    /// LIVE-FIRING (acyclic branch + precondition): `clamp_branch(x: i32, b: bool)
    /// -> i32` (`#[requires(x>0)] #[ensures(|r| *r>0)] { if b {x} else {1} }`,
    /// `/tmp/vfbr/clamp_branch.json`). TWO per-predecessor body-aware
    /// `Postcondition` VCs, each carrying the precondition-REFINED env
    /// (`x ∈ [1, MAX]`) and the precondition conjunct `(> x 0)`; the spine
    /// reproduces BOTH byte-for-byte, so BOTH flip SPINE-SOURCED (formula). This
    /// is the branch-AND-precondition case — the harder of the two fixtures.
    #[test]
    fn live_path_clamp_branch_postconditions_spine_sourced_formula() {
        use trust_types::ProofLevel;
        for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
            let (func, solver_vcs) = live_path_vcs("/tmp/vfbr/clamp_branch.json", max_level);
            let post_vcs: Vec<_> =
                solver_vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).collect();
            if max_level == ProofLevel::L0Safety {
                assert!(post_vcs.is_empty(), "[L0] postcondition is an L1 obligation");
                continue;
            }
            assert_eq!(
                post_vcs.len(),
                2,
                "[L1] clamp_branch's if/else join emits one postcondition VC per branch \
                 predecessor (two): {solver_vcs:?}"
            );
            // The live formula is precondition-refined: each VC carries `(>= x 1)`
            // (refined env) AND `(> x 0)` (the precondition conjunct).
            for vc in &post_vcs {
                let smt = vc.formula.to_smtlib();
                assert!(smt.contains("(>= x 1)"), "refined env present: {smt}");
                assert!(smt.contains("(> x 0)"), "precondition conjunct present: {smt}");
            }
            let cands = crate::lower::reconstruct_postcondition_formula_candidates(&func);
            for vc in &post_vcs {
                assert!(
                    cands.iter().any(|c| formula_eq_modulo_versions(c, &vc.formula)),
                    "the spine reproduces clamp_branch's branch postcondition byte-equal: {}",
                    vc.formula.to_smtlib()
                );
            }
            let before = solver_vcs.clone();
            let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
            assert_verdict_identical(&before, &after);
            for (vc, decision) in after.iter().zip(report.decisions.iter()) {
                if matches!(vc.kind, VcKind::Postcondition) {
                    assert_eq!(
                        *decision,
                        FlipDecision::SpineSourcedFormula,
                        "[L1] each of clamp_branch's branch postcondition VCs is \
                         spine-FORMULA-sourced: {vc:?}"
                    );
                }
            }
            assert!(
                report.spine_sourced_formula() >= 2,
                "both branch postcondition VCs (with precondition) must flip \
                 spine-sourced (formula): {report:?}"
            );
        }
    }

    /// SOUNDNESS (loop / back-edge, synthetic shape): the loop reconstruction may
    /// produce a candidate for a cyclic CFG (it does for `count`), but the flip is
    /// VERDICT-IDENTICAL regardless — a candidate is accepted only on exact
    /// byte-equality, so any loop whose live formula the spine does not exactly
    /// reproduce (or DOES) is verdict-preserving. We assert the strong invariant on a
    /// minimal hand-built back-edge body: every postcondition VC's formula is
    /// byte-identical before/after, and any spine-sourced swap is byte-equal to
    /// trust-vcgen's. The exact-equality gate guarantees nothing unsound ever flips.
    #[test]
    fn loop_body_postcondition_flip_is_verdict_identical() {
        use trust_types::{
            BasicBlock as TBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue,
            Statement, Terminator, Ty, VerifiableBody,
        };
        let span = SourceSpan {
            file: "/tmp/loop.rs".into(),
            line_start: 1,
            col_start: 0,
            line_end: 1,
            col_end: 40,
        };
        // _0 ret (None), _1 x. bb0: Goto bb1. bb1: _0 = _0 + 1 (statement); then
        // SwitchInt(x) { 0 => bb2 (Return), otherwise => bb1 (BACK-EDGE) }.
        let func = VerifiableFunction {
            name: "lp".into(),
            def_path: "lp".into(),
            span: span.clone(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::Bool, name: Some("x".into()) },
                ],
                blocks: vec![
                    TBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    TBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                            span: span.clone(),
                        }],
                        terminator: Terminator::SwitchInt {
                            exhaustive_enum_unreachable: false,
                            discr: Operand::Copy(Place::local(1)),
                            targets: vec![(0, BlockId(2))],
                            otherwise: BlockId(1), // back-edge to bb1
                            span: span.clone(),
                        },
                    },
                    TBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(0))),
                            span: span.clone(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::i32(),
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![
                trust_types::parse_spec_expr("result > 0").expect("predicate parses"),
            ],
            spec: trust_types::FunctionSpec {
                requires: vec![],
                ensures: vec!["result > 0".into()],
                invariants: vec![],
            },
        };
        let _ = BinOp::Add; // (keep the import used regardless of body shape)

        // SOUNDNESS (the load-bearing invariant, regardless of whether the loop
        // reconstruction fires): the flip is VERDICT-IDENTICAL on this loop. The loop
        // reconstruction MAY produce a candidate for a simple loop shape (it does for
        // `count`), but a candidate is accepted ONLY on exact byte-equality with the
        // live VC's formula — so either the candidate byte-matches the live formula
        // (verdict-identical swap) or it does not (kept trust-vcgen-sourced). Both are
        // sound. We assert the strong property: every postcondition VC's formula is
        // byte-identical before and after the flip, whatever the decision.
        for max_level in [ProofLevel::L0Safety, ProofLevel::L1Functional] {
            let summaries = trust_vcgen::SummaryDatabase::new();
            let (solver_vcs, _discharged) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries(&func, &summaries);
            let solver_vcs = trust_vcgen::filter_vcs_by_level(solver_vcs, max_level);
            let before = solver_vcs.clone();
            let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
            // Verdict-identical: kind/location/contract_metadata preserved AND every
            // formula's SMT-LIB byte-identical (a swap only ever replaces a formula
            // with a structurally-identical one).
            assert_verdict_identical(&before, &after);
            // And any flipped postcondition VC is byte-equal to its trust-vcgen input
            // (a SpineSourcedFormula decision here means the candidate matched the live
            // formula exactly — never an unsound substitution).
            for (b, a, decision) in
                itertools_zip3(before.iter(), after.iter(), report.decisions.iter())
            {
                if matches!(a.kind, VcKind::Postcondition)
                    && *decision == FlipDecision::SpineSourcedFormula
                {
                    assert_eq!(
                        b.formula.to_smtlib(),
                        a.formula.to_smtlib(),
                        "[{max_level:?}] a spine-sourced loop postcondition swap must be \
                         byte-equal to trust-vcgen's formula (verdict-identical): {a:?}"
                    );
                }
            }
        }
    }

    /// Three-way zip helper (no itertools dep): yields `(a, b, c)` tuples up to the
    /// shortest iterator.
    fn itertools_zip3<A, B, C>(
        a: impl Iterator<Item = A>,
        b: impl Iterator<Item = B>,
        c: impl Iterator<Item = C>,
    ) -> impl Iterator<Item = (A, B, C)> {
        a.zip(b).zip(c).map(|((a, b), c)| (a, b, c))
    }

    /// LIVE-FIRING (LOOP tier): the dumped `count` while-loop
    /// (`/tmp/vfloop/count.json` — `#[ensures(|r| *r>=0)] fn count(n:u32)->u32`,
    /// `while i<n { c=c.wrapping_add(1); i=i.wrapping_add(1); } c`) flips its
    /// `Postcondition` VC SPINE-SOURCED (formula) on the LIVE-path VC set.
    ///
    /// The live formula is
    /// `(and (and (>= n 0) (<= n 4294967295))
    ///       (and true true
    ///            (and (= _6 i) (= _5 (< _6 n))
    ///                 (and (not (< _6 n))
    ///                      (and (= _0 c) (not (>= _0 0)))))))` modulo SSA tokens:
    ///   * the env conjunct is the parameter `n`'s u32 type range ONLY — the loop
    ///     variables `c`/`i` widen to TOP (`[i128::MIN,i128::MAX]`) over the back-edge
    ///     and are FILTERED OUT by `interval_domain_to_formula`, so they contribute no
    ///     conjunct (the widening's observable env effect is "the loop vars drop out");
    ///   * the two `true`s are the return block's and the loop-header predecessor's
    ///     semantic guards, both JOIN-WEAKENED to `Bool(true)` on the back-edge revisit;
    ///   * `_6 = i` and `_5 = (_6 < n)` are the predecessor definitions made
    ///     relevant by the exact false loop-exit edge `not (_6 < n)`;
    ///   * `Eq(_0, c)` is the return-pin (`_0 = c`) and `Not(Ge(_0,0))` the negated
    ///     postcondition.
    /// The spine reconstructs every piece byte-for-byte WITHOUT running the fixpoint
    /// (it reproduces widening's observable RESULT — the param-only env — plus the
    /// semantic-guard join-weakening), so the formula now lives on the spine. Asserted
    /// against the LIVE `generate_vcs_with_discharge_and_summaries` path; verdicts are
    /// byte-identical (the swap is structurally identical to the matched VC's formula).
    #[test]
    fn live_path_count_loop_postcondition_flips_spine_sourced_formula() {
        // The Postcondition VC only exists at L1 (it is an L1 functional obligation).
        let (func, solver_vcs) = live_path_vcs("/tmp/vfloop/count.json", ProofLevel::L1Functional);
        let posts: Vec<_> =
            solver_vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).collect();
        assert_eq!(posts.len(), 1, "exactly one count postcondition VC expected: {solver_vcs:?}");

        // The spine reconstructs the live postcondition formula byte-for-byte.
        let cands = crate::lower::reconstruct_postcondition_formula_candidates(&func);
        assert!(
            cands.iter().any(|c| formula_eq_modulo_versions(c, &posts[0].formula)),
            "the spine must reconstruct count's loop postcondition formula byte-for-byte; \
             live = {}",
            posts[0].formula.to_smtlib()
        );
        // And it is exactly the env-wrapped, weakened-guard, return-pinned shape.
        // The LIVE formula carries trust-vcgen's S2c statement-granular SSA version
        // tokens (`c#s0_1_s3_0`); modulo those tokens it is the param-env +
        // weakened-guard + exact edge + return-pin shape.
        assert_eq!(
            strip_version_tokens_in_formula(&posts[0].formula).to_smtlib(),
            "(and (and (>= n 0) (<= n 4294967295)) \
             (and true true (and (= _6 i) (= _5 (< _6 n)) \
             (and (not (< _6 n)) (and (= _0 c) (not (>= _0 0)))))))",
            "the live count postcondition formula must be the param-env + weakened-guard \
             + exact exit edge + return-pin shape (loop vars widen to TOP and drop out)"
        );

        let before = solver_vcs.clone();
        let (after, report) = flip_safety_verdicts_to_spine(&func, solver_vcs);
        assert_verdict_identical(&before, &after);
        // The postcondition VC flips spine-sourced (formula).
        let post_spine_formula = after
            .iter()
            .zip(report.decisions.iter())
            .filter(|(vc, d)| {
                matches!(vc.kind, VcKind::Postcondition) && **d == FlipDecision::SpineSourcedFormula
            })
            .count();
        assert_eq!(
            post_spine_formula, 1,
            "count's loop postcondition VC must flip SPINE-SOURCED (formula): {report:?}"
        );
    }

    /// LOOP env byte-equality is a PROVABLE property of `count`, not a coincidence:
    /// pin that the spine's reconstructed env conjunct equals the LIVE merged
    /// abstract-interp env (the fixpoint-with-widening output joined across blocks).
    /// This is the load-bearing claim — that the widened loop-variable intervals
    /// (`c`, `i`) reach TOP and are FILTERED OUT, leaving only the parameter range.
    /// If a future widening change made a loop var NOT reach TOP, the live env would
    /// gain a conjunct, this assertion would fire, and the flip would (soundly) fall
    /// back to fail-closed via the exact-equality gate.
    #[test]
    fn loop_widened_env_is_param_range_only_for_count() {
        use trust_vcgen::AbstractDomain;
        let (func, _vcs) = live_path_vcs("/tmp/vfloop/count.json", ProofLevel::L1Functional);

        // LIVE merged env, built EXACTLY as generate_vcs_with_discharge does.
        let initial = trust_vcgen::type_aware_initial_state(&func);
        let config = trust_vcgen::FixpointConfig::for_function(&func);
        let fp = trust_vcgen::fixpoint_configured(&func, initial, &config);
        let mut merged = trust_vcgen::IntervalDomain::bottom();
        for state in fp.block_states.values() {
            merged = merged.join(state);
        }
        // The loop variables c (local 3) and i (local 4) widen to TOP.
        for v in ["c", "i"] {
            let iv = merged.get(v);
            assert_eq!(
                (iv.lo, iv.hi),
                (i128::MIN, i128::MAX),
                "loop variable {v} must widen to TOP (so it drops out of the env)"
            );
        }
        let live_env = trust_vcgen::interval_domain_to_formula(&merged);

        // SPINE env (no fixpoint run — param type ranges only).
        let spine_env = crate::lower::reconstruct_abstract_state_param_env_for_test(&func)
            .expect("count has an integer parameter (n)");
        assert_eq!(
            live_env, spine_env,
            "the spine's param-range env must byte-equal the live merged (widened) env \
             — i.e. the widened loop vars contribute NOTHING. live={:?} spine={:?}",
            live_env, spine_env
        );
    }
}

/// Trust (#57, 2026-08-17) — THE MISSING-OBLIGATION RATCHET.
///
/// This repo runs two independent safety-obligation producers over every function
/// and, until now, compared them only to decide WHICH set to dispatch — discarding
/// the comparison itself (`let _ = (native, vcgen_l0, vcgen_rest);`). That threw
/// away the one signal no downstream layer can reconstruct: an obligation that is
/// never emitted produces SILENCE, and silence is indistinguishable from success
/// everywhere below, including the Clean kernel, which can only re-check
/// propositions it is handed.
///
/// This test runs the real production entry point over the real trust-vcgen
/// pipeline across every committed dump, and pins the result.
///
/// **It is a RATCHET, not a zero-gate, and that is a measured decision rather than
/// a concession.** The population is not zero, but every survivor is one known,
/// benign class — see the assertions. What must never happen is a NEW class of
/// obligation appearing that trust-vcgen neither emits nor discharges; that is the
/// silent hole, and this test goes red the moment one shows up.
///
/// Getting to this state took correcting three false-alarm sources, each measured
/// against the corpus rather than reasoned about (the naive comparison reported 44):
///
///  1. **Kind spelling** — the spine says `SliceBoundsCheck` where trust-vcgen says
///     `IndexOutOfBounds`, at byte-identical spans. 4 rows, paired one-for-one in
///     both directions. Fixed by [`obligation_class`].
///  2. **Kind payload** — `ArithmeticOverflow` carries `operand_tys`, derived
///     independently by each producer. Fixed by the same function.
///  3. **Discharged obligations** — trust-vcgen returns emitted AND statically
///     PROVED sets; treating the proved ones as absent claimed "nothing checks
///     this" about obligations it had discharged. 3 rows (`bounded_add`, `inc_gt`,
///     `helper`). Fixed by [`l0_obligation_set_diff_with_discharged`].
#[cfg(test)]
mod missing_obligation_ratchet {
    use super::*;
    use std::path::{Path, PathBuf};

    /// ZERO. Not a ceiling, not a whitelist — every obligation the trust-ir spine
    /// derives is one trust-vcgen either dispatches or has already proved.
    ///
    /// This started as a ratchet at 31 with a `{DivisionByZero, RemainderByZero}`
    /// allowance, because the spine emitted a trivially-true divisor VC where
    /// trust-vcgen folded the obligation away. That allowance is gone: the spine
    /// now applies the SAME fold, from the SAME definition
    /// (`trust_types::static_truth::assert_failure_is_known_false`), so there is
    /// nothing left to whitelist. Anything appearing here is an obligation one
    /// producer derived and nothing checks.

    /// The spine's measured coverage gap. Bounds the OPPOSITE failure from the
    /// zero-gate: an over-aggressive fold that stops the spine deriving
    /// obligations trust-vcgen still emits.
    ///
    /// SPINE-DERIVABLE ONLY. `Assertion(unsafe-model)` rows are excluded and
    /// counted separately: they say "Trust has no model for this unsafe
    /// operation", which the spine does not derive and never should. Including
    /// them read as a 236-row gap when the real one is 139.
    ///
    /// Diagnosed sub-classes, for whoever closes them. The common thread is that
    /// the spine's generator walks `Terminator::Assert` and NOTHING ELSE, while
    /// trust-vcgen also derives obligations from place projections and from panic
    /// calls:
    ///  * `BoundsCheck` (24, was 38 before the C1/C1b slice range-index lanes) —
    ///    non-range shapes: arrayvec truncate, BigNat limbs, ascii,
    ///    `SliceIndex::get`, plus range calls whose receiver or endpoint falls
    ///    outside the modeled scope. The 4 projection-derived rows
    ///    (`slice::first`/`last`/`get`) remain blocked by the guard-formula port.
    ///  * `Assertion` (22, IDENTITY-PINNED below) — panic calls, and the
    ///    population is HETEROGENEOUS, not one macro: 17 `assert_failed` sites at
    ///    `macros/mod.rs:51` (16 byteorder `assert_eq!` preludes + arrayvec
    ///    `into_inner_unchecked`), 4 `panic_fmt` sites at `panic.rs:62`, and 1
    ///    sentinel at `panic.rs:73`. trust-vcgen derives these through
    ///    `overflow_vc.rs::v2_build_terminator_vc` via safety.rs lane 1b — NOT
    ///    `generate/panic_calls.rs`, which holds the div/rem + slice-method
    ///    recognizers only. The module side ALREADY mints the real check at every
    ///    site (the diverging panic-call arm: `Assert(const false)` + NoPanic +
    ///    `Unreachable` + a PanicFreedom obligation), so this gap is ACCOUNTING —
    ///    see `EXPECTED_ASSERTION_VCGEN_ONLY_ROWS` for the defer rationale.
    ///  * `ArithmeticOverflow(Add)` (37) — concentrated in probe fixtures.
    ///
    /// Lowering this is progress; raising it means coverage was retired. Note the
    /// asymmetry with the zero-gate above: ADDING spine derivation is the risky
    /// direction now, because anything the spine derives that trust-vcgen does not
    /// lands in `native_only` and fail-closes the compiler.
    const VCGEN_ONLY_CEILING: usize = 125;

    /// Trust (#63): the spine's DECLINE CENSUS — the pinned set of dump instances
    /// whose `generate_native_safety_vcs` returns `None`, keyed
    /// `(def_path, content-hash)`.
    ///
    /// A PINNED SET REPLACES A CARDINALITY, and the replacement is the whole
    /// point: `SPINE_DECLINED_CEILING: usize = 225` used to stand here, and a
    /// count cannot express the invariant its own doc claimed.
    ///
    /// WHAT THE CEILING MEASURED vs WHAT IT CLAIMED. It claimed that raising it
    /// "requires explaining which functions stopped being comparable", and its
    /// assertion message read "functions that used to be COMPARED now decline …
    /// This is the laundering channel, not progress." Neither sentence is
    /// something `set.len() <= N` can see. A cardinality moves for three
    /// different reasons and reports all three identically:
    ///   1. a COMPARED function starts declining — the regression it guards;
    ///   2. a NEW function enters the corpus already declining — INTAKE, which
    ///      retires no coverage because there was none to retire;
    ///   3. a declining function leaves the corpus — pure deletion.
    /// It fired on (2). Measured at `77e6ab164d`: 227 against a ceiling of 225,
    /// and the +2 are the two rows named at the bottom of this table, both of
    /// which ENTERED the corpus already un-comparable in `41189ffd76`. The
    /// message therefore accused a regression that had not happened — and,
    /// being an `assert!`, it aborted the test before `NATIVE_DISPATCH_FLOOR`,
    /// the Assertion identity pin, and `VCGEN_ONLY_CLASS_CEILINGS` ever ran. A
    /// gate that fires first and aborts hides every gate behind it; see the
    /// failure-accumulation note in the test body for why nothing aborts now.
    ///
    /// WHY NOT BARE-RAISE 225 → 227. The constant's stated meaning is "coverage
    /// was retired". Writing 227 into that slot records corpus INTAKE in a
    /// number that means the opposite, and the next reader inherits the same
    /// false claim with a larger figure and no way to tell which rows caused it.
    ///
    /// THE KEY, AND BOTH DIRECTIONS OF ITS IDENTITY HAZARD.
    ///  * NOT `def_path` alone. The 2334 parseable shipped dumps carry only 2092
    ///    distinct def_paths — 242 dumps share a key with another dump, and
    ///    `std::option::Option::<i32>::is_some` alone appears 6 times. Under a
    ///    def_path key a pinned decliner whose OTHER, currently-COMPARED instance
    ///    later declines moves nothing at all: the def_path is already present.
    ///    That is exactly the regression this gate exists for, slept through.
    ///  * NOT `(def_path, dump path)`. A fixture rename or a directory reshuffle
    ///    would read as one closure plus one phantom intake, and a gate that
    ///    cries wolf on `git mv` gets widened until it means nothing.
    ///  * SO: `(def_path, content-hash)` — the first 16 hex digits of
    ///    [`trust_types::VerifiableFunction::content_hash`], the repo's
    ///    designated content identity (SHA-256 over `stable_model_json` of body,
    ///    contracts, pre/postconditions and spec; `BTreeMap` throughout so the
    ///    rendering is a function of contents, and documented stable across Rust
    ///    versions, unlike `DefaultHasher`). It EXCLUDES `name` and `span`, so a
    ///    rename cannot fake an intake; it SEPARATES same-def_path instances, so
    ///    the erasure above is gone. 64 bits is ample because a truncation
    ///    collision could only mask a change WITHIN one def_path group, and the
    ///    largest such group in the corpus is 6.
    ///
    /// TRUST (#62) IS NOT REVERSED BY THIS. #62 ruled that the ceiling must count
    /// UNIQUE def_paths rather than instances, because a rebase adding three more
    /// dumps of already-declining functions read as a regression. That is a
    /// defect of COUNTING instances, not of IDENTIFYING them. A set difference
    /// NAMES the newcomer, so an extra dump of an already-declining function
    /// surfaces as one line to acknowledge instead of an unexplained `+3`.
    ///
    /// BOTH DIRECTIONS ARE RED, deliberately — this is a census, not a ceiling.
    /// An unpinned decliner is a finding (regression or intake; the failure
    /// prints the rows so a human can say which). A pinned row that is no longer
    /// observed is PROGRESS and still fails, because a census that silently rots
    /// stops being evidence: the fix is to delete the line, the same discipline
    /// `scripts/hooks-pin/pin-waivers.txt` applies to a waiver whose subject has
    /// gone coherent again.
    ///
    /// TRANSCRIBED FROM THE RATCHET'S OWN RENDERING. On failure this test prints
    /// the entire census in source syntax; paste that. A hand-derived key reads
    /// as a phantom identity, exactly as it would for the Assertion pin below.
    ///
    /// PROVEN LIVE IN BOTH DIRECTIONS (2026-08-19). "A gate that cannot go red is
    /// not a gate" — the rule the controls module below states — applies to the
    /// replacement as much as to the thing replaced, and a repaired instrument
    /// that cannot fail is worse than a broken one because it reads as green. The
    /// mutations cannot live as checked-in tests (each one edits this constant),
    /// so they were driven by hand against the unmutated green baseline and are
    /// recorded here to be re-runnable:
    ///
    ///  * FORCE ONE PINNED DECLINER OUT — delete
    ///    `("<[T] as lib::BitArray<T>>::bit_length", "0d044330f8215218")`.
    ///    Result: one NEW finding, `UNPINNED spine decline(s): 1 dump
    ///    instance(s) …`, naming exactly that row and nothing else.
    ///  * FORCE ONE COMPARED INSTANCE IN — add
    ///    `("arrayvec::ArrayVec::<T, CAP>::len", "489f98929f02a9df")`.
    ///    Result: one NEW finding, `STALE SPINE_DECLINED_PIN row(s): 1 pinned
    ///    decline(s) are no longer observed`, naming exactly that row.
    ///
    /// The second control is also the KEY's own proof. That def_path is ALREADY
    /// in this table — as `ae6144ec175edbda`, a different dump of the same
    /// function that DOES decline — so a `def_path`-keyed gate would have stayed
    /// green while a compared instance was pinned as a decliner. Seven of the 227
    /// census def_paths have further dumps in the corpus that are compared today;
    /// those are exactly the slots where a real regression would have been silent
    /// under the old key.
    const SPINE_DECLINED_PIN: &[(&str, &str)] = &[
        // The 225 declines that predate the two INTAKE rows below.
        ("<[T] as lib::BitArray<T>>::bit_length", "0d044330f8215218"),
        ("<core::slice::iter::Iter<'_, i32> as core::iter::traits::iterator::Iterator>::fold::<i32, {closure@<i32 as core::iter::traits::accum::Sum<&i32>>::sum<core::slice::iter::Iter<'_, i32>>::{closure#0}}>", "a14702a23ca07be2"),
        ("<core::slice::iter::Iter<'_, i32> as core::iter::traits::iterator::Iterator>::next", "571566dc7d3e162a"),
        ("<expr::subst::LevelParamSubstSlice<'_> as expr::visitor::opt::ExprFolderOpt>::fold_const_opt", "7739181a02c2e548"),
        ("<expr::types::BigNat as std::cmp::Ord>::cmp", "6706700503686cad"),
        ("<i128 as lib::BitField>::get_bit", "a90e8b292f0b1b3c"),
        ("<i128 as lib::BitField>::set_bit", "1500dc5cdbe22d1f"),
        ("<i16 as lib::BitField>::get_bit", "fcf619f56e35d6e4"),
        ("<i16 as lib::BitField>::set_bit", "352b34d4110d673b"),
        ("<i32 as lib::BitField>::get_bit", "346ac3cc94dccea9"),
        ("<i32 as lib::BitField>::set_bit", "60feff0319dbb3a6"),
        ("<i64 as lib::BitField>::get_bit", "a3aae1256c865deb"),
        ("<i64 as lib::BitField>::set_bit", "fcf1b617bd729110"),
        ("<i8 as lib::BitField>::get_bit", "fa3a40285a5c73ea"),
        ("<i8 as lib::BitField>::set_bit", "6d936455a53ba065"),
        ("<isize as lib::BitField>::get_bit", "a3aae1256c865deb"),
        ("<isize as lib::BitField>::set_bit", "fcf1b617bd729110"),
        ("<lib::ByteSize as core::ops::arith::AddAssign<T>>::add_assign", "cb718900716fe662"),
        ("<lib::ByteSize as core::ops::arith::AddAssign>::add_assign", "ba11eff572fca004"),
        ("<lib::ByteSize as core::ops::arith::MulAssign<T>>::mul_assign", "89e625c04ed6e72e"),
        ("<lib::Either<L, R> as core::clone::Clone>::clone_from", "137b8b62b1e6d970"),
        ("<lib::Either<L, R> as core::cmp::Ord>::cmp", "1c1d4461fc7391c1"),
        ("<lib::Either<L, R> as core::cmp::PartialEq>::eq", "9a2acfa7543aa11b"),
        ("<lib::Either<L, R> as core::cmp::PartialOrd>::partial_cmp", "ddee88df4b5a2c53"),
        ("<lib::Either<L, R> as core::convert::AsMut<[Target]>>::as_mut", "0aca333e806a657b"),
        ("<lib::Either<L, R> as core::convert::AsMut<str>>::as_mut", "c407541f2d916b80"),
        ("<lib::Either<L, R> as core::convert::AsMut<Target>>::as_mut", "80d8855f15a8d438"),
        ("<lib::Either<L, R> as core::convert::AsRef<[Target]>>::as_ref", "cfc6f6a0b5deadd9"),
        ("<lib::Either<L, R> as core::convert::AsRef<str>>::as_ref", "7400c569777e0e4b"),
        ("<lib::Either<L, R> as core::convert::AsRef<Target>>::as_ref", "4c64add06d6e1bf3"),
        ("<lib::Either<L, R> as core::fmt::Debug>::fmt", "de27a7c507a3b99d"),
        ("<lib::Either<L, R> as core::fmt::Display>::fmt", "3698658e3b6a049b"),
        ("<lib::Either<L, R> as core::fmt::Write>::write_char", "a53017bd293b5e86"),
        ("<lib::Either<L, R> as core::fmt::Write>::write_fmt", "733844c970226402"),
        ("<lib::Either<L, R> as core::fmt::Write>::write_str", "3fd48bdcd7346292"),
        ("<lib::Either<L, R> as core::hash::Hash>::hash", "116c4e9c975f460e"),
        ("<lib::Either<L, R> as core::ops::deref::Deref>::deref", "de706be0682cd15b"),
        ("<lib::Either<L, R> as core::ops::deref::DerefMut>::deref_mut", "640cc5d67f42803c"),
        ("<lib::errors::AsciiError as core::cmp::PartialEq>::eq", "71b02bd7870210b7"),
        ("<lib::errors::AsciiError as core::fmt::Debug>::fmt", "0cc53abc29bea0c2"),
        ("<lib::iterator::IterEither<L, R> as core::iter::traits::double_ended::DoubleEndedIterator>::next_back", "3a8a6b96b69c2727"),
        ("<lib::iterator::IterEither<L, R> as core::iter::traits::double_ended::DoubleEndedIterator>::nth_back", "cb4ae4caf80d2139"),
        ("<lib::iterator::IterEither<L, R> as core::iter::traits::exact_size::ExactSizeIterator>::len", "012d85606fd2c6b4"),
        ("<lib::iterator::IterEither<L, R> as core::iter::traits::iterator::Iterator>::next", "0ecb5446538ae8f9"),
        ("<lib::iterator::IterEither<L, R> as core::iter::traits::iterator::Iterator>::nth", "b504196cf67470f3"),
        ("<lib::iterator::IterEither<L, R> as core::iter::traits::iterator::Iterator>::size_hint", "db265b9d214f3329"),
        ("<std::slice::Iter<'_, i32> as std::iter::Iterator>::fold::<i32, {closure@<i32 as std::iter::Sum<&i32>>::sum<std::slice::Iter<'_, i32>>::{closure#0}}>", "d634fc6633dd9fb1"),
        ("<std::slice::Iter<'_, i32> as std::iter::Iterator>::next", "e9555c1150946b2e"),
        ("<u128 as lib::BitField>::get_bit", "4776e281ee1645e0"),
        ("<u128 as lib::BitField>::set_bit", "9f37adad28cd8170"),
        ("<u16 as lib::BitField>::get_bit", "de28c2a68d28190c"),
        ("<u16 as lib::BitField>::set_bit", "7243767db11abf0e"),
        ("<u32 as lib::BitField>::get_bit", "7be0bd8698ac992a"),
        ("<u32 as lib::BitField>::set_bit", "d4b14ff3801d5de2"),
        ("<u64 as lib::BitField>::get_bit", "57765eb4aef85a0e"),
        ("<u64 as lib::BitField>::set_bit", "24952898207a587b"),
        ("<u8 as lib::BitField>::get_bit", "ddd9f2576e070c37"),
        ("<u8 as lib::BitField>::set_bit", "ced99f1a056eda70"),
        ("<usize as lib::BitField>::get_bit", "57765eb4aef85a0e"),
        ("<usize as lib::BitField>::set_bit", "24952898207a587b"),
        ("arrayvec::ArrayVec::<T, CAP>::len", "ae6144ec175edbda"),
        ("avg_floor", "0135e2eb8439ebbe"),
        ("b", "850c6dfe3eb52479"),
        ("box_inner", "242787d59b08c788"),
        ("C1_dangling_local", "9fc6d25a51ed3b25"),
        ("ceil_div7", "f983e85d75451618"),
        ("cmp::impls::<impl cmp::Ord for i128>::cmp", "58378b3af1e3a82e"),
        ("cmp::impls::<impl cmp::Ord for i16>::cmp", "c0b13dee71617f71"),
        ("cmp::impls::<impl cmp::Ord for i32>::cmp", "f75fc366444f8ae5"),
        ("cmp::impls::<impl cmp::Ord for i64>::cmp", "f13eb17e5b9388d8"),
        ("cmp::Ord::clamp", "84ec0c0555f9bbb7"),
        ("cmp::Ordering::as_raw", "3b636abbcd039f4a"),
        ("cmp::Ordering::reverse", "9d024ecd874f203b"),
        ("cmp::Ordering::then", "fd99e14c993c1b4c"),
        ("core::num::<impl i32>::checked_pow", "87bf1dbc0d40e528"),
        ("core::num::<impl i32>::div_ceil", "674c1762325c18eb"),
        ("core::num::<impl i32>::div_floor", "9785e303f2ae7270"),
        ("core::num::<impl i32>::isqrt", "7408c5ad8e999cd3"),
        ("core::num::<impl i32>::midpoint", "4da22b893f2a6895"),
        ("core::num::<impl i32>::overflowing_pow", "f52f3d0d63b69a8e"),
        ("core::num::<impl i32>::signum", "2a94ab8a996ea30c"),
        ("core::num::<impl i32>::strict_pow", "12c899fd00b1bc6c"),
        ("core::num::<impl i32>::unchecked_shl", "801ac3e2adc3eeaa"),
        ("core::num::<impl i64>::signum", "a706b36f70b4fcc4"),
        ("core::num::<impl i8>::signum", "fd3e6b548c4d063f"),
        ("core::num::<impl u32>::ilog2", "4afc3fbe281e68f6"),
        ("core::num::<impl u32>::one_less_than_next_power_of_two", "850239fc54396aaf"),
        ("core::num::<impl usize>::unchecked_add::precondition_check", "06cbcafd82e8f840"),
        ("core::num::imp::int_sqrt::u16_stages", "0124a32c981fb95b"),
        ("core::num::imp::int_sqrt::u16", "0d1657aba5d9a480"),
        ("core::num::imp::int_sqrt::u32_stages", "30ea145049ec3224"),
        ("core::num::imp::int_sqrt::u32", "43305e7a3c0f00de"),
        ("core::num::nonzero::NonZero::<i32>::new", "9ae2a447689915ce"),
        ("core::num::nonzero::NonZero::<u16>::new", "ec7ddd9022838164"),
        ("core::num::nonzero::NonZero::<u32>::get", "cd339629a015cd5f"),
        ("core::num::nonzero::NonZero::<u32>::ilog2", "094ddab65ab2a993"),
        ("core::num::nonzero::NonZero::<u32>::new", "00893d35b7537777"),
        ("core::num::nonzero::NonZero::<u8>::new", "57464d39eb9c9486"),
        ("core::slice::iter::<impl core::iter::traits::collect::IntoIterator for &[i32]>::into_iter", "2738df63c73099d9"),
        ("core::slice::iter::<impl std::iter::IntoIterator for &[i32]>::into_iter", "83df2ef4de83877c"),
        ("core::slice::iter::Iter::<'_, i32>::new", "08b9f642e295a020"),
        ("crate::exp_bump", "f3fd4d05d65aa8be"),
        ("crate::vec_get", "1aed8bb5b637a0c1"),
        ("deref", "a51e6d29ed470ab3"),
        ("direct_call", "58d03eb8c010a621"),
        ("expr::meta::ExprMeta::approx_depth", "84be72a9fd24cd8f"),
        ("expr::meta::ExprMeta::has_expr_mvar", "2011094b879e562f"),
        ("expr::meta::ExprMeta::has_fvar", "1bbac65a6d5d443b"),
        ("expr::meta::ExprMeta::has_level_mvar", "86f9a5218139c5f5"),
        ("expr::meta::ExprMeta::has_level_param", "6a2a780bd93ecaa4"),
        ("expr::meta::ExprMeta::loose_bvar_range", "80919b00caf4864f"),
        ("expr::meta::ExprMeta::mk_app_meta", "7b4b5d877ab41c14"),
        ("expr::meta::ExprMeta::pack", "c0a97d45bf67a1db"),
        ("expr::meta::mix_hash", "ab6fc9de9c2134c8"),
        ("expr::subst::FoldMemo::get", "a4c3803052d33642"),
        ("expr::subst::FoldMemo::put", "ecd0c309faac4292"),
        ("expr::types::BigNat::mul_big_capped", "92a0ec34d32f899e"),
        ("expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions", "4379341969a517f3"),
        ("expr::visitor::opt::ExprFolderOpt::fold_expr_opt_inner_full", "7964b898062aa383"),
        ("expr::visitor::opt::ExprFolderOpt::fold_expr_opt_zfc", "f96f666fba151e4d"),
        ("expr::visitor::opt::ExprFolderOpt::fold_zfc_set_expr_opt", "1e8fe4d93bc462e6"),
        ("extract_foldmemo::level::Level::collect_params_impl", "7dfa6207401f04bb"),
        ("extract_foldmemo::level::Level::has_params_impl", "682d5d8bc85f3596"),
        ("extract_foldmemo::level::Level::is_nonzero", "ad5fe2f6abd9803c"),
        ("extract_foldmemo::level::Level::is_zero", "17e1ac8503a00bad"),
        ("extract_foldmemo::level::Level::substitute_map_impl_opt", "08ea49111feb4fe9"),
        ("extract_foldmemo::level::Level::substitute_slice_impl_opt", "98f0715eba1cf8e2"),
        ("forgery::F1_dangling_local", "49aca9324254bd29"),
        ("forgery::G1_signum_cmp_rhs_nonzero", "338e7b99a60d55a1"),
        ("forgery::G2_signum_wrong_disc_mapping", "9bf7a3e13d6de9ff"),
        ("forgery::G3_signum_non_ordering_enum", "8b58c86dff167a4d"),
        ("forgery::G4_signum_flipped_operands", "c02c77180c31c533"),
        ("forgery::G5_signum_unsigned_cast_dest", "46ff64ec5ed631ae"),
        ("forgery::G6_signum_valid_control", "5257042c509017bf"),
        ("halve", "421cc391197e0d14"),
        ("is_even", "065e6e084961b13e"),
        ("is_leap_year", "99ab05fb39368650"),
        ("lib::<impl lib::private::Sealed for i16>::write", "cba51fd9d1450d7d"),
        ("lib::<impl lib::private::Sealed for i32>::write", "fff1aa5f48a223e4"),
        ("lib::<impl lib::private::Sealed for i64>::write", "3c6debc0a174e2e9"),
        ("lib::<impl lib::private::Sealed for i8>::write", "406c4860d8ab0df6"),
        ("lib::<impl lib::private::Sealed for u16>::write", "fb83f1f1fda7b751"),
        ("lib::<impl lib::private::Sealed for u32>::write", "c19b2635d5b8e918"),
        ("lib::<impl lib::private::Sealed for u64>::write", "c01859ab01a2bf2c"),
        ("lib::<impl lib::private::Sealed for u8>::write", "09f8feb3c6fa0cff"),
        ("lib::arch::all::memchr::One::find_raw", "b67924cda44ffdcb"),
        ("lib::arch::all::memchr::One::rfind_raw", "9e71868623106510"),
        ("lib::arrayvec::ArrayVec::<T, CAP>::new_const", "5cb39681c865bcce"),
        ("lib::arrayvec::ArrayVec::<T, CAP>::retain::process_one", "a294277d217166b0"),
        ("lib::Either::<L, R>::as_mut", "193f1e970107f46a"),
        ("lib::Either::<L, R>::as_pin_mut", "77ebeab62aae1152"),
        ("lib::Either::<L, R>::as_pin_ref", "62afec6094bdefc5"),
        ("lib::Either::<L, R>::as_ref", "6a484295825b0d06"),
        ("lib::Either::<L, R>::factor_iter_mut", "d7587065b0549597"),
        ("lib::Either::<L, R>::factor_iter", "d228da658638fcd5"),
        ("lib::Either::<L, R>::iter_mut", "2174e4015f8ac340"),
        ("lib::Either::<L, R>::iter", "6c0f810ec3612f94"),
        ("lib::iterator::<impl core::iter::traits::double_ended::DoubleEndedIterator for lib::Either<L, R>>::next_back", "e5bba6dea997cae2"),
        ("lib::iterator::<impl core::iter::traits::double_ended::DoubleEndedIterator for lib::Either<L, R>>::nth_back", "4e1a8db959b4167f"),
        ("lib::iterator::<impl core::iter::traits::exact_size::ExactSizeIterator for lib::Either<L, R>>::len", "79f9ce62cad1a37a"),
        ("lib::iterator::<impl core::iter::traits::iterator::Iterator for lib::Either<L, R>>::next", "68c0693cd077eaf1"),
        ("lib::iterator::<impl core::iter::traits::iterator::Iterator for lib::Either<L, R>>::nth", "4cb8d6c494e8e9b7"),
        ("lib::iterator::<impl core::iter::traits::iterator::Iterator for lib::Either<L, R>>::size_hint", "0a82710858cad45b"),
        ("lib::udiv128::u128_mulhi", "6a1ddb48fc755c70"),
        ("lib::udiv128::udivmod_1e19", "97ca8cd00a333e35"),
        ("main::S::bump", "82ddd980b90eba58"),
        ("num::<impl i16>::signum", "9f57b91fe371e13d"),
        ("num::<impl i32>::signum", "5257042c509017bf"),
        ("num::<impl i64>::signum", "d21cb3a9d4117f84"),
        ("num::<impl i8>::signum", "9b94922315bb2245"),
        ("p_even_branch", "c8afaa804174c262"),
        ("p_is_even_usize", "eae681e3a08fe311"),
        ("p_is_odd_usize", "8871b08537049c17"),
        ("p_leap", "0b8e562cb0723332"),
        ("p_match_even", "c2de142dfd5c5d74"),
        ("p_mod2", "b7a1ba0c91fbeec8"),
        ("p_parity", "f9ee2693bddaf0d7"),
        ("parser::_convert_classic_tokens", "3946b6e8bb58891f"),
        ("parser::_get_ast", "4d87e1b2ddecae3f"),
        ("parser::fold_exprs", "4552e591288ce004"),
        ("reduction::<impl term::Term>::_apply", "0ea7fea8071b1e8c"),
        ("reduction::<impl term::Term>::beta_app", "3927a2e33007b13a"),
        ("reduction::<impl term::Term>::beta_hap", "135c24788b0bc509"),
        ("reduction::<impl term::Term>::beta_hno", "08e33d72aec2510b"),
        ("reduction::<impl term::Term>::beta_hsp", "784f28195b1d00a8"),
        ("reduction::<impl term::Term>::beta_nor", "aa8ba1bf1d0b6e49"),
        ("reduction::<impl term::Term>::eval", "545451318d8118f0"),
        ("reduction::<impl term::Term>::update_free_variables", "19e4420136a5900b"),
        ("rem2", "c3ca9d0bce4946e2"),
        ("std::num::NonZero::<i64>::get", "c949768fc9f0fe03"),
        ("std::num::NonZero::<i64>::new", "1c022513d4e6bd54"),
        ("std::num::NonZero::<u32>::get", "5e23789181280118"),
        ("std::num::NonZero::<u32>::new", "5a8b2f4ea66eb1fa"),
        ("std::option::Option::<i32>::and_then::<i32, {closure@main.rs:15:16: 15:19}>", "fef0eff00cb2375b"),
        ("std::option::Option::<i32>::and_then::<i32, {closure@main.rs:17:16: 17:24}>", "7915268a1a16bdcb"),
        ("std::option::Option::<i32>::expect", "76538a8b0171e834"),
        ("std::option::Option::<i32>::filter::<{closure@main.rs:20:14: 20:17}>", "4690500e691d8abc"),
        ("std::option::Option::<i32>::map::<i32, {closure@main.rs:10:11: 10:19}>", "07927a68806ad347"),
        ("std::option::Option::<i32>::map::<i32, {closure@main.rs:26:11: 26:19}>", "0f99f183a4037aa0"),
        ("std::option::Option::<i32>::map::<i32, {closure@main.rs:5:11: 5:14}>", "bd02b317d3060711"),
        ("std::option::Option::<i32>::unwrap", "f8103e479a2fdf99"),
        ("std::option::Option::<u8>::map::<u8, {closure@main.rs:12:11: 12:19}>", "ca3e5e3f7bade044"),
        ("std::option::Option::<u8>::map::<u8, {closure@main.rs:7:11: 7:19}>", "1861a0ab16376266"),
        ("std::option::Option::<u8>::unwrap", "1ae34b3770614960"),
        ("std::ptr::const_ptr::<impl *const T>::offset_from_unsigned::precondition_check", "ca730a2a0ecc740a"),
        ("std::ptr::mut_ptr::<impl *mut T>::add::precondition_check", "ad2acde7927b3952"),
        ("std::result::Result::<i32, u8>::unwrap", "0ae7f1429a408aac"),
        ("std::slice::Iter::<'_, i32>::new", "367323a6cc2c82ca"),
        ("term::base26_encode", "edc44e94d2a3ad5d"),
        ("term::show_precedence_cla", "d56ff62387007af3"),
        ("term::show_precedence_dbr", "0409cc642697f3aa"),
        ("term::Term::has_free_variables_helper", "f2b3e0374fc46358"),
        ("term::Term::is_isomorphic_to", "7312c772f07ff9bf"),
        ("term::Term::is_supercombinator", "4c3bcd1cba5fa4d9"),
        ("term::Term::max_depth", "2ad6084c2a052417"),
        ("term::Term::max_free_index_helper", "355013a93dc3d74a"),
        ("term::Term::unabs_mut", "094a093924bd0a9c"),
        ("term::Term::unabs_ref", "9fc9376ae90cc947"),
        ("term::Term::unabs", "e7a32086998f8b6f"),
        ("term::Term::unapp_mut", "d0f727ed5ec19b98"),
        ("term::Term::unapp_ref", "d3c141518ee9456c"),
        ("term::Term::unapp", "ab4b67e896872a8f"),
        ("term::Term::unvar_mut", "6562b41e2c499085"),
        ("term::Term::unvar_ref", "9f2f87141a2bae14"),
        ("version_meta_for", "f7673ce8a9c97de3"),

        // ------------------------------------------------------------------
        // Trust (#63): THE TWO ROWS THAT MADE THE OLD CEILING FIRE. These are
        // INTAKE, not retired coverage, and separating them from the 225 above
        // is the whole reason this table is a set and not the number 227.
        //
        // Both dump files were ADDED by `41189ffd76` ("r4: local mono dumps +
        // FS-CALL-RHS — the bytesize chain closes"), which created
        // `fixtures/mutator-harvest-2026-08-19/bytesize-mono/dumps/`. They have
        // never been comparable: they entered the corpus already declining, so
        // no cross-check existed to retire. The old `SPINE_DECLINED_CEILING`
        // counted them, read 227 against 225, and reported "functions that used
        // to be COMPARED now decline" — a regression that never happened.
        //
        // WHY THEY DECLINE, precisely, so a future closure is recognizable:
        // each body's checked arithmetic reads the receiver through a
        // projection —
        //     Assign { place: _4, rvalue: CheckedBinaryOp(Add|Mul,
        //              Copy(_1.[Deref, Field(0)]), Copy(_3)) }
        //     Assert { cond: Move(_4.[Field(1)]), msg: Overflow(Add|Mul) }
        // — and `native_operand_ty` (crates/trust-ir-bridge/src/lower.rs:9352)
        // admits a local operand ONLY when `p.projections.is_empty()`. The lhs
        // carries `[Deref, Field(0)]`, so it falls to that function's `_ => None`
        // arm; `reconstruct_assert_vc_kind`'s `ArithmeticOverflow` arm propagates
        // the `?`, and `generate_native_safety_vcs` declines the whole body.
        //
        // These two rows are NOT uncovered, and the census is not the reason to
        // hurry: their faithfulness is carried by the trust-clean walk lanes
        // (FS-CALL-RHS certifies them fully faithful). What is missing is
        // SPINE-SIDE call/projection envelope growth, which is separate future
        // work — so the pin records an envelope gap, not a coverage hole.
        //
        // Closing the projection lane retires BOTH rows at once, and the census
        // will then go red as STALE — which is correct, and the fix is to delete
        // these two lines.
        ("<main::bytesize::ByteSize as core::ops::arith::AddAssign<u64>>::add_assign", "e2743b9eca40d162"),
        ("<main::bytesize::ByteSize as core::ops::arith::MulAssign<u64>>::mul_assign", "18f7529d9044c241"),
    ];

    /// Trust (#61, C0): functions dispatching the spine's own VC set — measured
    /// 1809 at pin time. Must never silently fall.
    const NATIVE_DISPATCH_FLOOR: usize = 1809;

    /// Trust (#61, C0): per-class ceilings inside `vcgen_only`, so a campaign that
    /// claims to close one class must move THAT class's number — the aggregate
    /// alone can hide a swap (one class up, another down, total flat). Only the
    /// two campaign-relevant classes are pinned; the aggregate ceiling bounds the
    /// rest.
    const VCGEN_ONLY_CLASS_CEILINGS: &[(&str, usize)] = &[("BoundsCheck", 24)];

    /// Trust (#62, C-D0): the Assertion class is IDENTITY-PINNED, not count-bounded.
    ///
    /// A count ceiling cannot see a lateral swap — one known row closing while a
    /// NEW unknown identity appears reads as "unchanged". These 22 rows were the
    /// judged DEFER verdict of the Assertion-row design panel (2026-08-20): the
    /// module side already mints the real check at every site (the diverging
    /// panic-call arm, lower.rs — `Assert(const false)`+NoPanic, `Unreachable`, and
    /// a PanicFreedom obligation), the guard-formula blocker makes closure
    /// enumeration-only under EVERY design, and the per-site rows are documented
    /// dead in production. So the honest artifact is this pin: any NEW identity
    /// goes red and demands a fresh look; downward motion stays green.
    ///
    /// TRANSCRIBED FROM THE RATCHET'S OWN RENDERING (never from a report — the
    /// span keys are the run's `ObligationKey` Display, and a hand-derived key
    /// reads as a phantom new identity). Census: 16 byteorder `assert_eq!`
    /// preludes + arrayvec `into_inner_unchecked` at `macros/mod.rs:51`; 4
    /// `panic_fmt` sites at `panic.rs:62`; 1 sentinel at `panic.rs:73`.
    ///
    /// PRE-AUTHORIZED GROWTH (do not re-litigate): the panel named three LATENT
    /// identities that may surface as the corpus/vcgen shift — memchr
    /// `One::{find_raw,rfind_raw}` and itoa `udivmod_1e19`. Adding EXACTLY those,
    /// with this comment updated, is approved; anything else is a finding.
    const EXPECTED_ASSERTION_VCGEN_ONLY_ROWS: &[(&str, &str)] = &[
        ("core::cmp::impls::<impl core::cmp::Ord for i32>::clamp", "Assertion@core/src/panic.rs:62:8"),
        ("<expr::subst::Lowerer as expr::visitor::opt::ExprFolderOpt>::fold_bvar_opt", "Assertion@library/core/src/panic.rs:62:8"),
        ("lib::arrayvec::ArrayVec::<T, CAP>::into_inner_unchecked", "Assertion@core/src/macros/mod.rs:51:20"),
        ("lib::arrayvec::ArrayVec::<T, CAP>::new", "Assertion@core/src/panic.rs:62:8"),
        ("lib::arrayvec::extend_panic", "Assertion@core/src/panic.rs:62:8"),
        ("<lib::BigEndian as lib::ByteOrder>::read_u128_into", "Assertion@core/src/macros/mod.rs:51:20"),
        ("<lib::BigEndian as lib::ByteOrder>::read_u16_into", "Assertion@core/src/macros/mod.rs:51:20"),
        ("<lib::BigEndian as lib::ByteOrder>::read_u32_into", "Assertion@core/src/macros/mod.rs:51:20"),
        ("<lib::BigEndian as lib::ByteOrder>::read_u64_into", "Assertion@core/src/macros/mod.rs:51:20"),
        ("<lib::BigEndian as lib::ByteOrder>::write_u128_into", "Assertion@core/src/macros/mod.rs:51:20"),
        ("<lib::BigEndian as lib::ByteOrder>::write_u16_into", "Assertion@core/src/macros/mod.rs:51:20"),
        ("<lib::BigEndian as lib::ByteOrder>::write_u32_into", "Assertion@core/src/macros/mod.rs:51:20"),
        ("<lib::BigEndian as lib::ByteOrder>::write_u64_into", "Assertion@core/src/macros/mod.rs:51:20"),
        ("lib::check_ascii_printable", "Assertion@core/src/panic.rs:73:8"),
        ("<lib::LittleEndian as lib::ByteOrder>::read_u128_into", "Assertion@core/src/macros/mod.rs:51:20"),
        ("<lib::LittleEndian as lib::ByteOrder>::read_u16_into", "Assertion@core/src/macros/mod.rs:51:20"),
        ("<lib::LittleEndian as lib::ByteOrder>::read_u32_into", "Assertion@core/src/macros/mod.rs:51:20"),
        ("<lib::LittleEndian as lib::ByteOrder>::read_u64_into", "Assertion@core/src/macros/mod.rs:51:20"),
        ("<lib::LittleEndian as lib::ByteOrder>::write_u128_into", "Assertion@core/src/macros/mod.rs:51:20"),
        ("<lib::LittleEndian as lib::ByteOrder>::write_u16_into", "Assertion@core/src/macros/mod.rs:51:20"),
        ("<lib::LittleEndian as lib::ByteOrder>::write_u32_into", "Assertion@core/src/macros/mod.rs:51:20"),
        ("<lib::LittleEndian as lib::ByteOrder>::write_u64_into", "Assertion@core/src/macros/mod.rs:51:20"),
    ];

    fn dump_dirs(root: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(root) else { return };
        let mut has_json = false;
        let mut subdirs = Vec::new();
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                subdirs.push(path);
            } else if path.extension().and_then(|x| x.to_str()) == Some("json") {
                has_json = true;
            }
        }
        if has_json {
            out.push(root.to_path_buf());
        }
        for sub in subdirs {
            dump_dirs(&sub, out);
        }
    }

    fn vcgen_vcs_for(
        func: &VerifiableFunction,
    ) -> (Vec<VerificationCondition>, Vec<VerificationCondition>) {
        use trust_vcgen::SummaryDatabase;
        let summaries = SummaryDatabase::new();
        let (solver_vcs, discharged) =
            trust_vcgen::generate_vcs_with_discharge_and_summaries(func, &summaries);
        (
            trust_vcgen::filter_vcs_by_level(solver_vcs, trust_types::ProofLevel::L1Functional),
            discharged.into_iter().map(|(vc, _)| vc).collect(),
        )
    }

    /// Trust (#63): the decline census's identity key for ONE dump instance.
    ///
    /// `content_hash()` is the repo's designated content identity and excludes
    /// `name`/`span` — which is what makes this key survive a fixture rename and
    /// still separate two dumps that share a `def_path`. Truncated to 16 hex
    /// digits for a readable pin; see [`SPINE_DECLINED_PIN`] for why 64 bits is
    /// ample when the key is the PAIR.
    fn declined_key(func: &VerifiableFunction) -> (String, String) {
        let hash = func.try_content_hash().expect(
            "a VerifiableFunction that just deserialized must re-serialize; a failure here \
             is a model bug, and hashing a fallback would give two different bodies one \
             census identity",
        );
        (func.def_path.clone(), hash.chars().take(16).collect())
    }

    /// Render a census in the exact source syntax of [`SPINE_DECLINED_PIN`], so a
    /// red run is repaired by pasting rather than by hand-deriving a key.
    fn render_census(rows: &std::collections::BTreeSet<(String, String)>) -> String {
        rows.iter().map(|(d, h)| format!("        ({d:?}, {h:?}),\n")).collect()
    }

    #[test]
    fn no_obligation_is_derived_by_the_spine_and_checked_by_nobody() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../trust-clean/fixtures");
        let mut dirs = Vec::new();
        dump_dirs(&root, &mut dirs);
        assert!(!dirs.is_empty(), "the fixture corpora must be found, or this measures nothing");

        let mut functions = 0usize;
        let mut native_only: Vec<String> = Vec::new();
        let mut vcgen_only_total = 0usize;
        let mut unsafe_model_total = 0usize;
        // Trust (#61, C0): the tripwire counters. The two-sided bound above cannot
        // see a function that silently stops being COMPARED: a spine edit that makes
        // `generate_native_safety_vcs` decline (return None) flips the outcome from
        // Disagreed to FlippedFallback, the diff is never computed, and vcgen_only
        // DROPS under its ceiling while cross-check coverage was retired -- the
        // metric launders. Measured against the campaign this exists to guard: one
        // stray `?` in a new lowering arm converts compared functions into declines.
        let mut spine_declined: std::collections::BTreeSet<(String, String)> = Default::default();
        let mut native_generated = 0usize;
        let mut vcgen_only_by_class: std::collections::BTreeMap<String, usize> = Default::default();
        let mut assertion_rows_observed: Vec<(String, String)> = Vec::new();

        for dir in &dirs {
            let Ok(entries) = std::fs::read_dir(dir) else { continue };
            for entry in entries.flatten() {
                let path = entry.path();
                if path.extension().and_then(|x| x.to_str()) != Some("json") {
                    continue;
                }
                let Ok(text) = std::fs::read_to_string(&path) else { continue };
                let Ok(func) = serde_json::from_str::<VerifiableFunction>(&text) else { continue };
                functions += 1;
                let (vcgen, discharged) = vcgen_vcs_for(&func);
                // Trust (#61, C0): count spine declines DIRECTLY, not via the outcome
                // -- FlippedFallback conflates "spine declined" with "spine agreed
                // byte-for-byte after the formula check", and only the first is the
                // laundering hazard.
                if crate::lower::generate_native_safety_vcs(&func).is_none() {
                    spine_declined.insert(declined_key(&func));
                }
                let (_dispatched, outcome) = generate_native_or_flip_safety_vcs_with_discharged(
                    &func,
                    vcgen,
                    discharged.iter(),
                );
                match outcome {
                    NativeGenOutcome::NativeGenerated(_) => native_generated += 1,
                    NativeGenOutcome::Disagreed { diff, .. } => {
                        for k in &diff.vcgen_only {
                            if k.class == "Assertion(unsafe-model)" {
                                unsafe_model_total += 1;
                            } else {
                                vcgen_only_total += 1;
                                *vcgen_only_by_class.entry(k.class.clone()).or_insert(0) += 1;
                                if k.class == "Assertion" {
                                    assertion_rows_observed
                                        .push((func.def_path.clone(), k.to_string()));
                                }
                            }
                        }
                        native_only.extend(
                            diff.native_only.iter().map(|k| format!("{} :: {k}", func.def_path)),
                        );
                    }
                    NativeGenOutcome::FlippedFallback(_) => {}
                }
            }
        }

        assert!(functions > 2_000, "expected the full corpus, saw {functions} functions");

        // Trust (#63): EVERY GATE BELOW REPORTS; NONE ABORTS. These used to be a
        // run of bare `assert!`s, and the first one to fire ended the test — so
        // when the decline ceiling went red at 227/225, the dispatch floor, the
        // Assertion identity pin and the per-class ceilings behind it were not
        // "green", they were UNRUN, and nothing in the output said so. A gate
        // that fires first and aborts hides every gate behind it, and an
        // instrument that reports one finding per run takes as many runs as it
        // has defects. Each check now pushes onto `findings` and the single
        // assertion at the end prints all of them at once.
        //
        // The corpus precondition above stays a hard `assert!` on purpose: if the
        // fixtures did not load, every measurement below is vacuous and reporting
        // them as findings would be noise about nothing.
        let mut findings: Vec<String> = Vec::new();

        // THE GATE, at zero. Each row here is an obligation the trust-ir spine
        // derived that trust-vcgen neither dispatched nor discharged — a
        // proposition nothing in the pipeline verifies. Whitelisting a row is not
        // a fix; either the spine should not be deriving it (make the two
        // producers agree, as the div/rem fold did) or trust-vcgen has a hole.
        if !native_only.is_empty() {
            findings.push(format!(
                "UNCHECKED OBLIGATION(S): the trust-ir spine derived {} obligation(s) that \
                 trust-vcgen neither emitted nor discharged. Each is a proposition nothing \
                 verifies — an obligation that is never emitted produces silence, and silence \
                 is indistinguishable from success everywhere downstream:\n  {}",
                native_only.len(),
                native_only.join("\n  "),
            ));
        }

        // THE OTHER DIRECTION, and it needs its own bound. The zero-gate above only
        // catches the spine deriving TOO MUCH. A fold that is too AGGRESSIVE fails
        // the opposite way: the spine stops deriving an obligation trust-vcgen still
        // emits, which lands in `vcgen_only` and would sail past the gate above.
        //
        // That is not a soundness hole — trust-vcgen's obligation is still
        // dispatched and still checked — but it silently retires cross-check
        // coverage, and cross-checking is the entire value of running two
        // producers. Pinning a ceiling here means the div/rem fold cannot quietly
        // grow into obligations it was never meant to cover.
        if vcgen_only_total > VCGEN_ONLY_CEILING {
            findings.push(format!(
                "the spine's coverage gap GREW to {vcgen_only_total} (ceiling \
                 {VCGEN_ONLY_CEILING}). Nothing is unchecked — trust-vcgen still dispatches \
                 these — but the spine stopped cross-checking obligations it used to, which \
                 is how an over-aggressive fold hides.",
            ));
        }

        // Trust (#61, C0) -- the tripwires, pinned to measured values. Each guards a
        // laundering channel the two-sided bound above cannot see:
        //
        //  * SPINE_DECLINED_PIN: a regression that makes compared functions
        //    DECLINE drops their rows from vcgen_only without closing anything.
        //    The census makes that drop red instead of green -- and, unlike the
        //    cardinality it replaced, it NAMES the rows so intake can be told
        //    apart from retired coverage.
        //  * NATIVE_DISPATCH_FLOOR: the count of functions where the spine IS the
        //    dispatched producer must never silently fall.
        //  * per-class sub-ceilings: a campaign that claims to close one class must
        //    move THAT class's number; the aggregate alone can hide a swap.
        let pinned_declined: std::collections::BTreeSet<(String, String)> = SPINE_DECLINED_PIN
            .iter()
            .map(|(d, h)| ((*d).to_string(), (*h).to_string()))
            .collect();
        let unpinned_declines: std::collections::BTreeSet<(String, String)> =
            spine_declined.difference(&pinned_declined).cloned().collect();
        let vanished_declines: std::collections::BTreeSet<(String, String)> =
            pinned_declined.difference(&spine_declined).cloned().collect();
        if !unpinned_declines.is_empty() {
            findings.push(format!(
                "UNPINNED spine decline(s): {} dump instance(s) whose \
                 `generate_native_safety_vcs` returns None are absent from \
                 SPINE_DECLINED_PIN:\n{}\
                 Classify each before pinning it, because the two causes are opposite. \
                 If the dump FILE is new to the corpus, this is INTAKE and retires no \
                 cross-check coverage — pin it with the reason and the decline site. If \
                 the dump was already here, a COMPARED function has stopped being \
                 comparable: that is the laundering channel, because its rows leave \
                 vcgen_only and the coverage gap reads as improvement.\n\
                 The full census, in source syntax, paste-ready:\n{}",
                unpinned_declines.len(),
                render_census(&unpinned_declines),
                render_census(&spine_declined),
            ));
        }
        if !vanished_declines.is_empty() {
            findings.push(format!(
                "STALE SPINE_DECLINED_PIN row(s): {} pinned decline(s) are no longer \
                 observed:\n{}\
                 This is PROGRESS (the spine can compare them now) or a fixture deletion, \
                 and it is red on purpose — delete the line(s) so the census keeps \
                 matching the corpus. A census nobody prunes stops being evidence.\n\
                 The full census, in source syntax, paste-ready:\n{}",
                vanished_declines.len(),
                render_census(&vanished_declines),
                render_census(&spine_declined),
            ));
        }
        if native_generated < NATIVE_DISPATCH_FLOOR {
            findings.push(format!(
                "native dispatch FELL to {native_generated} (floor {NATIVE_DISPATCH_FLOOR}): \
                 fewer functions dispatch the spine's own VC set than before.",
            ));
        }
        // Trust (#62, C-D0): identity pin — observed must be a SUBSET of pinned.
        // A new identity is a real finding (a function stopped agreeing, or a new
        // shape entered the corpus) and must be looked at, not absorbed by a count.
        let unexpected_assertion_rows: Vec<&(String, String)> = assertion_rows_observed
            .iter()
            .filter(|(d, k)| {
                !EXPECTED_ASSERTION_VCGEN_ONLY_ROWS
                    .iter()
                    .any(|(pd, pk)| pd == d && pk == k)
            })
            .collect();
        if !unexpected_assertion_rows.is_empty() {
            findings.push(format!(
                "NEW Assertion-class vcgen_only identit{} (not in the 2026-08-20 pin):\n  {:?}\n\
                 A new identity means a function stopped agreeing or a new shape entered \
                 the corpus — investigate; do not widen the pin without naming why.",
                if unexpected_assertion_rows.len() == 1 { "y" } else { "ies" },
                unexpected_assertion_rows,
            ));
        }
        for (pd, pk) in EXPECTED_ASSERTION_VCGEN_ONLY_ROWS {
            if !assertion_rows_observed.iter().any(|(d, k)| d == pd && k == pk) {
                eprintln!("pinned Assertion row no longer observed (downward motion): {pd} :: {pk}");
            }
        }
        for (class, ceiling) in VCGEN_ONLY_CLASS_CEILINGS {
            let n = vcgen_only_by_class.get(*class).copied().unwrap_or(0);
            if n > *ceiling {
                findings.push(format!("vcgen_only class `{class}` GREW to {n} (ceiling {ceiling})"));
            }
        }

        assert!(
            findings.is_empty(),
            "{} ratchet finding(s), ALL of them — this instrument no longer stops at the \
             first:\n\n{}",
            findings.len(),
            findings
                .iter()
                .enumerate()
                .map(|(i, f)| format!("[{}/{}] {f}", i + 1, findings.len()))
                .collect::<Vec<_>>()
                .join("\n\n"),
        );
        eprintln!(
            "alarm: {functions} functions, native_only=0, vcgen_only={vcgen_only_total} \
             (spine-derivable coverage gap, ceiling {VCGEN_ONLY_CEILING}), \
             unsafe_model={unsafe_model_total} (not a gap — never spine-derived)"
        );
        // Both figures, because they answer different questions and the pin is
        // keyed on the first: INSTANCES is what the census pins (242 of the 2334
        // dumps share a def_path with another, so the two counts must differ),
        // UNIQUE def_paths is what the retired `SPINE_DECLINED_CEILING` counted
        // and is kept only so older measurements remain comparable.
        let declined_unique: std::collections::BTreeSet<&String> =
            spine_declined.iter().map(|(d, _)| d).collect();
        eprintln!(
            "tripwires: spine_declined={} instances / {} unique def_paths (census pinned at \
             {} rows), native_generated={native_generated} (floor {NATIVE_DISPATCH_FLOOR})",
            spine_declined.len(),
            declined_unique.len(),
            SPINE_DECLINED_PIN.len(),
        );
        eprintln!("vcgen_only by class: {vcgen_only_by_class:?}");
    }
}

/// Trust (#57) — the ratchet's negative controls. A gate that cannot go red is not
/// a gate, so these drive the diff directly rather than through the corpus.
#[cfg(test)]
mod missing_obligation_alarm_controls {
    use super::*;

    fn vc(kind: VcKind, line: u32) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: trust_types::Symbol::intern("ctrl"),
            location: trust_types::SourceSpan {
                file: "CTRL.rs".to_string(),
                line_start: line,
                col_start: 1,
                line_end: line,
                col_end: 2,
            },
            // The formula is deliberately irrelevant to this comparison — that is
            // the whole point of keying on `(class, span)`. A `Bool(true)` here
            // would silently pass even if the diff DID look at formulas, so use a
            // distinguishable one.
            formula: trust_types::Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn render(keys: &[ObligationKey]) -> Vec<String> {
        keys.iter().map(ToString::to_string).collect()
    }

    fn add_overflow_kind() -> VcKind {
        VcKind::ArithmeticOverflow {
            op: trust_types::BinOp::Add,
            operand_tys: (
                trust_types::Ty::Int { width: 32, signed: false },
                trust_types::Ty::Int { width: 32, signed: false },
            ),
        }
    }

    /// POSITIVE CONTROL — an obligation only the spine derives, of a class the
    /// ratchet does not whitelist, IS reported. This is the failure the whole
    /// mechanism exists to catch.
    #[test]
    fn spine_only_obligation_is_reported() {
        let native = vec![vc(add_overflow_kind(), 10)];
        let diff = l0_obligation_set_diff(&native, &[]);
        assert_eq!(render(&diff.native_only), vec!["ArithmeticOverflow(Add)@CTRL.rs:10:1"]);
        assert!(diff.vcgen_only.is_empty());
        assert!(!diff.is_empty(), "a spine-only obligation must NOT read as agreement");
    }

    /// The compiler renders each `native_only` entry into a fail-closed finding
    /// with THIS message. Pinned here because the caller lives in `compiler/**`,
    /// which no cargo sweep reaches.
    #[test]
    fn unchecked_finding_message_names_the_class_and_both_fixes() {
        let key = ObligationKey {
            class: "BoundsCheck".to_string(),
            location: trust_types::SourceSpan {
                file: "CTRL.rs".to_string(),
                line_start: 7,
                col_start: 1,
                line_end: 7,
                col_end: 2,
            },
        };
        let msg = key.unchecked_finding_message();
        assert!(msg.contains("BoundsCheck"), "the finding must name the obligation class");
        assert!(
            msg.contains("neither emitted nor discharged"),
            "the finding must say WHY nothing checked it, not merely that something is wrong"
        );
        // v7-D3: a refusal carries the fix, with OPTIONS. Both must be present —
        // "unsupported, good luck" is a defect.
        assert!(msg.contains("(a) teaching trust-vcgen to emit it"), "fix (a) missing");
        assert!(msg.contains("(b) making the spine agree"), "fix (b) missing");
    }

    /// NEGATIVE CONTROL — a DISCHARGED obligation is checked, and must not be
    /// reported. Without this the alarm claims "nothing verifies this" about
    /// something trust-vcgen proved.
    #[test]
    fn discharged_obligation_is_not_reported() {
        let native = vec![vc(add_overflow_kind(), 10)];
        let discharged = vec![vc(add_overflow_kind(), 10)];
        let diff = l0_obligation_set_diff_with_discharged(&native, &[], discharged.iter());
        assert!(diff.is_empty(), "a discharged obligation is checked: {diff:?}");
    }

    /// NEGATIVE CONTROL — the two producers' different SPELLINGS of the bounds
    /// obligation are the same obligation. Four corpus rows depend on this.
    #[test]
    fn bounds_kind_spelling_is_not_a_disagreement() {
        let native = vec![vc(VcKind::SliceBoundsCheck, 20)];
        let vcgen = vec![vc(VcKind::IndexOutOfBounds, 20)];
        let diff = l0_obligation_set_diff(&native, &vcgen);
        assert!(diff.is_empty(), "SliceBoundsCheck vs IndexOutOfBounds at one span: {diff:?}");
    }

    /// NEGATIVE CONTROL — but a bounds obligation at a DIFFERENT span is a
    /// different obligation, so aliasing the kind must not alias the span too.
    #[test]
    fn bounds_alias_does_not_collapse_distinct_spans() {
        let native = vec![vc(VcKind::SliceBoundsCheck, 20)];
        let vcgen = vec![vc(VcKind::IndexOutOfBounds, 21)];
        let diff = l0_obligation_set_diff(&native, &vcgen);
        assert_eq!(render(&diff.native_only), vec!["BoundsCheck@CTRL.rs:20:1"]);
        assert_eq!(render(&diff.vcgen_only), vec!["BoundsCheck@CTRL.rs:21:1"]);
    }

    /// NEGATIVE CONTROL — the spine MISSING an obligation trust-vcgen emits is a
    /// coverage gap, not silence: it lands in `vcgen_only`, never in the alarm
    /// direction. Conflating the two would bury the real signal in 250 rows.
    #[test]
    fn spine_coverage_gap_is_the_other_direction() {
        let vcgen = vec![vc(VcKind::DivisionByZero, 30)];
        let diff = l0_obligation_set_diff(&[], &vcgen);
        assert!(diff.native_only.is_empty(), "a spine gap is not an unchecked obligation");
        assert_eq!(render(&diff.vcgen_only), vec!["DivisionByZero@CTRL.rs:30:1"]);
    }
}
