// trust_vcgen/modular.rs: Modular verification with function summaries
//
// Extends SpecDatabase-based cross-function reasoning with a structured
// summary model. Each function summary captures pre/postconditions and
// proof status. At call sites:
// - Proved summary: verify preconditions
// - CONTRACT postconditions remain unmodeled (retained as evidence only): a
//   public label cannot authorize assuming a claim nobody replayed.
// - DEFINITIONAL postconditions (`with_definitional_postcondition` — the I5
//   cross-authority Clean-origin lane) ARE assumed at call sites, via the
//   establish-point rebinding lane in `generate::semantic_guard`; see
//   `has_reusable_postcondition_evidence` for the authority boundary.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::admissible_body::{ArithBinOp, ArithOperand};
use trust_types::fx::FxHashMap;
use trust_types::*;

use crate::specdb::SpecDatabase;

/// Trust: A function summary for modular verification.
///
/// Captures the contract (pre/postconditions) and proof status of a function.
/// When a callee has a proved summary, callers must verify the precondition at
/// the call site. Postconditions are retained as evidence only; callers must
/// not assume them without a precise call-site model.
#[derive(Debug, Clone)]
pub struct FunctionSummary {
    /// The function's name (matching `VerifiableFunction::name`).
    pub name: String,
    /// Formal parameter names in declaration order (e.g., `["x", "y"]`).
    /// Used by `wp_call` to substitute parameter names with actual argument
    /// expressions at call sites.
    pub param_names: Vec<String>,
    /// Trust (piece #8 — length-relationship preconditions): formal parameter
    /// TYPES in declaration order, parallel to `param_names`. Empty when the
    /// producer did not record them (every non-R1 caller). Used ONLY by
    /// `generate_callsite_precondition_vcs_attributed` to know WHICH formal is a
    /// slice/array — and thus needs a `<formal>__slice_len` σ length-replacement
    /// so a precondition like `n <= arr__slice_len` can discharge at the caller.
    /// Carries no proof authority; it is pure metadata for the σ renderer.
    pub param_types: Vec<Ty>,
    /// Preconditions that callers must satisfy at call sites.
    pub preconditions: Vec<Formula>,
    /// Postconditions proved for the callee. These are not automatically
    /// assumed by callers.
    pub postconditions: Vec<Formula>,
    /// F6 (float interval summaries): a signed interval containing every
    /// possible f64 return value of the callee UNDER ITS OWN preconditions,
    /// derived by the verifier's float tracer
    /// (`generate::derive_float_result_range` via `summaries::compute_summary`).
    /// `None` = no claim; every other producer — including the compiler's
    /// contract-summary builder — leaves it unset, so consumption is
    /// fail-closed there. Consumed ONLY by the float interval lane
    /// (`generate::float_summary_result_range`), which re-validates the
    /// interval shape and structurally re-establishes the callee's
    /// preconditions at the consuming call site (assume-guarantee) before
    /// honoring it.
    pub result_range: Option<(f64, f64)>,
    /// F6b (context-sensitive callee tracing): the callee's extracted body.
    ///
    /// Carries NO proof authority — it is an ANALYSIS INPUT the float tracer
    /// RE-TRACES per call site under caller-derived argument intervals
    /// (`generate` float lane): the caller first proves an interval for each
    /// actual, binds it as a parameter override on the callee's formal, and
    /// only then evaluates the requested return place inside this body. A
    /// static `result_range` is callee-global (valid only under the callee's
    /// own preconditions); this per-callsite re-trace is what makes chained
    /// magnitude reasoning (`a.add(b).scale(s)`) context-sensitive. The body's
    /// own gated preconditions ARE consumed by the re-trace, so the consumer
    /// structurally re-establishes them at the call site first
    /// (assume-guarantee, same discipline as `result_range`). Never
    /// serialized: an extracted body only means anything inside the verifier
    /// session that extracted it.
    pub extracted_body: Option<std::sync::Arc<trust_types::VerifiableFunction>>,
    /// Whether the summary has been proved.
    pub proved: bool,
    /// Evidence id that justifies reusing postconditions as proof facts.
    pub proof_evidence_id: Option<String>,
    /// Proof strength attached to `proof_evidence_id`.
    pub proof_strength: Option<ProofStrength>,
    /// PRIVATE (I5 cross-authority call modeling): true iff `postconditions` is
    /// non-empty and EVERY entry was added through
    /// [`Self::with_definitional_postcondition`] — i.e. every clause is a
    /// DEFINITIONAL restatement of a callee body the producing compiler itself
    /// constructed, not a contract claim awaiting proof. This is the one bit
    /// [`Self::has_reusable_postcondition_evidence`] reads; it is deliberately
    /// not `pub`, so a deserialized or field-forged summary cannot carry it —
    /// the only way to set it is the builder whose doc states the authority
    /// contract, and ANY plain `with_postcondition` on the same summary clears
    /// it permanently (mixed provenance fails closed).
    postconditions_are_definitional: bool,
    /// PRIVATE (postcondition composition, slice 2): true iff every
    /// postcondition on this summary was added through
    /// [`Self::with_verified_callee_postcondition`] — the builder whose
    /// authority contract is "the producer proved `preconditions -> this
    /// clause`", NOT "this clause holds unconditionally".
    ///
    /// It is the ONE bit that says a postcondition must ride at a call site
    /// UNDER THIS SUMMARY'S OWN PRECONDITIONS, as the implication the callee
    /// actually proved, rather than as a free-standing fact. A summary carrying
    /// it may therefore hand its clause to a caller even with a non-empty
    /// `preconditions` (see `definitional_precondition_free_subset`), because
    /// the value fact and its guard travel together in one formula.
    ///
    /// Deliberately not `pub` and not reachable from any public field write,
    /// for the same reason as `postconditions_are_definitional`: without it, a
    /// preconditioned summary's clause would be assumed UNCONDITIONALLY, which
    /// is a false PROVE whenever the caller is out of the callee's contract.
    postconditions_guarded_by_own_preconditions: bool,
}

impl FunctionSummary {
    /// Create a new unproved summary with no conditions.
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            param_names: Vec::new(),
            param_types: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            result_range: None,
            extracted_body: None,
            proved: false,
            proof_evidence_id: None,
            proof_strength: None,
            postconditions_are_definitional: false,
            postconditions_guarded_by_own_preconditions: false,
        }
    }

    /// F6: attach a derived float result interval (see the field doc — only
    /// the verifier-owned derivation should call this outside tests).
    #[must_use]
    pub fn with_result_range(mut self, lo: f64, hi: f64) -> Self {
        self.result_range = Some((lo, hi));
        self
    }

    /// F6b: attach the callee's extracted body for context-sensitive
    /// re-tracing (see the field doc — an analysis input, not evidence; the
    /// consumer re-derives everything it claims from this body plus
    /// caller-proved actual intervals).
    #[must_use]
    pub fn with_extracted_body(
        mut self,
        body: std::sync::Arc<trust_types::VerifiableFunction>,
    ) -> Self {
        self.extracted_body = Some(body);
        self
    }

    /// Set formal parameter names (in declaration order).
    pub fn with_param_names(mut self, names: Vec<String>) -> Self {
        self.param_names = names;
        self
    }

    /// Trust (piece #8): set formal parameter TYPES (in declaration order,
    /// parallel to `with_param_names`). Only the R1 length-precondition path
    /// records these; other producers leave `param_types` empty (the σ renderer
    /// then emits no length replacement, unchanged behavior).
    pub fn with_param_types(mut self, types: Vec<Ty>) -> Self {
        self.param_types = types;
        self
    }

    /// Add a precondition.
    pub fn with_precondition(mut self, formula: Formula) -> Self {
        self.preconditions.push(formula);
        self
    }

    /// Add a postcondition.
    ///
    /// A postcondition added here is a CONTRACT CLAIM: evidence to report,
    /// never a fact to assume (`has_reusable_postcondition_evidence` stays
    /// false). Adding one also permanently strips any definitional authority
    /// the summary previously carried — a summary of mixed provenance must
    /// fail closed, because the injection lane conjoins EVERY rebindable
    /// clause and cannot tell them apart afterwards.
    pub fn with_postcondition(mut self, formula: Formula) -> Self {
        self.postconditions.push(formula);
        self.postconditions_are_definitional = false;
        self
    }

    /// Trust (I5 cross-authority call modeling): add a DEFINITIONAL
    /// postcondition — one that restates, over the callee's formals and the
    /// result symbol `_0`, the exact semantics of a callee body the CALLER OF
    /// THIS BUILDER itself constructed or verified by construction.
    ///
    /// # The authority contract, which the caller asserts by calling this
    ///
    /// Unlike `with_postcondition`, a clause added here is ASSUMED at call
    /// sites (rebound formals→actuals / `_0`→dest, version-pinned to the
    /// dest's post-call SSA token, conjoined — the
    /// `build_semantic_guard_map_with_summaries` lane). That is sound exactly
    /// when the clause is TRUE OF EVERY EXECUTION of the callee body, not
    /// merely claimed of it. The intended (and currently only) producer is
    /// the Trust compiler's Clean-origin lane: there the callee body is
    /// EMITTED by the compiler from a kernel-checked plan
    /// (`trust_clean_origin::plan_clean_origin_body`), the faithfulness gate
    /// fatally refuses compilation if the emitted body disagrees with that
    /// plan, and the clause passed here is derived from the SAME plan — so
    /// the clause is definitionally true of the body that will run.
    ///
    /// Do NOT call this with a parsed user contract, a deserialized artifact,
    /// or anything whose truth rests on a proof that has not happened inside
    /// the calling authority. That is what `with_postcondition` is for.
    ///
    /// Mixing is fail-closed in both orders: a summary holding any plain
    /// postcondition never regains definitional authority.
    #[must_use]
    pub fn with_definitional_postcondition(mut self, formula: Formula) -> Self {
        let pure = self.postconditions.is_empty() || self.postconditions_are_definitional;
        self.postconditions.push(formula);
        self.postconditions_are_definitional = pure;
        self
    }

    /// Trust (postcondition composition): add an authored `ensures` clause whose
    /// OWN obligation the calling authority has ALREADY DISCHARGED in this same
    /// compilation, so callers may ASSUME it at call sites.
    ///
    /// # The authority contract, which the caller asserts by calling this
    ///
    /// Same reuse bit, and therefore the same consequence, as
    /// [`Self::with_definitional_postcondition`]: the clause is rebound
    /// (formals→actuals, `_0`→dest), version-pinned to the dest's post-call SSA
    /// token, and CONJOINED onto the caller's VCs. The two differ only in WHERE
    /// the truth comes from — a definitional clause restates a body the producer
    /// emitted, this one restates a body the producer PROVED.
    ///
    /// The caller of this builder asserts ALL of:
    ///
    ///  * the clause is the callee's own authored `ensures`, extracted from the
    ///    callee's contract bundle at the same instantiation the call site uses;
    ///  * the callee's `ensures` obligation was independently discharged in THIS
    ///    compilation and every obligation of that callee is statically proved —
    ///    an `ensures` that is merely DECLARED is the laundering channel this bit
    ///    exists to keep shut (`ensures false` would otherwise let every caller
    ///    inherit it and verify vacuously);
    ///  * `self.preconditions` is the callee's COMPLETE authored `requires` set
    ///    at that same instantiation — see the WHAT IS PROVED note below, which
    ///    is why completeness (not emptiness) is the requirement;
    ///  * the summary's NAME resolves to exactly one callee identity in the body
    ///    being summarized — the DB is keyed by a string, and a collision would
    ///    apply one callee's `ensures` at another's call site.
    ///
    /// # WHAT IS PROVED IS AN IMPLICATION, AND IT IS ASSUMED AS ONE
    ///
    /// A contract postcondition is guaranteed only WHERE THE PRECONDITION HELD:
    /// the callee's proof discharges `requires -> ensures`, never `ensures`
    /// alone. Slice 1 sidestepped that by refusing any callee with a `requires`
    /// at all. This builder does not — it sets
    /// `postconditions_guarded_by_own_preconditions`, and the call-site lane
    /// then injects the clause as exactly the implication that was proved,
    /// `pre[formals:=actuals] -> post[formals:=actuals, _0:=dest]`
    /// ([`crate::generate::rebind_callee_postconditions`]).
    ///
    /// That is what ties the assumption to the DISCHARGE AT THIS CALL SITE. The
    /// caller obtains the postcondition exactly when its own path context
    /// entails the instantiated precondition, and obtains NOTHING when it does
    /// not — in the same solver query, with no dependence on the separately
    /// emitted (and, at `L0Safety`, level-FILTERED) `VcKind::Precondition` row.
    /// Assuming the raw clause instead would be a false PROVE for every caller
    /// that is out of the callee's contract.
    ///
    /// Do NOT call this with a contract that has only been PARSED. That is what
    /// `with_postcondition` is for. Mixing is fail-closed in both orders, exactly
    /// as for the definitional builder, and the GUARD bit is additionally STICKY:
    /// once any clause has arrived under it, every clause on this summary rides
    /// under the precondition antecedent. Guarding a clause that did not need it
    /// only ever weakens the injected fact, so stickiness is the safe direction;
    /// clearing it on a later `with_definitional_postcondition` would silently
    /// un-guard the clause added here.
    #[must_use]
    pub fn with_verified_callee_postcondition(mut self, formula: Formula) -> Self {
        let pure = self.postconditions.is_empty() || self.postconditions_are_definitional;
        self.postconditions.push(formula);
        self.postconditions_are_definitional = pure;
        self.postconditions_guarded_by_own_preconditions = true;
        self
    }

    /// Trust (postcondition composition, slice 2): whether this summary's
    /// postconditions must ride at a call site UNDER its own preconditions.
    ///
    /// See the field doc and [`Self::with_verified_callee_postcondition`]. Read
    /// by exactly two places, which must agree:
    /// [`crate::generate::summary_postconditions_ride_with_their_guard`] (the
    /// ADMIT side, consulted by `definitional_precondition_free_subset` and by
    /// `callee_postcondition_is_injectable`) and
    /// [`crate::generate::rebind_callee_postconditions`] (the EMIT side).
    pub(crate) fn postconditions_guarded_by_own_preconditions(&self) -> bool {
        self.postconditions_guarded_by_own_preconditions
    }

    /// Mark the summary as proved for modular precondition checking.
    ///
    /// This does not authorize exporting postconditions as reusable facts.
    /// Reusable fact export is reserved for verifier-owned checked evidence.
    pub fn proved(mut self) -> Self {
        self.proved = true;
        self
    }

    /// Attach external proof metadata to this summary.
    ///
    /// The identifier and strength are public, forgeable metadata. They are
    /// retained for reporting but never authorize postcondition injection or VC
    /// suppression.
    pub fn with_proof_evidence(
        mut self,
        evidence_id: impl Into<String>,
        strength: ProofStrength,
    ) -> Self {
        self.proved = true;
        self.proof_evidence_id = Some(evidence_id.into());
        self.proof_strength = Some(strength);
        self
    }

    #[cfg(test)]
    /// Construct the strongest legacy metadata shape for negative authority
    /// tests. Despite the name, this does not carry or replay proof bytes.
    pub(crate) fn with_checked_proof_evidence(
        mut self,
        evidence_id: impl Into<String>,
        strength: ProofStrength,
    ) -> Self {
        self.proved = true;
        self.proof_evidence_id = Some(evidence_id.into());
        self.proof_strength = Some(strength);
        self
    }

    /// Attach compiler contract metadata to this summary.
    ///
    /// A def-path string is not proof evidence. This builder deliberately keeps
    /// the old metadata shape for diagnostics while the authority gate below
    /// remains closed until the compiler can transport and replay an exact
    /// contract/obligation-bound proof artifact.
    #[must_use]
    pub fn with_verified_contract_evidence(mut self, evidence_id: impl Into<String>) -> Self {
        self.proved = true;
        self.proof_evidence_id = Some(evidence_id.into());
        self.proof_strength = Some(ProofStrength::deductive());
        self
    }

    /// Whether this summary may authorize postcondition reuse.
    ///
    /// For CONTRACT-CLAIM postconditions this stays hard-blocked, for the
    /// original reason: every public field on `FunctionSummary` is publicly
    /// constructible, and `proof_evidence_id` is only an unbound string —
    /// accepting those would let a caller stamp `Sound`/`Certified` and
    /// conjoin an arbitrary postcondition into a caller VC. That half is
    /// unchanged: `proved`, `proof_evidence_id`, and `proof_strength` still
    /// authorize NOTHING here, and re-enabling them still requires an opaque,
    /// replayed proof capability bound to the exact callee identity, contract
    /// digest, and instantiated obligation.
    ///
    /// The ONE open lane is the crate-private DEFINITIONAL bit
    /// (`postconditions_are_definitional`), settable only through
    /// [`Self::with_definitional_postcondition`] — see its doc for the
    /// authority contract the caller asserts. It is not reachable from any
    /// public field write, any evidence string, or any mix that includes a
    /// plain `with_postcondition` clause.
    pub(crate) fn has_reusable_postcondition_evidence(&self) -> bool {
        self.postconditions_are_definitional && !self.postconditions.is_empty()
    }
}

/// Trust (I5 cross-authority call modeling — `WrappingBinOp`): the DEFINITIONAL
/// postcondition set for a Clean-origin callee whose emitted body is a single
/// wrapping binary op — `bb0: _0 = Call(u{w}::wrapping_{op}, [l, r]) -> bb1:
/// Return` — over operands that are each a source parameter or an in-range
/// numeral, at ONE unsigned machine width `width` shared by every signature
/// position (the shape `trust_clean_origin::CleanOriginShape::WrappingBinOp`
/// plans, with `width` from the plan's result carrier).
///
/// # The encoding, and why it is not this function's to choose
///
/// The clauses restate the EXTRACTOR'S OWN wrapping encoding — the single-`Ite`
/// modular reduction `generate::assert_refutation::wrapping_call_assert_model`
/// produces when it models a call to the SAME `u{w}::wrapping_{op}` primitive
/// inside an ordinary extracted Rust body, kept in Int/LIA so ay decides it
/// directly:
///
/// ```text
/// wrapping_add:  _0 == ite(x + y >= 2^w, x + y - 2^w, x + y)
/// wrapping_sub:  _0 == ite(x - y <  0,   x - y + 2^w, x - y)
/// ```
///
/// plus the extractor's operand range facts (`0 <= operand <= 2^w - 1`, one per
/// operand — true of every execution, because both operands are typed `u{w}`).
/// A summary that encoded wrapping DIFFERENTLY from the extractor's own
/// encoding would be a soundness bug: the same call modeled two ways in one
/// solver query can manufacture or destroy models. The unit tests in
/// `generate::clean_origin_wrapping_summary_tests` pin this equality against
/// `wrapping_call_assert_model` itself (same operands, same dest — the rebound
/// clauses must be BYTE-IDENTICAL formulas), so the two encodings cannot drift
/// silently. The unbounded `_0 == x + y` would be the classic false-PROVE
/// (`assert!(a.wrapping_add(1) > a)` at `a == MAX`) and is exactly what the
/// injection gate's machine-arithmetic filter still rejects
/// (`contracts::formula_is_exact_modular_wrapping_definition` admits ONLY the
/// self-consistent modular shape above).
///
/// # Authority contract
///
/// Every returned clause is intended for
/// [`FunctionSummary::with_definitional_postcondition`] and is definitionally
/// true of every execution of the emitted callee body — the producer (the
/// Trust compiler's Clean-origin lane) derives `op`/`left`/`right`/`width`
/// from the SAME kernel-gated plan the emitter acted on, and the faithfulness
/// gate fatally refuses compilation if the emitted body disagrees with that
/// plan. Do NOT call this with values from any other source.
///
/// # Refusals — `None` means "inject nothing", never a fallback
///
/// * **`ArithBinOp::Mul` — the recorded boundary.** The extractor's own Int/LIA
///   lane has NO encoding for `wrapping_mul` (its `WrappingMul(_) => None`:
///   the full nonlinear modular reduction is not decidable in the lane that
///   consumes these clauses, and a single-`Ite` reduction is wrong for `mul`,
///   which can wrap more than once). Encoding it here — e.g. via
///   `Formula::Rem` — would diverge from the extractor's own encoding, which
///   is the soundness bar stated above. The call's panic-freedom is modeled
///   separately by the compiler (wrapping ops are total); only its VALUE stays
///   havocked, fail-closed.
/// * **`width` outside `1..=64`** — the modulus `1i128 << width` (= `2^width`)
///   must stay within `i128` (the extractor's own cap, same reason); the
///   Clean-origin planner only mints 8/16/32/64, so this is refuse-not-trust.
/// * **`Param(i)` with `i >= param_names.len()`**, or **`Const(v)` with
///   `v >= 2^width`** — the planner guarantees neither can happen
///   (`recognise_arith_operand` re-checks numerals against the carrier width);
///   any violation refuses the summary rather than trusting it.
#[must_use]
pub fn clean_origin_wrapping_binop_postconditions(
    op: ArithBinOp,
    left: ArithOperand,
    right: ArithOperand,
    width: u32,
    param_names: &[String],
) -> Option<Vec<Formula>> {
    // The recorded Mul boundary — see the doc above. An explicit match with no
    // `_` arm, so a future `ArithBinOp` variant fails compilation here rather
    // than falling through to either polarity.
    match op {
        ArithBinOp::Add | ArithBinOp::Sub => {}
        ArithBinOp::Mul => return None,
    }
    if !(1..=64).contains(&width) {
        return None;
    }
    let operand_formula = |operand: ArithOperand| -> Option<Formula> {
        match operand {
            ArithOperand::Param(i) => Some(Formula::var(param_names.get(i)?.as_str(), Sort::Int)),
            // width <= 64 (checked above), so the shift cannot overflow and the
            // in-range value cannot exceed i128::MAX.
            ArithOperand::Const(v) => (v < (1u128 << width)).then(|| Formula::Int(v as i128)),
        }
    };
    let x = operand_formula(left)?;
    let y = operand_formula(right)?;
    // The single-Ite modular reduction, via THE shared constructor
    // (`generate::wrapping_binop_modular_ite`) — the same one
    // `wrapping_call_assert_model` and the bare-`Rvalue::BinaryOp` statement
    // model use, so this summary can never encode wrapping differently from
    // the extractor (the pin tests additionally compare the outputs
    // structurally against `wrapping_call_assert_model` itself).
    let bin_op = match op {
        ArithBinOp::Add => trust_types::BinOp::Add,
        ArithBinOp::Sub => trust_types::BinOp::Sub,
        ArithBinOp::Mul => return None, // unreachable; kept fail-closed
    };
    let ite = crate::generate::wrapping_binop_modular_ite(bin_op, &x, &y, width, false)?;
    let def = Formula::Eq(Box::new(Formula::var("_0", Sort::Int)), Box::new(ite));
    // The extractor emits a range fact per OPERAND FORMULA, unconditionally for
    // both operands (a constant's range fact is ground and trivially true).
    // Mirror it exactly — the parity pin covers these clauses too. Each fact is
    // definitional: a `u{width}`-typed value is in `[0, 2^width - 1]` in every
    // execution, and a rebindable free var (the formal) or no free var at all.
    let ranges = [
        crate::range::input_range_constraint(&x, width, false),
        crate::range::input_range_constraint(&y, width, false),
    ];
    Some(std::iter::once(def).chain(ranges).collect())
}

/// Trust (Clean-origin caller-side preconditions): the call-site obligations a
/// minted Clean-origin `def` carries, rendered over the summary's formal
/// parameter names.
///
/// This is the consuming half of the seam `fa788aab89` named: *"a caller-side
/// precondition on the minted `DefId` … its discharge is an ordinary Rust
/// obligation, never a `Faithful` token."* The producing half is
/// `trust_clean_carrier`'s hypothesis lift, which reads an erased proof binder
/// (`(h : b ≠ 0)`) off the Clean declaration's type. The two sides meet on
/// `trust_types::clean_origin_precondition`, the only vocabulary they share.
///
/// The returned formulas are for [`FunctionSummary::with_precondition`], which
/// is checked at every call site by the ordinary
/// `generate_callsite_precondition_vcs` lane: formals substituted by the
/// caller's actuals, caller path guards in scope, one `VcKind::Precondition`
/// row per call. Nothing here is assumed, and nothing here is a proof claim —
/// a precondition is a DEMAND on the caller.
///
/// # ALL OR NOTHING — the rule `650674bc71` restored
///
/// `None` is returned if **any single** obligation cannot be rendered, and the
/// producer must then publish NO summary at all — not the value facts without
/// the guard. That is the same rule the L0 subset enforces one layer up
/// (`SummaryDatabase::definitional_precondition_free_subset`): *a fact that
/// cannot travel with its guard must not travel at all*. Returning the
/// renderable subset would be strictly worse than returning nothing, because a
/// partially-guarded summary reads to every downstream consumer exactly like a
/// fully-guarded one.
///
/// # Refusals
///
/// * **an `Argument(i)` with `i >= param_names.len()`** — the call site has no
///   actual to substitute at that position, and a positional substitution would
///   silently bind the obligation to the wrong value or leave the formal free
///   (a free variable in `¬P[σ]` is spuriously SAT, which mints a VIOLATION row
///   about a proposition nobody stated);
/// * **`width` outside `1..=64`**, or a `Literal(v)` with `v >= 2^width` — the
///   producer range-checks both, so any violation here means the two sides
///   disagree, and a disagreement refuses rather than picks a reading;
/// * **a `Literal` above `i128::MAX`** — `Formula::Int` is `i128`, and a
///   numeral that does not fit it cannot be stated in this lane at all.
#[must_use]
pub fn clean_origin_declared_preconditions(
    preconditions: &[CleanOriginPrecondition],
    param_names: &[String],
) -> Option<Vec<Formula>> {
    let mut rendered = Vec::with_capacity(preconditions.len());
    for precondition in preconditions {
        rendered.push(clean_origin_declared_precondition(precondition, param_names)?);
    }
    Some(rendered)
}

/// One obligation, rendered. See [`clean_origin_declared_preconditions`] — this
/// is its per-atom half and shares every refusal.
#[must_use]
pub fn clean_origin_declared_precondition(
    precondition: &CleanOriginPrecondition,
    param_names: &[String],
) -> Option<Formula> {
    let width = precondition.width();
    if !(1..=64).contains(&width) {
        return None;
    }
    // Checked ONCE, before either operand is spelled: an out-of-range argument
    // index must refuse the whole atom, not produce half of one.
    if let Some(max) = precondition.max_argument_index()
        && max >= param_names.len()
    {
        return None;
    }

    let operand = |o: PreconditionOperand| -> Option<Formula> {
        match o {
            PreconditionOperand::Argument(i) => {
                Some(Formula::var(param_names.get(i)?.as_str(), Sort::Int))
            }
            PreconditionOperand::Literal(v) => {
                // Re-checked against the carrier width HERE rather than trusted
                // from the producer — the two crates range-check independently
                // on purpose, exactly as `carrier_for` and
                // `RepresentationObligation` do.
                if v >= (1u128 << width) {
                    return None;
                }
                i128::try_from(v).ok().map(Formula::Int)
            }
        }
    };

    let left = operand(precondition.left())?;
    let right = operand(precondition.right())?;

    match precondition.relation() {
        PreconditionRelation::NotEqual => {
            Some(Formula::Not(Box::new(Formula::Eq(Box::new(left), Box::new(right)))))
        }
        // `PreconditionRelation` is `#[non_exhaustive]`. A relation this
        // renderer has not grown an arm for withholds the WHOLE summary (the
        // all-or-nothing rule above), which is the fail-closed direction: a new
        // producer capability cannot reach a call site until the consumer can
        // spell it.
        #[allow(unreachable_patterns)]
        _ => None,
    }
}

/// Trust (Clean-origin caller-side preconditions): build the whole caller-side
/// summary for a minted Clean-origin `def` — its definitional value facts AND
/// the caller obligations its erased hypothesis binders impose — or **nothing**.
///
/// # This function IS the "publish nothing" rule, made structural
///
/// `650674bc71` restored the rule for the DB layer: *"a summary whose guard
/// cannot be carried must publish NO fact — never the fact without the guard."*
/// One layer up, the producer can violate the same rule by a plain `?` in the
/// wrong place: render the postconditions, fail to render a precondition,
/// publish the postconditions anyway. Nothing downstream can see that happen —
/// a summary with no preconditions is indistinguishable from a callee that
/// never had any.
///
/// So the producer does not get the two halves separately. It gets this, which
/// returns `Some` only when every obligation was rendered, and `None`
/// otherwise. There is no argument order that publishes half.
///
/// # What the caller must still do with `None`
///
/// `None` means "this call is not modeled" — the caller keeps whatever
/// fail-closed behaviour it has for an unmodeled Clean-origin callee (the
/// compiler's absent-callee arm: result havocked, the v7/D3 note naming the
/// callee). It does NOT mean "the callee has no contract", and it must never be
/// turned into an empty summary.
///
/// `postconditions` are attached through
/// [`FunctionSummary::with_definitional_postcondition`], whose authority
/// contract the Clean-origin plan satisfies. The preconditions ride as ordinary
/// [`FunctionSummary::with_precondition`] clauses — checked at every call site
/// as an ordinary Rust obligation, never assumed, and never a `Faithful` token.
#[must_use]
pub fn clean_origin_summary(
    name: &str,
    param_names: Vec<String>,
    definitional_postconditions: Vec<Formula>,
    declared_preconditions: &[CleanOriginPrecondition],
) -> Option<FunctionSummary> {
    // The guard is rendered FIRST, on purpose. A `?` here cannot leave a
    // half-built summary behind because nothing has been built yet.
    let guards = clean_origin_declared_preconditions(declared_preconditions, &param_names)?;

    let mut summary = FunctionSummary::new(name).with_param_names(param_names);
    for guard in guards {
        summary = summary.with_precondition(guard);
    }
    for post in definitional_postconditions {
        summary = summary.with_definitional_postcondition(post);
    }
    Some(summary)
}

/// Trust: Database of function summaries for modular verification.
///
/// Stores and retrieves function summaries keyed by function name.
/// Integrates with `SpecDatabase` to record proved postconditions as
/// reusable facts for cross-function spec composition.
#[derive(Debug, Clone, Default)]
pub struct SummaryDatabase {
    summaries: FxHashMap<String, FunctionSummary>,
    /// PRIVATE (I5 cross-authority call modeling, L0 lane): callee name →
    /// precondition count for every summary that [`Self::
    /// definitional_precondition_free_subset`] REFUSED to carry into this DB
    /// *because it declares preconditions*.
    ///
    /// Only that constructor ever writes this map; `new`/`insert` leave it
    /// empty, so an ordinary DB (the L1 lane, every test DB, every producer)
    /// is byte-identical to before this field existed. It exists because
    /// dropping such a summary is fail-closed for the VALUE FACT but was
    /// fail-OPEN for its GUARD: the call site then generated no row at all and
    /// the caller could be reported CLEAN while violating the callee's
    /// precondition. A withheld name makes the call sites emit a fail-closed
    /// `UnsupportedMir` row instead (`l0_withheld_summary_vc`).
    l0_withheld_preconditioned: FxHashMap<String, usize>,
}

impl SummaryDatabase {
    /// Create an empty summary database.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert or replace a function summary.
    pub fn insert(&mut self, summary: FunctionSummary) {
        self.summaries.insert(summary.name.clone(), summary);
    }

    /// Look up a summary by function name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&FunctionSummary> {
        self.summaries.get(name)
    }

    /// Returns the number of stored summaries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.summaries.len()
    }

    /// Iterate the stored summary names (diagnostics).
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.summaries.keys().map(String::as_str)
    }

    /// Returns true when this DB carries NOTHING a caller lane must act on.
    ///
    /// A DB holding only WITHHELD names (`l0_withheld_preconditioned`) is NOT
    /// empty: its call sites still owe the fail-closed row below. Consumers
    /// use `is_empty()` as an "adds nothing to any caller VC" early-out (the
    /// compiler's VC-artifact cache key, `build_callee_write_sets`), and
    /// answering `true` there would skip generation of exactly the rows this
    /// field exists to guarantee.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.summaries.is_empty() && self.l0_withheld_preconditioned.is_empty()
    }

    /// Trust (I5, L0 lane): the number of preconditions on the summary that
    /// [`Self::definitional_precondition_free_subset`] withheld for `callee`,
    /// or `None` when nothing was withheld for that name.
    ///
    /// Read-only. There is no public writer: a forged DB cannot claim a
    /// withholding, and — more importantly — cannot clear one.
    #[must_use]
    pub fn l0_withheld_precondition_count(&self, callee: &str) -> Option<usize> {
        self.l0_withheld_preconditioned.get(callee).copied()
    }

    /// Iterate the withheld callee names (diagnostics).
    pub fn l0_withheld_names(&self) -> impl Iterator<Item = &str> {
        self.l0_withheld_preconditioned.keys().map(String::as_str)
    }

    /// Trust (I5 cross-authority call modeling): the subset of summaries that
    /// may ride a caller's L0-safety VC generation — exactly those that carry
    /// DEFINITIONAL postcondition authority
    /// (`has_reusable_postcondition_evidence`, settable only via
    /// `with_definitional_postcondition`) AND declare NO preconditions.
    ///
    /// # Why this subset exists (audit R3 #1)
    ///
    /// A contract postcondition is CONDITIONAL on its precondition, and the
    /// two travel as different VC levels: the assumed postcondition rides L0
    /// body VCs while the precondition check is an L1 `VcKind::Precondition`.
    /// An L0-only run filters the precondition VC out, so applying the general
    /// summary DB at L0 would assume the postcondition WITHOUT ever checking
    /// its precondition — a false-PROVE. A definitional, precondition-free
    /// summary has no conditional half: there is no precondition to leave
    /// unchecked, and the clause is true of every execution of the emitted
    /// callee body by construction. Both properties are enforced HERE, in the
    /// crate that owns the authority bit, so no consumer can widen the L0
    /// lane by passing a different filter.
    ///
    /// # Dropping a PRECONDITION-CARRYING definitional summary is not enough
    ///
    /// The precondition clause used to make such a summary vanish from the
    /// returned DB *silently*. Half of that is right and stays: withholding
    /// the summary withholds the VALUE FACT, and a fact that cannot travel
    /// with its guard must not travel at all. The other half was FAIL-OPEN.
    /// With no entry under the callee's name, `generate_callsite_precondition_
    /// vcs` (and its attributed twin, and `modular_vcgen`) took the
    /// `NO-SUMMARY` arm and emitted NOTHING for the call — so an L0 caller
    /// that VIOLATES the callee's precondition was reported CLEAN. Nothing
    /// downstream could see the difference between "this callee has no
    /// contract" and "this callee's contract was dropped on the floor".
    ///
    /// So the refusal is now RECORDED (`l0_withheld_preconditioned`) and the
    /// call-site producers turn each recorded name into a fail-closed
    /// `UnsupportedMir` row ([`l0_withheld_summary_vc`]) at every call to it:
    /// unknown, never proved, and carrying the v7/D3 fix (verify at
    /// `L1Functional`, where the postcondition assumption and its
    /// `VcKind::Precondition` check survive the level filter together).
    ///
    /// A summary WITHOUT definitional authority is not recorded, on purpose.
    /// Those never rode the L0 lane in the first place — an ordinary
    /// `#[requires]` is an L1 obligation checked on the L1 lane, and minting
    /// an unknown for every L0 call to a contracted callee would be plain
    /// over-rejection, not a soundness gain. The recorded set is exactly the
    /// summaries that L0 WOULD have used but for their guard.
    ///
    /// NOTE (level inversion, unresolved and deliberately not decided here):
    /// `VcKind::Precondition` is hardcoded `L1Functional` while the hazard a
    /// Clean-origin precondition would guard is `L0Safety`/UB-class (a zero
    /// divisor). Until that is settled, the honest L0 answer is "unknown",
    /// not "checked". See
    /// `reports/2026-08-20-r2-campaign-plan.md` § "FAIL-OPEN (a)/(b)".
    ///
    /// # The one preconditioned summary that DOES ride (postcondition
    /// composition, slice 2)
    ///
    /// The refusal above rests on one premise, stated in its own words: "a fact
    /// that cannot travel with its guard must not travel at all". A summary
    /// carrying `postconditions_guarded_by_own_preconditions` is the case where
    /// the fact DOES travel with its guard — the call-site lane injects it as
    /// the implication the callee proved, `pre[actuals] -> post[actuals, dest]`
    /// (see [`FunctionSummary::with_verified_callee_postcondition`]), so the
    /// value fact and its precondition are one formula and cannot be separated
    /// by a level filter. The caller derives the postcondition exactly when its
    /// own context discharges the antecedent at that call site, and derives
    /// nothing otherwise.
    ///
    /// So it is admitted rather than withheld, and — this is the part that must
    /// stay true — the ADMIT test here is the SAME predicate the EMIT side
    /// applies ([`crate::generate::summary_postconditions_ride_with_their_guard`]).
    /// Admitting a summary the injector would then refuse to guard is precisely
    /// how an unguarded preconditioned clause would reach an L0 caller, so the
    /// two sides deliberately share one function rather than two spellings of
    /// one rule. Everything else is unchanged: a preconditioned DEFINITIONAL
    /// summary (no guard bit) is still withheld and still owes its call sites
    /// the fail-closed row.
    #[must_use]
    pub fn definitional_precondition_free_subset(&self) -> SummaryDatabase {
        let mut subset = SummaryDatabase::new();
        for summary in self.summaries.values() {
            if !summary.has_reusable_postcondition_evidence() {
                continue;
            }
            if summary.preconditions.is_empty()
                || crate::generate::summary_postconditions_ride_with_their_guard(summary)
            {
                subset.insert(summary.clone());
            } else {
                subset
                    .l0_withheld_preconditioned
                    .insert(summary.name.clone(), summary.preconditions.len());
            }
        }
        subset
    }

    /// Preserve the former summary-to-fact synchronization API.
    ///
    /// Current summaries carry metadata only, so this is intentionally a no-op.
    pub fn sync_to_spec_db(&self, spec_db: &mut SpecDatabase) {
        // Preserve the API while the authority gate is closed. Iterating every
        // summary would be pure overhead: no public summary can carry the opaque,
        // replayed evidence required for authoritative export yet.
        let _ = spec_db;
    }
}

/// Trust (I5, L0 lane): the ONE spelling of the fail-closed row a call site
/// owes when its callee's definitional summary was withheld from the L0 DB
/// because it declares preconditions
/// (`SummaryDatabase::definitional_precondition_free_subset`).
///
/// `UnsupportedMir` (an `L0Safety` kind, so it SURVIVES
/// `filter_vcs_by_level(_, L0Safety)` — a `VcKind::Precondition` row would
/// not) with an always-SAT `Bool(true)` body: the exact shape the sibling
/// `SummaryArityMismatch` refusal in this same lane already uses, which
/// `preclassify_unsupported_mir_vcs` turns into `Unknown`. Unknown is the
/// honest verdict — the verifier is not claiming the precondition is
/// violated, it is refusing to claim the call site is clean while the guard
/// is unchecked.
///
/// The detail text carries the fix, per v7/D3: raising the proof level to
/// `L1Functional` keeps the postcondition assumption and its
/// `VcKind::Precondition` check together on the same side of the level
/// filter, which is exactly what makes the summary usable again.
pub(crate) fn l0_withheld_summary_vc(
    caller: &VerifiableFunction,
    callee_name: &str,
    span: &SourceSpan,
    preconditions: usize,
) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::UnsupportedMir {
            kind: "L0WithheldPreconditionedSummary".to_string(),
            detail: format!(
                "callee `{callee_name}` has a definitional summary carrying \
                 {preconditions} precondition(s), which cannot be checked at \
                 L0Safety (`VcKind::Precondition` is L1Functional and is filtered \
                 out), so neither its value fact nor its guard is applied here; \
                 options: verify this function at L1Functional or above (a \
                 contracted caller already is), or give the callee a \
                 precondition-free definitional summary"
            ),
        },
        function: caller.name.as_str().into(),
        location: span.clone(),
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    }
}

/// Trust: Result of modular VC generation for a single function.
#[derive(Debug, Clone)]
pub struct ModularVcResult {
    /// Standard safety VCs from the function body.
    pub body_vcs: Vec<VerificationCondition>,
    /// Precondition VCs: one per (call-site, precondition) pair.
    /// The caller must prove these hold at each call site.
    pub precondition_vcs: Vec<VerificationCondition>,
    /// Number of call sites where a proved callee postcondition was injected as an
    /// assumption (conjoined at the dominated successors, version-pinned to the
    /// call's post-SSA dest). Sound under the "SAT iff violation" convention because
    /// the fact is CONJOINED — never `post => vc` — and scoped by the establish-point
    /// versioning, so a stale/reassigned dest cannot false-PROVE (design 2026-06-25).
    pub assumptions_injected: usize,
    /// Number of call sites whose return values/postconditions were not modeled
    /// as caller assumptions.
    pub havoced_calls: usize,
}

/// Trust: Generate VCs for a function using modular verification.
///
/// For each call site in the function body:
/// - If the callee has a proved summary in `summaries`, generate a
///   `Precondition` VC for each precondition at the call site.
/// - Regardless of summary status, assume nothing about return values and
///   postconditions until a precise call-site model exists.
///
/// Body VCs are generated via the standard `generate_vcs` pipeline and are not
/// rewritten with callee postconditions.
#[must_use]
pub fn modular_vcgen(func: &VerifiableFunction, summaries: &SummaryDatabase) -> ModularVcResult {
    // The summary-aware lane retains the precise rebinding machinery, but its
    // authority gate is closed: public string/label metadata cannot inject a
    // postcondition. Body VCs therefore remain equivalent to the ordinary lane.
    let body_vcs = crate::generate::generate_vcs_with_summaries(func, summaries);

    // Trust: Walk call sites and build precondition VCs.
    let mut precondition_vcs = Vec::new();
    let mut assumptions_injected: usize = 0;
    let mut havoced_calls: usize = 0;

    // The body lane bails to an EMPTY guard map for over-budget functions, so NO
    // postcondition is actually injected there. Mirror that here so the reported
    // `assumptions_injected` count never claims an injection the body VCs did not
    // receive (audit R2 #5; telemetry consistency).
    let injection_active = !crate::generate::func_exceeds_vcgen_budget(func);

    for block in &func.body.blocks {
        match &block.terminator {
            Terminator::Call { func: callee_name, args, dest, target, span, .. } => {
                let summary = summaries.get(callee_name);
                // Trust (L0 withholding, fail-closed): the callee's definitional
                // summary was refused entry to this DB because it declares
                // preconditions. `summaries.get` therefore answers `None` and the
                // arms below would emit nothing at all — the fail-OPEN this row
                // closes. See `l0_withheld_summary_vc`.
                if summary.is_none()
                    && let Some(count) = summaries.l0_withheld_precondition_count(callee_name)
                {
                    precondition_vcs.push(l0_withheld_summary_vc(func, callee_name, span, count));
                }
                if let Some(summary) = summary {
                    precondition_vcs.extend(callsite_precondition_vcs(
                        func,
                        callee_name,
                        args,
                        span,
                        summary,
                    ));
                }
                if injection_active
                    && target.is_some()
                    && summary.is_some_and(|s| {
                        crate::generate::callee_postcondition_is_injectable(
                            func,
                            dest,
                            s,
                            args.len(),
                        )
                    })
                {
                    assumptions_injected += 1;
                } else {
                    havoced_calls += 1;
                }
            }
            Terminator::TailCall { func: callee_name, args, span, .. } => {
                if let Some(summary) = summaries.get(callee_name) {
                    precondition_vcs.extend(callsite_precondition_vcs(
                        func,
                        callee_name,
                        args,
                        span,
                        summary,
                    ));
                } else if let Some(count) = summaries.l0_withheld_precondition_count(callee_name) {
                    // Same withholding row as the `Call` arm — a tail call is
                    // still a call site that owes the callee's guard.
                    precondition_vcs.push(l0_withheld_summary_vc(func, callee_name, span, count));
                }
                // There is no in-function successor at which a postcondition
                // assumption could be injected; the requires rows stay public.
                havoced_calls += 1;
            }
            _ => {}
        }
    }

    ModularVcResult { body_vcs, precondition_vcs, assumptions_injected, havoced_calls }
}

/// Trust: Contract check kinds for modular verification.
///
/// Each variant represents a specific obligation generated at module boundaries
/// when verifying functions against their contracts.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ContractCheck {
    /// Caller must establish callee's precondition at the call site.
    PreConditionAtCallSite {
        /// The callee function name.
        callee: String,
        /// Index of the precondition in the callee's contract.
        precondition_index: usize,
    },
    /// Callee must establish its own postcondition before returning.
    PostConditionOnReturn {
        /// Index of the postcondition in the function's contract.
        postcondition_index: usize,
    },
    /// Frame preservation: variables not mentioned in the contract are unchanged.
    FramePreservation {
        /// The variable that must be preserved.
        variable: String,
    },
}

/// Trust: Modular verifier that generates VCs using contracts at boundaries.
///
/// Uses function summaries and contracts to generate three kinds of VCs:
/// 1. Precondition VCs at call sites (caller must prove)
/// 2. Postcondition VCs at returns (callee must prove)
/// 3. Frame preservation VCs (modified variables must be declared)
#[derive(Debug)]
pub struct ModularVerifier {
    summaries: SummaryDatabase,
}

impl ModularVerifier {
    /// Create a new modular verifier with the given summary database.
    #[must_use]
    pub fn new(summaries: SummaryDatabase) -> Self {
        Self { summaries }
    }

    /// Access the underlying summary database.
    #[must_use]
    pub fn summaries(&self) -> &SummaryDatabase {
        &self.summaries
    }

    /// Generate modular VCs for a function using contracts at boundaries.
    ///
    /// Produces VCs for:
    /// - Each precondition of each callee at each call site
    /// - Each postcondition of the function itself (must hold at return)
    /// - Frame preservation for variables not in the modifies set
    #[must_use]
    pub fn verify(&self, func: &VerifiableFunction) -> Vec<VerificationCondition> {
        generate_modular_vcs(func, &self.summaries)
    }
}

/// Generate modular verification conditions for a function.
///
/// This produces contract-boundary VCs separate from the body safety VCs:
/// 1. `PreConditionAtCallSite`: for each call to a function with a proved
///    summary, the caller must prove each precondition holds.
/// 2. `PostConditionOnReturn`: the function must prove its own postconditions
///    hold at each return point.
/// 3. `FramePreservation`: (placeholder) variables not in the modifies clause
///    must remain unchanged.
#[must_use]
pub fn generate_modular_vcs(
    func: &VerifiableFunction,
    summaries: &SummaryDatabase,
) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    // 1. Precondition checks at call sites
    for block in &func.body.blocks {
        let (callee_name, args, span) = match &block.terminator {
            Terminator::Call { func, args, span, .. }
            | Terminator::TailCall { func, args, span, .. } => (func, args, span),
            _ => continue,
        };
        if let Some(summary) = summaries.get(callee_name) {
            vcs.extend(callsite_precondition_vcs(func, callee_name, args, span, summary));
            for i in 0..summary.preconditions.len() {
                let _check = ContractCheck::PreConditionAtCallSite {
                    callee: callee_name.clone(),
                    precondition_index: i,
                };
            }
        } else if let Some(count) = summaries.l0_withheld_precondition_count(callee_name) {
            // Trust (L0 withholding, fail-closed): identical row to the one
            // `modular_vcgen` and the two `generate_callsite_precondition_vcs`
            // producers emit — every lane that reads a summary DB by name has
            // to answer the withholding the same way. See
            // `l0_withheld_summary_vc`.
            vcs.push(l0_withheld_summary_vc(func, callee_name, span, count));
        }
    }

    // 2. Postcondition checks at return points
    for (i, post) in func.postconditions.iter().enumerate() {
        if crate::contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, post) {
            vcs.push(crate::contracts::spec_unverifiable_vc(
                func,
                func.span.clone(),
                "postcondition uses unmodeled fixed-width machine arithmetic",
                &format!("{post:?}"),
                None,
            ));
            let _check = ContractCheck::PostConditionOnReturn { postcondition_index: i };
            continue;
        }
        // SOUNDNESS: a postcondition over SYNTHETIC spec-model terms
        // (`{base}_discr`/`{base}_value*`/`{base}_sign`/`.__trust_ok_i`) is
        // under-constrained here — nothing grounds those names, so `Not(post)`
        // is satisfiable by havoc regardless of the body (a minted, non-program
        // counterexample). Route it to the fail-closed NON-REFUTABLE Unknown
        // shape instead; see `contracts::spec_model_ungrounded_vc`.
        let ungrounded = crate::contracts::ungrounded_spec_model_vars(post);
        if !ungrounded.is_empty() {
            vcs.push(crate::contracts::spec_model_ungrounded_vc(
                func,
                func.span.clone(),
                &format!("{post:?}"),
                &ungrounded,
                None,
            ));
            let _check = ContractCheck::PostConditionOnReturn { postcondition_index: i };
            continue;
        }
        vcs.push(VerificationCondition {
            kind: VcKind::Postcondition,
            function: func.name.as_str().into(),
            location: func.span.clone(),
            formula: Formula::Not(Box::new(post.clone())),
            contract_metadata: None,
            obligation: None,
        });
        let _check = ContractCheck::PostConditionOnReturn { postcondition_index: i };
    }

    // Note: Contract structs carry string bodies, not parsed formulas.
    // The parsed postconditions are already in func.postconditions.

    vcs
}

fn callsite_precondition_vcs(
    caller: &VerifiableFunction,
    callee_name: &str,
    args: &[Operand],
    span: &SourceSpan,
    summary: &FunctionSummary,
) -> Vec<VerificationCondition> {
    if summary.preconditions.is_empty() {
        return Vec::new();
    }

    if summary.param_names.len() != args.len() {
        return vec![VerificationCondition {
            kind: VcKind::UnsupportedMir {
                kind: "SummaryArityMismatch".to_string(),
                detail: format!(
                    "callee `{callee_name}` summary has {} formal parameter(s), call has {} argument(s)",
                    summary.param_names.len(),
                    args.len()
                ),
            },
            function: caller.name.as_str().into(),
            location: span.clone(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        }];
    }

    let replacements: Vec<(String, Formula)> = summary
        .param_names
        .iter()
        .zip(args.iter())
        .map(|(formal, actual)| (formal.clone(), crate::operand_to_formula(caller, actual)))
        .collect();

    summary
        .preconditions
        .iter()
        .map(|pre| {
            if crate::contracts::formula_uses_unmodeled_machine_arithmetic(pre) {
                return crate::contracts::spec_unverifiable_vc(
                    caller,
                    span.clone(),
                    &format!(
                        "callee `{callee_name}` requires uses unmodeled fixed-width machine arithmetic"
                    ),
                    &format!("{pre:?}"),
                    None,
                );
            }
            VerificationCondition {
                kind: VcKind::Precondition { callee: callee_name.to_string() },
                function: caller.name.as_str().into(),
                location: span.clone(),
                // Use the SINGLE, capture-avoiding rebinding point (audit R2 #1): the
                // former modular-local `substitute_summary_params` cloned quantifier
                // binders verbatim, so a callee `requires(forall x ..., a >= x)` called
                // with a caller local named `x` for formal `a` captured the argument
                // (`forall x, x >= x` = tautology) and vacuously discharged the
                // precondition — a false-PROVE. `generate::substitute_summary_params`
                // alpha-renames colliding binders (`capture_avoiding_rebind`).
                formula: Formula::Not(Box::new(crate::generate::substitute_summary_params(
                    pre,
                    &replacements,
                ))),
                contract_metadata: None,
                obligation: None,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: build a caller that calls `parse(input)` then does `n + 1`.
    fn caller_with_arithmetic() -> VerifiableFunction {
        VerifiableFunction {
            name: "compute".to_string(),
            def_path: "test::compute".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("input".into()) },
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("n".into()) },
                    LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                ],
                blocks: vec![
                    // bb0: n = parse(input)
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            callee_identity: None,
                            is_foreign: false,
                            func: "parse".to_string(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    // bb1: _3 = CheckedAdd(n, 1)
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place::field(3, 1)),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb2: return
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::usize(),
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // ---- separate-compilation postcondition assumption (design 2026-06-25) ----

    /// `parse`'s postcondition over its result symbol `_0`: `result <= 100`.
    fn parse_post_le_100() -> Formula {
        Formula::Le(Box::new(Formula::Var("_0".into(), Sort::Int)), Box::new(Formula::Int(100)))
    }

    /// Attack fixture carrying every former reuse label but no replayable proof.
    fn labeled_parse_summary() -> FunctionSummary {
        FunctionSummary::new("parse")
            .with_param_names(vec!["input".to_string()])
            .with_postcondition(parse_post_le_100())
            .with_checked_proof_evidence("proof:parse", ProofStrength::smt_unsat())
    }

    /// True iff `f` contains BOTH a version-pinned `Var` (name has `#`) and the
    /// integer literal `n` — i.e. the rebound, establish-versioned postcondition.
    fn has_versioned_var_and_int(f: &Formula, n: i128) -> bool {
        fn walk(f: &Formula, ver: &mut bool, int: &mut bool, n: i128) {
            match f {
                Formula::Var(name, _) if name.contains('#') => *ver = true,
                Formula::Int(v) if *v == n => *int = true,
                _ => {}
            }
            for c in f.children() {
                walk(c, ver, int, n);
            }
        }
        let (mut ver, mut int) = (false, false);
        walk(f, &mut ver, &mut int, n);
        ver && int
    }

    #[test]
    fn checked_label_does_not_inject_at_post_call_block() {
        use crate::generate::{build_semantic_guard_map, build_semantic_guard_map_with_summaries};
        // bb0: n = parse(input);  bb1 (the call target): n + 1;  bb2: return.
        let caller = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();
        db.insert(labeled_parse_summary());

        // Plain guard map: the post-call block carries NO callee postcondition fact.
        let plain = build_semantic_guard_map(&caller);
        let plain_bb1 = plain.get(&BlockId(1)).cloned().unwrap_or_default();
        assert!(
            !plain_bb1.iter().any(|f| has_versioned_var_and_int(f, 100)),
            "plain map must not assume the callee postcondition: {plain_bb1:?}"
        );

        // A summary carrying the old checked/string/strength metadata is still
        // non-authoritative, so the summary-aware lane must inject nothing.
        let aware = build_semantic_guard_map_with_summaries(&caller, &db);
        let bb1 = aware.get(&BlockId(1)).cloned().unwrap_or_default();
        assert!(
            !bb1.iter().any(|f| has_versioned_var_and_int(f, 100)),
            "label-only summary must not inject a postcondition: {bb1:?}"
        );
    }

    #[test]
    fn modular_vcgen_never_counts_label_only_postcondition_assumption() {
        let caller = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();
        db.insert(labeled_parse_summary());
        let r = modular_vcgen(&caller, &db);
        assert_eq!(r.assumptions_injected, 0);
        assert_eq!(r.havoced_calls, 1);
    }

    #[test]
    fn proved_without_checked_evidence_is_not_assumed() {
        // `with_proof_evidence` preserves public metadata but cannot mint
        // reusable evidence. The postcondition must not be assumed.
        let caller = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();
        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_postcondition(parse_post_le_100())
                .with_proof_evidence("proof:parse:fake", ProofStrength::smt_unsat()),
        );
        let r = modular_vcgen(&caller, &db);
        assert_eq!(r.assumptions_injected, 0, "proved-without-evidence must not be assumed");
        assert_eq!(r.havoced_calls, 1);
    }

    #[test]
    fn verified_contract_string_is_reporting_only() {
        let caller = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();
        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_postcondition(parse_post_le_100())
                .with_verified_contract_evidence("contract:example::parse"),
        );
        let summary = db.get("parse").unwrap();
        assert_eq!(summary.proof_evidence_id.as_deref(), Some("contract:example::parse"));
        assert!(!summary.has_reusable_postcondition_evidence());
        let r = modular_vcgen(&caller, &db);
        assert_eq!(r.assumptions_injected, 0);
        assert_eq!(r.havoced_calls, 1);
    }

    #[test]
    fn dyn_summary_names_cannot_bypass_evidence_gate() {
        let caller = caller_with_arithmetic(); // a single-arg `parse(input)` call site

        // Dyn shape WITHOUT param_names (the pre-fix bug): proved + reusable
        // evidence + a `_0`-only postcondition, but empty param_names -> arity gate
        // `0 == 1` is false -> nothing is injected (inert, the safe direction).
        let mut dead = SummaryDatabase::new();
        dead.insert(
            FunctionSummary::new("parse")
                .with_postcondition(parse_post_le_100())
                .with_verified_contract_evidence("dyn-sealed:parse"),
        );
        assert!(dead.get("parse").unwrap().param_names.is_empty());
        assert_eq!(
            modular_vcgen(&caller, &dead).assumptions_injected,
            0,
            "empty param_names (the dyn deadness) must inject nothing"
        );

        // Even matching names/arity cannot turn an unbound string into proof.
        let mut live = SummaryDatabase::new();
        live.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["self".to_string()])
                .with_postcondition(parse_post_le_100())
                .with_verified_contract_evidence("dyn-sealed:parse"),
        );
        assert_eq!(
            modular_vcgen(&caller, &live).assumptions_injected,
            0,
            "matching arity must not bypass the replay-evidence gate"
        );
    }

    /// A `_stray` callee symbol that is neither `_0` nor a formal parameter.
    fn post_eq_stray() -> Formula {
        Formula::Eq(
            Box::new(Formula::Var("_0".into(), Sort::Int)),
            Box::new(Formula::Var("_stray".into(), Sort::Int)),
        )
    }

    #[test]
    fn postcondition_with_unrebindable_free_var_is_dropped() {
        // SOUNDNESS (audit F1): a postcondition free var outside {params, _0} is a
        // callee-internal symbol; left unrebound it would capture a same-named caller
        // local — a false-PROVE. It must be DROPPED, never injected.
        use crate::generate::build_semantic_guard_map_with_summaries;
        let caller = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();
        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_postcondition(post_eq_stray())
                .with_checked_proof_evidence("proof:parse", ProofStrength::smt_unsat()),
        );
        // The only clause is unrebindable -> nothing is injectable.
        let r = modular_vcgen(&caller, &db);
        assert_eq!(r.assumptions_injected, 0, "an unrebindable postcondition must not be assumed");
        // And no `_stray`-bearing fact reaches the post-call block.
        let map = build_semantic_guard_map_with_summaries(&caller, &db);
        let bb1 = map.get(&BlockId(1)).cloned().unwrap_or_default();
        assert!(
            !bb1.iter().any(|f| mentions_var(f, "_stray")),
            "the stray callee symbol must not leak into the caller: {bb1:?}"
        );
    }

    #[test]
    fn rebindable_clause_still_needs_authoritative_evidence() {
        let caller = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();
        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_postcondition(parse_post_le_100())
                .with_postcondition(post_eq_stray())
                .with_checked_proof_evidence("proof:parse", ProofStrength::smt_unsat()),
        );
        let r = modular_vcgen(&caller, &db);
        assert_eq!(r.assumptions_injected, 0);
        let map = crate::generate::build_semantic_guard_map_with_summaries(&caller, &db);
        let bb1 = map.get(&BlockId(1)).cloned().unwrap_or_default();
        assert!(!bb1.iter().any(|f| mentions_var(f, "_stray")), "stray sibling dropped: {bb1:?}");
        assert!(!bb1.iter().any(|f| has_versioned_var_and_int(f, 100)));
    }

    #[test]
    fn quantified_precondition_binder_does_not_capture_caller_arg() {
        // audit R2 #1 (CRITICAL false-PROVE): a callee precondition
        // `forall input in 0..2, p >= input` whose binder collides with the caller's
        // argument local `input` must NOT capture it. Capture would collapse the
        // body to `forall input, input >= input` (a tautology), making the
        // Precondition VC `Not(tautology)` = UNSAT = vacuously PROVED with no real
        // check. The fix routes through the capture-avoiding rebinder.
        use trust_types::Symbol;
        let caller = caller_with_arithmetic(); // bb0: _2 = parse(input)  [arg = local 1 "input"]
        let v = |n: &str| Formula::Var(n.into(), Sort::Int);
        let pre = Formula::Forall(
            vec![(Symbol::intern("input"), Sort::Int)],
            Box::new(Formula::Implies(
                Box::new(Formula::And(vec![
                    Formula::Le(Box::new(Formula::Int(0)), Box::new(v("input"))),
                    Formula::Lt(Box::new(v("input")), Box::new(Formula::Int(2))),
                ])),
                Box::new(Formula::Ge(Box::new(v("p")), Box::new(v("input")))),
            )),
        );
        let mut db = SummaryDatabase::new();
        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["p".to_string()])
                .with_precondition(pre),
        );
        let r = modular_vcgen(&caller, &db);
        let pre_vc = r
            .precondition_vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::Precondition { .. }))
            .expect("a precondition VC");
        assert!(
            pre_vc.formula.free_variables().contains("input"),
            "the caller arg `input` must survive as a FREE var (not captured): {:?}",
            pre_vc.formula
        );
    }

    #[test]
    fn quantified_postcondition_still_needs_authoritative_evidence() {
        use trust_types::Symbol;
        let caller = caller_with_arithmetic();
        let post = Formula::Forall(
            vec![(Symbol::intern("i"), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Var("_0".into(), Sort::Int)),
                Box::new(Formula::Var("i".into(), Sort::Int)),
            )),
        );
        let mut db = SummaryDatabase::new();
        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_postcondition(post)
                .with_checked_proof_evidence("proof:parse", ProofStrength::smt_unsat()),
        );
        let r = modular_vcgen(&caller, &db);
        assert_eq!(r.assumptions_injected, 0, "rebindability is not proof authority");
    }

    /// Helper: build a function with two calls — one with summary, one without.
    fn caller_two_callees() -> VerifiableFunction {
        VerifiableFunction {
            name: "process".to_string(),
            def_path: "test::process".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::usize(), name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("input".into()) },
                    LocalDecl { index: 2, ty: Ty::usize(), name: Some("parsed".into()) },
                    LocalDecl { index: 3, ty: Ty::usize(), name: Some("result".into()) },
                    LocalDecl { index: 4, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                ],
                blocks: vec![
                    // bb0: parsed = validate(input)
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            callee_identity: None,
                            is_foreign: false,
                            func: "validate".to_string(),
                            args: vec![Operand::Copy(Place::local(1))],
                            dest: Place::local(2),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    // bb1: result = unknown_fn(parsed)
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            callee_identity: None,
                            is_foreign: false,
                            func: "unknown_fn".to_string(),
                            args: vec![Operand::Copy(Place::local(2))],
                            dest: Place::local(3),
                            target: Some(BlockId(2)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    // bb2: _4 = CheckedAdd(result, 1)
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(3)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Assert {
                            unwind: UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place::field(4, 1)),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(3),
                            span: SourceSpan::default(),
                        },
                    },
                    // bb3: return
                    BasicBlock {
                        id: BlockId(3),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(4, 0))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::usize(),
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_summary_database_insert_and_get() {
        let mut db = SummaryDatabase::new();
        assert!(db.is_empty());

        let summary = FunctionSummary::new("parse")
            .with_precondition(Formula::Bool(true))
            .with_postcondition(Formula::Ge(
                Box::new(Formula::Var("result".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))
            .proved();

        db.insert(summary);
        assert_eq!(db.len(), 1);

        let found = db.get("parse").expect("should find parse");
        assert_eq!(found.name, "parse");
        assert!(found.proved);
        assert_eq!(found.preconditions.len(), 1);
        assert_eq!(found.postconditions.len(), 1);

        assert!(db.get("nonexistent").is_none());
    }

    #[test]
    fn test_modular_vcgen_no_summaries_produces_havoced_calls() {
        let func = caller_with_arithmetic();
        let db = SummaryDatabase::new();

        let result = modular_vcgen(&func, &db);

        // parse call should be havoced (no summary)
        assert_eq!(result.havoced_calls, 1);
        assert_eq!(result.assumptions_injected, 0);
        assert!(result.precondition_vcs.is_empty());
        // overflow checks now in trust-mc-lib. CheckedBinaryOp no
        // longer generates ArithmeticOverflow VCs from trust_vcgen.
        // Body VCs may be empty (no overflow VCs produced by vcgen).
        for vc in &result.body_vcs {
            assert!(
                !matches!(&vc.formula, Formula::Implies(..)),
                "without summaries, VCs should not be wrapped in Implies"
            );
        }
    }

    #[test]
    fn test_modular_vcgen_proved_summary_does_not_inject_assumptions() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        // safe-api: use the REAL lowering (`result` -> `_0`). parse's
        // postcondition `_0 >= 0` is a fact about parse's RESULT; at the call
        // site it must be rebound to the caller binding `n` (dest local 2), and
        // must NOT be left aliasing compute's OWN return local `_0` — the latter
        // is the false-PROVE closed by rebind_callee_postconditions.
        let postcond =
            Formula::Ge(Box::new(Formula::Var("_0".into(), Sort::Int)), Box::new(Formula::Int(0)));

        let summary = FunctionSummary::new("parse").with_postcondition(postcond.clone()).proved();
        db.insert(summary);

        let result = modular_vcgen(&func, &db);

        assert_eq!(result.assumptions_injected, 0);
        assert_eq!(result.havoced_calls, 1);
        assert!(result.precondition_vcs.is_empty(), "no preconditions on parse");

        // Proved callee postconditions are stored as evidence but are not
        // injected as global premises into caller body VCs.
        for vc in &result.body_vcs {
            assert!(
                !matches!(&vc.formula, Formula::Implies(premise, _) if **premise == postcond),
                "body VCs must not be wrapped with callee postconditions"
            );
        }
    }

    #[test]
    fn test_modular_vcgen_generates_precondition_vcs() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        let precond = Formula::Ge(
            Box::new(Formula::Var("input".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let postcond = Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );

        let summary = FunctionSummary::new("parse")
            .with_param_names(vec!["input".to_string()])
            .with_precondition(precond.clone())
            .with_postcondition(postcond)
            .proved();
        db.insert(summary);

        let result = modular_vcgen(&func, &db);

        // Should generate 1 precondition VC for parse's precondition
        assert_eq!(result.precondition_vcs.len(), 1, "should generate one precondition VC");
        let pre_vc = &result.precondition_vcs[0];
        assert!(
            matches!(&pre_vc.kind, VcKind::Precondition { callee } if callee == "parse"),
            "precondition VC should reference parse"
        );
        assert_eq!(pre_vc.function, "compute", "VC should be in caller's context");
        // Formula is Not(precondition) — solver checks if negation is satisfiable
        assert!(
            matches!(&pre_vc.formula, Formula::Not(inner) if **inner == precond),
            "precondition VC formula should be Not(precondition)"
        );
    }

    #[test]
    fn test_modular_vcgen_unproved_summary_is_havoced() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        // Insert unproved summary — should be treated as havoc
        let summary = FunctionSummary::new("parse").with_postcondition(Formula::Bool(true));
        // Note: not calling .proved()
        db.insert(summary);

        let result = modular_vcgen(&func, &db);

        assert_eq!(result.havoced_calls, 1, "unproved summary should be havoced");
        assert_eq!(result.assumptions_injected, 0);
        assert!(result.precondition_vcs.is_empty());
    }

    /// True if `name` appears as a Var/SymVar anywhere in `f`.
    fn mentions_var(f: &Formula, name: &str) -> bool {
        let mut found = false;
        f.visit(&mut |sub| {
            if sub.var_name() == Some(name) {
                found = true;
            }
        });
        found
    }

    // safe-api: callee postconditions must be REBOUND at the call site
    // (formals -> actual args, callee result `_0` -> caller destination), not
    // injected verbatim. Verbatim injection aliases the caller's own `_0` (a
    // false-PROVE) and never reaches the caller binding. These exercise
    // `rebind_callee_postconditions` directly so they are independent of which
    // body VCs the active pipeline emits.
    #[test]
    fn rebind_maps_result_to_dest_and_formals_to_actuals() {
        use crate::generate::rebind_callee_postconditions;
        // compute: local 0 unnamed ("_0" = its own return), local 1 = "input",
        // local 2 = "n" (the destination of `n = parse(input)`).
        let func = caller_with_arithmetic();
        let args = vec![Operand::Copy(Place::local(1))];
        let dest = Place::local(2);
        let summary = FunctionSummary::new("parse")
            .with_param_names(vec!["p0".into()])
            // `result > 0`
            .with_postcondition(Formula::Gt(
                Box::new(Formula::Var("_0".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))
            // `result == p0` (exercises result->dest AND formal->actual together)
            .with_postcondition(Formula::Eq(
                Box::new(Formula::Var("_0".into(), Sort::Int)),
                Box::new(Formula::Var("p0".into(), Sort::Int)),
            ))
            .proved();

        let rebound = rebind_callee_postconditions(&func, &args, &dest, &summary);
        assert_eq!(rebound.len(), 2);

        // `_0` -> dest `n`, and crucially the caller's own `_0` does NOT survive.
        assert!(matches!(&rebound[0], Formula::Gt(l, _) if l.var_name() == Some("n")));
        assert!(!mentions_var(&rebound[0], "_0"), "false-PROVE: caller `_0` must not survive");

        // `_0` -> `n` AND formal `p0` -> actual arg local 1 ("input").
        assert!(matches!(&rebound[1], Formula::Eq(l, r)
                if l.var_name() == Some("n") && r.var_name() == Some("input")));
        assert!(!mentions_var(&rebound[1], "p0"), "formal must be rebound to the actual");
        assert!(!mentions_var(&rebound[1], "_0"), "false-PROVE: caller `_0` must not survive");
    }

    #[test]
    fn rebind_tail_call_identity_is_correct_not_a_bug() {
        use crate::generate::rebind_callee_postconditions;
        // `return f(x)` lowers the call dest to the caller's OWN return local 0.
        // Then the callee result genuinely IS the caller return, so `_0` -> `_0`
        // is the correct identity — a surviving `_0` here is NOT the bug.
        let func = caller_with_arithmetic();
        let args = vec![Operand::Copy(Place::local(1))];
        let dest = Place::local(0);
        let summary = FunctionSummary::new("parse")
            .with_postcondition(Formula::Gt(
                Box::new(Formula::Var("_0".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))
            .proved();
        let rebound = rebind_callee_postconditions(&func, &args, &dest, &summary);
        assert!(
            matches!(&rebound[0], Formula::Gt(l, _) if l.var_name() == Some("_0")),
            "tail-call dest = caller return: `_0` -> `_0` is the correct identity"
        );
    }

    #[test]
    fn rebind_distinct_dests_are_not_last_write_wins() {
        use crate::generate::rebind_callee_postconditions;
        // process: local 2 = "parsed", local 3 has the source debug name
        // "result". `result` is reserved by the contract surface for the return
        // place, so the distinct ordinary local must use its injective fallback
        // `_3` rather than aliasing `_0` through a source-level spelling.
        let func = caller_two_callees();
        let args = vec![Operand::Copy(Place::local(1))];
        let summary = FunctionSummary::new("validate")
            .with_postcondition(Formula::Gt(
                Box::new(Formula::Var("_0".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))
            .proved();
        let r2 = rebind_callee_postconditions(&func, &args, &Place::local(2), &summary);
        let r3 = rebind_callee_postconditions(&func, &args, &Place::local(3), &summary);
        assert!(matches!(&r2[0], Formula::Gt(l, _) if l.var_name() == Some("parsed")));
        assert!(matches!(&r3[0], Formula::Gt(l, _) if l.var_name() == Some("_3")));
    }

    #[test]
    fn rebind_projected_dest_binds_to_dest_not_caller_return() {
        use crate::generate::rebind_callee_postconditions;
        // Whole-`_0` postcondition with a projected destination must bind to the
        // projected dest place, never silently to an unrelated caller local
        // (above all, not the caller's own return `_0`).
        let func = caller_with_arithmetic();
        let args = vec![Operand::Copy(Place::local(1))];
        let dest = Place::field(3, 0);
        let summary = FunctionSummary::new("parse")
            .with_postcondition(Formula::Gt(
                Box::new(Formula::Var("_0".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))
            .proved();
        let rebound = rebind_callee_postconditions(&func, &args, &dest, &summary);
        assert!(
            !mentions_var(&rebound[0], "_0"),
            "projected dest must not leave the postcondition aliasing the caller return `_0`"
        );
    }

    #[test]
    fn test_modular_vcgen_mixed_proved_and_unknown() {
        let func = caller_two_callees();
        let mut db = SummaryDatabase::new();

        let postcond =
            Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100)));

        // validate has a proved summary; unknown_fn does not
        let summary =
            FunctionSummary::new("validate").with_postcondition(postcond.clone()).proved();
        db.insert(summary);

        let result = modular_vcgen(&func, &db);

        assert_eq!(result.assumptions_injected, 0);
        assert_eq!(result.havoced_calls, 2, "both calls leave return postconditions unmodeled");
        assert!(result.precondition_vcs.is_empty(), "validate has no preconditions");

        for vc in &result.body_vcs {
            assert!(
                !matches!(&vc.formula, Formula::Implies(premise, _) if **premise == postcond),
                "body VCs must not assume validate's postcondition"
            );
        }
    }

    #[test]
    fn test_summary_sync_is_inert_without_replayable_evidence() {
        let mut db = SummaryDatabase::new();
        let postcond =
            Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0)));

        // Even the old test-only "checked" label is just constructible metadata.
        db.insert(
            FunctionSummary::new("parse")
                .with_postcondition(postcond.clone())
                .with_checked_proof_evidence(
                    "proof:parse:postcondition",
                    ProofStrength::smt_unsat(),
                ),
        );

        // Unproved summary does NOT sync
        db.insert(FunctionSummary::new("unsafe_parse").with_postcondition(Formula::Bool(true)));

        let mut spec_db = SpecDatabase::new();
        db.sync_to_spec_db(&mut spec_db);

        assert_eq!(spec_db.len(), 0);
        let facts = spec_db.postconditions_for("parse");
        assert!(facts.is_empty());
    }

    #[test]
    fn test_summary_sync_rejects_proved_boolean_without_evidence() {
        let mut db = SummaryDatabase::new();
        db.insert(FunctionSummary::new("parse").with_postcondition(Formula::Bool(true)).proved());

        let mut spec_db = SpecDatabase::new();
        db.sync_to_spec_db(&mut spec_db);

        assert_eq!(spec_db.len(), 0, "plain proved flag is not reusable proof evidence");
    }

    #[test]
    fn test_summary_sync_rejects_public_fake_evidence() {
        let mut db = SummaryDatabase::new();
        db.insert(
            FunctionSummary::new("parse")
                .with_postcondition(Formula::Bool(true))
                .with_proof_evidence("proof:parse:fake", ProofStrength::smt_unsat()),
        );

        let mut spec_db = SpecDatabase::new();
        db.sync_to_spec_db(&mut spec_db);

        assert_eq!(spec_db.len(), 0, "public evidence strings are not reusable proof evidence");
    }

    #[test]
    fn test_caller_callee_verification_chain() {
        // Scenario: parse() has proved summary with postcondition n >= 0.
        // compute() calls parse() then does n + 1.
        // overflow checks now in trust-mc-lib, so body_vcs may be empty.
        // We verify the modular infrastructure (no assumption injection, spec sync).

        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        let postcond =
            Formula::Ge(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0)));

        db.insert(
            FunctionSummary::new("parse")
                .with_postcondition(postcond.clone())
                .with_checked_proof_evidence("proof:parse:chain", ProofStrength::smt_unsat()),
        );

        let result = modular_vcgen(&func, &db);

        // Step 1: postcondition facts are not injected as caller assumptions.
        assert_eq!(result.assumptions_injected, 0);
        assert_eq!(result.havoced_calls, 1);

        // Step 2: if any body VCs exist, they must not be strengthened with
        // callee postconditions as global premises.
        for vc in &result.body_vcs {
            assert!(
                !matches!(&vc.formula, Formula::Implies(premise, _) if **premise == postcond),
                "callee postcondition must not be a global premise"
            );
        }

        // Step 3: both authority consumers remain closed.
        let mut spec_db = SpecDatabase::new();
        db.sync_to_spec_db(&mut spec_db);
        let spec_facts = spec_db.postconditions_for("parse");
        assert!(spec_facts.is_empty());
    }

    #[test]
    fn extracted_body_is_inert_analysis_metadata() {
        // W3/F6b: attaching an extracted body is an ANALYSIS INPUT — it must
        // not flip any authority bit (proved / reusable evidence), and it
        // defaults to absent so every non-verifier producer stays fail-closed.
        let summary = FunctionSummary::new("f");
        assert!(summary.extracted_body.is_none(), "default: no body attached");
        let summary = summary.with_extracted_body(std::sync::Arc::new(caller_with_arithmetic()));
        assert!(summary.extracted_body.is_some());
        assert!(!summary.proved, "an extracted body must not mint proof status");
        assert!(!summary.has_reusable_postcondition_evidence());
    }

    #[test]
    fn test_function_summary_builder_pattern() {
        let summary = FunctionSummary::new("f")
            .with_precondition(Formula::Bool(true))
            .with_precondition(Formula::Bool(false))
            .with_postcondition(Formula::Int(42))
            .proved();

        assert_eq!(summary.name, "f");
        assert_eq!(summary.preconditions.len(), 2);
        assert_eq!(summary.postconditions.len(), 1);
        assert!(summary.proved);
    }

    #[test]
    fn test_modular_vcgen_empty_function() {
        let func = VerifiableFunction {
            name: "empty".to_string(),
            def_path: "test::empty".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let db = SummaryDatabase::new();
        let result = modular_vcgen(&func, &db);

        assert!(result.body_vcs.is_empty());
        assert!(result.precondition_vcs.is_empty());
        assert_eq!(result.assumptions_injected, 0);
        assert_eq!(result.havoced_calls, 0);
    }

    #[test]
    fn test_modular_vcgen_multiple_preconditions() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        let pre1 = Formula::Ge(
            Box::new(Formula::Var("input".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let pre2 = Formula::Le(
            Box::new(Formula::Var("input".into(), Sort::Int)),
            Box::new(Formula::Int(1000)),
        );

        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_precondition(pre1.clone())
                .with_precondition(pre2.clone())
                .with_postcondition(Formula::Bool(true))
                .proved(),
        );

        let result = modular_vcgen(&func, &db);

        // Should generate 2 precondition VCs — one per precondition
        assert_eq!(result.precondition_vcs.len(), 2);
        assert!(matches!(
            &result.precondition_vcs[0].formula,
            Formula::Not(inner) if **inner == pre1
        ));
        assert!(matches!(
            &result.precondition_vcs[1].formula,
            Formula::Not(inner) if **inner == pre2
        ));
    }

    // --- Tests for ContractCheck, ModularVerifier, generate_modular_vcs ---

    #[test]
    fn test_contract_check_enum_variants() {
        let pre = ContractCheck::PreConditionAtCallSite {
            callee: "parse".to_string(),
            precondition_index: 0,
        };
        let post = ContractCheck::PostConditionOnReturn { postcondition_index: 1 };
        let frame = ContractCheck::FramePreservation { variable: "state".to_string() };

        assert_eq!(pre, pre.clone());
        assert_eq!(post, post.clone());
        assert_eq!(frame, frame.clone());
        // Ensure they're distinct
        assert_ne!(
            ContractCheck::PreConditionAtCallSite { callee: "a".into(), precondition_index: 0 },
            ContractCheck::PreConditionAtCallSite { callee: "b".into(), precondition_index: 0 },
        );
    }

    #[test]
    fn test_generate_modular_vcs_precondition_at_call_site() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        let precond = Formula::Ge(
            Box::new(Formula::Var("input".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );

        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_precondition(precond.clone())
                .proved(),
        );

        let vcs = generate_modular_vcs(&func, &db);

        assert_eq!(vcs.len(), 1, "should generate 1 precondition VC");
        assert!(matches!(
            &vcs[0].kind,
            VcKind::Precondition { callee } if callee == "parse"
        ));
        assert!(matches!(
            &vcs[0].formula,
            Formula::Not(inner) if **inner == precond
        ));
    }

    #[test]
    fn test_generate_modular_vcs_postcondition_on_return() {
        let postcond = Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );

        let func = VerifiableFunction {
            name: "producer".to_string(),
            def_path: "test::producer".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::usize(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::usize(),
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![postcond.clone()],
            spec: Default::default(),
        };

        let db = SummaryDatabase::new();
        let vcs = generate_modular_vcs(&func, &db);

        assert_eq!(vcs.len(), 1, "should generate 1 postcondition VC");
        assert!(matches!(&vcs[0].kind, VcKind::Postcondition));
        assert!(matches!(
            &vcs[0].formula,
            Formula::Not(inner) if **inner == postcond
        ));
        assert_eq!(vcs[0].function, "producer");
    }

    #[test]
    fn modular_ungrounded_spec_model_postcondition_is_unknown_not_refutable() {
        // A parsed ensures over SYNTHETIC spec-model terms (here the Result
        // model of ny-cert `check_farkas`: `is_ok ∧ payload_sign > 0`, negated)
        // is under-constrained in this lane — nothing grounds `_0__discr` /
        // `_0__value__sign` — so the old `Not(post)` VC was satisfiable by havoc
        // (Failed with a minted, non-program counterexample). It must emit the
        // fail-closed NON-REFUTABLE Unknown shape instead, and never vanish.
        let is_ok = Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Var("_0__discr".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )));
        let sign_pos = Formula::Gt(
            Box::new(Formula::Var("_0__value__sign".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let postcond = Formula::Not(Box::new(Formula::And(vec![is_ok, sign_pos])));

        let func = VerifiableFunction {
            name: "check_farkas".to_string(),
            def_path: "test::check_farkas".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::usize(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::usize(),
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![postcond],
            spec: Default::default(),
        };

        let db = SummaryDatabase::new();
        let vcs = generate_modular_vcs(&func, &db);

        assert_eq!(vcs.len(), 1, "the obligation must not vanish: {vcs:#?}");
        assert!(
            matches!(&vcs[0].kind, VcKind::UnsupportedMir { kind, .. }
                if kind == crate::contracts::SPEC_MODEL_UNGROUNDED_KIND),
            "ungrounded postcondition must be the fail-closed Unknown shape: {:?}",
            vcs[0].kind
        );
        assert!(
            !vcs.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)),
            "no refutable Postcondition VC may be minted: {vcs:#?}"
        );
    }

    #[test]
    fn test_generate_modular_vcs_postcondition_from_field() {
        let postcond =
            Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100)));

        let func = VerifiableFunction {
            name: "bounded".to_string(),
            def_path: "test::bounded".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![],
                blocks: vec![],
                arg_count: 0,
                return_ty: Ty::usize(),
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![postcond.clone()],
            spec: Default::default(),
        };

        let db = SummaryDatabase::new();
        let vcs = generate_modular_vcs(&func, &db);

        assert_eq!(vcs.len(), 1, "postcondition should generate 1 VC");
        assert!(matches!(&vcs[0].kind, VcKind::Postcondition));
    }

    #[test]
    fn test_generate_modular_vcs_no_contracts_no_vcs() {
        let func = VerifiableFunction {
            name: "plain".to_string(),
            def_path: "test::plain".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![],
                blocks: vec![],
                arg_count: 0,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let db = SummaryDatabase::new();
        let vcs = generate_modular_vcs(&func, &db);
        assert!(vcs.is_empty(), "no contracts -> no modular VCs");
    }

    #[test]
    fn test_modular_verifier_delegates_to_generate() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        let precond = Formula::Bool(true);
        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_precondition(precond)
                .proved(),
        );

        let verifier = ModularVerifier::new(db);
        let vcs = verifier.verify(&func);

        assert_eq!(vcs.len(), 1);
        assert_eq!(verifier.summaries().len(), 1);
    }

    #[test]
    fn test_generate_modular_vcs_unproved_preconditions_are_enforced() {
        let func = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();

        db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_precondition(Formula::Bool(true)),
        );

        let vcs = generate_modular_vcs(&func, &db);
        assert_eq!(vcs.len(), 1, "declared callee preconditions are caller obligations");
        assert!(matches!(&vcs[0].kind, VcKind::Precondition { callee } if callee == "parse"));
    }

    // ---- I5 cross-authority call modeling: the DEFINITIONAL postcondition lane ----

    /// The Clean-origin producer's shape: `parse`'s summary carrying
    /// `result <= 100` as a DEFINITIONAL clause (as if the producer had itself
    /// emitted `parse`'s body and derived the clause from the emission plan).
    fn definitional_parse_summary() -> FunctionSummary {
        FunctionSummary::new("parse")
            .with_param_names(vec!["input".to_string()])
            .with_definitional_postcondition(parse_post_le_100())
    }

    #[test]
    fn definitional_postcondition_carries_reusable_evidence() {
        assert!(definitional_parse_summary().has_reusable_postcondition_evidence());
        // The plain builder still never does (unchanged authority boundary).
        let plain = FunctionSummary::new("parse")
            .with_param_names(vec!["input".to_string()])
            .with_postcondition(parse_post_le_100());
        assert!(!plain.has_reusable_postcondition_evidence());
        // Empty postconditions never carry evidence, whatever the flag history.
        assert!(!FunctionSummary::new("parse").has_reusable_postcondition_evidence());
    }

    #[test]
    fn mixed_provenance_kills_definitional_authority_in_both_orders() {
        let definitional_then_plain = FunctionSummary::new("parse")
            .with_definitional_postcondition(parse_post_le_100())
            .with_postcondition(post_eq_stray());
        assert!(
            !definitional_then_plain.has_reusable_postcondition_evidence(),
            "a plain clause after a definitional one must strip the authority"
        );
        let plain_then_definitional = FunctionSummary::new("parse")
            .with_postcondition(post_eq_stray())
            .with_definitional_postcondition(parse_post_le_100());
        assert!(
            !plain_then_definitional.has_reusable_postcondition_evidence(),
            "a definitional clause must not launder an earlier plain claim"
        );
    }

    #[test]
    fn definitional_postcondition_injects_at_post_call_block() {
        use crate::generate::build_semantic_guard_map_with_summaries;
        let caller = caller_with_arithmetic();
        let mut db = SummaryDatabase::new();
        db.insert(definitional_parse_summary());

        let r = modular_vcgen(&caller, &db);
        assert_eq!(r.assumptions_injected, 1, "the definitional clause must be assumed");
        assert_eq!(r.havoced_calls, 0);

        let map = build_semantic_guard_map_with_summaries(&caller, &db);
        let bb1 = map.get(&BlockId(1)).cloned().unwrap_or_default();
        assert!(
            bb1.iter().any(|f| has_versioned_var_and_int(f, 100)),
            "the rebound, version-pinned fact must reach the post-call block: {bb1:?}"
        );
    }

    /// Two-arg caller mirroring the Clean-origin fixture: `v = pick(41, 7)`.
    fn caller_of_pick_consts() -> VerifiableFunction {
        VerifiableFunction {
            name: "caller".to_string(),
            def_path: "test::caller".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::usize(), name: Some("v".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            callee_identity: None,
                            is_foreign: false,
                            func: "pick".to_string(),
                            args: vec![
                                Operand::Constant(ConstValue::Uint(41, 64)),
                                Operand::Constant(ConstValue::Uint(7, 64)),
                            ],
                            dest: Place::local(1),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn definitional_projection_pins_dest_to_projected_argument() {
        // The exact Clean-origin Projection summary shape: `_0 == a0` for
        // `pick(a0, a1)`, called as `pick(41, 7)`. The injected fact must PIN
        // the dest to 41 (an Eq — refutable by a wrong caller claim), and must
        // not mention the non-projected argument.
        use crate::generate::build_semantic_guard_map_with_summaries;
        let caller = caller_of_pick_consts();
        let post = Formula::Eq(
            Box::new(Formula::var("_0", Sort::Int)),
            Box::new(Formula::var("a0", Sort::Int)),
        );
        let mut db = SummaryDatabase::new();
        db.insert(
            FunctionSummary::new("pick")
                .with_param_names(vec!["a0".to_string(), "a1".to_string()])
                .with_definitional_postcondition(post),
        );

        let r = modular_vcgen(&caller, &db);
        assert_eq!(r.assumptions_injected, 1);

        let map = build_semantic_guard_map_with_summaries(&caller, &db);
        let bb1 = map.get(&BlockId(1)).cloned().unwrap_or_default();
        let pinned = bb1
            .iter()
            .find(|f| has_versioned_var_and_int(f, 41))
            .unwrap_or_else(|| panic!("expected a version-pinned `dest == 41` fact: {bb1:?}"));
        assert!(
            matches!(pinned, Formula::Eq(..)),
            "the projection fact must be an EQUALITY (it must refute a wrong \
             caller claim, not merely bless a right one): {pinned:?}"
        );
        fn mentions_int(f: &Formula, n: i128) -> bool {
            let mut found = false;
            fn walk(f: &Formula, n: i128, found: &mut bool) {
                if matches!(f, Formula::Int(v) if *v == n) {
                    *found = true;
                }
                for c in f.children() {
                    walk(c, n, found);
                }
            }
            walk(f, n, &mut found);
            found
        }
        assert!(
            !bb1.iter().any(|f| mentions_int(f, 7)),
            "the non-projected argument must not leak into any fact: {bb1:?}"
        );
        // The synthetic formal names must be substituted away entirely.
        assert!(
            !bb1.iter().any(|f| mentions_var(f, "a0") || mentions_var(f, "a1")),
            "callee formals must not survive rebinding: {bb1:?}"
        );
    }

    #[test]
    fn definitional_authority_still_respects_arity_and_rebindability_gates() {
        // Definitional authority opens ONLY the evidence gate; every other
        // soundness gate of `callee_postcondition_is_injectable` must still
        // hold. Wrong arity: inject nothing.
        let caller = caller_with_arithmetic(); // single-argument `parse(input)` call
        let mut arity_db = SummaryDatabase::new();
        arity_db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["a".to_string(), "b".to_string()])
                .with_definitional_postcondition(parse_post_le_100()),
        );
        let r = modular_vcgen(&caller, &arity_db);
        assert_eq!(r.assumptions_injected, 0, "arity mismatch must fail closed");
        assert_eq!(r.havoced_calls, 1);

        // A definitional clause whose free var is neither `_0` nor a formal:
        // unrebindable, inject nothing.
        let mut stray_db = SummaryDatabase::new();
        stray_db.insert(
            FunctionSummary::new("parse")
                .with_param_names(vec!["input".to_string()])
                .with_definitional_postcondition(post_eq_stray()),
        );
        let r = modular_vcgen(&caller, &stray_db);
        assert_eq!(r.assumptions_injected, 0, "unrebindable clause must fail closed");
        assert_eq!(r.havoced_calls, 1);
    }

    #[test]
    fn l0_subset_keeps_only_definitional_precondition_free_summaries() {
        let pre = Formula::Ge(Box::new(Formula::var("p", Sort::Int)), Box::new(Formula::Int(0)));
        let mut db = SummaryDatabase::new();
        // Kept: definitional, no preconditions.
        db.insert(definitional_parse_summary());
        // Dropped: plain contract postcondition (no definitional authority).
        db.insert(
            FunctionSummary::new("contracted")
                .with_param_names(vec!["p".to_string()])
                .with_postcondition(parse_post_le_100()),
        );
        // Dropped: definitional clause BUT carries a precondition — at L0 the
        // precondition VC would be filtered out, so the summary must not ride
        // (audit R3 #1).
        db.insert(
            FunctionSummary::new("conditional")
                .with_param_names(vec!["p".to_string()])
                .with_precondition(pre)
                .with_definitional_postcondition(parse_post_le_100()),
        );
        let subset = db.definitional_precondition_free_subset();
        assert_eq!(subset.len(), 1);
        assert!(subset.get("parse").is_some());
        assert!(subset.get("contracted").is_none());
        assert!(subset.get("conditional").is_none());
    }

    // ---- I5 cross-authority call modeling: the WrappingBinOp summary lane ----

    fn wrapping_formals() -> Vec<String> {
        vec!["a0".to_string(), "a1".to_string()]
    }

    #[test]
    fn wrapping_postconditions_constructor_boundaries() {
        use trust_types::admissible_body::{ArithBinOp, ArithOperand};
        let names = wrapping_formals();
        let pp = (ArithOperand::Param(0), ArithOperand::Param(1));

        // The recorded Mul boundary: the extractor's Int/LIA lane has no
        // nonlinear-mod encoding, so the summary lane must inject NOTHING.
        assert!(
            clean_origin_wrapping_binop_postconditions(ArithBinOp::Mul, pp.0, pp.1, 64, &names)
                .is_none(),
            "wrapping_mul has no faithful encoding in this lane — inject nothing"
        );
        // Width outside 1..=64 (the extractor's own modulus cap).
        for width in [0u32, 65, 128] {
            assert!(
                clean_origin_wrapping_binop_postconditions(
                    ArithBinOp::Add,
                    pp.0,
                    pp.1,
                    width,
                    &names,
                )
                .is_none(),
                "width {width} must be refused"
            );
        }
        // Operand validation: parameter index out of arity; numeral out of the
        // carrier range (the planner guarantees neither; refuse, don't trust).
        assert!(
            clean_origin_wrapping_binop_postconditions(
                ArithBinOp::Add,
                ArithOperand::Param(2),
                pp.1,
                64,
                &names,
            )
            .is_none()
        );
        assert!(
            clean_origin_wrapping_binop_postconditions(
                ArithBinOp::Add,
                pp.0,
                ArithOperand::Const(256),
                8,
                &names,
            )
            .is_none()
        );
        // In-range instances produce the def + one range fact per operand.
        for (op, right) in [
            (ArithBinOp::Add, ArithOperand::Param(1)),
            (ArithBinOp::Sub, ArithOperand::Param(1)),
            (ArithBinOp::Add, ArithOperand::Const(255)),
        ] {
            let posts = clean_origin_wrapping_binop_postconditions(op, pp.0, right, 8, &names)
                .expect("valid add/sub instances must be expressible");
            assert_eq!(posts.len(), 3, "def + two operand range facts");
            assert!(matches!(&posts[0], Formula::Eq(lhs, _)
                if matches!(lhs.as_ref(), Formula::Var(n, Sort::Int) if n == "_0")));
        }
    }

    /// Two-arg caller mirroring the Clean-origin wrapping fixture:
    /// `s = wsum(u64::MAX, 1)` at `u64`.
    fn caller_of_wsum_consts() -> VerifiableFunction {
        VerifiableFunction {
            name: "caller".to_string(),
            def_path: "test::caller".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u64(), name: Some("s".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            unwind: UnwindEdge::Unreachable,
                            is_unsafe_sig: false,
                            callee_identity: None,
                            is_foreign: false,
                            func: "wsum".to_string(),
                            args: vec![
                                Operand::Constant(ConstValue::Uint(u64::MAX as u128, 64)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ],
                            dest: Place::local(1),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 0,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn definitional_wrapping_summary_pins_dest_to_the_modular_ite() {
        // The exact Clean-origin WrappingBinOp summary shape for
        // `wsum(a0, a1) := a0 + a1` at UInt64, called as `wsum(u64::MAX, 1)`.
        // The injected fact must pin the dest to the MODULAR-Ite value (which
        // grounds to 0 — the wrapped result), never to the unbounded `a0 + a1`
        // (which would ground to 2^64 and REFUTE a correct `assert!(s == 0)`).
        use trust_types::admissible_body::{ArithBinOp, ArithOperand};

        use crate::generate::build_semantic_guard_map_with_summaries;
        let caller = caller_of_wsum_consts();
        let posts = clean_origin_wrapping_binop_postconditions(
            ArithBinOp::Add,
            ArithOperand::Param(0),
            ArithOperand::Param(1),
            64,
            &wrapping_formals(),
        )
        .expect("u64 wrapping add over two params must be expressible");
        let mut summary = FunctionSummary::new("wsum").with_param_names(wrapping_formals());
        for post in posts {
            summary = summary.with_definitional_postcondition(post);
        }
        let mut db = SummaryDatabase::new();
        db.insert(summary);

        // The summary must ride the L0 lane: definitional, precondition-free.
        assert!(
            db.definitional_precondition_free_subset().get("wsum").is_some(),
            "the wrapping summary must survive the L0 definitional subset"
        );

        let r = modular_vcgen(&caller, &db);
        assert_eq!(r.assumptions_injected, 1, "the definitional clauses must be assumed");
        assert_eq!(r.havoced_calls, 0);

        // The version-pinned fact at the post-call block must be the EXACT
        // modular reduction over the substituted actuals.
        let max = u64::MAX as i128;
        let s = || Box::new(Formula::Add(Box::new(Formula::Int(max)), Box::new(Formula::Int(1))));
        let m = || Box::new(Formula::Int(1i128 << 64));
        let expected_rhs =
            Formula::Ite(Box::new(Formula::Ge(s(), m())), Box::new(Formula::Sub(s(), m())), s());
        let map = build_semantic_guard_map_with_summaries(&caller, &db);
        let bb1 = map.get(&BlockId(1)).cloned().unwrap_or_default();
        assert!(
            bb1.iter().any(|f| matches!(f, Formula::Eq(lhs, rhs)
                if matches!(lhs.as_ref(), Formula::Var(n, _) if n.contains('#'))
                    && rhs.as_ref() == &expected_rhs)),
            "expected a version-pinned `dest == ite((MAX+1) >= 2^64, ..)` fact: {bb1:?}"
        );
        // The anti-blessing control: no fact may pin the dest to the UNBOUNDED
        // sum — that encoding would refute the correct wrapped-value claim.
        assert!(
            !bb1.iter().any(|f| matches!(f, Formula::Eq(_, rhs)
                if matches!(rhs.as_ref(), Formula::Add(..)))),
            "the unbounded `a0 + a1` encoding must never be injected: {bb1:?}"
        );
        // The synthetic formals must be substituted away entirely.
        assert!(
            !bb1.iter().any(|f| mentions_var(f, "a0") || mentions_var(f, "a1")),
            "callee formals must not survive rebinding: {bb1:?}"
        );
    }
}
