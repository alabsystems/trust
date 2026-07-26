// trust_vcgen/abstract_interp/discharge.rs: VC discharge via abstract interpretation,
// formula augmentation with abstract state, and VC-kind-specific helpers
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use super::arithmetic::*;
use super::{Interval, IntervalDomain};

// ── VC Discharge Pre-Pass ───────────────────────────────────────────────────
//
// Uses abstract interpretation to cheaply discharge easy VCs before hitting
// an SMT/CHC solver. If interval analysis proves a VC holds for all possible
// values, we return Proved without invoking a solver. This is sound because
// interval abstraction is an over-approximation: if the property holds for
// the abstract interval, it holds for every concrete value in that interval.

/// Result of attempting to discharge a VC via abstract interpretation.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum AbstractInterpResult {
    /// The VC was discharged (proved) by abstract interpretation alone.
    Discharged(VerificationResult),
    /// Abstract interpretation could not determine the result; send to solver.
    Undetermined,
}

impl AbstractInterpResult {
    /// Whether the VC was successfully discharged.
    #[must_use]
    pub fn is_discharged(&self) -> bool {
        matches!(self, AbstractInterpResult::Discharged(_))
    }
}

/// Evaluate a `Formula` to an `Interval` under the given variable environment.
///
/// This is a recursive abstract evaluator: it maps formula sub-expressions to
/// intervals by composing the interval arithmetic operations. Variables not in
/// `env` are mapped to Top (all values possible).
#[must_use]
pub fn abstract_eval_formula(formula: &Formula, env: &IntervalDomain) -> Interval {
    match formula {
        Formula::Int(n) => Interval::constant(*n),
        Formula::UInt(n) => {
            if let Ok(v) = i128::try_from(*n) {
                Interval::constant(v)
            } else {
                Interval::TOP
            }
        }
        Formula::Var(name, _) => env.get(name),
        Formula::Add(a, b) => {
            interval_add(&abstract_eval_formula(a, env), &abstract_eval_formula(b, env))
        }
        Formula::Sub(a, b) => {
            interval_sub(&abstract_eval_formula(a, env), &abstract_eval_formula(b, env))
        }
        Formula::Mul(a, b) => {
            interval_mul(&abstract_eval_formula(a, env), &abstract_eval_formula(b, env))
        }
        Formula::Div(a, b) => {
            interval_div(&abstract_eval_formula(a, env), &abstract_eval_formula(b, env))
        }
        Formula::Rem(a, b) => {
            interval_rem(&abstract_eval_formula(a, env), &abstract_eval_formula(b, env))
        }
        Formula::Neg(inner) => {
            let a = abstract_eval_formula(inner, env);
            if a.is_bottom() {
                Interval::BOTTOM
            } else {
                let lo = a.hi.checked_neg();
                let hi = a.lo.checked_neg();
                match (lo, hi) {
                    (Some(lo), Some(hi)) => Interval { lo, hi },
                    _ => Interval::TOP,
                }
            }
        }
        // For formulas that produce boolean results (comparisons, connectives),
        // we treat them as [0,1] (Bool) or as opaque Top.
        Formula::Bool(true) => Interval::constant(1),
        Formula::Bool(false) => Interval::constant(0),
        // Anything else we cannot evaluate abstractly.
        _ => Interval::TOP,
    }
}

/// Check if a comparison `lhs op rhs` holds for ALL values in the given intervals.
///
/// Returns `Some(true)` if definitely holds, `Some(false)` if definitely fails,
/// `None` if indeterminate.
pub(crate) fn check_comparison_intervals(
    lhs: &Interval,
    rhs: &Interval,
    cmp: ComparisonOp,
) -> Option<bool> {
    if lhs.is_bottom() || rhs.is_bottom() {
        return None;
    }
    // Trust #soundness (i128 add/sub false-PROVE, fuzzer `fn f(a:i128,b:i128){a+b}`):
    // an interval that equals TOP ([i128::MIN, i128::MAX]) carries NO information.
    // Crucially, it is also what `interval_add`/`interval_sub`/`interval_mul`
    // collapse to when the operation OVERFLOWS the i128 this domain represents
    // values in — so TOP's endpoints are SATURATION SENTINELS, not precise bounds.
    // Drawing a definite ordering from them is unsound: for a 128-bit overflow VC
    // the result type's own MAX equals i128::MAX, so `Gt(a+b, i128::MAX)` reads
    // TOP.hi == i128::MAX as "result <= MAX, overflow impossible" and the generic
    // `try_eval_boolean` discharges a REAL i128 add/sub overflow as Proved (the
    // domain literally cannot represent a value past i128::MAX — exactly the
    // overflow being checked). Treat a TOP operand as indeterminate; the obligation
    // then falls through to ay (unbounded-BigInt LIA), which decides it correctly,
    // matching i64/u128. A precise NON-TOP interval whose `hi` happens to be
    // i128::MAX (e.g. [5, i128::MAX], a genuine bound, never produced by an
    // overflowing op which yields full TOP) is unaffected and still concludes.
    // This only ever LOSES a (tautological) conclusion, never enables a discharge,
    // so it cannot introduce a false-FAIL — the kind-specific overflow path already
    // bails on a TOP result (see `check_overflow_discharge`).
    if *lhs == Interval::TOP || *rhs == Interval::TOP {
        return None;
    }
    match cmp {
        // lhs < rhs holds for ALL values iff lhs.hi < rhs.lo
        ComparisonOp::Lt => {
            if lhs.hi < rhs.lo {
                Some(true)
            } else if lhs.lo >= rhs.hi {
                Some(false)
            } else {
                None
            }
        }
        // lhs <= rhs holds for ALL values iff lhs.hi <= rhs.lo
        ComparisonOp::Le => {
            if lhs.hi <= rhs.lo {
                Some(true)
            } else if lhs.lo > rhs.hi {
                Some(false)
            } else {
                None
            }
        }
        // lhs > rhs holds for ALL values iff lhs.lo > rhs.hi
        ComparisonOp::Gt => {
            if lhs.lo > rhs.hi {
                Some(true)
            } else if lhs.hi <= rhs.lo {
                Some(false)
            } else {
                None
            }
        }
        // lhs >= rhs holds for ALL values iff lhs.lo >= rhs.hi
        ComparisonOp::Ge => {
            if lhs.lo >= rhs.hi {
                Some(true)
            } else if lhs.hi < rhs.lo {
                Some(false)
            } else {
                None
            }
        }
        // lhs == rhs holds for ALL values iff both are the same constant
        ComparisonOp::Eq => {
            if lhs.lo == lhs.hi && rhs.lo == rhs.hi && lhs.lo == rhs.lo {
                Some(true)
            } else if lhs.hi < rhs.lo || lhs.lo > rhs.hi {
                Some(false)
            } else {
                None
            }
        }
    }
}

/// Internal comparison operators for `check_comparison_intervals`.
#[derive(Debug, Clone, Copy)]
pub(crate) enum ComparisonOp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
}

/// Try to determine the truth value of a formula under interval abstraction.
///
/// Returns `Some(true)` if the formula is definitely true for all values in
/// the intervals, `Some(false)` if definitely false, `None` if indeterminate.
pub(crate) fn try_eval_boolean(formula: &Formula, env: &IntervalDomain) -> Option<bool> {
    match formula {
        Formula::Bool(b) => Some(*b),

        // Eq(lhs, rhs): check if always equal or never equal
        Formula::Eq(lhs, rhs) => {
            let l = abstract_eval_formula(lhs, env);
            let r = abstract_eval_formula(rhs, env);
            check_comparison_intervals(&l, &r, ComparisonOp::Eq)
        }

        Formula::Lt(lhs, rhs) => {
            let l = abstract_eval_formula(lhs, env);
            let r = abstract_eval_formula(rhs, env);
            check_comparison_intervals(&l, &r, ComparisonOp::Lt)
        }

        Formula::Le(lhs, rhs) => {
            let l = abstract_eval_formula(lhs, env);
            let r = abstract_eval_formula(rhs, env);
            check_comparison_intervals(&l, &r, ComparisonOp::Le)
        }

        Formula::Gt(lhs, rhs) => {
            let l = abstract_eval_formula(lhs, env);
            let r = abstract_eval_formula(rhs, env);
            check_comparison_intervals(&l, &r, ComparisonOp::Gt)
        }

        Formula::Ge(lhs, rhs) => {
            let l = abstract_eval_formula(lhs, env);
            let r = abstract_eval_formula(rhs, env);
            check_comparison_intervals(&l, &r, ComparisonOp::Ge)
        }

        Formula::Not(inner) => try_eval_boolean(inner, env).map(|b| !b),

        Formula::And(clauses) => {
            let mut all_true = true;
            for clause in clauses {
                match try_eval_boolean(clause, env) {
                    Some(false) => return Some(false),
                    Some(true) => {}
                    None => all_true = false,
                }
            }
            if all_true { Some(true) } else { None }
        }

        Formula::Or(clauses) => {
            let mut all_false = true;
            for clause in clauses {
                match try_eval_boolean(clause, env) {
                    Some(true) => return Some(true),
                    Some(false) => {}
                    None => all_false = false,
                }
            }
            if all_false { Some(false) } else { None }
        }

        Formula::Implies(premise, conclusion) => {
            // P => Q is equivalent to !P || Q
            match try_eval_boolean(premise, env) {
                Some(false) => Some(true), // false => anything is true
                Some(true) => try_eval_boolean(conclusion, env),
                None => {
                    // If conclusion is always true, implication holds
                    if try_eval_boolean(conclusion, env) == Some(true) { Some(true) } else { None }
                }
            }
        }

        _ => None,
    }
}

/// Attempt to discharge a VC using abstract interpretation.
///
/// Convention: VC formulas represent the *violation* condition. If the violation
/// formula is UNSAT (always false), the property holds. So if abstract
/// interpretation shows the formula is definitely false for all values in the
/// interval domain, the VC is proved.
///
/// For specific VC kinds, applies targeted checks:
/// - **Overflow VCs:** Checks if computed interval fits within type bounds.
/// - **Division by zero:** Checks if divisor interval excludes zero.
/// - **Index out of bounds:** Checks if index interval fits within array length.
#[must_use]
pub fn try_discharge_vc(vc: &VerificationCondition, env: &IntervalDomain) -> AbstractInterpResult {
    if matches!(vc.kind, VcKind::UnsupportedMir { .. }) {
        // Unsupported MIR is a coverage gap, not a proved unsatisfiable violation.
        // Refuse discharge before generic formula evaluation can prove `false`.
        return AbstractInterpResult::Undetermined;
    }
    // A bitvector-bearing VC (the Machine{w} contract lane) has WRAPPING
    // semantics this Int-interval domain cannot express. Today the evaluators
    // fall to `None`/`TOP` on every `Bv*` atom and the one sort-generic
    // survivor (`Eq` over same-width patterns) is value↔pattern-bijection
    // sound — but that safety is incidental, and an unbounded-Int reading of a
    // wrapping clause is exactly the `result + 1 > result` false-proof vector.
    // Refuse the whole class explicitly.
    if trust_types::formula_mentions_bitvector_theory(&vc.formula) {
        return AbstractInterpResult::Undetermined;
    }

    // First, try the generic formula evaluator: if the violation formula is
    // definitely false, the VC is proved.
    if try_eval_boolean(&vc.formula, env) == Some(false) {
        return AbstractInterpResult::Discharged(VerificationResult::Proved {
            solver: "abstract-interp".into(),
            time_ms: 0,
            strength: ProofStrength::abstract_interpretation(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        });
    }

    // Disjunctive-violation discharge: a violation `And([assumptions…, Or[d1..dn]])`
    // is UNSAT when EACH disjunct `di` is the exact logical negation of an
    // assumption conjunct (`Gt`↔`Le`, `Lt`↔`Ge`, identical operands). The
    // non-relational interval env cannot refute a param-vs-param ordering like
    // `start <= end`, but a dominating guard supplies the literal negation as a
    // sibling conjunct — e.g. the guarded exclusive `&s[a..b]` whose violation is
    // `Or[Gt(a,b), Gt(b,len)]` under `Le(a,b) ∧ Le(b,len)`. Purely syntactic and
    // exact (an assumption `Le(x,y)` LITERALLY entails `¬Gt(x,y)`), so sound; a
    // disjunct with no matching negated assumption leaves the VC undischarged
    // (fail-closed), so a partial/wrong guard cannot over-discharge.
    if try_discharge_negated_disjuncts(&vc.formula) {
        return AbstractInterpResult::Discharged(VerificationResult::Proved {
            solver: "abstract-interp-disjunct".into(),
            time_ms: 0,
            strength: ProofStrength::abstract_interpretation(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        });
    }

    // VC-kind-specific discharge logic for common patterns.
    match &vc.kind {
        // Division by zero: if the formula is And([guards..., Eq(divisor, 0)])
        // and the divisor's interval excludes zero, discharge.
        VcKind::DivisionByZero | VcKind::RemainderByZero => {
            if let Some(divisor_interval) = extract_divisor_interval(&vc.formula, env)
                && !divisor_interval.contains(0)
            {
                return AbstractInterpResult::Discharged(VerificationResult::Proved {
                    solver: "abstract-interp".into(),
                    time_ms: 0,
                    strength: ProofStrength::abstract_interpretation(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                });
            }
        }

        // Arithmetic overflow: check if the result interval fits within type bounds.
        VcKind::ArithmeticOverflow { op, operand_tys } => {
            if let Some(result_ok) = check_overflow_discharge(&vc.formula, env, *op, operand_tys)
                && result_ok
            {
                return AbstractInterpResult::Discharged(VerificationResult::Proved {
                    solver: "abstract-interp".into(),
                    time_ms: 0,
                    strength: ProofStrength::abstract_interpretation(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                });
            }
        }

        // Index out of bounds: check if index < length for all values.
        VcKind::IndexOutOfBounds => {
            if let Some(safe) = check_bounds_discharge(&vc.formula, env)
                && safe
            {
                return AbstractInterpResult::Discharged(VerificationResult::Proved {
                    solver: "abstract-interp".into(),
                    time_ms: 0,
                    strength: ProofStrength::abstract_interpretation(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                });
            }
        }

        // Negation overflow — if operand interval excludes INT_MIN,
        // negation is safe. The formula is And([input_in_range, Eq(val, INT_MIN)]).
        VcKind::NegationOverflow { ty } => {
            if let Some(safe) = check_negation_discharge(&vc.formula, env, ty)
                && safe
            {
                return AbstractInterpResult::Discharged(VerificationResult::Proved {
                    solver: "abstract-interp".into(),
                    time_ms: 0,
                    strength: ProofStrength::abstract_interpretation(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                });
            }
        }

        // Shift overflow — if the shift amount interval is within [0, W) for the
        // EMITTED threshold W (read from the formula, never the possibly-fabricated
        // `operand_ty` width), the shift is safe. Formula is And([range, violation]).
        VcKind::ShiftOverflow { .. } => {
            if let Some(safe) = check_shift_discharge(&vc.formula, env)
                && safe
            {
                return AbstractInterpResult::Discharged(VerificationResult::Proved {
                    solver: "abstract-interp".into(),
                    time_ms: 0,
                    strength: ProofStrength::abstract_interpretation(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                });
            }
        }

        // Float division by zero — same pattern as integer div-by-zero.
        VcKind::FloatDivisionByZero => {
            if let Some(divisor_interval) = extract_divisor_interval(&vc.formula, env)
                && !divisor_interval.contains(0)
            {
                return AbstractInterpResult::Discharged(VerificationResult::Proved {
                    solver: "abstract-interp".into(),
                    time_ms: 0,
                    strength: ProofStrength::abstract_interpretation(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                });
            }
        }

        // Cast overflow — if source interval fits in target type bounds.
        // Formula is And([input_in_range, Or([Lt(val, min), Gt(val, max)])]).
        VcKind::CastOverflow { to_ty, .. } => {
            if let Some(safe) = check_cast_discharge(&vc.formula, env, to_ty)
                && safe
            {
                return AbstractInterpResult::Discharged(VerificationResult::Proved {
                    solver: "abstract-interp".into(),
                    time_ms: 0,
                    strength: ProofStrength::abstract_interpretation(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                });
            }
        }

        _ => {}
    }

    AbstractInterpResult::Undetermined
}

/// Attempt to discharge a batch of VCs, returning those that could not be
/// discharged (and thus need a solver).
///
/// The returned tuples pair each undischarged VC with its original index.
/// Discharged VCs are collected into the `discharged` output vector.
#[must_use]
pub fn try_discharge_batch(vcs: &[VerificationCondition], env: &IntervalDomain) -> DischargeReport {
    let mut discharged = Vec::new();
    let mut remaining = Vec::new();

    for (i, vc) in vcs.iter().enumerate() {
        match try_discharge_vc(vc, env) {
            AbstractInterpResult::Discharged(result) => {
                discharged.push((i, result));
            }
            AbstractInterpResult::Undetermined => {
                remaining.push(i);
            }
        }
    }

    DischargeReport { discharged, remaining }
}

/// Report from a batch discharge attempt.
#[derive(Debug, Clone)]
pub struct DischargeReport {
    /// (original index, verification result) for VCs discharged by abstract interp.
    pub discharged: Vec<(usize, VerificationResult)>,
    /// Original indices of VCs that need a solver.
    pub remaining: Vec<usize>,
}

impl DischargeReport {
    /// Number of VCs discharged.
    #[must_use]
    pub fn discharged_count(&self) -> usize {
        self.discharged.len()
    }

    /// Number of VCs remaining for the solver.
    #[must_use]
    pub fn remaining_count(&self) -> usize {
        self.remaining.len()
    }
}

// ── VC Augmentation with Abstract State ──────────────────────────────────

/// Convert an `IntervalDomain` to a `Formula` conjunction of variable bounds.
///
/// For each variable with a finite interval `[lo, hi]`:
/// - If `lo != i128::MIN`: emit `Ge(Var(name), Int(lo))`
/// - If `hi != i128::MAX`: emit `Le(Var(name), Int(hi))`
///
/// Returns `Bool(true)` if no finite bounds exist (Top state).
///
/// Shared logic factored from `CpaIntervalState::to_formula()`.
#[must_use]
pub fn interval_domain_to_formula(env: &IntervalDomain) -> Formula {
    if env.is_unreachable {
        return Formula::Bool(false);
    }

    let mut conjuncts = Vec::new();
    for (name, interval) in &env.vars {
        if interval.is_bottom() {
            return Formula::Bool(false);
        }
        let var = Formula::Var(name.clone(), Sort::Int);
        if interval.lo != i128::MIN {
            conjuncts.push(Formula::Ge(Box::new(var.clone()), Box::new(Formula::Int(interval.lo))));
        }
        if interval.hi != i128::MAX {
            conjuncts.push(Formula::Le(Box::new(var), Box::new(Formula::Int(interval.hi))));
        }
    }

    // Collapse: empty => Bool(true), single => unwrap, else => And(...)
    conjuncts.retain(|f| *f != Formula::Bool(true));
    match conjuncts.len() {
        0 => Formula::Bool(true),
        1 => conjuncts.pop().unwrap_or(Formula::Bool(true)),
        _ => Formula::And(conjuncts),
    }
}

/// Augment a verification condition's formula with abstract-state assumptions.
///
/// The abstract state at the VC's program point provides tighter variable
/// bounds than the type-level constraints already present in the VC. These
/// bounds are injected as additional conjuncts in the violation formula,
/// narrowing the solver's search space.
///
/// # Soundness
///
/// The abstract state is an over-approximation: every concrete execution
/// satisfies the abstract constraints. Adding them as conjuncts to a
/// violation formula (checked for SAT) cannot exclude real counterexamples.
///
/// # Returns
///
/// A new VC with the same kind, function, location, and contract_metadata,
/// but with `formula = And([abstract_state_formula, original_formula])`.
/// If the abstract state is Top (no useful constraints), returns the VC unchanged.
#[must_use]
pub fn augment_vc_with_abstract_state(
    vc: &VerificationCondition,
    env: &IntervalDomain,
) -> VerificationCondition {
    // A Machine{w}-lane VC models its variables as declared-width bitvectors.
    // Conjoining the interval environment's Int-sorted facts onto it would
    // give the SAME variable two sorts in one formula — an ill-sorted goal
    // the typed native lowering (`trust.vc.formula.payload`) rightly refuses,
    // severing the row's native evidence. The BV width already carries the
    // type-range information these facts would add; leave the row untouched.
    if trust_types::formula_mentions_bitvector_theory(&vc.formula) {
        return vc.clone();
    }
    let env_formula = interval_domain_to_formula(env);

    // If the environment yields no constraints (Top), return the VC unchanged.
    if env_formula == Formula::Bool(true) {
        return vc.clone();
    }

    VerificationCondition {
        kind: vc.kind.clone(),
        function: vc.function,
        location: vc.location.clone(),
        formula: Formula::And(vec![env_formula, vc.formula.clone()]),
        contract_metadata: vc.contract_metadata,
    }
}

/// Augment a batch of VCs with abstract-state assumptions.
///
/// For each VC, uses the merged environment to inject variable-bound
/// constraints. VCs whose abstract state is Top are returned unchanged.
///
///
#[must_use]
pub fn augment_batch(
    vcs: &[VerificationCondition],
    env: &IntervalDomain,
) -> Vec<VerificationCondition> {
    vcs.iter().map(|vc| augment_vc_with_abstract_state(vc, env)).collect()
}

// ── VC-Kind-Specific Helpers ─────────────────────────────────────────────

/// Try to extract the divisor's interval from a div-by-zero VC formula.
///
/// Div-by-zero VCs have the form: Eq(divisor_expr, 0) (possibly wrapped in
/// And with guard conditions). We look for `Eq(expr, Int(0))` and evaluate
/// `expr` abstractly.
fn extract_divisor_interval(formula: &Formula, env: &IntervalDomain) -> Option<Interval> {
    match formula {
        // Direct: Eq(divisor, 0)
        Formula::Eq(lhs, rhs) => {
            if is_zero(rhs) {
                Some(abstract_eval_formula(lhs, env))
            } else if is_zero(lhs) {
                Some(abstract_eval_formula(rhs, env))
            } else {
                None
            }
        }
        // Guarded: And([guard_conditions..., Eq(divisor, 0)])
        Formula::And(clauses) => {
            // The last clause is typically the violation; earlier clauses are guards.
            for clause in clauses.iter().rev() {
                if let Some(interval) = extract_divisor_interval(clause, env) {
                    return Some(interval);
                }
            }
            None
        }
        _ => None,
    }
}

/// Check if a formula is the integer constant zero.
fn is_zero(formula: &Formula) -> bool {
    matches!(formula, Formula::Int(0))
}

/// Try to discharge an arithmetic overflow VC.
///
/// Overflow VCs are produced when a checked binary operation might exceed
/// the type's representable range. If the interval of the result fits
/// within [type_min, type_max], no overflow is possible.
fn check_overflow_discharge(
    formula: &Formula,
    env: &IntervalDomain,
    op: BinOp,
    operand_tys: &(Ty, Ty),
) -> Option<bool> {
    // Get the type bounds for the result type (same as first operand for +,-,*).
    let (type_min, type_max) = type_bounds(&operand_tys.0)?;

    // Try to find the operand expressions in the formula and compute the
    // result interval. Overflow VCs have various formula shapes; we extract
    // operand intervals from the environment when possible.
    //
    // The formula is a violation condition: Or(result < min, result > max).
    // If the result interval is within [min, max], the violation is impossible.
    let result_interval = match formula {
        // Guarded formula: And([guards..., violation])
        // (P1-11): With semantic guards, And can have 3+ elements.
        // The violation formula is always the last conjunct.
        Formula::And(clauses) if clauses.len() >= 2 => {
            compute_overflow_result(clauses.last().expect("non-empty And"), env, op)
        }
        // Unguarded formula: the violation directly
        _ => compute_overflow_result(formula, env, op),
    };

    let result_interval = result_interval?;
    if result_interval == Interval::TOP || result_interval.is_bottom() {
        return None;
    }

    // If the result interval fits entirely within type bounds, no overflow.
    Some(result_interval.lo >= type_min && result_interval.hi <= type_max)
}

/// Compute the result interval of a binary operation from an overflow formula.
///
/// Overflow violation formulas have the form:
///   Or(Lt(result, min), Gt(result, max))
/// We extract the result expression and evaluate it abstractly.
fn compute_overflow_result(formula: &Formula, env: &IntervalDomain, op: BinOp) -> Option<Interval> {
    // Try to find the result expression in various formula shapes.
    match formula {
        Formula::Or(clauses) if clauses.len() == 2 => {
            // Or(Lt(expr, min), Gt(expr, max)) — extract expr from either branch
            if let Formula::Lt(expr, _) | Formula::Gt(expr, _) = &clauses[0] {
                return Some(abstract_eval_formula(expr, env));
            }
            None
        }
        // If we can't decompose the formula, try evaluating all variables
        // and computing the result from the op and type.
        _ => {
            // Fallback: evaluate the whole formula abstractly.
            let _ = (op, env);
            None
        }
    }
}

/// Get the representable bounds [min, max] for an integer type.
pub(crate) fn type_bounds(ty: &Ty) -> Option<(i128, i128)> {
    match ty {
        Ty::Int { width, signed: true } => {
            if *width > 128 {
                return None;
            }
            if *width == 128 {
                Some((i128::MIN, i128::MAX))
            } else {
                let half = 1i128 << (width - 1);
                Some((-half, half - 1))
            }
        }
        Ty::Int { width, signed: false } => {
            if *width > 128 {
                return None;
            }
            if *width == 128 {
                // P1-12: u128::MAX (2^128-1) does not fit in i128.
                // Return None to refuse discharge rather than truncating the range.
                None
            } else {
                Some((0, (1i128 << width) - 1))
            }
        }
        _ => None,
    }
}

/// Try to discharge an index-out-of-bounds VC.
///
/// Bounds VCs assert that an index is within [0, len). If the index interval
/// is entirely within that range, the access is safe.
fn check_bounds_discharge(formula: &Formula, env: &IntervalDomain) -> Option<bool> {
    // Bounds violation formulas: Or(Lt(index, 0), Ge(index, length))
    // or: Ge(index, length)
    // We look for Ge(index_expr, length_expr) patterns.
    match formula {
        Formula::Ge(index_expr, length_expr) => {
            let idx = abstract_eval_formula(index_expr, env);
            let len = abstract_eval_formula(length_expr, env);
            // Safe if index.hi < length.lo (all indices < all lengths)
            // AND index.lo >= 0 (no negative indices)
            if idx == Interval::TOP || len == Interval::TOP {
                return None;
            }
            if idx.lo >= 0 && idx.hi < len.lo { Some(true) } else { None }
        }
        Formula::Or(clauses) if clauses.len() == 2 => {
            // Or(Lt(index, 0), Ge(index, length))
            // Check both conditions are impossible.
            let neg_impossible = match &clauses[0] {
                Formula::Lt(idx_expr, zero_expr) => {
                    let idx = abstract_eval_formula(idx_expr, env);
                    let zero = abstract_eval_formula(zero_expr, env);
                    check_comparison_intervals(&idx, &zero, ComparisonOp::Lt) == Some(false)
                }
                _ => false,
            };
            let oob_impossible = match &clauses[1] {
                Formula::Ge(idx_expr, len_expr) => {
                    let idx = abstract_eval_formula(idx_expr, env);
                    let len = abstract_eval_formula(len_expr, env);
                    check_comparison_intervals(&idx, &len, ComparisonOp::Ge) == Some(false)
                }
                _ => false,
            };
            if neg_impossible && oob_impossible { Some(true) } else { None }
        }
        Formula::And(clauses) => {
            // Guarded: And([guard, violation]) — recurse into the violation part.
            if clauses.len() == 2 { check_bounds_discharge(&clauses[1], env) } else { None }
        }
        _ => None,
    }
}

/// Flatten a (possibly deeply nested) conjunction into its leaf conjuncts. Every
/// returned formula is asserted (And-ed together), so each is a sound assumption.
fn collect_and_conjuncts<'a>(f: &'a Formula, out: &mut Vec<&'a Formula>) {
    match f {
        Formula::And(clauses) => {
            for c in clauses {
                collect_and_conjuncts(c, out);
            }
        }
        other => out.push(other),
    }
}

/// True iff assumption `a` is the EXACT logical negation of disjunct `d`: `Le`
/// entails `¬Gt`, `Ge` entails `¬Lt`, and the reverses — with structurally
/// identical operands. Strict on purpose: a non-exact or operand-mismatched pair
/// returns false, so this can only ever soundly KILL a disjunct it provably
/// refutes (never over-discharge).
fn is_exact_negation(a: &Formula, d: &Formula) -> bool {
    match (a, d) {
        // a = Le(x,y) ⟹ x<=y ⟹ ¬(x>y) ⟹ ¬Gt(x,y)
        (Formula::Le(ax, ay), Formula::Gt(dx, dy))
        // a = Gt(x,y) ⟹ x>y  ⟹ ¬(x<=y) ⟹ ¬Le(x,y)
        | (Formula::Gt(ax, ay), Formula::Le(dx, dy))
        // a = Ge(x,y) ⟹ x>=y ⟹ ¬(x<y) ⟹ ¬Lt(x,y)
        | (Formula::Ge(ax, ay), Formula::Lt(dx, dy))
        // a = Lt(x,y) ⟹ x<y  ⟹ ¬(x>=y) ⟹ ¬Ge(x,y)
        | (Formula::Lt(ax, ay), Formula::Ge(dx, dy)) => ax == dx && ay == dy,
        _ => false,
    }
}

/// A violation `And([assumptions…, Or[d1..dn]])` is UNSAT — so the property holds —
/// when some `Or` conjunct has EVERY disjunct exactly negated by an assumption
/// conjunct. Then `assumptions ∧ Or` is contradictory regardless of the remaining
/// conjuncts. See the call site in `try_discharge_vc` for the soundness argument.
fn try_discharge_negated_disjuncts(formula: &Formula) -> bool {
    let mut conjuncts = Vec::new();
    collect_and_conjuncts(formula, &mut conjuncts);
    conjuncts.iter().any(|c| match c {
        Formula::Or(disjuncts) if !disjuncts.is_empty() => {
            disjuncts.iter().all(|d| conjuncts.iter().any(|a| is_exact_negation(a, d)))
        }
        _ => false,
    })
}

// ── Additional VC-Kind Discharge Helpers ───────────────────────

/// Try to discharge a negation overflow VC.
///
/// Negation overflow occurs only when the operand equals INT_MIN for the
/// signed type. If the operand's interval excludes INT_MIN, negation is safe.
///
/// The formula is: And([input_in_range, Eq(val, INT_MIN)]).
fn check_negation_discharge(formula: &Formula, env: &IntervalDomain, ty: &Ty) -> Option<bool> {
    let (type_min, _type_max) = type_bounds(ty)?;

    // Extract the operand interval from the formula. The inner Eq(val, INT_MIN)
    // gives us the variable; evaluate it in the environment.
    let operand_interval = extract_negation_operand_interval(formula, env)?;

    // If the operand interval doesn't contain INT_MIN, negation is safe.
    Some(!operand_interval.contains(type_min))
}

/// Extract the operand interval from a negation overflow VC formula.
///
/// Pattern: And([input_in_range, Eq(val, INT_MIN)])
/// or: And([input_in_range, And([..., Eq(val, INT_MIN)])])
fn extract_negation_operand_interval(formula: &Formula, env: &IntervalDomain) -> Option<Interval> {
    match formula {
        Formula::Eq(lhs, _rhs) => Some(abstract_eval_formula(lhs, env)),
        Formula::And(clauses) => {
            // Walk clauses looking for Eq(val, INT_MIN).
            for clause in clauses.iter().rev() {
                if let Some(interval) = extract_negation_operand_interval(clause, env) {
                    return Some(interval);
                }
            }
            None
        }
        _ => None,
    }
}

/// Try to discharge a shift overflow VC.
///
/// Shift overflow occurs when the shift amount is negative or >= bit_width.
/// If the shift amount interval is within [0, bit_width), the shift is safe.
///
/// The formula is: And([rhs_in_range, Or([Lt(amt, 0), Ge(amt, width)])])
/// or: And([rhs_in_range, Ge(amt, width)]) for unsigned shift amounts.
fn check_shift_discharge(formula: &Formula, env: &IntervalDomain) -> Option<bool> {
    // Trust #soundness (128-bit shift VC width residue closure): the UB bound is
    // the EMITTED threshold `W` in the violation core `Ge(amt, Int(W))`, NEVER the
    // VC kind's `operand_ty` width. For a constant shifted value (`1i32 << n`) the
    // kind's `operand_ty` fabricates i64 (the width-less `ConstValue::Int`), while
    // the emitter recovers the TRUE result width for the formula — discharging
    // against the fabricated width 64 would falsely prove a real `32 <= n < 64` UB
    // shift. Reading the formula also makes 128-bit value shifts (`u128 << n`,
    // threshold 128) discharge at their honest bound. Fail closed (`None`) when no
    // `Ge(amt, Int(W))` threshold is found.
    let violation = find_shift_violation(formula)?;
    check_shift_violation_refuted(violation, env)
}

/// Locate the shift violation inside a shift overflow VC formula.
///
/// Pattern: And([range_constraint, violation])
/// where violation is Or([Lt(amt, 0), Ge(amt, Int(W))]) or Ge(amt, Int(W)).
fn find_shift_violation(formula: &Formula) -> Option<&Formula> {
    match formula {
        Formula::Ge(_, _) | Formula::Or(_) => Some(formula),
        // And([range_constraint, violation]) — recurse into the violation part
        // (typically the last clause).
        Formula::And(clauses) if clauses.len() >= 2 => find_shift_violation(clauses.last()?),
        _ => None,
    }
}

/// Whether the shift violation is REFUTED by the interval environment — every
/// disjunct is checked against ITS OWN amount expression (never `clauses[0]`'s
/// interval against another clause's threshold):
///   * `Ge(x, Int(W))` — the emitted UB bound; refuted iff `x ∈ [0, W)`.
///   * `Lt(x, Int(0))` — the signed-amount negativity disjunct; refuted iff
///     `x.lo ≥ 0`.
/// Any other disjunct shape, a non-`Int` threshold, a missing `Ge` bound, or a
/// TOP/bottom amount interval returns `None` (fail closed — never a guess).
fn check_shift_violation_refuted(violation: &Formula, env: &IntervalDomain) -> Option<bool> {
    let eval = |x: &Formula| -> Option<Interval> {
        let i = abstract_eval_formula(x, env);
        if i == Interval::TOP || i.is_bottom() { None } else { Some(i) }
    };
    match violation {
        Formula::Ge(amt, bound) => {
            let Formula::Int(w) = bound.as_ref() else { return None };
            let i = eval(amt)?;
            Some(i.lo >= 0 && i.hi < *w)
        }
        Formula::Or(clauses) if !clauses.is_empty() => {
            let mut saw_ge_bound = false;
            let mut refuted = true;
            for clause in clauses {
                match clause {
                    Formula::Ge(amt, bound) => {
                        let Formula::Int(w) = bound.as_ref() else { return None };
                        saw_ge_bound = true;
                        let i = eval(amt)?;
                        refuted &= i.lo >= 0 && i.hi < *w;
                    }
                    Formula::Lt(amt, zero) => {
                        if !matches!(zero.as_ref(), Formula::Int(0)) {
                            return None;
                        }
                        let i = eval(amt)?;
                        refuted &= i.lo >= 0;
                    }
                    _ => return None,
                }
            }
            // Without a `Ge(_, W)` bound this is not the shift-violation shape.
            if saw_ge_bound { Some(refuted) } else { None }
        }
        _ => None,
    }
}

/// Try to discharge a cast overflow VC.
///
/// Cast overflow occurs when the source value doesn't fit in the target type.
/// If the source interval fits entirely within the target type bounds, the
/// cast is safe.
///
/// The formula is: And([input_in_range, Or([Lt(val, min), Gt(val, max)])])
fn check_cast_discharge(formula: &Formula, env: &IntervalDomain, to_ty: &Ty) -> Option<bool> {
    let (target_min, target_max) = type_bounds(to_ty)?;

    // Extract the source value interval from the formula.
    let val_interval = extract_cast_value_interval(formula, env)?;

    if val_interval == Interval::TOP || val_interval.is_bottom() {
        return None;
    }

    // Safe if the entire source interval fits within the target bounds.
    Some(val_interval.lo >= target_min && val_interval.hi <= target_max)
}

/// Extract the source value interval from a cast overflow VC formula.
///
/// Pattern: And([input_in_range, Or([Lt(val, min), Gt(val, max)])])
fn extract_cast_value_interval(formula: &Formula, env: &IntervalDomain) -> Option<Interval> {
    match formula {
        // Or([Lt(val, min), Gt(val, max)]) — extract val from either clause
        Formula::Or(clauses) if clauses.len() == 2 => match &clauses[0] {
            Formula::Lt(val_expr, _) | Formula::Gt(val_expr, _) => {
                Some(abstract_eval_formula(val_expr, env))
            }
            _ => None,
        },
        // And([input_in_range, violation]) — recurse into the violation part
        Formula::And(clauses) if clauses.len() >= 2 => {
            extract_cast_value_interval(clauses.last()?, env)
        }
        _ => None,
    }
}
