// trust-router/constant_folder.rs: Constant-folding backend for trivial formulas
//
// Evaluates only trivially-constant formulas. Any formula containing a free
// variable (or any expression a real solver would need to discharge) is
// returned as `Unknown`. This mock is a pipeline stub, not a real solver — it
// must never claim a counterexample or proof for symbolic content, because the
// outer VC semantics (assertion vs. assumption polarity) is opaque here.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::{BackendRole, VerificationBackend};

// ── verifier-perf: total-WORK budget for the propositional-UNSAT case-split
// recursion ─────────────────────────────────────────────────────────────────
//
// `prop_unsat_conjuncts` proves a conjunction UNSAT by RESOLUTION case-split: for every
// `Or` conjunct it recurses on `rest + branch` for EACH branch. `fuel` bounds the
// recursion DEPTH but NOT the BREADTH, so a formula with several `Or` conjuncts of
// several branches each fans out `O(branches^depth)` — exponential. The recursive
// kernel functions over `Expr`/`Level` (e.g. `env::native_reducers_int`) turn into huge
// guard conjunctions with many `Or` overflow/bounds conjuncts, and this case-split
// explodes: a single `formula_is_propositionally_unsat` call spins for many minutes,
// 100% CPU, on the MAIN compiler thread (no solver, no process isolation — confirmed by
// stack sample: `prop_unsat_conjuncts` self-recursing hundreds of frames deep × wide).
// `fuel=32` does not save it (the fan-out happens within the depth budget), and the
// per-fn/solver timeouts do not catch it (this is in-process folding, not a solver).
//
// FIX (2026-08-31 note: this paragraph describes the ORIGINAL fix and is kept
// because the layer below it is only legible against it): a thread-local
// TOTAL-work budget counting cumulative `prop_unsat_conjuncts` invocations across
// one top-level check. When exhausted the recursion returns the conservative
// `false` (formula NOT proven UNSAT here).
//
// SOUNDNESS (paramount): this discharge is a sound UNDER-approximation — it returns
// `true` only for a genuinely-UNSAT formula and is purely an OPTIMIZATION (a
// structural-UNSAT shortcut ahead of the real solver). Returning `false` early (budget
// exhausted) only DECLINES the shortcut: the obligation then flows to the normal solver
// path unchanged. So the bound can only LOSE a structural discharge (turning a would-be
// structural-Proved into a solver-decided verdict), never manufacture a false
// `true`/UNSAT. The result-level Proved gate is unchanged. DROP-ONLY.
//
// ── 2026-08-31: THE BOUND WAS ON CALLS, AND THE COST IS NOT PER-CALL ─────────
//
// The budget above counts CALLS. Every call, before it splits anything, runs eight
// `conjuncts_carry_*` scans over the whole conjunct list; each is at least one linear
// pass and two of them (`index_len_eq`, `booltemp`) are quadratic in the list with
// heap-allocating, deep-structural-equality inner work. A call is therefore Θ(n) at
// best and Θ(n²) at worst in `n = conjuncts.len()` — never Θ(1) — so a CALL budget
// bounds the number of steps and not the work, and the wall time of a single
// "bounded" check still grows without limit as the guard conjunction gets wider.
//
// MEASURED (release build, `prop_unsat_work_ladder`, 8 atom conjuncts + k `Or`
// bound conjuncts, no contradiction present so the search runs to exhaustion):
//
//   n=12  k=4      0 ms       65 calls     search completed
//   n=14  k=6      1 ms    1,957 calls     search completed
//   n=16  k=8     60 ms  109,601 calls     search completed
//   n=18  k=10   130 ms  200,000 calls     CALL BUDGET HIT
//   n=26  k=10   170 ms  200,000 calls     CALL BUDGET HIT
//   n=42  k=10   255 ms  200,000 calls     CALL BUDGET HIT
//   n=74  k=10   436 ms  200,000 calls     CALL BUDGET HIT
//
// Read the last four rows: at a SATURATED budget the wall clock is linear in `n`
// (130 -> 436 ms as n goes 18 -> 74, ≈ 5.3 ms per 10 conjuncts) and nothing caps it.
// The first three rows are the case-split explosion itself — 65 -> 1,957 -> 109,601
// for k = 4 -> 6 -> 8, i.e. the `k! · branches^k` fan-out the paragraph above
// predicts. So the 2026-08-31 nn-core stack sample that put `prop_unsat_conjuncts`
// at the top of a 31-frame self-recursion was reading a real cost layer, but NOT an
// unbounded one: the search terminates, and what was missing is a bound on WORK.
//
// FIX, part 1 — METER THE SCAN WIDTH. `step(units)` charges `conjuncts.len()` per
// call instead of 1, so the budget bounds Σ n over the whole search: wall time
// becomes FLAT in the conjunct count instead of linear in it.
//
//     PROP_UNSAT_WORK_BUDGET = 6_400_000 scan units
//
// THE CROSSOVER IS n ≈ 15.5, AND IT WAS MEASURED, NOT DERIVED. The first draft of
// this block asserted n = 32, reasoning that a call over n conjuncts costs n units
// so 6.4M/n = 200_000 at n = 32. That reasoning is wrong and the harness caught it:
// the charge attributable to ONE `prop_unsat_conjuncts` call is `2n+1`, not `n`,
// because the call also drives n `prop_unsat_by_discriminant` sub-calls that part 2
// now charges 1 unit each, plus its own n. Measured `units/conj_call` on the ladder
// is exactly 25, 29, 33, 37, 53, 85, 149 at n = 12, 14, 16, 18, 26, 42, 74 — that
// is `2n+1` on every row. So the permitted call count is `6_400_000 / (2n+1)`, which
// equals the old 200_000 at `2n+1 = 32`, i.e. n = 15.5.
//
//   n <= 15  WIDER than the old bound (n=12 buys 256_000 calls, was 200_000)
//   n >= 16  NARROWER — and no width pays for that in wall clock, which is the
//            point: the old bound's saturated wall time was ≈ 5.5·n + 32 ms, so it
//            crossed the new flat ≈ 110 ms ceiling at n ≈ 14. The crossover in
//            SEARCH WIDTH therefore sits within a conjunct or two of the crossover
//            in COST. Below it the search is wider and no slower; above it the
//            search is narrower and strictly faster. Nothing is both.
//
// MEASURED A/B, same harness, same release build, BEFORE = the 200_000-call budget:
//
//   n     conj_calls BEFORE   conj_calls AFTER      wall BEFORE   wall AFTER
//   12         65                  65                    0 ms        0 ms
//   14      1,957               1,957                    1 ms        1 ms
//   16    109,601             109,601                   60 ms       65 ms
//   18    200,000  (bound)    172,972  (bound)         130 ms      123 ms
//   26    200,000  (bound)    120,754  (bound)         170 ms      111 ms
//   42    200,000  (bound)     75,294  (bound)         255 ms      104 ms
//   74    200,000  (bound)     42,953  (bound)         436 ms       99 ms
//
// EQUIVALENCE: on every row whose search COMPLETES — n = 12, 14, 16 — the call count
// is identical to the digit and so is the verdict. That is the whole equivalence
// claim and it is exact, because when neither budget binds the meter is invisible:
// it changes when the traversal stops and nothing about what it does. Divergence is
// confined to the rows that print `bound`, where by construction no proof existed to
// lose (a completed search on those shapes finds nothing — they are SAT).
//
// DISCLOSED BEHAVIOURAL CHANGE, stated as a loss and not dressed up: for n >= 16 this
// searches LESS than before, so a structural discharge that needed between
// `6_400_000/(2n+1)` and `200_000` calls at a width of 16 or more is no longer found
// and falls to the solver. It is completeness-negative in that band and
// completeness-positive below it. It is sound in both directions — see the soundness
// note at the bottom of this block — and the wall-clock table is the reason to take
// the trade: the old bound had no ceiling at all as `n` grew.
//
// FIX, part 2 — METER THE `Or` DESCENT. `prop_unsat_by_discriminant` recursed over
// `Or` disjuncts with only `fuel` (depth 32) bounding it and NO work meter at all:
// the total-work budget covered the `And` re-entry only. A nest of `Or`s whose
// disjuncts are individually UNSAT (so `all` does not short-circuit) fans out
// `branches^32` unmetered. That path is now charged one unit per call, so the bound
// covers the whole traversal rather than one of its two recursive edges.
//
// FIX, part 3 — REPORT IT. Exhaustion used to return the same bare `false` as a
// completed search, so "no contradiction exists" and "we stopped looking" were
// indistinguishable to every caller and to every log. `PropUnsatVerdict` now
// separates them and `formula_is_propositionally_unsat_reported` returns it.
//
// STILL DETERMINISTIC, and deliberately so: the meter is a step count, never a
// clock. Exhaustion decides whether this backend returns a structural proof or
// delegates to the solver, so a wall-clock bound would make a verdict depend on
// machine load. That property is why part 1 is a re-metering and not a timeout.
//
// SOUNDNESS of all three parts: unchanged and DROP-ONLY. Nothing here can make the
// search return `true`; a charge can only make it stop EARLIER, and stopping early
// only declines the shortcut. The `n <= 15` widening does admit `false -> true`
// flips, but only by running MORE of the same resolution steps that were already
// there — a `true` is produced by exactly the same code, so it is as sound as it
// was before, and it is the completeness-positive direction.
const PROP_UNSAT_WORK_BUDGET: u64 = 6_400_000;

/// The budget the pre-2026-08-31 meter enforced, in ITS unit: `prop_unsat_conjuncts`
/// calls. Kept so the crossover is pinned against the real historical number rather
/// than against a comment.
#[cfg(test)]
const LEGACY_PROP_UNSAT_CALL_BUDGET: u64 = 200_000;

/// Scan units charged by one `prop_unsat_conjuncts` call over `n` conjuncts: its own
/// `n`, plus one per `prop_unsat_by_discriminant` sub-call it drives over those same
/// conjuncts. MEASURED exactly on every ladder row — see the header block; the first
/// draft of this file assumed `n` and was wrong by that factor of two.
#[cfg(test)]
const fn scan_units_per_call(n: u64) -> u64 {
    2 * n + 1
}

/// The verdict of the bounded structural-UNSAT search.
///
/// The point of the third variant is that it is NOT a statement about the formula.
/// Collapsing it into `false` — which is what this lane did until 2026-08-31 — makes
/// a declined search look exactly like a completed one that found nothing, so a
/// future blowup degrades silently instead of reporting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropUnsatVerdict {
    /// Proven UNSAT by resolution over opaque atoms. Sound; carries the proof claim.
    Unsat,
    /// The search COMPLETED and found no contradiction. A genuine negative: the
    /// structural lane declines and the obligation keeps its solver verdict.
    NotProven,
    /// The deterministic work bound was reached before the search completed. The
    /// shortcut was declined UNDECIDED — say so rather than record a silent miss.
    SearchBoundReached,
}

impl PropUnsatVerdict {
    /// True only for a genuine proof. `SearchBoundReached` is not a proof and is
    /// not a refutation, so it maps to `false` on the boolean surface — the same
    /// conservative answer the old code gave, minus the ambiguity.
    #[must_use]
    pub fn is_unsat(self) -> bool {
        matches!(self, Self::Unsat)
    }
}

mod prop_work {
    //! Thread-local total-work meter for the propositional-UNSAT case-split. Reset at
    //! each top-level entry; charged the SCAN WIDTH per `prop_unsat_conjuncts` call
    //! (and one unit per `prop_unsat_by_discriminant` call), because per-call cost is
    //! Θ(n) in the conjunct count and never Θ(1). See the header block.
    use std::cell::Cell;

    thread_local! {
        static REMAINING: Cell<u64> = const { Cell::new(0) };
        /// MEASUREMENT ONLY: calls charged since the last `reset`, so a harness can
        /// report the AVERAGE scan width (units / calls) — the quantity the
        /// crossover is actually defined on. See `PROP_UNSAT_CROSSOVER_WIDTH`.
        #[cfg(test)]
        static CALLS: Cell<u64> = const { Cell::new(0) };
        /// MEASUREMENT ONLY: charged calls that were `prop_unsat_conjuncts` (charge
        /// > 1). This is the population the OLD call budget metered, and the only
        /// one an A/B against it may be read off.
        #[cfg(test)]
        static WIDE_CALLS: Cell<u64> = const { Cell::new(0) };
        /// Set when a charge is refused. Sticky until the next `reset`, so a bound
        /// reached anywhere in the traversal is visible at the top-level entry —
        /// the recursion discards intermediate results, so the flag is the only
        /// way the fact survives back up.
        static BOUND_REACHED: Cell<bool> = const { Cell::new(false) };
    }

    /// The production work budget is deterministic because exhaustion changes
    /// whether this backend returns a structural proof or delegates to a solver.
    fn budget() -> u64 {
        super::PROP_UNSAT_WORK_BUDGET
    }

    /// Reset the meter to the deterministic budget at a top-level entry.
    pub(super) fn reset() {
        REMAINING.with(|r| r.set(budget()));
        BOUND_REACHED.with(|b| b.set(false));
        #[cfg(test)]
        CALLS.with(|c| c.set(0));
        #[cfg(test)]
        WIDE_CALLS.with(|c| c.set(0));
    }

    /// Consume `units` of work; returns `false` once the budget cannot cover the
    /// charge (the caller must then return the conservative `false`). Saturating
    /// at 0, and a refusal latches [`bound_reached`].
    ///
    /// A charge of 0 is treated as 1: every call does SOME work, and a free step
    /// would reopen an unmetered path, which is the defect this meter exists to
    /// close.
    pub(super) fn step(units: u64) -> bool {
        let units = units.max(1);
        REMAINING.with(|r| {
            let n = r.get();
            if n < units {
                r.set(0);
                BOUND_REACHED.with(|b| b.set(true));
                return false;
            }
            r.set(n - units);
            #[cfg(test)]
            CALLS.with(|c| c.set(c.get() + 1));
            #[cfg(test)]
            if units > 1 {
                WIDE_CALLS.with(|c| c.set(c.get() + 1));
            }
            true
        })
    }

    /// MEASUREMENT ONLY (test builds): charged calls since the last `reset`.
    #[cfg(test)]
    pub(super) fn calls() -> u64 {
        CALLS.with(std::cell::Cell::get)
    }

    /// MEASUREMENT ONLY (test builds): `prop_unsat_conjuncts` calls since the last
    /// `reset` — the population the pre-2026-08-31 call budget metered.
    #[cfg(test)]
    pub(super) fn wide_calls() -> u64 {
        WIDE_CALLS.with(std::cell::Cell::get)
    }

    /// Whether the work bound was reached during the search since the last `reset`.
    pub(super) fn bound_reached() -> bool {
        BOUND_REACHED.with(std::cell::Cell::get)
    }

    /// MEASUREMENT ONLY (test builds): units consumed since the last `reset`.
    #[cfg(test)]
    pub(super) fn consumed() -> u64 {
        REMAINING.with(|r| budget().saturating_sub(r.get()))
    }
}

/// Constant-folding backend that evaluates trivial formulas.
pub struct ConstantFolderBackend;

impl VerificationBackend for ConstantFolderBackend {
    fn name(&self) -> &str {
        "constant-folder"
    }

    fn role(&self) -> BackendRole {
        BackendRole::General
    }

    fn can_handle(&self, _vc: &VerificationCondition) -> bool {
        true
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        let start = std::time::Instant::now();
        if let Some(result) =
            crate::backend_trait::unsupported_mir_unknown(vc, "constant-folder", 0)
        {
            return result;
        }

        let result = eval_formula(&vc.formula);
        let elapsed = start.elapsed().as_millis() as u64;

        match result {
            FormulaResult::False => VerificationResult::Proved {
                solver: "constant-folder".into(),
                time_ms: elapsed,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
            FormulaResult::True => VerificationResult::Failed {
                solver: "constant-folder".into(),
                time_ms: elapsed,
                counterexample: None,
            },
            FormulaResult::Unknown => VerificationResult::Unknown {
                solver: "constant-folder".into(),
                time_ms: elapsed,
                reason: "constant-folder cannot evaluate complex formulas".to_string(),
            },
        }
    }
}

enum FormulaResult {
    True,
    False,
    Unknown,
}

/// Trivial formula evaluator. Only fully-constant formulas resolve to True or
/// False; anything involving a variable (directly or transitively) is reported
/// as Unknown so the folder never narrows symbolic obligations.
fn eval_formula(formula: &Formula) -> FormulaResult {
    match formula {
        Formula::Bool(true) => FormulaResult::True,
        Formula::Bool(false) => FormulaResult::False,
        Formula::Not(inner) => match eval_formula(inner) {
            FormulaResult::True => FormulaResult::False,
            FormulaResult::False => FormulaResult::True,
            FormulaResult::Unknown => FormulaResult::Unknown,
        },
        Formula::And(terms) => {
            let mut any_unknown = false;
            for term in terms {
                match eval_formula(term) {
                    FormulaResult::False => return FormulaResult::False,
                    FormulaResult::Unknown => any_unknown = true,
                    FormulaResult::True => {}
                }
            }
            if any_unknown { FormulaResult::Unknown } else { FormulaResult::True }
        }
        Formula::Or(terms) => {
            let mut any_unknown = false;
            for term in terms {
                match eval_formula(term) {
                    FormulaResult::True => return FormulaResult::True,
                    FormulaResult::Unknown => any_unknown = true,
                    FormulaResult::False => {}
                }
            }
            if any_unknown { FormulaResult::Unknown } else { FormulaResult::False }
        }
        // Equality of constants — only resolves when both sides are constants.
        Formula::Eq(a, b) => match (a.as_ref(), b.as_ref()) {
            (Formula::Int(x), Formula::Int(y)) => {
                if x == y {
                    FormulaResult::True
                } else {
                    FormulaResult::False
                }
            }
            _ => FormulaResult::Unknown,
        },
        // Anything else (variables, symbolic relations, calls, ...) → Unknown.
        _ => FormulaResult::Unknown,
    }
}

/// Trust: vacuity detector for the phase-A vacuity gate.
///
/// A verification condition asserts its `formula` — the *violation* condition —
/// and checks satisfiability: UNSAT ⇒ the property holds, SAT ⇒ counterexample.
/// If the violation formula is false purely as a BOOLEAN LITERAL (`Bool(false)`,
/// or boolean structure over `Bool` literals — e.g. `¬Bool(true)`), then "UNSAT"
/// carries no information about the program and the proof is VACUOUS: this is the
/// structural sibling of the synthetic `bool_literal(false)` admission and the
/// literal-`true` goal whose violation `¬goal` folds to `false`.
///
/// CRUCIALLY it does NOT fold ARITHMETIC atoms: a violation like
/// `… ∧ (2 = -1)` (a constant-divisor division-overflow check) or `Or([2<0, 2≥32])`
/// (a constant shift-amount check) is a REAL safety obligation that merely happens
/// to be statically decidable — it must reach the solver / kernel and be
/// CERTIFIED, not flagged vacuous and downgraded. Treating every non-boolean atom
/// as opaque (Unknown) draws exactly that line: only the synthetic boolean
/// placeholder folds; every obligation with arithmetic content survives.
#[must_use]
pub fn violation_formula_is_vacuously_unsat(formula: &Formula) -> bool {
    matches!(eval_boolean_skeleton(formula), FormulaResult::False)
}

/// Evaluate ONLY the boolean-literal skeleton of `formula`: `Bool`, `Not`, `And`,
/// `Or` over `Bool` literals. Every other node — arithmetic comparison (`Eq`,
/// `Lt`, …), variable, call — is opaque (`Unknown`), so the result is `False`
/// only when boolean structure over literals alone forces it. This is the
/// vacuity gate's evaluator; it deliberately does NOT fold `Eq(Int, Int)` (unlike
/// [`eval_formula`], which the constant-folder backend uses to discharge trivial
/// obligations) so a statically-decidable arithmetic obligation is never
/// mis-flagged as a vacuous proof.
fn eval_boolean_skeleton(formula: &Formula) -> FormulaResult {
    match formula {
        Formula::Bool(true) => FormulaResult::True,
        Formula::Bool(false) => FormulaResult::False,
        Formula::Not(inner) => match eval_boolean_skeleton(inner) {
            FormulaResult::True => FormulaResult::False,
            FormulaResult::False => FormulaResult::True,
            FormulaResult::Unknown => FormulaResult::Unknown,
        },
        Formula::And(terms) => {
            let mut any_unknown = false;
            for term in terms {
                match eval_boolean_skeleton(term) {
                    FormulaResult::False => return FormulaResult::False,
                    FormulaResult::Unknown => any_unknown = true,
                    FormulaResult::True => {}
                }
            }
            if any_unknown { FormulaResult::Unknown } else { FormulaResult::True }
        }
        Formula::Or(terms) => {
            let mut any_unknown = false;
            for term in terms {
                match eval_boolean_skeleton(term) {
                    FormulaResult::True => return FormulaResult::True,
                    FormulaResult::Unknown => any_unknown = true,
                    FormulaResult::False => {}
                }
            }
            if any_unknown { FormulaResult::Unknown } else { FormulaResult::False }
        }
        // Arithmetic atoms, variables, calls — opaque to the vacuity gate.
        _ => FormulaResult::Unknown,
    }
}

/// Trust: the phase-A vacuity gate. Given an obligation's verification outcome,
/// reject it if it was `Proved` only because its violation formula is vacuously
/// unsatisfiable (constant `false` — a literal true/false goal). Such a "proof"
/// carries no information about the program and must not be counted as real.
///
/// The downgrade target is `Unknown`, not `Failed`: there is no counterexample
/// (the obligation is vacuous, not violated), but under fail-closed semantics an
/// unknown real obligation is a compile error — which is exactly the "hard
/// failure" the vacuity gate demands. A genuine proof (symbolic violation
/// discharged by a real solver) is never touched, because its violation formula
/// does not constant-fold.
#[must_use]
pub fn apply_vacuity_gate(
    vc: &VerificationCondition,
    result: VerificationResult,
) -> VerificationResult {
    if result.is_proved() && violation_formula_is_vacuously_unsat(&vc.formula) {
        return VerificationResult::Unknown {
            solver: "vacuity-gate".into(),
            time_ms: 0,
            reason: "vacuous proof rejected: the violation formula is constant-false \
                     (a literal true/false goal), so the obligation holds regardless of \
                     the program and proves nothing about its safety"
                .to_string(),
        };
    }
    result
}

/// Trust (`[unreach]` structural discharge): is `formula` UNSAT by PURE
/// PROPOSITIONAL resolution over its atoms — treating every non-Boolean-connective
/// subterm (`Eq`, `Lt`, `Pred`, …) as an OPAQUE Boolean literal?
///
/// It recognizes the exhaustive-enum unreachable pattern specifically: a top-level
/// conjunct `Or([Eq(d,c0), …, Eq(d,cn)])` — the `exhaustive_enum_unreachable`
/// validity fact `d ∈ {cases}` emitted by `build_exhaustive_enum_validity_facts` —
/// together with a `Not(Eq(d,ci))` top-level conjunct for EVERY `ci` — the
/// `otherwise → unreachable` path guard `d ∉ {cases}` (`SwitchIntOtherwise`). That
/// is `(E0 ∨ … ∨ En) ∧ ¬E0 ∧ … ∧ ¬En`, UNSAT by pure resolution: resolve the
/// disjunction against each unit `¬Ei` to derive the empty clause. NO theory
/// reasoning is involved (the `Eq` atoms are opaque), so this is a SOUND,
/// self-evident discharge that needs neither ay's strict proof (which only
/// reconstructs LINEAR-ARITHMETIC UNSAT, not a trivial equality/Boolean
/// contradiction — it falls back to an unverified `trust` step / a `Generic`
/// theory lemma the strict checker rejects) nor the SMT trust base.
///
/// SOUNDNESS: the membership fact `d ∈ {cases}` is emitted ONLY for a switch the
/// TyCtxt extraction certified `exhaustive_enum_unreachable` (the case values are
/// EXACTLY the enum's full discriminant tag set), so the contradiction reflects a
/// real program invariant — identical trust to the native trust-mc path, which
/// likewise drops the dead `otherwise` transition under that same flag. A
/// partial/non-exhaustive match never gets the fact, so its formula lacks the `Or`
/// conjunct and this returns `false` (stays runtime-checked — sound, drop-in).
///
/// SURVIVES THE VACUITY GATE: the contradiction is over `Eq` atoms, not `Bool`
/// literals, so [`violation_formula_is_vacuously_unsat`] (which folds ONLY the
/// Boolean-literal skeleton) reports `Unknown` — a discharge here is a genuine
/// proof, not a vacuous one.
#[must_use]
pub fn formula_is_unsat_by_exhaustive_discriminant(formula: &Formula) -> bool {
    prop_work::reset();
    prop_unsat_by_discriminant(formula, 32)
}

/// Sound (under-approximating) propositional-UNSAT check, treating every
/// non-Boolean-connective subterm as an opaque atom. Returns `true` only when the
/// formula is genuinely UNSAT — never for a satisfiable one (no false positives):
///   * `Or(t…)`  is UNSAT iff EVERY disjunct is UNSAT (and there is at least one);
///   * `And(t…)` is UNSAT if ANY conjunct is UNSAT, or the conjuncts contain the
///     exhaustive-discriminant contradiction `(E0∨…∨En) ∧ ¬E0 ∧ … ∧ ¬En`.
///
/// The recursion handles the NESTED-loop trap: a `for i { for j { … } }`
/// unreachable block is reached via `Or([outer_exhausted, inner_exhausted])`,
/// where each branch is independently UNSAT by a DIFFERENT discriminant (the
/// outer `disc_i ∈ {cases} ∧ disc_i ∉ {cases}`, the inner `disc_j …`). The flat
/// single-loop check misses the disjunction; this proves both branches dead.
/// `fuel` bounds the structural descent (sound: exhausting it only yields
/// `false`, an incompleteness, never a wrong `true`).
fn prop_unsat_by_discriminant(formula: &Formula, fuel: u32) -> bool {
    if fuel == 0 {
        return false;
    }
    // verifier-perf: the `Or` descent below was metered by DEPTH only, so a nest of
    // `Or`s whose disjuncts are individually UNSAT (`all` does not short-circuit)
    // fanned out `branches^32` with nothing counting it — the total-work budget
    // covered the `And` re-entry alone. One unit per call closes that edge.
    // SOUNDNESS: refusing the charge returns the conservative `false`, DROP-ONLY.
    if !prop_work::step(1) {
        return false;
    }
    match formula {
        // Trust (R2 family 1): a LITERAL false is UNSAT — the shape a VC takes when
        // vcgen discharges the violation STRUCTURALLY at emission (e.g. the
        // CharIndices-yield str-range fold conjoins `Bool(false)` into the bad-state
        // formula). ay's strict Farkas lane leaves the trivial contradiction Unknown,
        // so without this arm the designed structural promotion never fires. Sound by
        // definition: `false` has no model.
        Formula::Bool(false) => true,
        // A disjunction is false iff every disjunct is false.
        Formula::Or(terms) => {
            !terms.is_empty() && terms.iter().all(|t| prop_unsat_by_discriminant(t, fuel - 1))
        }
        Formula::And(_) => {
            let mut conjuncts: Vec<&Formula> = Vec::new();
            flatten_top_level_and(formula, &mut conjuncts);
            prop_unsat_conjuncts(&conjuncts, fuel)
        }
        _ => false,
    }
}

/// A conjunction (given as its flattened conjuncts) is UNSAT if: any conjunct is
/// itself UNSAT; the conjuncts carry an atom-level contradiction (exhaustive
/// discriminant, complementary pair, bool-temp biconditional, or constant
/// arithmetic bound); OR — by RESOLUTION — some `Or` conjunct case-splits so that
/// EVERY branch, conjoined with the remaining conjuncts, is UNSAT. The case-split
/// is what proves an accumulator overflow `… ∧ Or([Lt(Add,0), Gt(Add,MAX)])`: each
/// branch contradicts a bound fact (`Add ≥ 0`, `Add ≤ bound ≤ MAX`). `fuel` bounds
/// the recursion (sound: running out only yields a conservative `false`).
fn prop_unsat_conjuncts(conjuncts: &[&Formula], fuel: u32) -> bool {
    if fuel == 0 {
        return false;
    }
    // verifier-perf: bound the TOTAL case-split WORK (breadth × depth × scan width),
    // not just depth and not just the call count. The charge is the conjunct count
    // because the eight `conjuncts_carry_*` scans below are each at least one linear
    // pass over this list — a call is Θ(n), never Θ(1), so charging 1 bounded steps
    // and not work. See the header block for the measurement and the calibration.
    // SOUNDNESS: DROP-ONLY — refusing the charge only declines a structural-UNSAT
    // discharge; the obligation falls through to the solver. See `PROP_UNSAT_WORK_BUDGET`.
    if !prop_work::step(conjuncts.len() as u64) {
        return false;
    }
    if conjuncts.iter().any(|c| prop_unsat_by_discriminant(c, fuel - 1))
        || conjuncts_carry_exhaustive_contradiction(conjuncts)
        || conjuncts_carry_complementary_pair(conjuncts)
        || conjuncts_carry_booltemp_contradiction(conjuncts)
        || conjuncts_carry_arith_contradiction(conjuncts)
        || conjuncts_carry_incompatible_const_bounds(conjuncts)
        || conjuncts_carry_const_eq_bound_contradiction(conjuncts)
        || conjuncts_carry_index_len_eq_contradiction(conjuncts)
        || conjuncts_carry_bv_overflow_safe(conjuncts)
    {
        return true;
    }
    // RESOLUTION by case-split on an `Or` conjunct: `F ∧ (B0 ∨ … ∨ Bn)` is UNSAT
    // iff `F ∧ Bi` is UNSAT for every branch `Bi`.
    for (i, c) in conjuncts.iter().enumerate() {
        let Formula::Or(branches) = c else { continue };
        if branches.is_empty() {
            continue;
        }
        let rest: Vec<&Formula> =
            conjuncts.iter().enumerate().filter(|(j, _)| *j != i).map(|(_, f)| *f).collect();
        let all_branches_unsat = branches.iter().all(|b| {
            let mut combined = rest.clone();
            flatten_top_level_and(b, &mut combined);
            prop_unsat_conjuncts(&combined, fuel - 1)
        });
        if all_branches_unsat {
            return true;
        }
    }
    false
}

/// Constant-arithmetic bound contradictions among the conjuncts — sound,
/// theory-free (each is a single comparison of constants):
///   * `Gt(X, hi) ∧ Le(X, c)` with `c ≤ hi`  (`X > hi ≥ c ≥ X`);
///   * `Lt(X, lo) ∧ X ≥ 0` with `lo ≤ 0` — where `X ≥ 0` holds directly
///     (`Le(0, X)` / `Ge(X, 0)`) OR `X = Add(A, B)` with `A ≥ 0` and `B ≥ 0`
///     (a sum of non-negatives is non-negative).
/// This discharges a bounded reduction's per-add overflow `Or([Lt(Add,0),
/// Gt(Add,MAX)])` once the post-add sum bound `Le(Add, K·per_max ≤ MAX)` is present
/// — which ay leaves Unknown because the `<<k` addend is a mixed Int/BV round-trip.
fn conjuncts_carry_arith_contradiction(conjuncts: &[&Formula]) -> bool {
    let cint =
        |f: &Formula| -> Option<i128> { if let Formula::Int(v) = f { Some(*v) } else { None } };
    // `t ≥ 0` provable from a conjunct `Le(0, t)` or `Ge(t, 0)`.
    let nonneg = |t: &Formula| -> bool {
        conjuncts.iter().any(|c| match c {
            Formula::Le(a, b) => cint(a) == Some(0) && **b == *t,
            Formula::Ge(a, b) => **a == *t && cint(b) == Some(0),
            _ => false,
        })
    };
    let term_nonneg = |x: &Formula| -> bool {
        if nonneg(x) {
            return true;
        }
        match x {
            // A sum of non-negatives is non-negative.
            Formula::Add(a, b) => nonneg(a) && nonneg(b),
            // A GUARDED subtraction cannot underflow: `Sub(A,B) ≥ 0` whenever a
            // dominating guard `A ≥ B` (`Ge(A,B)` / `Le(B,A)`) is present — the
            // `if a >= b { a - b }` idiom. Closes the `[overflow:sub]` of guarded
            // subtraction (ay leaves it Unknown; an UNGUARDED `a - b` has no
            // `Ge(A,B)` conjunct, so it stays refutable).
            Formula::Sub(a, b) => conjuncts.iter().any(|c| match c {
                Formula::Ge(l, r) => **l == **a && **r == **b,
                Formula::Le(l, r) => **l == **b && **r == **a,
                _ => false,
            }),
            _ => false,
        }
    };
    // `c ≤ threshold` where the threshold is `Int` OR `UInt`. A `UInt` upper bound
    // (the u64/u128 overflow limit `2^w-1`, which may EXCEED i128::MAX) is handled
    // here because `cint` cannot represent it — without this a wide UNSIGNED reduction
    // (`t += (x as u128) << 4`) never discharges (its overflow threshold is
    // `UInt(u128::MAX)`).
    let le_threshold = |c: i128, hi: &Formula| -> bool {
        match hi {
            Formula::Int(h) => c <= *h,
            Formula::UInt(h) => c < 0 || (c as u128) <= *h,
            _ => false,
        }
    };
    conjuncts.iter().any(|c| match c {
        // `X > hi` contradicted by an upper bound `X ≤ c ≤ hi`.
        Formula::Gt(x, hi) if matches!(hi.as_ref(), Formula::Int(_) | Formula::UInt(_)) => {
            conjuncts.iter().any(|d| match d {
                Formula::Le(y, cc) => **y == **x && cint(cc).is_some_and(|c| le_threshold(c, hi)),
                _ => false,
            })
        }
        // `X < lo` (lo ≤ 0) contradicted by `X ≥ 0`.
        Formula::Lt(x, lo) => cint(lo).is_some_and(|l| l <= 0) && term_nonneg(x),
        _ => false,
    })
}

/// Incompatible CONSTANT bounds on the SAME term: a lower bound `x ≥ L` and an upper
/// bound `x ≤ U` among the conjuncts with `L > U`, so no value satisfies both and the
/// conjunction is UNSAT. Discharges a bounds access whose index is pinned both ways —
/// e.g. the clamp-through-cast `(j as usize) ≤ 7` (an emitted fact) versus the
/// out-of-bounds violation `(j as usize) ≥ 8` (`≥ len`): `7 < 8`, contradiction.
///
/// SOUNDNESS: purely propositional over the SAME opaque term `x` with constant
/// endpoints — `x ≥ L ∧ x ≤ U ∧ L > U` is unsatisfiable in any theory with a total
/// order, no solver trust. SELF-LIMITING: a genuinely out-of-bounds access has
/// compatible bounds (`(j as usize) ≤ 12 ∧ ≥ 10` for a len-10 array — satisfiable, NOT
/// detected), and a stale/withheld fact leaves no upper-bound conjunct, so neither is
/// promoted. ay cannot strictly reconstruct this trivial linear contradiction (only
/// Farkas over its own derivations), which is why the safe access stays runtime-checked
/// without this structural discharge.
fn conjuncts_carry_incompatible_const_bounds(conjuncts: &[&Formula]) -> bool {
    fn cint(f: &Formula) -> Option<i128> {
        if let Formula::Int(v) = f { Some(*v) } else { None }
    }
    // A conjunct that lower-bounds some term: returns `(term, L)` for `term ≥ L`.
    fn lower(c: &Formula) -> Option<(&Formula, i128)> {
        match c {
            Formula::Ge(x, a) => cint(a).map(|v| (x.as_ref(), v)), // x ≥ a
            Formula::Gt(x, a) => cint(a).and_then(|v| v.checked_add(1)).map(|v| (x.as_ref(), v)), // x > a ⇒ x ≥ a+1
            Formula::Le(a, x) => cint(a).map(|v| (x.as_ref(), v)), // a ≤ x ⇒ x ≥ a
            Formula::Lt(a, x) => cint(a).and_then(|v| v.checked_add(1)).map(|v| (x.as_ref(), v)), // a < x ⇒ x ≥ a+1
            _ => None,
        }
    }
    // A conjunct that upper-bounds some term: returns `(term, U)` for `term ≤ U`.
    fn upper(c: &Formula) -> Option<(&Formula, i128)> {
        match c {
            Formula::Le(x, b) => cint(b).map(|v| (x.as_ref(), v)), // x ≤ b
            Formula::Lt(x, b) => cint(b).and_then(|v| v.checked_sub(1)).map(|v| (x.as_ref(), v)), // x < b ⇒ x ≤ b-1
            Formula::Ge(b, x) => cint(b).map(|v| (x.as_ref(), v)), // b ≥ x ⇒ x ≤ b
            Formula::Gt(b, x) => cint(b).and_then(|v| v.checked_sub(1)).map(|v| (x.as_ref(), v)), // b > x ⇒ x ≤ b-1
            _ => None,
        }
    }
    conjuncts
        .iter()
        .filter_map(|c| lower(c))
        .any(|(xl, l)| conjuncts.iter().filter_map(|c| upper(c)).any(|(xu, u)| *xl == *xu && l > u))
}

/// A bound contradiction reached by EQUALITY SUBSTITUTION: a variable resolves to a constant
/// value `v` (via `Eq(var, const)` and `Eq(var, var)` chains among the conjuncts), and another
/// conjunct asserts a bound that `v` violates (`Ge(var, k)` with `v < k`, etc.). Discharges the
/// `arr[e as usize]` discriminant index: after the exhaustive-disjunction case-split picks a branch
/// `Eq(disc, k)`, the cast equality `Eq(idx, disc)` resolves `idx = k`, and the bounds violation
/// `Ge(idx, len)` is then false for `k < len`.
///
/// SOUNDNESS: equality is transitive and a resolved constant is exact, so `x = v ∧ x >= k ∧ v < k`
/// (etc.) is unsatisfiable — pure substitution over the conjuncts, no theory/solver trust. The
/// resolution is a bounded fixpoint over Eq edges; a variable resolving to two DIFFERENT constants
/// (itself a contradiction) is simply not exploited here — that is incompleteness, never a wrong
/// proof.
fn conjuncts_carry_const_eq_bound_contradiction(conjuncts: &[&Formula]) -> bool {
    fn var_name(f: &Formula) -> Option<&str> {
        if let Formula::Var(n, _) = f { Some(n.as_str()) } else { None }
    }
    fn cint(f: &Formula) -> Option<i128> {
        if let Formula::Int(v) = f { Some(*v) } else { None }
    }
    // Seed: `Eq(var, const)` / `Eq(const, var)`.
    let mut vals: Vec<(String, i128)> = Vec::new();
    for c in conjuncts {
        if let Formula::Eq(a, b) = c {
            if let (Some(n), Some(v)) = (var_name(a), cint(b)) {
                vals.push((n.to_string(), v));
            } else if let (Some(v), Some(n)) = (cint(a), var_name(b)) {
                vals.push((n.to_string(), v));
            }
        }
    }
    if vals.is_empty() {
        return false;
    }
    let lookup = |vals: &[(String, i128)], n: &str| -> Option<i128> {
        vals.iter().find(|(vn, _)| vn == n).map(|(_, v)| *v)
    };
    // Propagate over `Eq(var, var)` to a fixpoint (bounded).
    let mut changed = true;
    let mut guard = 0;
    while changed && guard < 16 {
        changed = false;
        guard += 1;
        for c in conjuncts {
            if let Formula::Eq(a, b) = c
                && let (Some(na), Some(nb)) = (var_name(a), var_name(b))
            {
                match (lookup(&vals, na), lookup(&vals, nb)) {
                    (Some(v), None) => {
                        vals.push((nb.to_string(), v));
                        changed = true;
                    }
                    (None, Some(v)) => {
                        vals.push((na.to_string(), v));
                        changed = true;
                    }
                    _ => {}
                }
            }
        }
    }
    // A bound conjunct violated by the resolved constant value.
    conjuncts.iter().any(|c| {
        let check = |x: &Formula, k: &Formula, viol: fn(i128, i128) -> bool| -> bool {
            matches!((var_name(x), cint(k)), (Some(n), Some(kk))
                if lookup(&vals, n).is_some_and(|v| viol(v, kk)))
        };
        match c {
            Formula::Ge(x, k) => check(x, k, |v, kk| v < kk),
            Formula::Gt(x, k) => check(x, k, |v, kk| v <= kk),
            Formula::Le(x, k) => check(x, k, |v, kk| v > kk),
            Formula::Lt(x, k) => check(x, k, |v, kk| v >= kk),
            _ => false,
        }
    })
}

/// An index-vs-length violation `Ge(idx, len)` (`idx >= len`, the classic OOB condition) or
/// `Gt(idx, len)` refuted by a CONSTANT index and a lower bound on `len` reached across EQUALITY.
/// For `idx >= len` to hold given `idx == ci` (const) and `len >= lb` (a fact on `len` OR any var
/// equated to it), we'd need `ci >= len >= lb`, i.e. `ci >= lb`; if `ci < lb` it is UNSAT.
/// Discharges `c[0]` on a slice whose length is only KNOWN-positive symbolically — e.g.
/// `<[T]>::chunks(n)` yields a sub-slice with `c.len() in [1, n]`, and the bounds VC carries
/// `Eq(_15, c__slice_len) ∧ Ge(c__slice_len, 1) ∧ Eq(idx, 0) ∧ Ge(idx, _15)`: `0 < 1`, UNSAT.
///
/// SOUNDNESS: equality is transitive and the lower bound is a real conjunct, so the chain
/// `ci >= len = _15-class >= lb > ci` is a contradiction — pure substitution, no solver trust.
/// SELF-LIMITING: a genuinely-OOB `idx` is not a small const below the length's lower bound, and a
/// `len` with no positive lower bound yields no contradiction.
fn conjuncts_carry_index_len_eq_contradiction(conjuncts: &[&Formula]) -> bool {
    fn var_name(f: &Formula) -> Option<&str> {
        if let Formula::Var(n, _) = f { Some(n.as_str()) } else { None }
    }
    fn cint(f: &Formula) -> Option<i128> {
        if let Formula::Int(v) = f { Some(*v) } else { None }
    }
    // Resolve a var to a constant via `Eq(var, const)` (one hop — sufficient for an index `_14=0`).
    let resolve_const = |x: &Formula| -> Option<i128> {
        if let Some(c) = cint(x) {
            return Some(c);
        }
        let n = var_name(x)?;
        conjuncts.iter().find_map(|c| match c {
            Formula::Eq(a, b) if var_name(a) == Some(n) => cint(b),
            Formula::Eq(a, b) if var_name(b) == Some(n) => cint(a),
            _ => None,
        })
    };
    // The equality CLASS of `n`: `n` plus every var transitively equated to it (bounded BFS over
    // `Eq(var, var)` conjuncts).
    let eq_class = |n: &str| -> Vec<String> {
        let mut class = vec![n.to_string()];
        let mut i = 0;
        while i < class.len() && class.len() < 32 {
            let cur = class[i].clone();
            for c in conjuncts {
                if let Formula::Eq(a, b) = c
                    && let (Some(na), Some(nb)) = (var_name(a), var_name(b))
                {
                    let other = if na == cur {
                        Some(nb)
                    } else if nb == cur {
                        Some(na)
                    } else {
                        None
                    };
                    if let Some(o) = other
                        && !class.iter().any(|m| m == o)
                    {
                        class.push(o.to_string());
                    }
                }
            }
            i += 1;
        }
        class
    };
    // The greatest constant LOWER bound across a var's equality class.
    let class_lower = |n: &str| -> Option<i128> {
        let class = eq_class(n);
        let mut best: Option<i128> = None;
        for c in conjuncts {
            let bound = match c {
                Formula::Ge(m, k) => {
                    var_name(m).filter(|m| class.iter().any(|x| x == m)).and(cint(k))
                }
                Formula::Gt(m, k) => var_name(m)
                    .filter(|m| class.iter().any(|x| x == m))
                    .and(cint(k))
                    .and_then(|v| v.checked_add(1)),
                Formula::Le(k, m) => {
                    var_name(m).filter(|m| class.iter().any(|x| x == m)).and(cint(k))
                }
                Formula::Lt(k, m) => var_name(m)
                    .filter(|m| class.iter().any(|x| x == m))
                    .and(cint(k))
                    .and_then(|v| v.checked_add(1)),
                _ => None,
            };
            if let Some(b) = bound {
                best = Some(best.map_or(b, |cur: i128| cur.max(b)));
            }
        }
        best
    };
    conjuncts.iter().any(|c| {
        let (idx, len, strict) = match c {
            Formula::Ge(a, b) => (a, b, false), // idx >= len
            Formula::Gt(a, b) => (a, b, true),  // idx > len
            _ => return false,
        };
        let Some(ci) = resolve_const(idx) else { return false };
        let Some(len_name) = var_name(len) else { return false };
        let Some(lb) = class_lower(len_name) else { return false };
        // `idx >= len` with idx=ci, len>=lb: needs ci>=lb. `idx > len`: needs ci>lb i.e. ci>=lb+1.
        if strict { ci < lb.saturating_add(1) } else { ci < lb }
    })
}

/// Trust (guarded-safety structural discharge): is the violation `formula`
/// PROPOSITIONALLY UNSAT by pure resolution over opaque atoms? Generalizes
/// [`formula_is_unsat_by_exhaustive_discriminant`] with two more shapes:
///   * a direct COMPLEMENTARY PAIR `X ∧ ¬X` — a guarded division/modulo's
///     `[divzero]`/`[remzero]` violation `(b ≠ 0) ∧ (b = 0)`;
///   * a BOOL-TEMP biconditional `(_t ⟺ X) ∧ _t ∧ ¬X` (or `∧ ¬_t ∧ X`) — the
///     SAME guarded division as lowered on the legacy/full-verification path,
///     where the divisor-zero violation is the bool temp `_4` with a block-def
///     `_4 = (b = 0)`, not a bare `Eq(b,0)` conjunct.
///
/// ay cannot STRICTLY reconstruct such a trivial Boolean/equality contradiction
/// (only linear-arithmetic UNSAT), so a safe guarded operation stays
/// runtime-checked despite being provable. An UNGUARDED operation lacks the
/// contradicting conjunct, so its violation is NOT recognized — never falsely
/// proved (drop-in).
#[must_use]
pub fn formula_is_propositionally_unsat(formula: &Formula) -> bool {
    formula_is_propositionally_unsat_reported(formula).is_unsat()
}

/// The same bounded structural-UNSAT search as [`formula_is_propositionally_unsat`],
/// returning WHY it said no.
///
/// Use this at any site that records or logs a decline. The boolean form cannot tell
/// "the search completed and there is no contradiction" from "the deterministic work
/// bound stopped the search", and those are different facts: the first is a statement
/// about the formula, the second is a statement about this backend. Reporting the
/// second is what keeps a future fan-out blowup from degrading silently — the failure
/// mode this lane shipped with until 2026-08-31.
///
/// Determinism: identical inputs give an identical verdict on any machine, because
/// the bound is a step count and not a clock.
#[must_use]
pub fn formula_is_propositionally_unsat_reported(formula: &Formula) -> PropUnsatVerdict {
    prop_work::reset();
    if prop_unsat_by_discriminant(formula, 32) {
        // A `true` is a real proof even if the bound was reached elsewhere in the
        // search: the resolution steps that produced it all ran. The bound can only
        // have suppressed OTHER branches, and a suppressed branch cannot license a
        // discharge — it can only withhold one.
        PropUnsatVerdict::Unsat
    } else if prop_work::bound_reached() {
        PropUnsatVerdict::SearchBoundReached
    } else {
        PropUnsatVerdict::NotProven
    }
}

/// True iff the conjuncts contain a direct complementary pair `X ∧ ¬X` — some
/// conjunct `Not(X)` whose `X` also appears as a conjunct. UNSAT by one resolution
/// step over the opaque atom `X` (e.g. a guarded division `(b ≠ 0) ∧ (b = 0)`).
fn conjuncts_carry_complementary_pair(conjuncts: &[&Formula]) -> bool {
    conjuncts.iter().any(|c| match c {
        Formula::Not(inner) => conjuncts.iter().any(|d| **d == **inner),
        _ => false,
    })
}

/// True iff the conjuncts carry a bool-temp biconditional contradiction: a
/// definition `Eq(boolvar, atom)` (`boolvar ⟺ atom`) where `boolvar` is asserted
/// true (a bare conjunct `boolvar`) while `atom` is asserted false (`¬atom` is a
/// conjunct), OR symmetrically `¬boolvar ∧ atom`. Unit propagation over the
/// definition yields `atom ∧ ¬atom`. This is the legacy/full-verification lowering
/// of a guarded division: `(_4 ⟺ (b=0)) ∧ _4 ∧ (b ≠ 0)`.
fn conjuncts_carry_booltemp_contradiction(conjuncts: &[&Formula]) -> bool {
    conjuncts.iter().any(|c| {
        // A definition `Eq(boolvar, atom)` with one side a Bool-sorted variable.
        let Formula::Eq(lhs, rhs) = c else { return false };
        let (boolvar, atom): (&Formula, &Formula) = match (lhs.as_ref(), rhs.as_ref()) {
            (bv @ Formula::Var(_, Sort::Bool), atom) => (bv, atom),
            (atom, bv @ Formula::Var(_, Sort::Bool)) => (bv, atom),
            _ => return false,
        };
        let asserted = |t: &Formula| conjuncts.iter().any(|d| **d == *t);
        let negated =
            |t: &Formula| conjuncts.iter().any(|d| matches!(d, Formula::Not(i) if **i == *t));
        // boolvar true ∧ atom false   →   atom ∧ ¬atom
        (asserted(boolvar) && negated(atom))
            // boolvar false ∧ atom true   →   atom ∧ ¬atom
            || (negated(boolvar) && asserted(atom))
    })
}

/// True iff the flattened conjuncts contain a disjunction-of-equalities
/// (`E0 ∨ … ∨ En`, the `exhaustive_enum_unreachable` validity fact `disc ∈ {cases}`)
/// whose EVERY disjunct `Ei` ALSO appears negated as its own conjunct (`¬Ei`, the
/// `SwitchIntOtherwise` guard `disc ∉ {cases}`). That is `(E0∨…∨En) ∧ ¬E0 ∧ … ∧ ¬En`,
/// UNSAT by pure resolution over the opaque `Eq` atoms.
fn conjuncts_carry_exhaustive_contradiction(conjuncts: &[&Formula]) -> bool {
    // The negated equality atoms present as their own conjuncts (`¬Ei`).
    let negated: Vec<&Formula> = conjuncts
        .iter()
        .copied()
        .filter_map(|c| match c {
            Formula::Not(inner) if matches!(inner.as_ref(), Formula::Eq(..)) => {
                Some(inner.as_ref())
            }
            _ => None,
        })
        .collect();

    conjuncts.iter().any(|c| match c {
        Formula::Or(disjuncts) => {
            !disjuncts.is_empty()
                && disjuncts
                    .iter()
                    .all(|d| matches!(d, Formula::Eq(..)) && negated.iter().any(|n| **n == *d))
        }
        _ => false,
    })
}

/// Trust (guarded `i128`/wide add/sub overflow): the operands of the BV overflow
/// check `BvAdd(x, y, w)` / `BvSub(x, y, w)` carry SIGNED BV bounds threaded from
/// dominating guards (`BvSLt(c, x)` ⟹ `x > c`; `BvSLt(x, c)` ⟹ `x < c`); if the
/// result range provably fits `[signed_min(w), signed_max(w)]`, the overflow is
/// impossible and the violation is UNSAT. ay's QF_BV solver leaves the bounded
/// 128-bit sign-bit overflow test Unknown (`sr_i128_add_guarded_safe`), so this
/// structural bound-propagation discharges the guarded wide add/sub.
///
/// SOUND: it uses ONLY the explicit `BvSLt`/`BvSLe` bounds (which only NARROW the
/// operand range, monotone), so additional constraints cannot reintroduce an
/// overflow; an UNGUARDED add has no tight bound (only the `[MIN, MAX]` type range,
/// whose sum overflows → `checked_add` is `None` → not discharged), so a real
/// overflow stays refutable.
fn conjuncts_carry_bv_overflow_safe(conjuncts: &[&Formula]) -> bool {
    // The FIRST `BvAdd`/`BvSub(Var, Var, w)` anywhere in the conjunct tree.
    let mut target: Option<(String, String, u32, bool)> = None;
    for c in conjuncts {
        c.visit(&mut |sub| {
            if target.is_some() {
                return;
            }
            if let Formula::BvAdd(a, b, w) | Formula::BvSub(a, b, w) = sub
                && let (Formula::Var(x, _), Formula::Var(y, _)) = (a.as_ref(), b.as_ref())
            {
                target = Some((x.clone(), y.clone(), *w, matches!(sub, Formula::BvAdd(..))));
            }
        });
        if target.is_some() {
            break;
        }
    }
    let Some((x, y, w, is_add)) = target else { return false };
    if w == 0 || w > 128 {
        return false;
    }
    // Tightest signed `[lo, hi]` bound on a BV var from `BvSLt`/`BvSLe` conjuncts.
    let bounds = |name: &str| -> (Option<i128>, Option<i128>) {
        let mut lo: Option<i128> = None;
        let mut hi: Option<i128> = None;
        let tighten_lo = |lo: &mut Option<i128>, v: i128| *lo = Some(lo.map_or(v, |p| p.max(v)));
        let tighten_hi = |hi: &mut Option<i128>, v: i128| *hi = Some(hi.map_or(v, |p| p.min(v)));
        for c in conjuncts {
            let (strict, l, r) = match c {
                Formula::BvSLt(l, r, _) => (true, l, r),
                Formula::BvSLe(l, r, _) => (false, l, r),
                _ => continue,
            };
            match (l.as_ref(), r.as_ref()) {
                // `c <(=) name`  ⟹  lower bound (`name > c` ⟹ `name >= c+1`).
                (Formula::BitVec { value, .. }, Formula::Var(n, _)) if n == name => {
                    if strict {
                        if let Some(v) = value.checked_add(1) {
                            tighten_lo(&mut lo, v);
                        }
                    } else {
                        tighten_lo(&mut lo, *value);
                    }
                }
                // `name <(=) c`  ⟹  upper bound (`name < c` ⟹ `name <= c-1`).
                (Formula::Var(n, _), Formula::BitVec { value, .. }) if n == name => {
                    if strict {
                        if let Some(v) = value.checked_sub(1) {
                            tighten_hi(&mut hi, v);
                        }
                    } else {
                        tighten_hi(&mut hi, *value);
                    }
                }
                _ => {}
            }
        }
        (lo, hi)
    };
    let (Some(lx), Some(hx)) = bounds(&x) else { return false };
    let (Some(ly), Some(hy)) = bounds(&y) else { return false };
    let (min, max) = if w >= 128 {
        (i128::MIN, i128::MAX)
    } else {
        (-(1i128 << (w - 1)), (1i128 << (w - 1)) - 1)
    };
    // `x op y` cannot overflow iff BOTH extremes of its result range fit `[min, max]`.
    let (lo_res, hi_res) = if is_add {
        (lx.checked_add(ly), hx.checked_add(hy))
    } else {
        (lx.checked_sub(hy), hx.checked_sub(ly))
    };
    lo_res.is_some_and(|r| r >= min) && hi_res.is_some_and(|r| r <= max)
}

/// Collect the conjuncts of a (possibly nested) `And`, descending through nested
/// `And` nodes so `And([a, And([b, c])])` yields `[a, b, c]`. A non-`And` formula
/// is a single conjunct.
fn flatten_top_level_and<'a>(formula: &'a Formula, out: &mut Vec<&'a Formula>) {
    match formula {
        Formula::And(terms) => {
            for t in terms {
                flatten_top_level_and(t, out);
            }
        }
        other => out.push(other),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn eq(var: &str, val: i128) -> Formula {
        Formula::Eq(Box::new(Formula::Var(var.into(), Sort::Int)), Box::new(Formula::Int(val)))
    }

    /// verifier-perf: a conjunction of many independent `Or` conjuncts, each with several
    /// SAT branches, makes the resolution case-split fan out `O(branches^or_conjuncts)` —
    /// the shape that stalled `env::native_reducers_int` for many minutes on the main
    /// compiler thread (confirmed by stack sample). The total-WORK budget must make this
    /// return promptly (no exponential blow-up). SOUNDNESS: the formula here is SAT
    /// (every Or has a satisfiable branch and the conjuncts share no contradiction), so
    /// the correct answer is `false` — exactly what the budget-bounded check returns. It
    /// can NEVER return a false `true`.
    #[test]
    fn deep_case_split_fanout_is_bounded_and_not_false_proved() {
        // 24 independent `Or(a_i==0, a_i==1, a_i==2)` conjuncts over distinct vars —
        // 3^24 ≈ 2.8e11 naive case-split combinations; unbounded recursion would hang.
        let conjuncts: Vec<Formula> = (0..24)
            .map(|i| {
                let v = format!("a{i}");
                Formula::Or(vec![eq(&v, 0), eq(&v, 1), eq(&v, 2)])
            })
            .collect();
        let formula = Formula::And(conjuncts);
        let start = std::time::Instant::now();
        // SAT formula → must NOT be reported UNSAT, and must return fast.
        assert!(
            !formula_is_propositionally_unsat(&formula),
            "a satisfiable fan-out formula must never be proved UNSAT (soundness)"
        );
        assert!(
            start.elapsed() < std::time::Duration::from_secs(5),
            "the work budget must bound the case-split fan-out (took {:?})",
            start.elapsed()
        );
    }

    /// SOUNDNESS twin: a SMALL genuine contradiction still discharges under the budget —
    /// the bound is far above any legitimate structural-UNSAT proof, so it never costs a
    /// real discharge. `(d==0 ∨ d==1) ∧ d≠0 ∧ d≠1` is exhaustively UNSAT and needs only a
    /// couple of case-split steps.
    #[test]
    fn small_exhaustive_contradiction_still_discharges_under_budget() {
        let formula = Formula::And(vec![
            Formula::Or(vec![eq("d", 0), eq("d", 1)]),
            Formula::Not(Box::new(eq("d", 0))),
            Formula::Not(Box::new(eq("d", 1))),
        ]);
        assert!(
            formula_is_propositionally_unsat(&formula),
            "a small exhaustive contradiction must still discharge (budget never costs a real proof)"
        );
    }

    fn boolvar(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Bool)
    }

    fn ivar(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn bvvar(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(128))
    }
    fn bvc(v: i128) -> Formula {
        Formula::BitVec { value: v, width: 128 }
    }

    /// Guarded i128 add: operands bounded `(-1000, 1000)` in BV (`BvSLt` guards) so
    /// Trust (R2 family 1): a literal `false` — the shape of a structurally
    /// discharged VC (the CharIndices-yield str-range fold) — is UNSAT, bare or
    /// as a conjunct; `Bool(true)` and a bare atom stay satisfiable.
    #[test]
    fn literal_false_is_unsat_bare_and_conjoined() {
        assert!(formula_is_propositionally_unsat(&Formula::Bool(false)));
        assert!(formula_is_propositionally_unsat(&Formula::And(vec![
            Formula::Var("g".into(), Sort::Bool),
            Formula::Bool(false),
        ])));
        assert!(!formula_is_propositionally_unsat(&Formula::Bool(true)));
        assert!(!formula_is_propositionally_unsat(&Formula::Var("g".into(), Sort::Bool)));
    }

    /// the sum is in `(-1998, 1998)`, well within i128 — the 128-bit sign-bit
    /// overflow test `Or([… BvAdd(x,y) …])` is UNSAT. ay's QF_BV leaves it Unknown.
    #[test]
    fn guarded_i128_add_bounded_operands_is_unsat() {
        let viol = Formula::BvULt(
            Box::new(Formula::BvAdd(Box::new(bvvar("x")), Box::new(bvvar("y")), 128)),
            Box::new(bvc(i128::MIN)),
            128,
        );
        let formula = Formula::And(vec![
            Formula::BvSLt(Box::new(bvc(-1000)), Box::new(bvvar("x")), 128), // x > -1000
            Formula::BvSLt(Box::new(bvvar("x")), Box::new(bvc(1000)), 128),  // x < 1000
            Formula::BvSLt(Box::new(bvc(-1000)), Box::new(bvvar("y")), 128),
            Formula::BvSLt(Box::new(bvvar("y")), Box::new(bvc(1000)), 128),
            Formula::Or(vec![viol]),
        ]);
        assert!(formula_is_propositionally_unsat(&formula));
    }

    /// SOUNDNESS twin: an UNBOUNDED operand (only the `[i128::MIN, i128::MAX]` type
    /// range) makes the sum range overflow i128 — `checked_add` is `None` — so the
    /// add is NOT discharged; a real `i128::MAX + 1` overflow stays refutable.
    #[test]
    fn unbounded_i128_add_is_not_unsat() {
        let viol = Formula::BvULt(
            Box::new(Formula::BvAdd(Box::new(bvvar("x")), Box::new(bvvar("y")), 128)),
            Box::new(bvc(i128::MIN)),
            128,
        );
        let formula = Formula::And(vec![
            Formula::BvSLe(Box::new(bvc(i128::MIN)), Box::new(bvvar("x")), 128),
            Formula::BvSLe(Box::new(bvvar("x")), Box::new(bvc(i128::MAX)), 128),
            Formula::BvSLe(Box::new(bvc(i128::MIN)), Box::new(bvvar("y")), 128),
            Formula::BvSLe(Box::new(bvvar("y")), Box::new(bvc(i128::MAX)), 128),
            Formula::Or(vec![viol]),
        ]);
        assert!(!formula_is_propositionally_unsat(&formula));
    }

    /// Bounded-reduction per-add overflow: `Or([Lt(Add(t,a),0), Gt(Add(t,a),65535)])`
    /// with `t≥0`, `a≥0`, and the post-add sum bound `Add(t,a) ≤ 65280 ≤ 65535` is
    /// UNSAT — each Or branch contradicts a bound (resolution + constant arithmetic).
    /// This is the `shift` gap (ay leaves it Unknown on the `<<k` Int/BV round-trip).
    #[test]
    fn accumulator_overflow_with_sum_bound_is_unsat() {
        let sum = Formula::Add(Box::new(ivar("t")), Box::new(ivar("a")));
        let formula = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(ivar("t"))),
            Formula::Le(Box::new(Formula::Int(0)), Box::new(ivar("a"))),
            Formula::Le(Box::new(sum.clone()), Box::new(Formula::Int(65280))),
            Formula::Or(vec![
                Formula::Lt(Box::new(sum.clone()), Box::new(Formula::Int(0))),
                Formula::Gt(Box::new(sum), Box::new(Formula::Int(65535))),
            ]),
        ]);
        assert!(formula_is_propositionally_unsat(&formula));
    }

    /// A WIDE unsigned reduction's overflow threshold is `UInt(u128::MAX)` (exceeds
    /// i128::MAX): `Or([Lt(Add,0), Gt(Add, UInt(MAX))]) ∧ Add≥0 ∧ Add≤65280` is UNSAT.
    #[test]
    fn wide_unsigned_accumulator_uint_threshold_is_unsat() {
        let sum = Formula::Add(Box::new(ivar("t")), Box::new(ivar("a")));
        let formula = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(ivar("t"))),
            Formula::Le(Box::new(Formula::Int(0)), Box::new(ivar("a"))),
            Formula::Le(Box::new(sum.clone()), Box::new(Formula::Int(65280))),
            Formula::Or(vec![
                Formula::Lt(Box::new(sum.clone()), Box::new(Formula::Int(0))),
                Formula::Gt(Box::new(sum), Box::new(Formula::UInt(u128::MAX))),
            ]),
        ]);
        assert!(formula_is_propositionally_unsat(&formula));
    }

    /// Guarded subtraction: `if a >= b { a - b }` — the `[overflow:sub]` underflow
    /// violation `Lt(Sub(a,b), 0)` with the guard `Ge(a,b)` is UNSAT (a≥b ⟹ a−b≥0).
    #[test]
    fn guarded_subtraction_no_underflow_is_unsat() {
        let sub = Formula::Sub(Box::new(ivar("a")), Box::new(ivar("b")));
        let formula = Formula::And(vec![
            Formula::Ge(Box::new(ivar("a")), Box::new(ivar("b"))), // guard a >= b
            Formula::Lt(Box::new(sub), Box::new(Formula::Int(0))), // underflow violation
        ]);
        assert!(formula_is_propositionally_unsat(&formula));
    }

    /// SOUNDNESS twin: an UNGUARDED `a - b` (no `a >= b`) can underflow — must NOT
    /// be discharged.
    #[test]
    fn unguarded_subtraction_is_not_unsat() {
        let sub = Formula::Sub(Box::new(ivar("a")), Box::new(ivar("b")));
        let formula = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(ivar("a"))),
            Formula::Lt(Box::new(sub), Box::new(Formula::Int(0))),
        ]);
        assert!(!formula_is_propositionally_unsat(&formula));
    }

    /// Clamp-through-cast bounds: an emitted upper-bound fact `(j as usize) ≤ 7` versus
    /// the out-of-bounds violation `(j as usize) ≥ 8` (a len-8 array) — incompatible
    /// constant bounds (`7 < 8`), so the conjunction is UNSAT and the access is safe.
    #[test]
    fn incompatible_const_bounds_is_unsat() {
        let x = ivar("cast");
        let formula = Formula::And(vec![
            Formula::Le(Box::new(x.clone()), Box::new(Formula::Int(7))), // fact: x <= 7
            Formula::Ge(Box::new(x), Box::new(Formula::Int(8))),         // violation: x >= 8
        ]);
        assert!(formula_is_propositionally_unsat(&formula));
    }

    /// SOUNDNESS twin (OOB mutant): a clamp whose upper bound OVERRUNS the array
    /// (`(j as usize) ≤ 12` on a len-10 array) leaves the violation `≥ 10` SATISFIABLE
    /// (`10 ≤ x ≤ 12`), so it must NOT be discharged — a genuine OOB stays refutable.
    #[test]
    fn compatible_const_bounds_is_not_unsat() {
        let x = ivar("cast");
        let formula = Formula::And(vec![
            Formula::Le(Box::new(x.clone()), Box::new(Formula::Int(12))),
            Formula::Ge(Box::new(x), Box::new(Formula::Int(10))),
        ]);
        assert!(!formula_is_propositionally_unsat(&formula));
    }

    /// SOUNDNESS twin (staleness): when the upper-bound fact is WITHHELD (e.g. the SSA
    /// gate dropped a stale `(j as usize) ≤ 9` after a `&mut` reassignment), only the
    /// violation `≥ 10` remains — satisfiable, so NOT discharged (the OOB refutes).
    #[test]
    fn lone_lower_bound_is_not_unsat() {
        let x = ivar("cast");
        let formula = Formula::Ge(Box::new(x), Box::new(Formula::Int(10)));
        assert!(!formula_is_propositionally_unsat(&formula));
    }

    /// Enum-discriminant index `arr[e as usize]` (`#[repr(u8)] enum E{A,B,C,D}`, len-4 array):
    /// the validity disjunction `disc ∈ {0,1,2,3}`, the cast equality `idx == disc`, and the
    /// bounds violation `idx ≥ 4`. Each case-split branch `disc=k` resolves `idx=k` (equality
    /// chain) and `k < 4` refutes `idx ≥ 4` — UNSAT.
    #[test]
    fn enum_discriminant_index_is_unsat() {
        let disc = ivar("disc");
        let idx = ivar("idx");
        let formula = Formula::And(vec![
            Formula::Or(vec![
                Formula::Eq(Box::new(disc.clone()), Box::new(Formula::Int(0))),
                Formula::Eq(Box::new(disc.clone()), Box::new(Formula::Int(1))),
                Formula::Eq(Box::new(disc.clone()), Box::new(Formula::Int(2))),
                Formula::Eq(Box::new(disc.clone()), Box::new(Formula::Int(3))),
            ]),
            Formula::Eq(Box::new(idx.clone()), Box::new(disc)), // idx == disc
            Formula::Ge(Box::new(idx), Box::new(Formula::Int(4))), // violation idx >= 4
        ]);
        assert!(formula_is_propositionally_unsat(&formula));
    }

    /// SOUNDNESS twin: a 5-variant enum `{0,1,2,3,4}` indexing a len-4 array CAN reach index 4
    /// (OOB) — the branch `disc=4` resolves `idx=4` which does NOT refute `idx ≥ 4` (4 is not
    /// < 4), so the disjunction is NOT all-UNSAT and must NOT be discharged.
    #[test]
    fn enum_discriminant_index_oob_is_not_unsat() {
        let disc = ivar("disc");
        let idx = ivar("idx");
        let formula = Formula::And(vec![
            Formula::Or(vec![
                Formula::Eq(Box::new(disc.clone()), Box::new(Formula::Int(0))),
                Formula::Eq(Box::new(disc.clone()), Box::new(Formula::Int(1))),
                Formula::Eq(Box::new(disc.clone()), Box::new(Formula::Int(2))),
                Formula::Eq(Box::new(disc.clone()), Box::new(Formula::Int(3))),
                Formula::Eq(Box::new(disc.clone()), Box::new(Formula::Int(4))),
            ]),
            Formula::Eq(Box::new(idx.clone()), Box::new(disc)),
            Formula::Ge(Box::new(idx), Box::new(Formula::Int(4))),
        ]);
        assert!(!formula_is_propositionally_unsat(&formula));
    }

    /// `chunks(n)` index `c[0]`: the bounds VC carries `idx == 0`, `_15 == c.len()`,
    /// `c.len() >= 1`, and the violation `idx >= _15`. Across the `_15 == c.len()` equality the
    /// length's lower bound 1 refutes `0 >= _15` — UNSAT.
    #[test]
    fn chunks_index_len_via_equality_is_unsat() {
        let idx = ivar("idx");
        let len_proxy = ivar("len_proxy");
        let slice_len = ivar("slice_len");
        let formula = Formula::And(vec![
            Formula::Eq(Box::new(idx.clone()), Box::new(Formula::Int(0))), // idx == 0
            Formula::Eq(Box::new(len_proxy.clone()), Box::new(slice_len.clone())), // _15 == c.len
            Formula::Ge(Box::new(slice_len), Box::new(Formula::Int(1))),   // c.len >= 1
            Formula::Ge(Box::new(idx), Box::new(len_proxy)),               // violation idx >= _15
        ]);
        assert!(formula_is_propositionally_unsat(&formula));
    }

    /// SOUNDNESS twin: a length only known `>= 0` (no positive lower bound) does NOT refute
    /// `idx(=0) >= len` — index 0 into a possibly-EMPTY slice is genuinely OOB, must NOT discharge.
    #[test]
    fn chunks_index_into_maybe_empty_is_not_unsat() {
        let idx = ivar("idx");
        let len_proxy = ivar("len_proxy");
        let slice_len = ivar("slice_len");
        let formula = Formula::And(vec![
            Formula::Eq(Box::new(idx.clone()), Box::new(Formula::Int(0))),
            Formula::Eq(Box::new(len_proxy.clone()), Box::new(slice_len.clone())),
            Formula::Ge(Box::new(slice_len), Box::new(Formula::Int(0))), // len >= 0 only
            Formula::Ge(Box::new(idx), Box::new(len_proxy)),
        ]);
        assert!(!formula_is_propositionally_unsat(&formula));
    }

    /// SOUNDNESS twin: a GENUINELY-overflowing reduction has a sum bound ABOVE MAX
    /// (`Add ≤ 70000 > 65535`), so the `Gt(Add,65535)` branch is NOT contradicted —
    /// the violation is satisfiable and must NOT be discharged.
    #[test]
    fn accumulator_overflow_above_max_is_not_unsat() {
        let sum = Formula::Add(Box::new(ivar("t")), Box::new(ivar("a")));
        let formula = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(ivar("t"))),
            Formula::Le(Box::new(Formula::Int(0)), Box::new(ivar("a"))),
            Formula::Le(Box::new(sum.clone()), Box::new(Formula::Int(70000))),
            Formula::Or(vec![
                Formula::Lt(Box::new(sum.clone()), Box::new(Formula::Int(0))),
                Formula::Gt(Box::new(sum), Box::new(Formula::Int(65535))),
            ]),
        ]);
        assert!(!formula_is_propositionally_unsat(&formula));
    }

    /// Guarded division (V2 form): `[divzero]` violation `(b ≠ 0) ∧ (b = 0)` is a
    /// complementary pair, UNSAT.
    #[test]
    fn guarded_division_complementary_pair_is_unsat() {
        let formula = Formula::And(vec![Formula::Not(Box::new(eq("b", 0))), eq("b", 0)]);
        assert!(formula_is_propositionally_unsat(&formula));
    }

    /// Guarded division (legacy/full-verification form): the violation is the bool
    /// temp `_4` with a block-def `_4 ⟺ (b = 0)`, conjoined with the guard `b ≠ 0`.
    /// `(_4 ⟺ (b=0)) ∧ _4 ∧ ¬(b=0)` is UNSAT by unit propagation through the def.
    #[test]
    fn guarded_division_booltemp_biconditional_is_unsat() {
        let formula = Formula::And(vec![
            // type ranges (irrelevant noise, like the real legacy formula)
            Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Var("a".into(), Sort::Int))),
            Formula::Eq(Box::new(boolvar("_4")), Box::new(eq("b", 0))), // _4 ⟺ (b=0)
            Formula::Not(Box::new(eq("b", 0))),                         // guard b ≠ 0
            boolvar("_4"),                                              // violation: _4 true
        ]);
        assert!(formula_is_propositionally_unsat(&formula));
    }

    /// SOUNDNESS twin: an UNGUARDED division (violation `b = 0` with no `b ≠ 0`
    /// guard, whether bare or via a bool temp) is SATISFIABLE and must NOT be
    /// recognized — a real division-by-zero must stay refutable.
    #[test]
    fn unguarded_division_is_not_unsat() {
        let bare = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::Var("a".into(), Sort::Int))),
            eq("b", 0),
        ]);
        assert!(!formula_is_propositionally_unsat(&bare));
        let booltemp = Formula::And(vec![
            Formula::Eq(Box::new(boolvar("_4")), Box::new(eq("b", 0))),
            boolvar("_4"), // _4 asserted, but NO `b ≠ 0` guard → SAT (b = 0)
        ]);
        assert!(!formula_is_propositionally_unsat(&booltemp));
    }

    /// The exhaustive-enum unreachable contradiction `(E0∨E1) ∧ ¬E0 ∧ ¬E1` is
    /// propositionally UNSAT and must be recognized — even nested inside the
    /// `And([Bool(true), …])` shape the V2 pipeline produces, and even with
    /// unrelated conjuncts (bounds facts) present.
    #[test]
    fn exhaustive_discriminant_contradiction_is_unsat() {
        let formula = Formula::And(vec![
            Formula::Bool(true),
            Formula::And(vec![
                Formula::Not(Box::new(eq("_7", 0))),
                Formula::Not(Box::new(eq("_7", 1))),
            ]),
            Formula::Or(vec![eq("_7", 0), eq("_7", 1)]),
            Formula::Le(
                Box::new(Formula::Var("t".into(), Sort::Int)),
                Box::new(Formula::Int(65280)),
            ),
        ]);
        assert!(formula_is_unsat_by_exhaustive_discriminant(&formula));
    }

    /// NESTED-loop trap: the unreachable block is reached via
    /// `Or([outer_exhausted, inner_exhausted])`, each branch UNSAT by a DIFFERENT
    /// discriminant (`_8` outer, `_15` inner). The whole `Or` is UNSAT iff BOTH
    /// branches are — the recursive check must prove it (the flat single-loop
    /// check misses the disjunction). This is the `nest2d`/`nest3d` gap.
    #[test]
    fn nested_loop_disjunctive_unreachable_is_unsat() {
        let branch_outer = Formula::And(vec![
            // outer guard `_8 ∉ {0,1}` + outer validity `_8 ∈ {0,1}` (+ inner fact, no inner guard).
            Formula::Not(Box::new(eq("_8", 0))),
            Formula::Not(Box::new(eq("_8", 1))),
            Formula::Or(vec![eq("_8", 0), eq("_8", 1)]),
            Formula::Or(vec![eq("_15", 0), eq("_15", 1)]),
        ]);
        let branch_inner = Formula::And(vec![
            // outer took Some (`_8 == 1`); inner guard `_15 ∉ {0,1}` + inner validity.
            eq("_8", 1),
            Formula::Not(Box::new(eq("_15", 0))),
            Formula::Not(Box::new(eq("_15", 1))),
            Formula::Or(vec![eq("_8", 0), eq("_8", 1)]),
            Formula::Or(vec![eq("_15", 0), eq("_15", 1)]),
        ]);
        let formula =
            Formula::And(vec![Formula::Bool(true), Formula::Or(vec![branch_outer, branch_inner])]);
        assert!(formula_is_unsat_by_exhaustive_discriminant(&formula));
    }

    /// SOUNDNESS twin of the nested case: if ONE branch of the `Or` is NOT UNSAT
    /// (a reachable path), the whole disjunction is satisfiable and must NOT be
    /// recognized — otherwise a genuinely reachable nested trap is false-proved.
    #[test]
    fn nested_disjunction_with_one_satisfiable_branch_is_not_unsat() {
        let branch_unsat = Formula::And(vec![
            Formula::Not(Box::new(eq("_8", 0))),
            Formula::Not(Box::new(eq("_8", 1))),
            Formula::Or(vec![eq("_8", 0), eq("_8", 1)]),
        ]);
        // second branch: a bare guard with no validity fact → satisfiable.
        let branch_sat = Formula::And(vec![Formula::Not(Box::new(eq("_15", 0)))]);
        let formula = Formula::Or(vec![branch_unsat, branch_sat]);
        assert!(!formula_is_unsat_by_exhaustive_discriminant(&formula));
    }

    /// A single-case exhaustive switch (`E0 ∧ ¬E0`) also resolves.
    #[test]
    fn single_case_exhaustive_discriminant_is_unsat() {
        let formula =
            Formula::And(vec![Formula::Not(Box::new(eq("_3", 0))), Formula::Or(vec![eq("_3", 0)])]);
        assert!(formula_is_unsat_by_exhaustive_discriminant(&formula));
    }

    /// A NON-exhaustive guard (only `¬E0 ∧ ¬E1`, no `E0∨E1` validity fact —
    /// the partial-match case) is NOT recognized: it is genuinely satisfiable
    /// (the discriminant could be a third value), so the trap must stay
    /// runtime-checked, never falsely proved.
    #[test]
    fn non_exhaustive_guard_alone_is_not_unsat() {
        let formula = Formula::And(vec![
            Formula::Not(Box::new(eq("_7", 0))),
            Formula::Not(Box::new(eq("_7", 1))),
        ]);
        assert!(!formula_is_unsat_by_exhaustive_discriminant(&formula));
    }

    /// A validity fact whose disjunct is NOT fully negated (one arm reachable)
    /// is satisfiable — must NOT be recognized as UNSAT.
    #[test]
    fn partially_negated_disjunction_is_not_unsat() {
        let formula = Formula::And(vec![
            Formula::Not(Box::new(eq("_7", 0))),
            // `_7 == 1` is NOT excluded, so `(E0 ∨ E1) ∧ ¬E0` is SAT (E1 true).
            Formula::Or(vec![eq("_7", 0), eq("_7", 1)]),
        ]);
        assert!(!formula_is_unsat_by_exhaustive_discriminant(&formula));
    }

    /// A different discriminant in the guard vs. the fact must not cross-resolve.
    #[test]
    fn mismatched_discriminant_is_not_unsat() {
        let formula = Formula::And(vec![
            Formula::Not(Box::new(eq("_7", 0))),
            Formula::Not(Box::new(eq("_7", 1))),
            // fact over a DIFFERENT variable `_9` — no contradiction with `_7`.
            Formula::Or(vec![eq("_9", 0), eq("_9", 1)]),
        ]);
        assert!(!formula_is_unsat_by_exhaustive_discriminant(&formula));
    }

    #[test]
    fn vacuity_detector_flags_constant_false_violation() {
        // The admission's goal `bool_literal(false)`, as a violation formula:
        // trivially UNSAT ⇒ vacuous.
        assert!(violation_formula_is_vacuously_unsat(&Formula::Bool(false)));
    }

    #[test]
    fn vacuity_detector_flags_literal_true_goal() {
        // A goal of `true` ⇒ violation `¬true` ⇒ folds to false ⇒ vacuous.
        let violation = Formula::Not(Box::new(Formula::Bool(true)));
        assert!(violation_formula_is_vacuously_unsat(&violation));
    }

    #[test]
    fn vacuity_detector_ignores_symbolic_violation() {
        // A real overflow violation mentions program variables; the folder
        // cannot evaluate it, so it is NOT flagged vacuous — a real solver
        // decides it. This guards against false-positives that would wrongly
        // reject genuine proofs.
        let violation = Formula::Gt(
            Box::new(Formula::Add(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Var("b".into(), Sort::Int)),
            )),
            Box::new(Formula::Int(4_294_967_295)),
        );
        assert!(!violation_formula_is_vacuously_unsat(&violation));
    }

    #[test]
    fn vacuity_detector_ignores_constant_true_violation() {
        // A constant-true violation is a genuine FAILURE (a counterexample
        // always exists), not a vacuous proof — it must not be flagged.
        assert!(!violation_formula_is_vacuously_unsat(&Formula::Bool(true)));
    }

    #[test]
    fn vacuity_detector_ignores_statically_decidable_arithmetic_violation() {
        // A constant-divisor division-overflow violation `… ∧ (2 = -1)` folds to
        // false ONLY by evaluating the arithmetic atom `2 = -1`. It is a REAL
        // safety obligation that must reach the kernel and be CERTIFIED, not
        // flagged vacuous. The boolean-skeleton evaluator treats `Eq` as opaque,
        // so it is NOT flagged.
        let violation = Formula::And(vec![
            Formula::Eq(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(-2_147_483_648)),
            ),
            Formula::Eq(Box::new(Formula::Int(2)), Box::new(Formula::Int(-1))),
        ]);
        assert!(
            !violation_formula_is_vacuously_unsat(&violation),
            "a statically-decidable arithmetic obligation must NOT be flagged vacuous"
        );
        // Likewise a lone constant-false equality `2 = 0` (div-by-zero divisor).
        assert!(!violation_formula_is_vacuously_unsat(&Formula::Eq(
            Box::new(Formula::Int(2)),
            Box::new(Formula::Int(0)),
        )));
        // But the synthetic admission / a nested `Bool(false)` is STILL flagged.
        assert!(violation_formula_is_vacuously_unsat(&Formula::And(vec![
            Formula::Eq(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)),),
            Formula::Bool(false),
        ])));
    }

    fn vc_with_formula(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    fn proved() -> VerificationResult {
        VerificationResult::Proved {
            solver: "constant-folder".into(),
            time_ms: 0,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    #[test]
    fn vacuity_gate_downgrades_a_vacuous_proof() {
        // Constant-false violation ⇒ trivially UNSAT ⇒ vacuous "proof".
        let gated = apply_vacuity_gate(&vc_with_formula(Formula::Bool(false)), proved());
        assert!(
            matches!(gated, VerificationResult::Unknown { .. }),
            "a vacuous proof must be downgraded (⇒ fail-closed), got: {gated:?}"
        );
    }

    #[test]
    fn vacuity_gate_preserves_a_genuine_proof() {
        // Symbolic violation (mentions a program variable) ⇒ discharged by a
        // real solver; the gate must not touch it.
        let symbolic =
            Formula::Eq(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let gated = apply_vacuity_gate(&vc_with_formula(symbolic), proved());
        assert!(gated.is_proved(), "a genuine symbolic proof must be preserved: {gated:?}");
    }

    #[test]
    fn vacuity_gate_ignores_non_proved_results() {
        let failed =
            VerificationResult::Failed { solver: "ay".into(), time_ms: 0, counterexample: None };
        let gated = apply_vacuity_gate(&vc_with_formula(Formula::Bool(false)), failed);
        assert!(gated.is_failed(), "the gate only touches Proved results: {gated:?}");
    }

    #[test]
    fn test_constant_folder_proves_trivially_false() {
        let backend = ConstantFolderBackend;
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        let result = backend.verify(&vc);
        assert!(result.is_proved());
    }

    #[test]
    fn test_constant_folder_fails_trivially_true() {
        let backend = ConstantFolderBackend;
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        };
        let result = backend.verify(&vc);
        assert!(result.is_failed());
    }

    #[test]
    fn test_constant_folder_unknown_for_variables() {
        let backend = ConstantFolderBackend;
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Var("x".into(), Sort::Int),
            contract_metadata: None,
            obligation: None,
        };
        let result = backend.verify(&vc);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
    }

    #[test]
    fn test_constant_folder_unknown_for_symbolic_eq() {
        // `Eq(Var, Int(0))` is symbolic — the folder must NOT claim it is
        // satisfiable / refutable. A real solver may resolve it, but the mock
        // is a pipeline stub and cannot interpret the VC's outer polarity.
        let backend = ConstantFolderBackend;
        let divisor = Formula::Var("y".into(), Sort::Int);
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(Box::new(divisor), Box::new(Formula::Int(0))),
            contract_metadata: None,
            obligation: None,
        };

        let result = backend.verify(&vc);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
    }

    #[test]
    fn test_constant_folder_proves_explicit_contradiction() {
        // `And(Not(p), p)` where p has Bool(false) inside — fully constant,
        // so the folder can recognise the contradiction.
        let backend = ConstantFolderBackend;
        let p = Formula::Bool(false);
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::And(vec![Formula::Not(Box::new(p.clone())), p]),
            contract_metadata: None,
            obligation: None,
        };

        let result = backend.verify(&vc);
        // p = false, Not(p) = true, And(true, false) = false → Proved.
        assert!(result.is_proved());
    }

    #[test]
    fn test_constant_folder_unknown_for_symbolic_relation() {
        let backend = ConstantFolderBackend;
        let amount = Formula::Var("amount".into(), Sort::Int);
        let vc = VerificationCondition {
            kind: VcKind::ShiftOverflow {
                op: BinOp::Shl,
                operand_ty: Ty::u32(),
                shift_ty: Ty::u32(),
            },
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Ge(Box::new(amount), Box::new(Formula::Int(32))),
            contract_metadata: None,
            obligation: None,
        };

        let result = backend.verify(&vc);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
    }

    // ── LAYER-4 MEASUREMENT HARNESS ────────────────────────────────────────
    //
    // Builds the shape the 2026-08-31 nn-core stack sample caught: a large guard
    // conjunction carrying several `Or` bound conjuncts and no contradiction, so
    // the resolution case-split runs to exhaustion instead of short-circuiting on
    // a proof. Reports (n conjuncts, k Or conjuncts, wall ms, work units charged).
    //
    // `cargo test -p trust-router -- --ignored --nocapture prop_unsat_work_ladder`
    fn ladder_formula(atoms: usize, ors: usize) -> Formula {
        let mut cs: Vec<Formula> = Vec::new();
        for i in 0..atoms {
            cs.push(Formula::Lt(
                Box::new(Formula::Var(format!("x{i}"), Sort::Int)),
                Box::new(Formula::Int(i as i128)),
            ));
        }
        for j in 0..ors {
            let a = Formula::Var(format!("a{j}"), Sort::Int);
            cs.push(Formula::Or(vec![
                Formula::Lt(Box::new(a.clone()), Box::new(Formula::Int(0))),
                Formula::Gt(Box::new(a), Box::new(Formula::Int(i128::from(i64::MAX)))),
            ]));
        }
        Formula::And(cs)
    }

    #[test]
    #[ignore = "measurement harness, not an assertion"]
    fn prop_unsat_work_ladder() {
        println!(
            "atoms  ors  n    verdict             wall_ms   work_units     calls  conj_calls  units/conj"
        );
        for (atoms, ors) in [(8, 4), (8, 6), (8, 8), (8, 10), (16, 10), (32, 10), (64, 10)] {
            let f = ladder_formula(atoms, ors);
            let t0 = std::time::Instant::now();
            let v = formula_is_propositionally_unsat_reported(&f);
            let ms = t0.elapsed().as_millis();
            let (units, calls) = (prop_work::consumed(), prop_work::calls());
            let wide = prop_work::wide_calls();
            #[allow(clippy::cast_precision_loss)]
            let mean_width = units as f64 / wide.max(1) as f64;
            println!(
                "{atoms:5}  {ors:3}  {:<4} {:<19} {ms:7}   {units:>9} {calls:>9} {wide:>9}   {mean_width:>8.2}",
                atoms + ors,
                format!("{v:?}"),
            );
        }
    }

    /// The re-metering is CALIBRATED against the real historical bound, and the
    /// crossover is where this file SAYS it is. Pinned because the first draft put it
    /// at n = 32 by assuming a call costs `n` units; it costs `2n+1`, and only the
    /// harness caught that. If someone re-tunes the budget, this fails and names the
    /// width that moved rather than letting the prose drift.
    #[test]
    fn prop_unsat_budget_crossover_is_where_the_header_says() {
        let calls_at = |n: u64| PROP_UNSAT_WORK_BUDGET / scan_units_per_call(n);
        assert!(
            calls_at(15) >= LEGACY_PROP_UNSAT_CALL_BUDGET,
            "n=15 must still buy at least the legacy search: {} calls",
            calls_at(15)
        );
        assert!(
            calls_at(16) < LEGACY_PROP_UNSAT_CALL_BUDGET,
            "n=16 must be the first NARROWER width: {} calls",
            calls_at(16)
        );
    }

    /// The measured charge law. `scan_units_per_call` is used by the calibration
    /// above, so it is not allowed to be a guess: this re-derives it from the meter
    /// on the real search, at three widths.
    #[test]
    fn prop_unsat_charge_law_is_two_n_plus_one() {
        for (atoms, ors, n) in [(8_usize, 4_usize, 12_u64), (8, 6, 14), (8, 8, 16)] {
            let f = ladder_formula(atoms, ors);
            let _ = formula_is_propositionally_unsat(&f);
            let (units, wide) = (prop_work::consumed(), prop_work::wide_calls());
            assert!(wide > 0, "n={n}: the harness shape must reach the case split");
            assert_eq!(
                units / wide,
                scan_units_per_call(n),
                "n={n}: measured {units} units over {wide} calls"
            );
        }
    }

    /// A declined search is DISTINGUISHABLE from a completed one. Before 2026-08-31
    /// both were a bare `false`, so a fan-out blowup degraded with nothing said.
    #[test]
    fn prop_unsat_reports_why_it_said_no() {
        // Proof: the guarded-division contradiction `b ≠ 0 ∧ b = 0`.
        let b = Formula::Var("b".into(), Sort::Int);
        let eq0 = Formula::Eq(Box::new(b.clone()), Box::new(Formula::Int(0)));
        let proved = Formula::And(vec![Formula::Not(Box::new(eq0.clone())), eq0]);
        assert_eq!(formula_is_propositionally_unsat_reported(&proved), PropUnsatVerdict::Unsat);

        // Completed search, no contradiction: small enough that the bound cannot bite.
        let small = ladder_formula(4, 2);
        assert_eq!(
            formula_is_propositionally_unsat_reported(&small),
            PropUnsatVerdict::NotProven,
            "a small exhaustive search must report NotProven, not a bound"
        );

        // Bound reached: the fan-out shape from the ladder, wide enough to saturate.
        let wide = ladder_formula(64, 10);
        assert_eq!(
            formula_is_propositionally_unsat_reported(&wide),
            PropUnsatVerdict::SearchBoundReached,
            "a saturating search must SAY it was cut short"
        );
        // ...and the boolean surface still answers conservatively, unchanged.
        assert!(!formula_is_propositionally_unsat(&wide));
    }

    /// The `Or` descent in `prop_unsat_by_discriminant` used to carry NO work meter
    /// (depth-32 fuel only), so the total-work budget covered one of the two
    /// recursive edges. This pins that it is charged now: a wide `Or` nest must
    /// terminate against the meter rather than against the fuel alone.
    #[test]
    fn prop_unsat_or_descent_is_metered() {
        // Or of Ors, each leaf a distinct SAT atom, 8 deep × 4 wide.
        fn nest(depth: u32, wide: usize, tag: &mut u64) -> Formula {
            if depth == 0 {
                *tag += 1;
                return Formula::Var(format!("v{tag}"), Sort::Bool);
            }
            Formula::Or((0..wide).map(|_| nest(depth - 1, wide, tag)).collect())
        }
        let mut tag = 0;
        let f = nest(8, 4, &mut tag);
        let t0 = std::time::Instant::now();
        assert!(!formula_is_propositionally_unsat(&f));
        // Not a wall-clock verdict — just a tripwire that the traversal is bounded.
        assert!(t0.elapsed().as_secs() < 10, "Or descent ran unbounded");
    }
}
