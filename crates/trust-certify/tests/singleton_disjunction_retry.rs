//! THE SINGLETON-DISJUNCTION RETRY, at the smallest formula that exhibits it.
//!
//! `certify_singleton_disjunction_retry` is the producer's last rung: a flat
//! (disjunction-free) violation carrying a top-level NEGATED CONJUNCTION is
//! re-presented to `certify_disjunctive_contradiction` as a one-arm disjunction,
//! because that engine's `distribute_negated_conjunctions` is the only lane that
//! can split such a conjunct and it is unreachable behind an
//! `or_candidates.is_empty()` gate. The a7 per-path postcondition row is what
//! motivated it; `crates/trust-vcgen/tests/per_path_postcondition_kernel_recheck.rs`
//! measures it on real extracted MIR.
//!
//! This file pins the DIRECTION on a two-conjunct formula, where nothing about
//! the shape is in question and only the verdict is. Both tests are the same
//! violation `_0 = k ∧ ¬(0 ≤ _0 ≤ 3)` with `k` moved across the bound, so a lane
//! that certified on the shape rather than on the mathematics passes one and
//! fails the other.
//!
//! `recheck_vc_cleancic` is asserted on the positive because a certificate this
//! rung mints must replay through the ordinary consumer path: the re-check
//! regenerates from the ORIGINAL violation through this same producer, so a
//! certificate produced under the wrap but replayed without it would be
//! rejected. It is not, which is the evidence that `identity` and the emitted
//! term belong to the unwrapped row.

use trust_certify::{certify_vc, recheck_vc_cleancic};
use trust_ir::ProofEvidence;
use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

fn int(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}

fn lit(value: i128) -> Formula {
    Formula::Int(value)
}

/// `_0 = value ∧ ¬(0 ≤ _0 ∧ _0 ≤ 3)` — a postcondition `0 <= result <= 3` over a
/// body returning the constant `value`, in the shape vcgen emits: the clause is
/// negated as ONE conjunction, never distributed.
fn range_postcondition_violation(value: i128) -> VerificationCondition {
    let formula = Formula::And(vec![
        Formula::Eq(Box::new(int("_0")), Box::new(lit(value))),
        Formula::Not(Box::new(Formula::And(vec![
            Formula::Le(Box::new(lit(0)), Box::new(int("_0"))),
            Formula::Le(Box::new(int("_0")), Box::new(lit(3))),
        ]))),
    ]);
    VerificationCondition {
        kind: VcKind::Postcondition,
        function: "constant_return".into(),
        location: SourceSpan {
            file: "singleton_disjunction_retry.rs".into(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 1,
        },
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

/// POSITIVE. `_0 = 2` satisfies `0 ≤ _0 ≤ 3`, so the violation is UNSAT and the
/// kernel must refute it. At HEAD this returned `None`: the negated conjunction's
/// leaves are absent from the pool (so the propositional-closure lane declines)
/// and `collect_supported_atoms` drops the conjunct outright (so the linear-Int
/// lane never sees the contradiction at all).
#[test]
fn a_flat_negated_range_over_a_satisfying_constant_is_kernel_certified() {
    let vc = range_postcondition_violation(2);
    let evidence = certify_vc(&vc)
        .expect("`_0 = 2 ∧ ¬(0 ≤ _0 ≤ 3)` is unsatisfiable and must reach a kernel refutation");
    let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
        panic!("the kernel lane must return CleanCic evidence");
    };
    assert!(
        recheck_vc_cleancic(&term, &context, &lineage, &vc),
        "the certificate must replay against the UNWRAPPED obligation: the consumer \
         regenerates from the original violation, so a term bound to the wrapped \
         formula would fail here",
    );
}

/// CLOSE NEGATIVE TWIN — one literal moved, across the bound. `_0 = 5` violates
/// `_0 ≤ 3`, so the violation is SATISFIABLE and no certificate may exist. The
/// retry rung FIRES on this formula (disjunction-free pool, top-level negated
/// conjunction) and must come back empty-handed: what stops it is the engine's
/// ay-UNSAT gate and kernel re-check, not the rung's own entry test.
#[test]
fn the_same_shape_over_a_violating_constant_stays_uncertified() {
    assert!(
        certify_vc(&range_postcondition_violation(5)).is_none(),
        "`_0 = 5 ∧ ¬(0 ≤ _0 ≤ 3)` is SATISFIABLE — the postcondition is genuinely \
         violated — so certifying it would be a kernel certificate for a false clause",
    );
}

/// The other boundary of the same twin, one step the other way: `_0 = -1`
/// violates `0 ≤ _0`. Both halves of the negated conjunction must fail closed,
/// not just the upper one the distribution happens to try first.
#[test]
fn the_lower_half_of_the_range_fails_closed_too() {
    assert!(
        certify_vc(&range_postcondition_violation(-1)).is_none(),
        "`_0 = -1 ∧ ¬(0 ≤ _0 ≤ 3)` is SATISFIABLE through the LOWER bound",
    );
}
