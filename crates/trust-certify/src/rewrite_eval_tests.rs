// Trust (D5-B follow-up, 2026-09-25): the kernel-checked rewriting lane.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Every positive here is a violation NO earlier lane certifies (asserted), so
//! the lane is what moved it; every negative is SATISFIABLE (a witness is named
//! in the comment) and must never certify, through the lane directly or through
//! the full producer.

use super::*;

fn int(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Int)
}
fn boolv(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Bool)
}
fn lit(k: i128) -> Formula {
    Formula::Int(k)
}
fn eq(a: Formula, b: Formula) -> Formula {
    Formula::Eq(Box::new(a), Box::new(b))
}
fn lt(a: Formula, b: Formula) -> Formula {
    Formula::Lt(Box::new(a), Box::new(b))
}
fn not(a: Formula) -> Formula {
    Formula::Not(Box::new(a))
}
fn implies(a: Formula, b: Formula) -> Formula {
    Formula::Implies(Box::new(a), Box::new(b))
}

fn on_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(f)
        .expect("spawn")
        .join()
        .expect("join")
}

/// The lane alone, under the formula-only identity.
fn lane(violation: &Formula) -> Option<trust_ir::ProofEvidence> {
    let v = violation.clone();
    on_stack(move || {
        let identity = crate::ObligationIdentity::from_violation(&v)?;
        certify_rewrite_evaluation(&v, &identity)
    })
}

/// The full producer (every lane, memo off).
fn producer(violation: &Formula) -> Option<trust_ir::ProofEvidence> {
    crate::reset_certify_memo();
    crate::certify_violation(violation)
}

fn term_of(evidence: &Option<trust_ir::ProofEvidence>) -> Option<&[u8]> {
    match evidence {
        Some(trust_ir::ProofEvidence::CleanCic { term, .. }) => Some(term.as_slice()),
        _ => None,
    }
}

fn closed_addition_lane(violation: &Formula) -> Option<trust_ir::ProofEvidence> {
    let v = violation.clone();
    on_stack(move || {
        let identity = crate::ObligationIdentity::from_violation(&v)?;
        certify_rewrite_evaluation_with_closed_additions(&v, &identity)
    })
}

fn two_additions(start: i128, lower: i128, upper: i128) -> Formula {
    let add = |a, b| Formula::Add(Box::new(a), Box::new(b));
    let sum = || add(int("second"), lit(1));
    Formula::And(vec![
        eq(int("start"), lit(start)),
        eq(int("first"), add(int("start"), lit(1))),
        eq(int("second"), int("first")),
        Formula::Or(vec![
            lt(sum(), lit(lower)),
            Formula::Gt(Box::new(sum()), Box::new(lit(upper))),
        ]),
    ])
}

#[test]
fn successive_closed_additions_require_the_new_final_lane() {
    for (start, lower, upper) in [
        (0, 0, 3),
        (0, 0, u64::MAX as i128),
        (-3, i128::MIN, i128::MAX),
        (i128::MAX - 2, i128::MIN, i128::MAX),
    ] {
        let violation = two_additions(start, lower, upper);
        assert!(lane(&violation).is_none(), "the original evaluator must keep its fragment");
        let from_lane = closed_addition_lane(&violation);
        assert!(from_lane.is_some(), "safe chain {start}, {lower}, {upper}");
        let produced = producer(&violation);
        assert_eq!(term_of(&produced), term_of(&from_lane));
    }
}

#[test]
fn successive_additions_do_not_certify_real_range_violations() {
    // Each chain has a unique model; its final sum is outside the stated range.
    for (start, lower, upper) in [
        (0, 0, 1),
        (-3, 0, 3),
        (u64::MAX as i128 - 1, 0, u64::MAX as i128),
        (i128::MAX - 2, i128::MIN, i128::MAX - 1),
        (i128::MIN, i128::MIN + 3, i128::MAX),
    ] {
        let violation = two_additions(start, lower, upper);
        assert!(closed_addition_lane(&violation).is_none(), "satisfiable chain {start}");
        assert!(producer(&violation).is_none(), "satisfiable chain {start}");
    }
}

#[test]
fn overflowing_search_arithmetic_does_not_wrap_into_a_certificate() {
    // Mathematical Int addition exceeds i128, so the search evaluator must
    // decline rather than treating MAX+2 as a negative machine integer.
    let violation = two_additions(i128::MAX, i128::MIN, i128::MAX);
    assert!(closed_addition_lane(&violation).is_none());
    assert!(producer(&violation).is_none());
}

#[test]
fn wide_non_strict_addition_orders_refute_only_the_false_orientation() {
    let add = |a, b| Formula::Add(Box::new(a), Box::new(b));
    for greater in [false, true] {
        for satisfiable in [false, true] {
            let sum = add(int("first"), lit(1));
            let maximum = lit(u64::MAX as i128);
            let (a, b) = if greater == satisfiable { (maximum, sum) } else { (sum, maximum) };
            let order = if greater {
                Formula::Ge(Box::new(a), Box::new(b))
            } else {
                Formula::Le(Box::new(a), Box::new(b))
            };
            let violation = Formula::And(vec![
                eq(int("start"), lit(0)),
                eq(int("first"), add(int("start"), lit(1))),
                order,
            ]);
            assert_eq!(closed_addition_lane(&violation).is_some(), !satisfiable);
            if satisfiable {
                // start=0, first=1 satisfies this order; no lane may certify it.
                assert!(producer(&violation).is_none());
            }
        }
    }
}

#[test]
fn reversed_addition_equalities_compare_closed_values_without_assuming_them() {
    let add = |a, b| Formula::Add(Box::new(a), Box::new(b));
    for first_value in [1, 2] {
        let violation = Formula::And(vec![
            eq(int("start"), lit(0)),
            eq(add(int("start"), lit(first_value)), int("first")),
            eq(int("second"), add(lit(2), lit(-1))),
            not(eq(int("first"), int("second"))),
        ]);
        assert_eq!(closed_addition_lane(&violation).is_some(), first_value == 1);
        if first_value == 2 {
            // start=0, first=2, second=1 is an actual satisfying assignment.
            assert!(producer(&violation).is_none());
        }
    }
}

#[test]
fn closed_addition_retry_keeps_placeholder_pool_and_depth_refusals() {
    assert!(closed_addition_lane(&Formula::Bool(false)).is_none());
    let placeholder = Formula::And(vec![eq(int("x"), lit(0)), Formula::Bool(false)]);
    assert!(closed_addition_lane(&placeholder).is_none());
    let mut pool: Vec<_> = (0..MAX_POOL).map(|i| eq(int(&format!("x{i}")), lit(0))).collect();
    // Without the cap, x0=0 and x0!=0 would immediately refute this pool.
    pool.push(not(eq(int("x0"), lit(0))));
    let mut within_cap = pool.clone();
    within_cap.remove(MAX_POOL - 1);
    assert!(closed_addition_lane(&Formula::And(within_cap)).is_some());
    let oversized = Formula::And(pool);
    assert!(closed_addition_lane(&oversized).is_none());

    // This is a real contradiction, but searching an addition deeper than the
    // established evaluation bound must still decline rather than bypass it.
    let mut sum = lit(0);
    for _ in 0..MAX_EVAL_DEPTH + 2 {
        sum = Formula::Add(Box::new(sum), Box::new(lit(1)));
    }
    let deep =
        Formula::And(vec![eq(int("x"), sum), not(eq(int("x"), lit((MAX_EVAL_DEPTH + 2) as i128)))]);
    assert!(closed_addition_lane(&deep).is_none());
}

/// The lane certifies, AND the full producer's certificate is byte-identical to
/// the lane's — the producer returns its FIRST certifying lane, so equality
/// means no earlier lane certified this violation: the lane is what moved it.
fn assert_certifies(label: &str, violation: Formula) {
    let from_lane = lane(&violation);
    let Some(trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. }) = from_lane.clone()
    else {
        panic!("{label}: the rewriting lane must certify {violation:?}");
    };
    let produced = producer(&violation);
    assert!(produced.is_some(), "{label}: the producer must reach the lane");
    assert_eq!(
        term_of(&produced),
        term_of(&from_lane),
        "{label}: an earlier lane certified it — this is not the lane's measurement"
    );
    // The consumer re-check regenerates through the same producer.
    let v = violation.clone();
    assert!(
        on_stack(move || crate::recheck_cleancic(&term, &context, &lineage, &v)),
        "{label}: the consumer re-check must accept the lane's certificate"
    );
}

fn assert_refused(label: &str, violation: Formula) {
    assert!(lane(&violation).is_none(), "{label}: SATISFIABLE — the lane must refuse");
    assert!(producer(&violation).is_none(), "{label}: SATISFIABLE — the producer must refuse");
}

/// `fn guard(bit: u32) -> bool { bit < 64 }` in PRE-optimization MIR:
/// `_2 = copy _1; _0 = Lt(move _2, 64)`, checked against `_0 == (bit < 64)`.
fn guard_preopt(claim_bound: i128) -> Formula {
    Formula::And(vec![
        eq(int("_2"), int("bit")),
        eq(boolv("_0"), lt(int("_2"), lit(64))),
        not(eq(boolv("_0"), lt(int("bit"), lit(claim_bound)))),
    ])
}

#[test]
fn preopt_guard_alias_is_eliminated_in_the_kernel() {
    assert_certifies("guard(pre-opt)", guard_preopt(64));
}

#[test]
fn preopt_guard_with_a_wrong_bound_is_refused() {
    // bit = 64: _2 = 64, _0 = false, and (bit < 65) = true, so _0 ⟺ … fails.
    assert_refused("guard(pre-opt, claims bit < 65)", guard_preopt(65));
}

#[test]
fn an_alias_to_a_different_variable_is_refused() {
    // _2 = other, not bit: other = 0, bit = 100 makes _0 = true, bit < 64 false.
    let violation = Formula::And(vec![
        eq(int("_2"), int("other")),
        eq(boolv("_0"), lt(int("_2"), lit(64))),
        not(eq(boolv("_0"), lt(int("bit"), lit(64)))),
    ]);
    assert_refused("alias to another variable", violation);
}

/// A two-step chain in both orientations (`_3 = _2`, `bit = _2`): the class
/// proof is an `Eq.trans`/`Eq.symm` path, re-checked by the kernel.
#[test]
fn an_alias_chain_is_transported() {
    let violation = Formula::And(vec![
        eq(int("_3"), int("_2")),
        eq(int("bit"), int("_2")),
        eq(boolv("_0"), lt(int("_3"), lit(64))),
        not(eq(boolv("_0"), lt(int("bit"), lit(64)))),
    ]);
    assert_certifies("alias chain", violation);
}

/// `fn band(a: bool, b: bool) -> bool { a & b }` pre-opt: two BOOL aliases.
#[test]
fn preopt_bool_aliases_are_eliminated() {
    let violation = Formula::And(vec![
        eq(boolv("_3"), boolv("a")),
        eq(boolv("_4"), boolv("b")),
        eq(boolv("_0"), Formula::And(vec![boolv("_3"), boolv("_4")])),
        not(eq(boolv("_0"), Formula::And(vec![boolv("a"), boolv("b")]))),
    ]);
    assert_certifies("band(pre-opt)", violation);
}

/// `fn g_not(b: u32) -> bool { let t = b < 64; !t }`: a Bool DEFINITION.
fn g_not(claim: Formula) -> Formula {
    Formula::And(vec![
        eq(boolv("_2"), lt(int("b"), lit(64))),
        eq(boolv("_0"), not(boolv("_2"))),
        not(eq(boolv("_0"), claim)),
    ])
}

#[test]
fn a_bool_definition_is_rewritten_with_propext() {
    assert_certifies("g_not", g_not(not(lt(int("b"), lit(64)))));
}

#[test]
fn a_negated_bool_definition_claim_is_refused() {
    // b = 0: _2 = true, _0 = false, claim (b < 64) = true.
    assert_refused("g_not claims b < 64", g_not(lt(int("b"), lit(64))));
}

/// `nz`'s first path (`d == 0`, returns 1) against the diamond's implication
/// pair — the shape the generator's `Ite` elimination emits.
fn nz_path(d_is_zero: bool, swapped: bool) -> Formula {
    let d0 = eq(int("d"), lit(0));
    let (then_val, else_val) = if swapped { (int("d"), lit(1)) } else { (lit(1), int("d")) };
    let claim = Formula::And(vec![
        implies(not(d0.clone()), eq(int("_0"), else_val)),
        implies(not(not(d0.clone())), eq(int("_0"), then_val)),
    ]);
    let (guard, ret) = if d_is_zero {
        (d0.clone(), eq(int("_0"), lit(1)))
    } else {
        (not(d0.clone()), eq(int("_0"), int("d")))
    };
    Formula::And(vec![
        Formula::Bool(true),
        eq(boolv("_3"), d0),
        guard,
        eq(int("_2#s1_0"), int("_0")),
        eq(int("_0"), int("_2#s1_0_s2_0")),
        ret,
        not(claim),
    ])
}

#[test]
fn diamond_paths_certify() {
    assert_certifies("nz path d == 0", nz_path(true, false));
    assert_certifies("nz path d != 0", nz_path(false, false));
}

#[test]
fn a_swapped_diamond_is_refused_on_both_paths() {
    // d = 0 returns 1, but the swapped claim wants d there (1 != 0);
    // d = 5 returns 5, but the swapped claim wants 1.
    assert_refused("swapped nz, d == 0", nz_path(true, true));
    assert_refused("swapped nz, d != 0", nz_path(false, true));
}

/// Two distinct literals in one class are the refutation (`x = 1 ∧ y = x ∧ y = 2`).
#[test]
fn two_literals_in_one_class_refute() {
    let violation = Formula::And(vec![
        eq(int("x"), lit(1)),
        eq(int("y"), int("x")),
        eq(int("y"), lit(2)),
        boolv("unrelated"),
    ]);
    assert!(lane(&violation).is_some(), "x = 1 = y = 2 is unsatisfiable");
}

/// Forward chaining through an implication: `¬c → r = 1` with `¬c` known.
#[test]
fn modus_ponens_feeds_the_evaluation() {
    let violation = Formula::And(vec![
        not(eq(int("x"), lit(0))),
        eq(boolv("_5"), eq(int("x"), lit(0))),
        implies(not(boolv("_5")), eq(int("r"), lit(1))),
        not(implies(not(eq(int("x"), lit(0))), eq(int("r"), lit(1)))),
    ]);
    assert_certifies("modus ponens", violation);
    // Without the premise it is satisfiable (x = 0, r = 7).
    let satisfiable = Formula::And(vec![
        eq(boolv("_5"), eq(int("x"), lit(0))),
        implies(not(boolv("_5")), eq(int("r"), lit(1))),
        not(implies(Formula::Bool(true), eq(int("r"), lit(1)))),
    ]);
    assert_refused("no premise", satisfiable);
}

/// Unencodable conjuncts are DROPPED (a weakening), never guessed at.
#[test]
fn unencodable_conjuncts_are_dropped_not_read() {
    let bv = Formula::BvULt(
        Box::new(Formula::Var("w".into(), Sort::BitVec(8))),
        Box::new(Formula::BitVec { value: 3, width: 8 }),
        8,
    );
    let mut conjuncts = match guard_preopt(64) {
        Formula::And(cs) => cs,
        _ => unreachable!(),
    };
    conjuncts.push(bv);
    assert!(lane(&Formula::And(conjuncts)).is_some(), "the BV conjunct is irrelevant");
    // …and dropping one can only lose a refutation: with the alias itself
    // spelled outside the fragment the lane has nothing to rewrite with.
    let violation = Formula::And(vec![
        eq(
            Formula::Var("_2".into(), Sort::BitVec(32)),
            Formula::Var("bit".into(), Sort::BitVec(32)),
        ),
        eq(boolv("_0"), lt(int("_2"), lit(64))),
        not(eq(boolv("_0"), lt(int("bit"), lit(64)))),
    ]);
    assert!(lane(&violation).is_none(), "an unreadable alias must not be assumed");
}

/// The injectivity gate: one name at two sorts shares no skolem.
#[test]
fn a_name_at_two_sorts_declines() {
    let conjuncts = [eq(int("x"), lit(1)), boolv("x")];
    let refs: Vec<&Formula> = conjuncts.iter().collect();
    assert!(injective_skolems(&refs).is_none());
    let fine = [eq(int("x"), lit(1)), boolv("y")];
    let refs: Vec<&Formula> = fine.iter().collect();
    assert_eq!(injective_skolems(&refs), Some(BTreeSet::from(["x".into(), "y".into()])));
}

/// A purely propositional SATISFIABLE pool: nothing to refute.
#[test]
fn a_satisfiable_propositional_pool_is_refused() {
    let violation = Formula::And(vec![
        eq(boolv("p"), boolv("q")),
        implies(boolv("q"), boolv("r")),
        not(boolv("r")),
    ]);
    // p = q = r = false.
    assert_refused("p ⟺ q, q → r, ¬r", violation);
}

/// Closed arithmetic after rewriting, both polarities, including a negative
/// literal and a strict order the kernel must reduce.
#[test]
fn closed_atoms_after_rewriting() {
    // x = -1 ∧ ¬((x < 0 → x = -1) ∧ (0 ≤ x → x = 3)): x = -1 makes both hold.
    let violation = Formula::And(vec![
        eq(int("x"), lit(-1)),
        not(Formula::And(vec![
            implies(lt(int("x"), lit(0)), eq(int("x"), lit(-1))),
            implies(Formula::Le(Box::new(lit(0)), Box::new(int("x"))), eq(int("x"), lit(3))),
        ])),
    ]);
    assert!(lane(&violation).is_some(), "closed evaluation after x := -1");
    // …and x = 5 makes the second implication false: satisfiable.
    let satisfiable = Formula::And(vec![
        eq(int("x"), lit(5)),
        not(Formula::And(vec![
            implies(lt(int("x"), lit(0)), eq(int("x"), lit(-1))),
            implies(Formula::Le(Box::new(lit(0)), Box::new(int("x"))), eq(int("x"), lit(3))),
        ])),
    ]);
    assert!(lane(&satisfiable).is_none(), "x = 5 is a model");
}

/// The cost caps are real: the same refutable core padded past `MAX_POOL`
/// top-level conjuncts is declined before any rewriting.
#[test]
fn a_pool_past_the_cap_is_declined() {
    let Formula::And(mut conjuncts) = guard_preopt(64) else { unreachable!() };
    let core = conjuncts.len();
    for i in 0..(MAX_POOL - core) {
        conjuncts.push(boolv(&format!("pad{i}")));
    }
    assert!(lane(&Formula::And(conjuncts.clone())).is_some(), "at the cap it still certifies");
    conjuncts.push(boolv("one_too_many"));
    assert!(lane(&Formula::And(conjuncts)).is_none(), "past the cap it must decline");
}

/// A CASE SPLIT with a RESTART: the caller-side shape of a diamond helper's
/// lemma (`x / nz(d)`), measured from the vcgen composition. Refuting it needs
/// `Classical.em (d = 0)`, and in each branch an equality chaining derives
/// (`_3 = d`, `_3 = 1`) joined with the rewritten unit `_3 = 0`.
fn div_nz_caller(else_value: Formula) -> Formula {
    let d0 = eq(int("d"), lit(0));
    Formula::And(vec![
        Formula::Ge(Box::new(int("d")), Box::new(lit(0))),
        implies(not(d0.clone()), eq(int("_3"), else_value)),
        implies(not(not(d0)), eq(int("_3"), lit(1))),
        eq(boolv("_4"), eq(int("_3"), lit(0))),
        boolv("_4"),
    ])
}

#[test]
fn a_case_split_refutes_the_diamond_caller() {
    assert_certifies("x / nz(d)", div_nz_caller(int("d")));
}

#[test]
fn a_case_split_never_refutes_a_satisfiable_caller() {
    // `nz` returning `d - d`-like 0 on the else arm: d = 5, _3 = 0 is a model.
    assert_refused("x / bad_nz(d)", div_nz_caller(lit(0)));
}

/// A literal-`false` violation is a producer placeholder (an unlowered contract
/// predicate carries it — measured on `#[trust::invariant(x > 0)]`, 2026-09-25) or
/// an already-discharged row: the lane must mint no authority for it, alone or
/// beside real conjuncts. A closed pool (no variable) is not this lane's either.
#[test]
fn a_placeholder_false_or_closed_pool_is_declined() {
    assert!(lane(&Formula::Bool(false)).is_none(), "bare `false` placeholder");
    assert!(
        lane(&Formula::And(vec![eq(int("x"), lit(0)), Formula::Bool(false)])).is_none(),
        "`false` beside a real conjunct"
    );
    assert!(lane(&not(eq(lit(1), lit(1)))).is_none(), "closed pool");
    // Positive control: the same lane still certifies an open refutation.
    let guard = Formula::And(vec![
        eq(int("_2"), int("bit")),
        eq(boolv("_0"), lt(int("_2"), lit(64))),
        not(eq(boolv("_0"), lt(int("bit"), lit(64)))),
    ]);
    assert!(lane(&guard).is_some(), "the pre-optimization guard shape still certifies");
}

#[test]
fn proof_dependency_walk_visits_shared_dag_without_expanding_every_path() {
    use std::sync::Arc;

    use clean_kernel::expr::ExprKind;

    let left = FVarId::new(71);
    let right = FVarId::new(72);
    let mut proof = Arc::new(Expr::app(Expr::fvar(left), Expr::fvar(right)));
    // Expanding the two edges separately would visit more than 2^80 paths.
    // Both distinct dependencies must still be collected from the shared leaf.
    for _ in 0..80 {
        proof = Arc::new(Expr::from(ExprKind::App(proof.clone(), proof)));
    }
    let mut dependencies = FxHashSet::default();
    assert_eq!(proof_free_variables(&proof, &mut dependencies), Some(()));
    assert_eq!(dependencies, FxHashSet::from_iter([left, right]));
}

#[test]
fn wave496_const_arith_redex_gate_matches_fold_constant_arith_opt_exactly() {
    let cases = [
        lt(int("x"), lit(10)),
        lt(Formula::Mul(Box::new(int("x")), Box::new(lit(4))), lit(64)),
        Formula::Or(vec![
            lt(Formula::Mul(Box::new(lit(4096)), Box::new(lit(64))), lit(0)),
            Formula::Gt(
                Box::new(Formula::Mul(Box::new(lit(4096)), Box::new(lit(64)))),
                Box::new(lit(1_000_000)),
            ),
        ]),
        eq(
            int("r"),
            Formula::Add(
                Box::new(Formula::Sub(Box::new(lit(9)), Box::new(lit(4)))),
                Box::new(int("x")),
            ),
        ),
        eq(int("r"), Formula::Neg(Box::new(lit(-7)))),
        // Overflowing i128 extremes are NOT foldable redexes.
        eq(int("r"), Formula::Add(Box::new(lit(i128::MAX)), Box::new(lit(1)))),
        eq(int("r"), Formula::Neg(Box::new(lit(i128::MIN)))),
        // Implies is outside fold_constant_arith_opt's spine.
        implies(eq(Formula::Add(Box::new(lit(1)), Box::new(lit(2))), lit(3)), boolv("p")),
    ];
    for f in &cases {
        assert_eq!(
            crate::formula_has_const_arith_redex(f),
            crate::fold_constant_arith_opt(f).is_some(),
            "redex gate must match fold_constant_arith_opt on {f:?}"
        );
    }
}

#[test]
fn wave496_on_certify_stack_if_needed_reuses_active_stack_and_scopes_stops() {
    use trust_types::determinism::StopCause;

    let caller_tid = std::thread::current().id();
    let ((), outer_stop) = crate::with_stop_scope(|| {
        let hopped_tid = crate::on_certify_stack(|| {
            let stack_tid = std::thread::current().id();
            assert_ne!(stack_tid, caller_tid, "outer on_certify_stack must hop threads");
            crate::note_certify_stop(StopCause::Effort);
            let nested = crate::on_certify_stack_if_needed(|| {
                assert_eq!(
                    std::thread::current().id(),
                    stack_tid,
                    "nested on_certify_stack_if_needed must stay on active 256 MiB thread"
                );
                assert_eq!(
                    crate::RUN_STOP.with(std::cell::Cell::get),
                    None,
                    "nested scope starts with clean RUN_STOP just like a worker hop"
                );
                crate::note_certify_stop(StopCause::Unclassified);
                Some(42usize)
            });
            assert_eq!(nested, Some(42));
            assert_eq!(
                crate::RUN_STOP.with(std::cell::Cell::get),
                Some(StopCause::Unclassified),
                "least-reproducible inner stop combines back into enclosing scope"
            );
            Some(stack_tid)
        });
        assert!(hopped_tid.is_some());
    });
    assert_eq!(outer_stop, Some(StopCause::Unclassified));
}

#[test]
fn wave496_kb_neg_and_flipped_int_eq_lookup_and_cow_subst_leaf_preserve_proofs() {
    // Flipped Int equality & negated Int equality in Kb::lookup + untouched subtree sharing:
    let untouched = Formula::Or((0..20).map(|i| lt(int(&format!("u_{i}")), lit(i))).collect());
    let f = Formula::And(vec![untouched.clone(), lt(int("target"), lit(5))]);
    let rewritten = subst_leaf(&f, "target", &Sort::Int, &lit(10));
    assert_eq!(
        rewritten,
        Formula::And(vec![untouched, lt(lit(10), lit(5))]),
        "copy-on-write subst_leaf must match exact substitution"
    );
    assert_eq!(subst_leaf(&f, "absent", &Sort::Int, &lit(0)), f);

    // Flipped Int disequality refutation inside implication: `b = a` refuted via `¬(a = b)`.
    let violation = Formula::And(vec![
        not(eq(int("a"), int("b"))),
        implies(not(eq(int("b"), int("a"))), eq(int("r"), lit(1))),
        not(eq(int("r"), lit(1))),
    ]);
    assert_certifies("flipped negated Int eq lookup", violation);

    // Wide disjunction common-conjunct extraction (> 16 conjuncts per arm) + retain_new_atoms:
    let make_arm = |tag: i128| {
        let mut arm: Vec<Formula> = (0..20).map(|i| lt(int(&format!("p_{tag}_{i}")), lit(100))).collect();
        arm.push(eq(int("shared"), lit(7)));
        Formula::And(arm)
    };
    let or = Formula::Or(vec![make_arm(0), make_arm(1), make_arm(2)]);
    let view = [&or];
    assert_eq!(crate::extract_disjunction_common_conjuncts(&view), vec![eq(int("shared"), lit(7))]);
    let base_atoms: Vec<Formula> = (0..20).map(|i| eq(int(&format!("v_{i}")), lit(i))).collect();
    let base_refs: Vec<&Formula> = base_atoms.iter().collect();
    let emitted = vec![
        eq(int("v_3"), lit(3)),
        eq(int("fresh"), lit(99)),
        eq(int("fresh"), lit(99)),
    ];
    assert_eq!(crate::retain_new_atoms(&base_refs, emitted), vec![eq(int("fresh"), lit(99))]);
}
