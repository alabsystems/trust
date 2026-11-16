//! The gate's solver bounds (DECISION_QUEUE BUDGET-1): one deterministic
//! effort count per query, sized by `trust_types::determinism` over the one
//! formula each route asserts and observed as sent (`record_gate_efforts`), and
//! a wall clock behind it whose expiry is reported as `wall-backstop`. The
//! loop-cut route's own check is `call_event/loop_cut/tests.rs`
//! `l0_each_query_sends_the_gate_count_over_not_m_equals_s`.

use super::*;

/// The largest prime below 2^62.
const PRIME_BELOW_2_62: i128 = (1 << 62) - 57;

fn bv32(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::BitVec(32))
}

/// `x * y == P` with `1 < x, y < 2^32` and `P` prime: no such factors exist,
/// so `NOT` of it is valid, but ay must refute a 64-bit multiplier to see it,
/// far more than a handful of conflicts. `discharge_valid` asserts the
/// negation of its argument, so the claim it is handed is `NOT` of this.
fn factors_of_a_prime() -> Formula {
    let one = || b(Formula::BitVec { value: 1, width: 32 });
    let product = Formula::BvMul(
        b(Formula::BvZeroExt(b(bv32("x")), 32)),
        b(Formula::BvZeroExt(b(bv32("y")), 32)),
        64,
    );
    Formula::And(vec![
        Formula::Eq(b(product), b(Formula::BitVec { value: PRIME_BELOW_2_62, width: 64 })),
        Formula::BvULt(one(), b(bv32("x")), 32),
        Formula::BvULt(one(), b(bv32("y")), 32),
    ])
}

fn unknown_reason(outcome: Discharge) -> String {
    match outcome {
        Discharge::Unknown(reason) => reason,
        other => panic!("expected Unknown, got {other:?}"),
    }
}

/// The gate sizes its count with the verifier's own formula over the assertion
/// it makes: `NOT(f)` for a validity check, `pre AND NOT(a == c)` for an
/// equality. No second formula: a change to `EffortScale` moves both.
#[test]
fn the_gate_effort_is_the_verifiers_count_over_the_asserted_formula() {
    let f = factors_of_a_prime();
    let asserted = Formula::Not(b(f.clone()));
    let size = trust_types::determinism::query_size(&[&asserted]);
    assert!(size > 1, "{size}");
    assert_eq!(
        gate_query_effort(&asserted).expect("default scale"),
        EffortScale::BUILTIN.for_query(&[&asserted])
    );
    let one = EffortScale::parse("1").expect("k = 1");
    let effort = with_gate_effort(one, || gate_query_effort(&asserted)).expect("k = 1");
    assert_eq!((effort.size, effort.conflicts), (size, size));
    let most = EffortScale::parse(&EffortScale::CEILING.to_string()).expect("k = C");
    let effort = with_gate_effort(most, || gate_query_effort(&asserted)).expect("k = C");
    assert_eq!(effort.conflicts, EffortScale::CEILING, "the ceiling clamps every query");
    // The seam is restored on return.
    assert_eq!(
        gate_query_effort(&asserted).expect("default"),
        EffortScale::BUILTIN.for_query(&[&asserted])
    );
}

/// A clock far past anything the count lets the factoring query run, so that a
/// query the count does not stop (the count never sent, say) fails this test on
/// its reason, `[stop:wall-backstop]`, in about this long, instead of running
/// unbounded. Under its count the query ends in milliseconds.
const FAR_BACKSTOP_MS: u64 = 60_000;

/// One factoring query under `k = 1` behind [`FAR_BACKSTOP_MS`], asserted to end
/// on ay's deterministic count, not the clock.
fn factoring_stops_on_effort(run: impl FnOnce() -> Discharge) -> String {
    let one = EffortScale::parse("1").expect("k = 1");
    let reason =
        with_gate_budget_ms(FAR_BACKSTOP_MS, || with_gate_effort(one, || unknown_reason(run())));
    assert_eq!(StopCause::from_reason(&reason), Some(StopCause::Effort), "{reason}");
    assert!(reason.ends_with("[stop:effort]"), "{reason}");
    assert!(reason.contains("(ay reason resource_limit)"), "{reason}");
    reason
}

/// A query that needs more conflicts than its count gives it is Unknown on the
/// COUNT, never the clock, and ends with the same reason on every run.
#[test]
fn a_query_past_its_count_is_unknown_on_effort_identically() {
    let f = factors_of_a_prime();
    let no_factors = Formula::Not(b(f.clone()));
    let runs: Vec<String> =
        (0..3).map(|_| factoring_stops_on_effort(|| discharge_valid(&no_factors))).collect();
    assert!(runs.iter().all(|r| *r == runs[0]), "{runs:#?}");
    // The equality form, `pre AND NOT(a == c)`: with `pre` the factoring
    // claim and `a == c` false, the assertion is `pre` itself.
    let (zero, one_bit) =
        (Formula::BitVec { value: 0, width: 1 }, Formula::BitVec { value: 1, width: 1 });
    let equal_runs: Vec<String> = (0..2)
        .map(|_| factoring_stops_on_effort(|| discharge_equal_pre(&zero, &one_bit, Some(&f))))
        .collect();
    assert_eq!(equal_runs[0], equal_runs[1]);
}

/// The scales the per-route checks below run under: the default, and two set
/// through the test seam, each far below the ceiling for these small queries
/// so that `k` and the size both show in the count sent.
fn scales() -> Vec<Option<EffortScale>> {
    vec![
        None,
        Some(EffortScale::parse("1").expect("k = 1")),
        Some(EffortScale::parse("7").expect("k = 7")),
    ]
}

/// `body` under `scale` (the default when `None`), with every `:rlimit` it
/// handed to ay, and the scale that was in force.
fn sent_under<R>(
    scale: Option<EffortScale>,
    body: impl FnOnce() -> R,
) -> (R, Vec<QueryEffort>, EffortScale) {
    match scale {
        Some(k) => {
            let (r, sent) = with_gate_effort(k, || record_gate_efforts(body));
            (r, sent, k)
        }
        None => {
            let (r, sent) = record_gate_efforts(body);
            (r, sent, EffortScale::BUILTIN)
        }
    }
}

/// `x <u 5` over the 32-bit `x`: a precondition with terms of its own, so a
/// count sized without it is smaller.
fn x_below_five() -> Formula {
    Formula::BvULt(b(bv32("x")), b(Formula::BitVec { value: 5, width: 32 }), 32)
}

/// The validity route sends exactly one `:rlimit`, sized by the scale in
/// force over `NOT(f)`, the one formula it asserts, and the verdict is ay's.
#[test]
fn the_validity_route_sends_the_count_over_not_f() {
    let x = bv32("x");
    let f = Formula::Eq(
        b(Formula::BvAdd(b(x.clone()), b(Formula::BitVec { value: 0, width: 32 }), 32)),
        b(x.clone()),
    );
    let asserted = Formula::Not(b(f.clone()));
    for scale in scales() {
        let (outcome, sent, k) = sent_under(scale, || discharge_valid(&f));
        assert!(matches!(outcome, Discharge::Proven), "{outcome:?}");
        let want = k.for_query(&[&asserted]);
        assert!(want.conflicts < EffortScale::CEILING, "{want:?}");
        assert_eq!(sent, vec![want], "k = {}", k.conflicts_per_node);
    }
}

/// The equality route sends exactly one `:rlimit`, sized by the scale in force
/// over `pre AND NOT(a == c)` with a precondition and over `NOT(a == c)`
/// without one, on a proof and on a counterexample alike.
#[test]
fn the_equality_route_sends_the_count_over_pre_and_not_equal() {
    let x = bv32("x");
    let plus =
        |n: i128| Formula::BvAdd(b(x.clone()), b(Formula::BitVec { value: n, width: 32 }), 32);
    let pre = x_below_five();
    for scale in scales() {
        for (a, proven) in [(plus(0), true), (plus(1), false)] {
            let differ = Formula::Not(b(Formula::Eq(b(a.clone()), b(x.clone()))));
            let with_pre = Formula::And(vec![pre.clone(), differ.clone()]);
            assert!(
                trust_types::determinism::query_size(&[&with_pre])
                    > trust_types::determinism::query_size(&[&differ]),
                "the precondition adds terms"
            );
            for (pre, asserted) in [(Some(&pre), with_pre), (None, differ)] {
                let (outcome, sent, k) = sent_under(scale, || discharge_equal_pre(&a, &x, pre));
                assert_eq!(
                    matches!(outcome, Discharge::Proven),
                    proven,
                    "{outcome:?} (pre {})",
                    pre.is_some()
                );
                let want = k.for_query(&[&asserted]);
                assert!(want.conflicts < EffortScale::CEILING, "{want:?}");
                assert_eq!(sent, vec![want], "k = {}, pre {}", k.conflicts_per_node, pre.is_some());
            }
        }
    }
}

/// The same query given the most effort but an artificially tiny clock is
/// ended by the CLOCK, and says so: `wall-backstop`, never a plain Unknown and
/// never `effort`.
#[test]
fn a_query_the_clock_ends_is_reported_as_wall_backstop() {
    let most = EffortScale::parse(&EffortScale::CEILING.to_string()).expect("k = C");
    let no_factors = Formula::Not(b(factors_of_a_prime()));
    let reason = with_gate_budget_ms(1, || {
        with_gate_effort(most, || unknown_reason(discharge_valid(&no_factors)))
    });
    assert_eq!(StopCause::from_reason(&reason), Some(StopCause::WallBackstop), "{reason}");
    assert!(reason.ends_with("[stop:wall-backstop]"), "{reason}");
    assert!(reason.contains("the wall-clock backstop (1 ms)"), "{reason}");
}

/// Controls: an easy valid query is Proven and an easy invalid one a
/// counterexample under the default count and clock, so the count only ever
/// ends a search that has not decided.
#[test]
fn easy_queries_are_decided_under_the_count() {
    let x = bv32("x");
    let x_plus_zero = Formula::BvAdd(b(x.clone()), b(Formula::BitVec { value: 0, width: 32 }), 32);
    assert!(matches!(discharge_equal_pre(&x_plus_zero, &x, None), Discharge::Proven));
    let x_plus_one = Formula::BvAdd(b(x.clone()), b(Formula::BitVec { value: 1, width: 32 }), 32);
    assert!(matches!(discharge_equal_pre(&x_plus_one, &x, None), Discharge::CounterExample));
}
