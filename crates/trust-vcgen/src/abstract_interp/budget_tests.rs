// trust_vcgen/abstract_interp/budget_tests.rs: the interval fixpoint under the
// ambient per-function budget, and the cost of its call havoc.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// Trust (2026-10-02, trust-fixpoint-deadline). The interval fixpoint
// (`transfer::fixpoint_configured`, behind `merged_interval_environment`) polled no
// budget and re-derived and string-scanned every call block's havoc set at every
// visit; on aterm-census `run_lock_order_census` at `-Zmir-opt-level=2` it ran 226 s
// past the function's 120 s budget. Pinned here, deterministically (step counts and
// the work counters of `AnalysisMemoStats`, never a wall clock):
//
// * a trip REFUSES — every block Top and reachable, the merged environment empty —
//   whether the step half or the clock half tripped, and whether the trip happened
//   during the run or before it began; the refusal is not remembered;
// * the run stops within its step budget, and does no unit of work at all once the
//   deadline has passed;
// * each call block's havoc is derived ONCE per run however often the block is
//   visited (and, under `cfg(test)`, every visit re-derives it and every per-name
//   answer of the index is compared with the `write_rebinds` scan it replaced — see
//   `transfer::CallHavoc`);
// * (added at landing, from the review's planted defects) EVERY step budget answers
//   the control or the refusal, whichever phase it trips in; a trip that lands after
//   the last poll, inside a unit's own work, is still refused by the final budget
//   read; and a REFINED call havoc forgets what its refined list names;
// * (added at landing on main de6288dddf, 2026-10-08, whose havoc rules had moved
//   under this change) an ESCAPE-arm call forgets the kept part of the whole-function
//   list, through one index per run; and an OPAQUE terminator forgets every local.

use std::time::Instant;

use trust_types::verify_budget::{VerifyBudgetGuard, exhausted_readonly};
use trust_types::*;

use super::transfer::{FixpointConfig, FixpointResult, fixpoint_configured};
use super::{Interval, merged_interval_environment, type_aware_initial_state};
use crate::fn_memo::{analysis_memo_stats, reset_analysis_memo_stats};

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

/// `opaque(copy r, copy p) -> t_i`: `p` is a `&mut`, so the call is not a
/// pure-value call and havocs the whole-function list (`c`, which `p` borrows, and
/// `p` itself) besides its destination; `r` is in neither.
fn call(dest: usize, target: usize) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: None,
        is_foreign: false,
        func: "test::opaque".to_string(),
        args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(4))],
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
    }
}

/// `abstract_interp::tests::bottom_tested_loop(5)` — `loop { r += 1; if r > 5 {
/// break } }`, whose loop head the fixpoint bounds by the break test — with a chain
/// of `n` calls between the head and the test, in the same block order:
///
/// ```text
/// bb0:            r = 0; c = 0; p = &mut c                 -> bb1
/// bb1 (head):     _2 = CheckedAdd(r, 1)  Assert(!_2.1)     -> bb4
/// bb2:            _0 = _2.0  Return
/// bb3:            r = _2.0                                 -> bb1 (the back edge)
/// bb4 .. bb4+n-1: t_i = opaque(copy r, copy p)             -> the next block
/// bb4+n:          _3 = Gt(_2.0, 5)  SwitchInt(_3): 0 -> bb3, else -> bb2
/// ```
///
/// With `n == 0` this is `bottom_tested_loop(5)` block for block. No new constant
/// joins the threshold set (`0`, `1`, `5` are already there).
fn call_loop(n: usize) -> VerifiableFunction {
    assert!(n >= 1);
    let local =
        |index: usize, ty: Ty, name: &str| LocalDecl { index, ty, name: Some(name.to_string()) };
    let first_dest = 6;
    let test_block = 4 + n;
    let mut locals = vec![
        local(0, u32_ty(), "_0"),
        local(1, u32_ty(), "r"),
        local(2, Ty::Tuple(vec![u32_ty(), Ty::Bool]), "_2"),
        local(3, Ty::Bool, "_3"),
        local(4, Ty::Ref { mutable: true, inner: Box::new(u32_ty()) }, "p"),
        local(5, u32_ty(), "c"),
    ];
    for i in 0..n {
        locals.push(local(first_dest + i, u32_ty(), &format!("t{i}")));
    }
    let sum = Place { local: 2, projections: vec![Projection::Field(0)] };
    let overflowed = Place { local: 2, projections: vec![Projection::Field(1)] };
    let mut blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(1), Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32)))),
                assign(Place::local(5), Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32)))),
                assign(Place::local(4), Rvalue::Ref { mutable: true, place: Place::local(5) }),
            ],
            terminator: Terminator::Goto(BlockId(1)),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(
                Place::local(2),
                Rvalue::CheckedBinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Uint(1, 32)),
                ),
            )],
            terminator: Terminator::Assert {
                cond: Operand::Move(overflowed),
                expected: false,
                msg: AssertMessage::Overflow(BinOp::Add),
                target: BlockId(4),
                unwind: UnwindEdge::Unreachable,
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(sum.clone())))],
            terminator: Terminator::Return,
        },
        BasicBlock {
            id: BlockId(3),
            stmts: vec![assign(Place::local(1), Rvalue::Use(Operand::Copy(sum.clone())))],
            terminator: Terminator::Goto(BlockId(1)),
        },
    ];
    for i in 0..n {
        blocks.push(BasicBlock {
            id: BlockId(4 + i),
            stmts: vec![],
            terminator: call(first_dest + i, 4 + i + 1),
        });
    }
    blocks.push(BasicBlock {
        id: BlockId(test_block),
        stmts: vec![assign(
            Place::local(3),
            Rvalue::BinaryOp(
                BinOp::Gt,
                Operand::Copy(sum),
                Operand::Constant(ConstValue::Uint(5, 32)),
            ),
        )],
        terminator: Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(3)),
            targets: vec![(0, BlockId(3))],
            otherwise: BlockId(2),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        },
    });
    VerifiableFunction {
        name: "call_loop".to_string(),
        def_path: format!("test::call_loop_{n}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 0,
            return_ty: u32_ty(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn run(func: &VerifiableFunction) -> FixpointResult {
    fixpoint_configured(func, type_aware_initial_state(func), &FixpointConfig::for_function(func))
}

/// One block's state as a comparable row: its id, whether it is unreachable, and
/// its tracked entries.
type BlockRow = (usize, bool, Vec<(String, Interval)>);

/// The block states as a comparable, ordered list.
fn states(result: &FixpointResult) -> Vec<BlockRow> {
    let mut out: Vec<_> = result
        .block_states
        .iter()
        .map(|(id, s)| {
            (id.0, s.is_unreachable, s.vars.iter().map(|(k, v)| (k.clone(), *v)).collect())
        })
        .collect();
    out.sort_by_key(|(id, ..)| *id);
    out
}

/// The refusal: one state per block, every one Top (no tracked entry) and reachable.
fn assert_refused(func: &VerifiableFunction, result: &FixpointResult, why: &str) {
    assert_eq!(result.block_states.len(), func.body.blocks.len(), "{why}: one state per block");
    for (id, state) in &result.block_states {
        assert!(!state.is_unreachable, "{why}: bb{} was claimed unreachable", id.0);
        assert!(state.vars.is_empty(), "{why}: bb{} kept {:?}", id.0, state.vars);
    }
}

/// The loop head's interval for `r`, which the control bounds by the break test.
fn head_r(fp: &FixpointResult) -> Interval {
    fp.block_states[&BlockId(1)].get("r")
}

#[test]
fn the_control_bounds_the_counter_and_derives_each_call_havoc_once() {
    for n in [1usize, 8] {
        let func = call_loop(n);
        reset_analysis_memo_stats();
        let fp = run(&func);
        let stats = analysis_memo_stats();
        // The answer the budget tests below must NOT give: the head bounds the
        // counter (no call havocs `r`), so a refusal is observable.
        let r = head_r(&fp);
        assert!(
            r.lo >= 0 && r.hi <= 5,
            "n={n}: the loop head must bound r by the break test, got {r:?}; states {:?}",
            states(&fp)
        );
        assert!(!fp.block_states[&BlockId(4)].is_unreachable, "n={n}: the chain is reachable");
        // Every call block is visited several times in one run (ascending pops,
        // narrowing, repair) ...
        assert!(
            stats.interval_fixpoint_units > 3 * (n as u64 + 5),
            "ANTI-VACUITY: {} units for {} blocks",
            stats.interval_fixpoint_units,
            n + 5
        );
        // ... and its havoc is derived exactly once (before 2026-10-02: once per
        // visit, each followed by a tracked-names x havoc-names `write_rebinds`
        // scan), with the whole-function list indexed once and shared.
        assert_eq!(stats.interval_havoc_sets, n as u64, "n={n}: one derivation per call block");
        assert_eq!(
            stats.interval_function_havoc_indexes, 1,
            "n={n}: the whole-function havoc list is indexed once per run"
        );
        // `c` is in the whole-function list (`p` borrows it), so the first call
        // forgets it: the shared index is consulted, not just the destinations.
        let after_calls = &fp.block_states[&BlockId(4 + n)];
        assert!(!after_calls.is_unreachable);
        assert_eq!(after_calls.get("c"), Interval::TOP, "n={n}: the call havoc forgets `c`");
    }
}

#[test]
fn a_step_trip_refuses_and_is_not_remembered() {
    let func = call_loop(16);
    let control = states(&run(&func));
    {
        // One step: spent by the first poll, so the second refuses.
        let _budget = VerifyBudgetGuard::install(None, 1);
        reset_analysis_memo_stats();
        let fp = run(&func);
        assert!(exhausted_readonly(), "ANTI-VACUITY: the step budget must trip");
        assert_refused(&func, &fp, "one step");
        assert!(analysis_memo_stats().interval_fixpoint_units <= 1);
        let env = merged_interval_environment(&func);
        assert!(env.vars.is_empty(), "a tripped environment bounds nothing: {:?}", env.vars);
        assert!(!env.is_unreachable, "a tripped environment claims no unreachability");
    }
    // The guard restored the ambient budget: the same run answers like the control.
    assert_eq!(states(&run(&func)), control, "the refusal leaked past its budget scope");
}

#[test]
fn the_run_stops_within_its_step_budget() {
    let func = call_loop(64);
    reset_analysis_memo_stats();
    let _ = run(&func);
    let unbudgeted = analysis_memo_stats().interval_fixpoint_units;
    const STEPS: u64 = 40;
    assert!(unbudgeted > 8 * STEPS, "ANTI-VACUITY: {unbudgeted} units must outgrow {STEPS} steps");
    let _budget = VerifyBudgetGuard::install(None, STEPS);
    reset_analysis_memo_stats();
    let fp = run(&func);
    let done = analysis_memo_stats().interval_fixpoint_units;
    assert!(exhausted_readonly(), "ANTI-VACUITY: no trip");
    assert!(done <= STEPS, "the fixpoint did {done} units under a {STEPS}-step budget");
    assert_refused(&func, &fp, "step budget");
}

#[test]
fn a_passed_deadline_refuses_before_the_first_unit() {
    let func = call_loop(64);
    // A deadline that has already passed and a step budget that never runs out: only
    // the CLOCK can stop this run, and it must stop it at the first poll — not 4096
    // polls later, where `budget_exhausted` alone would first read the clock.
    let _budget = VerifyBudgetGuard::install(Some(Instant::now()), u64::MAX);
    reset_analysis_memo_stats();
    let fp = run(&func);
    let stats = analysis_memo_stats();
    assert_eq!(stats.interval_fixpoint_units, 0, "work done past the deadline");
    assert_eq!(stats.interval_havoc_sets, 0, "a havoc set derived past the deadline");
    assert!(exhausted_readonly());
    assert_refused(&func, &fp, "passed deadline");
}

#[test]
fn a_trip_before_the_run_refuses_it_at_once() {
    let func = call_loop(16);
    let _budget = VerifyBudgetGuard::install(None, 2);
    // Some earlier walk of the same function spent the budget.
    while !trust_types::verify_budget::budget_exhausted() {}
    reset_analysis_memo_stats();
    let fp = run(&func);
    assert_eq!(analysis_memo_stats().interval_fixpoint_units, 0, "work done after a trip");
    assert_refused(&func, &fp, "earlier trip");
}

#[test]
fn every_entry_point_of_the_fixpoint_refuses_on_a_trip() {
    let func = call_loop(16);
    let _budget = VerifyBudgetGuard::install(None, 1);
    let legacy = super::transfer::fixpoint(&func, type_aware_initial_state(&func));
    assert_refused(&func, &legacy, "fixpoint()");
    let narrowing =
        super::transfer::fixpoint_with_narrowing(&func, type_aware_initial_state(&func), 3);
    assert_refused(&func, &narrowing, "fixpoint_with_narrowing()");
}

#[test]
fn the_repair_pass_refuses_on_a_trip() {
    let func = call_loop(16);
    let mut fp = run(&func);
    assert!(head_r(&fp).hi <= 5, "control: the head bounds `r`, got {:?}", head_r(&fp));
    // One step: the pass's first poll spends it and its second refuses.
    let _budget = VerifyBudgetGuard::install(None, 1);
    super::transfer::repair_to_post_fixpoint(&func, &mut fp);
    assert_refused(&func, &fp, "repair_to_post_fixpoint");
}

// ---------------------------------------------------------------------------------
// Added at landing (2026-10-04) from the independent review of this change
// (review-trust-fixpoint-deadline r1): it planted 18 defects in `transfer.rs`, and the
// tests above missed four of them. Each test below is named after the defect it pins.
// ---------------------------------------------------------------------------------

/// The fixpoint as each of its three entry points runs it.
fn entry(func: &VerifiableFunction, which: u8) -> FixpointResult {
    match which {
        0 => run(func),
        1 => super::transfer::fixpoint(func, type_aware_initial_state(func)),
        _ => super::transfer::fixpoint_with_narrowing(func, type_aware_initial_state(func), 3),
    }
}

fn is_refusal(func: &VerifiableFunction, rows: &[BlockRow]) -> bool {
    rows.len() == func.body.blocks.len()
        && rows.iter().all(|(_, unreachable, vars)| !*unreachable && vars.is_empty())
}

/// `(steps, tripped, units)` for every step budget from 1 up to 8 past the first
/// budget the run fits in.
fn sweep(func: &VerifiableFunction, which: u8, control: &[BlockRow]) -> Vec<(u64, bool, u64)> {
    let mut out = Vec::new();
    let mut first_clean: Option<u64> = None;
    let mut steps = 1u64;
    loop {
        let (tripped, done, rows) = {
            let _budget = VerifyBudgetGuard::install(None, steps);
            reset_analysis_memo_stats();
            let fp = entry(func, which);
            (exhausted_readonly(), analysis_memo_stats().interval_fixpoint_units, states(&fp))
        };
        if tripped {
            assert!(
                first_clean.is_none(),
                "which={which}: a trip at {steps} steps after an untripped run at {first_clean:?}"
            );
            assert!(
                is_refusal(func, &rows),
                "which={which} steps={steps}: a TRIPPED run must answer the refusal, got {rows:?}"
            );
            assert!(done <= steps, "which={which}: {done} units counted under {steps} steps");
        } else {
            assert_eq!(
                rows, control,
                "which={which} steps={steps}: an UNTRIPPED run must answer the control"
            );
            first_clean.get_or_insert(steps);
        }
        out.push((steps, tripped, done));
        if first_clean.is_some_and(|c| steps >= c + 8) {
            break;
        }
        assert!(steps < 1_000_000, "which={which}: never untripped below 1M steps");
        steps += 1;
    }
    assert!(first_clean.is_some_and(|c| c > 1), "ANTI-VACUITY which={which}: never tripped");
    out
}

/// Review mutants M17 (a trip in a NARROWING pass returned the half-narrowed states
/// unrefused) and M02 (no narrowing poll at all, caught above only by an anti-vacuity
/// threshold): EVERY step budget, so every trip point — ascending pops, narrowing
/// passes, repair rounds — answers either the unbudgeted control exactly or the
/// refusal, never a third answer; it counts no more units than its budget; tripping
/// is monotone in the budget; and the whole sweep is reproducible. All three entry
/// points, three sizes.
#[test]
fn every_step_budget_answers_the_control_or_the_refusal() {
    for which in 0u8..3 {
        for n in [1usize, 3, 8] {
            let func = call_loop(n);
            let control = states(&entry(&func, which));
            assert!(
                !is_refusal(&func, &control),
                "ANTI-VACUITY which={which} n={n}: the control is itself all-Top"
            );
            let first = sweep(&func, which, &control);
            let second = sweep(&func, which, &control);
            assert_eq!(first, second, "which={which} n={n}: the sweep is not reproducible");
        }
    }
}

/// [`every_step_budget_answers_the_control_or_the_refusal`] through
/// `merged_interval_environment`, the production consumer: a tripped environment
/// bounds nothing and claims no unreachability.
#[test]
fn every_step_budget_environment_is_the_control_or_empty() {
    for n in [1usize, 4] {
        let func = call_loop(n);
        let control = merged_interval_environment(&func);
        assert!(!control.vars.is_empty(), "ANTI-VACUITY n={n}: the control environment is empty");
        let mut first_clean: Option<u64> = None;
        let mut steps = 1u64;
        loop {
            let (tripped, env) = {
                let _budget = VerifyBudgetGuard::install(None, steps);
                let env = merged_interval_environment(&func);
                (exhausted_readonly(), env)
            };
            if tripped {
                assert!(first_clean.is_none(), "n={n}: not monotone at {steps}");
                assert!(
                    env.vars.is_empty() && !env.is_unreachable,
                    "n={n} steps={steps}: a tripped environment must bound nothing: {:?}",
                    env.vars
                );
            } else {
                assert_eq!(env.vars, control.vars, "n={n} steps={steps}");
                assert_eq!(env.is_unreachable, control.is_unreachable, "n={n} steps={steps}");
                first_clean.get_or_insert(steps);
            }
            if first_clean.is_some_and(|c| steps >= c + 4) {
                break;
            }
            assert!(steps < 1_000_000, "n={n}: never untripped");
            steps += 1;
        }
        assert!(first_clean.is_some_and(|c| c > 1), "ANTI-VACUITY n={n}: never tripped");
    }
}

/// Trust (2026-10-09, trust-interval-drop-havoc). `merged_interval_environment` walks
/// every block once more after the fixpoint, joining the value each statement leaves
/// (`transfer::join_statement_values`). That walk is fixpoint work like any other: one
/// poll of the ambient budget per block, counted as a unit, and a trip in it answers
/// the refusal ([`every_step_budget_environment_is_the_control_or_empty`] checks every
/// budget). A budget the fixpoint alone fits in is NOT enough for the environment.
#[test]
fn the_environment_s_statement_walk_is_budgeted_fixpoint_work() {
    for n in [1usize, 4] {
        let func = call_loop(n);
        let blocks = func.body.blocks.len() as u64;
        reset_analysis_memo_stats();
        let _ = run(&func);
        let fixpoint_units = analysis_memo_stats().interval_fixpoint_units;
        reset_analysis_memo_stats();
        let control = merged_interval_environment(&func);
        let environment_units = analysis_memo_stats().interval_fixpoint_units;
        assert!(!control.vars.is_empty(), "ANTI-VACUITY n={n}: the control environment is empty");
        assert_eq!(
            environment_units,
            fixpoint_units + blocks,
            "n={n}: the statement walk is one unit per block"
        );
        // The smallest step budget each of the two finishes within.
        let first_clean = |environment: bool| -> u64 {
            let mut steps = 1u64;
            loop {
                let tripped = {
                    let _budget = VerifyBudgetGuard::install(None, steps);
                    if environment {
                        let _ = merged_interval_environment(&func);
                    } else {
                        let _ = run(&func);
                    }
                    exhausted_readonly()
                };
                if !tripped {
                    return steps;
                }
                assert!(steps < 1_000_000, "n={n}: never untripped");
                steps += 1;
            }
        };
        let fixpoint_alone = first_clean(false);
        let with_walk = first_clean(true);
        assert!(
            with_walk >= fixpoint_alone + blocks,
            "n={n}: the environment finished within {with_walk} steps, the fixpoint alone needs \
             {fixpoint_alone} and the walk polls once for each of {blocks} blocks"
        );
        // Inside the fixpoint's budget but short of the walk's: the refusal.
        let (tripped, env) = {
            let _budget = VerifyBudgetGuard::install(None, fixpoint_alone);
            let env = merged_interval_environment(&func);
            (exhausted_readonly(), env)
        };
        assert!(tripped, "n={n}: the walk did not charge the budget");
        assert!(env.vars.is_empty() && !env.is_unreachable, "n={n}: {:?}", env.vars);
    }
}

/// [`call_loop`] with a read THROUGH A REFERENCE at the end of every block:
/// `k = 3; q = &k` in `bb0`, then `d = copy (*q)` last in each block. Naming `*q`
/// resolves `q`'s referent through the referent fold, which charges the ambient
/// budget, so every unit of fixpoint work charges steps AFTER its poll passed — the
/// shape in which the fixpoint's FINAL budget read, not a poll, is what sees a trip.
fn call_loop_reading(n: usize) -> VerifiableFunction {
    let mut func = call_loop(n);
    let k = func.body.locals.len();
    let (q, d) = (k + 1, k + 2);
    let local =
        |index: usize, ty: Ty, name: &str| LocalDecl { index, ty, name: Some(name.to_string()) };
    func.body.locals.push(local(k, u32_ty(), "k"));
    func.body.locals.push(local(q, Ty::Ref { mutable: false, inner: Box::new(u32_ty()) }, "q"));
    func.body.locals.push(local(d, u32_ty(), "d"));
    func.body.blocks[0].stmts.extend([
        assign(Place::local(k), Rvalue::Use(Operand::Constant(ConstValue::Uint(3, 32)))),
        assign(Place::local(q), Rvalue::Ref { mutable: false, place: Place::local(k) }),
    ]);
    let read = Place { local: q, projections: vec![Projection::Deref] };
    for block in &mut func.body.blocks {
        block.stmts.push(assign(Place::local(d), Rvalue::Use(Operand::Copy(read.clone()))));
    }
    func.def_path = format!("test::call_loop_reading_{n}");
    func
}

/// Review mutants M05 / M06 (the final `exhausted_readonly` read of
/// `fixpoint_configured` / `fixpoint` removed): no test observed them, because the
/// fixpoint's poll is `budget_exhausted() || exhausted_readonly()` and so trips on
/// the very charge that spends the last step. The final read matters exactly when
/// the LAST charge of the run is made inside a unit's work, after that unit's poll
/// passed. Here: one step less than the run needs, every poll passes (all the
/// control's units are done), the counter reaches zero inside the last unit's `*q`
/// read, and the answer must still be the refusal.
#[test]
fn a_trip_after_the_last_poll_still_refuses() {
    let func = call_loop_reading(2);
    for which in 0u8..3 {
        reset_analysis_memo_stats();
        let control = states(&entry(&func, which));
        let control_units = analysis_memo_stats().interval_fixpoint_units;
        assert!(!is_refusal(&func, &control), "ANTI-VACUITY which={which}: the control is all-Top");
        let tripped = |steps: u64| {
            let _budget = VerifyBudgetGuard::install(None, steps);
            let _ = entry(&func, which);
            exhausted_readonly()
        };
        // The first budget the run fits in (tripping is monotone in the budget).
        let mut hi = 1u64;
        while tripped(hi) {
            hi *= 2;
            assert!(hi < 1 << 40, "which={which}: the run never fits a budget");
        }
        let mut lo = hi / 2;
        while hi - lo > 1 {
            let mid = lo + (hi - lo) / 2;
            if tripped(mid) {
                lo = mid;
            } else {
                hi = mid;
            }
        }
        let _budget = VerifyBudgetGuard::install(None, hi - 1);
        reset_analysis_memo_stats();
        let fp = entry(&func, which);
        assert!(exhausted_readonly(), "which={which}: one step short must trip");
        assert_eq!(
            analysis_memo_stats().interval_fixpoint_units,
            control_units,
            "ANTI-VACUITY which={which}: every poll must pass (the last charge sits inside \
             the last unit), so that only the final budget read can refuse this run"
        );
        assert_refused(&func, &fp, "a trip after the last poll");
    }
}

/// `h(copy r)` with `r = &(*q)`, `q: &mut u32`, and `p = &mut c`: a call whose havoc
/// is a REFINED whole-function list (see [`a_refined_call_havoc_forgets_the_borrowed_local`]).
fn refined_call_fixture() -> VerifiableFunction {
    let local =
        |index: usize, ty: Ty, name: &str| LocalDecl { index, ty, name: Some(name.to_string()) };
    let locals = vec![
        local(0, u32_ty(), "_0"),
        local(1, Ty::Ref { mutable: true, inner: Box::new(u32_ty()) }, "q"),
        local(2, Ty::Ref { mutable: false, inner: Box::new(u32_ty()) }, "r"),
        local(3, u32_ty(), "c"),
        local(4, Ty::Ref { mutable: true, inner: Box::new(u32_ty()) }, "p"),
        local(5, u32_ty(), "t"),
    ];
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(3), Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32)))),
                assign(Place::local(4), Rvalue::Ref { mutable: true, place: Place::local(3) }),
                assign(
                    Place::local(2),
                    Rvalue::Ref {
                        mutable: false,
                        place: Place { local: 1, projections: vec![Projection::Deref] },
                    },
                ),
            ],
            terminator: Terminator::Goto(BlockId(1)),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::Call {
                unwind: UnwindEdge::Unreachable,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: None,
                is_foreign: false,
                func: "test::reader".to_string(),
                args: vec![Operand::Copy(Place::local(2))],
                dest: Place::local(5),
                target: Some(BlockId(2)),
                span: SourceSpan::default(),
                atomic: None,
            },
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(3))))],
            terminator: Terminator::Return,
        },
    ];
    VerifiableFunction {
        name: "refined_call".to_string(),
        def_path: "test::refined_call".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 1,
            return_ty: u32_ty(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Review mutant M13 (the names of a [`TermHavoc::Refined`] call dropped from the
/// index): every call above havocs the whole-function list unrefined, and no other
/// test of this crate sends a refined call through the interval fixpoint, so
/// dropping the refined names passed every test. `h(copy r)` with `r = &(*q)` and
/// `q: &mut u32` is refined by the frozen-shared-reborrow narrowing, which drops `q`
/// from the whole-function list and keeps `c` (mutably borrowed by `p = &mut c`):
/// the call must still forget `c`. Under `cfg(test)` every per-name answer of the
/// index is also compared with the `write_rebinds` scan it replaced, which is what
/// fails first under M13.
///
/// [`TermHavoc::Refined`]: crate::generate::TermHavoc::Refined
#[test]
fn a_refined_call_havoc_forgets_the_borrowed_local() {
    let func = refined_call_fixture();
    let defs = crate::generate::terminator_def_names_structured(&func, &func.body.blocks[1]);
    assert!(
        matches!(defs.havoc, crate::generate::TermHavoc::Refined(_)),
        "ANTI-VACUITY: the fixture's call must havoc a REFINED list, got {:?}",
        defs.havoc
    );
    let names = crate::generate::terminator_def_names(&func, &func.body.blocks[1]);
    assert!(
        names.iter().any(|n| n == "c"),
        "ANTI-VACUITY: `c` must be in the refined list: {names:?}"
    );
    let fp = run(&func);
    let before = &fp.block_states[&BlockId(1)];
    assert_ne!(before.get("c"), Interval::TOP, "ANTI-VACUITY: `c` is bounded before the call");
    let after = &fp.block_states[&BlockId(2)];
    assert!(!after.is_unreachable);
    assert_eq!(
        after.get("c"),
        Interval::TOP,
        "the refined call havoc must forget `c`: {:?}",
        states(&fp)
    );
}

// ---------------------------------------------------------------------------------
// Added at landing on main de6288dddf (2026-10-08). Between this change's review and
// its landing, main gave the terminator havoc two shapes the index did not know:
// `TermHavoc::Escape` (CALL-HAVOC-ESCAPE-2 / TINV-18, 2026-10-06) and the every-local
// write set of an `Opaque` terminator, which the interval transfer now havocs at too
// (H3 OPAQUE-ASM-OUTPUT, 2026-10-08). Each gets the direct fixture the review asked
// for of the `Refined` arm: an arm of the index no test routes a block through is an
// arm a dropped name survives in.
// ---------------------------------------------------------------------------------

fn function_of(
    name: &str,
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
    arg_count: usize,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count,
            return_ty: u32_ty(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `g(args) -> dest`, then `target`.
fn call_with(args: Vec<Operand>, dest: usize, target: usize) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: None,
        is_foreign: false,
        func: "test::g".to_string(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
    }
}

/// `fn f(s: &mut u32)`: `c = 0; p = &mut c`, then `n` calls `t_i = g(const 7)` and,
/// with `full_call`, one more call `t_n = g(copy p)`; then `_0 = copy c`.
///
/// `s` is a protected private `&mut` parameter (never used), so a call whose
/// arguments hand the callee no pointer havocs the whole-function list WITHOUT `s`:
/// `TermHavoc::Escape`, `kept` holding `c` (mutably borrowed by `p`) and `p`. The
/// call that receives `p` havocs the whole list, unrefined.
fn escape_calls_fixture(n: usize, full_call: bool) -> VerifiableFunction {
    let local =
        |index: usize, ty: Ty, name: &str| LocalDecl { index, ty, name: Some(name.to_string()) };
    let mut_ref = || Ty::Ref { mutable: true, inner: Box::new(u32_ty()) };
    let calls = n + usize::from(full_call);
    let first_dest = 4;
    let mut locals = vec![
        local(0, u32_ty(), "_0"),
        local(1, mut_ref(), "s"),
        local(2, u32_ty(), "c"),
        local(3, mut_ref(), "p"),
    ];
    for i in 0..calls {
        locals.push(local(first_dest + i, u32_ty(), &format!("t{i}")));
    }
    let mut blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![
            assign(Place::local(2), Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32)))),
            assign(Place::local(3), Rvalue::Ref { mutable: true, place: Place::local(2) }),
        ],
        terminator: Terminator::Goto(BlockId(1)),
    }];
    for i in 0..calls {
        let args = if i < n {
            vec![Operand::Constant(ConstValue::Uint(7, 32))]
        } else {
            vec![Operand::Copy(Place::local(3))]
        };
        blocks.push(BasicBlock {
            id: BlockId(1 + i),
            stmts: vec![],
            terminator: call_with(args, first_dest + i, 2 + i),
        });
    }
    blocks.push(BasicBlock {
        id: BlockId(1 + calls),
        stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(2))))],
        terminator: Terminator::Return,
    });
    function_of(&format!("escape_calls_{n}_{full_call}"), locals, blocks, 1)
}

/// The escape arm of the index (`TermHavoc::Escape`, on main since 2026-10-06): the
/// call forgets what the arm KEEPS of the whole-function list — `c`, which is in
/// `kept` and in no extra of the call, so only the kept-list index can forget it —
/// and the kept list is indexed once per run under the function's memo scope (the
/// production shape), however many escape-arm calls the body has; a call that
/// havocs the whole list beside them gets the whole-list index, a second one. With
/// no memo scope every call carries its own copy of the payload and so its own
/// index: the answers are the same. Under `cfg(test)` every per-name answer is also
/// compared with the `write_rebinds` scan over the flattened list.
#[test]
fn an_escape_arm_call_havoc_forgets_the_kept_list_through_one_index() {
    use crate::generate::TermHavoc;
    for (n, full_call) in [(1usize, false), (6, false), (6, true)] {
        let func = escape_calls_fixture(n, full_call);
        let calls = n + usize::from(full_call);
        let scope = crate::generate::row_replay_scope();
        for i in 0..calls {
            let block = &func.body.blocks[1 + i];
            let defs = crate::generate::terminator_def_names_structured(&func, block);
            if i < n {
                let TermHavoc::Escape(escape) = &defs.havoc else {
                    panic!(
                        "ANTI-VACUITY n={n}: call {i} must take the escape arm, got {:?}; the \
                         whole-function list is {:?}",
                        defs.havoc,
                        crate::generate::function_havoc_names(&func)
                    );
                };
                assert!(
                    escape.kept.iter().any(|k| k == "c"),
                    "ANTI-VACUITY n={n}: `c` must be kept: {escape:?}"
                );
                assert!(
                    escape.dropped.iter().any(|d| d == "s"),
                    "ANTI-VACUITY n={n}: the protected parameter `s` must be dropped: {escape:?}"
                );
                // Only the kept list names `c`: no extra of the call rebinds it.
                let extras = crate::generate::TermDefs { havoc: TermHavoc::None, ..defs.clone() }
                    .flatten(&func);
                assert!(
                    !extras.iter().any(|h| crate::generate::write_rebinds(h, "c")),
                    "ANTI-VACUITY n={n}: an extra of call {i} already forgets `c`: {extras:?}"
                );
            } else {
                assert!(
                    matches!(defs.havoc, TermHavoc::Function),
                    "ANTI-VACUITY n={n}: the call that receives `p` must havoc the whole list, \
                     got {:?}",
                    defs.havoc
                );
            }
        }
        reset_analysis_memo_stats();
        let scoped = run(&func);
        let stats = analysis_memo_stats();
        drop(scope);
        assert_eq!(stats.interval_havoc_sets, calls as u64, "n={n}: one derivation per call");
        assert_eq!(
            stats.interval_function_havoc_indexes,
            1 + u64::from(full_call),
            "n={n} full_call={full_call}: one index of the kept list per run, shared by every \
             escape-arm call (and one of the whole list when a call havocs it)"
        );
        let before = &scoped.block_states[&BlockId(1)];
        assert_ne!(before.get("c"), Interval::TOP, "ANTI-VACUITY n={n}: `c` is bounded before");
        let after = &scoped.block_states[&BlockId(2)];
        assert!(!after.is_unreachable);
        assert_eq!(
            after.get("c"),
            Interval::TOP,
            "n={n}: the escape-arm call must forget `c`: {:?}",
            states(&scoped)
        );
        // No memo scope: a payload per call, an index per call, the same answer.
        reset_analysis_memo_stats();
        let unscoped = run(&func);
        assert_eq!(states(&unscoped), states(&scoped), "n={n}: the memo scope changed the answer");
        assert_eq!(analysis_memo_stats().interval_havoc_sets, calls as u64);
    }
}

/// `k = 3`, then `terminator`, then `_0 = copy k`.
fn one_terminator_fixture(name: &str, terminator: Terminator) -> VerifiableFunction {
    let local =
        |index: usize, ty: Ty, name: &str| LocalDecl { index, ty, name: Some(name.to_string()) };
    let locals = vec![local(0, u32_ty(), "_0"), local(1, u32_ty(), "k")];
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(
                Place::local(1),
                Rvalue::Use(Operand::Constant(ConstValue::Uint(3, 32))),
            )],
            terminator,
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(1))))],
            terminator: Terminator::Return,
        },
    ];
    function_of(name, locals, blocks, 0)
}

/// The `Opaque` arm of the index (H3 OPAQUE-ASM-OUTPUT, on main since 2026-10-08): an
/// `Opaque` terminator — an `asm!` whose outputs the extraction did not keep — writes
/// every local as far as the oracle can tell, so the state on its out-edge bounds
/// none. `k` is a plain `u32` nothing borrows: it is in no whole-function list, only
/// in the every-local extras, so an index that skipped the `Opaque` terminator (as
/// this change's did before main moved) keeps `k in [3, 3]` across it.
#[test]
fn an_opaque_terminator_forgets_every_local() {
    let opaque = one_terminator_fixture(
        "opaque_writes_k",
        Terminator::Opaque {
            kind: "InlineAsm".to_string(),
            targets: vec![BlockId(1)],
            span: SourceSpan::default(),
        },
    );
    let names = crate::generate::terminator_def_names(&opaque, &opaque.body.blocks[0]);
    assert!(
        names.iter().any(|n| n == "k"),
        "ANTI-VACUITY: the opaque terminator's write set must name `k`: {names:?}"
    );
    reset_analysis_memo_stats();
    let fp = run(&opaque);
    assert_eq!(analysis_memo_stats().interval_havoc_sets, 1, "the opaque block is indexed");
    let after = &fp.block_states[&BlockId(1)];
    assert!(!after.is_unreachable);
    assert_eq!(after.get("k"), Interval::TOP, "the opaque terminator must forget `k`");
    // The same body with a plain jump keeps the bound: the havoc is what forgot it.
    let goto = one_terminator_fixture("goto_keeps_k", Terminator::Goto(BlockId(1)));
    reset_analysis_memo_stats();
    let fp = run(&goto);
    assert_eq!(analysis_memo_stats().interval_havoc_sets, 0, "a jump derives no havoc");
    let k = fp.block_states[&BlockId(1)].get("k");
    assert_eq!((k.lo, k.hi), (3, 3), "ANTI-VACUITY: without the terminator `k` stays [3, 3]");
}
