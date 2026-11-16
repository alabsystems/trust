use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::{append_stable_flattened_index_bound, stable_checked_result_field0_consumer};

const USIZE: Ty = Ty::Int { width: 64, signed: false };

fn extraction(local: usize) -> Statement {
    Statement::Assign {
        place: Place::local(local),
        rvalue: Rvalue::Use(Operand::Copy(Place {
            local: 2,
            projections: vec![Projection::Field(0)],
        })),
        span: SourceSpan::default(),
    }
}

fn assign(local: usize, value: u128) -> Statement {
    Statement::Assign {
        place: Place::local(local),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(value, 64))),
        span: SourceSpan::default(),
    }
}

fn extraction_func(consumer: usize, arg_count: usize, extra: Vec<Statement>) -> VerifiableFunction {
    let mut stmts = vec![extraction(consumer)];
    stmts.extend(extra);
    VerifiableFunction {
        name: "flattened_index_consumer".into(),
        def_path: "test::flattened_index_consumer".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: USIZE, name: Some("param".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Tuple(vec![USIZE, Ty::Bool]),
                    name: Some("checked".into()),
                },
                LocalDecl { index: 3, ty: USIZE, name: Some("idx".into()) },
                LocalDecl {
                    index: 4,
                    ty: Ty::Ref { mutable: true, inner: Box::new(USIZE) },
                    name: Some("idx_ref".into()),
                },
            ],
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn emitted_index_bounds(func: &VerifiableFunction) -> Vec<trust_types::Formula> {
    let mut facts = Vec::new();
    append_stable_flattened_index_bound(func, 2, 5, &mut facts);
    facts
}

#[test]
fn single_assignment_non_parameter_consumer_is_licensed() {
    let func = extraction_func(3, 1, vec![]);
    assert_eq!(stable_checked_result_field0_consumer(&func, 2), Some(3));
    assert_eq!(emitted_index_bounds(&func).len(), 1);
}

#[test]
fn merged_consumer_is_not_given_a_global_flattened_index_bound() {
    let func = extraction_func(3, 1, vec![assign(3, 99)]);
    assert_eq!(stable_checked_result_field0_consumer(&func, 2), None);
    assert!(emitted_index_bounds(&func).is_empty());
}

#[test]
fn reassigned_parameter_keeps_its_distinct_entry_value() {
    // The extraction is the parameter's only explicit definition, but its bare
    // name denotes the implicit caller-supplied entry value too.
    let func = extraction_func(1, 1, vec![]);
    assert_eq!(stable_checked_result_field0_consumer(&func, 2), None);
    assert!(emitted_index_bounds(&func).is_empty());
}

#[test]
fn mutably_escaped_consumer_is_not_treated_as_static() {
    let borrow = Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::Ref { mutable: true, place: Place::local(3) },
        span: SourceSpan::default(),
    };
    let func = extraction_func(3, 1, vec![borrow]);
    assert_eq!(stable_checked_result_field0_consumer(&func, 2), None);
    assert!(emitted_index_bounds(&func).is_empty());
}

// ── MANUAL COUNTER TRIP COUNT ───────────────────────────────────────────────
//
// `while i < N { … i += s; }`. A hand-written loop has no `Iterator::next` to read
// a trip count from; `counter_loop_driver` supplies one from the counter test, and
// `block_execution_bound` turns it into a bound per self-add. Each REFUSAL test pins
// one way a naive version UNDER-counts, which is the false-proof direction.
//
// The fixtures carry the real checked-arithmetic shape: `tmp = CheckedAdd(x, s)`
// is the last statement of its block, the block's TERMINATOR asserts `!tmp.1`,
// and the read-back `x = tmp.0` opens the next block.

use trust_types::loop_nest::LoopNest;
use trust_types::{AssertMessage, BinOp, UnwindEdge};

use super::{
    block_execution_bound, counter_loop_driver, manual_counter_trip_count, total_loop_iterations,
};

/// The counter driver's trip count for the fixture's outermost loop.
fn counter_trip(func: &VerifiableFunction) -> Option<i128> {
    let nest = LoopNest::of(&func.body)?;
    let lp = func.body.blocks.iter().find_map(|b| nest.containing(b.id.0).last().copied())?;
    counter_loop_driver(func, &nest, lp).map(|d| d.trip)
}

const U32: Ty = Ty::Int { width: 32, signed: false };

fn const_u32(value: u128) -> Operand {
    Operand::Constant(ConstValue::Uint(value, 32))
}

fn set_const(local: usize, value: u128) -> Statement {
    Statement::Assign {
        place: Place::local(local),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(value, 32))),
        span: SourceSpan::default(),
    }
}

/// `tmp = CheckedAdd(local, step)`
fn checked_add(local: usize, tmp: usize, step: u128) -> Statement {
    Statement::Assign {
        place: Place::local(tmp),
        rvalue: Rvalue::CheckedBinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(local)),
            const_u32(step),
        ),
        span: SourceSpan::default(),
    }
}

/// `local = tmp.0` — the read-back that makes the add a SELF-add.
fn read_back(local: usize, tmp: usize) -> Statement {
    Statement::Assign {
        place: Place::local(local),
        rvalue: Rvalue::Use(Operand::Copy(Place {
            local: tmp,
            projections: vec![Projection::Field(0)],
        })),
        span: SourceSpan::default(),
    }
}

/// `dst = src` — a plain local-to-local copy.
fn copy_local(dst: usize, src: usize) -> Statement {
    Statement::Assign {
        place: Place::local(dst),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(src))),
        span: SourceSpan::default(),
    }
}

/// `assert(!tmp.1) -> next` — the overflow trap.
fn overflow_assert(tmp: usize, next: usize) -> Terminator {
    Terminator::Assert {
        cond: Operand::Copy(Place { local: tmp, projections: vec![Projection::Field(1)] }),
        expected: false,
        msg: AssertMessage::Overflow(BinOp::Add),
        target: BlockId(next),
        span: SourceSpan::default(),
        unwind: UnwindEdge::Unreachable,
    }
}

fn less_than(cmp: usize, lhs_local: usize, rhs: Operand) -> Statement {
    Statement::Assign {
        place: Place::local(cmp),
        rvalue: Rvalue::BinaryOp(BinOp::Lt, Operand::Copy(Place::local(lhs_local)), rhs),
        span: SourceSpan::default(),
    }
}

fn switch(cmp: usize, if_false: usize, if_true: usize) -> Terminator {
    Terminator::SwitchInt {
        discr: Operand::Copy(Place::local(cmp)),
        targets: vec![(0, BlockId(if_false))],
        otherwise: BlockId(if_true),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    }
}

fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

fn counter_func(blocks: Vec<BasicBlock>, extra_locals: usize) -> VerifiableFunction {
    let mut locals = vec![
        LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
        LocalDecl { index: 1, ty: U32, name: Some("i".into()) },
        LocalDecl { index: 2, ty: U32, name: Some("c".into()) },
        LocalDecl { index: 3, ty: Ty::Bool, name: Some("cmp".into()) },
        LocalDecl { index: 4, ty: Ty::Tuple(vec![U32, Ty::Bool]), name: Some("ck_i".into()) },
        LocalDecl { index: 5, ty: Ty::Tuple(vec![U32, Ty::Bool]), name: Some("ck_c".into()) },
    ];
    for index in 6..6 + extra_locals {
        locals.push(LocalDecl { index, ty: Ty::Bool, name: Some(format!("x{index}")) });
    }
    VerifiableFunction {
        name: "counter".into(),
        def_path: "test::counter".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 0,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `let mut i = 0; let mut c = 0; while i < limit { c += 1; i += 1; }`
///
/// bb0 init | bb1 test | bb2 `ck_c = c+1` | bb3 `c = ck_c.0; ck_i = i+1`
/// | bb4 `i = ck_i.0` | bb5 return.
fn while_counter(limit: u128) -> VerifiableFunction {
    counter_func(
        vec![
            block(0, vec![set_const(1, 0), set_const(2, 0)], Terminator::Goto(BlockId(1))),
            block(1, vec![less_than(3, 1, const_u32(limit))], switch(3, 5, 2)),
            block(2, vec![checked_add(2, 5, 1)], overflow_assert(5, 3)),
            block(3, vec![read_back(2, 5), checked_add(1, 4, 1)], overflow_assert(4, 4)),
            block(4, vec![read_back(1, 4)], Terminator::Goto(BlockId(1))),
            block(5, vec![], Terminator::Return),
        ],
        0,
    )
}

#[test]
fn a_manual_while_counter_yields_its_trip_count() {
    let func = while_counter(3);
    assert_eq!(counter_trip(&func), Some(3));
    // And it reaches the mechanism through the per-block entry point, which is the
    // only reason `build_accumulator_bound_facts` can bound `c` at all: `c += 1`
    // (bb2) sits behind the test's continue edge, so it runs at most 3 times.
    assert_eq!(block_execution_bound(&func, 2), Some(3));
}

#[test]
fn the_trip_count_tracks_the_constant_bound() {
    assert_eq!(counter_trip(&while_counter(10)), Some(10));
    // A zero-trip loop crosses its continue edge zero times, so a self-add behind
    // it never runs. (A self-add OUTSIDE the loop is bounded by 1 as a block in no
    // loop, not by clamping the trip count.)
    assert_eq!(counter_trip(&while_counter(0)), Some(0));
    assert_eq!(block_execution_bound(&while_counter(0), 2), Some(0));
}

#[test]
fn an_untrapped_overflow_flag_is_refused() {
    // `i = i.overflowing_add(1).0` has the SAME `CheckedBinaryOp` + `Field(0)`
    // read-back but CONTINUES on overflow, so `i` is not monotone and the loop
    // can run far more than `ceil((3-0)/1)` times. Dropping the trap must
    // therefore lose the trip count entirely.
    let mut func = while_counter(3);
    func.body.blocks[3].terminator = Terminator::Goto(BlockId(4));
    assert_eq!(
        counter_trip(&func),
        None,
        "an untrapped overflow flag leaves the counter free to wrap"
    );
}

#[test]
fn an_unmodelable_write_anywhere_is_refused() {
    // Inline asm (`Opaque`) can set the counter with no `Assign` this scan sees.
    let mut func = while_counter(3);
    func.body.blocks.push(block(6, vec![], Terminator::Return));
    func.body.blocks[5].terminator = Terminator::Opaque {
        kind: "asm".into(),
        targets: vec![BlockId(6)],
        span: SourceSpan::default(),
    };
    assert_eq!(
        counter_trip(&func),
        None,
        "a fail-closed write channel anywhere in the function voids the trip count"
    );
}

#[test]
fn a_variable_bound_is_refused() {
    // `while i < n` — `n` is local 6, not a constant. The entry-state interval
    // that could bound it belongs to the abstract interpreter, not to this
    // pass, so the trip count is refused rather than guessed.
    let mut func = while_counter(3);
    func.body.blocks[1].stmts = vec![less_than(3, 1, Operand::Copy(Place::local(6)))];
    func.body.locals.push(LocalDecl { index: 6, ty: U32, name: Some("n".into()) });
    assert_eq!(counter_trip(&func), None);
}

#[test]
fn a_counter_incremented_on_only_some_paths_is_refused() {
    // `while i < 3 { c += 1; if cond { i += 1; } }` — the counter advances on
    // only one path, so the loop runs MORE than `ceil((3-0)/1)` times and a
    // trip count of 3 would UNDER-count, i.e. a false bound on `c`.
    let func = counter_func(
        vec![
            block(0, vec![set_const(1, 0), set_const(2, 0)], Terminator::Goto(BlockId(1))),
            block(1, vec![less_than(3, 1, const_u32(3))], switch(3, 6, 2)),
            block(2, vec![checked_add(2, 5, 1)], overflow_assert(5, 3)),
            // branch: only one arm increments `i`
            block(3, vec![read_back(2, 5)], switch(6, 5, 4)),
            block(4, vec![checked_add(1, 4, 1)], overflow_assert(4, 7)),
            block(5, vec![], Terminator::Goto(BlockId(1))),
            block(6, vec![], Terminator::Return),
            block(7, vec![read_back(1, 4)], Terminator::Goto(BlockId(1))),
        ],
        1,
    );
    assert_eq!(
        counter_trip(&func),
        None,
        "a counter incremented on only some paths under-counts the trip count"
    );
}

#[test]
fn a_test_that_does_not_gate_the_back_edge_is_refused() {
    // `loop { if i < 3 { } c += 1; i += 1; }` — the comparison is evaluated
    // every iteration but BOTH its edges stay inside the loop, so `i < 3` is
    // not a loop-continuation condition and bounds nothing.
    let mut func = while_counter(3);
    func.body.blocks[1].terminator = switch(3, 2, 2);
    assert_eq!(
        counter_trip(&func),
        None,
        "a comparison whose two edges both stay in the loop gates nothing"
    );
}

#[test]
fn a_self_add_in_an_undriven_inner_loop_is_unbounded() {
    // Two back edges: the outer counter bounds the OUTER loop, but `c += 1` (bb2) is
    // in an inner self-loop no test bounds, so it runs any number of times per outer
    // iteration and has no bound. (The old whole-function count refused every
    // nested loop for this reason; the per-block bound refuses exactly the add.)
    let mut func = while_counter(3);
    // Make block 2 a self-loop as well, adding a second back edge.
    func.body.blocks[2].terminator = switch(6, 3, 2);
    func.body.locals.push(LocalDecl { index: 6, ty: Ty::Bool, name: Some("inner".into()) });
    assert_eq!(counter_trip(&func), Some(3), "the outer loop is still a counter loop");
    assert_eq!(block_execution_bound(&func, 2), None, "the inner loop has no driver");
}

/// `loop { c += 1; if i < 10 { i += 1 } else { break } }` — the add runs before the
/// test. bb0 init | bb1 `ck_c = c+1` | bb2 `c = ck_c.0`, test | bb3 `ck_i = i+1`
/// | bb4 `i = ck_i.0` | bb5 return.
fn add_before_test() -> VerifiableFunction {
    counter_func(
        vec![
            block(0, vec![set_const(1, 0), set_const(2, 0)], Terminator::Goto(BlockId(1))),
            block(1, vec![checked_add(2, 5, 1)], overflow_assert(5, 2)),
            block(2, vec![read_back(2, 5), less_than(3, 1, const_u32(10))], switch(3, 5, 3)),
            block(3, vec![checked_add(1, 4, 1)], overflow_assert(4, 4)),
            block(4, vec![read_back(1, 4)], Terminator::Goto(BlockId(1))),
            block(5, vec![], Terminator::Return),
        ],
        0,
    )
}

#[test]
fn a_self_add_before_the_test_runs_once_more_than_the_trip_count() {
    // The loop continues 10 times and the add (bb1) also runs on the 11th,
    // exiting pass. The old trip count bounded it by 10, and
    // `loop { c += 1; if i >= 10 { break } i += 1 } a[c]` over an 11-element array
    // was proved and indexed out of bounds (trip-count lane audit, 2026-09-29).
    let func = add_before_test();
    assert_eq!(counter_trip(&func), Some(10));
    assert_eq!(block_execution_bound(&func, 1), Some(11));
}

#[test]
fn a_cycle_that_skips_the_counter_bounds_nothing() {
    // `loop { if flag { c += 1; continue } if i < 10 { i += 1 } else { break } }`:
    // the `continue` cycle bb1 -> bb2 -> bb3 -> bb1 passes neither the test nor
    // the advance, so `c` is added without bound. The old gate asked only that
    // every cycle THROUGH THE TEST advance the counter, and proved this.
    let func = counter_func(
        vec![
            block(0, vec![set_const(1, 0), set_const(2, 0)], Terminator::Goto(BlockId(1))),
            block(1, vec![], switch(6, 4, 2)),
            block(2, vec![checked_add(2, 5, 1)], overflow_assert(5, 3)),
            block(3, vec![read_back(2, 5)], Terminator::Goto(BlockId(1))),
            block(4, vec![less_than(3, 1, const_u32(10))], switch(3, 7, 5)),
            block(5, vec![checked_add(1, 4, 1)], overflow_assert(4, 6)),
            block(6, vec![read_back(1, 4)], Terminator::Goto(BlockId(1))),
            block(7, vec![], Terminator::Return),
        ],
        1,
    );
    assert_eq!(counter_trip(&func), None);
    assert_eq!(block_execution_bound(&func, 2), None);
}

#[test]
fn the_two_step_read_back_rustc_actually_emits_is_recognized() {
    // THE SHAPE THAT MATTERS. `-Ztrust-dump=mir` on
    // `while i < 3 { c += 1; i += 1; }` emits the read-back through a TEMP:
    //
    //   bb4: _7 = CheckedAdd(_2, 1); assert(!_7.1) -> bb5
    //   bb5: _4 = _7.0;  _2 = _4;    // not `_2 = _7.0`
    //
    // A direct-only matcher recognizes neither the counter nor the accumulator,
    // which is why the bound mechanism was silent on every `while` loop.
    let mut func = while_counter(3);
    // Re-point the counter's read-back through temp local 6.
    func.body.locals.push(LocalDecl { index: 6, ty: U32, name: Some("tmp_i".into()) });
    func.body.blocks[4].stmts = vec![read_back(6, 4), copy_local(1, 6)];
    assert_eq!(
        counter_trip(&func),
        Some(3),
        "the trip count must survive the temp rustc actually emits"
    );
}

#[test]
fn a_read_back_temp_with_two_definitions_is_refused() {
    // The hop is only sound while the temp has a UNIQUE value definition. Give
    // it a second one and `unique_value_def` answers `None`, so the counter is
    // no longer known to advance by the stride and the trip count is refused.
    let mut func = while_counter(3);
    func.body.locals.push(LocalDecl { index: 6, ty: U32, name: Some("tmp_i".into()) });
    func.body.blocks[4].stmts = vec![read_back(6, 4), copy_local(1, 6)];
    func.body.blocks[0].stmts.push(set_const(6, 99));
    assert_eq!(
        counter_trip(&func),
        None,
        "a read-back temp with two definitions is not a self-add"
    );
}

// ── BOTTOM-TESTED LOOPS AND A `min`-BOUNDED LIMIT ───────────────────────────
//
// The daily-driver bench's `ctrl/c5`:
//
//     pub fn f(x: u32) -> u32 { let mut r = 0; loop { r += 1; if r > x.min(5) { break; } } r }
//
// Its real MIR (`-Ztrust-dump=mir-only`) differs from a `while` loop in three
// ways at once, and each is a separate refusal until handled: the TRUE edge
// exits (so continuing is the comparison's NEGATION), the compared operand is a
// COPY of the counter, and the limit is an `Ord::min` destination rather than a
// literal. `ctrl/c9` is the same loop with a literal `5` and already passed.

/// `min(a, c) -> dest`, the call c5 lowers `x.min(5)` to.
fn min_call(dest: usize, arg_local: usize, konst: u128, next: usize) -> Terminator {
    Terminator::Call {
        func: "<u32 as core::cmp::Ord>::min".into(),
        args: vec![Operand::Copy(Place::local(arg_local)), const_u32(konst)],
        dest: Place::local(dest),
        target: Some(BlockId(next)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: None,
        is_foreign: false,
        unwind: UnwindEdge::Unreachable,
    }
}

fn greater_than(cmp: usize, lhs_local: usize, rhs_local: usize) -> Statement {
    Statement::Assign {
        place: Place::local(cmp),
        rvalue: Rvalue::BinaryOp(
            BinOp::Gt,
            Operand::Move(Place::local(lhs_local)),
            Operand::Move(Place::local(rhs_local)),
        ),
        span: SourceSpan::default(),
    }
}

/// c5's exact shape. `callee` lets a test swap `min` for `max`.
/// bb0 init | bb1 `ck = r+1` | bb2 `r = ck.0; cp = r` + min call
/// | bb3 test `cp > m` | bb4 return.
fn bottom_tested_min_loop(callee: &str, konst: u128) -> VerifiableFunction {
    let mut func = counter_func(
        vec![
            block(0, vec![set_const(1, 0)], Terminator::Goto(BlockId(1))),
            block(1, vec![checked_add(1, 4, 1)], overflow_assert(4, 2)),
            block(2, vec![read_back(1, 4), copy_local(6, 1)], min_call(7, 2, konst, 3)),
            block(3, vec![greater_than(3, 6, 7)], switch(3, 1, 4)),
            block(4, vec![], Terminator::Return),
        ],
        0,
    );
    if let Terminator::Call { func: name, .. } = &mut func.body.blocks[2].terminator {
        *name = callee.into();
    }
    func.body.locals.push(LocalDecl { index: 6, ty: U32, name: Some("cp".into()) });
    func.body.locals.push(LocalDecl { index: 7, ty: U32, name: Some("m".into()) });
    func
}

#[test]
fn a_bottom_tested_loop_with_a_min_bounded_limit_yields_its_trip_count() {
    // `r` runs 1..=6 before `r > min(x, 5)` is true, so six iterations.
    let func = bottom_tested_min_loop("<u32 as core::cmp::Ord>::min", 5);
    assert_eq!(counter_trip(&func), Some(6));
    // The add (bb1, the header) is not behind the continue edge, so it gets one
    // more: 7, one loose, since the test here reads the ADVANCED counter (see
    // `counter_loop_driver`).
    assert_eq!(block_execution_bound(&func, 1), Some(7));
}

#[test]
fn a_user_fn_named_min_is_not_a_bound() {
    // `mod lim { pub fn min(a: u32, _cap: u32) -> u32 { a } }` ends in `::min` too.
    // `0..lim::min(n, 10)` was proved to run at most 10 times and overflowed
    // (trip-count lane audit, 2026-09-29).
    let func = bottom_tested_min_loop("user_min::lim::min", 5);
    assert_eq!(counter_trip(&func), None);
}

#[test]
fn max_is_not_an_upper_bound_and_is_refused() {
    // `max(a, c) >= c` bounds the limit from BELOW and says nothing about how far
    // the counter can run. Reading it as an upper bound would UNDER-count.
    let func = bottom_tested_min_loop("<u32 as core::cmp::Ord>::max", 5);
    assert_eq!(counter_trip(&func), None);
}

#[test]
fn a_bound_local_with_a_second_definition_is_refused() {
    // The `pmod` false proof in `local_defs` came from an `Assign`-only scan
    // missing a `Call`-destination definition. Here the reverse: the `min`
    // destination is ALSO assigned, so `m <= 5` is not established.
    let mut func = bottom_tested_min_loop("<u32 as core::cmp::Ord>::min", 5);
    func.body.blocks[0].stmts.push(set_const(7, 99));
    assert_eq!(counter_trip(&func), None);
}

#[test]
fn a_counter_copy_taken_before_the_loop_is_refused() {
    // A STALE copy. Moving `cp = r` into the pre-header makes the test compare
    // the counter's INITIAL value forever, so the loop never exits on it and any
    // trip count read off it under-counts.
    let mut func = bottom_tested_min_loop("<u32 as core::cmp::Ord>::min", 5);
    func.body.blocks[2].stmts = vec![read_back(1, 4)];
    func.body.blocks[0].stmts.push(copy_local(6, 1));
    assert_eq!(
        counter_trip(&func),
        None,
        "a copy taken before the increment is stale and must not carry the bound"
    );
}

#[test]
fn a_comparison_whose_both_edges_stay_in_the_loop_is_refused() {
    // Polarity is read from which edge LEAVES the cycle; if neither does, the
    // comparison is an ordinary `if` in the body and gates nothing.
    let mut func = bottom_tested_min_loop("<u32 as core::cmp::Ord>::min", 5);
    func.body.blocks[3].terminator = switch(3, 1, 1);
    assert_eq!(counter_trip(&func), None);
}

// ── `min` AS A GLOBAL UPPER BOUND ───────────────────────────────────────────

/// A function whose local 7 is defined by one `min(param, konst)` call.
fn min_bound_func(callee: &str, konst: u128) -> VerifiableFunction {
    let mut func = counter_func(
        vec![block(0, vec![], min_call(7, 1, konst, 1)), block(1, vec![], Terminator::Return)],
        0,
    );
    if let Terminator::Call { func: name, .. } = &mut func.body.blocks[0].terminator {
        *name = callee.into();
    }
    func.body.locals.push(LocalDecl { index: 6, ty: U32, name: Some("cp".into()) });
    func.body.locals.push(LocalDecl { index: 7, ty: U32, name: Some("m".into()) });
    func
}

fn min_facts(func: &VerifiableFunction) -> Vec<String> {
    super::loop_bounds::build_min_upper_bound_facts(func).iter().map(|f| format!("{f:?}")).collect()
}

#[test]
fn a_min_destination_gets_a_global_upper_bound() {
    // `min(a, 8) <= 8` holds at every program point, which is what makes
    // `(0..n.min(8) as u32).collect()` a bounded allocation.
    let facts = min_facts(&min_bound_func("<u32 as core::cmp::Ord>::min", 8));
    assert_eq!(facts.len(), 1, "expected exactly one bound fact, got {facts:?}");
    assert!(facts[0].contains("Int(8)"), "the bound must be the min's constant: {facts:?}");
}

#[test]
fn max_gets_no_upper_bound() {
    // `max(a, c) >= c` is a LOWER bound and says nothing about how large the
    // value can be. Emitting it as an upper bound would be a false fact.
    assert!(min_facts(&min_bound_func("<u32 as core::cmp::Ord>::max", 8)).is_empty());
}

#[test]
fn a_min_destination_that_is_also_assigned_gets_no_bound() {
    // The `pmod` lesson: a second definition through the OTHER channel.
    let mut func = min_bound_func("<u32 as core::cmp::Ord>::min", 8);
    func.body.blocks[1].stmts.push(set_const(7, 99));
    assert!(min_facts(&func).is_empty());
}

#[test]
fn a_parameter_gets_no_min_bound() {
    // A parameter carries an implicit entry definition this statement scan
    // cannot see, so its one visible `Call` definition is not its only one.
    let mut func = min_bound_func("<u32 as core::cmp::Ord>::min", 8);
    func.body.arg_count = 7;
    assert!(min_facts(&func).is_empty());
}

#[test]
fn the_bound_crosses_a_value_preserving_cast() {
    // `(0..n.min(8) as u32)` puts a `Cast` between the `min` and the range end,
    // so without this hop the bound never reaches the allocation lane that reads
    // the end. `min(_, 8)` is in `[0, 8]` and 8 fits `u32`, so the cast cannot
    // change the value.
    let mut func = min_bound_func("<u32 as core::cmp::Ord>::min", 8);
    func.body.locals.push(LocalDecl { index: 8, ty: U32, name: Some("cast".into()) });
    func.body.blocks[1].stmts.push(Statement::Assign {
        place: Place::local(8),
        rvalue: Rvalue::Cast(Operand::Move(Place::local(7)), U32),
        span: SourceSpan::default(),
    });
    let facts = min_facts(&func);
    assert_eq!(facts.len(), 2, "the min AND its cast must be bounded: {facts:?}");
    assert!(facts.iter().all(|f| f.contains("Int(8)")), "{facts:?}");
}

#[test]
fn the_bound_does_not_cross_a_narrowing_cast() {
    // `min(_, 300) as u8` CAN change the value (300 does not fit `u8`), so the
    // bound must not be carried across. Propagating it would emit `c <= 300`
    // about a `u8`, which is vacuous here but would be a false fact the moment
    // the constant mattered.
    let mut func = min_bound_func("<u32 as core::cmp::Ord>::min", 300);
    let u8_ty = Ty::Int { width: 8, signed: false };
    func.body.locals.push(LocalDecl { index: 8, ty: u8_ty.clone(), name: Some("cast".into()) });
    func.body.blocks[1].stmts.push(Statement::Assign {
        place: Place::local(8),
        rvalue: Rvalue::Cast(Operand::Move(Place::local(7)), u8_ty),
        span: SourceSpan::default(),
    });
    let facts = min_facts(&func);
    assert_eq!(facts.len(), 1, "only the min itself may be bounded: {facts:?}");
}

// ── THE SEAM ROWS (2026-09-19) ──────────────────────────────────────────────
//
// `local_defs_seam_lint` named four sites in `loop_bounds.rs` that answered a
// per-local definition question with a hand-rolled block scan. Routing each
// through the seam changed two answers, and both changes are here: a `min`-bounded
// limit that is a PARAMETER, and a value-preserving cast whose SOURCE is one.
// Every row below is a matched pair — the same body, with `arg_count` as the only
// difference — because `arg_count` is the whole discriminator.

/// `while i < m { i += 1 }` whose limit `m` is written by `m = x.min(5)` on ONE
/// branch. bb0 init + branch | bb1 the `min` call | bb2 test | bb3 `ck = i+1`
/// | bb4 `i = ck.0` | bb5 return.
///
/// With `arg_count == 2`, `m` is a PARAMETER: on the path that skips bb1 the loop
/// tests against the CALLER's value, which no `min` bounds.
fn param_min_limit_loop(arg_count: usize) -> VerifiableFunction {
    let locals = vec![
        LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
        LocalDecl { index: 1, ty: U32, name: Some("m".into()) },
        LocalDecl { index: 2, ty: U32, name: Some("x".into()) },
        LocalDecl { index: 3, ty: U32, name: Some("i".into()) },
        LocalDecl { index: 4, ty: Ty::Tuple(vec![U32, Ty::Bool]), name: Some("ck".into()) },
        LocalDecl { index: 5, ty: Ty::Bool, name: Some("cmp".into()) },
        LocalDecl { index: 6, ty: Ty::Bool, name: Some("sel".into()) },
    ];
    let test = Statement::Assign {
        place: Place::local(5),
        rvalue: Rvalue::BinaryOp(
            BinOp::Lt,
            Operand::Copy(Place::local(3)),
            Operand::Copy(Place::local(1)),
        ),
        span: SourceSpan::default(),
    };
    VerifiableFunction {
        name: "param_min_limit".into(),
        def_path: "test::param_min_limit".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![
                block(0, vec![set_const(3, 0)], switch(6, 1, 2)),
                block(1, vec![], min_call(1, 2, 5, 2)),
                block(2, vec![test], switch(5, 5, 3)),
                block(3, vec![checked_add(3, 4, 1)], overflow_assert(4, 4)),
                block(4, vec![read_back(3, 4)], Terminator::Goto(BlockId(2))),
                block(5, vec![], Terminator::Return),
            ],
            arg_count,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

#[test]
fn a_min_bounded_limit_that_is_not_a_parameter_still_yields_its_trip_count() {
    // The SAFE half of the pair: `m`'s only value is the `min` call's result, so
    // `m <= 5` holds at the test and `K = 5` is a true bound.
    assert_eq!(counter_trip(&param_min_limit_loop(0)), Some(5));
}

#[test]
fn a_min_bounded_parameter_limit_is_refused() {
    // The UNSAFE twin, and the reason `bound_operand_upper_bound` had to move onto
    // the seam: it was the one `min`-bound reader with NO parameter arm. `m` is a
    // parameter here, the `min` call is on a branch, and on the other branch the
    // loop runs the CALLER's `m` times — any u32. `K = 5` would be a false bound,
    // and an under-counted `K` makes `acc <= init + K*M` false.
    //
    // MEASURED on the parent commit: `Some(5)`, from a body identical to the row
    // above but for `arg_count`.
    assert_eq!(
        counter_trip(&param_min_limit_loop(2)),
        None,
        "a parameter's entry value is not bounded by a `min` call the loop can skip"
    );
}

#[test]
fn a_counter_written_through_the_partial_channel_is_refused() {
    // The channel the replaced scan could not see. `SetDiscriminant` is
    // `WriteEffect::Captured`, so `has_unmodelable_write` does not stop it either,
    // and the old two-pass scan skipped every statement that was not an `Assign`
    // to the counter — so the counter still read as "one const init and one
    // self-add" while something else changed what it holds. `local_defs::value_defs`
    // refuses `LocalWrite::Partial` outright.
    //
    // MEASURED on the parent commit: `Some(3)`.
    let mut func = while_counter(3);
    func.body.blocks[4]
        .stmts
        .push(Statement::SetDiscriminant { place: Place::local(1), variant_index: 0 });
    assert_eq!(counter_trip(&func), None);
}

#[test]
fn a_cast_from_a_parameter_min_gets_no_bound() {
    // `if c { n = n.min(8); } let k = n as u32;` — the cast hop re-asks the bound
    // question about its SOURCE, and the source is a PARAMETER whose entry value
    // reaches the cast on the path that skips the call. `k <= 8` is false there.
    // `build_min_upper_bound_facts`'s own `1..=arg_count` skip covered the local it
    // tested and not the hop; the seam covers both.
    //
    // MEASURED on the parent commit: one fact, `Le(Var("cast", Int), Int(8))`.
    let mut func = min_bound_func("<u32 as core::cmp::Ord>::min", 8);
    func.body.arg_count = 7;
    func.body.locals.push(LocalDecl { index: 8, ty: U32, name: Some("cast".into()) });
    func.body.blocks[1].stmts.push(Statement::Assign {
        place: Place::local(8),
        rvalue: Rvalue::Cast(Operand::Move(Place::local(7)), U32),
        span: SourceSpan::default(),
    });
    let facts = min_facts(&func);
    assert!(
        facts.is_empty(),
        "a bound read off a parameter's body definition must not cross the cast: {facts:?}"
    );
}

// ── THE IDENTITY, NOT THE NAME (Trust, 2026-10-03, NAME-ANCHOR-1) ───────────
//
// `local_min_upper_bound` decided "this call is `Ord::min`" with
// `callee.ends_with("::min")`, so a user function merely NAMED `min` got the
// global fact `dest <= c`. The Clean kernel certified the `+ 1` overflow row under
// that fact and the elision deleted the check: `util::min(u32::MAX, 10) + 1`
// returned 0 (`tests/ui/trust/min_upper_bound_requires_std_min{,_run}.rs`). The
// lane now asks `call_facts::is_ord_min_call`, std's path, for BOTH consumers.

/// The spellings a user can give a callee that is not std's `Ord::min`: a module
/// function, a trait named `Ord` (crate-qualified, and the bare spelling the
/// producer never emits for std's trait), and a nested `core::cmp` path.
const USER_MINS: &[&str] = &[
    "minbug2::util::min",
    "min_upper_bound_requires_std_min::util2::min",
    "<u32 as min_upper_bound_requires_std_min::spoof::Ord>::min",
    "<u32 as spoof::Ord>::min",
    "<u32 as Ord>::min",
    "<u32 as spoof::core::cmp::Ord>::min",
    "min_upper_bound_requires_std_min::spoof::core::cmp::min",
    "x::Ord::min",
];

#[test]
fn a_user_fn_named_min_gets_no_bound() {
    for callee in USER_MINS {
        let facts = min_facts(&min_bound_func(callee, 10));
        assert!(facts.is_empty(), "`{callee}` is not std's `Ord::min`; got {facts:?}");
    }
}

#[test]
fn std_min_spellings_keep_their_bound() {
    for callee in [
        "<u32 as core::cmp::Ord>::min",
        "<u32 as std::cmp::Ord>::min",
        "core::cmp::Ord::min",
        "core::cmp::min",
    ] {
        let facts = min_facts(&min_bound_func(callee, 10));
        assert_eq!(facts.len(), 1, "`{callee}` is std's `min`; got {facts:?}");
        assert!(facts[0].contains("Int(10)"), "the bound is the constant: {facts:?}");
    }
}

#[test]
fn a_std_ord_min_into_a_non_integer_destination_gets_no_bound() {
    // `ord_method` anchors the TRAIT, not `Self`: `<W as core::cmp::Ord>::min` on a
    // user type is std's trait path, yet the body that runs is the user impl's
    // (`Ord::min` may be overridden). Only an integer destination makes `Self` a
    // primitive integer, whose `Ord` only `core` implements.
    let mut func = min_bound_func("<user::W as core::cmp::Ord>::min", 10);
    func.body.locals[7].ty = Ty::adt("user::W", vec![("0".to_string(), U32)]);
    let facts = min_facts(&func);
    assert!(facts.is_empty(), "a user `Self` gets no `min` bound: {facts:?}");
}

#[test]
fn a_bottom_tested_loop_with_a_user_min_limit_gets_no_trip_count() {
    // The SECOND consumer, `bound_operand_upper_bound`: the same c5 loop as
    // `a_bottom_tested_loop_with_a_min_bounded_limit_yields_its_trip_count`, with
    // the limit a user `min` whose result is not bounded by 5. A trip count read
    // off it would UNDER-count, the false-bound direction.
    for callee in USER_MINS {
        let func = bottom_tested_min_loop(callee, 5);
        assert_eq!(manual_counter_trip_count(&func), None, "`{callee}`");
        assert_eq!(total_loop_iterations(&func), None, "`{callee}`");
    }
}

/// REAL extracted MIR (`-Ztrust-dump=mir:<dir>`, stage 1 of main `a0877b2a62`,
/// 2026-10-03) of `minbug2.rs`:
///
/// ```text
/// pub mod util { pub fn min(a: u32, _b: u32) -> u32 { a } }
/// pub fn f(x: u32) -> u32 { util::min(x, 10) + 1 }                // `minbug2::util::min`
/// pub fn std_min(x: u32) -> u32 { x.min(10) + 1 }                 // `<u32 as core::cmp::Ord>::min`
/// pub fn build(n: usize) -> Vec<u32> { (0..n.min(8) as u32).collect() }
/// ```
///
/// `build` is the shape the lane was written for (aad24d4640): its range end is a
/// `min` destination behind a cast.
const MIR_MINBUG2_F: &str = r#"{"name":"f","def_path":"minbug2::f","span":{"file":"minbug2.rs","line_start":6,"col_start":0,"line_end":8,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":1,"ty":{"Int":{"width":32,"signed":false}},"name":"x"},{"index":2,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":3,"ty":{"Tuple":[{"Int":{"width":32,"signed":false}},"Bool"]},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"minbug2::util::min","args":[{"Copy":{"local":1,"projections":[]}},{"Constant":{"Uint":[10,32]}}],"dest":{"local":2,"projections":[]},"target":1,"span":{"file":"minbug2.rs","line_start":7,"col_start":4,"line_end":7,"col_end":4},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":16011015682147715544,"def_index":4,"substs_digest":[14241860155052752853,2268345107747320411]},"callee_key":{"krate_is_real_sysroot":false,"krate_name_is_ambiguous":false,"stable_crate_id":16011015682147715544,"krate_name":"minbug2"}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"CheckedBinaryOp":["Add",{"Copy":{"local":2,"projections":[]}},{"Constant":{"Uint":[1,32]}}]},"span":{"file":"minbug2.rs","line_start":7,"col_start":4,"line_end":7,"col_end":4}}}],"terminator":{"Assert":{"cond":{"Move":{"local":3,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Add"},"target":2,"span":{"file":"minbug2.rs","line_start":7,"col_start":4,"line_end":7,"col_end":4},"unwind":"Continue"}}},{"id":2,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":3,"projections":[{"Field":0}]}}},"span":{"file":"minbug2.rs","line_start":8,"col_start":1,"line_end":8,"col_end":1}}}],"terminator":"Return"}],"arg_count":1,"return_ty":{"Int":{"width":32,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["x","Int"]},{"Int":0}]},{"Le":[{"Var":["x","Int"]},{"Int":4294967295}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;
const MIR_MINBUG2_STD_MIN: &str = r#"{"name":"std_min","def_path":"minbug2::std_min","span":{"file":"minbug2.rs","line_start":9,"col_start":0,"line_end":11,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":1,"ty":{"Int":{"width":32,"signed":false}},"name":"x"},{"index":2,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":3,"ty":{"Tuple":[{"Int":{"width":32,"signed":false}},"Bool"]},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"<u32 as core::cmp::Ord>::min","args":[{"Copy":{"local":1,"projections":[]}},{"Constant":{"Uint":[10,32]}}],"dest":{"local":2,"projections":[]},"target":1,"span":{"file":"minbug2.rs","line_start":10,"col_start":4,"line_end":10,"col_end":13},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":3570,"substs_digest":[12295953916534365648,15423895294860648131]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"CheckedBinaryOp":["Add",{"Copy":{"local":2,"projections":[]}},{"Constant":{"Uint":[1,32]}}]},"span":{"file":"minbug2.rs","line_start":10,"col_start":4,"line_end":10,"col_end":17}}}],"terminator":{"Assert":{"cond":{"Move":{"local":3,"projections":[{"Field":1}]}},"expected":false,"msg":{"Overflow":"Add"},"target":2,"span":{"file":"minbug2.rs","line_start":10,"col_start":4,"line_end":10,"col_end":17},"unwind":"Continue"}}},{"id":2,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Move":{"local":3,"projections":[{"Field":0}]}}},"span":{"file":"minbug2.rs","line_start":10,"col_start":4,"line_end":10,"col_end":17}}}],"terminator":"Return"}],"arg_count":1,"return_ty":{"Int":{"width":32,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["x","Int"]},{"Int":0}]},{"Le":[{"Var":["x","Int"]},{"Int":4294967295}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;
const MIR_MINBUG2_BUILD: &str = r#"{"name":"build","def_path":"minbug2::build","span":{"file":"minbug2.rs","line_start":12,"col_start":0,"line_end":14,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}},"name":null},{"index":1,"ty":{"Int":{"width":64,"signed":false}},"name":"n"},{"index":2,"ty":{"Adt":{"name":"core::ops::range::Range","fields":[["start",{"Int":{"width":32,"signed":false}}],["end",{"Int":{"width":32,"signed":false}}]],"variants":[],"disc_index_safe":false,"faithful_enum_repr":null,"layout":null,"enum_layout":null,"adt_kind":"Struct"}},"name":null},{"index":3,"ty":{"Int":{"width":32,"signed":false}},"name":null},{"index":4,"ty":{"Int":{"width":64,"signed":false}},"name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"Call":{"func":"<usize as core::cmp::Ord>::min","args":[{"Copy":{"local":1,"projections":[]}},{"Constant":{"Uint":[8,64]}}],"dest":{"local":4,"projections":[]},"target":1,"span":{"file":"minbug2.rs","line_start":13,"col_start":8,"line_end":13,"col_end":16},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":3570,"substs_digest":[14472905155864919619,5837942336132216210]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"Cast":[{"Move":{"local":4,"projections":[]}},{"Int":{"width":32,"signed":false}}]},"span":{"file":"minbug2.rs","line_start":13,"col_start":8,"line_end":13,"col_end":23}}},{"Assign":{"place":{"local":2,"projections":[]},"rvalue":{"Aggregate":[{"Adt":{"name":"core::ops::range::Range","variant":0,"active_field":null,"args":"core::ops::range::Range<u32>"}},[{"Constant":{"Uint":[0,32]}},{"Move":{"local":3,"projections":[]}}]]},"span":{"file":"minbug2.rs","line_start":13,"col_start":4,"line_end":13,"col_end":24}}}],"terminator":{"Call":{"func":"<core::ops::range::Range<u32> as core::iter::traits::iterator::Iterator>::collect::<alloc::vec::Vec<u32>>::<__trust_elem_bytes@4>","args":[{"Move":{"local":2,"projections":[]}}],"dest":{"local":0,"projections":[]},"target":2,"span":{"file":"minbug2.rs","line_start":13,"col_start":4,"line_end":13,"col_end":34},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue","callee_identity":{"stable_crate_id":4703791156326232143,"def_index":10602,"substs_digest":[5567954926818798508,11814145014553215735]},"callee_key":{"krate_is_real_sysroot":true,"krate_name_is_ambiguous":false,"stable_crate_id":4703791156326232143,"krate_name":"core"}}}},{"id":2,"stmts":[],"terminator":"Return"}],"arg_count":1,"return_ty":{"Seq":{"elem":{"Int":{"width":32,"signed":false}}}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["n","Int"]},{"Int":0}]},{"Le":[{"Var":["n","Int"]},{"Int":18446744073709551615}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"#;

#[test]
fn the_extracted_user_min_gets_no_bound_and_std_min_keeps_it() {
    let parse = |mir: &str| -> VerifiableFunction {
        serde_json::from_str(mir).expect("the captured MIR fixture must deserialize")
    };
    let f = parse(MIR_MINBUG2_F);
    let facts = min_facts(&f);
    assert!(facts.is_empty(), "`minbug2::util::min` is not `Ord::min`; got {facts:?}");

    let std_min = parse(MIR_MINBUG2_STD_MIN);
    let facts = min_facts(&std_min);
    assert_eq!(facts.len(), 1, "std `x.min(10)` keeps its bound: {facts:?}");
    assert!(facts[0].contains("Int(10)"), "{facts:?}");

    let build = parse(MIR_MINBUG2_BUILD);
    let facts = min_facts(&build);
    assert!(
        !facts.is_empty() && facts.iter().all(|f| f.contains("Int(8)")),
        "the motivating `(0..n.min(8) as u32).collect()` keeps its bound: {facts:?}"
    );
}

// ── TRIP-COUNT SOUNDNESS (wave 14: TRIP-ZERO-PRODUCT-1, TRIP-INIT-CYCLE-1, ────
// ── TRIP-MID-TEST-1) ───────────────────────────────────────────────────────
//
// Every consumer of `total_loop_iterations` (`build_accumulator_bound_facts`, the BV
// accumulator lane, the BMC reduction) multiplies `K` into a GLOBAL fact `acc <= init +
// K*M`, so `K` must bound how many times a self-add runs. Each row below is a shape
// where it did not: the Clean kernel then re-checked overflow and bounds rows under a
// false hypothesis, and `elide_kernel_certified_checks` removed real checks.
//
// The `realmir` rows are REAL extracted MIR (`-Ztrust-dump=mir-only:<dir>` on
// `scratchpad/stage1-w12`, 2026-10-04) of the functions in
// `tests/ui/trust/{loop_trip_zero_factor_is_not_a_bound, manual_counter_init_in_loop,
// mid_tested_loop_counts_the_pre_test_block}.rs`, captured at the fixtures' own flags
// (`-Coverflow-checks=on`; the `_opt` files add `-O`), plus `zero_alone`, from a probe
// beside them. Each "MEASURED BEFORE" is what the parent commit's code returned on the
// same body.

/// A captured function from `tests/fixtures/loop_trip_count/`.
macro_rules! trip_fixture {
    ($name:literal) => {
        serde_json::from_str::<VerifiableFunction>(include_str!(concat!(
            "../../tests/fixtures/loop_trip_count/",
            $name,
            ".json"
        )))
        .expect(concat!("the captured MIR fixture `", $name, "` must deserialize"))
    };
}

fn acc_facts(func: &VerifiableFunction) -> Vec<String> {
    super::loop_bounds::build_accumulator_bound_facts(func)
        .iter()
        .map(|f| format!("{f:?}"))
        .collect()
}

/// [`acc_facts`], sorted, for comparison with an exact expected set.
fn sorted_acc_facts(func: &VerifiableFunction) -> Vec<String> {
    let mut facts = acc_facts(func);
    facts.sort();
    facts
}

/// The `Debug` rendering of the accumulator fact `var <= k`, as [`acc_facts`] prints it.
fn acc_le(var: &str, k: i128) -> String {
    format!(
        "{:?}",
        trust_types::Formula::Le(
            Box::new(trust_types::Formula::Var(var.into(), trust_types::Sort::Int)),
            Box::new(trust_types::Formula::Int(k)),
        )
    )
}

// ── TRIP-ZERO-PRODUCT-1: a zero-trip loop is the factor 1, never 0 ──────────

#[test]
fn a_zero_trip_loop_does_not_cancel_the_other_loops_factor() {
    // `const WARMUP: u32 = 0; for _ in 0..WARMUP {} for _ in 0..300u32 { c += 1; }`
    // MEASURED BEFORE: `Some(0)` for all four, so the fact was `c <= 0` and the build
    // returned 44 for `count_after_warmup` where vanilla Rust panics.
    let count_after_warmup = trip_fixture!("count_after_warmup");
    for (name, func) in [
        ("count_after_warmup", &count_after_warmup),
        ("zero_then", &trip_fixture!("zero_then")),
        ("empty_arr_then", &trip_fixture!("empty_arr_then")),
        ("zero_after", &trip_fixture!("zero_after")),
    ] {
        assert_eq!(
            total_loop_iterations(func),
            Some(300),
            "`{name}`: 300 adds follow the zero-trip loop"
        );
    }
    let facts = acc_facts(&count_after_warmup);
    assert!(
        facts.iter().any(|f| f.contains("Int(300)"))
            && !facts.iter().any(|f| f.contains("Int(0))")),
        "the accumulator fact must be `c <= 300`, never `c <= 0`: {facts:?}"
    );
}

#[test]
fn a_nested_zero_trip_inner_loop_is_the_factor_one() {
    // `for _ in 0..300u32 { c += 1; for _ in 0..0u32 {} }` — the add sits in the OUTER
    // body. MEASURED BEFORE: `Some(0)`. It also pins the iterator lane's header
    // exemption: the inner driver's pre-region holds the outer body's add, and the
    // inner driver heads its own loop, so the add is the outer factor's to bound.
    assert_eq!(total_loop_iterations(&trip_fixture!("nested_zero")), Some(300));
}

#[test]
fn a_zero_trip_loop_alone_is_the_factor_one() {
    // `for _ in 0..0u32 { c += 1; }` — `K >= 1`, the same floor the manual lane keeps
    // (`the_trip_count_tracks_the_constant_bound`). MEASURED BEFORE: `Some(0)`.
    assert_eq!(total_loop_iterations(&trip_fixture!("zero_alone")), Some(1));
}

#[test]
fn loops_that_run_keep_their_product() {
    // Controls. `one_then`: `0..1` then `0..300` — `Some(300)` before and after.
    // `safe_after_zero`: `0..0` then `0..200` on `u8` — `Some(0)` before (a vacuous
    // proof), `Some(200)` now, which still proves `c += 1` on `u8`.
    assert_eq!(total_loop_iterations(&trip_fixture!("one_then")), Some(300));
    assert_eq!(total_loop_iterations(&trip_fixture!("safe_after_zero")), Some(200));
}

// ── TRIP-INIT-CYCLE-1: a counter init on a cycle is a reset ─────────────────

#[test]
fn a_counter_reinitialised_inside_the_loop_is_refused() {
    // `while_counter(10)` with `i = 0` moved from the pre-header into the loop body:
    // the test `i < 10` then sees 0 on every pass and bounds nothing.
    // MEASURED BEFORE: `Some(10)` from both entry points.
    let mut func = while_counter(10);
    func.body.blocks[0].stmts = vec![set_const(2, 0)];
    func.body.blocks[2].stmts.insert(0, set_const(1, 0));
    assert_eq!(manual_counter_trip_count(&func), None);
    assert_eq!(total_loop_iterations(&func), None);
    // The unmodified function is the control.
    assert_eq!(total_loop_iterations(&while_counter(10)), Some(10));
}

#[test]
fn realmir_a_counter_init_inside_the_loop_is_refused() {
    // `loop { i = 0; c += 1; if c == limit { break; } i += 1; if i >= 10 { break; } }`,
    // the same with `let mut i: u32 = 0;` / `let mut tries = 0u32;` declared in the
    // body. MEASURED BEFORE: `Some(10)` for all four (`TRUST_ACC … K=10 -> bound c <=
    // 10`); `reset_loop(0)` returned 0 where vanilla Rust panics.
    for (name, func) in [
        ("reset_loop", trip_fixture!("reset_loop")),
        ("reset_idx", trip_fixture!("reset_idx")),
        ("let_in_loop", trip_fixture!("let_in_loop")),
        ("retry", trip_fixture!("retry")),
    ] {
        assert_eq!(total_loop_iterations(&func), None, "`{name}`: the init resets the counter");
        assert!(acc_facts(&func).is_empty(), "`{name}`: no accumulator fact without a trip count");
    }
    // Control: the init above `while i < 10` keeps `K = 10`.
    assert_eq!(total_loop_iterations(&trip_fixture!("while_ctl")), Some(10));
}

// ── TRIP-MID-TEST-1: code above the test runs once more; a cycle that skips ──
// ── the test is not bounded by it ───────────────────────────────────────────

/// `let mut i = 0; let mut c = 0; loop { c += 1; if !(i < limit) { break; } i += 1; }`
///
/// bb0 init | bb1 `ck_c = c+1` | bb2 `c = ck_c.0`, test `i < limit` | bb3 `ck_i = i+1`
/// | bb4 `i = ck_i.0` -> bb1 | bb5 return. The test continues `limit` times; `c += 1`
/// runs `limit + 1` times.
fn mid_tested_counter(limit: u128) -> VerifiableFunction {
    counter_func(
        vec![
            block(0, vec![set_const(1, 0), set_const(2, 0)], Terminator::Goto(BlockId(1))),
            block(1, vec![checked_add(2, 5, 1)], overflow_assert(5, 2)),
            block(2, vec![read_back(2, 5), less_than(3, 1, const_u32(limit))], switch(3, 5, 3)),
            block(3, vec![checked_add(1, 4, 1)], overflow_assert(4, 4)),
            block(4, vec![read_back(1, 4)], Terminator::Goto(BlockId(1))),
            block(5, vec![], Terminator::Return),
        ],
        0,
    )
}

#[test]
fn a_mid_tested_counter_counts_the_pre_test_add() {
    // MEASURED BEFORE: `Some(255)`, one short of the 256 times `c += 1` runs.
    assert_eq!(manual_counter_trip_count(&mid_tested_counter(255)), Some(256));
    assert_eq!(total_loop_iterations(&mid_tested_counter(255)), Some(256));
    // The top-tested and bottom-tested controls keep their exact counts.
    assert_eq!(manual_counter_trip_count(&while_counter(10)), Some(10));
    assert_eq!(
        manual_counter_trip_count(&bottom_tested_min_loop("<u32 as core::cmp::Ord>::min", 5)),
        Some(6)
    );
}

#[test]
fn a_counter_written_after_the_test_counts_from_the_write_not_the_add() {
    // `loop { c += 1; let n = i + 1; if !(i < 10) { break; } i = n; }` — the counter's
    // checked add runs BEFORE the test but its value lands in `i` AFTER it, so the test
    // still sees the old `i` and continues 10 times while `c += 1` runs 11 times. A rule
    // keyed on where the ADD sits ("the counter's add precedes the test, so the count is
    // exact") would return 10.
    //
    // bb0 init | bb1 `ck_c = c+1` | bb2 `c = ck_c.0; ck_i = i+1` | bb3 `t = ck_i.0`, test
    // `i < 10` | bb4 `i = t` -> bb1 | bb5 return. MEASURED BEFORE: `Some(10)`.
    let mut func = counter_func(
        vec![
            block(0, vec![set_const(1, 0), set_const(2, 0)], Terminator::Goto(BlockId(1))),
            block(1, vec![checked_add(2, 5, 1)], overflow_assert(5, 2)),
            block(2, vec![read_back(2, 5), checked_add(1, 4, 1)], overflow_assert(4, 3)),
            block(3, vec![read_back(6, 4), less_than(3, 1, const_u32(10))], switch(3, 5, 4)),
            block(4, vec![copy_local(1, 6)], Terminator::Goto(BlockId(1))),
            block(5, vec![], Terminator::Return),
        ],
        0,
    );
    func.body.locals.push(LocalDecl { index: 6, ty: U32, name: Some("t".into()) });
    assert_eq!(manual_counter_trip_count(&func), Some(11));
}

#[test]
fn a_cycle_that_skips_the_test_is_refused() {
    // `loop { c += 1; if flag { continue; } if !(i < 10) { break; } i += 1; }` — the
    // `continue` loops back above the test without testing or advancing `i`, so `c += 1`
    // runs as long as `flag` holds. Every cycle THROUGH the test still passes the
    // counter's add, which is all the old gates asked.
    //
    // bb0 init | bb1 `ck_c = c+1` | bb2 `c = ck_c.0`, switch on `flag` -> bb1 / bb3 | bb3
    // test `i < 10` | bb4 `ck_i = i+1` | bb5 `i = ck_i.0` -> bb1 | bb6 return.
    // MEASURED BEFORE: `Some(10)`.
    let func = counter_func(
        vec![
            block(0, vec![set_const(1, 0), set_const(2, 0)], Terminator::Goto(BlockId(1))),
            block(1, vec![checked_add(2, 5, 1)], overflow_assert(5, 2)),
            block(2, vec![read_back(2, 5)], switch(6, 3, 1)),
            block(3, vec![less_than(3, 1, const_u32(10))], switch(3, 6, 4)),
            block(4, vec![checked_add(1, 4, 1)], overflow_assert(4, 5)),
            block(5, vec![read_back(1, 4)], Terminator::Goto(BlockId(1))),
            block(6, vec![], Terminator::Return),
        ],
        1,
    );
    assert_eq!(manual_counter_trip_count(&func), None);
    assert_eq!(total_loop_iterations(&func), None);
}

#[test]
fn a_counter_whose_write_is_conditional_is_refused() {
    // `while i < 10 { c += 1; let n = i + 1; if flag { i = n; } }`, with the add on the
    // counter itself — every cycle through the test passes the ADD, but only some pass
    // the write that lands it, so `i` stays put while `flag` is false. No measured
    // program reaches this today (rustc adds a COPY of `i`, which the stride gate
    // refuses), so this row is defensive.
    //
    // bb0 init | bb1 test `i < 10` | bb2 `ck_c = c+1` | bb3 `c = ck_c.0; ck_i = i+1` |
    // bb4 `t = ck_i.0`, switch on `flag` -> bb1 / bb5 | bb5 `i = t` -> bb1 | bb6 return.
    // MEASURED BEFORE: `Some(10)`.
    let mut func = counter_func(
        vec![
            block(0, vec![set_const(1, 0), set_const(2, 0)], Terminator::Goto(BlockId(1))),
            block(1, vec![less_than(3, 1, const_u32(10))], switch(3, 6, 2)),
            block(2, vec![checked_add(2, 5, 1)], overflow_assert(5, 3)),
            block(3, vec![read_back(2, 5), checked_add(1, 4, 1)], overflow_assert(4, 4)),
            block(4, vec![read_back(7, 4)], switch(6, 1, 5)),
            block(5, vec![copy_local(1, 7)], Terminator::Goto(BlockId(1))),
            block(6, vec![], Terminator::Return),
        ],
        1,
    );
    func.body.locals.push(LocalDecl { index: 7, ty: U32, name: Some("t".into()) });
    assert_eq!(manual_counter_trip_count(&func), None);
}

#[test]
fn realmir_a_mid_tested_counter_counts_the_pre_test_add() {
    // `loop { c += 1; if i >= 255 { break; } i += 1; }` (and `c += 2`, and `a[c]` read
    // inside the loop). MEASURED BEFORE: `Some(255)` (`TRUST_ACC … K=255 -> bound c <=
    // 255`, the real `c` is 256), and the `a[c]` bounds row on `[u8; 256]` was
    // kernel-certified.
    for (name, func) in [
        ("mid_idx", trip_fixture!("mid_idx")),
        ("mid_idx2", trip_fixture!("mid_idx2")),
        ("mid_idx_inloop", trip_fixture!("mid_idx_inloop")),
    ] {
        assert_eq!(total_loop_iterations(&func), Some(256), "`{name}`");
    }
    // At `-O` (`mid_wrap`, `i >= 254`). MEASURED BEFORE: `Some(254)`; all three checks
    // were elided and the program returned 0.
    assert_eq!(total_loop_iterations(&trip_fixture!("mid_wrap_opt")), Some(255));
    // Controls. The top-tested `while i < 255` keeps 255, and c5's bottom-tested shape
    // at `-O` (its own write precedes the test) keeps the exact 6.
    assert_eq!(total_loop_iterations(&trip_fixture!("top_idx")), Some(255));
    assert_eq!(total_loop_iterations(&trip_fixture!("c5_like_opt")), Some(6));
}

#[test]
fn realmir_a_cycle_that_skips_the_test_is_refused() {
    // `loop { c += 1; if c == limit { break; } if flag { continue; } i += 1; if i >= 10
    // { break; } }`. MEASURED BEFORE: `Some(10)` for both; `skip_idx`'s `bounds` row on
    // `[u8; 11]` was proved and `skip_wrap(0, true)` returned 0.
    assert_eq!(total_loop_iterations(&trip_fixture!("skip_idx")), None);
    assert_eq!(total_loop_iterations(&trip_fixture!("skip_wrap")), None);
}

#[test]
fn realmir_a_driver_below_a_loop_add_is_refused() {
    // `loop { c += 1; let Some(_) = it.next() else { break }; }` over `0..254u32`, and
    // the `if it.next().is_none() { break; }` twin: 254 items, 255 adds.
    // MEASURED BEFORE: `Some(254)` for both; `it_mid_wrap` returned 0.
    assert_eq!(total_loop_iterations(&trip_fixture!("it_mid_idx")), None);
    assert_eq!(total_loop_iterations(&trip_fixture!("it_mid_wrap")), None);
    // Control: `while let Some(_) = it.next() { c += 1; }` — the driver heads its loop.
    assert_eq!(total_loop_iterations(&trip_fixture!("it_top_idx")), Some(254));
}

// ── TRIP-MID-TEST-1 residual (2026-10-05): the test's OWN block, and a driver's ──
// ── own two blocks, run on the exiting pass ─────────────────────────────────────
//
// REAL extracted MIR of `tests/ui/trust/loop_test_block_add_runs_on_the_exit_pass.rs`
// (`-Ztrust-dump=mir-only:<dir>` on `scratchpad/stage1-w14`, the stage 1 of
// `76a6ea45b2`, 2026-10-05): the `_m2` files at its `m2` flags (`-O
// -Zmir-opt-level=2`), the `_noinline` files at its `noinline` flags
// (`-Zmir-opt-level=2 -Zinline-mir=no`), both with `-Coverflow-checks=on`.

#[test]
fn a_non_trapping_add_in_the_test_block_counts_as_pre_test() {
    // `loop { c = c.overflowing_add(1).0; if !(i < 255) { break; } i += 1; }` once the
    // add is inlined: a NON-trapping checked add in the test block itself.
    //
    // bb0 init | bb1 `ck_c = c+1; c = ck_c.0`, test `i < 255` | bb2 `ck_i = i+1` | bb3
    // `i = ck_i.0` -> bb1 | bb4 return. The test continues 255 times; the add runs 256.
    // MEASURED BEFORE: `Some(255)`, and the accumulator fact `c <= 255`.
    let func = counter_func(
        vec![
            block(0, vec![set_const(1, 0), set_const(2, 0)], Terminator::Goto(BlockId(1))),
            block(
                1,
                vec![checked_add(2, 5, 1), read_back(2, 5), less_than(3, 1, const_u32(255))],
                switch(3, 4, 2),
            ),
            block(2, vec![checked_add(1, 4, 1)], overflow_assert(4, 3)),
            block(3, vec![read_back(1, 4)], Terminator::Goto(BlockId(1))),
            block(4, vec![], Terminator::Return),
        ],
        0,
    );
    assert_eq!(manual_counter_trip_count(&func), Some(256));
    // Trust (merge 2026-10-14): the accumulator lane reads a PER-BLOCK bound
    // (`block_execution_bound`, 956be649567), not `total_loop_iterations`. `c`'s add
    // sits in the test block, which every pass reaches before the test, so it runs
    // `255 + 1` times: `c <= 256`, never `c <= 255`. `i`'s add sits behind the test's
    // continue edge and runs exactly 255 times, so its fact `i <= 255` is true and
    // tight (the former whole-function product gave `i <= 256`). Pinned exactly, so
    // the under-count `c <= 255` stays refused by name rather than by the bare number.
    assert_eq!(
        sorted_acc_facts(&func),
        vec![acc_le("c", 256), acc_le("i", 255)],
        "the accumulator fact must be `c <= 256`, never `c <= 255`"
    );
}

#[test]
fn realmir_a_test_block_add_counts_as_pre_test() {
    // `ovf_wrap` (stable `overflowing_add`, `i >= 254`) and `intr_mid_idx` (the
    // `add_with_overflow` intrinsic, `i >= 255`): the add lands in the test block.
    // MEASURED BEFORE: `Some(254)` / `Some(255)` (`TRUST_ACC … -> bound c <= 254`, the
    // real `c` is 255; `ovf_wrap`'s two overflow checks were elided and it returned 0).
    assert_eq!(total_loop_iterations(&trip_fixture!("ovf_wrap_m2")), Some(255));
    assert_eq!(total_loop_iterations(&trip_fixture!("intr_mid_idx_m2")), Some(256));
    assert_eq!(total_loop_iterations(&trip_fixture!("intr_mid_idx_noinline")), Some(256));
    // Controls: the add in the body of a top-tested `while` keeps the exact count.
    assert_eq!(total_loop_iterations(&trip_fixture!("ovf_top_m2")), Some(254));
    assert_eq!(total_loop_iterations(&trip_fixture!("intr_top_idx_m2")), Some(255));
    assert_eq!(total_loop_iterations(&trip_fixture!("intr_top_idx_noinline")), Some(255));
}

#[test]
fn realmir_an_add_in_a_drivers_own_blocks_is_refused() {
    // `while let Some(_) = { c = add_with_overflow(c, 1).0; it.next() } {}` (the add in
    // the call block of a driver that HEADS its loop) and `let x = it.next(); c = …;
    // let Some(_) = x else { break };` (the add in the block the call returns to), over
    // `0..255u32`: 255 items, 256 adds. MEASURED BEFORE: `Some(255)` for both, and
    // `a[c]` on `[u8; 256]` was proved.
    //
    // Trust (merge 2026-10-14): the accumulator lane does not read
    // `total_loop_iterations` (the refutation lane's whole-function product) but the
    // add block's own bound, `block_execution_bound` (956be649567,
    // `trust_types::loop_nest`): a block NOT behind its loop's driver edge runs
    // `trip + 1` times. Both adds run on the `None` pass, so each gets `c <= 256` —
    // the TRUE count, which leaves `a[c]` on `[u8; 256]` unproved — and never the
    // `c <= 255` under-count this row was written against.
    for (name, func) in [
        ("it_call_block_idx", trip_fixture!("it_call_block_idx_noinline")),
        ("it_switch_block_idx", trip_fixture!("it_switch_block_idx_noinline")),
    ] {
        assert_eq!(total_loop_iterations(&func), None, "`{name}`: the add runs on the None pass");
        assert_eq!(
            sorted_acc_facts(&func),
            vec![acc_le("c", 256)],
            "`{name}`: the accumulator fact counts the None pass (256 adds), never 255"
        );
    }
    // Control: the add in the body of `while let Some(_) = it.next()`.
    assert_eq!(total_loop_iterations(&trip_fixture!("it_top_idx_noinline")), Some(255));
}

// ── TRIP-DRIVER-1: a `next()` on a cycle drives a loop only when the loop exits ──
// ── on its `None` ─────────────────────────────────────────────────────────────
//
// REAL extracted MIR of `tests/ui/trust/loop_driver_must_exit_on_none.rs` (and
// `for_with_stray`, from a probe beside it), captured like the rows above.

#[test]
fn realmir_a_next_that_does_not_drive_its_loop_bounds_nothing() {
    // `let _ = r.next();` in a `loop` that exits on `c == limit`; a manual `while`
    // balanced by a `next` in another loop (sequential and nested); `match r.next() {
    // None => {}, … }`; and an iterator rebuilt on every pass (`is_none()` and
    // `let … else` spellings). MEASURED BEFORE: `Some(2)` for `stray_on_cycle`,
    // `none_continues` and both `fresh_each_iter*`, `Some(1)` for `two_next` and
    // `nested_balance`; `stray_on_cycle(0)` returned 0 where vanilla Rust panics.
    for (name, func) in [
        ("stray_on_cycle", trip_fixture!("stray_on_cycle")),
        ("two_next", trip_fixture!("two_next")),
        ("nested_balance", trip_fixture!("nested_balance")),
        ("none_continues", trip_fixture!("none_continues")),
        ("fresh_each_iter", trip_fixture!("fresh_each_iter")),
        ("fresh_each_iter_let", trip_fixture!("fresh_each_iter_let")),
    ] {
        assert_eq!(total_loop_iterations(&func), None, "`{name}`: no call drives the adding loop");
    }
    // No loop that adds here exits on a `next()`'s `None`, so no `next` call bounds an
    // add, and the loops that exit only on `c == limit` mint no accumulator fact.
    for (name, func) in [
        ("stray_on_cycle", trip_fixture!("stray_on_cycle")),
        ("none_continues", trip_fixture!("none_continues")),
        ("fresh_each_iter", trip_fixture!("fresh_each_iter")),
        ("fresh_each_iter_let", trip_fixture!("fresh_each_iter_let")),
    ] {
        assert!(acc_facts(&func).is_empty(), "`{name}`: no accumulator fact without a trip count");
    }
    // Trust (merge 2026-10-14): `two_next` and `nested_balance` add inside `while j <
    // 1000`, a manual counter loop. The accumulator lane bounds each add block by ITS
    // OWN loop's driver (`block_execution_bound`, 956be649567): here the counter test,
    // which the stray `next` does not balance or replace. So `c <= 1000` and `j <=
    // 1000`, both true (the `c += 1` row stays unproved on `u8`), and never the `c <= 1`
    // the former `#next == #loops` identity read.
    for (name, func) in [
        ("two_next", trip_fixture!("two_next")),
        ("nested_balance", trip_fixture!("nested_balance")),
    ] {
        assert_eq!(
            sorted_acc_facts(&func),
            vec![acc_le("c", 1000), acc_le("j", 1000)],
            "`{name}`: the `while j < 1000` counter bounds the adds, the stray `next` nothing"
        );
    }
}

#[test]
fn realmir_loops_driven_by_their_own_next_keep_their_product() {
    // Controls: a plain `for` (`K = 2`), a nested `for` (`K = 3 * 4`), and a nested
    // `for` with an add in the OUTER body (still `K = 12`: the outer driver bounds it).
    assert_eq!(total_loop_iterations(&trip_fixture!("plain_for")), Some(2));
    assert_eq!(total_loop_iterations(&trip_fixture!("matrix")), Some(12));
    assert_eq!(total_loop_iterations(&trip_fixture!("outer_add_nested")), Some(12));
    // A stray `let _ = r.next();` beside a real `for` driver is ignored, not counted:
    // `for &x in a { let _ = r.next(); t += x as u32; }` over `[u8; 8]`. MEASURED
    // BEFORE: `None` (two `next` calls, one loop), so `t += x` was refuted.
    assert_eq!(total_loop_iterations(&trip_fixture!("for_with_stray")), Some(8));
    // The other wave-14 controls keep their values under the driver rule.
    assert_eq!(total_loop_iterations(&trip_fixture!("it_top_idx")), Some(254));
    assert_eq!(total_loop_iterations(&trip_fixture!("one_then")), Some(300));
}

// ── CAST-SIGNED-REDUCTION-TARGET-1: the signed lane reads the cast TARGET ───────
//
// REAL extracted MIR of `tests/ui/trust/signed_reduction_unsigned_cast_target_not_proved.rs`
// (`-Ztrust-dump=mir-only:<dir>` on `scratchpad/stage1-w15r`, the stage 1 of main +
// wave 15, 2026-10-05, at the fixture's flags `-Coverflow-checks=on`): `sum_u32`,
// `k2_u16`, `k4_u64` and `idx` from its `liars` revision, `sum_i32` and `sum_i8` from
// `holds`. Each body is `for x in a { t += <elem> as ACC; }` over a fixed `[iN; LEN]`.

/// The `(acc, addend)` locals of the body's one overflow-checked self-add.
fn reduction_acc_and_addend(func: &VerifiableFunction) -> (usize, usize) {
    let adds: Vec<(usize, usize)> = func
        .body
        .blocks
        .iter()
        .flat_map(|b| &b.stmts)
        .filter_map(|s| match s {
            Statement::Assign {
                rvalue:
                    Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(acc) | Operand::Move(acc),
                        Operand::Copy(addend) | Operand::Move(addend),
                    ),
                ..
            } if acc.projections.is_empty() && addend.projections.is_empty() => {
                Some((acc.local, addend.local))
            }
            _ => None,
        })
        .collect();
    assert_eq!(adds.len(), 1, "one self-add in `{}`: {adds:?}", func.name);
    adds[0]
}

fn var_named(func: &VerifiableFunction, local: usize) -> trust_types::Formula {
    trust_types::Formula::Var(
        crate::place_to_var_name(func, &Place::local(local)),
        trust_types::Sort::Int,
    )
}

#[test]
fn realmir_an_unsigned_cast_target_gets_no_signed_reduction_range() {
    // `-1i8 as u32 == 4294967295`: the ELEMENT's range is not the ADDEND's. MEASURED
    // BEFORE (the parent commit's lane): `Some((-128, 127))` for the `i8` rows and
    // `Some((-32768, 32767))` / `Some((-2147483648, 2147483647))` for `k2_u16` /
    // `k4_u64`, and six facts each — for `sum_u32` `_9 <= 127`, `t <= 508` and
    // `t + _9 <= 508`, which the Clean kernel re-checked as the overflow proof.
    for (name, func) in [
        ("sum_u32", trip_fixture!("signed_red_sum_u32")),
        ("k2_u16", trip_fixture!("signed_red_k2_u16")),
        ("k4_u64", trip_fixture!("signed_red_k4_u64")),
        ("idx", trip_fixture!("signed_red_idx")),
    ] {
        let (_, addend) = reduction_acc_and_addend(&func);
        assert!(
            matches!(
                crate::local_defs::unique_value_def(&func, addend),
                Some(Rvalue::Cast(_, Ty::Int { signed: false, .. }))
            ),
            "`{name}`: the captured addend is the unsigned cast this row is about"
        );
        assert_eq!(
            super::loop_bounds::signed_addend_per_iteration_range(&func, addend),
            None,
            "`{name}`: an unsigned cast target wraps every negative element"
        );
        // The unsigned lane declines the signed element too, so nothing is emitted.
        assert!(
            super::loop_bounds::build_accumulator_bound_facts(&func).is_empty(),
            "`{name}`: no accumulator fact may describe a wrapped addend: {:?}",
            acc_facts(&func)
        );
    }
}

#[test]
fn realmir_a_value_preserving_signed_target_keeps_the_symmetric_pair() {
    // Controls: `t: i32 += *x as i32` over `[i8; 4]` and the `for &x` spelling over
    // `[i8; 8]` (`proved/signed_accumulator.rs`). Same facts before and after.
    for (name, func, k) in [
        ("sum_i32", trip_fixture!("signed_red_sum_i32"), 4i128),
        ("sum_i8", trip_fixture!("signed_red_sum_i8"), 8),
    ] {
        let (acc, addend) = reduction_acc_and_addend(&func);
        assert_eq!(
            super::loop_bounds::signed_addend_per_iteration_range(&func, addend),
            Some((-128, 127)),
            "`{name}`: `i8 as i32` preserves every element"
        );
        let facts = super::loop_bounds::build_accumulator_bound_facts(&func);
        let (a, x) = (var_named(&func, acc), var_named(&func, addend));
        let sum = trust_types::Formula::Add(Box::new(a.clone()), Box::new(x.clone()));
        let le = |l: &trust_types::Formula, c: i128| {
            trust_types::Formula::Le(Box::new(l.clone()), Box::new(trust_types::Formula::Int(c)))
        };
        let ge = |l: &trust_types::Formula, c: i128| {
            trust_types::Formula::Ge(Box::new(l.clone()), Box::new(trust_types::Formula::Int(c)))
        };
        for want in [
            le(&a, 127 * k),
            ge(&a, -128 * k),
            le(&x, 127),
            ge(&x, -128),
            le(&sum, 127 * k),
            ge(&sum, -128 * k),
        ] {
            assert!(facts.contains(&want), "`{name}`: missing {want:?} in {facts:?}");
        }
    }
}
