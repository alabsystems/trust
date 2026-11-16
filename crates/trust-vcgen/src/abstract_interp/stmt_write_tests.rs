// trust_vcgen/abstract_interp/stmt_write_tests.rs: the interval transfer at a
// statement that writes more than its own destination.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// Trust (2026-10-08, trust-interval-drop-havoc). The statement transfer forgot the
// names its destination rebinds and nothing else. A store through a pointer with more
// than one possible referent writes one of several locals, and the interval of each
// survived it; the discharge then withheld a real overflow from the solver. Measured
// as a build that passed while the program panicked, in plain safe code with no call
// and no drop (probe round `as-r1`). Pinned here on that probe's MIR, transcribed
// from `-Ztrust-dump=mir`:
//
// * an opaque deref store forgets every local a pointer can reach, and the obligation
//   behind the dead-looking arm is dispatched, not discharged;
// * it keeps its own destination and a local no pointer reaches;
// * `SetDiscriminant` and `Deinit` forget the names under their place;
// * a `CopyNonOverlapping` that copies anything forgets everything, one that copies
//   nothing forgets nothing;
// * the same body without the store discharges the obligation (anti-vacuity).
//
// Every fixpoint these tests run also runs the lockstep check of
// `transfer::transfer_statements`: a name kept across a statement is one the formula
// path's `stmt_writes_name` says that statement does not write.
//
// Trust (2026-10-09, independent review). Three planted defects in the statement path
// passed every test above and the whole lib suite, because no fixture had the shape
// that tells them apart: a block with TWO extra-write statements (only the first
// applied), a PROJECTED opaque store (`(*p).0 = v` not recognised), and a loop whose
// head is re-tightened by narrowing so that only the repair pass sees the back edge's
// store. The three tests at the end are the review's (`r3`, `r4`, `r5`); each fails on
// its plant. After them: which statements write, as `Statement::place_writes`
// classifies them.
//
// Trust (2026-10-12, INTERVAL-WRITE-LOCKSTEP-2). Wave 24 widened the formula path's
// oracle (LAUNDERED-ALIAS-STORE: a direct write into escaped storage havocs the
// whole-function list; UNION-SIBLING-WRITE-1: a `SetDiscriminant` / `Deinit` of a union
// field writes its siblings) and not this lane, and the lockstep check failed on
// `a_statement_that_writes_no_place_and_a_borrow_forget_nothing` (`c = 0` before
// `src = &raw mut c` writes escaped storage while `dst` is an unresolved raw pointer;
// that test's own assertions are unchanged and hold). The last two tests pin each
// widening on this lane, each with its anti-vacuity control.

use trust_types::*;

use super::transfer::{FixpointConfig, FixpointResult, fixpoint_configured};
use super::{Interval, merged_interval_environment, type_aware_initial_state};

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn zero() -> Rvalue {
    Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32)))
}

fn function(
    name: &str,
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
    arg_count: usize,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("stmt_write::{name}"),
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

fn local(index: usize, ty: Ty, name: &str) -> LocalDecl {
    LocalDecl { index, ty, name: Some(name.to_string()) }
}

/// The probe `as01_branch_ptr_bug`, with one extra local `e` that no pointer reaches:
///
/// ```text
/// pub fn f(k: u32) -> u32 {
///     let mut c = 0u32;
///     let mut d = 0u32;
///     let p = if k > 3 { &mut c } else { &mut d };
///     *p = k;
///     match c { 0 => d, n => n + u32::MAX }
/// }
/// ```
///
/// ```text
/// bb0: c = 0; d = 0; e = 0; _5 = Gt(copy k, 3)   SwitchInt(move _5): 0 -> bb2, else -> bb1
/// bb1: p = &mut c                                  -> bb3
/// bb2: _6 = &mut d; p = copy _6                    -> bb3
/// bb3: (*p) = copy k                               SwitchInt(copy c): 0 -> bb5, else -> bb4
/// bb4: n = copy c; _8 = CheckedAdd(copy n, u32::MAX)   Assert(!_8.1) -> bb6
/// bb5: _0 = copy d                                 -> bb7
/// bb6: _0 = move _8.0                              -> bb7
/// bb7: Return
/// ```
///
/// `store == false` replaces `(*p) = copy k` with a `Nop` (the anti-vacuity control).
fn selected_pointer(store: bool) -> VerifiableFunction {
    let mut_u32 = Ty::Ref { mutable: true, inner: Box::new(u32_ty()) };
    let locals = vec![
        local(0, u32_ty(), "_0"),
        local(1, u32_ty(), "k"),
        local(2, u32_ty(), "c"),
        local(3, u32_ty(), "d"),
        local(4, mut_u32.clone(), "p"),
        local(5, Ty::Bool, "_5"),
        local(6, mut_u32, "_6"),
        local(7, u32_ty(), "n"),
        local(8, Ty::Tuple(vec![u32_ty(), Ty::Bool]), "_8"),
        local(9, u32_ty(), "e"),
    ];
    let through_p = Place { local: 4, projections: vec![Projection::Deref] };
    let sum = Place { local: 8, projections: vec![Projection::Field(0)] };
    let overflowed = Place { local: 8, projections: vec![Projection::Field(1)] };
    let switch = |discr: Operand, zero_to: usize, otherwise: usize| Terminator::SwitchInt {
        discr,
        targets: vec![(0, BlockId(zero_to))],
        otherwise: BlockId(otherwise),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(2), zero()),
                assign(Place::local(3), zero()),
                assign(Place::local(9), zero()),
                assign(
                    Place::local(5),
                    Rvalue::BinaryOp(
                        BinOp::Gt,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(3, 32)),
                    ),
                ),
            ],
            terminator: switch(Operand::Move(Place::local(5)), 2, 1),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(
                Place::local(4),
                Rvalue::Ref { mutable: true, place: Place::local(2) },
            )],
            terminator: Terminator::Goto(BlockId(3)),
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![
                assign(Place::local(6), Rvalue::Ref { mutable: true, place: Place::local(3) }),
                assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::local(6)))),
            ],
            terminator: Terminator::Goto(BlockId(3)),
        },
        BasicBlock {
            id: BlockId(3),
            stmts: vec![if store {
                assign(through_p, Rvalue::Use(Operand::Copy(Place::local(1))))
            } else {
                Statement::Nop
            }],
            terminator: switch(Operand::Copy(Place::local(2)), 5, 4),
        },
        BasicBlock {
            id: BlockId(4),
            stmts: vec![
                assign(Place::local(7), Rvalue::Use(Operand::Copy(Place::local(2)))),
                assign(
                    Place::local(8),
                    Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(7)),
                        Operand::Constant(ConstValue::Uint(u128::from(u32::MAX), 32)),
                    ),
                ),
            ],
            terminator: Terminator::Assert {
                cond: Operand::Move(overflowed),
                expected: false,
                msg: AssertMessage::Overflow(BinOp::Add),
                target: BlockId(6),
                span: SourceSpan::default(),
                unwind: UnwindEdge::Continue,
            },
        },
        BasicBlock {
            id: BlockId(5),
            stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(3))))],
            terminator: Terminator::Goto(BlockId(7)),
        },
        BasicBlock {
            id: BlockId(6),
            stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Move(sum)))],
            terminator: Terminator::Goto(BlockId(7)),
        },
        BasicBlock { id: BlockId(7), stmts: vec![], terminator: Terminator::Return },
    ];
    function("f", locals, blocks, 1)
}

fn run(func: &VerifiableFunction) -> FixpointResult {
    fixpoint_configured(func, type_aware_initial_state(func), &FixpointConfig::for_function(func))
}

/// Whether the body's one Add-overflow obligation was discharged at generation
/// (withheld from the solver) rather than dispatched.
fn overflow_discharged(func: &VerifiableFunction) -> bool {
    let (solver, discharged) = crate::generate_vcs_with_discharge(func);
    let is_add_overflow = |vc: &VerificationCondition| {
        matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. })
    };
    let in_solver = solver.iter().filter(|vc| is_add_overflow(vc)).count();
    let in_discharged = discharged.iter().filter(|(vc, _)| is_add_overflow(vc)).count();
    assert_eq!(
        in_solver + in_discharged,
        1,
        "ANTI-VACUITY: the fixture has exactly one Add-overflow obligation; solver {solver:?}, \
         discharged {discharged:?}"
    );
    in_discharged == 1
}

/// The control: with no store, `c ∈ [0, 0]` holds at the switch and in the
/// whole-function environment, and the `n` arm's overflow is discharged. This is the
/// conclusion the store must NOT reach.
#[test]
fn without_the_store_the_arm_s_overflow_is_discharged() {
    let func = selected_pointer(false);
    let fp = run(&func);
    assert_eq!(fp.block_states[&BlockId(5)].get("d"), Interval::constant(0));
    assert_eq!(merged_interval_environment(&func).get("c"), Interval::constant(0));
    assert!(overflow_discharged(&func));
}

/// The probe: `p` points at `c` or at `d`, so `*p = k` may write either. Both are
/// forgotten, the arm is live and its overflow goes to the solver (which refutes it:
/// `k = 7` makes `c = 7`). Before this change the store forgot nothing but `p*` and
/// this test saw the control's answer.
#[test]
fn an_opaque_store_forgets_every_local_a_pointer_can_reach() {
    let func = selected_pointer(true);
    let store = &func.body.blocks[3];
    let Statement::Assign { place, .. } = &store.stmts[0] else { unreachable!() };
    assert!(
        crate::deref_store_is_opaque(&func, place),
        "ANTI-VACUITY: `p` has two referents, so the store must be opaque"
    );
    for name in ["c", "d"] {
        assert!(
            crate::generate::stmt_writes_name(&func, store, 0, name),
            "ANTI-VACUITY: the formula path's oracle must say the store writes `{name}`"
        );
    }
    let fp = run(&func);
    // bb5 is entered on the `c == 0` edge, which narrows `c` itself; `d` is the
    // witness there, and `c` on the other edge.
    assert_eq!(fp.block_states[&BlockId(5)].get("d"), Interval::TOP);
    assert_ne!(fp.block_states[&BlockId(4)].get("c"), Interval::constant(0));
    let env = merged_interval_environment(&func);
    assert_ne!(env.get("c"), Interval::constant(0));
    assert_eq!(env.get("d"), Interval::TOP);
    assert!(!overflow_discharged(&func));
}

/// The havoc is the whole-function list, not everything: `e` is never borrowed, no
/// pointer reaches it, and it keeps `[0, 0]` across the store.
#[test]
fn an_opaque_store_keeps_a_local_no_pointer_reaches() {
    let func = selected_pointer(true);
    assert!(
        !crate::generate::stmt_writes_name(&func, &func.body.blocks[3], 0, "e"),
        "ANTI-VACUITY: the oracle must say the store does not write `e`"
    );
    let fp = run(&func);
    assert_eq!(fp.block_states[&BlockId(4)].get("e"), Interval::constant(0));
    assert_eq!(fp.block_states[&BlockId(5)].get("e"), Interval::constant(0));
    assert_eq!(merged_interval_environment(&func).get("e"), Interval::constant(0));
}

/// One block `c = 0; t.0 = 5; <stmt>` then `_0 = copy t.0`, for the statements that
/// write a place without assigning it.
fn after(stmt: Statement) -> (VerifiableFunction, String) {
    let pair = Ty::Tuple(vec![u32_ty(), u32_ty()]);
    let raw = Ty::RawPtr { mutable: true, pointee: Box::new(u32_ty()) };
    let field = Place { local: 2, projections: vec![Projection::Field(0)] };
    let locals = vec![
        local(0, u32_ty(), "_0"),
        local(1, u32_ty(), "c"),
        local(2, pair, "t"),
        local(3, raw.clone(), "src"),
        local(4, raw, "dst"),
    ];
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(1), zero()),
                assign(field.clone(), Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 32)))),
                stmt,
            ],
            terminator: Terminator::Goto(BlockId(1)),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(field.clone())))],
            terminator: Terminator::Return,
        },
    ];
    let func = function("g", locals, blocks, 0);
    let name = crate::place_to_var_name(&func, &field);
    (func, name)
}

fn copy_nonoverlapping(count: u128) -> Statement {
    Statement::CopyNonOverlapping {
        src: Operand::Copy(Place::local(3)),
        dst: Operand::Copy(Place::local(4)),
        count: Operand::Constant(ConstValue::Uint(count, 64)),
        elem_ty: u32_ty(),
        span: SourceSpan::default(),
    }
}

/// `SetDiscriminant` and `Deinit` write every name under their place and nothing
/// else; a `Nop` in their position keeps the field (anti-vacuity).
#[test]
fn set_discriminant_and_deinit_forget_the_names_under_their_place() {
    let (control, field) = after(Statement::Nop);
    let at = run(&control);
    assert_eq!(
        at.block_states[&BlockId(1)].get(&field),
        Interval::constant(5),
        "ANTI-VACUITY: the lane tracks `{field}`"
    );
    for stmt in [
        Statement::SetDiscriminant { place: Place::local(2), variant_index: 1 },
        Statement::Deinit { place: Place::local(2) },
    ] {
        let (func, field) = after(stmt.clone());
        assert!(
            crate::generate::stmt_writes_name(&func, &func.body.blocks[0], 2, &field),
            "ANTI-VACUITY: the oracle must say {stmt:?} writes `{field}`"
        );
        let at = run(&func);
        assert_eq!(at.block_states[&BlockId(1)].get(&field), Interval::TOP, "{stmt:?}");
        assert_eq!(at.block_states[&BlockId(1)].get("c"), Interval::constant(0), "{stmt:?}");
    }
}

/// A `CopyNonOverlapping` writes memory no place names: every local is a possible
/// write, unless it copies a literal zero elements.
#[test]
fn a_pointer_copy_forgets_everything_unless_it_copies_nothing() {
    let (func, field) = after(copy_nonoverlapping(1));
    let at = run(&func);
    assert_eq!(at.block_states[&BlockId(1)].get(&field), Interval::TOP);
    assert_eq!(at.block_states[&BlockId(1)].get("c"), Interval::TOP);

    let (func, field) = after(copy_nonoverlapping(0));
    let at = run(&func);
    assert_eq!(at.block_states[&BlockId(1)].get(&field), Interval::constant(5));
    assert_eq!(at.block_states[&BlockId(1)].get("c"), Interval::constant(0));
}

/// Two opaque stores in ONE block, the facts re-established between them:
/// `bb3: (*p) = copy k; c = 0; d = 0; (*p) = copy k`. After the block neither `c` nor
/// `d` is known. A transfer that applies only the block's FIRST extra write keeps
/// both at `[0, 0]` (review plant RM2).
#[test]
fn every_opaque_store_of_a_block_forgets() {
    let through_p = Place { local: 4, projections: vec![Projection::Deref] };
    let k = || Rvalue::Use(Operand::Copy(Place::local(1)));
    let with = |stmts: Vec<Statement>| {
        let mut func = selected_pointer(true);
        func.body.blocks[3].stmts = stmts;
        func
    };
    // Anti-vacuity: without the second store the re-established facts hold.
    let once = with(vec![
        assign(through_p.clone(), k()),
        assign(Place::local(2), zero()),
        assign(Place::local(3), zero()),
    ]);
    assert_eq!(run(&once).block_states[&BlockId(5)].get("d"), Interval::constant(0));
    let twice = with(vec![
        assign(through_p.clone(), k()),
        assign(Place::local(2), zero()),
        assign(Place::local(3), zero()),
        assign(through_p, k()),
    ]);
    let fp = run(&twice);
    assert_eq!(
        fp.block_states[&BlockId(5)].get("d"),
        Interval::TOP,
        "`d` survived the second store"
    );
    assert_ne!(
        fp.block_states[&BlockId(4)].get("c"),
        Interval::constant(0),
        "`c` survived the second store"
    );
}

/// A PROJECTED opaque store: `p` is `&mut a` or `&mut b` (two pairs) and
/// `(*p).0 = copy k` writes `a.0` or `b.0` (review plant RM6: a store recognised only
/// when its place is exactly `*p`).
///
/// ```text
/// bb0: a.0 = 0; b.0 = 0; _5 = Gt(copy k, 3)   SwitchInt(move _5): 0 -> bb2, else -> bb1
/// bb1: p = &mut a                              -> bb3
/// bb2: _6 = &mut b; p = copy _6                -> bb3
/// bb3: (*p).0 = copy k                         -> bb4
/// bb4: _0 = copy a.0                           Return
/// ```
#[test]
fn a_projected_opaque_store_forgets_the_fields_it_can_reach() {
    let pair = Ty::Tuple(vec![u32_ty(), u32_ty()]);
    let mut_pair = Ty::Ref { mutable: true, inner: Box::new(pair.clone()) };
    let locals = vec![
        local(0, u32_ty(), "_0"),
        local(1, u32_ty(), "k"),
        local(2, pair.clone(), "a"),
        local(3, pair, "b"),
        local(4, mut_pair.clone(), "p"),
        local(5, Ty::Bool, "_5"),
        local(6, mut_pair, "_6"),
    ];
    let a0 = Place { local: 2, projections: vec![Projection::Field(0)] };
    let b0 = Place { local: 3, projections: vec![Projection::Field(0)] };
    let through_p0 = Place { local: 4, projections: vec![Projection::Deref, Projection::Field(0)] };
    let body = |store: bool| {
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    assign(a0.clone(), zero()),
                    assign(b0.clone(), zero()),
                    assign(
                        Place::local(5),
                        Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(3, 32)),
                        ),
                    ),
                ],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(5)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![assign(
                    Place::local(4),
                    Rvalue::Ref { mutable: true, place: Place::local(2) },
                )],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![
                    assign(Place::local(6), Rvalue::Ref { mutable: true, place: Place::local(3) }),
                    assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::local(6)))),
                ],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(3),
                stmts: vec![if store {
                    assign(through_p0.clone(), Rvalue::Use(Operand::Copy(Place::local(1))))
                } else {
                    Statement::Nop
                }],
                terminator: Terminator::Goto(BlockId(4)),
            },
            BasicBlock {
                id: BlockId(4),
                stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(a0.clone())))],
                terminator: Terminator::Return,
            },
        ];
        function("projected_store", locals.clone(), blocks, 1)
    };
    let control = body(false);
    let a0_name = crate::place_to_var_name(&control, &a0);
    let b0_name = crate::place_to_var_name(&control, &b0);
    assert_eq!(
        run(&control).block_states[&BlockId(4)].get(&a0_name),
        Interval::constant(0),
        "ANTI-VACUITY: without the store the lane tracks `{a0_name}`"
    );
    let func = body(true);
    let Statement::Assign { place, .. } = &func.body.blocks[3].stmts[0] else { unreachable!() };
    assert!(crate::deref_store_is_opaque(&func, place), "ANTI-VACUITY: `p` has two referents");
    let at = run(&func);
    assert_eq!(at.block_states[&BlockId(4)].get(&a0_name), Interval::TOP, "`{a0_name}`");
    assert_eq!(at.block_states[&BlockId(4)].get(&b0_name), Interval::TOP, "`{b0_name}`");
}

/// A loop whose body re-establishes `c = 0` and then stores through the selected
/// pointer before the back edge:
///
/// ```text
/// bb0: c = 0; d = 0; i = 0; _5 = Gt(copy k, 3)  SwitchInt(move _5): 0 -> bb2, else -> bb1
/// bb1: p = &mut c                                -> bb3
/// bb2: _6 = &mut d; p = copy _6                  -> bb3
/// bb3: _8 = Lt(copy i, copy k)                   SwitchInt(move _8): 0 -> bb6, else -> bb4
/// bb4: c = 0                                     -> bb5
/// bb5: (*p) = copy k; i = Add(copy i, 1)         -> bb3
/// bb6: _0 = copy c                               Return
/// ```
///
/// On the back edge `c` may be `k`, so the loop head (bb3) and the exit (bb6) know
/// nothing about `c`. Narrowing re-tightens the head from the entry edge; only the
/// repair pass, walking bb5 WITH its store, widens it again (review plant RM4: a
/// repair pass that walks statements without their extra writes).
#[test]
fn a_store_before_the_back_edge_reaches_the_loop_head() {
    let mut_u32 = Ty::Ref { mutable: true, inner: Box::new(u32_ty()) };
    let locals = vec![
        local(0, u32_ty(), "_0"),
        local(1, u32_ty(), "k"),
        local(2, u32_ty(), "c"),
        local(3, u32_ty(), "d"),
        local(4, mut_u32.clone(), "p"),
        local(5, Ty::Bool, "_5"),
        local(6, mut_u32, "_6"),
        local(7, u32_ty(), "i"),
        local(8, Ty::Bool, "_8"),
    ];
    let through_p = Place { local: 4, projections: vec![Projection::Deref] };
    let switch = |discr: usize, zero_to: usize, otherwise: usize| Terminator::SwitchInt {
        discr: Operand::Move(Place::local(discr)),
        targets: vec![(0, BlockId(zero_to))],
        otherwise: BlockId(otherwise),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(2), zero()),
                assign(Place::local(3), zero()),
                assign(Place::local(7), zero()),
                assign(
                    Place::local(5),
                    Rvalue::BinaryOp(
                        BinOp::Gt,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(3, 32)),
                    ),
                ),
            ],
            terminator: switch(5, 2, 1),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(
                Place::local(4),
                Rvalue::Ref { mutable: true, place: Place::local(2) },
            )],
            terminator: Terminator::Goto(BlockId(3)),
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![
                assign(Place::local(6), Rvalue::Ref { mutable: true, place: Place::local(3) }),
                assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::local(6)))),
            ],
            terminator: Terminator::Goto(BlockId(3)),
        },
        BasicBlock {
            id: BlockId(3),
            stmts: vec![assign(
                Place::local(8),
                Rvalue::BinaryOp(
                    BinOp::Lt,
                    Operand::Copy(Place::local(7)),
                    Operand::Copy(Place::local(1)),
                ),
            )],
            terminator: switch(8, 6, 4),
        },
        BasicBlock {
            id: BlockId(4),
            stmts: vec![assign(Place::local(2), zero())],
            terminator: Terminator::Goto(BlockId(5)),
        },
        BasicBlock {
            id: BlockId(5),
            stmts: vec![
                assign(through_p, Rvalue::Use(Operand::Copy(Place::local(1)))),
                assign(
                    Place::local(7),
                    Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(7)),
                        Operand::Constant(ConstValue::Uint(1, 32)),
                    ),
                ),
            ],
            terminator: Terminator::Goto(BlockId(3)),
        },
        BasicBlock {
            id: BlockId(6),
            stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(2))))],
            terminator: Terminator::Return,
        },
    ];
    let func = function("loop_store", locals, blocks, 1);
    let fp = run(&func);
    assert_eq!(
        fp.block_states[&BlockId(5)].get("c"),
        Interval::constant(0),
        "ANTI-VACUITY: the body re-establishes `c`"
    );
    assert_eq!(fp.block_states[&BlockId(3)].get("c"), Interval::TOP, "the loop head kept `c`");
    assert_eq!(fp.block_states[&BlockId(6)].get("c"), Interval::TOP, "the loop exit kept `c`");
}

/// WHICH statements write is `Statement::place_writes`' classification, not a list
/// kept in this lane. A statement it classifies as writing memory no place names
/// forgets every tracked name — an intrinsic other than `assume`, an `Unsupported`
/// statement — and the two shapes measured to write nothing keep everything:
/// `assume` (the generator's own metadata no-op) and a pointer copy of zero elements
/// (pinned above).
#[test]
fn an_unlocatable_statement_forgets_everything_unless_it_is_known_to_write_nothing() {
    let flag = Operand::Constant(ConstValue::Bool(true));
    let assume = Statement::Intrinsic { name: "assume".to_string(), args: vec![flag.clone()] };
    assert_eq!(
        assume.place_writes(),
        PlaceWrites::Unlocatable,
        "ANTI-VACUITY: `assume` is spared by this lane's own exception, not by the classifier"
    );
    let (func, field) = after(assume);
    let at = run(&func);
    assert_eq!(at.block_states[&BlockId(1)].get(&field), Interval::constant(5));
    assert_eq!(at.block_states[&BlockId(1)].get("c"), Interval::constant(0));

    for stmt in [
        Statement::Intrinsic { name: "volatile_store".to_string(), args: vec![flag.clone()] },
        // `assume` is the no-op only in the one shape the generator clears.
        Statement::Intrinsic { name: "assume".to_string(), args: vec![] },
        Statement::Unsupported {
            kind: "BackwardIncompatibleDropHint".to_string(),
            detail: String::new(),
            operands: vec![],
            span: SourceSpan::default(),
        },
    ] {
        assert_eq!(stmt.place_writes(), PlaceWrites::Unlocatable, "ANTI-VACUITY: {stmt:?}");
        let (func, field) = after(stmt.clone());
        let at = run(&func);
        assert_eq!(at.block_states[&BlockId(1)].get(&field), Interval::TOP, "{stmt:?}");
        assert_eq!(at.block_states[&BlockId(1)].get("c"), Interval::TOP, "{stmt:?}");
    }
}

/// The other side: a statement that writes no place, and one whose only write beyond
/// its destination is a borrow it TAKES, forget nothing. (The write through the
/// borrow is a later store or call.)
#[test]
fn a_statement_that_writes_no_place_and_a_borrow_forget_nothing() {
    for stmt in [
        Statement::StorageDead(3),
        Statement::Retag { place: Place::local(2) },
        Statement::PlaceMention(Place::local(1)),
        // `src = &raw mut c`: a `RawBorrow` of `c` and a store to `src`.
        assign(Place::local(3), Rvalue::AddressOf(true, Place::local(1))),
    ] {
        let (func, field) = after(stmt.clone());
        let at = run(&func);
        assert_eq!(at.block_states[&BlockId(1)].get(&field), Interval::constant(5), "{stmt:?}");
        assert_eq!(at.block_states[&BlockId(1)].get("c"), Interval::constant(0), "{stmt:?}");
    }
}

/// INTERVAL-WRITE-LOCKSTEP-2 (2026-10-12): `len = m; p = &raw mut len; w = p as *mut
/// u8; q = w as *mut u32; (*q) = 5; <write>` then `_0 = copy (*q)`. The
/// pointee-changing cast does not fold, so `*q` is the opaque `q*` and the store through
/// `q` sets it to `[5, 5]`; `len` is escaped storage (its raw address is taken) in a body
/// that reads through that unresolved pointer. `<write>` is statement 5.
fn laundered_store(write: Statement) -> (VerifiableFunction, String) {
    let raw = |pointee: Ty| Ty::RawPtr { mutable: true, pointee: Box::new(pointee) };
    let through_q = Place { local: 5, projections: vec![Projection::Deref] };
    let locals = vec![
        local(0, u32_ty(), "_0"),
        local(1, u32_ty(), "m"),
        local(2, u32_ty(), "n"),
        local(3, u32_ty(), "len"),
        local(4, raw(u32_ty()), "p"),
        local(5, raw(u32_ty()), "q"),
        local(6, raw(Ty::Int { width: 8, signed: false }), "w"),
        local(7, u32_ty(), "x"),
    ];
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(3), Rvalue::Use(Operand::Copy(Place::local(1)))),
                assign(Place::local(4), Rvalue::AddressOf(true, Place::local(3))),
                assign(
                    Place::local(6),
                    Rvalue::Cast(
                        Operand::Copy(Place::local(4)),
                        raw(Ty::Int { width: 8, signed: false }),
                    ),
                ),
                assign(
                    Place::local(5),
                    Rvalue::Cast(Operand::Copy(Place::local(6)), raw(u32_ty())),
                ),
                assign(through_q.clone(), Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 32)))),
                write,
            ],
            terminator: Terminator::Goto(BlockId(1)),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(through_q.clone())))],
            terminator: Terminator::Return,
        },
    ];
    let func = function("laundered", locals, blocks, 2);
    let name = crate::place_to_var_name(&func, &through_q);
    (func, name)
}

/// A DIRECT write into escaped storage forgets the interval of a read through an
/// unresolved copy of its address, exactly as the formula path's oracle versions it
/// (LAUNDERED-ALIAS-STORE's `write_havocs_function_list`, asked by both lanes). Before
/// INTERVAL-WRITE-LOCKSTEP-2 this lane asked only "is it an opaque deref store?", kept
/// `q* ∈ [5, 5]` across `len = n`, and the lockstep check failed. A write to a local
/// whose address is never taken keeps it (anti-vacuity).
#[test]
fn a_write_into_escaped_storage_forgets_an_unresolved_copy_s_pointee() {
    let n = || Rvalue::Use(Operand::Copy(Place::local(2)));
    let (control, q_star) = laundered_store(assign(Place::local(7), n()));
    assert!(q_star.contains('*'), "`*q` must be the opaque `q*`, got `{q_star}`");
    assert!(
        !crate::generate::stmt_writes_name(&control, &control.body.blocks[0], 5, &q_star),
        "ANTI-VACUITY: `x = n` does not write `{q_star}`"
    );
    assert_eq!(
        run(&control).block_states[&BlockId(1)].get(&q_star),
        Interval::constant(5),
        "ANTI-VACUITY: the lane tracks `{q_star}` past a write that does not reach it"
    );

    let (func, q_star) = laundered_store(assign(Place::local(3), n()));
    assert!(
        crate::generate::write_havocs_function_list(&func, &Place::local(3)),
        "`len = n` is a write into escaped storage"
    );
    assert!(
        crate::generate::stmt_writes_name(&func, &func.body.blocks[0], 5, &q_star),
        "the oracle versions `{q_star}` at `len = n`"
    );
    assert_eq!(run(&func).block_states[&BlockId(1)].get(&q_star), Interval::TOP);
}

/// A union whose field 0 is an enum and whose field 1 is a `u32` (`kind` stamps it; a
/// `Struct` is the control). `u.1 = 5; <stmt>` then `_0 = copy u.1`.
fn union_sibling(
    kind: AdtKind,
    stmt: impl FnOnce(Place) -> Statement,
) -> (VerifiableFunction, String) {
    let mut two = Ty::adt(
        "c::U",
        vec![("a".into(), Ty::adt("core::option::Option<u8>", Vec::new())), ("b".into(), u32_ty())],
    );
    if let Ty::Adt { adt_kind, .. } = &mut two {
        *adt_kind = Some(kind);
    }
    let field = |i: usize| Place { local: 1, projections: vec![Projection::Field(i)] };
    let locals = vec![local(0, u32_ty(), "_0"), local(1, two, "u")];
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(field(1), Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 32)))),
                stmt(field(0)),
            ],
            terminator: Terminator::Goto(BlockId(1)),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(field(1))))],
            terminator: Terminator::Return,
        },
    ];
    let func = function("union_sibling", locals, blocks, 0);
    let name = crate::place_to_var_name(&func, &field(1));
    (func, name)
}

/// A `Deinit(u.0)` and a `discriminant(u.0) = 0` each rewrite bytes the overlapping
/// sibling `u.b` reads. UNION-SIBLING-WRITE-1 gave both statements the union cover in the
/// formula path's oracle and not in this lane, which kept `u.1 ∈ [5, 5]`
/// (INTERVAL-WRITE-LOCKSTEP-2). The same statements over a STRUCT keep the sibling.
#[test]
fn a_union_field_discriminant_write_or_deinit_forgets_the_overlapping_sibling() {
    let set_discriminant = |place: Place| Statement::SetDiscriminant { place, variant_index: 0 };
    let deinit = |place: Place| Statement::Deinit { place };
    for (kind, want) in [(AdtKind::Union, Interval::TOP), (AdtKind::Struct, Interval::constant(5))]
    {
        for (stmt, what) in [
            (&set_discriminant as &dyn Fn(Place) -> Statement, "SetDiscriminant"),
            (&deinit, "Deinit"),
        ] {
            let (func, sibling) = union_sibling(kind, stmt);
            assert_eq!(
                crate::generate::stmt_writes_name(&func, &func.body.blocks[0], 1, &sibling),
                kind == AdtKind::Union,
                "{kind:?}: the oracle on {what} and `{sibling}`"
            );
            assert_eq!(
                run(&func).block_states[&BlockId(1)].get(&sibling),
                want,
                "{kind:?}: `{sibling}` after {what} of field 0"
            );
        }
    }
}

/// UNION-SIBLING-WRITE-2 (2026-10-12, the review of INTERVAL-WRITE-LOCKSTEP-2): `u.0 = 5;
/// r = &mut u.1; <write through r>` then `_0 = copy u.0`, with `<write through r>` a
/// store `(*r) = n` (`call == false`) or a call `set(move r, n)`. `kind` stamps `u`'s
/// type; a `Struct` is the control.
fn union_ref_write(kind: AdtKind, call: bool) -> (VerifiableFunction, String) {
    let mut two = Ty::adt("c::U", vec![("a".into(), u32_ty()), ("b".into(), u32_ty())]);
    if let Ty::Adt { adt_kind, .. } = &mut two {
        *adt_kind = Some(kind);
    }
    let field = |i: usize| Place { local: 2, projections: vec![Projection::Field(i)] };
    let locals = vec![
        local(0, u32_ty(), "_0"),
        local(1, u32_ty(), "n"),
        local(2, two, "u"),
        local(3, Ty::Ref { mutable: true, inner: Box::new(u32_ty()) }, "r"),
        local(4, Ty::Unit, "_4"),
    ];
    let mut stmts = vec![
        assign(field(0), Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 32)))),
        assign(Place::local(3), Rvalue::Ref { mutable: true, place: field(1) }),
    ];
    let terminator = if call {
        Terminator::Call {
            unwind: UnwindEdge::Continue,
            func: "c::set".into(),
            args: vec![Operand::Move(Place::local(3)), Operand::Copy(Place::local(1))],
            dest: Place::local(4),
            target: Some(BlockId(1)),
            span: SourceSpan::default(),
            atomic: None,
            is_unsafe_sig: false,
            callee_identity: None,
            callee_key: crate::sep_engine::tests::fixture_key("c::set"),
            is_foreign: false,
        }
    } else {
        stmts.push(assign(
            Place { local: 3, projections: vec![Projection::Deref] },
            Rvalue::Use(Operand::Copy(Place::local(1))),
        ));
        Terminator::Goto(BlockId(1))
    };
    let blocks = vec![
        BasicBlock { id: BlockId(0), stmts, terminator },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(field(0))))],
            terminator: Terminator::Return,
        },
    ];
    let func = function("union_ref_write", locals, blocks, 1);
    let name = crate::place_to_var_name(&func, &field(0));
    (func, name)
}

/// A store through `&mut u.b`, and a call handed `&mut u.b`, each rewrite the bytes
/// `u.a` reads: the interval lane forgets `u.0`, as the formula path's oracle versions
/// it (the lockstep check of `transfer_statements` runs on every statement here). FAILS
/// BEFORE: both kept `u.0 ∈ [5, 5]` (the cover was taken on the syntactic `(*r)`, and
/// the call havoc carried `u.1`, not `u`). Over a STRUCT both keep it.
#[test]
fn a_write_through_a_pointer_into_a_union_field_forgets_the_sibling() {
    for call in [false, true] {
        for (kind, want) in
            [(AdtKind::Union, Interval::TOP), (AdtKind::Struct, Interval::constant(5))]
        {
            let (func, sibling) = union_ref_write(kind, call);
            assert_eq!(
                run(&func).block_states[&BlockId(1)].get(&sibling),
                want,
                "{kind:?}, call={call}: `{sibling}` after the write through `r`"
            );
        }
    }
}
