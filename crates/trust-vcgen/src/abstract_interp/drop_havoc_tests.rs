// trust_vcgen/abstract_interp/drop_havoc_tests.rs: the interval transfer at a
// `Drop` terminator, and its lockstep with the formula path at every terminator.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// Trust (2026-10-04, trust-interval-drop-havoc). The interval transfer havocked only
// at `Call`/`TailCall` (and, since H3 OPAQUE-ASM-OUTPUT, at `Opaque`). Drop glue runs
// user code with `&mut` to the dropped value and to everything mut-reachable from it,
// so an interval established before a `Drop` outlived a write the glue made, and the
// discharge (which reads a post-drop SSA version through its bare-name fallback)
// withheld a real overflow from the solver. Measured as a build that passed while the
// program panicked (probe rounds `dh-r1`/`dh-r2`). Pinned here on that probe's MIR,
// transcribed from `-Ztrust-dump=mir`:
//
// * a `Drop` forgets every name its `terminator_def_names_structured` list rebinds,
//   and the obligation behind the dead-looking arm is dispatched, not discharged;
// * it forgets the dropped place itself (the list's extras), not only the
//   whole-function list;
// * it forgets nothing else (a local the glue cannot reach keeps its interval);
// * an `Opaque` terminator forgets a local no pointer reaches (H3's every-local list);
// * the same body with a plain `Goto` in place of the `Drop` discharges the
//   obligation (anti-vacuity: the fixture's obligation is one the interval lane does
//   discharge while the fact survives);
// * LOCKSTEP: at every terminator of every fixture, the interval transfer forgets
//   exactly when the formula path's write set is non-empty.

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

/// How the fixture's first block ends.
#[derive(Clone, Copy, Debug)]
enum End {
    /// `drop(_s)`: the guard's glue runs.
    Drop,
    /// An inline `asm!` (`Opaque { kind: "InlineAsm" }`).
    Opaque,
    /// No code runs (the anti-vacuity control).
    Goto,
}

/// The probe `dh01_match_overflow_bug`:
///
/// ```text
/// pub struct Setter<'a> { r: &'a mut u32, v: u32 }
/// impl Drop for Setter<'_> { fn drop(&mut self) { *self.r = self.v; } }
/// pub fn f(k: u32) -> u32 {
///     let mut c = 0u32;
///     { let _s = Setter { r: &mut c, v: k }; }
///     match c { 0 => 0, n => n + u32::MAX }
/// }
/// ```
///
/// ```text
/// bb0: c = 0; _4 = &mut c; _s = Setter { copy _4, copy k }   -> drop(_s) -> bb1
/// bb1: SwitchInt(copy c): 0 -> bb3, else -> bb2
/// bb2: n = copy c; _6 = CheckedAdd(copy n, u32::MAX)  Assert(!_6.1) -> bb4
/// bb3: _0 = 0                                                 -> bb5
/// bb4: _0 = _6.0                                              -> bb5
/// bb5: Return
/// ```
///
/// `borrowed == false` drops the `_4 = &mut c` statement, so `c` is in no havoc list
/// (`_4` and `_s` still are: their types carry a `&mut`).
fn guard(end: End, borrowed: bool) -> VerifiableFunction {
    let local =
        |index: usize, ty: Ty, name: &str| LocalDecl { index, ty, name: Some(name.to_string()) };
    let mut_u32 = Ty::Ref { mutable: true, inner: Box::new(u32_ty()) };
    let setter = Ty::adt(
        "drop_havoc::Setter",
        vec![("r".to_string(), mut_u32.clone()), ("v".to_string(), u32_ty())],
    );
    let locals = vec![
        local(0, u32_ty(), "_0"),
        local(1, u32_ty(), "k"),
        local(2, u32_ty(), "c"),
        local(3, setter, "_s"),
        local(4, mut_u32, "_4"),
        local(5, u32_ty(), "n"),
        local(6, Ty::Tuple(vec![u32_ty(), Ty::Bool]), "_6"),
    ];
    let mut bb0 =
        vec![assign(Place::local(2), Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))))];
    if borrowed {
        bb0.push(assign(Place::local(4), Rvalue::Ref { mutable: true, place: Place::local(2) }));
    }
    bb0.push(assign(
        Place::local(3),
        Rvalue::Aggregate(
            AggregateKind::Adt {
                name: "drop_havoc::Setter".into(),
                variant: 0,
                active_field: None,
                args: None,
            },
            vec![Operand::Copy(Place::local(4)), Operand::Copy(Place::local(1))],
        ),
    ));
    let end0 = match end {
        End::Drop => Terminator::Drop {
            place: Place::local(3),
            target: BlockId(1),
            span: SourceSpan::default(),
            unwind: UnwindEdge::Continue,
        },
        End::Opaque => Terminator::Opaque {
            kind: "InlineAsm".to_string(),
            targets: vec![BlockId(1)],
            span: SourceSpan::default(),
        },
        End::Goto => Terminator::Goto(BlockId(1)),
    };
    let sum = Place { local: 6, projections: vec![Projection::Field(0)] };
    let overflowed = Place { local: 6, projections: vec![Projection::Field(1)] };
    let blocks = vec![
        BasicBlock { id: BlockId(0), stmts: bb0, terminator: end0 },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(2)),
                targets: vec![(0, BlockId(3))],
                otherwise: BlockId(2),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![
                assign(Place::local(5), Rvalue::Use(Operand::Copy(Place::local(2)))),
                assign(
                    Place::local(6),
                    Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(5)),
                        Operand::Constant(ConstValue::Uint(u128::from(u32::MAX), 32)),
                    ),
                ),
            ],
            terminator: Terminator::Assert {
                cond: Operand::Move(overflowed),
                expected: false,
                msg: AssertMessage::Overflow(BinOp::Add),
                target: BlockId(4),
                span: SourceSpan::default(),
                unwind: UnwindEdge::Continue,
            },
        },
        BasicBlock {
            id: BlockId(3),
            stmts: vec![assign(
                Place::local(0),
                Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
            )],
            terminator: Terminator::Goto(BlockId(5)),
        },
        BasicBlock {
            id: BlockId(4),
            stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Move(sum)))],
            terminator: Terminator::Goto(BlockId(5)),
        },
        BasicBlock { id: BlockId(5), stmts: vec![], terminator: Terminator::Return },
    ];
    VerifiableFunction {
        name: "f".to_string(),
        def_path: "drop_havoc::f".to_string(),
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

fn run(func: &VerifiableFunction) -> FixpointResult {
    fixpoint_configured(func, type_aware_initial_state(func), &FixpointConfig::for_function(func))
}

/// What the interval lane concluded about the probe's dead-looking arm.
#[derive(Debug, PartialEq)]
struct Answer {
    /// `c` at the switch (bb1).
    c_at_switch: Interval,
    /// `c` in the whole-function environment the discharge reads.
    c_in_env: Interval,
    /// The arm's overflow obligation was discharged at generation (withheld from the
    /// solver) rather than dispatched.
    overflow_discharged: bool,
}

fn answer(func: &VerifiableFunction) -> Answer {
    let fp = run(func);
    let env = merged_interval_environment(func);
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
    Answer {
        c_at_switch: fp.block_states[&BlockId(1)].get("c"),
        c_in_env: env.get("c"),
        overflow_discharged: in_discharged == 1,
    }
}

/// The control: no code runs between `c = 0` and the switch, so `c ∈ [0, 0]` holds
/// there and in the whole-function environment, and the interval lane discharges the
/// `n` arm's overflow (the arm's path condition `c != 0` is false under it; the
/// fixpoint itself does not mark the arm unreachable). This is the conclusion the
/// `Drop` must NOT reach.
#[test]
fn without_a_write_the_arm_s_overflow_is_discharged() {
    let a = answer(&guard(End::Goto, true));
    assert_eq!(a.c_at_switch, Interval::constant(0), "{a:?}");
    assert_eq!(a.c_in_env, Interval::constant(0), "{a:?}");
    assert!(a.overflow_discharged, "{a:?}");
}

/// The probe: `_s`'s drop glue may write `c` through the `&mut c` it holds, so the
/// `Drop` forgets `c`, the arm is reachable, and the overflow goes to the solver
/// (which refutes it: `k = 7` makes `c = 7`). Before this change the transfer skipped
/// the `Drop` and this test saw the control's answer: `c ∈ [0, 0]` at the switch and
/// in the environment, the overflow discharged.
#[test]
fn a_drop_forgets_what_its_glue_can_write() {
    let func = guard(End::Drop, true);
    let names = crate::generate::terminator_def_names(&func, &func.body.blocks[0]);
    assert!(
        names.iter().any(|n| n == "c"),
        "ANTI-VACUITY: the formula path's Drop havoc must name `c`: {names:?}"
    );
    let a = answer(&func);
    assert_eq!(a.c_at_switch, Interval::TOP, "{a:?}");
    assert_eq!(a.c_in_env, Interval::TOP, "{a:?}");
    assert!(!a.overflow_discharged, "{a:?}");
}

/// The havoc is the formula path's set, not everything: with no `&mut c` anywhere,
/// the glue cannot reach `c`, so the `Drop` keeps `c ∈ [0, 0]` and the discharge it
/// licenses. (`_4` and `_s` are in the set and are forgotten.)
#[test]
fn a_drop_keeps_what_its_glue_cannot_reach() {
    let func = guard(End::Drop, false);
    let names = crate::generate::terminator_def_names(&func, &func.body.blocks[0]);
    assert!(
        !names.iter().any(|n| n == "c") && names.iter().any(|n| n == "_s"),
        "ANTI-VACUITY: the Drop havoc must name the dropped `_s` and not `c`: {names:?}"
    );
    let a = answer(&func);
    assert_eq!(a.c_at_switch, Interval::constant(0), "{a:?}");
    assert_eq!(a.c_in_env, Interval::constant(0), "{a:?}");
    assert!(a.overflow_discharged, "{a:?}");
}

/// An `Opaque` terminator's writes are not in the body (an `asm!` output operand
/// writes a local that is neither borrowed nor a pointer), so the formula path names
/// EVERY local at it (H3 OPAQUE-ASM-OUTPUT) and this lane forgets `c`, which no
/// pointer reaches here.
#[test]
fn an_opaque_terminator_forgets_a_local_no_pointer_reaches() {
    let func = guard(End::Opaque, false);
    let names = crate::generate::terminator_def_names(&func, &func.body.blocks[0]);
    assert!(
        names.iter().any(|n| n == "c"),
        "ANTI-VACUITY: the formula path's Opaque write set must name every local, `c` \
         included: {names:?}"
    );
    assert!(
        !crate::generate::function_havoc_names(&func).iter().any(|n| n == "c"),
        "ANTI-VACUITY: `c` must not be in the whole-function list, so only the every-local \
         extras name it"
    );
    let fp = run(&func);
    assert_eq!(fp.block_states[&BlockId(1)].get("c"), Interval::TOP);
    assert_eq!(merged_interval_environment(&func).get("c"), Interval::TOP);
}

/// The dropped place itself: a pointer-free value with a `Drop` impl is in no
/// whole-function list, and its glue still holds `&mut` to it. The `Drop`'s extras
/// name it, so a tracked field of the dropped place is forgotten while an unrelated
/// local keeps its interval.
///
/// ```text
/// bb0: c = 0; p = Plain { 5 }; p.0 = 5   -> drop(p) -> bb1
/// bb1: _0 = copy p.0                      -> return
/// ```
#[test]
fn a_drop_forgets_the_dropped_place_itself() {
    let local =
        |index: usize, ty: Ty, name: &str| LocalDecl { index, ty, name: Some(name.to_string()) };
    let plain = Ty::adt("drop_havoc::Plain", vec![("n".to_string(), u32_ty())]);
    let field = Place { local: 2, projections: vec![Projection::Field(0)] };
    let five = || Operand::Constant(ConstValue::Uint(5, 32));
    let body = |end: Terminator| VerifiableFunction {
        name: "g".to_string(),
        def_path: "drop_havoc::g".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                local(0, u32_ty(), "_0"),
                local(1, u32_ty(), "c"),
                local(2, plain.clone(), "p"),
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        assign(
                            Place::local(1),
                            Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                        ),
                        assign(
                            Place::local(2),
                            Rvalue::Aggregate(
                                AggregateKind::Adt {
                                    name: "drop_havoc::Plain".into(),
                                    variant: 0,
                                    active_field: None,
                                    args: None,
                                },
                                vec![five()],
                            ),
                        ),
                        assign(field.clone(), Rvalue::Use(five())),
                    ],
                    terminator: end,
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(field.clone())))],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 0,
            return_ty: u32_ty(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let field_name = |func: &VerifiableFunction| crate::place_to_var_name(func, &field);

    let control = body(Terminator::Goto(BlockId(1)));
    let name = field_name(&control);
    assert_eq!(
        run(&control).block_states[&BlockId(1)].get(&name),
        Interval::constant(5),
        "ANTI-VACUITY: without the drop the lane tracks `{name}`"
    );

    let dropped = body(Terminator::Drop {
        place: Place::local(2),
        target: BlockId(1),
        span: SourceSpan::default(),
        unwind: UnwindEdge::Continue,
    });
    assert!(
        crate::generate::function_havoc_names(&dropped).is_empty(),
        "ANTI-VACUITY: nothing here is borrowed or a pointer, so only the Drop's extras \
         can name `p`: {:?}",
        crate::generate::function_havoc_names(&dropped)
    );
    let at_bb1 = &run(&dropped).block_states[&BlockId(1)];
    assert_eq!(at_bb1.get(&name), Interval::TOP, "the dropped place's field survived its glue");
    assert_eq!(at_bb1.get("c"), Interval::constant(0), "an unrelated local was forgotten");
}

/// LOCKSTEP. The interval transfer forgets a name at a terminator exactly when the
/// formula path's write set (`terminator_def_names`) rebinds it, and a terminator
/// that runs no code has an EMPTY set there. The `Drop` gap was a terminator with a
/// non-empty set that the transfer skipped. (`CallHavoc::of` makes the same
/// comparison at every visit of every fixpoint this crate's tests run.)
#[test]
fn the_transfer_havocs_wherever_the_formula_path_writes() {
    for (end, borrowed) in [
        (End::Drop, true),
        (End::Drop, false),
        (End::Opaque, true),
        (End::Opaque, false),
        (End::Goto, true),
    ] {
        let func = guard(end, borrowed);
        let fp = run(&func);
        // bb0 ends in `end`, with `c ∈ [0, 0]` tracked on entry to its terminator.
        let names = crate::generate::terminator_def_names(&func, &func.body.blocks[0]);
        let formula_path_writes_c = names.iter().any(|n| n == "c");
        let transfer_forgot_c = fp.block_states[&BlockId(1)].get("c") == Interval::TOP;
        assert_eq!(
            transfer_forgot_c, formula_path_writes_c,
            "{end:?}, borrowed {borrowed}: the transfer and the formula path disagree about \
             `c`; the formula path's set is {names:?}"
        );
        assert_eq!(
            names.is_empty(),
            matches!(end, End::Goto),
            "ANTI-VACUITY ({end:?}): a terminator that runs code has a write set: {names:?}"
        );
        // bb1..bb5 end in SwitchInt, Assert, Goto, Goto and Return: no code runs.
        for block in &func.body.blocks[1..] {
            let names = crate::generate::terminator_def_names(&func, block);
            assert!(
                names.is_empty(),
                "{end:?}: bb{} ({:?}) runs no code but has the write set {names:?}",
                block.id.0,
                block.terminator
            );
        }
    }
}

/// The `Drop` and `Opaque` havocs are derived once per block per run, like a call's.
#[test]
fn each_writing_terminator_is_derived_once_per_run() {
    for (end, borrowed) in [(End::Drop, true), (End::Drop, false), (End::Opaque, false)] {
        let func = guard(end, borrowed);
        reset_analysis_memo_stats();
        let _ = run(&func);
        let stats = analysis_memo_stats();
        assert!(
            stats.interval_fixpoint_units > 6,
            "ANTI-VACUITY ({end:?}): {} units",
            stats.interval_fixpoint_units
        );
        assert_eq!(stats.interval_havoc_sets, 1, "{end:?}, borrowed {borrowed}");
    }
    reset_analysis_memo_stats();
    let _ = run(&guard(End::Goto, true));
    assert_eq!(analysis_memo_stats().interval_havoc_sets, 0, "a Goto derives no havoc");
}
