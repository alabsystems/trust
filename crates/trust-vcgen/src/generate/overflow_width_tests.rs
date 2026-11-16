// Width-soundness regression: an overflow VC must be built at the operation's
// TRUE width, never at a width fabricated from widthless constants.
//
// `ConstValue::Int` carries no width in TrustIR, so `operand_ty`/`int_op_type`
// fabricate i64 for it. A public/forged body `_0: i8 = Add(const 100, const 100)`
// passes admission (`validate_binary_assignment_types` checks each literal FITS
// the i8 destination — 100 does) yet its runtime i8 addition overflows (200 >
// 127). Before the destination-type threading, the plain Add/Sub/Mul arm built
// the violation at the fabricated i64 width — `200 outside [i64::MIN, i64::MAX]`
// is UNSAT, so the row PROVED and the real i8 overflow was certified away: a
// FALSE PROVE. The same hole existed on the checked-assert lane
// (`CheckedBinaryOp(Add, 100, 100)` into an `(i8, bool)` carrier).
//
// The fix threads the VALIDATED assignment-destination type — the audited
// operation type, which admission pins every operand to — into
// `v2_build_overflow_vc_for_operands_typed`, mirroring what the
// `UncheckedBinaryOp` arm already did. These tests pin the violation core at
// the i8 bound (`Gt(100 + 100, 127)`, which is SAT — the row is refutable) and
// FAIL if the threading is reverted (the core would carry `i64::MAX` again and
// the `Int(127)` bound would vanish).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place,
    Rvalue, SourceSpan, Statement, Terminator, Ty, UnwindEdge, VcKind, VerifiableBody,
    VerifiableFunction,
};

fn make_func(
    name: &str,
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
    arg_count: usize,
) -> VerifiableFunction {
    let return_ty = locals
        .iter()
        .find(|local| local.index == 0)
        .expect("synthetic function must declare return local _0")
        .ty
        .clone();
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("synthetic::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count,
            return_ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn formula_contains(formula: &Formula, pred: &impl Fn(&Formula) -> bool) -> bool {
    pred(formula) || formula.children().into_iter().any(|child| formula_contains(child, pred))
}

/// The violation core must test the mathematical result against the i8 maximum
/// (`Gt(_, 127)`), and the i64 maximum must appear NOWHERE in the formula.
/// (`Int(127)` alone would be too weak a pin: the operand range constraints
/// also mention type bounds. `Gt(.., Int(127))` is the out-of-range core
/// itself, and it is what makes the violation SAT — refutable — for 100+100.)
fn assert_overflow_core_at_i8(vc_formula: &Formula, label: &str) {
    assert!(
        formula_contains(vc_formula, &|f| {
            matches!(f, Formula::Gt(_, rhs) if matches!(rhs.as_ref(), Formula::Int(127)))
        }),
        "{label}: the overflow violation must be checked at the VALIDATED i8 \
         destination width (`Gt(result, 127)`), got {vc_formula:?}"
    );
    assert!(
        !formula_contains(vc_formula, &|f| {
            matches!(f, Formula::Int(n) if *n == i128::from(i64::MAX) || *n == i128::from(i64::MIN))
        }),
        "{label}: the fabricated i64 bound must not appear anywhere in the \
         violation — that is the exact false-PROVE this test pins \
         (`200 outside i64` is UNSAT), got {vc_formula:?}"
    );
}

/// Plain `BinaryOp` arm: `_0: i8 = Add(const 100, const 100)` — admitted (each
/// literal fits i8), overflows at runtime. The row must be built at width 8.
#[test]
fn plain_const_const_add_overflow_checked_at_destination_width() {
    let func = make_func(
        "i8_const_add_plain",
        vec![LocalDecl { index: 0, ty: Ty::i8(), name: None }],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Add,
                    Operand::Constant(ConstValue::Int(100)),
                    Operand::Constant(ConstValue::Int(100)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        0,
    );

    let vcs = crate::generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::UnsupportedMir { .. })),
        "the i8 const-add body is admitted MIR and must not fail closed: {vcs:#?}"
    );
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .unwrap_or_else(|| panic!("plain i8 const add must carry an overflow row: {vcs:#?}"));
    // The recorded operand types are the validated operation type, not the
    // fabricated i64 the widthless constants would infer to.
    match &vc.kind {
        VcKind::ArithmeticOverflow { operand_tys: (lhs_ty, rhs_ty), .. } => {
            assert_eq!(lhs_ty, &Ty::i8(), "lhs type must be the validated i8 destination type");
            assert_eq!(rhs_ty, &Ty::i8(), "rhs type must be the validated i8 destination type");
        }
        other => panic!("expected ArithmeticOverflow, got {other:?}"),
    }
    assert_overflow_core_at_i8(&vc.formula, "plain const+const i8 add");
}

/// Checked-assert lane: `CheckedBinaryOp(Add, 100, 100)` into an `(i8, bool)`
/// carrier, guarded by the canonical `.1`-flag assert. The checked op's
/// destination payload type is established at admission and must drive the
/// overflow bound.
#[test]
fn checked_assert_const_const_add_overflow_checked_at_payload_width() {
    let func = make_func(
        "i8_const_add_checked",
        vec![
            LocalDecl { index: 0, ty: Ty::i8(), name: None },
            LocalDecl { index: 1, ty: Ty::Tuple(vec![Ty::i8(), Ty::Bool]), name: None },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Constant(ConstValue::Int(100)),
                        Operand::Constant(ConstValue::Int(100)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert {
                    unwind: UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::field(1, 1)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Add),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        0,
    );

    let vcs = crate::generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::UnsupportedMir { .. })),
        "the checked i8 const-add body is admitted MIR and must not fail closed: {vcs:#?}"
    );
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .unwrap_or_else(|| panic!("checked i8 const add must carry an overflow row: {vcs:#?}"));
    assert_overflow_core_at_i8(&vc.formula, "checked const+const i8 add");
}
