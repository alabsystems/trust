// trust_vcgen/tests/synthetic_mir.rs: Synthetic MIR fixtures for error detection
//
// Tests that exercise each VcKind directly by constructing MIR nodes and
// feeding them through generate_vcs(). No rustc parsing involved — every
// VerifiableFunction is built from scratch.
//
// Part of #586.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;
use trust_vcgen::{generate_vcs, generate_vcs_with_discharge};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Build a minimal VerifiableFunction from locals, blocks, and arg_count.
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
        body: VerifiableBody { locals, blocks, arg_count, return_ty },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Assert that exactly one VC is produced and it matches the expected kind
/// via a predicate.
fn assert_single_vc(vcs: &[VerificationCondition], pred: impl Fn(&VcKind) -> bool, label: &str) {
    let matching: Vec<_> = vcs.iter().filter(|vc| pred(&vc.kind)).collect();
    assert!(
        !matching.is_empty(),
        "{label}: expected at least one matching VC, got 0 out of {} total VCs: {:#?}",
        vcs.len(),
        vcs.iter().map(|v| v.kind.description()).collect::<Vec<_>>()
    );
}

fn formula_contains(formula: &Formula, pred: &impl Fn(&Formula) -> bool) -> bool {
    pred(formula) || formula.children().into_iter().any(|child| formula_contains(child, pred))
}

/// Strip every `#token` version suffix from a formula's variable names. The S2c
/// flip versions place reads (`casted` -> `casted#s0_0`); these structural
/// assertions test the modeled equality, not the versioning encoding.
fn strip_versions(f: &Formula) -> Formula {
    f.clone().map(&mut |node| match node {
        Formula::Var(name, sort) if name.contains('#') => {
            Formula::Var(name.split('#').next().unwrap_or(&name).to_string(), sort)
        }
        other => other,
    })
}

fn assert_no_unsupported_mir(vcs: &[VerificationCondition], label: &str) {
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::UnsupportedMir { .. })),
        "{label}: concrete MIR should not produce UnsupportedMir VCs: {:#?}",
        vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
}

// ---------------------------------------------------------------------------
// ArithmeticOverflow: Add
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_arithmetic_overflow_add() {
    // fn overflow_add(a: u32, b: u32) -> u32 { a + b }
    let func = make_func(
        "overflow_add",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::field(3, 1)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Add),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(
        &vcs,
        |k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }),
        "overflow add",
    );
}

// ---------------------------------------------------------------------------
// ArithmeticOverflow: Sub
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_arithmetic_overflow_sub() {
    let func = make_func(
        "overflow_sub",
        vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]), name: None },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Sub,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::field(3, 1)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Sub),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(
        &vcs,
        |k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. }),
        "overflow sub",
    );
}

// ---------------------------------------------------------------------------
// ArithmeticOverflow: Mul
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_arithmetic_overflow_mul() {
    let func = make_func(
        "overflow_mul",
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: Ty::u64(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u64(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]), name: None },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Mul,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::field(3, 1)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Mul),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(
        &vcs,
        |k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }),
        "overflow mul",
    );
}

// ---------------------------------------------------------------------------
// DivisionByZero
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_division_by_zero() {
    // fn div(a: u32, b: u32) -> u32 { a / b }
    let func = make_func(
        "div_zero",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::u32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Div,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::DivisionByZero), "division by zero");
}

#[test]
fn test_symbolic_divisor_formula_preserved_in_division_vc() {
    let symbolic_divisor =
        Formula::var_owned("__trust_lifted_symbolic_divisor".to_string(), Sort::BitVec(64));
    let func = make_func(
        "symbolic_divisor_preserved",
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: Ty::u64(), name: Some("x0".into()) },
            LocalDecl { index: 2, ty: Ty::u64(), name: Some("result".into()) },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Div,
                    Operand::Copy(Place::local(1)),
                    Operand::Symbolic(symbolic_divisor.clone()),
                ),
                span: SourceSpan::binary_address(0x4000),
            }],
            terminator: Terminator::Return,
        }],
        1,
    );

    let vcs = generate_vcs(&func);
    let div_vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::DivisionByZero))
        .expect("symbolic divisor should emit a DivisionByZero VC");
    let expected_formula =
        Formula::Eq(Box::new(symbolic_divisor), Box::new(Formula::BitVec { value: 0, width: 64 }));

    assert_eq!(
        div_vc.formula, expected_formula,
        "canonical TrustIr Operand::Symbolic must remain the exact VC formula, not an unknown fallback"
    );
    assert!(
        !formula_contains(&div_vc.formula, &|formula| matches!(
            formula,
            Formula::Var(name, _) if name.contains("unknown") || name.contains("undef")
        )),
        "symbolic formula was lowered to an unknown/undef fallback: {:?}",
        div_vc.formula
    );
}

// ---------------------------------------------------------------------------
// RemainderByZero
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_remainder_by_zero() {
    // fn rem(a: u32, b: u32) -> u32 { a % b }
    let func = make_func(
        "rem_zero",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::u32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Rem,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::RemainderByZero), "remainder by zero");
}

// ---------------------------------------------------------------------------
// ShiftOverflow: Shl
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_shift_overflow_shl() {
    // fn shl(x: u32, amt: u32) -> u32 { x << amt }
    let func = make_func(
        "shift_shl",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("amt".into()) },
            LocalDecl { index: 3, ty: Ty::u32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Shl,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(
        &vcs,
        |k| matches!(k, VcKind::ShiftOverflow { op: BinOp::Shl, .. }),
        "shift overflow shl",
    );
}

// ---------------------------------------------------------------------------
// ShiftOverflow: Shr
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_shift_overflow_shr() {
    let func = make_func(
        "shift_shr",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("amt".into()) },
            LocalDecl { index: 3, ty: Ty::u32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Shr,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(
        &vcs,
        |k| matches!(k, VcKind::ShiftOverflow { op: BinOp::Shr, .. }),
        "shift overflow shr",
    );
}

// ---------------------------------------------------------------------------
// Narrowing int->int `as` cast is DEFINED, not "cast overflow"
// (drop-in, owner decision 2026-07-06): a truncating / reinterpreting integer
// `as` cast is defined behavior in Rust (wraps, never UB), so Trust does NOT
// restrict the programmer with a CastOverflow safety obligation. Instead it
// TYPE-TRACKS the result to the target-type range. This test pins the new policy
// (previously it asserted a CastOverflow VC fired — the drop-in-breaking behavior).
// ---------------------------------------------------------------------------

#[test]
fn test_narrowing_cast_is_defined_no_overflow_vc() {
    // fn narrow(x: i32) -> u8 { x as u8 }
    let func = make_func(
        "cast_narrow",
        vec![
            LocalDecl { index: 0, ty: Ty::u8(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::u8(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u8()),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        1,
    );

    let vcs = generate_vcs(&func);
    // A plain int->int `as` cast is defined, so NO CastOverflow (or any other
    // fabricated safety obligation) is emitted — `x as u8` compiles.
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::CastOverflow { .. })),
        "narrowing int->int `as` is defined behavior and must NOT emit a CastOverflow \
         obligation: {vcs:#?}"
    );
    assert_no_unsupported_mir(&vcs, "narrowing int->int cast");
}

#[test]
fn test_stage2_bool_to_usize_cast_feeds_downstream_vc() {
    let func = make_func(
        "stage2_bool_to_usize_cast",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) },
            LocalDecl { index: 2, ty: Ty::usize(), name: Some("flag_as_usize".into()) },
            LocalDecl { index: 3, ty: Ty::usize(), name: Some("quot".into()) },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::usize()),
                    span: SourceSpan::default(),
                },
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Constant(ConstValue::Uint(1, 64)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                },
            ],
            terminator: Terminator::Return,
        }],
        1,
    );

    let vcs = generate_vcs(&func);
    assert_no_unsupported_mir(&vcs, "bool-to-usize cast");
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::CastOverflow { .. })),
        "bool-to-int cast is total and should not emit CastOverflow"
    );

    let div_vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::DivisionByZero))
        .expect("using the cast result as a divisor should produce a divzero VC");
    // The bool→usize cast result is modeled as `ite(flag, 1, 0)` and feeds the
    // divisor; the general term-`Ite` elimination pass then LIFTS that `Ite` to
    // formula-level guards, so the div-zero VC carries NO term-`Ite` but STILL
    // models the cast via `flag` and both branch values 1/0. Verdict-identical —
    // the div-by-zero check `flag_as_usize == 0` is preserved, so it is still SAT
    // exactly when `flag` is false (the divisor is 0).
    let dbg = format!("{:?}", div_vc.formula);
    assert!(
        !formula_contains(&div_vc.formula, &|f| matches!(f, Formula::Ite(..))),
        "the general Ite-elimination pass should have lifted the cast Ite: {dbg}"
    );
    assert!(
        dbg.contains("Implies(Var(\"flag\", Bool), Eq(Var(\"flag_as_usize\", Int), Int(1)))")
            && dbg.contains(
                "Implies(Not(Var(\"flag\", Bool)), Eq(Var(\"flag_as_usize\", Int), Int(0)))"
            ),
        "bool-to-int cast must still be modeled as guarded `flag ? 1 : 0`: {dbg}"
    );
}

#[test]
fn test_stage2_thin_pointer_cast_identity_feeds_downstream_assert() {
    let src_ptr_ty = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) };
    let dst_ptr_ty = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) };
    let func = make_func(
        "stage2_thin_pointer_cast_identity",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: src_ptr_ty.clone(), name: Some("src".into()) },
            LocalDecl { index: 2, ty: dst_ptr_ty.clone(), name: Some("casted".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("same_addr".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), dst_ptr_ty),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::local(3)),
                    expected: true,
                    msg: AssertMessage::Custom("thin pointer cast preserves address".into()),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        1,
    );

    let vcs = generate_vcs(&func);
    assert_no_unsupported_mir(&vcs, "thin pointer-to-pointer cast");
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::CastOverflow { .. })),
        "thin pointer-to-pointer identity cast is not an integer CastOverflow obligation"
    );

    let assertion_vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::Assertion { .. }))
        .expect("downstream assertion should produce a VC");
    assert!(
        formula_contains(&strip_versions(&assertion_vc.formula), &|f| {
            matches!(
                f,
                Formula::Eq(lhs, rhs)
                    if lhs.as_ref().var_name() == Some("casted")
                        && rhs.as_ref().var_name() == Some("src")
            )
        }),
        "thin pointer cast should be modeled as casted == src, got {:?}",
        assertion_vc.formula
    );
}

#[test]
fn test_stage2_fn_pointer_identity_cast_feeds_downstream_assert() {
    let fn_ptr_ty = Ty::FnPtr { sig: Box::new(FnSig { params: vec![], ret: Box::new(Ty::i32()) }) };
    let func = make_func(
        "stage2_fn_pointer_identity_cast",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: fn_ptr_ty.clone(), name: Some("safe_fp".into()) },
            LocalDecl { index: 2, ty: fn_ptr_ty.clone(), name: Some("unsafe_fp".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("same_fp".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), fn_ptr_ty),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::local(3)),
                    expected: true,
                    msg: AssertMessage::Custom("fn pointer cast preserves identity".into()),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        1,
    );

    let vcs = generate_vcs(&func);
    assert_no_unsupported_mir(&vcs, "fn pointer-to-fn pointer identity cast");

    let assertion_vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::Assertion { .. }))
        .expect("downstream assertion should produce a VC");
    assert!(
        formula_contains(&strip_versions(&assertion_vc.formula), &|f| {
            matches!(
                f,
                Formula::Eq(lhs, rhs)
                    if lhs.as_ref().var_name() == Some("unsafe_fp")
                        && rhs.as_ref().var_name() == Some("safe_fp")
            )
        }),
        "fn pointer identity cast should be modeled as unsafe_fp == safe_fp, got {:?}",
        assertion_vc.formula
    );
}

#[test]
fn test_stage2_callable_reification_cast_uses_opaque_token() {
    let fn_ptr_ty = Ty::FnPtr { sig: Box::new(FnSig { params: vec![], ret: Box::new(Ty::i32()) }) };
    let func = make_func(
        "stage2_callable_reification_cast",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: fn_ptr_ty.clone(), name: Some("fp".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("same_fp".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Cast(Operand::Constant(ConstValue::Unit), fn_ptr_ty),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::local(2)),
                    expected: true,
                    msg: AssertMessage::Custom("reified fn pointer is reflexive".into()),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        0,
    );

    let vcs = generate_vcs(&func);
    assert_no_unsupported_mir(&vcs, "callable reification cast");

    {
        let assertion_vc = vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::Assertion { .. }))
            .expect("downstream assertion should produce a VC");
        assert!(
            formula_contains(&assertion_vc.formula, &|f| {
                f.var_name() == Some("__trust_callable_reify_fp")
            }),
            "callable reification should use an opaque token, got {:?}",
            assertion_vc.formula
        );
        assert!(
            !formula_contains(&assertion_vc.formula, &|f| {
                matches!(
                    f,
                    Formula::Eq(lhs, rhs)
                        if lhs.as_ref().var_name() == Some("fp")
                            && matches!(rhs.as_ref(), Formula::Int(0))
                )
            }),
            "callable reification must not collapse to fp == 0, got {:?}",
            assertion_vc.formula
        );
    }
}

#[test]
fn test_stage2_fn_def_reification_equal_signature_uses_opaque_token() {
    let sig = Box::new(FnSig { params: vec![Ty::i32()], ret: Box::new(Ty::i32()) });
    let fn_def_ty = Ty::FnDef { name: "synthetic::helper_i32".into(), sig: sig.clone() };
    let fn_ptr_ty = Ty::FnPtr { sig };
    let func = make_func(
        "stage2_fn_def_reification_equal_signature",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: fn_def_ty, name: Some("helper".into()) },
            LocalDecl { index: 2, ty: fn_ptr_ty.clone(), name: Some("fp".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("same_fp".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), fn_ptr_ty),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::local(3)),
                    expected: true,
                    msg: AssertMessage::Custom("reified FnDef pointer is reflexive".into()),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        1,
    );

    let vcs = generate_vcs(&func);
    assert_no_unsupported_mir(&vcs, "equal-signature FnDef -> FnPtr reification");

    {
        let assertion_vc = vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::Assertion { .. }))
            .expect("downstream assertion should produce a VC");
        assert!(
            formula_contains(&assertion_vc.formula, &|f| {
                f.var_name() == Some("__trust_callable_reify_fp")
            }),
            "FnDef reification should use an opaque token, got {:?}",
            assertion_vc.formula
        );
    }
}

#[test]
fn test_stage2_fn_pointer_mismatched_signature_cast_fails_closed() {
    let src_fn_ptr_ty =
        Ty::FnPtr { sig: Box::new(FnSig { params: vec![Ty::i32()], ret: Box::new(Ty::i32()) }) };
    let dst_fn_ptr_ty =
        Ty::FnPtr { sig: Box::new(FnSig { params: vec![Ty::u64()], ret: Box::new(Ty::u64()) }) };
    let func = make_func(
        "stage2_fn_pointer_mismatched_signature_cast",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: src_fn_ptr_ty, name: Some("src_fp".into()) },
            LocalDecl { index: 2, ty: dst_fn_ptr_ty.clone(), name: Some("dst_fp".into()) },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), dst_fn_ptr_ty),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        1,
    );

    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| {
            matches!(
                &vc.kind,
                VcKind::UnsupportedMir { kind, detail }
                    if kind == "Rvalue::Cast" && detail.contains("signature")
            )
        }),
        "mismatched fn pointer signatures must fail closed: {vcs:#?}"
    );
}

#[test]
fn test_stage2_fn_def_mismatched_signature_reification_fails_closed() {
    let fn_def_ty = Ty::FnDef {
        name: "synthetic::helper_i32".into(),
        sig: Box::new(FnSig { params: vec![Ty::i32()], ret: Box::new(Ty::i32()) }),
    };
    let fn_ptr_ty =
        Ty::FnPtr { sig: Box::new(FnSig { params: vec![Ty::u64()], ret: Box::new(Ty::u64()) }) };
    let func = make_func(
        "stage2_fn_def_mismatched_signature_reification",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: fn_def_ty, name: Some("helper".into()) },
            LocalDecl { index: 2, ty: fn_ptr_ty.clone(), name: Some("fp".into()) },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), fn_ptr_ty),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        0,
    );

    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| {
            matches!(
                &vc.kind,
                VcKind::UnsupportedMir { kind, detail }
                    if kind == "Rvalue::Cast" && detail.contains("signature")
            )
        }),
        "mismatched FnDef -> FnPtr signatures must fail closed: {vcs:#?}"
    );
}

#[test]
fn test_stage2_unsupported_pointer_to_int_cast_does_not_inject_identity_definition() {
    let src_ptr_ty = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) };
    let func = make_func(
        "stage2_pointer_to_int_cast",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: src_ptr_ty, name: Some("src".into()) },
            LocalDecl { index: 2, ty: Ty::usize(), name: Some("addr".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("addr_is_zero".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::usize()),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Uint(0, 64)),
                        ),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::local(3)),
                    expected: false,
                    msg: AssertMessage::Custom("ptr-to-int cast has no identity semantics".into()),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        1,
    );

    let vcs = generate_vcs(&func);
    // ptr-to-int casts are now ACCEPTED (no UnsupportedMir cast VC). Exposing a pointer's
    // address yields an arbitrary integer; we do not refuse the cast.
    assert!(
        !vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. } if kind == "Rvalue::Cast"
        )),
        "ptr-to-int casts are accepted, not refused as UnsupportedMir: {vcs:#?}"
    );
    // The soundness guard that gives this test its name still holds: accepting the cast must
    // leave the dest UNCONSTRAINED -- it must NOT inject an identity `addr == src` definition
    // (that would let `addr` be reasoned about as the pointer's provenance and could falsely
    // discharge the derived null check).
    assert!(
        !vcs.iter().any(|vc| {
            formula_contains(&vc.formula, &|f| {
                matches!(
                    f,
                    Formula::Eq(lhs, rhs)
                        if lhs.as_ref().var_name() == Some("addr")
                            && rhs.as_ref().var_name() == Some("src")
                )
            })
        }),
        "ptr-to-int casts must not inject addr == src: {vcs:#?}"
    );
}

#[test]
fn test_stage2_fat_pointer_cast_fails_closed() {
    let src_ptr_ty = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) };
    let dst_fat_ptr_ty =
        Ty::RawPtr { mutable: false, pointee: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) };
    let func = make_func(
        "stage2_fat_pointer_cast",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: src_ptr_ty, name: Some("src".into()) },
            LocalDecl { index: 2, ty: dst_fat_ptr_ty.clone(), name: Some("fat".into()) },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), dst_fat_ptr_ty),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        1,
    );

    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "Rvalue::Cast"
                    && detail.contains("fat-pointer metadata/provenance")
        )),
        "fat pointer metadata-changing casts must fail closed: {vcs:#?}"
    );
}

/// Build `fn f(p: <operand_ty>) { let _2 = PtrMetadata(Copy(_1)); }`.
fn ptr_metadata_extraction_func(operand_ty: Ty) -> VerifiableFunction {
    make_func(
        "stage2_ptr_metadata_extraction",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: operand_ty, name: Some("data".into()) },
            LocalDecl { index: 2, ty: Ty::usize(), name: Some("len".into()) },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(1))),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        1,
    )
}

fn has_ptr_metadata_unsupported(vcs: &[VerificationCondition]) -> bool {
    vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "Rvalue::UnaryOp(PtrMetadata)"
                    && detail.contains("fat-pointer metadata/provenance")
        )
    })
}

// `PtrMetadata` over a SLICE fat pointer is just its length, modeled
// deterministically by `slice_len_formula` (and shared by the `s.len()` guard and
// the `s[i]` bounds check), so it must NOT emit a spurious UnsupportedMir
// obligation — that wedged the ubiquitous `if i < s.len() { s[i] }` idiom. This
// holds for BOTH a safe `&[T]` AND a raw `*const/mut [T]`: a `*const [T]`'s
// metadata word IS the element count, semantically identical to `&[T]` (the
// `<[T]>::len()` lowering on a `&mut [T]` reads exactly this raw fat pointer). A
// free length var is sound — with no guard it can only fail-close; with a
// same-pointer guard it discharges a genuine bounds fact. Genuinely metadata-less
// pointers (a THIN `*const u32`, whose metadata is `()`) carry no length, so they
// must STILL fail closed.
#[test]
fn test_stage2_ptr_metadata_extraction_precise_modeling() {
    // Safe `&[u32]`: length is modeled, no fail-closed obligation.
    let slice_ref = ptr_metadata_extraction_func(Ty::Ref {
        mutable: false,
        inner: Box::new(Ty::Slice { elem: Box::new(Ty::u32()) }),
    });
    let slice_vcs = generate_vcs(&slice_ref);
    assert!(
        !has_ptr_metadata_unsupported(&slice_vcs),
        "PtrMetadata over a safe &[u32] is modeled by slice_len_formula and must \
         not emit an UnsupportedMir obligation: {slice_vcs:#?}"
    );

    // Raw slice fat pointer `*const [u32]`: the metadata word IS the slice length
    // (the `<[T]>::len()` lowering reads exactly this on a `&mut [T]`), so it is
    // modeled too — no fail-closed obligation. Soundness: the length var is free
    // unless an `AddressOf`/guard ties it, so it never false-proves.
    let raw_fat_ptr = ptr_metadata_extraction_func(Ty::RawPtr {
        mutable: false,
        pointee: Box::new(Ty::Slice { elem: Box::new(Ty::u32()) }),
    });
    let raw_vcs = generate_vcs(&raw_fat_ptr);
    assert!(
        !has_ptr_metadata_unsupported(&raw_vcs),
        "PtrMetadata over a raw *const [u32] is the slice length (same as &[u32]) \
         and must not emit an UnsupportedMir obligation: {raw_vcs:#?}"
    );

    // THIN raw pointer `*const u32`: metadata is `()`, no length semantics — must
    // STILL fail closed (the slice-length modeling is scoped to slice pointees).
    let thin_ptr =
        ptr_metadata_extraction_func(Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) });
    let thin_vcs = generate_vcs(&thin_ptr);
    assert!(
        has_ptr_metadata_unsupported(&thin_vcs),
        "PtrMetadata over a thin *const u32 has no length metadata and must stay \
         explicit (fail closed): {thin_vcs:#?}"
    );
}

#[test]
fn test_stage2_concrete_integer_bool_constants_in_switch_and_call_are_modeled() {
    let span = SourceSpan::default();
    let func = make_func(
        "stage2_concrete_constants",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: Ty::Unit, name: Some("dest".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Constant(ConstValue::Bool(true)),
                    targets: vec![(1, BlockId(1))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: span.clone(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Call { unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "synthetic::callee".to_string(),
                    args: vec![
                        Operand::Constant(ConstValue::Uint(7, 64)),
                        Operand::Constant(ConstValue::Bool(false)),
                    ],
                    dest: Place::local(1),
                    target: Some(BlockId(2)),
                    span: span.clone(),
                    atomic: None,
                },
            },
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
        ],
        0,
    );

    let vcs = generate_vcs(&func);
    assert_no_unsupported_mir(&vcs, "concrete integer/bool constants");
}

#[test]
fn test_stage2_unavailable_integer_bool_constants_fail_closed() {
    // Distinct spans for the switch discriminant and the call: in real MIR these
    // are different source locations, and the generation-time unsupported dedup
    // keys on (kind, location), so a shared span would (correctly, but
    // unrealistically) coalesce the two distinct fail-closed obligations.
    let span_switch = SourceSpan {
        file: "synthetic.rs".to_string(),
        line_start: 10,
        col_start: 5,
        line_end: 10,
        col_end: 20,
    };
    let span_call = SourceSpan {
        file: "synthetic.rs".to_string(),
        line_start: 20,
        col_start: 5,
        line_end: 20,
        col_end: 30,
    };
    let func = make_func(
        "stage2_unavailable_constants",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: Ty::Unit, name: Some("dest".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Unsupported {
                        kind: "Const".to_string(),
                        detail: "unsupported constant of MIR type bool; refusing to prove with a guessed value"
                            .to_string(),
                    },
                    targets: vec![(1, BlockId(1))],
                    otherwise: BlockId(2),
                    span: span_switch.clone(),
                exhaustive_enum_unreachable: false,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Call { unwind: trust_types::UnwindEdge::Unreachable,  is_unsafe_sig: false, is_foreign: false,
                    func: "synthetic::callee".to_string(),
                    args: vec![
                        Operand::Constant(ConstValue::Uint(0, 64)),
                        Operand::Constant(ConstValue::Bool(true)),
                        Operand::Unsupported {
                            kind: "Const".to_string(),
                            detail: "unsupported constant of MIR type usize; refusing to prove with a guessed value"
                                .to_string(),
                        },
                    ],
                    dest: Place::local(1),
                    target: Some(BlockId(2)),
                    span: span_call.clone(),
                    atomic: None,
                },
            },
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
        ],
        0,
    );

    let vcs = generate_vcs(&func);
    let unsupported: Vec<_> = vcs
        .iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::UnsupportedMir { kind, detail } => {
                Some((kind.as_str(), detail.as_str(), &vc.formula))
            }
            _ => None,
        })
        .collect();
    assert!(
        unsupported.iter().any(|(kind, detail, formula)| {
            *kind == "Const"
                && detail.contains("bb0 switch discriminant")
                && detail.contains("MIR type bool")
                && **formula == Formula::Bool(true)
        }),
        "unavailable bool switch constant should fail closed: {unsupported:#?}"
    );
    assert!(
        unsupported.iter().any(|(kind, detail, formula)| {
            *kind == "Const"
                && detail.contains("bb1 call args[2]")
                && detail.contains("MIR type usize")
                && **formula == Formula::Bool(true)
        }),
        "unavailable usize call constant should fail closed: {unsupported:#?}"
    );
}

// ---------------------------------------------------------------------------
// NegationOverflow (signed)
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_negation_overflow() {
    // fn negate(x: i32) -> i32 { -x }
    let func = make_func(
        "negation_overflow",
        vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        1,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::NegationOverflow { .. }), "negation overflow");
}

// ---------------------------------------------------------------------------
// IndexOutOfBounds (via Assert terminator with BoundsCheck)
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_index_out_of_bounds() {
    // fn index(arr: &[u32], i: usize) -> u32 { arr[i] }
    // MIR: Assert(cond, true, BoundsCheck) to check i < len
    let func = make_func(
        "index_oob",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::usize(), name: Some("i".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("in_bounds".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::local(2)),
                    expected: true,
                    msg: AssertMessage::BoundsCheck,
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::IndexOutOfBounds), "index out of bounds");
}

// ---------------------------------------------------------------------------
// Unmodeled safety asserts must FAIL CLOSED (not be silently dropped).
//
// rustc inserts NullPointerDereference / MisalignedPointerDereference /
// InvalidEnumConstruction Assert terminators as real runtime UB checks. vcgen
// does not model them precisely, but dropping the obligation makes the function
// vacuously "proved" while the check would still fire at runtime -- a
// false-PROVE. The unhandled-assert arm must instead emit an UnsupportedMir
// obligation, which the compiler preclassifies to Unknown (never proved).
//
// ResumedAfterReturn/Panic/Drop are deliberately NOT in this family: they are
// coroutine executor-protocol preconditions, modeled as Assume by the TrustIr
// bridge. Dedicated tests below pin that narrow carveout while these tests pin
// the fail-closed remainder.
// ---------------------------------------------------------------------------

fn assert_fails_closed_for_assert_msg(name: &str, msg: AssertMessage) {
    let func = make_func(
        name,
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::Bool, name: Some("ok".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::local(1)),
                    expected: true,
                    msg,
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        1,
    );

    let vcs = generate_vcs(&func);
    // Must NOT be silently dropped (zero obligations => vacuous proved).
    assert!(!vcs.is_empty(), "{name}: unmodeled safety assert was silently dropped (false-PROVE)");
    assert!(
        vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. } if kind.contains("UnmodeledSafetyAssert")
        )),
        "{name}: unmodeled safety assert must fail closed to UnsupportedMir, got: {vcs:#?}"
    );
}

#[test]
fn test_synthetic_null_pointer_deref_assert_fails_closed() {
    assert_fails_closed_for_assert_msg("null_ptr_deref", AssertMessage::NullPointerDereference);
}

#[test]
fn test_synthetic_misaligned_pointer_deref_assert_fails_closed() {
    assert_fails_closed_for_assert_msg(
        "misaligned_ptr_deref",
        AssertMessage::MisalignedPointerDereference,
    );
}

#[test]
fn test_synthetic_invalid_enum_construction_assert_fails_closed() {
    assert_fails_closed_for_assert_msg(
        "invalid_enum_construction",
        AssertMessage::InvalidEnumConstruction,
    );
}

fn assert_coroutine_protocol_assert_is_not_a_data_safety_vc(name: &str, msg: AssertMessage) {
    let func = make_func(
        name,
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: Ty::Bool, name: Some("protocol_state_valid".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::local(1)),
                    expected: true,
                    msg,
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        1,
    );

    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. } if kind.contains("UnmodeledSafetyAssert(ResumedAfter")
        )),
        "{name}: coroutine protocol assert must not become a data-safety Unknown: {vcs:#?}"
    );
}

#[test]
fn test_coroutine_resume_protocol_asserts_are_not_data_safety_vcs() {
    for (name, msg) in [
        ("resumed_after_return", AssertMessage::ResumedAfterReturn),
        ("resumed_after_panic", AssertMessage::ResumedAfterPanic),
        ("resumed_after_drop", AssertMessage::ResumedAfterDrop),
    ] {
        assert_coroutine_protocol_assert_is_not_a_data_safety_vc(name, msg);
    }
}

// ---------------------------------------------------------------------------
// Malformed recognized safety asserts must also FAIL CLOSED.
//
// The recognized Overflow, OverflowNeg, and BoundsCheck builders return
// Option<VC> because they need adjacent MIR evidence. If that evidence is
// malformed, dropping the VC is a false proof. The assert was recognized as a
// safety check, so builder failure must become an explicit Unknown obligation.
// ---------------------------------------------------------------------------

fn assert_recognized_assert_gap_unknown(func: VerifiableFunction, assert_family: &str) {
    let vcs = generate_vcs(&func);
    assert_eq!(
        vcs.len(),
        1,
        "{assert_family}: malformed recognized assert must add exactly one obligation: {vcs:#?}"
    );

    let gap = vcs
        .iter()
        .find(|vc| {
            matches!(
                &vc.kind,
                VcKind::UnsupportedMir { kind, detail }
                    if kind.contains("RecognizedSafetyAssertProofGap")
                        && kind.contains(assert_family)
                        && detail.contains("builder returned no VC")
            )
        })
        .expect("recognized assert builder failure must emit an UnsupportedMir proof gap");
    assert_eq!(gap.formula, Formula::Bool(true));

    let (solver_vcs, preclassified) = generate_vcs_with_discharge(&func);
    assert!(
        solver_vcs.is_empty(),
        "{assert_family}: proof-gap VC must be preclassified, not solver-dispatched: {solver_vcs:#?}"
    );
    assert_eq!(
        preclassified.len(),
        1,
        "{assert_family}: proof-gap VC must increment Unknown obligations: {preclassified:#?}"
    );
    assert!(
        preclassified.iter().any(|(vc, result)| {
            matches!(
                &vc.kind,
                VcKind::UnsupportedMir { kind, .. }
                    if kind.contains("RecognizedSafetyAssertProofGap")
                        && kind.contains(assert_family)
            ) && matches!(
                result,
                VerificationResult::Unknown { reason, .. }
                    if reason.contains("unsupported MIR") && reason.contains(assert_family)
            )
        }),
        "{assert_family}: proof gap must be Unknown, not disappeared: {preclassified:#?}"
    );
}

#[test]
fn test_malformed_recognized_overflow_assert_is_unknown() {
    let func = make_func(
        "malformed_overflow_assert",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::Bool, name: Some("overflowed".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::local(1)),
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

    assert_recognized_assert_gap_unknown(func, "Overflow(Add)");
}

#[test]
fn test_malformed_recognized_overflow_neg_assert_is_unknown() {
    let func = make_func(
        "malformed_overflow_neg_assert",
        vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::Bool, name: Some("overflowed".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::local(1)),
                    expected: false,
                    msg: AssertMessage::OverflowNeg,
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        0,
    );

    assert_recognized_assert_gap_unknown(func, "OverflowNeg");
}

#[test]
fn test_malformed_recognized_bounds_check_assert_fails_at_structural_admission() {
    let func = make_func(
        "malformed_bounds_check_assert",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::Bool, name: Some("in_bounds".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::local(1)),
                    expected: true,
                    msg: AssertMessage::BoundsCheck,
                    target: BlockId(99),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        0,
    );

    // Dense BlockId validation is now stronger than the old per-builder
    // fallback: an invalid assert target never reaches the BoundsCheck
    // builder. It must still surface as exactly one fail-closed Unknown, now
    // classified at the structural TrustIr boundary.
    let vcs = generate_vcs(&func);
    assert_eq!(vcs.len(), 1, "malformed target must produce one proof gap: {vcs:#?}");
    let VcKind::UnsupportedMir { kind, detail } = &vcs[0].kind else {
        panic!("malformed target must become UnsupportedMir: {vcs:#?}");
    };
    assert_eq!(kind, "MalformedTrustIr");
    assert!(
        detail.contains("bb99"),
        "structural diagnostic must identify the invalid target: {detail}"
    );
    assert_eq!(vcs[0].formula, Formula::Bool(true));

    let (solver_vcs, preclassified) = generate_vcs_with_discharge(&func);
    assert!(solver_vcs.is_empty(), "malformed TrustIr must not reach a solver");
    assert_eq!(preclassified.len(), 1);
    assert!(matches!(preclassified[0].1, VerificationResult::Unknown { .. }));
}

#[test]
fn test_synthetic_direct_projection_index_out_of_bounds() {
    let func = make_func(
        "direct_projection_index_oob",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl {
                index: 1,
                ty: Ty::Array { elem: Box::new(Ty::u32()), len: 10 },
                name: Some("arr".into()),
            },
            LocalDecl { index: 2, ty: Ty::usize(), name: Some("idx".into()) },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Copy(Place {
                    local: 1,
                    projections: vec![Projection::Index(2)],
                })),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    let bounds_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds)).collect();
    assert_eq!(
        bounds_vcs.len(),
        1,
        "direct projection load should produce exactly one IndexOutOfBounds VC"
    );
    assert!(
        formula_contains(&bounds_vcs[0].formula, &|f| {
            matches!(
                f,
                Formula::Ge(lhs, rhs)
                    if lhs.var_name() == Some("idx") && matches!(rhs.as_ref(), Formula::Int(10))
            )
        }),
        "direct projection bounds VC should check idx >= 10, got {:?}",
        bounds_vcs[0].formula
    );
}

// ---------------------------------------------------------------------------
// Assertion (custom message)
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_assertion() {
    // fn check(cond: bool) { assert!(cond, "invariant violated") }
    let func = make_func(
        "custom_assert",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: Ty::Bool, name: Some("cond".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::local(1)),
                    expected: true,
                    msg: AssertMessage::Custom("invariant violated".to_string()),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        1,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(
        &vcs,
        |k| matches!(k, VcKind::Assertion { message } if message == "invariant violated"),
        "custom assertion",
    );
}

#[test]
fn test_synthetic_native_switchint_assertion_panic_fmt() {
    let span = SourceSpan::default();
    let func = make_func(
        "native_assertion",
        vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("ok".into()) },
            LocalDecl { index: 3, ty: Ty::Never, name: None },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Ge,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Int(0)),
                    ),
                    span: span.clone(),
                }],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(2)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: span.clone(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                    span: span.clone(),
                }],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: Terminator::Call { unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "std::rt::panic_fmt".to_string(),
                    args: vec![],
                    dest: Place::local(3),
                    target: None,
                    span: span.clone(),
                    atomic: None,
                },
            },
        ],
        1,
    );

    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(
            |vc| matches!(&vc.kind, VcKind::Assertion { message } if message.contains("panic_fmt")),
        )
        .expect("panic_fmt assertion path should generate an Assertion VC");

    // The vcgen inlines the `ok` local (defined as `x >= 0`) into the path
    // condition, so the SwitchInt false-branch guard appears as
    // `Not(Ge(Var("x"), 0))` rather than `Not(Var("ok"))`. Accept either form:
    // raw boolean-local reference (no inlining) or the equivalent inlined
    // predicate.
    assert!(
        formula_contains(&vc.formula, &|f| {
            match f {
                Formula::Not(inner) => match inner.as_ref() {
                    Formula::Var(name, _) if name == "ok" => true,
                    Formula::Ge(lhs, rhs) => matches!(
                        (lhs.as_ref(), rhs.as_ref()),
                        (Formula::Var(name, _), Formula::Int(0)) if name == "x"
                    ),
                    _ => false,
                },
                _ => false,
            }
        }),
        "assertion VC should keep the false SwitchInt guard (either Not(ok) or Not(x >= 0)), got {:?}",
        vc.formula
    );
}

// ---------------------------------------------------------------------------
// Float division is DEFINED (Trust §9): `a / b` on f64 never traps — `a / 0.0`
// is ±inf/NaN — so it emits NO division-by-zero obligation (parallel to the
// int→int cast case above). Contrast integer `/` which keeps DivisionByZero.
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_float_division_emits_no_obligation() {
    // fn fdiv(a: f64, b: f64) -> f64 { a / b }
    let func = make_func(
        "float_div_zero",
        vec![
            LocalDecl { index: 0, ty: Ty::Float { width: 64 }, name: None },
            LocalDecl { index: 1, ty: Ty::Float { width: 64 }, name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::Float { width: 64 }, name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::Float { width: 64 }, name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Div,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter()
            .any(|vc| matches!(vc.kind, VcKind::FloatDivisionByZero | VcKind::DivisionByZero)),
        "float division is defined — no division-by-zero obligation; got {:?}",
        vcs.iter().map(|vc| vc.kind.description()).collect::<Vec<_>>()
    );
}

// ---------------------------------------------------------------------------
// InvalidDiscriminant (read discriminant on non-enum type)
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_invalid_discriminant() {
    // Reading discriminant of a u32 (not an enum).
    let func = make_func(
        "invalid_discrim",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Discriminant(Place::local(1)),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        1,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(
        &vcs,
        |k| matches!(k, VcKind::InvalidDiscriminant { .. }),
        "invalid discriminant",
    );
}

// ---------------------------------------------------------------------------
// AggregateArrayLengthMismatch
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_aggregate_array_length_mismatch() {
    // Construct [u32; 3] with only 2 operands.
    let func = make_func(
        "array_len_mismatch",
        vec![
            LocalDecl { index: 0, ty: Ty::Array { elem: Box::new(Ty::u32()), len: 3 }, name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::Array { elem: Box::new(Ty::u32()), len: 3 }, name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::Aggregate(
                    AggregateKind::Array,
                    vec![
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                        // Only 2 operands for a [u32; 3] — mismatch!
                    ],
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(
        &vcs,
        |k| matches!(k, VcKind::AggregateArrayLengthMismatch { expected: 3, actual: 2 }),
        "aggregate array length mismatch",
    );
}

// ---------------------------------------------------------------------------
// Unreachable
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_unreachable() {
    // A function with an Unreachable terminator reachable from entry.
    let func = make_func(
        "has_unreachable",
        vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Unreachable }],
        0,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::Unreachable), "unreachable");
}

#[test]
fn test_synthetic_native_unreachable_panic_fmt_from_str_nonconst_chain() {
    let span = SourceSpan::default();
    let func = make_func(
        "native_unreachable",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("in_range".into()) },
            LocalDecl { index: 3, ty: Ty::Unit, name: Some("args".into()) },
            LocalDecl { index: 4, ty: Ty::Never, name: None },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(1)),
                    targets: vec![(0, BlockId(1))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: span.clone(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Le,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(100, 32)),
                    ),
                    span: span.clone(),
                }],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(2)),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(4),
                    exhaustive_enum_unreachable: false,
                    span: span.clone(),
                },
            },
            BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            BasicBlock {
                id: BlockId(4),
                stmts: vec![],
                terminator: Terminator::Call { unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "std::fmt::Arguments::<'a>::from_str_nonconst".to_string(),
                    args: vec![],
                    dest: Place::local(3),
                    target: Some(BlockId(5)),
                    span: span.clone(),
                    atomic: None,
                },
            },
            BasicBlock {
                id: BlockId(5),
                stmts: vec![],
                terminator: Terminator::Call { unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "std::rt::panic_fmt".to_string(),
                    args: vec![],
                    dest: Place::local(4),
                    target: None,
                    span: span.clone(),
                    atomic: None,
                },
            },
        ],
        1,
    );

    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::Unreachable)),
        "from_str_nonconst -> panic_fmt chain should classify as Unreachable, got {:?}",
        vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::Assertion { .. })),
        "unreachable panic chain should not also emit Assertion, got {:?}",
        vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
}

#[test]
fn test_synthetic_native_numeric_switch_panic_fmt_stays_assertion_without_nonconst_chain() {
    let span = SourceSpan::default();
    let func = make_func(
        "native_assertion_from_fmt",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::Unit, name: Some("args".into()) },
            LocalDecl { index: 3, ty: Ty::Never, name: None },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(1)),
                    targets: vec![(0, BlockId(1))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: span.clone(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: Terminator::Call { unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "std::fmt::Arguments::<'a>::from_str".to_string(),
                    args: vec![],
                    dest: Place::local(2),
                    target: Some(BlockId(3)),
                    span: span.clone(),
                    atomic: None,
                },
            },
            BasicBlock {
                id: BlockId(3),
                stmts: vec![],
                terminator: Terminator::Call { unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "std::rt::panic_fmt".to_string(),
                    args: vec![],
                    dest: Place::local(3),
                    target: None,
                    span: span.clone(),
                    atomic: None,
                },
            },
        ],
        1,
    );

    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(
            |vc| matches!(&vc.kind, VcKind::Assertion { message } if message.contains("panic_fmt"))
        ),
        "numeric-switch panic_fmt without from_str_nonconst should stay Assertion, got {:?}",
        vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::Unreachable)),
        "plain panic_fmt path should not classify as Unreachable, got {:?}",
        vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
}

// ---------------------------------------------------------------------------
// Signed division overflow (INT_MIN / -1)
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_signed_div_overflow() {
    // fn signed_div(a: i32, b: i32) -> i32 { a / b }
    // Should produce DivisionByZero AND ArithmeticOverflow (INT_MIN / -1).
    let func = make_func(
        "signed_div",
        vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::i32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Div,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    // Should have both DivisionByZero and ArithmeticOverflow
    assert_single_vc(&vcs, |k| matches!(k, VcKind::DivisionByZero), "signed div: div by zero");
    assert_single_vc(
        &vcs,
        |k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Div, .. }),
        "signed div: INT_MIN / -1 overflow",
    );
}

#[test]
fn test_synthetic_native_slice_bounds_formula() {
    let span = SourceSpan::default();
    let func = make_func(
        "native_slice_bounds",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl {
                index: 1,
                ty: Ty::Ref {
                    mutable: false,
                    inner: Box::new(Ty::Slice { elem: Box::new(Ty::u32()) }),
                },
                name: Some("data".into()),
            },
            LocalDecl { index: 2, ty: Ty::usize(), name: Some("zero".into()) },
            LocalDecl { index: 3, ty: Ty::usize(), name: Some("len".into()) },
            LocalDecl { index: 4, ty: Ty::Bool, name: Some("in_bounds".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(1))),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(3)),
                        ),
                        span: span.clone(),
                    },
                ],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Move(Place::local(4)),
                    expected: true,
                    msg: AssertMessage::BoundsCheck,
                    target: BlockId(1),
                    span: span.clone(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Deref, Projection::Index(2)],
                    })),
                    span: span.clone(),
                }],
                terminator: Terminator::Return,
            },
        ],
        1,
    );

    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck))
        .expect("native slice bounds check should generate SliceBoundsCheck");

    assert!(
        formula_contains(&strip_versions(&vc.formula), &|f| {
            matches!(
                f,
                Formula::Ge(lhs, rhs)
                    if lhs.var_name() == Some("zero") && rhs.var_name() == Some("len")
            )
        }),
        "slice bounds VC should use the direct zero >= len violation, got {:?}",
        vc.formula
    );
}

#[test]
fn test_synthetic_native_guarded_slice_is_empty_proves_bounds_without_unsafe_vcs() {
    let span = SourceSpan::default();
    let func = make_func(
        "native_guarded_slice_bounds",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl {
                index: 1,
                ty: Ty::Ref {
                    mutable: false,
                    inner: Box::new(Ty::Slice { elem: Box::new(Ty::u32()) }),
                },
                name: Some("data".into()),
            },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("is_empty".into()) },
            LocalDecl { index: 3, ty: Ty::usize(), name: Some("zero".into()) },
            LocalDecl { index: 4, ty: Ty::usize(), name: Some("len".into()) },
            LocalDecl { index: 5, ty: Ty::Bool, name: Some("in_bounds".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call { unwind: trust_types::UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: "core::slice::<impl [u32]>::is_empty".to_string(),
                    args: vec![Operand::Copy(Place::local(1))],
                    dest: Place::local(2),
                    target: Some(BlockId(1)),
                    span: span.clone(),
                    atomic: None,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(2)),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: span.clone(),
                },
            },
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            BasicBlock {
                id: BlockId(3),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(1))),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(3)),
                            Operand::Copy(Place::local(4)),
                        ),
                        span: span.clone(),
                    },
                ],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Move(Place::local(5)),
                    expected: true,
                    msg: AssertMessage::BoundsCheck,
                    target: BlockId(4),
                    span: span.clone(),
                },
            },
            BasicBlock {
                id: BlockId(4),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Deref, Projection::Index(3)],
                    })),
                    span: span.clone(),
                }],
                terminator: Terminator::Return,
            },
        ],
        1,
    );

    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck))
        .expect("guarded slice path should generate SliceBoundsCheck");

    assert!(
        formula_contains(&vc.formula, &|f| {
            matches!(
                f,
                Formula::Gt(lhs, rhs)
                    if lhs.var_name() == Some("data__slice_len")
                        && matches!(rhs.as_ref(), Formula::Int(0))
            )
        }),
        "guarded slice bounds VC should carry !is_empty => len > 0, got {:?}",
        vc.formula
    );
    assert!(
        !vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("[unsafe]")
        )),
        "safe slice access should not emit unsafe assertions, got {:?}",
        vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
}

#[test]
fn test_synthetic_native_index_bounds_formula() {
    let span = SourceSpan::default();
    let func = make_func(
        "native_index_bounds",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl {
                index: 1,
                ty: Ty::Array { elem: Box::new(Ty::u32()), len: 10 },
                name: Some("arr".into()),
            },
            LocalDecl { index: 2, ty: Ty::usize(), name: Some("idx".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("in_bounds".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local(2)),
                        Operand::Constant(ConstValue::Uint(10, 64)),
                    ),
                    span: span.clone(),
                }],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Move(Place::local(3)),
                    expected: true,
                    msg: AssertMessage::BoundsCheck,
                    target: BlockId(1),
                    span: span.clone(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Index(2)],
                    })),
                    span: span.clone(),
                }],
                terminator: Terminator::Return,
            },
        ],
        2,
    );

    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds))
        .expect("native array bounds check should generate IndexOutOfBounds");

    assert!(
        formula_contains(&vc.formula, &|f| {
            matches!(
                f,
                Formula::Ge(lhs, rhs)
                    if lhs.var_name() == Some("idx")
                        && matches!(rhs.as_ref(), Formula::Int(10))
            )
        }),
        "index bounds VC should use the direct idx >= len violation, got {:?}",
        vc.formula
    );
}

#[test]
fn test_synthetic_native_shift_overflow_formula() {
    let span = SourceSpan::default();
    let func = make_func(
        "native_shift_overflow",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("shift".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("shift_ok".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local(2)),
                        Operand::Constant(ConstValue::Uint(32, 32)),
                    ),
                    span: span.clone(),
                }],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Move(Place::local(3)),
                    expected: true,
                    msg: AssertMessage::Overflow(BinOp::Shl),
                    target: BlockId(1),
                    span: span.clone(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Shl,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: span.clone(),
                }],
                terminator: Terminator::Return,
            },
        ],
        2,
    );

    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::ShiftOverflow { op: BinOp::Shl, .. }))
        .expect("native shift overflow assert should generate ShiftOverflow");

    assert!(
        formula_contains(&vc.formula, &|f| {
            matches!(
                f,
                Formula::Ge(lhs, rhs)
                    if lhs.var_name() == Some("shift")
                        && matches!(rhs.as_ref(), Formula::Int(32))
            )
        }),
        "shift overflow VC should use the direct shift >= width violation, got {:?}",
        vc.formula
    );
}

#[test]
fn test_synthetic_checked_shift_assert_generates_shift_overflow() {
    let span = SourceSpan::default();
    let func = make_func(
        "checked_shift_overflow",
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: Ty::u64(), name: Some("value".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("shift".into()) },
            LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]), name: None },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Shl,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: span.clone(),
                }],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::field(3, 1)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Shl),
                    target: BlockId(1),
                    span: span.clone(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(
        &vcs,
        |k| matches!(k, VcKind::ShiftOverflow { op: BinOp::Shl, .. }),
        "checked shift overflow",
    );
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::UnsupportedMir { .. })),
        "checked shift overflow should not fall back to UnsupportedMir: {:?}",
        vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
}

#[test]
fn test_synthetic_native_signed_div_overflow_formula() {
    let span = SourceSpan::default();
    let func = make_func(
        "native_signed_div_overflow",
        vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("y".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("divzero".into()) },
            LocalDecl { index: 4, ty: Ty::Bool, name: Some("is_neg_one".into()) },
            LocalDecl { index: 5, ty: Ty::Bool, name: Some("is_min".into()) },
            LocalDecl { index: 6, ty: Ty::Bool, name: Some("overflow".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Eq,
                        Operand::Copy(Place::local(2)),
                        Operand::Constant(ConstValue::Int(0)),
                    ),
                    span: span.clone(),
                }],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Move(Place::local(3)),
                    expected: false,
                    msg: AssertMessage::DivisionByZero,
                    target: BlockId(1),
                    span: span.clone(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Int(-1)),
                        ),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(-(1i128 << 31))),
                        ),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(6),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::BitAnd,
                            Operand::Move(Place::local(4)),
                            Operand::Move(Place::local(5)),
                        ),
                        span: span.clone(),
                    },
                ],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Move(Place::local(6)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Div),
                    target: BlockId(2),
                    span: span.clone(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: span.clone(),
                }],
                terminator: Terminator::Return,
            },
        ],
        2,
    );

    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Div, .. }))
        .expect("native signed div assert should generate ArithmeticOverflow(Div)");

    assert!(
        formula_contains(&vc.formula, &|f| {
            matches!(
                f,
                Formula::Eq(lhs, rhs)
                    if lhs.var_name() == Some("x")
                        && matches!(rhs.as_ref(), Formula::Int(n) if *n == -(1i128 << 31))
            )
        }) && formula_contains(&vc.formula, &|f| {
            matches!(
                f,
                Formula::Eq(lhs, rhs)
                    if lhs.var_name() == Some("y")
                        && matches!(rhs.as_ref(), Formula::Int(-1))
            )
        }),
        "signed div overflow VC should use the direct INT_MIN / -1 formula, got {:?}",
        vc.formula
    );
}

#[test]
fn test_synthetic_native_signed_rem_overflow_formula() {
    let span = SourceSpan::default();
    let func = make_func(
        "native_signed_rem_overflow",
        vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("y".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: Some("remzero".into()) },
            LocalDecl { index: 4, ty: Ty::Bool, name: Some("is_neg_one".into()) },
            LocalDecl { index: 5, ty: Ty::Bool, name: Some("is_min".into()) },
            LocalDecl { index: 6, ty: Ty::Bool, name: Some("overflow".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Eq,
                        Operand::Copy(Place::local(2)),
                        Operand::Constant(ConstValue::Int(0)),
                    ),
                    span: span.clone(),
                }],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Move(Place::local(3)),
                    expected: false,
                    msg: AssertMessage::RemainderByZero,
                    target: BlockId(1),
                    span: span.clone(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Int(-1)),
                        ),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(-(1i128 << 31))),
                        ),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(6),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::BitAnd,
                            Operand::Move(Place::local(4)),
                            Operand::Move(Place::local(5)),
                        ),
                        span: span.clone(),
                    },
                ],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Move(Place::local(6)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Rem),
                    target: BlockId(2),
                    span: span.clone(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Rem,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: span.clone(),
                }],
                terminator: Terminator::Return,
            },
        ],
        2,
    );

    let vcs = generate_vcs(&func);
    let rem_overflow_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Rem, .. }))
        .collect();
    assert_eq!(
        rem_overflow_vcs.len(),
        1,
        "native signed rem assert should generate exactly one ArithmeticOverflow(Rem): {vcs:#?}"
    );
    let vc = rem_overflow_vcs[0];

    assert!(
        formula_contains(&vc.formula, &|f| {
            matches!(
                f,
                Formula::Eq(lhs, rhs)
                    if lhs.var_name() == Some("x")
                        && matches!(rhs.as_ref(), Formula::Int(n) if *n == -(1i128 << 31))
            )
        }) && formula_contains(&vc.formula, &|f| {
            matches!(
                f,
                Formula::Eq(lhs, rhs)
                    if lhs.var_name() == Some("y")
                        && matches!(rhs.as_ref(), Formula::Int(-1))
            )
        }),
        "signed rem overflow VC should use the direct INT_MIN % -1 formula, got {:?}",
        vc.formula
    );
}

// ---------------------------------------------------------------------------
// No false positives: constant divisor should not produce DivisionByZero
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_no_false_positive_const_divisor() {
    // fn safe_div(a: u32) -> u32 { a / 2 }
    let func = make_func(
        "safe_div",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Div,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Uint(2, 32)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        1,
    );

    let vcs = generate_vcs(&func);
    let div_zero_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).collect();
    assert!(
        div_zero_vcs.is_empty(),
        "constant non-zero divisor should not produce DivisionByZero VC"
    );
}

// ---------------------------------------------------------------------------
// Multiple VcKinds in one function
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_multiple_vcs() {
    // fn multi(a: u32, b: u32) -> u32 {
    //     let sum = a + b;     // overflow VC
    //     let quot = sum / b;  // div-by-zero VC
    //     quot
    // }
    let func = make_func(
        "multi_vc",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
            LocalDecl { index: 4, ty: Ty::u32(), name: Some("sum".into()) },
            LocalDecl { index: 5, ty: Ty::u32(), name: Some("quot".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::field(3, 1)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Add),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(4)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            },
        ],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(
        &vcs,
        |k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }),
        "multi: overflow",
    );
    assert_single_vc(&vcs, |k| matches!(k, VcKind::DivisionByZero), "multi: div by zero");
}

// ---------------------------------------------------------------------------
// ProofLevel classification
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_vc_proof_levels() {
    // Build a function with a checked add (L0) and check proof level.
    let func = make_func(
        "proof_level_test",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::field(3, 1)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Add),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(
        &vcs,
        |k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }),
        "proof level: overflow",
    );
    for vc in &vcs {
        assert_eq!(vc.kind.proof_level(), ProofLevel::L0Safety, "overflow VCs should be L0 safety");
    }
}

// ---------------------------------------------------------------------------
// No VCs for empty function
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_empty_function_no_vcs() {
    let func = make_func(
        "empty",
        vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
        0,
    );

    let vcs = generate_vcs(&func);
    assert!(vcs.is_empty(), "empty function should produce no VCs");
}

// ---------------------------------------------------------------------------
// Type-unsupported obligation explosion: dedup across locals
// ---------------------------------------------------------------------------

#[test]
fn test_type_unsupported_obligations_dedup_across_locals() {
    // Regression for the obligation-generation explosion. MIR for a real
    // function (e.g. `extern_spec_registry::collect_entries`, which threads a
    // recursive `syn::Item` through hundreds of temporaries) was observed
    // emitting ~1.9M `UnsupportedMir` obligations that all coalesced to ~51
    // distinct (kind, span) display keys — one per local, per type node. The
    // per-type "unsupported" walk must dedup by structural type so a type
    // shared by N locals is walked once, not N times.
    let shared = Ty::Unsupported {
        kind: "TraitObjectDynItem".to_string(),
        detail: "dyn Item is not modeled".to_string(),
    };
    let n = 500usize;
    let locals: Vec<LocalDecl> =
        (0..n).map(|i| LocalDecl { index: i, ty: shared.clone(), name: None }).collect();
    let func = make_func(
        "many_locals_same_unsupported_ty",
        locals,
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
        0,
    );

    let vcs = generate_vcs(&func);
    let shared_unsupported: Vec<_> = vcs
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { detail, .. }
                if detail.contains("dyn Item is not modeled"))
        })
        .collect();

    // The shared type must still be flagged (soundness of the unsupported
    // signal is preserved) ...
    assert!(
        !shared_unsupported.is_empty(),
        "the shared unsupported type must still produce at least one obligation"
    );
    // ... but exactly once, regardless of how many locals share it (dedup), not
    // once per local. Pre-fix this was {n}; post-fix it is 1.
    assert!(
        shared_unsupported.len() <= 2,
        "shared unsupported type must be deduplicated across {n} locals (≤2 obligations), got {}",
        shared_unsupported.len()
    );
}

#[test]
fn test_type_unsupported_obligations_dedup_within_single_type_walk() {
    // Regression for the *within-walk* half of the explosion. A single deeply
    // structured type (modeling a recursive `syn` type after trust-mir-extract
    // expands it) emits one `UnsupportedMir` leaf per Unsupported node. All
    // same-`kind` leaves at one span share a single display key, so the
    // generation stream must collapse them to one obligation per distinct kind
    // — not one per leaf — matching the compiler's display coalescing. These
    // obligations are all preclassified to Unknown and never dispatched, so the
    // collapse cannot hide a provable or violating obligation.
    let leaf_a = Ty::Unsupported {
        kind: "TraitObjectDynItem".to_string(),
        detail: "dyn Item is not modeled".to_string(),
    };
    let leaf_b = Ty::Unsupported {
        kind: "FnPtrHigherRanked".to_string(),
        detail: "for<'a> fn(&'a T) is not modeled".to_string(),
    };
    // One tuple type carrying 200 Unsupported leaves: 150 of kind A, 50 of B.
    let mut fields: Vec<Ty> = Vec::new();
    fields.extend(std::iter::repeat(leaf_a).take(150));
    fields.extend(std::iter::repeat(leaf_b).take(50));
    let big_ty = Ty::Tuple(fields);
    let func = make_func(
        "single_local_wide_unsupported_ty",
        vec![LocalDecl { index: 0, ty: big_ty, name: None }],
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
        0,
    );

    let vcs = generate_vcs(&func);
    let kind_a = vcs
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "TraitObjectDynItem")
        })
        .count();
    let kind_b = vcs
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "FnPtrHigherRanked")
        })
        .count();

    // Each distinct kind survives exactly once (soundness signal preserved),
    // and the 150/50 same-kind leaves collapse rather than flowing downstream as
    // 200 raw obligations.
    assert_eq!(
        kind_a, 1,
        "150 same-kind leaves must collapse to one display-key obligation, got {kind_a}"
    );
    assert_eq!(
        kind_b, 1,
        "50 same-kind leaves must collapse to one display-key obligation, got {kind_b}"
    );
}

#[test]
fn test_type_unsupported_obligations_dedup_full_multiplicative_explosion() {
    // Headline regression faithfully mirroring the observed pathology:
    // `extern_spec_registry::collect_entries` threaded one recursive `syn`-shaped
    // type (expanded to many Unsupported leaves) through hundreds of temporaries.
    // The raw obligation count is then (locals) x (Unsupported leaves per type),
    // which was measured at ~1.9M for a function whose distinct display-key set
    // is a handful. Both dedup passes together must collapse that product:
    // per-structural-type dedup walks the shared type once across all locals, and
    // display-key dedup folds the same-(kind, span) leaves of that one walk into
    // one obligation per distinct kind.
    let leaf_a = Ty::Unsupported {
        kind: "TraitObjectDynItem".to_string(),
        detail: "dyn Item is not modeled".to_string(),
    };
    let leaf_b = Ty::Unsupported {
        kind: "FnPtrHigherRanked".to_string(),
        detail: "for<'a> fn(&'a T) is not modeled".to_string(),
    };
    let mut fields: Vec<Ty> = Vec::new();
    fields.extend(std::iter::repeat(leaf_a).take(150));
    fields.extend(std::iter::repeat(leaf_b).take(50));
    let wide_recursive_ty = Ty::Tuple(fields);

    // 300 locals all sharing the wide type: pre-fix this is 300 x 200 = 60_000
    // raw `UnsupportedMir` obligations; post-fix it is bounded by the distinct
    // display keys (2).
    let n_locals = 300usize;
    let locals: Vec<LocalDecl> = (0..n_locals)
        .map(|i| LocalDecl { index: i, ty: wide_recursive_ty.clone(), name: None })
        .collect();
    let func = make_func(
        "many_locals_wide_recursive_ty",
        locals,
        vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
        0,
    );

    let vcs = generate_vcs(&func);
    let total_unsupported =
        vcs.iter().filter(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { .. })).count();

    // The full multiplicative product collapses to the distinct display-key
    // count, independent of how many locals or leaves fed it. Soundness is
    // preserved: at least one Unknown obligation survives per distinct kind, so
    // the function can never be reported as fully proved.
    assert!(
        total_unsupported >= 2,
        "both distinct unsupported kinds must survive (soundness signal), got {total_unsupported}"
    );
    assert!(
        total_unsupported <= 8,
        "300 locals x 200 leaves ({}) must collapse to the distinct display-key count, got {total_unsupported}",
        n_locals * 200
    );
}

// ---------------------------------------------------------------------------
// BV mul dominating-guard translation (guard-bounded multiply must PROVE)
// ---------------------------------------------------------------------------

/// Shared shape: `if cols <= 4096 { cols * 64 }` (checked mul under a
/// dominating linear guard) — mirrors
/// tests/trust-falsification/proved/cell_grid_stride.rs.
// `if cols <= 4096 { cols * rows }` (u32). The multiplier is a VARIABLE:
// a const-multiplier mul is linear and deliberately routed to the Int/LIA
// path (91d8dcb9f8, where conjoined guards already bind), so only a
// var*var mul reaches the BV lane whose guard threading these tests pin.
fn guarded_checked_mul_func() -> VerifiableFunction {
    make_func(
        "guarded_checked_mul",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("cols".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("rows".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: None },
            LocalDecl { index: 4, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Le,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(4096, 32)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(3)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(4),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Mul,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::field(4, 1)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Mul),
                    target: BlockId(3),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
        ],
        2,
    )
}

fn mul_overflow_vc(vcs: &[VerificationCondition]) -> &VerificationCondition {
    vcs.iter()
        .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }))
        .expect("checked mul should produce an ArithmeticOverflow{Mul} VC")
}

#[test]
fn guarded_mul_vc_carries_bv_dominating_guard_bound() {
    let vcs = generate_vcs(&guarded_checked_mul_func());
    let vc = mul_overflow_vc(&vcs);
    let dbg = format!("{:?}", vc.formula);
    // The dominating `cols <= 4096` guard must be conjoined as a BV bound on
    // the fresh BV operand var, so the guard-bounded mul can PROVE.
    assert!(
        dbg.contains("__trust_ovf_bv_lhs_cols"),
        "BV mul formula must reference the fresh lhs operand var: {dbg}"
    );
    assert!(
        dbg.contains("BvULe") && dbg.contains("4096"),
        "the dominating guard must be BV-encoded (BvULe ... 4096): {dbg}"
    );
}

#[test]
fn unguarded_mul_vc_has_no_bv_guard_bound() {
    // MUTANT shape: the mul is in the entry block — no dominating guard, so no
    // BV bound may be conjoined (a fabricated bound could mask a real overflow).
    // var*var so the shape actually routes to the BV lane (a const multiplier
    // routes to Int per 91d8dcb9f8, where this property would hold vacuously).
    let func = make_func(
        "unguarded_checked_mul",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("cols".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("rows".into()) },
            LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Mul,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::field(3, 1)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Mul),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        2,
    );
    let vcs = generate_vcs(&func);
    let dbg = format!("{:?}", mul_overflow_vc(&vcs).formula);
    assert!(!dbg.contains("BvULe"), "unguarded mul must get no BV guard bound: {dbg}");
}

#[test]
fn join_reachable_mul_gets_no_bv_guard_bound() {
    // The mul block is reachable BOTH through the guard's true edge and its
    // false edge (a join): the guard does not dominate, so conjoining its
    // bound would be unsound. The path intersection must come up empty.
    let func = make_func(
        "join_reachable_checked_mul",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("cols".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: None },
            LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Le,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(4096, 32)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(0, BlockId(1))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            // False edge joins straight into the mul block.
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Goto(BlockId(2)) },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Mul,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(64, 32)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::field(3, 1)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Mul),
                    target: BlockId(3),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
        ],
        1,
    );
    let vcs = generate_vcs(&func);
    let dbg = format!("{:?}", mul_overflow_vc(&vcs).formula);
    assert!(
        !dbg.contains("BvULe"),
        "a non-dominating guard must contribute no BV bound (join unsoundness): {dbg}"
    );
}

#[test]
fn signed_guarded_mul_vc_carries_negative_bv_guard_bound() {
    // `if n >= -1000 && n <= 1000 { n * m }` (i32): both dominating bounds —
    // including the NEGATIVE one — must be BV-encoded onto the fresh operand
    // var with signed comparisons. The two's-complement constant masking is
    // exact in both downstream paths (formula/smtlib.rs printer and
    // ay_bindings::normalize_bitvec_value). The multiplier is a VARIABLE so
    // the shape routes to the BV lane (const multipliers go to Int, 91d8dcb9f8).
    let func = make_func(
        "signed_guarded_checked_mul",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("n".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("m".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: None },
            LocalDecl { index: 4, ty: Ty::Bool, name: None },
            LocalDecl { index: 5, ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]), name: None },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Ge,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Int(-1000)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(3)),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(4),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Le,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Int(1000)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(4)),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(5),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Mul,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::field(5, 1)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Mul),
                    target: BlockId(4),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
        ],
        2,
    );
    let vcs = generate_vcs(&func);
    let dbg = format!("{:?}", mul_overflow_vc(&vcs).formula);
    assert!(
        dbg.contains("__trust_ovf_bv_lhs_n"),
        "signed BV mul formula must reference the fresh lhs operand var: {dbg}"
    );
    assert!(
        dbg.contains("BvSLe") && dbg.contains("-1000"),
        "the negative dominating bound must be BV-encoded with a signed comparison: {dbg}"
    );
    assert!(dbg.contains("1000"), "the upper bound must be conjoined too: {dbg}");
}

#[test]
fn contract_bounded_mul_vc_carries_bv_precondition_bounds() {
    // `#[trust::requires(n <= 1000)] #[trust::requires(n >= 0)] ... n * 4`
    // (i32): the GATED precondition assumptions in func.preconditions must be
    // BV-encoded onto the fresh mul operand var, exactly like dominating path
    // guards — otherwise a contract-bounded multiply false-Fails on the
    // fresh-operand BV formula.
    // var*var so the shape routes to the BV lane (const multipliers go to the
    // Int/LIA path per 91d8dcb9f8, covered by the companion test below).
    let mut func = make_func(
        "contract_bounded_mul",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("n".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("m".into()) },
            LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]), name: None },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Mul,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::field(3, 1)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Mul),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        2,
    );
    func.preconditions = vec![
        Formula::Le(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(1000))),
        // Negative bounds arrive as Neg(Int(..)) wrappers, not Int(-..).
        Formula::Ge(
            Box::new(Formula::Var("n".into(), Sort::Int)),
            Box::new(Formula::Neg(Box::new(Formula::Int(1000)))),
        ),
    ];
    let vcs = generate_vcs(&func);
    let dbg = format!("{:?}", mul_overflow_vc(&vcs).formula);
    assert!(
        dbg.contains("__trust_ovf_bv_lhs_n") && dbg.contains("BvSLe"),
        "gated precondition bounds must be BV-encoded onto the mul operand: {dbg}"
    );
    assert!(dbg.contains("1000"), "the upper bound constant must appear: {dbg}");
    assert!(
        dbg.contains("-1000") || dbg.matches("BvSLe").count() >= 2,
        "the Neg-wrapped lower bound must be translated too: {dbg}"
    );
}

#[test]
fn precondition_bounded_const_mul_stays_int_and_carries_bounds() {
    // Companion contract for 91d8dcb9f8's routing decision: a CONST-multiplier
    // mul (`n * 4`) is linear, so it stays on the Int/LIA path — which must
    // conjoin the gated preconditions directly (no fresh BV vars that would
    // drop them). This is the exact shape the BV-threading tests above used
    // before the routing change; the two contracts together pin that BOTH
    // routes carry the bounds.
    let mut func = make_func(
        "precondition_bounded_const_mul",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("n".into()) },
            LocalDecl { index: 2, ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]), name: None },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Mul,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Int(4)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                    cond: Operand::Copy(Place::field(2, 1)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Mul),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
        1,
    );
    func.preconditions = vec![
        Formula::Le(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(1000))),
        Formula::Ge(
            Box::new(Formula::Var("n".into(), Sort::Int)),
            Box::new(Formula::Neg(Box::new(Formula::Int(1000)))),
        ),
    ];
    let vcs = generate_vcs(&func);
    let dbg = format!("{:?}", mul_overflow_vc(&vcs).formula);
    assert!(
        !dbg.contains("__trust_ovf_bv_"),
        "const-multiplier mul must stay on the Int path (no fresh BV operand vars): {dbg}"
    );
    assert!(
        dbg.contains("1000") && dbg.contains("Le("),
        "the Int path must conjoin the gated precondition bounds: {dbg}"
    );
    assert!(
        dbg.contains("Mul("),
        "the Int overflow disjunction over the product must be present: {dbg}"
    );
}
