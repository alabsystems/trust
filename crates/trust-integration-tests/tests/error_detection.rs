// trust-integration-tests/tests/error_detection.rs: Comprehensive error detection test suite
//
// Tests that Trust's verification pipeline detects common Rust errors across 12 VcKind categories:
// 1. Arithmetic overflow (add, sub, mul)
// 2. Division by zero (variable divisor vs constant divisor)
// 3. Index out of bounds (unchecked array access vs bounds-checked)
// 4. Remainder by zero (variable vs constant)
// 5. Shift overflow (shift amount >= bit width)
// 6. Cast overflow (narrowing integer cast)
// 7. Negation overflow (signed negation of INT_MIN)
// 8. Assertion (custom assert! failure)
// 9. Unreachable (reachable unreachable block)
// 10. Slice bounds check (unchecked slice indexing)
// 11. Invalid discriminant (discriminant read on non-enum)
//
// Each category: buggy version (ay finds counterexample or vcgen detects) + safe version.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_integration_tests::ay_test_support::require_ay;
use trust_router::VerificationBackend;
use trust_types::*;

// ===========================================================================
// Category 1: Arithmetic Overflow
// ===========================================================================

/// Buggy: `result = a + b` on u32 — no overflow guard.
///
/// MIR: bb0: _3 = CheckedAdd(_1, _2); Assert(!_3.1, overflow); goto bb1
///       bb1: _0 = _3.0; return
fn overflow_add_u32_buggy() -> VerifiableFunction {
    VerifiableFunction {
        name: "overflow_add_u32".to_string(),
        def_path: "test::overflow_add_u32".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
            ],
            blocks: vec![
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
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Buggy: `result = a - b` on u32 (unsigned subtraction overflow).
///
/// MIR: bb0: _3 = CheckedSub(_1, _2); Assert(!_3.1, overflow); goto bb1
///       bb1: _0 = _3.0; return
fn overflow_sub_u32_buggy() -> VerifiableFunction {
    VerifiableFunction {
        name: "overflow_sub_u32".to_string(),
        def_path: "test::overflow_sub_u32".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
            ],
            blocks: vec![
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
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Sub),
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Safe: `result = a + 1` where a is u8 with precondition a < 255.
/// Uses direct Formula construction for a provably-safe add.
fn overflow_add_safe_formula() -> VerificationCondition {
    // We encode: given 0 <= a <= 254, prove a + 1 <= 255 (i.e. no overflow)
    // Negated for ay: 0 <= a AND a <= 254 AND a + 1 > 255 (should be UNSAT)
    let a = Formula::Var("a".into(), Sort::Int);
    let one = Formula::Int(1);
    let sum = Formula::Add(Box::new(a.clone()), Box::new(one));
    let max = Formula::Int(255);

    let formula = Formula::And(vec![
        Formula::Ge(Box::new(a.clone()), Box::new(Formula::Int(0))),
        Formula::Le(Box::new(a), Box::new(Formula::Int(254))),
        Formula::Gt(Box::new(sum), Box::new(max)),
    ]);

    VerificationCondition {
        kind: VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::u8(), Ty::u8()) },
        function: "safe_add_one".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

// ===========================================================================
// Category 2: Division by Zero
// ===========================================================================

/// Buggy: `result = x / y` where y is an unconstrained variable.
fn divzero_variable_buggy() -> VerifiableFunction {
    VerifiableFunction {
        name: "div_by_var".to_string(),
        def_path: "test::div_by_var".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Safe: `result = x / 3` — constant divisor is never zero.
fn divzero_constant_safe() -> VerifiableFunction {
    VerifiableFunction {
        name: "div_by_three".to_string(),
        def_path: "test::div_by_three".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(3, 32)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

// ===========================================================================
// Category 3: Index Out of Bounds
// ===========================================================================

/// Buggy: `result = arr[idx]` where idx is unconstrained and arr has length 5.
fn index_oob_buggy() -> VerifiableFunction {
    VerifiableFunction {
        name: "unchecked_index".to_string(),
        def_path: "test::unchecked_index".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::u32()), len: 5 },
                    name: Some("arr".into()),
                },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("idx".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Index(2)],
                        })),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Safe: direct Formula encoding — index < array_len is provably in-bounds.
/// We encode: given 0 <= idx AND idx < 5, prove idx < 5 (tautology, UNSAT negation).
fn index_safe_formula() -> VerificationCondition {
    let idx = Formula::Var("idx".into(), Sort::Int);
    let len = Formula::Int(5);

    // Negated check: 0 <= idx AND idx < 5 AND idx >= 5 (should be UNSAT)
    let formula = Formula::And(vec![
        Formula::Ge(Box::new(idx.clone()), Box::new(Formula::Int(0))),
        Formula::Lt(Box::new(idx.clone()), Box::new(len.clone())),
        Formula::Ge(Box::new(idx), Box::new(len)),
    ]);

    VerificationCondition {
        kind: VcKind::IndexOutOfBounds,
        function: "safe_checked_index".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

// ===========================================================================
// Category 4: Remainder by Zero
// ===========================================================================

/// Buggy: `result = x % y` where y is unconstrained.
fn rem_zero_buggy() -> VerifiableFunction {
    VerifiableFunction {
        name: "rem_by_var".to_string(),
        def_path: "test::rem_by_var".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Rem,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Safe: `result = x % 7` — constant modulus never zero.
fn rem_constant_safe() -> VerifiableFunction {
    VerifiableFunction {
        name: "rem_by_seven".to_string(),
        def_path: "test::rem_by_seven".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Rem,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(7, 32)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

// ===========================================================================
// Category 5: Arithmetic Overflow (Mul)
// ===========================================================================

/// Buggy: `result = a * b` on u32 — no overflow guard.
fn overflow_mul_u32_buggy() -> VerifiableFunction {
    VerifiableFunction {
        name: "overflow_mul_u32".to_string(),
        def_path: "test::overflow_mul_u32".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
            ],
            blocks: vec![
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
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Mul),
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Safe: `result = a * 2` where a is u16 with precondition a <= 32767.
/// Uses direct Formula: given 0 <= a <= 32767, prove a * 2 <= 65535 (UNSAT negation).
fn overflow_mul_safe_formula() -> VerificationCondition {
    let a = Formula::Var("a".into(), Sort::Int);
    let two = Formula::Int(2);
    let product = Formula::Mul(Box::new(a.clone()), Box::new(two));
    let max = Formula::Int(65535);

    let formula = Formula::And(vec![
        Formula::Ge(Box::new(a.clone()), Box::new(Formula::Int(0))),
        Formula::Le(Box::new(a), Box::new(Formula::Int(32767))),
        Formula::Gt(Box::new(product), Box::new(max)),
    ]);

    VerificationCondition {
        kind: VcKind::ArithmeticOverflow { op: BinOp::Mul, operand_tys: (Ty::u16(), Ty::u16()) },
        function: "safe_mul_two".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

// ===========================================================================
// Category 6: Shift Overflow
// ===========================================================================

/// Buggy: `result = x << amt` where amt is unconstrained u32. The shift
/// can exceed bit width (32).
fn shift_overflow_buggy() -> VerifiableFunction {
    VerifiableFunction {
        name: "shift_left_unconstrained".to_string(),
        def_path: "test::shift_left_unconstrained".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("amt".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Shl,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Safe: shift amount is provably < 32.
/// Formula: 0 <= amt AND amt <= 31 AND amt >= 32 (UNSAT).
fn shift_overflow_safe_formula() -> VerificationCondition {
    let amt = Formula::Var("amt".into(), Sort::Int);

    let formula = Formula::And(vec![
        Formula::Ge(Box::new(amt.clone()), Box::new(Formula::Int(0))),
        Formula::Le(Box::new(amt.clone()), Box::new(Formula::Int(31))),
        Formula::Ge(Box::new(amt), Box::new(Formula::Int(32))),
    ]);

    VerificationCondition {
        kind: VcKind::ShiftOverflow { op: BinOp::Shl, operand_ty: Ty::u32(), shift_ty: Ty::u32() },
        function: "safe_shift".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

// ===========================================================================
// Category 7: Cast Overflow
// ===========================================================================

/// Buggy: `result = x as u8` where x is unconstrained u32.
fn cast_overflow_buggy() -> VerifiableFunction {
    VerifiableFunction {
        name: "cast_u32_to_u8".to_string(),
        def_path: "test::cast_u32_to_u8".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u8(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u8()),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u8(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Safe: value is provably in u8 range.
/// Formula: 0 <= x AND x <= 255 AND (x < 0 OR x > 255) (UNSAT).
fn cast_overflow_safe_formula() -> VerificationCondition {
    let x = Formula::Var("x".into(), Sort::Int);

    let formula = Formula::And(vec![
        Formula::Ge(Box::new(x.clone()), Box::new(Formula::Int(0))),
        Formula::Le(Box::new(x.clone()), Box::new(Formula::Int(255))),
        Formula::Or(vec![
            Formula::Lt(Box::new(x.clone()), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(x), Box::new(Formula::Int(255))),
        ]),
    ]);

    VerificationCondition {
        kind: VcKind::CastOverflow { from_ty: Ty::u32(), to_ty: Ty::u8() },
        function: "safe_cast".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

// ===========================================================================
// Category 8: Negation Overflow
// ===========================================================================

/// Buggy: `result = -x` where x is unconstrained i32 (x could be i32::MIN).
fn negation_overflow_buggy() -> VerifiableFunction {
    VerifiableFunction {
        name: "negate_i32".to_string(),
        def_path: "test::negate_i32".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Safe: x is provably > i32::MIN so negation cannot overflow.
/// Formula: x >= -2147483647 AND x <= 2147483647 AND x == -2147483648 (UNSAT).
fn negation_overflow_safe_formula() -> VerificationCondition {
    let x = Formula::Var("x".into(), Sort::Int);
    let int_min = Formula::Int(-2_147_483_648);

    let formula = Formula::And(vec![
        // x > INT_MIN, i.e. x >= INT_MIN+1
        Formula::Ge(Box::new(x.clone()), Box::new(Formula::Int(-2_147_483_647))),
        Formula::Le(Box::new(x.clone()), Box::new(Formula::Int(2_147_483_647))),
        // Violation: x == INT_MIN
        Formula::Eq(Box::new(x), Box::new(int_min)),
    ]);

    VerificationCondition {
        kind: VcKind::NegationOverflow { ty: Ty::i32() },
        function: "safe_negate".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

// ===========================================================================
// Category 9: Assertion
// ===========================================================================

/// Buggy: `assert!(flag)` where flag is an unconstrained bool. The assert
/// fires when flag is false, and ay will find a counterexample (flag = false).
fn assertion_buggy() -> VerifiableFunction {
    VerifiableFunction {
        name: "assert_flag".to_string(),
        def_path: "test::assert_flag".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(1)),
                        expected: true,
                        msg: AssertMessage::Custom("user assertion failed".to_string()),
                        target: BlockId(1),
                        unwind: trust_types::UnwindEdge::Unreachable,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Safe: direct Formula — assertion condition is tautologically true.
/// Formula: false (trivially UNSAT — no violation possible).
fn assertion_safe_formula() -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Assertion { message: "safe assertion".to_string() },
        function: "safe_assert".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
        obligation: None,
    }
}

// ===========================================================================
// Category 10: Unreachable
// ===========================================================================

/// Buggy: entry block IS the unreachable terminator — trivially reachable.
fn unreachable_buggy() -> VerifiableFunction {
    VerifiableFunction {
        name: "entry_unreachable".to_string(),
        def_path: "test::entry_unreachable".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Unreachable,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Safe: unreachable block is dead (not reachable from entry).
/// Block 0 returns; block 1 has Unreachable but no edge leads to it.
fn unreachable_safe() -> VerifiableFunction {
    VerifiableFunction {
        name: "dead_unreachable".to_string(),
        def_path: "test::dead_unreachable".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![
                BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Unreachable },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

// ===========================================================================
// Category 11: Slice Bounds Check
// ===========================================================================

/// Buggy: `result = slice[idx]` where idx is unconstrained and slice has
/// symbolic length. The bounds checker generates SliceBoundsCheck VCs.
fn slice_bounds_buggy() -> VerifiableFunction {
    VerifiableFunction {
        name: "unchecked_slice_index".to_string(),
        def_path: "test::unchecked_slice_index".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Slice { elem: Box::new(Ty::u32()) },
                    name: Some("s".into()),
                },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("idx".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Index(2)],
                        })),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Safe: direct Formula — index < slice_len with both bounded.
/// Formula: 0 <= idx AND 0 < len AND idx < len AND idx >= len (UNSAT).
fn slice_bounds_safe_formula() -> VerificationCondition {
    let idx = Formula::Var("idx".into(), Sort::Int);
    let len = Formula::Var("len".into(), Sort::Int);

    let formula = Formula::And(vec![
        Formula::Ge(Box::new(idx.clone()), Box::new(Formula::Int(0))),
        Formula::Gt(Box::new(len.clone()), Box::new(Formula::Int(0))),
        Formula::Lt(Box::new(idx.clone()), Box::new(len.clone())),
        // Violation: idx >= len
        Formula::Ge(Box::new(idx), Box::new(len)),
    ]);

    VerificationCondition {
        kind: VcKind::SliceBoundsCheck,
        function: "safe_slice_access".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

// ===========================================================================
// Category 12: Invalid Discriminant (pipeline fixture)
// ===========================================================================

/// Buggy: Discriminant read on a non-ADT (u32) type. The rvalue_safety
/// module detects this and generates an InvalidDiscriminant VC.
fn invalid_discriminant_buggy() -> VerifiableFunction {
    VerifiableFunction {
        name: "bad_discriminant".to_string(),
        def_path: "test::bad_discriminant".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("val".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: None }, // discriminant dest
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Discriminant(Place::local(1)),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Safe: Discriminant read on an ADT type — no VC generated.
fn invalid_discriminant_safe() -> VerifiableFunction {
    VerifiableFunction {
        name: "good_discriminant".to_string(),
        def_path: "test::good_discriminant".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Adt { adt_kind: None, layout: None, variants: Vec::new(),
                        name: "Option".to_string(),
                        fields: vec![
                            ("None".to_string(), Ty::Unit),
                            ("Some".to_string(), Ty::u32()),
                        ],
                        disc_index_safe: false,
                        // Trust (B3-1 field completion): pre-existing E0063.
                        faithful_enum_repr: None, enum_layout: None, },
                    name: Some("opt".into()),
                },
                LocalDecl { index: 2, ty: Ty::u32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Discriminant(Place::local(1)),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

// ===========================================================================
// Tests
// ===========================================================================

// --- Category 1: Arithmetic Overflow ---

#[test]
fn test_detect_overflow_add_u32() {
    let ay = require_ay();
    let func = overflow_add_u32_buggy();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for overflow_add_u32", vcs.len());
    for vc in &vcs {
        eprintln!("  VC: {:?} — {}", vc.kind, vc.function);
    }

    let overflow_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .collect();

    assert!(!overflow_vcs.is_empty(), "vcgen must produce ArithmeticOverflow(Add) VC for u32 add");

    for vc in &overflow_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result: {:?}", result);

        assert!(result.is_failed(), "ay must find u32 add can overflow. Got: {result:?}");

        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            assert!(!cex.assignments.is_empty(), "counterexample must have assignments");
            eprintln!("  Counterexample: {cex}");
        }
    }
}

#[test]
fn test_detect_overflow_sub_u32() {
    let ay = require_ay();
    let func = overflow_sub_u32_buggy();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for overflow_sub_u32", vcs.len());

    let overflow_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. }))
        .collect();

    assert!(
        !overflow_vcs.is_empty(),
        "vcgen must produce ArithmeticOverflow(Sub) VC for u32 subtract"
    );

    for vc in &overflow_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result for sub overflow: {:?}", result);

        assert!(result.is_failed(), "ay must find u32 subtract can underflow. Got: {result:?}");

        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            assert!(!cex.assignments.is_empty(), "counterexample must have assignments");
            eprintln!("  Counterexample: {cex}");
        }
    }
}

#[test]
fn test_detect_overflow_add_safe() {
    let ay = require_ay();
    let vc = overflow_add_safe_formula();

    let result = ay.verify(&vc);
    eprintln!("ay result for safe add: {:?}", result);

    assert!(
        result.is_proved(),
        "ay must prove a + 1 is safe when a <= 254 (UNSAT). Got: {result:?}"
    );
}

// --- Category 2: Division by Zero ---

#[test]
fn test_detect_divzero_variable() {
    let ay = require_ay();
    let func = divzero_variable_buggy();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for div_by_var", vcs.len());

    let divzero_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).collect();

    assert!(!divzero_vcs.is_empty(), "vcgen must produce DivisionByZero VC for variable divisor");

    for vc in &divzero_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result: {:?}", result);

        assert!(result.is_failed(), "ay must find variable divisor CAN be zero. Got: {result:?}");

        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            eprintln!("  Counterexample: {cex}");
        }
    }
}

#[test]
fn test_detect_divzero_constant_safe() {
    let ay = require_ay();
    let func = divzero_constant_safe();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for div_by_three", vcs.len());

    let divzero_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).collect();

    for vc in &divzero_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result for constant division: {:?}", result);

        assert!(
            result.is_proved(),
            "ay must prove division by constant 3 is safe (UNSAT). Got: {result:?}"
        );
    }
}

// --- Category 3: Index Out of Bounds ---

#[test]
fn test_detect_index_oob_unchecked() {
    let ay = require_ay();
    let func = index_oob_buggy();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for unchecked_index", vcs.len());
    for vc in &vcs {
        eprintln!("  VC: {:?} — {}", vc.kind, vc.function);
    }

    let bounds_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds)).collect();

    assert!(
        !bounds_vcs.is_empty(),
        "vcgen must produce IndexOutOfBounds VC for unchecked array access"
    );

    for vc in &bounds_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result for bounds check: {:?}", result);

        assert!(
            result.is_failed(),
            "ay must find unchecked index CAN be out of bounds. Got: {result:?}"
        );

        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            eprintln!("  Counterexample: {cex}");
        }
    }
}

#[test]
fn test_detect_index_bounds_safe() {
    let ay = require_ay();
    let vc = index_safe_formula();

    let result = ay.verify(&vc);
    eprintln!("ay result for safe index: {:?}", result);

    assert!(result.is_proved(), "ay must prove bounded index is safe (UNSAT). Got: {result:?}");
}

// --- Category 4: Remainder by Zero ---

#[test]
fn test_detect_remzero_variable() {
    let ay = require_ay();
    let func = rem_zero_buggy();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for rem_by_var", vcs.len());

    let rem_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::RemainderByZero)).collect();

    assert!(!rem_vcs.is_empty(), "vcgen must produce RemainderByZero VC for variable modulus");

    for vc in &rem_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result for rem by var: {:?}", result);

        assert!(result.is_failed(), "ay must find variable modulus CAN be zero. Got: {result:?}");

        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            eprintln!("  Counterexample: {cex}");
        }
    }
}

#[test]
fn test_detect_remzero_constant_safe() {
    let ay = require_ay();
    let func = rem_constant_safe();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for rem_by_seven", vcs.len());

    let rem_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::RemainderByZero)).collect();

    for vc in &rem_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result for constant remainder: {:?}", result);

        assert!(
            result.is_proved(),
            "ay must prove remainder by constant 7 is safe (UNSAT). Got: {result:?}"
        );
    }
}

// --- Category 5: Arithmetic Overflow (Mul) ---

#[test]
fn test_detect_overflow_mul_u32() {
    let ay = require_ay();
    let func = overflow_mul_u32_buggy();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for overflow_mul_u32", vcs.len());
    for vc in &vcs {
        eprintln!("  VC: {:?} -- {}", vc.kind, vc.function);
    }

    let overflow_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }))
        .collect();

    assert!(
        !overflow_vcs.is_empty(),
        "vcgen must produce ArithmeticOverflow(Mul) VC for u32 multiply"
    );

    for vc in &overflow_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result for mul overflow: {:?}", result);

        assert!(result.is_failed(), "ay must find u32 multiply can overflow. Got: {result:?}");

        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            assert!(!cex.assignments.is_empty(), "counterexample must have assignments");
            eprintln!("  Counterexample: {cex}");
        }
    }
}

#[test]
fn test_detect_overflow_mul_safe() {
    let ay = require_ay();
    let vc = overflow_mul_safe_formula();

    let result = ay.verify(&vc);
    eprintln!("ay result for safe mul: {:?}", result);

    assert!(
        result.is_proved(),
        "ay must prove a * 2 is safe when a <= 32767 (UNSAT). Got: {result:?}"
    );
}

// --- Category 6: Shift Overflow ---

#[test]
fn test_detect_shift_overflow_unconstrained() {
    let ay = require_ay();
    let func = shift_overflow_buggy();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for shift_left_unconstrained", vcs.len());
    for vc in &vcs {
        eprintln!("  VC: {:?} -- {}", vc.kind, vc.function);
    }

    let shift_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::ShiftOverflow { .. })).collect();

    assert!(
        !shift_vcs.is_empty(),
        "vcgen must produce ShiftOverflow VC for unconstrained shift amount"
    );

    for vc in &shift_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result for shift overflow: {:?}", result);

        assert!(
            result.is_failed(),
            "ay must find unconstrained shift CAN overflow. Got: {result:?}"
        );

        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            eprintln!("  Counterexample: {cex}");
        }
    }
}

#[test]
fn test_detect_shift_overflow_safe() {
    let ay = require_ay();
    let vc = shift_overflow_safe_formula();

    let result = ay.verify(&vc);
    eprintln!("ay result for safe shift: {:?}", result);

    assert!(
        result.is_proved(),
        "ay must prove bounded shift amount is safe (UNSAT). Got: {result:?}"
    );
}

// --- Category 7: Cast Overflow ---

#[test]
fn test_detect_cast_overflow_u32_to_u8() {
    let ay = require_ay();
    let func = cast_overflow_buggy();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for cast_u32_to_u8", vcs.len());
    for vc in &vcs {
        eprintln!("  VC: {:?} -- {}", vc.kind, vc.function);
    }

    let cast_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::CastOverflow { .. })).collect();

    assert!(!cast_vcs.is_empty(), "vcgen must produce CastOverflow VC for u32 -> u8 cast");

    for vc in &cast_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result for cast overflow: {:?}", result);

        assert!(result.is_failed(), "ay must find u32 -> u8 cast CAN overflow. Got: {result:?}");

        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            eprintln!("  Counterexample: {cex}");
        }
    }
}

#[test]
fn test_detect_cast_overflow_safe() {
    let ay = require_ay();
    let vc = cast_overflow_safe_formula();

    let result = ay.verify(&vc);
    eprintln!("ay result for safe cast: {:?}", result);

    assert!(
        result.is_proved(),
        "ay must prove bounded value cast is safe (UNSAT). Got: {result:?}"
    );
}

// --- Category 8: Negation Overflow ---

#[test]
fn test_detect_negation_overflow_i32() {
    let ay = require_ay();
    let func = negation_overflow_buggy();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for negate_i32", vcs.len());
    for vc in &vcs {
        eprintln!("  VC: {:?} -- {}", vc.kind, vc.function);
    }

    let neg_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. })).collect();

    assert!(
        !neg_vcs.is_empty(),
        "vcgen must produce NegationOverflow VC for unconstrained i32 negation"
    );

    for vc in &neg_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result for negation overflow: {:?}", result);

        assert!(
            result.is_failed(),
            "ay must find i32 negation CAN overflow (INT_MIN). Got: {result:?}"
        );

        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            eprintln!("  Counterexample: {cex}");
        }
    }
}

#[test]
fn test_detect_negation_overflow_safe() {
    let ay = require_ay();
    let vc = negation_overflow_safe_formula();

    let result = ay.verify(&vc);
    eprintln!("ay result for safe negation: {:?}", result);

    assert!(
        result.is_proved(),
        "ay must prove negation of non-INT_MIN value is safe (UNSAT). Got: {result:?}"
    );
}

// --- Category 9: Assertion ---

#[test]
fn test_detect_assertion_buggy() {
    let ay = require_ay();
    let func = assertion_buggy();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for assert_flag", vcs.len());
    for vc in &vcs {
        eprintln!("  VC: {:?} -- {}", vc.kind, vc.function);
    }

    let assert_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Assertion { .. })).collect();

    assert!(
        !assert_vcs.is_empty(),
        "vcgen must produce Assertion VC for unconstrained bool assertion"
    );

    for vc in &assert_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result for assertion: {:?}", result);

        assert!(
            result.is_failed(),
            "ay must find assertion CAN fail (flag can be false). Got: {result:?}"
        );
    }
}

#[test]
fn test_detect_assertion_safe() {
    let ay = require_ay();
    let vc = assertion_safe_formula();

    let result = ay.verify(&vc);
    eprintln!("ay result for safe assertion: {:?}", result);

    assert!(
        result.is_proved(),
        "ay must prove tautological assertion is safe (UNSAT). Got: {result:?}"
    );
}

// --- Category 10: Unreachable ---

#[test]
fn test_detect_unreachable_buggy() {
    let ay = require_ay();
    let func = unreachable_buggy();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for entry_unreachable", vcs.len());
    for vc in &vcs {
        eprintln!("  VC: {:?} -- {}", vc.kind, vc.function);
    }

    let unreach_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Unreachable)).collect();

    assert!(
        !unreach_vcs.is_empty(),
        "vcgen must produce Unreachable VC for entry-block unreachable"
    );

    for vc in &unreach_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result for unreachable: {:?}", result);

        assert!(
            result.is_failed(),
            "ay must find entry-block unreachable IS reachable. Got: {result:?}"
        );
    }
}

#[test]
fn test_detect_unreachable_safe() {
    let func = unreachable_safe();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for dead_unreachable", vcs.len());

    let unreach_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Unreachable)).collect();

    assert!(
        unreach_vcs.is_empty(),
        "vcgen must NOT produce Unreachable VC for dead block (no path to it)"
    );
}

// --- Category 11: Slice Bounds Check ---

#[test]
fn test_detect_slice_bounds_buggy() {
    let ay = require_ay();
    let func = slice_bounds_buggy();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for unchecked_slice_index", vcs.len());
    for vc in &vcs {
        eprintln!("  VC: {:?} -- {}", vc.kind, vc.function);
    }

    let slice_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck)).collect();

    assert!(
        !slice_vcs.is_empty(),
        "vcgen must produce SliceBoundsCheck VC for unchecked slice index"
    );

    for vc in &slice_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result for slice bounds: {:?}", result);

        assert!(
            result.is_failed(),
            "ay must find unchecked slice index CAN be out of bounds. Got: {result:?}"
        );
    }
}

#[test]
fn test_detect_slice_bounds_safe() {
    let ay = require_ay();
    let vc = slice_bounds_safe_formula();

    let result = ay.verify(&vc);
    eprintln!("ay result for safe slice access: {:?}", result);

    assert!(
        result.is_proved(),
        "ay must prove bounded slice access is safe (UNSAT). Got: {result:?}"
    );
}

// --- Category 12: Invalid Discriminant (pipeline fixture) ---

#[test]
fn test_detect_invalid_discriminant_buggy() {
    let ay = require_ay();
    let func = invalid_discriminant_buggy();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for bad_discriminant", vcs.len());
    for vc in &vcs {
        eprintln!("  VC: {:?} -- {}", vc.kind, vc.function);
    }

    let discr_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::InvalidDiscriminant { .. })).collect();

    assert!(
        !discr_vcs.is_empty(),
        "vcgen must produce InvalidDiscriminant VC for discriminant read on u32"
    );

    for vc in &discr_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result for invalid discriminant: {:?}", result);

        assert!(
            result.is_failed(),
            "ay must find discriminant on non-ADT IS invalid. Got: {result:?}"
        );
    }
}

#[test]
fn test_detect_invalid_discriminant_safe() {
    let func = invalid_discriminant_safe();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for good_discriminant", vcs.len());

    let discr_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::InvalidDiscriminant { .. })).collect();

    assert!(
        discr_vcs.is_empty(),
        "vcgen must NOT produce InvalidDiscriminant VC for ADT discriminant read"
    );
}
