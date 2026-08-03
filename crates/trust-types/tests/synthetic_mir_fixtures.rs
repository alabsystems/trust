// trust-types integration tests: Synthetic MIR fixtures for error detection
//
// Exercises each error-detection VcKind by constructing realistic MIR fixtures
// without going through rustc parsing. Part of Epic #553.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

// ---------------------------------------------------------------------------
// Helpers (inline since test_utils requires feature gate)
// ---------------------------------------------------------------------------

/// Source span pointing at a specific line for fixture clarity.
fn span_at(file: &str, line: u32) -> SourceSpan {
    SourceSpan {
        file: file.to_string(),
        line_start: line,
        col_start: 1,
        line_end: line,
        col_end: 1,
    }
}

/// Make a VC with kind, function name, and explicit formula.
fn make_vc(kind: VcKind, function: &str, formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: function.into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

/// Make a VC with default formula.
fn make_default_vc(kind: VcKind, function: &str) -> VerificationCondition {
    make_vc(kind, function, Formula::Bool(true))
}

/// Make a VerifiableFunction with given name and body.
fn make_func(name: &str, body: VerifiableBody) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("fixtures::{name}"),
        span: SourceSpan::default(),
        body,
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Make a LocalDecl.
fn local(idx: usize, ty: Ty) -> LocalDecl {
    LocalDecl { index: idx, ty, name: None }
}

/// Make a named LocalDecl.
fn named_local(idx: usize, name: &str, ty: Ty) -> LocalDecl {
    LocalDecl { index: idx, ty, name: Some(name.to_string()) }
}

/// Make a constant i32 operand.
fn const_i32(val: i32) -> Operand {
    Operand::Constant(ConstValue::Int(i128::from(val)))
}

// ---------------------------------------------------------------------------
// ArithmeticOverflow: fn add_i32(a: i32, b: i32) -> i32 { a + b }
//
// MIR:
//   _0: i32 (return), _1: i32 (a), _2: i32 (b)
//   _3: (i32, bool) (checked add result)
//   bb0: _3 = CheckedAdd(_1, _2); assert(!_3.1, "overflow") -> bb1
//   bb1: _0 = _3.0; return
// ---------------------------------------------------------------------------

#[test]
fn fixture_arithmetic_overflow_add_i32() {
    let func = VerifiableFunction {
        name: "add_i32".to_string(),
        def_path: "fixtures::add_i32".to_string(),
        span: span_at("fixtures.rs", 10),
        body: VerifiableBody {
            locals: vec![
                local(0, Ty::i32()),
                named_local(1, "a", Ty::i32()),
                named_local(2, "b", Ty::i32()),
                local(3, Ty::Tuple(vec![Ty::i32(), Ty::Bool])),
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
                        span: span_at("fixtures.rs", 11),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: span_at("fixtures.rs", 11),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                        span: span_at("fixtures.rs", 11),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    assert_eq!(func.name, "add_i32");
    assert_eq!(func.body.locals.len(), 4);
    assert_eq!(func.body.blocks.len(), 2);
    assert_eq!(func.body.arg_count, 2);

    // Verify overflow assert is present
    assert!(func.body.blocks.iter().any(|bb| matches!(
        &bb.terminator,
        Terminator::Assert { msg: AssertMessage::Overflow(BinOp::Add), .. }
    )));

    // Build the corresponding VC: a + b overflows i32
    let a = Formula::Var("a".to_string(), Sort::BitVec(32));
    let b = Formula::Var("b".to_string(), Sort::BitVec(32));
    let overflow_formula = Formula::Or(vec![
        Formula::Gt(
            Box::new(Formula::Add(Box::new(a.clone()), Box::new(b.clone()))),
            Box::new(Formula::Int(i128::from(i32::MAX))),
        ),
        Formula::Lt(
            Box::new(Formula::Add(Box::new(a), Box::new(b))),
            Box::new(Formula::Int(i128::from(i32::MIN))),
        ),
    ]);

    let vc = make_vc(
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) },
        "add_i32",
        overflow_formula,
    );
    assert_eq!(vc.function, "add_i32");
    assert!(matches!(&vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }));

    // Clause discovery: Assert produces 2 clauses (holds + fails)
    let clauses = func.body.discovered_clauses();
    assert_eq!(clauses.len(), 2);
    assert!(clauses.iter().any(|c| matches!(c.target, ClauseTarget::Panic)));

    // Serde roundtrip
    let json = serde_json::to_string(&func).expect("serialize");
    let rt: VerifiableFunction = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(rt.name, func.name);
    assert_eq!(rt.body.locals.len(), func.body.locals.len());
}

// ---------------------------------------------------------------------------
// ArithmeticOverflow (Sub): fn sub_u8(a: u8, b: u8) -> u8 { a - b }
// ---------------------------------------------------------------------------

#[test]
fn fixture_arithmetic_overflow_sub_u8() {
    let func = VerifiableFunction {
        name: "sub_u8".to_string(),
        def_path: "fixtures::sub_u8".to_string(),
        span: span_at("fixtures.rs", 20),
        body: VerifiableBody {
            locals: vec![
                local(0, Ty::u8()),
                named_local(1, "a", Ty::u8()),
                named_local(2, "b", Ty::u8()),
                local(3, Ty::Tuple(vec![Ty::u8(), Ty::Bool])),
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
                        span: span_at("fixtures.rs", 21),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Sub),
                        target: BlockId(1),
                        span: span_at("fixtures.rs", 21),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                        span: span_at("fixtures.rs", 21),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::u8(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    assert!(func.body.blocks.iter().any(|bb| matches!(
        &bb.terminator,
        Terminator::Assert { msg: AssertMessage::Overflow(BinOp::Sub), .. }
    )));

    let vc = make_vc(
        VcKind::ArithmeticOverflow { op: BinOp::Sub, operand_tys: (Ty::u8(), Ty::u8()) },
        "sub_u8",
        Formula::Gt(
            Box::new(Formula::Var("b".to_string(), Sort::BitVec(8))),
            Box::new(Formula::Var("a".to_string(), Sort::BitVec(8))),
        ),
    );
    assert!(matches!(&vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. }));
}

// ---------------------------------------------------------------------------
// ArithmeticOverflow (Mul): fn mul_i64(a: i64, b: i64) -> i64 { a * b }
// ---------------------------------------------------------------------------

#[test]
fn fixture_arithmetic_overflow_mul_i64() {
    let func = make_func(
        "mul_i64",
        VerifiableBody {
            locals: vec![
                local(0, Ty::i64()),
                named_local(1, "a", Ty::i64()),
                named_local(2, "b", Ty::i64()),
                local(3, Ty::Tuple(vec![Ty::i64(), Ty::Bool])),
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
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
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
            return_ty: Ty::i64(),
        },
    );

    assert!(func.body.blocks.iter().any(|bb| matches!(
        &bb.terminator,
        Terminator::Assert { msg: AssertMessage::Overflow(BinOp::Mul), .. }
    )));

    let vc = make_vc(
        VcKind::ArithmeticOverflow { op: BinOp::Mul, operand_tys: (Ty::i64(), Ty::i64()) },
        "mul_i64",
        Formula::Bool(true),
    );
    assert!(matches!(&vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }));
}

// ---------------------------------------------------------------------------
// ShiftOverflow: fn shl_u32(val: u32, shift: u32) -> u32 { val << shift }
//
// MIR:
//   bb0: _3 = CheckedShl(_1, _2); assert(!_3.1, "overflow") -> bb1
//   bb1: _0 = _3.0; return
// ---------------------------------------------------------------------------

#[test]
fn fixture_shift_overflow_shl() {
    let func = make_func(
        "shl_u32",
        VerifiableBody {
            locals: vec![
                local(0, Ty::u32()),
                named_local(1, "val", Ty::u32()),
                named_local(2, "shift", Ty::u32()),
                local(3, Ty::Tuple(vec![Ty::u32(), Ty::Bool])),
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Shl,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Shl),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
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
    );

    // Shift overflow: shift >= bit_width
    let shift_var = Formula::Var("shift".to_string(), Sort::BitVec(32));
    let vc = make_vc(
        VcKind::ShiftOverflow { op: BinOp::Shl, operand_ty: Ty::u32(), shift_ty: Ty::u32() },
        "shl_u32",
        Formula::Ge(Box::new(shift_var), Box::new(Formula::Int(32))),
    );
    assert!(matches!(&vc.kind, VcKind::ShiftOverflow { op: BinOp::Shl, .. }));

    assert!(func.body.blocks.iter().any(|bb| matches!(
        &bb.terminator,
        Terminator::Assert { msg: AssertMessage::Overflow(BinOp::Shl), .. }
    )));
}

#[test]
fn fixture_shift_overflow_shr() {
    let func = make_func(
        "shr_i16",
        VerifiableBody {
            locals: vec![
                local(0, Ty::i16()),
                named_local(1, "val", Ty::i16()),
                named_local(2, "shift", Ty::u32()),
                local(3, Ty::Tuple(vec![Ty::i16(), Ty::Bool])),
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Shr,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Shr),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
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
            return_ty: Ty::i16(),
        },
    );

    let vc = make_vc(
        VcKind::ShiftOverflow { op: BinOp::Shr, operand_ty: Ty::i16(), shift_ty: Ty::u32() },
        "shr_i16",
        Formula::Ge(
            Box::new(Formula::Var("shift".to_string(), Sort::BitVec(32))),
            Box::new(Formula::Int(16)),
        ),
    );
    assert!(matches!(&vc.kind, VcKind::ShiftOverflow { op: BinOp::Shr, .. }));

    let clauses = func.body.discovered_clauses();
    assert_eq!(clauses.len(), 2);
}

// ---------------------------------------------------------------------------
// DivisionByZero: fn div_i32(a: i32, b: i32) -> i32 { a / b }
//
// MIR:
//   bb0: assert(b != 0, "division by zero") -> bb1
//   bb1: _0 = Div(_1, _2); return
// ---------------------------------------------------------------------------

#[test]
fn fixture_division_by_zero() {
    let func = VerifiableFunction {
        name: "div_i32".to_string(),
        def_path: "fixtures::div_i32".to_string(),
        span: span_at("fixtures.rs", 30),
        body: VerifiableBody {
            locals: vec![
                local(0, Ty::i32()),
                named_local(1, "a", Ty::i32()),
                named_local(2, "b", Ty::i32()),
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(2)),
                        expected: false,
                        msg: AssertMessage::DivisionByZero,
                        target: BlockId(1),
                        span: span_at("fixtures.rs", 31),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span_at("fixtures.rs", 31),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    assert!(func.body.blocks.iter().any(|bb| matches!(
        &bb.terminator,
        Terminator::Assert { msg: AssertMessage::DivisionByZero, .. }
    )));

    let vc = make_vc(
        VcKind::DivisionByZero,
        "div_i32",
        Formula::Eq(
            Box::new(Formula::Var("b".to_string(), Sort::BitVec(32))),
            Box::new(Formula::Int(0)),
        ),
    );
    assert!(matches!(&vc.kind, VcKind::DivisionByZero));

    // Serde roundtrip
    let json = serde_json::to_string(&vc).expect("serialize vc");
    let rt: VerificationCondition = serde_json::from_str(&json).expect("deserialize vc");
    assert!(matches!(&rt.kind, VcKind::DivisionByZero));
}

// ---------------------------------------------------------------------------
// RemainderByZero: fn rem_u64(a: u64, b: u64) -> u64 { a % b }
// ---------------------------------------------------------------------------

#[test]
fn fixture_remainder_by_zero() {
    let func = make_func(
        "rem_u64",
        VerifiableBody {
            locals: vec![
                local(0, Ty::u64()),
                named_local(1, "a", Ty::u64()),
                named_local(2, "b", Ty::u64()),
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(2)),
                        expected: false,
                        msg: AssertMessage::RemainderByZero,
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
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
                },
            ],
            arg_count: 2,
            return_ty: Ty::u64(),
        },
    );

    assert!(func.body.blocks.iter().any(|bb| matches!(
        &bb.terminator,
        Terminator::Assert { msg: AssertMessage::RemainderByZero, .. }
    )));

    let vc = make_vc(
        VcKind::RemainderByZero,
        "rem_u64",
        Formula::Eq(
            Box::new(Formula::Var("b".to_string(), Sort::BitVec(64))),
            Box::new(Formula::Int(0)),
        ),
    );
    assert!(matches!(&vc.kind, VcKind::RemainderByZero));
}

// ---------------------------------------------------------------------------
// IndexOutOfBounds: fn index_array(arr: [i32; 4], idx: usize) -> i32 { arr[idx] }
//
// MIR:
//   bb0: _3 = Len(_1); assert(Lt(_2, _3), "bounds check") -> bb1
//   bb1: _0 = _1[_2]; return
// ---------------------------------------------------------------------------

#[test]
fn fixture_index_out_of_bounds() {
    let arr_ty = Ty::Array { elem: Box::new(Ty::i32()), len: 4 };
    let func = VerifiableFunction {
        name: "index_array".to_string(),
        def_path: "fixtures::index_array".to_string(),
        span: span_at("fixtures.rs", 40),
        body: VerifiableBody {
            locals: vec![
                local(0, Ty::i32()),
                named_local(1, "arr", arr_ty),
                named_local(2, "idx", Ty::usize()),
                local(3, Ty::usize()),
                local(4, Ty::Bool),
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Len(Place::local(1)),
                            span: span_at("fixtures.rs", 41),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(2)),
                                Operand::Copy(Place::local(3)),
                            ),
                            span: span_at("fixtures.rs", 41),
                        },
                    ],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(4)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck,
                        target: BlockId(1),
                        span: span_at("fixtures.rs", 41),
                        unwind: UnwindEdge::Unreachable,
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
                        span: span_at("fixtures.rs", 41),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    assert!(func.body.blocks.iter().any(|bb| matches!(
        &bb.terminator,
        Terminator::Assert { msg: AssertMessage::BoundsCheck, expected: true, .. }
    )));

    let vc = make_vc(
        VcKind::IndexOutOfBounds,
        "index_array",
        Formula::Ge(
            Box::new(Formula::Var("idx".to_string(), Sort::BitVec(64))),
            Box::new(Formula::Var("len".to_string(), Sort::BitVec(64))),
        ),
    );
    assert!(matches!(&vc.kind, VcKind::IndexOutOfBounds));

    // Verify Len rvalue is present
    assert!(
        func.body.blocks[0]
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { rvalue: Rvalue::Len(_), .. }))
    );
}

// ---------------------------------------------------------------------------
// SliceBoundsCheck: fn slice_range(s: &[u8], start: usize, end: usize) -> &[u8]
//
// MIR:
//   bb0: assert(start <= end, "slice bounds") -> bb1
//   bb1: assert(end <= len(s), "slice bounds") -> bb2
//   bb2: _0 = s[start..end]; return
// ---------------------------------------------------------------------------

#[test]
fn fixture_slice_bounds_check() {
    let slice_ty =
        Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) };
    let func = VerifiableFunction {
        name: "slice_range".to_string(),
        def_path: "fixtures::slice_range".to_string(),
        span: span_at("fixtures.rs", 50),
        body: VerifiableBody {
            locals: vec![
                local(0, slice_ty.clone()),
                named_local(1, "s", slice_ty),
                named_local(2, "start", Ty::usize()),
                named_local(3, "end", Ty::usize()),
                local(4, Ty::usize()),
                local(5, Ty::Bool),
                local(6, Ty::Bool),
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Len(Place::local(1)),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Le,
                                Operand::Copy(Place::local(2)),
                                Operand::Copy(Place::local(3)),
                            ),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(5)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck,
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(6),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Le,
                            Operand::Copy(Place::local(3)),
                            Operand::Copy(Place::local(4)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(6)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck,
                        target: BlockId(2),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Subslice {
                                from: 2,
                                to: 3,
                                from_end: false,
                            }],
                        })),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 3,
            return_ty: Ty::Ref {
                mutable: false,
                inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
            },
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    // Two bounds-check asserts
    let assert_count = func
        .body
        .blocks
        .iter()
        .filter(|bb| {
            matches!(&bb.terminator, Terminator::Assert { msg: AssertMessage::BoundsCheck, .. })
        })
        .count();
    assert_eq!(assert_count, 2, "expected 2 bounds-check asserts for slice range");

    let vc = make_vc(
        VcKind::SliceBoundsCheck,
        "slice_range",
        Formula::Or(vec![
            Formula::Gt(
                Box::new(Formula::Var("start".to_string(), Sort::BitVec(64))),
                Box::new(Formula::Var("end".to_string(), Sort::BitVec(64))),
            ),
            Formula::Gt(
                Box::new(Formula::Var("end".to_string(), Sort::BitVec(64))),
                Box::new(Formula::Var("len".to_string(), Sort::BitVec(64))),
            ),
        ]),
    );
    assert!(matches!(&vc.kind, VcKind::SliceBoundsCheck));

    // Clause discovery: 2 asserts x 2 clauses each = 4 total
    let clauses = func.body.discovered_clauses();
    assert_eq!(clauses.len(), 4);
}

// ---------------------------------------------------------------------------
// CastOverflow: fn i32_to_u8(x: i32) -> u8 { x as u8 }
// ---------------------------------------------------------------------------

#[test]
fn fixture_cast_overflow() {
    let func = make_func(
        "i32_to_u8",
        VerifiableBody {
            locals: vec![local(0, Ty::u8()), named_local(1, "x", Ty::i32()), local(2, Ty::Bool)],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Le,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(255)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(2)),
                        expected: true,
                        msg: AssertMessage::Custom("cast overflow".to_string()),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::u8()),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::u8(),
        },
    );

    let x = Formula::Var("x".to_string(), Sort::BitVec(32));
    let vc = make_vc(
        VcKind::CastOverflow { from_ty: Ty::i32(), to_ty: Ty::u8() },
        "i32_to_u8",
        Formula::Or(vec![
            Formula::Lt(Box::new(x.clone()), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(x), Box::new(Formula::Int(255))),
        ]),
    );
    assert!(matches!(&vc.kind, VcKind::CastOverflow { .. }));

    // Verify cast rvalue exists
    assert!(func.body.blocks.iter().any(|bb| {
        bb.stmts.iter().any(|s| matches!(s, Statement::Assign { rvalue: Rvalue::Cast(_, _), .. }))
    }));
}

// ---------------------------------------------------------------------------
// NegationOverflow: fn negate_i8(x: i8) -> i8 { -x }
//
// MIR:
//   bb0: assert(x != i8::MIN, "negate with overflow") -> bb1
//   bb1: _0 = Neg(_1); return
// ---------------------------------------------------------------------------

#[test]
fn fixture_negation_overflow() {
    let func = make_func(
        "negate_i8",
        VerifiableBody {
            locals: vec![local(0, Ty::i8()), named_local(1, "x", Ty::i8()), local(2, Ty::Bool)],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Ne,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(i128::from(i8::MIN))),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(2)),
                        expected: true,
                        msg: AssertMessage::OverflowNeg,
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::i8(),
        },
    );

    assert!(func.body.blocks.iter().any(|bb| matches!(
        &bb.terminator,
        Terminator::Assert { msg: AssertMessage::OverflowNeg, .. }
    )));

    let vc = make_vc(
        VcKind::NegationOverflow { ty: Ty::i8() },
        "negate_i8",
        Formula::Eq(
            Box::new(Formula::Var("x".to_string(), Sort::BitVec(8))),
            Box::new(Formula::Int(i128::from(i8::MIN))),
        ),
    );
    assert!(matches!(&vc.kind, VcKind::NegationOverflow { .. }));

    // Verify Neg unary op exists
    assert!(func.body.blocks.iter().any(|bb| {
        bb.stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { rvalue: Rvalue::UnaryOp(UnOp::Neg, _), .. }))
    }));
}

// ---------------------------------------------------------------------------
// Unreachable: fn unreachable_after_match(x: bool) -> i32
//
// MIR:
//   bb0: switchInt(x) -> [true: bb1, false: bb2]
//   bb1: _0 = 1; return
//   bb2: _0 = 0; return
//   bb3: unreachable  (dead code after exhaustive match)
// ---------------------------------------------------------------------------

#[test]
fn fixture_unreachable() {
    let func = make_func(
        "unreachable_after_match",
        VerifiableBody {
            locals: vec![local(0, Ty::i32()), named_local(1, "x", Ty::Bool)],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(1, BlockId(1)), (0, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(const_i32(1)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(const_i32(0)),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Unreachable },
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
    );

    assert!(func.body.blocks.iter().any(|bb| matches!(&bb.terminator, Terminator::Unreachable)));

    let vc = make_vc(
        VcKind::Unreachable,
        "unreachable_after_match",
        Formula::Not(Box::new(Formula::Or(vec![
            Formula::Eq(
                Box::new(Formula::Var("x".to_string(), Sort::Bool)),
                Box::new(Formula::Bool(true)),
            ),
            Formula::Eq(
                Box::new(Formula::Var("x".to_string(), Sort::Bool)),
                Box::new(Formula::Bool(false)),
            ),
        ]))),
    );
    assert!(matches!(&vc.kind, VcKind::Unreachable));

    // Path map should show bb3 reached via otherwise branch
    let path_map = func.body.path_map();
    let bb3 = path_map.iter().find(|e| e.block == BlockId(3)).expect("bb3 reachable in path map");
    assert_eq!(bb3.exits, vec![ClauseTarget::Unreachable]);
}

// ---------------------------------------------------------------------------
// Assertion: fn assert_positive(x: i32) { assert!(x > 0) }
//
// MIR:
//   bb0: _2 = Gt(_1, 0); assert(_2, "assertion failed: x > 0") -> bb1
//   bb1: return
// ---------------------------------------------------------------------------

#[test]
fn fixture_assertion() {
    let func = make_func(
        "assert_positive",
        VerifiableBody {
            locals: vec![local(0, Ty::Unit), named_local(1, "x", Ty::i32()), local(2, Ty::Bool)],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local(1)),
                            const_i32(0),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(2)),
                        expected: true,
                        msg: AssertMessage::Custom("assertion failed: x > 0".to_string()),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
    );

    assert!(func.body.blocks.iter().any(|bb| matches!(
        &bb.terminator,
        Terminator::Assert { expected: true, msg: AssertMessage::Custom(m), .. } if m.contains("x > 0")
    )));

    let vc = make_vc(
        VcKind::Assertion { message: "assertion failed: x > 0".to_string() },
        "assert_positive",
        Formula::Le(
            Box::new(Formula::Var("x".to_string(), Sort::BitVec(32))),
            Box::new(Formula::Int(0)),
        ),
    );
    assert!(matches!(&vc.kind, VcKind::Assertion { message } if message.contains("x > 0")));
}

// ---------------------------------------------------------------------------
// Precondition: fn checked_sqrt(x: f64) -> f64
//   #[requires("x >= 0.0")]
// ---------------------------------------------------------------------------

#[test]
fn fixture_precondition() {
    let func = VerifiableFunction {
        name: "checked_sqrt".to_string(),
        def_path: "fixtures::checked_sqrt".to_string(),
        span: span_at("fixtures.rs", 60),
        body: VerifiableBody {
            locals: vec![local(0, Ty::f64_ty()), named_local(1, "x", Ty::f64_ty())],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::f64::sqrt".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: span_at("fixtures.rs", 62),
                        atomic: None,
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::f64_ty(),
        },
        contracts: vec![Contract {
            kind: ContractKind::Requires,
            span: span_at("fixtures.rs", 60),
            body: "x >= 0.0".to_string(),
        }],
        preconditions: vec![Formula::Ge(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )],
        postconditions: vec![],
        spec: Default::default(),
    };

    assert_eq!(func.contracts.len(), 1);
    assert!(matches!(&func.contracts[0].kind, ContractKind::Requires));

    let vc = make_vc(
        VcKind::Precondition { callee: "std::f64::sqrt".to_string() },
        "checked_sqrt",
        Formula::Lt(Box::new(Formula::Var("x".to_string(), Sort::Int)), Box::new(Formula::Int(0))),
    );
    assert!(matches!(&vc.kind, VcKind::Precondition { callee } if callee == "std::f64::sqrt"));
}

// ---------------------------------------------------------------------------
// Postcondition: fn abs_i32(x: i32) -> i32
//   #[ensures("result >= 0")]
// ---------------------------------------------------------------------------

#[test]
fn fixture_postcondition() {
    let func = VerifiableFunction {
        name: "abs_i32".to_string(),
        def_path: "fixtures::abs_i32".to_string(),
        span: span_at("fixtures.rs", 70),
        body: VerifiableBody {
            locals: vec![local(0, Ty::i32()), named_local(1, "x", Ty::i32()), local(2, Ty::Bool)],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Ge,
                            Operand::Copy(Place::local(1)),
                            const_i32(0),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![Contract {
            kind: ContractKind::Ensures,
            span: span_at("fixtures.rs", 70),
            body: "result >= 0".to_string(),
        }],
        preconditions: vec![],
        postconditions: vec![Formula::Ge(
            Box::new(Formula::Var("result".to_string(), Sort::BitVec(32))),
            Box::new(Formula::Int(0)),
        )],
        spec: Default::default(),
    };

    assert_eq!(func.contracts.len(), 1);
    assert!(matches!(&func.contracts[0].kind, ContractKind::Ensures));

    let vc = make_vc(
        VcKind::Postcondition,
        "abs_i32",
        Formula::Lt(
            Box::new(Formula::Var("result".to_string(), Sort::BitVec(32))),
            Box::new(Formula::Int(0)),
        ),
    );
    assert!(matches!(&vc.kind, VcKind::Postcondition));

    // Path map: 4 blocks, bb3 reachable via both branches
    let path_map = func.body.path_map();
    assert_eq!(path_map.len(), 4);
}

// ---------------------------------------------------------------------------
// Combined: fn safe_divide(a: i32, b: i32) -> i32
//   Exercises: DivisionByZero + ArithmeticOverflow (i32::MIN / -1)
// ---------------------------------------------------------------------------

#[test]
fn fixture_combined_div_overflow_and_divzero() {
    let func = VerifiableFunction {
        name: "safe_divide".to_string(),
        def_path: "fixtures::safe_divide".to_string(),
        span: span_at("fixtures.rs", 80),
        body: VerifiableBody {
            locals: vec![
                local(0, Ty::i32()),
                named_local(1, "a", Ty::i32()),
                named_local(2, "b", Ty::i32()),
                local(3, Ty::Bool),
                local(4, Ty::Bool),
                local(5, Ty::Bool),
            ],
            blocks: vec![
                // bb0: division by zero check
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(2)),
                        expected: false,
                        msg: AssertMessage::DivisionByZero,
                        target: BlockId(1),
                        span: span_at("fixtures.rs", 82),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                // bb1: overflow check (MIN / -1)
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Eq,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Int(i128::from(i32::MIN))),
                            ),
                            span: span_at("fixtures.rs", 83),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Eq,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Int(-1)),
                            ),
                            span: span_at("fixtures.rs", 83),
                        },
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::BitAnd,
                                Operand::Copy(Place::local(3)),
                                Operand::Copy(Place::local(4)),
                            ),
                            span: span_at("fixtures.rs", 83),
                        },
                    ],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(5)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Div),
                        target: BlockId(2),
                        span: span_at("fixtures.rs", 83),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                // bb2: actual division
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span_at("fixtures.rs", 84),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    // Both asserts present
    assert!(func.body.blocks.iter().any(|bb| matches!(
        &bb.terminator,
        Terminator::Assert { msg: AssertMessage::DivisionByZero, .. }
    )));
    assert!(func.body.blocks.iter().any(|bb| matches!(
        &bb.terminator,
        Terminator::Assert { msg: AssertMessage::Overflow(BinOp::Div), .. }
    )));

    // Build both VCs
    let divzero_vc = make_vc(
        VcKind::DivisionByZero,
        "safe_divide",
        Formula::Eq(
            Box::new(Formula::Var("b".to_string(), Sort::BitVec(32))),
            Box::new(Formula::Int(0)),
        ),
    );
    let overflow_vc = make_vc(
        VcKind::ArithmeticOverflow { op: BinOp::Div, operand_tys: (Ty::i32(), Ty::i32()) },
        "safe_divide",
        Formula::And(vec![
            Formula::Eq(
                Box::new(Formula::Var("a".to_string(), Sort::BitVec(32))),
                Box::new(Formula::Int(i128::from(i32::MIN))),
            ),
            Formula::Eq(
                Box::new(Formula::Var("b".to_string(), Sort::BitVec(32))),
                Box::new(Formula::Int(-1)),
            ),
        ]),
    );

    assert!(matches!(&divzero_vc.kind, VcKind::DivisionByZero));
    assert!(matches!(&overflow_vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Div, .. }));

    // Clause discovery: 2 asserts x 2 clauses = 4
    let clauses = func.body.discovered_clauses();
    assert_eq!(clauses.len(), 4);

    // Content hash is deterministic
    let h1 = func.content_hash();
    let h2 = func.content_hash();
    assert_eq!(h1, h2);
    assert_eq!(h1.len(), 64);

    // Serde roundtrip
    let json = serde_json::to_string(&func).expect("serialize");
    let rt: VerifiableFunction = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(rt.name, "safe_divide");
    assert_eq!(rt.body.blocks.len(), 3);
}

// ---------------------------------------------------------------------------
// VcKind serde roundtrip for all error-detection variants
// ---------------------------------------------------------------------------

#[test]
fn all_error_vc_kinds_serde_roundtrip() {
    let kinds = vec![
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) },
        VcKind::ArithmeticOverflow { op: BinOp::Sub, operand_tys: (Ty::u8(), Ty::u8()) },
        VcKind::ArithmeticOverflow { op: BinOp::Mul, operand_tys: (Ty::i64(), Ty::i64()) },
        VcKind::ShiftOverflow { op: BinOp::Shl, operand_ty: Ty::u32(), shift_ty: Ty::u32() },
        VcKind::ShiftOverflow { op: BinOp::Shr, operand_ty: Ty::i16(), shift_ty: Ty::u32() },
        VcKind::DivisionByZero,
        VcKind::RemainderByZero,
        VcKind::IndexOutOfBounds,
        VcKind::SliceBoundsCheck,
        VcKind::CastOverflow { from_ty: Ty::i32(), to_ty: Ty::u8() },
        VcKind::CastOverflow { from_ty: Ty::u64(), to_ty: Ty::i32() },
        VcKind::NegationOverflow { ty: Ty::i8() },
        VcKind::NegationOverflow { ty: Ty::i128() },
        VcKind::Unreachable,
        VcKind::Assertion { message: "x > 0".to_string() },
        VcKind::Precondition { callee: "std::f64::sqrt".to_string() },
        VcKind::Postcondition,
    ];

    for kind in &kinds {
        let vc = make_default_vc(kind.clone(), "roundtrip_test");
        let json = serde_json::to_string(&vc).expect("serialize");
        let rt: VerificationCondition = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(rt.function, "roundtrip_test");
        // Verify the discriminant survived roundtrip
        let rt_json = serde_json::to_string(&rt).expect("re-serialize");
        assert_eq!(json, rt_json, "roundtrip must be byte-exact for {:?}", kind);
    }
}

// ---------------------------------------------------------------------------
// Content hash varies across different error fixtures
// ---------------------------------------------------------------------------

#[test]
fn content_hash_differs_across_fixtures() {
    let overflow_func = make_func(
        "add_i32",
        VerifiableBody {
            locals: vec![
                local(0, Ty::i32()),
                local(1, Ty::i32()),
                local(2, Ty::i32()),
                local(3, Ty::Tuple(vec![Ty::i32(), Ty::Bool])),
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
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
    );

    let divzero_func = make_func(
        "div_i32",
        VerifiableBody {
            locals: vec![local(0, Ty::i32()), local(1, Ty::i32()), local(2, Ty::i32())],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(2)),
                        expected: false,
                        msg: AssertMessage::DivisionByZero,
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
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
                },
            ],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
    );

    assert_ne!(
        overflow_func.content_hash(),
        divzero_func.content_hash(),
        "different error fixture bodies must have different content hashes"
    );
}
