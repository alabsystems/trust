//! trust-integration-tests: Cross-crate integration tests for the Trust verification pipeline
//!
//! Provides shared test fixtures (synthetic MIR functions) used by integration
//! tests in the `tests/` directory. No production code lives here.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// Trust: Allow std HashMap — FxHash lint only applies to compiler internals
#![allow(rustc::default_hash_types, rustc::potential_query_instability)]
// dead_code audit: crate-level suppression removed

#[cfg(test)]
pub mod framework;
pub mod ay_test_support;
pub mod clean_test_support;
pub mod extracted;

use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Contract, ContractKind, Formula,
    LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan, Statement, Terminator, Ty,
    VerifiableBody, VerifiableFunction,
};

/// Build a synthetic `get_midpoint(a: usize, b: usize) -> usize` function.
///
/// MIR equivalent:
/// ```text
/// bb0: _3 = CheckedAdd(_1, _2); Assert(!_3.1, overflow); goto bb1
/// bb1: _4 = _3.0; _5 = Div(_4, 2); _0 = _5; return
/// ```
///
/// Expected VCs: 1 arithmetic overflow (Add).
pub fn midpoint_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "get_midpoint".to_string(),
        def_path: "midpoint::get_midpoint".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                LocalDecl { index: 4, ty: Ty::usize(), name: None },
                LocalDecl { index: 5, ty: Ty::usize(), name: None },
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
                        unwind: trust_types::UnwindEdge::Unreachable,
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
                                Operand::Constant(ConstValue::Uint(2, 64)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Build a synthetic `divide(x: u32, y: u32) -> u32` function.
///
/// MIR equivalent:
/// ```text
/// bb0: _3 = Div(_1, _2); _0 = _3; return
/// ```
///
/// Expected VCs: 1 DivisionByZero.
pub fn division_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "divide".to_string(),
        def_path: "arith::divide".to_string(),
        span: SourceSpan {
            file: "src/arith.rs".to_string(),
            line_start: 10,
            col_start: 1,
            line_end: 12,
            col_end: 2,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan {
                            file: "src/arith.rs".to_string(),
                            line_start: 11,
                            col_start: 5,
                            line_end: 11,
                            col_end: 10,
                        },
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
        spec: Default::default(),
    }
}

/// Build a synthetic `lookup(arr: [u32; 10], idx: usize) -> u32` function.
///
/// MIR equivalent:
/// ```text
/// bb0: _3 = _1[_2]; _0 = _3; return
/// ```
///
/// Expected VCs: 1 IndexOutOfBounds.
pub fn array_access_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "lookup".to_string(),
        def_path: "container::lookup".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::u32()), len: 10 },
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
        spec: Default::default(),
    }
}

/// Build a synthetic function with a postcondition contract.
///
/// `safe_add(a: u32, b: u32) -> u32` with `ensures result <= u32::MAX`.
///
/// Expected VCs: 1 arithmetic overflow (Add) + 1 Postcondition.
pub fn contract_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "safe_add".to_string(),
        def_path: "arith::safe_add".to_string(),
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
                        span: SourceSpan::default(),
                        unwind: trust_types::UnwindEdge::Unreachable,
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
        contracts: vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "result <= 4294967295".to_string(),
        }],
        preconditions: vec![],
        postconditions: vec![Formula::Le(
            Box::new(Formula::Var("result".into(), trust_types::Sort::Int)),
            Box::new(Formula::Int(4_294_967_295)),
        )],
        spec: Default::default(),
    }
}

/// Build a function with only a Return terminator and no operations.
///
/// `noop() -> ()` — should produce 0 VCs.
pub fn noop_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "noop".to_string(),
        def_path: "misc::noop".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}
