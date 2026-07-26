// Golden test: The Midpoint Bug (pipeline, mock backend)
//
// Exercises the verification pipeline without a real solver:
// VerifiableFunction -> trust_vcgen -> trust-router(mock) -> trust-report
//
// fn get_midpoint(a: usize, b: usize) -> usize { (a + b) / 2 }
//
// This test validates VC generation and pipeline plumbing.
// The ay-specific end-to-end counterpart is tests/full_pipeline.rs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

fn midpoint_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "get_midpoint".to_string(),
        def_path: "midpoint::get_midpoint".to_string(),
        span: SourceSpan {
            file: "examples/midpoint.rs".to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 3,
            col_end: 1,
        },
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
                        unwind: UnwindEdge::Unreachable,
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

#[test]
fn golden_test_midpoint_pipeline() {
    let func = midpoint_function();

    // Generate verification conditions
    let vcs = trust_vcgen::generate_vcs(&func);
    assert!(!vcs.is_empty(), "midpoint must generate VCs");

    // Must have overflow VC
    let has_overflow =
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }));
    assert!(has_overflow, "must detect overflow in checked add");

    // Division by constant 2 is trivially safe — no div-by-zero VC
    let has_div = vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero));
    assert!(!has_div, "div by constant 2 is trivially safe");

    // Route through mock backend — validates pipeline plumbing
    let router = trust_router::Router::new();
    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), vcs.len(), "one result per VC");

    // Build report — validates report generation
    let report = trust_report::build_report("midpoint", &results);
    assert_eq!(report.functions.len(), 1);
    assert_eq!(report.functions[0].function, "get_midpoint");

    let summary = trust_report::format_summary(&report);
    assert!(!summary.is_empty(), "summary must not be empty");
}

#[test]
fn test_identity_function_no_vcs() {
    let func = VerifiableFunction {
        name: "identity".to_string(),
        def_path: "test::identity".to_string(),
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
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
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
        spec: Default::default(),
    };

    let vcs = trust_vcgen::generate_vcs(&func);
    assert!(vcs.is_empty(), "identity function should have no VCs");
}
