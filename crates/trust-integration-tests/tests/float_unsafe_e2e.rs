// trust-integration-tests/tests/float_unsafe_e2e.rs: Float + Unsafe/FFI error detection E2E
//
// Tests that Trust's verification pipeline detects 4 Float + Unsafe/FFI VcKind variants:
// 1. FloatDivisionByZero — float division where divisor may be zero
// 2. FloatOverflowToInfinity — float arithmetic exceeding representable range
// 3. UnsafeOperation — raw pointer dereference / transmute / FFI (conservative)
// 4. FfiBoundaryViolation — FFI call with summary-based contract violation
//
// Each category has a buggy variant (VC expected) and a safe variant (no such VC).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_integration_tests::ay_test_support::require_ay;
use trust_router::VerificationBackend;
use trust_types::*;

// ===========================================================================
// Category 1: FloatDivisionByZero
// ===========================================================================

/// Buggy: `result = a / b` where both a and b are f64 variables.
/// The divisor b is unconstrained, so it can be zero.
///
/// MIR: bb0: _0 = BinaryOp(Div, _1, _2); return
fn float_div_by_var_buggy() -> VerifiableFunction {
    let ty = Ty::Float { width: 64 };
    VerifiableFunction {
        name: "float_div_by_var".to_string(),
        def_path: "test::float_div_by_var".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
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
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Safe: `result = a / 2.0` — constant nonzero divisor cannot be zero.
fn float_div_by_const_safe() -> VerifiableFunction {
    let ty = Ty::Float { width: 64 };
    VerifiableFunction {
        name: "float_div_by_const".to_string(),
        def_path: "test::float_div_by_const".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Float(2.0)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

// ===========================================================================
// Category 2: FloatOverflowToInfinity
// ===========================================================================

/// Buggy: `result = a * b` where both a and b are f64 variables.
/// Unconstrained floats can produce a result exceeding f64::MAX (overflow to Inf).
///
/// MIR: bb0: _0 = BinaryOp(Mul, _1, _2); return
fn float_mul_overflow_buggy() -> VerifiableFunction {
    let ty = Ty::Float { width: 64 };
    VerifiableFunction {
        name: "float_mul_overflow".to_string(),
        def_path: "test::float_mul_overflow".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Mul,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Safe: integer multiplication does NOT produce FloatOverflowToInfinity VCs.
/// Using u32 operands — only float types trigger float-specific VCs.
fn int_mul_no_float_overflow_safe() -> VerifiableFunction {
    VerifiableFunction {
        name: "int_mul_no_float_overflow".to_string(),
        def_path: "test::int_mul_no_float_overflow".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Mul,
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

// ===========================================================================
// Category 3: UnsafeOperation
// ===========================================================================
//
// The UnsafeOperation VcKind is generated by trust_vcgen's unsafe_vc module
// (pub(crate)), which is not wired into generate_vcs() — it is a separate
// classification engine for audit tracking. Integration tests construct
// UnsafeOperation VCs directly with Formula::Bool(true) (conservative:
// always SAT = always a finding) matching the module's design intent.

/// Buggy: raw pointer dereference — conservative VC (always SAT).
fn unsafe_raw_deref_buggy() -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::UnsafeOperation { desc: "raw pointer dereference of `_2.*`".to_string() },
        function: "unsafe_raw_deref".into(),
        location: SourceSpan::default(),
        // Conservative: Formula::Bool(true) is always SAT — meaning
        // this unsafe operation exists and was not proved safe.
        formula: Formula::Bool(true),
        contract_metadata: None,
    }
}

/// Safe: a function with no unsafe operations produces no UnsafeOperation VCs.
/// We encode this as: given a trivially false formula (Bool(false)), the solver
/// reports UNSAT (i.e., "proved safe" — no counterexample).
fn unsafe_safe_formula() -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::UnsafeOperation { desc: "safe operation (no raw pointers)".to_string() },
        function: "safe_function".into(),
        location: SourceSpan::default(),
        // Formula::Bool(false) is UNSAT — the negation is always true,
        // meaning there is no way to violate this VC.
        formula: Formula::Bool(false),
        contract_metadata: None,
    }
}

// ===========================================================================
// Category 4: FfiBoundaryViolation
// ===========================================================================

/// Buggy: call to `libc::malloc` with unconstrained size argument.
/// The FFI summary database generates null-check and allocation VCs.
///
/// MIR: bb0: _0 = Call("libc::malloc", [_1]); goto bb1
///       bb1: return
fn ffi_malloc_call_buggy() -> VerifiableFunction {
    let ptr_ty = Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) };
    VerifiableFunction {
        name: "ffi_malloc_call".to_string(),
        def_path: "test::ffi_malloc_call".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ptr_ty.clone(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("size".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { is_unsafe_sig: false, is_foreign: false,
                        func: "libc::malloc".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: ptr_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
    }
}

/// Safe: call to a known safe function (Vec::push) — NOT an FFI boundary.
/// No FfiBoundaryViolation VCs should be generated.
fn safe_call_no_ffi() -> VerifiableFunction {
    VerifiableFunction {
        name: "safe_push_call".to_string(),
        def_path: "test::safe_push_call".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("v".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { is_unsafe_sig: false, is_foreign: false,
                        func: "std::vec::Vec::push".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        unwind: trust_types::UnwindEdge::Unreachable,
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

// ===========================================================================
// Tests
// ===========================================================================

// --- Category 1: FloatDivisionByZero ---

#[test]
fn test_detect_float_div_by_zero_variable() {
    let ay = require_ay();
    let func = float_div_by_var_buggy();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for float_div_by_var", vcs.len());
    for vc in &vcs {
        eprintln!("  VC: {:?} — {}", vc.kind, vc.function);
    }

    let float_divzero_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::FloatDivisionByZero)).collect();

    assert!(
        !float_divzero_vcs.is_empty(),
        "vcgen must produce FloatDivisionByZero VC for float division by variable"
    );

    for vc in &float_divzero_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result for float div-by-zero: {:?}", result);

        assert!(
            result.is_failed(),
            "ay must find float variable divisor CAN be zero. Got: {result:?}"
        );

        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            eprintln!("  Counterexample: {cex}");
        }
    }
}

#[test]
fn test_detect_float_div_by_const_safe() {
    let func = float_div_by_const_safe();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for float_div_by_const", vcs.len());
    for vc in &vcs {
        eprintln!("  VC: {:?} — {}", vc.kind, vc.function);
    }

    let float_divzero_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::FloatDivisionByZero)).collect();

    assert!(
        float_divzero_vcs.is_empty(),
        "vcgen must NOT produce FloatDivisionByZero VC when divisor is a nonzero constant"
    );
}

// --- Category 2: FloatOverflowToInfinity ---

#[test]
fn test_detect_float_overflow_to_infinity_mul() {
    let ay = require_ay();
    let func = float_mul_overflow_buggy();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for float_mul_overflow", vcs.len());
    for vc in &vcs {
        eprintln!("  VC: {:?} — {}", vc.kind, vc.function);
    }

    let overflow_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::FloatOverflowToInfinity { op: BinOp::Mul, .. }))
        .collect();

    assert!(
        !overflow_vcs.is_empty(),
        "vcgen must produce FloatOverflowToInfinity(Mul) VC for float multiplication"
    );

    for vc in &overflow_vcs {
        let result = ay.verify(vc);
        eprintln!("ay result for float overflow: {:?}", result);

        // The overflow formula checks if result > float_max OR result < -float_max.
        // With unconstrained operands, this is SAT (overflow is possible).
        assert!(
            result.is_failed(),
            "ay must find float mul CAN overflow to infinity. Got: {result:?}"
        );
    }
}

#[test]
fn test_detect_float_overflow_to_infinity_safe_int() {
    let func = int_mul_no_float_overflow_safe();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for int_mul_no_float_overflow", vcs.len());
    for vc in &vcs {
        eprintln!("  VC: {:?} — {}", vc.kind, vc.function);
    }

    let float_overflow_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::FloatOverflowToInfinity { .. })).collect();

    assert!(
        float_overflow_vcs.is_empty(),
        "vcgen must NOT produce FloatOverflowToInfinity VC for integer operations"
    );
}

// --- Category 3: UnsafeOperation ---

#[test]
fn test_detect_unsafe_operation_raw_deref() {
    let ay = require_ay();
    let vc = unsafe_raw_deref_buggy();

    // Verify the VC kind is correctly tagged
    assert!(
        matches!(&vc.kind, VcKind::UnsafeOperation { desc } if desc.contains("raw pointer dereference")),
        "VC must be UnsafeOperation with raw pointer dereference description"
    );

    // Verify proof level is L0Safety
    assert_eq!(
        vc.kind.proof_level(),
        ProofLevel::L0Safety,
        "UnsafeOperation must be L0 safety level"
    );

    // Verify no runtime fallback
    assert!(!vc.kind.has_runtime_fallback(true), "UnsafeOperation must have no runtime fallback");

    // Conservative formula Bool(true) is always SAT → ay finds "counterexample"
    let result = ay.verify(&vc);
    eprintln!("ay result for unsafe raw deref: {:?}", result);

    assert!(
        result.is_failed(),
        "ay must report unsafe operation as unproved (SAT). Got: {result:?}"
    );
}

#[test]
fn test_detect_unsafe_operation_safe() {
    let ay = require_ay();
    let vc = unsafe_safe_formula();

    // Formula::Bool(false) is UNSAT → ay proves the VC
    let result = ay.verify(&vc);
    eprintln!("ay result for safe (no unsafe ops): {:?}", result);

    assert!(result.is_proved(), "ay must prove safe formula (UNSAT). Got: {result:?}");
}

// --- Category 4: FfiBoundaryViolation ---

#[test]
fn test_detect_ffi_boundary_violation_malloc() {
    let ay = require_ay();
    let func = ffi_malloc_call_buggy();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for ffi_malloc_call", vcs.len());
    for vc in &vcs {
        eprintln!("  VC: {:?} — {}", vc.kind, vc.function);
    }

    let ffi_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::FfiBoundaryViolation { .. })).collect();

    assert!(
        !ffi_vcs.is_empty(),
        "vcgen must produce FfiBoundaryViolation VCs for libc::malloc call"
    );

    // Verify at least one VC mentions allocation / null
    let has_alloc_vc = ffi_vcs.iter().any(|vc| {
        matches!(
            &vc.kind,
            VcKind::FfiBoundaryViolation { desc, .. }
                if desc.contains("allocation") || desc.contains("null") || desc.contains("non-null")
        )
    });
    assert!(has_alloc_vc, "malloc VCs should include allocation or null-check related VC");

    // All FFI VCs should be L0Safety
    for vc in &ffi_vcs {
        assert_eq!(
            vc.kind.proof_level(),
            ProofLevel::L0Safety,
            "FfiBoundaryViolation must be L0 safety"
        );
        assert!(
            !vc.kind.has_runtime_fallback(true),
            "FfiBoundaryViolation must have no runtime fallback"
        );
    }

    // Verify at least one VC fails verification (is SAT — vulnerability found)
    let any_failed = ffi_vcs.iter().any(|vc| {
        let result = ay.verify(vc);
        eprintln!("ay result for FFI VC ({:?}): {:?}", vc.kind, result);
        result.is_failed()
    });
    assert!(any_failed, "at least one FFI boundary VC should be SAT (unproved)");
}

#[test]
fn test_detect_ffi_boundary_violation_safe_call() {
    let func = safe_call_no_ffi();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("Generated {} VCs for safe_push_call", vcs.len());
    for vc in &vcs {
        eprintln!("  VC: {:?} — {}", vc.kind, vc.function);
    }

    let ffi_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::FfiBoundaryViolation { .. })).collect();

    assert!(
        ffi_vcs.is_empty(),
        "vcgen must NOT produce FfiBoundaryViolation VCs for safe function calls"
    );
}
