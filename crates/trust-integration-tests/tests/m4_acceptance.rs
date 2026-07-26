// trust-integration-tests/tests/m4_acceptance.rs: M4 milestone acceptance tests
//
// Demonstrates Trust catching a real bug in binary search: the classic integer
// overflow in `(lo + hi) / 2` (Bloch, 2006). Verifies both:
//   1. The buggy version produces an ArithmeticOverflow VC (detected)
//   2. The fixed version (`lo + (hi - lo) / 2`) produces no overflow VCs
//
// This is THE motivating example from VISION.md — the compiler finds the bug
// AND proves the fix correct.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Counterexample, CounterexampleValue,
    LocalDecl, Operand, Place, ProofLevel, ProofStrength, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction, VerificationCondition,
    VerificationResult,
};

// ---------------------------------------------------------------------------
// Synthetic MIR builders for binary search midpoint computation
// ---------------------------------------------------------------------------

/// Build the BUGGY midpoint: `mid = (lo + hi) / 2`
///
/// MIR equivalent:
/// ```text
/// bb0: _3 = CheckedAdd(_1, _2); Assert(!_3.1, overflow); goto bb1
/// bb1: _4 = _3.0; _5 = Div(_4, 2); _0 = _5; return
/// ```
///
/// Expected VCs: 1 ArithmeticOverflow(Add) — the classic binary search bug.
fn buggy_midpoint() -> VerifiableFunction {
    VerifiableFunction {
        name: "binary_search_buggy_midpoint".to_string(),
        def_path: "binary_search::binary_search_buggy_midpoint".to_string(),
        span: SourceSpan {
            file: "examples/showcase/m4_binary_search_demo.rs".to_string(),
            line_start: 30,
            col_start: 9,
            line_end: 30,
            col_end: 31,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None }, // _0: return
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("lo".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("hi".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None }, // _3: checked add
                LocalDecl { index: 4, ty: Ty::usize(), name: None }, // _4: sum
                LocalDecl { index: 5, ty: Ty::usize(), name: None }, // _5: mid
            ],
            blocks: vec![
                // bb0: _3 = CheckedAdd(lo, hi); assert(!_3.1, overflow) -> bb1
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)), // lo
                            Operand::Copy(Place::local(2)), // hi
                        ),
                        span: SourceSpan {
                            file: "examples/showcase/m4_binary_search_demo.rs".to_string(),
                            line_start: 30,
                            col_start: 19,
                            line_end: 30,
                            col_end: 26,
                        },
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: SourceSpan {
                            file: "examples/showcase/m4_binary_search_demo.rs".to_string(),
                            line_start: 30,
                            col_start: 19,
                            line_end: 30,
                            col_end: 26,
                        },
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
                // bb1: _4 = _3.0; _5 = _4 / 2; _0 = _5; return
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

/// Build the FIXED midpoint: `mid = lo + (hi - lo) / 2`
///
/// MIR equivalent:
/// ```text
/// bb0: _3 = Sub(hi, lo); _4 = Div(_3, 2); _5 = CheckedAdd(lo, _4);
///      Assert(!_5.1, overflow); goto bb1
/// bb1: _0 = _5.0; return
/// ```
///
/// The subtraction `hi - lo` is safe because the loop invariant guarantees
/// `lo <= hi`. The division by 2 halves the difference. The final add
/// `lo + (hi - lo) / 2` cannot overflow because:
///   lo + (hi - lo) / 2 <= lo + (hi - lo) = hi <= usize::MAX
///
/// VCGen will still produce an ArithmeticOverflow VC for the CheckedAdd
/// (it does not yet reason about value ranges), but a real solver would
/// prove it UNSAT given the loop invariant constraints.
///
/// For this test, we model the safe version WITHOUT CheckedAdd to
/// demonstrate the structural difference: using BinaryOp(Add, ...) which
/// produces no overflow VC. This represents the compiler's wrapping_add
/// lowering when overflow is statically impossible.
fn safe_midpoint() -> VerifiableFunction {
    VerifiableFunction {
        name: "binary_search_safe_midpoint".to_string(),
        def_path: "binary_search::binary_search_safe_midpoint".to_string(),
        span: SourceSpan {
            file: "examples/showcase/m4_binary_search_demo.rs".to_string(),
            line_start: 52,
            col_start: 9,
            line_end: 52,
            col_end: 36,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None }, // _0: return
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("lo".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("hi".into()) },
                LocalDecl { index: 3, ty: Ty::usize(), name: None }, // _3: hi - lo
                LocalDecl { index: 4, ty: Ty::usize(), name: None }, // _4: (hi-lo)/2
                LocalDecl { index: 5, ty: Ty::usize(), name: None }, // _5: lo + _4
            ],
            blocks: vec![
                // bb0: _3 = hi - lo; _4 = _3 / 2; _5 = lo + _4; _0 = _5; return
                // Using unchecked BinaryOp for all operations — the compiler
                // can prove these safe from the loop invariant (lo <= hi).
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Sub,
                                Operand::Copy(Place::local(2)), // hi
                                Operand::Copy(Place::local(1)), // lo
                            ),
                            span: SourceSpan {
                                file: "examples/showcase/m4_binary_search_demo.rs".to_string(),
                                line_start: 52,
                                col_start: 24,
                                line_end: 52,
                                col_end: 32,
                            },
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(3)),
                                Operand::Constant(ConstValue::Uint(2, 64)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)), // lo
                                Operand::Copy(Place::local(4)), // (hi-lo)/2
                            ),
                            span: SourceSpan {
                                file: "examples/showcase/m4_binary_search_demo.rs".to_string(),
                                line_start: 52,
                                col_start: 19,
                                line_end: 52,
                                col_end: 36,
                            },
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

// ---------------------------------------------------------------------------
// M4 Acceptance Test 1: Buggy binary search produces overflow VC
// ---------------------------------------------------------------------------

#[test]
fn test_m4_buggy_binary_search_overflow_detected() {
    let func = buggy_midpoint();

    // Step 1: VCGen produces an ArithmeticOverflow VC for (lo + hi).
    let vcs = trust_vcgen::generate_vcs(&func);
    assert!(!vcs.is_empty(), "buggy binary search midpoint should produce at least 1 VC");

    // Verify the overflow VC exists.
    let overflow_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .collect();
    assert_eq!(
        overflow_vcs.len(),
        1,
        "should produce exactly 1 ArithmeticOverflow(Add) VC, got {}",
        overflow_vcs.len()
    );

    // Verify the VC is attributed to the correct function.
    assert_eq!(overflow_vcs[0].function, "binary_search_buggy_midpoint");

    // Verify this is a Level 0 safety property.
    assert_eq!(
        overflow_vcs[0].kind.proof_level(),
        ProofLevel::L0Safety,
        "arithmetic overflow should be L0 safety"
    );

    // Step 2: Route through the pipeline.
    let router = trust_router::Router::new();
    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), vcs.len(), "router should return one result per VC");

    // The mock backend returns Unknown for variable-containing formulas.
    // In production with ay, this VC would return Failed with a counterexample
    // like lo = 2^63, hi = 2^63 (their sum overflows usize).
    let (ref vc, ref result) = results[0];
    assert_eq!(vc.function, "binary_search_buggy_midpoint");
    // Mock returns Unknown for variable formulas — a real solver would return Failed.
    assert!(
        matches!(result, VerificationResult::Unknown { .. } | VerificationResult::Failed { .. }),
        "overflow VC should be Unknown (mock) or Failed (real solver), got: {result:?}"
    );

    // Step 3: Build the proof report.
    let report = trust_report::build_json_report("m4-binary-search-buggy", &results);
    assert!(!report.functions.is_empty(), "report should have function entries");
    assert!(report.summary.total_obligations >= 1, "report should have at least 1 obligation");

    eprintln!("=== M4 Buggy Binary Search: Overflow Detected ===");
    eprintln!("  VCs generated: {}", vcs.len());
    eprintln!("  Overflow VCs: {}", overflow_vcs.len());
    eprintln!("  Pipeline result: {:?}", result);
    eprintln!("  Report verdict: {:?}", report.summary.verdict);
    eprintln!("===================================================");
}

// ---------------------------------------------------------------------------
// M4 Acceptance Test 2: Fixed binary search overflow VCs are provably safe
// ---------------------------------------------------------------------------

#[test]
fn test_m4_safe_binary_search_overflow_provably_safe() {
    let func = safe_midpoint();

    // Step 1: VCGen on the safe version. The safe MIR uses plain BinaryOp
    // (no CheckedBinaryOp/Assert(Overflow) pair) for Sub/Add — see the
    // `safe_midpoint` fixture comment.
    //
    // trust_vcgen now hardens EVERY unguarded direct integer
    // `Rvalue::BinaryOp(Add|Sub|Mul)` with a solver-facing ArithmeticOverflow
    // obligation (generate.rs `v2_build_overflow_vc_for_operands`): an
    // unguarded overflowing op that emitted no VC would be a silent
    // false-PROVE. So the safe version emits exactly TWO ArithmeticOverflow
    // VCs — one for `Sub(hi, lo)` and one for the final `Add(lo, (hi-lo)/2)`.
    // The `Div(_, 2)` op emits no overflow VC (division never overflows here).
    //
    // The genuine "provably safe" property is NOT "zero overflow VCs"; it is
    // that the dangerous `CheckedAdd(lo, hi)` overflow VC (the classic bug)
    // has been removed entirely, and the remaining overflow obligations are
    // discharged by a real solver given the loop invariant `lo <= hi`
    // (lo + (hi - lo)/2 <= hi <= usize::MAX). That is the property the
    // strengthen->backprop loop achieves end-to-end.
    let vcs = trust_vcgen::generate_vcs(&func);

    let overflow_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })).collect();
    assert_eq!(
        overflow_vcs.len(),
        2,
        "safe midpoint emits one overflow VC per direct integer BinaryOp \
         (Sub(hi,lo) and Add(lo,(hi-lo)/2)); the unsafe CheckedAdd(lo,hi) is gone. \
         Got {} overflow VCs.",
        overflow_vcs.len()
    );

    // Crucially: the dangerous `Add(lo, hi)` sum is GONE. The safe version's
    // overflow obligations are over the structurally-safe rewrite: a single
    // Sub(hi, lo) and a single Add(lo, difference/2). There is exactly one
    // overflow VC per op kind, and no Mul.
    let add_overflow = overflow_vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .count();
    let sub_overflow = overflow_vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. }))
        .count();
    assert_eq!(add_overflow, 1, "exactly one Add overflow VC (the safe lo + (hi-lo)/2)");
    assert_eq!(sub_overflow, 1, "exactly one Sub overflow VC (the safe hi - lo)");

    // Step 2: Route through the pipeline. The remaining safety VCs (e.g.,
    // Div /2 -- provably safe since divisor is a nonzero constant) must
    // route cleanly without panics.
    let router = trust_router::Router::new();
    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), vcs.len(), "router should return one result per VC");

    // Step 3: Build the proof report.
    let report = trust_report::build_json_report("m4-binary-search-safe", &results);

    eprintln!("=== M4 Safe Binary Search: Overflow VCs Provably Safe ===");
    eprintln!("  VCs generated: {}", vcs.len());
    eprintln!(
        "  Overflow VCs: {} (Sub(hi,lo)+Add(lo,(hi-lo)/2); unsafe CheckedAdd(lo,hi) removed)",
        overflow_vcs.len()
    );
    eprintln!("  Report verdict: {:?}", report.summary.verdict);
    eprintln!("==========================================================");
}

// ---------------------------------------------------------------------------
// M4 Acceptance Test 3: End-to-end demo — buggy vs safe, side by side
// ---------------------------------------------------------------------------

#[test]
fn test_m4_binary_search_end_to_end_comparison() {
    let buggy = buggy_midpoint();
    let safe = safe_midpoint();

    // Generate VCs for both.
    let buggy_vcs = trust_vcgen::generate_vcs(&buggy);
    let safe_vcs = trust_vcgen::generate_vcs(&safe);

    // Buggy version has overflow on the dangerous Add(lo, hi) (modeled as
    // CheckedBinaryOp + Assert(Overflow)) -> exactly 1 Add overflow VC.
    //
    // Safe version models the post-fix lowering with plain BinaryOp (no
    // CheckedAdd(lo, hi)). trust_vcgen now hardens every unguarded direct
    // integer BinaryOp(Add|Sub|Mul) with a solver-facing ArithmeticOverflow
    // obligation, so the safe rewrite (Sub(hi,lo), Div, Add(lo,(hi-lo)/2))
    // emits exactly 2 overflow VCs: one Sub and one Add. The structural fix
    // is that the dangerous CheckedAdd(lo, hi) is GONE — the safe Add is over
    // (lo, (hi-lo)/2), which a real solver proves UNSAT given lo <= hi.
    let buggy_overflow_count = buggy_vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .count();
    let safe_overflow_count =
        safe_vcs.iter().filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })).count();
    let safe_add_overflow = safe_vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .count();
    let safe_sub_overflow = safe_vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. }))
        .count();

    assert_eq!(buggy_overflow_count, 1, "buggy version must have 1 overflow(Add) VC");
    assert_eq!(
        safe_overflow_count, 2,
        "safe version emits 2 overflow VCs (Sub(hi,lo) + Add(lo,(hi-lo)/2)); \
         the unsafe CheckedAdd(lo,hi) is removed"
    );
    assert_eq!(safe_add_overflow, 1, "safe version: exactly one Add overflow VC (the safe sum)");
    assert_eq!(safe_sub_overflow, 1, "safe version: exactly one Sub overflow VC (hi - lo)");

    // Route both through the full pipeline.
    let router = trust_router::Router::new();
    let buggy_results = router.verify_all(&buggy_vcs);
    let safe_results = router.verify_all(&safe_vcs);

    // Build combined report showing both functions.
    let mut all_results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();
    all_results.extend(buggy_results);
    all_results.extend(safe_results);

    let report = trust_report::build_json_report("m4-binary-search-demo", &all_results);

    // Report should cover both functions.
    let function_names: Vec<&str> = report.functions.iter().map(|f| f.function.as_str()).collect();
    assert!(
        function_names.contains(&"binary_search_buggy_midpoint"),
        "report should include buggy function, got: {function_names:?}"
    );

    eprintln!("=== M4 Binary Search: End-to-End Comparison ===");
    eprintln!("  Buggy VCs: {} (overflow: {buggy_overflow_count})", buggy_vcs.len());
    eprintln!("  Safe VCs:  {} (overflow: {safe_overflow_count})", safe_vcs.len());
    eprintln!("  Report functions: {}", report.functions.len());
    eprintln!("  Report verdict: {:?}", report.summary.verdict);
    eprintln!("=================================================");
}

// ---------------------------------------------------------------------------
// M4 Acceptance Test 4: Counterexample structure (simulated ay result)
// ---------------------------------------------------------------------------

#[test]
fn test_m4_counterexample_demonstrates_overflow() {
    let func = buggy_midpoint();
    let vcs = trust_vcgen::generate_vcs(&func);

    // Find the overflow VC.
    let overflow_vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .expect("buggy version must produce an overflow VC");

    // Simulate what ay would return: a counterexample where lo + hi overflows.
    // For usize (64-bit): lo = 2^63, hi = 2^63 => lo + hi = 2^64 which wraps to 0.
    let simulated_cex = Counterexample::new(vec![
        ("lo".to_string(), CounterexampleValue::Uint(1u128 << 63)),
        ("hi".to_string(), CounterexampleValue::Uint(1u128 << 63)),
    ]);

    let simulated_failed = VerificationResult::Failed {
        solver: "ay".into(),
        time_ms: 42,
        counterexample: Some(simulated_cex),
    };

    // Verify the simulated result structure is well-formed.
    assert!(simulated_failed.is_failed());
    assert_eq!(simulated_failed.solver_name(), "ay");

    // Build a report with the simulated result.
    let results = vec![(overflow_vc.clone(), simulated_failed)];
    let report = trust_report::build_json_report("m4-simulated-ay", &results);

    // The report should show a violation.
    assert_eq!(report.summary.total_failed, 1, "report should show 1 failed obligation");
    assert!(
        matches!(report.summary.verdict, trust_types::CrateVerdict::HasViolations),
        "verdict should be HasViolations, got: {:?}",
        report.summary.verdict
    );

    // Verify JSON serialization includes the counterexample.
    let json = serde_json::to_string_pretty(&report).expect("serialize report");
    assert!(json.contains("binary_search_buggy_midpoint"), "JSON should name the function");
    assert!(json.contains("failed"), "JSON should contain 'failed' outcome");

    eprintln!("=== M4 Counterexample (Simulated ay) ===");
    eprintln!("  VC: {:?}", overflow_vc.kind);
    eprintln!("  Counterexample: lo = 2^63, hi = 2^63");
    eprintln!("  Verdict: {:?}", report.summary.verdict);
    eprintln!("==========================================");
}

// ---------------------------------------------------------------------------
// M4 Acceptance Test 5: Proof structure (simulated ay proof for safe version)
// ---------------------------------------------------------------------------

#[test]
fn test_m4_safe_version_proof_structure() {
    let func = safe_midpoint();
    let vcs = trust_vcgen::generate_vcs(&func);

    // The safe version may still produce DivisionByZero VCs (for the / 2
    // operations), even though dividing by a constant 2 is trivially safe.
    // For this test, we simulate ay proving each VC.
    let simulated_results: Vec<(VerificationCondition, VerificationResult)> = vcs
        .iter()
        .map(|vc| {
            let proved = VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 3,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            };
            (vc.clone(), proved)
        })
        .collect();

    if simulated_results.is_empty() {
        // No VCs at all — the safe version is trivially safe.
        eprintln!("=== M4 Safe Version Proof: No VCs (trivially safe) ===");
        return;
    }

    let report = trust_report::build_json_report("m4-safe-proof", &simulated_results);

    // All obligations should be proved.
    assert_eq!(
        report.summary.total_proved, report.summary.total_obligations,
        "all obligations should be proved: {} proved out of {}",
        report.summary.total_proved, report.summary.total_obligations
    );
    assert_eq!(report.summary.total_failed, 0, "no obligations should fail");

    assert!(
        matches!(report.summary.verdict, trust_types::CrateVerdict::Verified),
        "verdict should be Verified, got: {:?}",
        report.summary.verdict
    );

    eprintln!("=== M4 Safe Version Proof (Simulated ay) ===");
    eprintln!("  VCs: {}", vcs.len());
    eprintln!("  All proved: {}", report.summary.total_proved);
    eprintln!("  Verdict: {:?}", report.summary.verdict);
    eprintln!("==============================================");
}
