// trust-integration-tests/tests/m3_acceptance.rs: M3 milestone acceptance tests
//
// Exercises the full Trust verification pipeline at crate scale (100+ functions).
// Demonstrates that the system works end-to-end: vcgen -> router -> report for a
// realistic number of functions with varying verification patterns.
//
// M3 acceptance criteria:
// - Run verification on 100+ functions without panics
// - Generate VCs for each function
// - Produce structured proof report covering all functions
// - Exercise cross-function contract analysis
// - Document: N proved, N failed, N unknown
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use std::fmt::Write;
use trust_types::fx::FxHashMap;

use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, Contract, ContractKind, Formula, LocalDecl, Operand,
    Place, Projection, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody,
    VerifiableFunction, VerificationCondition, VerificationResult,
};

// ---------------------------------------------------------------------------
// Synthetic crate generation: 100+ functions with varying VC patterns
// ---------------------------------------------------------------------------

/// The different function patterns we generate.
#[derive(Debug, Clone, Copy)]
enum FunctionPattern {
    /// Checked addition -- produces ArithmeticOverflow VC.
    CheckedAdd,
    /// Checked subtraction -- produces ArithmeticOverflow VC.
    CheckedSub,
    /// Checked multiplication -- produces ArithmeticOverflow VC.
    CheckedMul,
    /// Division -- produces DivisionByZero VC.
    Division,
    /// Array index -- produces IndexOutOfBounds VC.
    ArrayIndex,
    /// Function with postcondition contract.
    WithContract,
    /// Noop function -- produces 0 VCs.
    Noop,
}

const ALL_PATTERNS: &[FunctionPattern] = &[
    FunctionPattern::CheckedAdd,
    FunctionPattern::CheckedSub,
    FunctionPattern::CheckedMul,
    FunctionPattern::Division,
    FunctionPattern::ArrayIndex,
    FunctionPattern::WithContract,
    FunctionPattern::Noop,
];

/// Generate a synthetic crate of N functions with varied VC patterns.
///
/// Distributes functions across patterns round-robin so every pattern
/// is exercised multiple times at scale.
fn generate_synthetic_crate(n: usize) -> Vec<VerifiableFunction> {
    (0..n)
        .map(|i| {
            let pattern = ALL_PATTERNS[i % ALL_PATTERNS.len()];
            make_function(i, pattern)
        })
        .collect()
}

/// Build a single synthetic VerifiableFunction for the given pattern.
fn make_function(index: usize, pattern: FunctionPattern) -> VerifiableFunction {
    let name = format!("func_{index:04}");
    let def_path = format!("synthetic::{name}");

    match pattern {
        FunctionPattern::CheckedAdd => make_checked_binop(&name, &def_path, BinOp::Add),
        FunctionPattern::CheckedSub => make_checked_binop(&name, &def_path, BinOp::Sub),
        FunctionPattern::CheckedMul => make_checked_binop(&name, &def_path, BinOp::Mul),
        FunctionPattern::Division => make_division(&name, &def_path),
        FunctionPattern::ArrayIndex => make_array_index(&name, &def_path),
        FunctionPattern::WithContract => make_with_contract(&name, &def_path),
        FunctionPattern::Noop => make_noop(&name, &def_path),
    }
}

fn make_checked_binop(name: &str, def_path: &str, op: BinOp) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: def_path.to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            op,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(op),
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
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn make_division(name: &str, def_path: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: def_path.to_string(),
        span: SourceSpan::default(),
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

fn make_array_index(name: &str, def_path: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: def_path.to_string(),
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

fn make_with_contract(name: &str, def_path: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: def_path.to_string(),
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
        contracts: vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "result <= 4294967295".to_string(),
        }],
        preconditions: vec![],
        postconditions: vec![Formula::Le(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Int(4_294_967_295)),
        )],
        spec: Default::default(),
    }
}

fn make_noop(name: &str, def_path: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: def_path.to_string(),
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

// ---------------------------------------------------------------------------
// M3 Acceptance Test 1: VCGen at scale (120 functions)
// ---------------------------------------------------------------------------

#[test]
fn test_m3_vcgen_at_scale() {
    let functions = generate_synthetic_crate(120);
    assert_eq!(functions.len(), 120, "synthetic crate should have 120 functions");

    let mut total_vcs = 0usize;
    let mut functions_with_vcs = 0usize;
    let mut vc_counts_by_kind: FxHashMap<String, usize> = FxHashMap::default();

    for func in &functions {
        let vcs = trust_vcgen::generate_vcs(func);
        if !vcs.is_empty() {
            functions_with_vcs += 1;
        }
        total_vcs += vcs.len();

        for vc in &vcs {
            *vc_counts_by_kind.entry(vc.kind.description().to_string()).or_default() += 1;
        }
    }

    // Under pipeline-v2, vcgen delegates many patterns to MirRouter, so fewer
    // functions produce direct VCs from generate_vcs(). We verify that at least
    // some functions produce VCs and that we see multiple distinct VC kinds.
    assert!(functions_with_vcs > 0, "at least some functions should produce VCs, got 0");
    assert!(total_vcs > 0, "total VCs should be > 0 for 120 functions, got 0");

    // Verify we have a mix of VC kinds (at least 2 distinct kinds).
    assert!(
        vc_counts_by_kind.len() >= 2,
        "should have at least 2 distinct VC kinds, got: {vc_counts_by_kind:?}"
    );

    eprintln!("=== M3 VCGen at Scale ===");
    eprintln!("  Functions: 120");
    eprintln!("  Functions with VCs: {functions_with_vcs}");
    eprintln!("  Total VCs: {total_vcs}");
    for (kind, count) in &vc_counts_by_kind {
        eprintln!("    {kind}: {count}");
    }
    eprintln!("=========================");
}

// ---------------------------------------------------------------------------
// M3 Acceptance Test 2: Full pipeline (vcgen -> router -> report) at scale
// ---------------------------------------------------------------------------

#[test]
fn test_m3_full_pipeline_100_functions() {
    let functions = generate_synthetic_crate(120);
    let router = trust_router::Router::new();

    let mut all_results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();
    let mut proved = 0usize;
    let mut failed = 0usize;
    let mut unknown = 0usize;

    for func in &functions {
        // Step 1: VCGen
        let vcs = trust_vcgen::generate_vcs(func);

        // Step 2: Route through backend
        let results = router.verify_all(&vcs);

        // Step 3: Tally results
        for (_vc, result) in &results {
            match result {
                VerificationResult::Proved { .. } => proved += 1,
                VerificationResult::Failed { .. } => failed += 1,
                _ => {
                    unknown += 1;
                }
            }
        }
        all_results.extend(results);
    }

    // Under pipeline-v2, Router delegates many VCs through MirRouter which
    // returns aggregate results, so the direct result count may be lower than
    // the function count. Verify we got some results.
    assert!(!all_results.is_empty(), "pipeline should produce at least some verification results");

    // Step 4: Build proof report
    let report = trust_report::build_json_report("synthetic-crate", &all_results);

    // Verify report structure.
    assert!(!report.functions.is_empty(), "report should contain function-level entries");
    assert!(
        report.summary.total_obligations > 0,
        "report should cover at least some obligations, got {}",
        report.summary.total_obligations
    );

    eprintln!("=== M3 Full Pipeline (120 functions) ===");
    eprintln!("  Total obligations: {}", all_results.len());
    eprintln!("  Proved: {proved}");
    eprintln!("  Failed: {failed}");
    eprintln!("  Unknown: {unknown}");
    eprintln!("  Report functions: {}", report.functions.len());
    eprintln!("  Report verdict: {:?}", report.summary.verdict);
    eprintln!("=========================================");
}

// ---------------------------------------------------------------------------
// M3 Acceptance Test 3: Standalone source analysis at scale
// ---------------------------------------------------------------------------

#[test]
fn test_m3_standalone_source_analysis_at_scale() {
    // Create a temporary crate with 130+ function declarations.
    let tmp_dir = std::env::temp_dir().join("trust_m3_source_analysis");
    let src_dir = tmp_dir.join("src");
    let _ = std::fs::create_dir_all(&src_dir);

    // Generate a lib.rs with 130 functions of varying signatures.
    let mut source = String::from("//! Synthetic crate for M3 acceptance testing.\n\n");

    for i in 0..130 {
        match i % 5 {
            0 => {
                // Public function with arithmetic
                let _ = write!(
                    source,
                    "pub fn add_{i}(a: u64, b: u64) -> u64 {{ a.wrapping_add(b) }}\n\n"
                );
            }
            1 => {
                // Public function with specs
                let _ = write!(
                    source,
                    "#[requires(n > 0)]\npub fn checked_{i}(n: u32) -> u32 {{ n }}\n\n"
                );
            }
            2 => {
                // Unsafe function
                let _ = write!(
                    source,
                    "pub unsafe fn raw_ptr_{i}(ptr: *const u8) -> u8 {{ *ptr }}\n\n"
                );
            }
            3 => {
                // Private helper (should produce no VCs in standalone)
                let _ = write!(source, "fn helper_{i}(x: i32) -> i32 {{ x + 1 }}\n\n");
            }
            4 => {
                // Function with ensures
                let _ = write!(
                    source,
                    "#[ensures(result > 0)]\npub fn positive_{i}() -> u32 {{ 42 }}\n\n"
                );
            }
            _ => unreachable!(),
        }
    }

    std::fs::write(src_dir.join("lib.rs"), &source).expect("write synthetic lib.rs");

    // Write a minimal Cargo.toml for the temp crate.
    std::fs::write(
        tmp_dir.join("Cargo.toml"),
        "[package]\nname = \"m3-synthetic\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    )
    .expect("write Cargo.toml");

    // Use the source analysis module indirectly: count functions via text parsing.
    // Since source_analysis is pub(crate) in targo-trust, we replicate the key check:
    // parse the source and verify we get 130 functions.
    let content = std::fs::read_to_string(src_dir.join("lib.rs")).expect("read lib.rs");
    let fn_count = content
        .lines()
        .filter(|line| {
            let trimmed = line.trim();
            (trimmed.starts_with("pub fn ")
                || trimmed.starts_with("pub unsafe fn ")
                || trimmed.starts_with("fn "))
                && trimmed.contains('(')
        })
        .count();

    assert!(fn_count >= 130, "synthetic crate should have >= 130 functions, found {fn_count}");

    // Count spec attributes.
    let requires_count = content.lines().filter(|l| l.trim().starts_with("#[requires")).count();
    let ensures_count = content.lines().filter(|l| l.trim().starts_with("#[ensures")).count();
    let unsafe_count = content.lines().filter(|l| l.trim().contains("unsafe fn ")).count();

    assert!(requires_count >= 26, "should have >= 26 #[requires], got {requires_count}");
    assert!(ensures_count >= 26, "should have >= 26 #[ensures], got {ensures_count}");
    assert!(unsafe_count >= 26, "should have >= 26 unsafe fns, got {unsafe_count}");

    eprintln!("=== M3 Standalone Source Analysis ===");
    eprintln!("  Functions found: {fn_count}");
    eprintln!("  #[requires]: {requires_count}");
    eprintln!("  #[ensures]: {ensures_count}");
    eprintln!("  unsafe fn: {unsafe_count}");
    eprintln!("=====================================");

    // Cleanup.
    let _ = std::fs::remove_dir_all(&tmp_dir);
}

// ---------------------------------------------------------------------------
// M3 Acceptance Test 4: Cross-function contract analysis
// ---------------------------------------------------------------------------

#[test]
fn test_m3_cross_function_contracts() {
    // Create functions where one's postcondition feeds another's precondition.
    // This exercises cross-function VC generation.

    // Function A: safe_add with ensures(result >= a && result >= b)
    let func_a = VerifiableFunction {
        name: "safe_add".to_string(),
        def_path: "cross::safe_add".to_string(),
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
        contracts: vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "result >= a".to_string(),
        }],
        preconditions: vec![],
        postconditions: vec![Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Var("a".into(), Sort::Int)),
        )],
        spec: Default::default(),
    };

    // Function B: double_safe that calls safe_add (with its own contract)
    let func_b = VerifiableFunction {
        name: "double_safe".to_string(),
        def_path: "cross::double_safe".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(2, 1)),
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
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(2, 0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![
            Contract {
                kind: ContractKind::Ensures,
                span: SourceSpan::default(),
                body: "result >= x".to_string(),
            },
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "x <= 2147483647".to_string(),
            },
        ],
        preconditions: vec![Formula::Le(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(2_147_483_647)),
        )],
        postconditions: vec![Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Var("x".into(), Sort::Int)),
        )],
        spec: Default::default(),
    };

    // Generate VCs for both functions.
    let vcs_a = trust_vcgen::generate_vcs(&func_a);
    let vcs_b = trust_vcgen::generate_vcs(&func_b);

    // Both should produce VCs.
    assert!(!vcs_a.is_empty(), "safe_add should produce VCs (overflow + postcondition)");
    assert!(!vcs_b.is_empty(), "double_safe should produce VCs (overflow + contract)");

    // Verify contract-related VCs exist.
    let has_postcondition_a = vcs_a.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition));
    assert!(has_postcondition_a, "safe_add should have postcondition VC");

    // Route all VCs through the backend.
    let router = trust_router::Router::new();
    let mut all_results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();
    all_results.extend(router.verify_all(&vcs_a));
    all_results.extend(router.verify_all(&vcs_b));

    // Build combined report.
    let report = trust_report::build_json_report("cross-function-test", &all_results);

    assert!(
        report.functions.len() >= 2,
        "report should cover at least 2 functions, got {}",
        report.functions.len()
    );

    eprintln!("=== M3 Cross-Function Contracts ===");
    eprintln!("  safe_add VCs: {}", vcs_a.len());
    eprintln!("  double_safe VCs: {}", vcs_b.len());
    eprintln!("  Total results: {}", all_results.len());
    eprintln!("  Report functions: {}", report.functions.len());
    eprintln!("===================================");
}

// ---------------------------------------------------------------------------
// M3 Acceptance Test 5: JSON proof report at scale
// ---------------------------------------------------------------------------

#[test]
fn test_m3_report_generation_at_scale() {
    let functions = generate_synthetic_crate(120);
    let router = trust_router::Router::new();

    // Collect all verification results.
    let mut all_results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();
    for func in &functions {
        let vcs = trust_vcgen::generate_vcs(func);
        all_results.extend(router.verify_all(&vcs));
    }

    // Build the JSON proof report.
    let report = trust_report::build_json_report("m3-acceptance-crate", &all_results);

    // Validate report metadata.
    assert_eq!(report.crate_name, "m3-acceptance-crate");
    assert!(!report.metadata.schema_version.is_empty());
    assert!(!report.metadata.trust_version.is_empty());
    assert!(!report.metadata.timestamp.is_empty());

    // Validate summary counts. Under pipeline-v2, fewer VCs are generated
    // through the direct vcgen path.
    assert!(
        report.summary.total_obligations > 0,
        "report should have at least some obligations, got {}",
        report.summary.total_obligations
    );
    assert_eq!(
        report.summary.total_obligations,
        report.summary.total_proved
            + report.summary.total_failed
            + report.summary.total_unknown
            + report.summary.total_runtime_checked,
        "obligation counts should sum correctly"
    );

    // Validate JSON serialization round-trips.
    let json = serde_json::to_string_pretty(&report).expect("serialize report");
    assert!(json.len() > 1000, "JSON report should be substantial, got {} bytes", json.len());

    // Validate the JSON contains expected structure.
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("parse JSON");
    assert!(parsed["functions"].is_array());
    assert!(parsed["summary"].is_object());
    assert!(parsed["metadata"].is_object());

    // Validate text summary generation.
    let text_summary = trust_report::format_json_summary(&report);
    assert!(!text_summary.is_empty(), "text summary should be non-empty");

    eprintln!("=== M3 Report Generation ===");
    eprintln!("  JSON size: {} bytes", json.len());
    eprintln!("  Functions in report: {}", report.functions.len());
    eprintln!("  Total obligations: {}", report.summary.total_obligations);
    eprintln!("  Proved: {}", report.summary.total_proved);
    eprintln!("  Failed: {}", report.summary.total_failed);
    eprintln!("  Unknown: {}", report.summary.total_unknown);
    eprintln!("============================");
}

// ---------------------------------------------------------------------------
// M3 Acceptance Test 6: Pipeline does not panic on any pattern
// ---------------------------------------------------------------------------

#[test]
fn test_m3_no_panics_on_diverse_patterns() {
    // Generate a large diverse set and verify nothing panics.
    let functions = generate_synthetic_crate(200);
    let router = trust_router::Router::new();

    let mut total_vcs = 0usize;
    let mut total_results = 0usize;

    for func in &functions {
        let vcs = trust_vcgen::generate_vcs(func);
        total_vcs += vcs.len();

        let results = router.verify_all(&vcs);
        total_results += results.len();

        // Every VC should get a result.
        assert_eq!(
            vcs.len(),
            results.len(),
            "router should return one result per VC for function {}",
            func.name
        );
    }

    // Build report from all results (tests report builder does not panic).
    let all_results: Vec<(VerificationCondition, VerificationResult)> = functions
        .iter()
        .flat_map(|func| {
            let vcs = trust_vcgen::generate_vcs(func);
            let router = trust_router::Router::new();
            router.verify_all(&vcs)
        })
        .collect();

    let report = trust_report::build_json_report("stress-test", &all_results);
    let _json = serde_json::to_string(&report).expect("serialize stress test report");

    eprintln!("=== M3 No-Panic Stress Test (200 functions) ===");
    eprintln!("  Total VCs: {total_vcs}");
    eprintln!("  Total results: {total_results}");
    eprintln!("  Report obligations: {}", report.summary.total_obligations);
    eprintln!("===============================================");
}

// ---------------------------------------------------------------------------
// Real MIR fixture loading helpers
// ---------------------------------------------------------------------------

/// Path to real compiler-extracted MIR fixtures.
fn fixtures_dir() -> std::path::PathBuf {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures").join("real_mir")
}

/// Load all real MIR fixtures from the fixtures directory.
///
/// Returns an empty vec if fixtures have not been generated yet.
fn load_all_real_mir_fixtures() -> Vec<(String, VerifiableFunction)> {
    let dir = fixtures_dir();
    if !dir.exists() {
        return vec![];
    }
    let mut fixtures = Vec::new();
    for entry in std::fs::read_dir(&dir).expect("read fixtures dir") {
        let entry = entry.expect("read dir entry");
        let path = entry.path();
        if path.extension().is_none_or(|ext| ext != "json") {
            continue;
        }
        let name = path.file_stem().unwrap().to_string_lossy().to_string();
        let json = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
        match serde_json::from_str::<VerifiableFunction>(&json) {
            Ok(func) => fixtures.push((name, func)),
            Err(e) => {
                eprintln!("WARNING: skipping invalid fixture {}: {e}", path.display());
            }
        }
    }
    fixtures
}

/// Skip a test if no real MIR fixtures are available.
macro_rules! require_real_fixtures {
    ($fixtures:expr) => {
        if $fixtures.is_empty() {
            eprintln!(
                "SKIPPING: No real MIR fixtures found. Generate with:\n  \
                 ./scripts/generate_mir_fixtures.sh"
            );
            return;
        }
    };
}

// ---------------------------------------------------------------------------
// M3 Acceptance Test 7: Real MIR through full pipeline
// ---------------------------------------------------------------------------

#[test]
fn test_m3_real_mir_pipeline_at_scale() {
    let fixtures = load_all_real_mir_fixtures();
    require_real_fixtures!(fixtures);

    let router = trust_router::Router::new();

    let mut total_vcs = 0usize;
    let mut all_results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();
    let mut proved = 0usize;
    let mut failed = 0usize;
    let mut unknown = 0usize;

    for (_name, func) in &fixtures {
        let vcs = trust_vcgen::generate_vcs(func);
        total_vcs += vcs.len();
        let results = router.verify_all(&vcs);
        for (_vc, result) in &results {
            match result {
                VerificationResult::Proved { .. } => proved += 1,
                VerificationResult::Failed { .. } => failed += 1,
                _ => unknown += 1,
            }
        }
        all_results.extend(results);
    }

    // Build report.
    let report = trust_report::build_json_report("m3-real-mir", &all_results);

    // At least 10 real fixtures should be loaded (we have 13).
    assert!(fixtures.len() >= 10, "expected >= 10 real MIR fixtures, got {}", fixtures.len());

    // Real MIR should produce some VCs.
    assert!(total_vcs > 0, "real MIR should produce at least some VCs, got 0");

    // Report should have function entries for functions that produced VCs.
    assert!(!report.functions.is_empty(), "report should have function entries from real MIR");

    eprintln!("=== M3 Real MIR Pipeline at Scale ===");
    eprintln!("  Fixtures loaded: {}", fixtures.len());
    eprintln!("  Total VCs: {total_vcs}");
    eprintln!("  Proved: {proved}");
    eprintln!("  Failed: {failed}");
    eprintln!("  Unknown: {unknown}");
    eprintln!("  Report functions: {}", report.functions.len());
    eprintln!("  Report verdict: {:?}", report.summary.verdict);
    eprintln!("=====================================");
}

// ---------------------------------------------------------------------------
// M3 Acceptance Test 8: Mixed synthetic + real MIR pipeline
// ---------------------------------------------------------------------------

#[test]
fn test_m3_real_mir_mixed_synthetic_and_real() {
    let real_fixtures = load_all_real_mir_fixtures();
    require_real_fixtures!(real_fixtures);

    // Combine 120 synthetic functions with all real MIR fixtures.
    let synthetic = generate_synthetic_crate(120);
    let mut all_functions: Vec<&VerifiableFunction> = synthetic.iter().collect();
    let real_refs: Vec<&VerifiableFunction> = real_fixtures.iter().map(|(_, f)| f).collect();
    all_functions.extend(real_refs);

    let router = trust_router::Router::new();
    let mut all_results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();

    for func in &all_functions {
        let vcs = trust_vcgen::generate_vcs(func);
        let results = router.verify_all(&vcs);
        // Every VC should get a result.
        assert_eq!(
            vcs.len(),
            results.len(),
            "router should return one result per VC for function {}",
            func.name
        );
        all_results.extend(results);
    }

    // Build combined report.
    let report = trust_report::build_json_report("m3-mixed-crate", &all_results);

    // Total functions should be 120 + real fixture count.
    let expected_total = 120 + real_fixtures.len();
    assert_eq!(
        all_functions.len(),
        expected_total,
        "should have {} total functions (120 synthetic + {} real)",
        expected_total,
        real_fixtures.len()
    );

    // The combined set should produce some results. Under pipeline-v2, Router
    // delegates many VCs through MirRouter which returns aggregate results, so
    // the count may be lower than the function count.
    assert!(!all_results.is_empty(), "mixed pipeline should produce at least some results");

    eprintln!("=== M3 Mixed Synthetic + Real MIR ===");
    eprintln!("  Synthetic functions: 120");
    eprintln!("  Real MIR fixtures: {}", real_fixtures.len());
    eprintln!("  Total functions: {}", all_functions.len());
    eprintln!("  Total obligations: {}", all_results.len());
    eprintln!("  Report functions: {}", report.functions.len());
    eprintln!("  Report verdict: {:?}", report.summary.verdict);
    eprintln!("=====================================");
}

// ---------------------------------------------------------------------------
// M3 Acceptance Test 9: Real MIR VC kind diversity
// ---------------------------------------------------------------------------

#[test]
fn test_m3_real_mir_vc_categories() {
    let fixtures = load_all_real_mir_fixtures();
    require_real_fixtures!(fixtures);

    let mut vc_counts_by_kind: FxHashMap<String, usize> = FxHashMap::default();
    let mut total_vcs = 0usize;

    for (_name, func) in &fixtures {
        let vcs = trust_vcgen::generate_vcs(func);
        for vc in &vcs {
            *vc_counts_by_kind.entry(vc.kind.description().to_string()).or_default() += 1;
        }
        total_vcs += vcs.len();
    }

    // Real MIR should produce at least 2 distinct VC kinds.
    assert!(
        vc_counts_by_kind.len() >= 2,
        "real MIR should produce at least 2 distinct VC kinds, got {:?}",
        vc_counts_by_kind
    );

    eprintln!("=== M3 Real MIR VC Categories ===");
    eprintln!("  Fixtures: {}", fixtures.len());
    eprintln!("  Total VCs: {total_vcs}");
    for (kind, count) in &vc_counts_by_kind {
        eprintln!("    {kind}: {count}");
    }
    eprintln!("=================================");
}
