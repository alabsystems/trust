// trust-integration-tests/tests/scale_fixture_crate.rs: Scale test on physical fixture crate
//
// Validates the full verification pipeline against a real, multi-file Rust
// crate (fixtures/sample_crate/) with 100+ functions across 20 modules.
//
// This complements scale_real_crate.rs (which uses inline-generated code)
// by testing against a physical on-disk crate with realistic directory
// structure, module hierarchy, and mixed patterns.
//
// Part of #682
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use std::path::{Path, PathBuf};
use std::process::Command;

use trust_types::fx::FxHashMap;
use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, Contract, ContractKind, Formula, LocalDecl, Operand,
    Place, Projection, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, VerifiableBody,
    VerifiableFunction, VerificationCondition, VerificationResult,
};

// ---------------------------------------------------------------------------
// Fixture crate path resolution
// ---------------------------------------------------------------------------

fn fixture_crate_root() -> PathBuf {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest_dir.join("fixtures/sample_crate")
}

// ---------------------------------------------------------------------------
// Source file discovery and function counting
// ---------------------------------------------------------------------------

fn find_rs_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                files.extend(find_rs_files(&path));
            } else if path.extension().is_some_and(|ext| ext == "rs") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

/// Count function definitions in a Rust source file (line-based heuristic).
struct FunctionStats {
    total: usize,
    public: usize,
    unsafe_fns: usize,
    async_fns: usize,
    const_fns: usize,
    generic_fns: usize,
    requires_count: usize,
    ensures_count: usize,
    names: Vec<String>,
}

fn count_functions(source: &str) -> FunctionStats {
    let mut stats = FunctionStats {
        total: 0,
        public: 0,
        unsafe_fns: 0,
        async_fns: 0,
        const_fns: 0,
        generic_fns: 0,
        requires_count: 0,
        ensures_count: 0,
        names: Vec::new(),
    };

    for line in source.lines() {
        let trimmed = line.trim();

        if trimmed.starts_with("#[requires") {
            stats.requires_count += 1;
            continue;
        }
        if trimmed.starts_with("#[ensures") {
            stats.ensures_count += 1;
            continue;
        }

        let is_fn = (trimmed.starts_with("pub fn ")
            || trimmed.starts_with("pub unsafe fn ")
            || trimmed.starts_with("pub async fn ")
            || trimmed.starts_with("pub const fn ")
            || trimmed.starts_with("fn ")
            || trimmed.starts_with("unsafe fn ")
            || trimmed.starts_with("const fn ")
            || trimmed.starts_with("async fn "))
            && trimmed.contains('(');

        if is_fn {
            stats.total += 1;
            if trimmed.starts_with("pub ") {
                stats.public += 1;
            }
            if trimmed.contains("unsafe ") {
                stats.unsafe_fns += 1;
            }
            if trimmed.contains("async ") {
                stats.async_fns += 1;
            }
            if trimmed.contains("const ") {
                stats.const_fns += 1;
            }
            if trimmed.contains('<') && trimmed.contains('>') {
                stats.generic_fns += 1;
            }
            if let Some(fn_pos) = trimmed.find("fn ") {
                let after_fn = &trimmed[fn_pos + 3..];
                let end = after_fn.find(['(', '<']).unwrap_or(after_fn.len());
                let name = after_fn[..end].trim();
                if !name.is_empty() {
                    stats.names.push(name.to_string());
                }
            }
        }
    }

    stats
}

// ---------------------------------------------------------------------------
// VerifiableFunction builders (reused from scale_real_crate.rs patterns)
// ---------------------------------------------------------------------------

fn noop_fn(name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("sample_crate::{name}"),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn checked_add_fn(name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("sample_crate::{name}"),
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
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn division_fn(name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("sample_crate::{name}"),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn contract_fn(name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("sample_crate::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("val".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("lo".into()) },
                LocalDecl { index: 3, ty: Ty::i32(), name: Some("hi".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(1)), (1, BlockId(2))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 3,
            return_ty: Ty::i32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "lo <= hi".to_string(),
            },
            Contract {
                kind: ContractKind::Ensures,
                span: SourceSpan::default(),
                body: "result >= lo".to_string(),
            },
        ],
        preconditions: vec![Formula::Le(
            Box::new(Formula::Var("lo".into(), Sort::Int)),
            Box::new(Formula::Var("hi".into(), Sort::Int)),
        )],
        postconditions: vec![Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Var("lo".into(), Sort::Int)),
        )],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn array_index_fn(name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("sample_crate::{name}"),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

// ---------------------------------------------------------------------------
// Build VerifiableFunctions matching the fixture crate's pattern distribution
// ---------------------------------------------------------------------------

/// Build 120+ VerifiableFunctions representing the fixture crate's patterns.
///
/// Distribution mirrors the fixture's modules:
/// - 40 noop/identity (arithmetic accessors, string ops, patterns, conversions)
/// - 15 checked arithmetic (wrapping/checked/saturating ops)
/// - 10 division (safe_divide, safe_rem patterns)
/// - 10 array/bounds checks (binary_search, collection indexing)
/// - 15 contract functions (contracts module + validation)
/// - 10 generic/trait-dispatch (combinators, trait objects)
/// - 20 misc (closures, iterators, bitwise, io_utils)
fn build_fixture_functions() -> Vec<VerifiableFunction> {
    let mut funcs = Vec::with_capacity(120);

    // Noop/trivial: string ops, patterns, conversions, io_utils
    for i in 0..40 {
        funcs.push(noop_fn(&format!("trivial_{i:03}")));
    }
    // Checked arithmetic: wrapping_add, checked_add, saturating_add etc.
    for i in 0..15 {
        funcs.push(checked_add_fn(&format!("arith_{i:03}")));
    }
    // Division: safe_divide, safe_rem, gcd
    for i in 0..10 {
        funcs.push(division_fn(&format!("div_{i:03}")));
    }
    // Array/bounds: binary_search, collection indexing
    for i in 0..10 {
        funcs.push(array_index_fn(&format!("bounds_{i:03}")));
    }
    // Contract functions: clamp, abs, max_i32, min_i32, factorial, etc.
    for i in 0..15 {
        funcs.push(contract_fn(&format!("contract_{i:03}")));
    }
    // Generic/trait dispatch: identity, contains, all_match, apply_fn
    for i in 0..10 {
        funcs.push(noop_fn(&format!("generic_{i:03}")));
    }
    // Misc: closures, iterators, bitwise, io
    for i in 0..20 {
        funcs.push(noop_fn(&format!("misc_{i:03}")));
    }

    assert!(funcs.len() >= 120, "should have >= 120 functions, got {}", funcs.len());
    funcs
}

// ===========================================================================
// Test 1: Fixture crate structure validation
// ===========================================================================

#[test]
fn test_fixture_crate_exists_and_has_100_plus_functions() {
    let root = fixture_crate_root();
    assert!(root.exists(), "fixture crate should exist at {}", root.display());
    assert!(root.join("Cargo.toml").exists(), "fixture crate should have Cargo.toml");
    assert!(root.join("src/lib.rs").exists(), "fixture crate should have src/lib.rs");

    // Count source files
    let rs_files = find_rs_files(&root.join("src"));
    assert!(
        rs_files.len() >= 20,
        "fixture crate should have >= 20 .rs files, got {}",
        rs_files.len()
    );

    // Count total functions across all files
    let mut total_stats = FunctionStats {
        total: 0,
        public: 0,
        unsafe_fns: 0,
        async_fns: 0,
        const_fns: 0,
        generic_fns: 0,
        requires_count: 0,
        ensures_count: 0,
        names: Vec::new(),
    };

    for file in &rs_files {
        let content = std::fs::read_to_string(file).expect("read source file");
        let stats = count_functions(&content);
        total_stats.total += stats.total;
        total_stats.public += stats.public;
        total_stats.unsafe_fns += stats.unsafe_fns;
        total_stats.async_fns += stats.async_fns;
        total_stats.const_fns += stats.const_fns;
        total_stats.generic_fns += stats.generic_fns;
        total_stats.requires_count += stats.requires_count;
        total_stats.ensures_count += stats.ensures_count;
        total_stats.names.extend(stats.names);
    }

    // Acceptance criteria: 100+ functions
    assert!(
        total_stats.total >= 100,
        "fixture crate should have >= 100 functions, got {}",
        total_stats.total
    );

    // Pattern diversity
    assert!(
        total_stats.unsafe_fns >= 5,
        "should have >= 5 unsafe functions, got {}",
        total_stats.unsafe_fns
    );
    assert!(
        total_stats.async_fns >= 5,
        "should have >= 5 async functions, got {}",
        total_stats.async_fns
    );
    assert!(
        total_stats.const_fns >= 5,
        "should have >= 5 const functions, got {}",
        total_stats.const_fns
    );
    assert!(
        total_stats.generic_fns >= 5,
        "should have >= 5 generic functions, got {}",
        total_stats.generic_fns
    );

    // Spec annotations
    assert!(
        total_stats.requires_count >= 5,
        "should have >= 5 #[requires] annotations, got {}",
        total_stats.requires_count
    );
    assert!(
        total_stats.ensures_count >= 5,
        "should have >= 5 #[ensures] annotations, got {}",
        total_stats.ensures_count
    );

    eprintln!("=== Fixture Crate Structure ===");
    eprintln!("  Source files: {}", rs_files.len());
    eprintln!("  Total functions: {}", total_stats.total);
    eprintln!("  Public: {}", total_stats.public);
    eprintln!("  Unsafe: {}", total_stats.unsafe_fns);
    eprintln!("  Async: {}", total_stats.async_fns);
    eprintln!("  Const: {}", total_stats.const_fns);
    eprintln!("  Generic: {}", total_stats.generic_fns);
    eprintln!("  #[requires]: {}", total_stats.requires_count);
    eprintln!("  #[ensures]: {}", total_stats.ensures_count);
    eprintln!("===============================");
}

// ===========================================================================
// Test 2: Full pipeline on fixture-derived functions
// ===========================================================================

#[test]
fn test_fixture_pipeline_120_functions() {
    let functions = build_fixture_functions();
    assert!(functions.len() >= 120);

    let router = trust_router::Router::new();
    let mut all_results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();
    let mut proved = 0usize;
    let mut failed = 0usize;
    let mut unknown = 0usize;
    let mut vc_kind_counts: FxHashMap<String, usize> = FxHashMap::default();

    for func in &functions {
        let vcs = trust_vcgen::generate_vcs(func);
        let results = router.verify_all(&vcs);
        assert_eq!(
            vcs.len(),
            results.len(),
            "router should return one result per VC for {}",
            func.name
        );
        for (vc, result) in &results {
            *vc_kind_counts.entry(vc.kind.description().to_string()).or_default() += 1;
            match result {
                VerificationResult::Proved { .. } => proved += 1,
                VerificationResult::Failed { .. } => failed += 1,
                _ => unknown += 1,
            }
        }
        all_results.extend(results);
    }

    // Should produce meaningful VCs
    assert!(
        all_results.len() >= 50,
        "should produce >= 50 VCs from 120 functions, got {}",
        all_results.len()
    );

    // Multiple VC kinds
    assert!(
        vc_kind_counts.len() >= 3,
        "should have >= 3 distinct VC kinds, got: {vc_kind_counts:?}"
    );

    // Per-function prove rate
    let mut functions_fully_proved = 0usize;
    for func in &functions {
        let vcs = trust_vcgen::generate_vcs(func);
        if vcs.is_empty() {
            functions_fully_proved += 1;
            continue;
        }
        let results = router.verify_all(&vcs);
        if results.iter().all(|(_, r)| matches!(r, VerificationResult::Proved { .. })) {
            functions_fully_proved += 1;
        }
    }
    let proved_pct = (functions_fully_proved as f64 / functions.len() as f64) * 100.0;

    assert!(
        proved_pct >= 30.0,
        "at least 30% of functions should be fully proved, got {:.1}% ({}/{})",
        proved_pct,
        functions_fully_proved,
        functions.len()
    );

    eprintln!("=== Fixture Pipeline (120+ functions) ===");
    eprintln!("  Functions: {}", functions.len());
    eprintln!("  Total VCs: {}", all_results.len());
    eprintln!("  Proved VCs: {proved}");
    eprintln!("  Failed VCs: {failed}");
    eprintln!("  Unknown VCs: {unknown}");
    eprintln!("  VC kinds: {vc_kind_counts:?}");
    eprintln!(
        "  Functions proved: {functions_fully_proved}/{} ({proved_pct:.1}%)",
        functions.len()
    );
    eprintln!("=========================================");
}

// ===========================================================================
// Test 3: Report generation from fixture functions
// ===========================================================================

#[test]
fn test_fixture_report_generation() {
    let functions = build_fixture_functions();
    let router = trust_router::Router::new();
    let mut all_results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();

    for func in &functions {
        let vcs = trust_vcgen::generate_vcs(func);
        all_results.extend(router.verify_all(&vcs));
    }

    let report = trust_report::build_json_report("sample-crate", &all_results);

    assert_eq!(report.crate_name, "sample-crate");
    assert!(
        report.summary.total_obligations >= 50,
        "report should have >= 50 obligations, got {}",
        report.summary.total_obligations
    );
    assert!(
        report.functions.len() >= 30,
        "report should cover >= 30 functions, got {}",
        report.functions.len()
    );

    // JSON round-trip
    let json = serde_json::to_string_pretty(&report).expect("serialize report");
    assert!(json.len() > 2000, "JSON report should be substantial");
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("parse JSON");
    assert!(parsed["functions"].is_array());
    assert!(parsed["summary"]["total_obligations"].is_number());

    // Obligation counts are consistent
    assert_eq!(
        report.summary.total_obligations,
        report.summary.total_proved
            + report.summary.total_failed
            + report.summary.total_unknown
            + report.summary.total_runtime_checked,
        "obligation counts should sum correctly"
    );

    // HTML report
    let html = trust_report::html_report::generate_html_report(&report);
    assert!(html.contains("<html") || html.contains("<!DOCTYPE"));
    assert!(html.contains("sample-crate"));

    // Text summary
    let text = trust_report::format_json_summary(&report);
    assert!(!text.is_empty());
    assert!(text.contains("Verdict:"));

    eprintln!("=== Fixture Report ===");
    eprintln!("  Obligations: {}", report.summary.total_obligations);
    eprintln!("  Functions: {}", report.functions.len());
    eprintln!("  JSON size: {} bytes", json.len());
    eprintln!("  HTML size: {} bytes", html.len());
    eprintln!("  Verdict: {:?}", report.summary.verdict);
    eprintln!("======================");
}

// ===========================================================================
// Test 4: Zero false positives on safe fixture functions
// ===========================================================================

#[test]
fn test_fixture_no_false_positives() {
    // Trivial/noop functions should produce 0 VCs and thus 0 failures.
    let safe_functions: Vec<VerifiableFunction> =
        (0..40).map(|i| noop_fn(&format!("safe_{i:03}"))).collect();

    for func in &safe_functions {
        let vcs = trust_vcgen::generate_vcs(func);
        assert!(
            vcs.is_empty(),
            "safe function {} should produce 0 VCs, got {}",
            func.name,
            vcs.len()
        );
    }
}

// ===========================================================================
// Test 5: targo-trust standalone mode on fixture crate (subprocess)
// ===========================================================================

#[test]
fn test_fixture_targo_trust_standalone() {
    let root = fixture_crate_root();
    assert!(root.exists(), "fixture crate must exist");

    let targo_trust_bin = require_targo_trust_binary();

    // Run: targo-trust trust check --standalone --format json
    // (We invoke it directly, not via `targo trust`, since we want to
    // point it at the fixture crate directory.)
    let output = Command::new(&targo_trust_bin)
        .args(["trust", "check", "--standalone", "--format", "json"])
        .current_dir(&root)
        .output()
        .expect("failed to run targo-trust");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let context = format!(
        "{} trust check --standalone --format json in {}\nexit: {:?}\nstdout (first 500): {}\nstderr (first 2000): {}",
        targo_trust_bin.display(),
        root.display(),
        output.status.code(),
        stdout.chars().take(500).collect::<String>(),
        stderr.chars().take(2000).collect::<String>(),
    );

    // Every outcome below is asserted: a binary that crashes, prints nothing,
    // prints something other than the source-audit report, or exits in a way
    // its own report does not explain FAILS this test. Until 2026-09-30 empty or
    // non-JSON stdout only warned, so `/usr/bin/false` and `/bin/echo` passed;
    // after that fix a one-line script printing `{"functions_found":100}` still
    // passed (measured 2026-09-30), because nothing else in the report, and not
    // the exit status, was checked.
    let json: serde_json::Value = serde_json::from_str(&stdout)
        .unwrap_or_else(|e| panic!("stdout is not the JSON report: {e}\n{context}"));
    assert_eq!(json["schema_version"], "trust.source-audit.v1", "{context}");
    assert_eq!(json["mode"], "source-audit", "{context}");
    // Standalone mode is a source audit: it must never claim proof authority.
    assert_eq!(json["proof_authority"], "none", "{context}");
    assert_eq!(json["compiler_verification_performed"], false, "{context}");

    let functions_found =
        json["functions_found"].as_u64().unwrap_or_else(|| panic!("no functions_found\n{context}"));
    assert!(
        functions_found >= 100,
        "should find >= 100 functions, got {functions_found}\n{context}"
    );
    let functions =
        json["functions"].as_array().unwrap_or_else(|| panic!("no functions array\n{context}"));
    assert_eq!(
        functions.len() as u64,
        functions_found,
        "functions array vs functions_found\n{context}"
    );
    assert!(json["files_analyzed"].as_u64().unwrap_or(0) > 0, "no file analyzed\n{context}");

    // The counts the report states must be the rows it lists.
    let rows = json["audit_rows"].as_array().unwrap_or_else(|| panic!("no audit_rows\n{context}"));
    assert_eq!(json["total_audit_rows"].as_u64(), Some(rows.len() as u64), "{context}");
    let count = |outcome: &str| rows.iter().filter(|r| r["outcome"] == outcome).count() as u64;
    assert_eq!(json["present"].as_u64(), Some(count("Present")), "present\n{context}");
    assert_eq!(json["failed"].as_u64(), Some(count("Failed")), "failed\n{context}");
    assert_eq!(json["unknown"].as_u64(), Some(count("Unknown")), "unknown\n{context}");

    // The exit code is the report's verdict, and nothing else: 0 when the
    // audit passed, 1 when it did not (the fixture's hardened-profile
    // findings make it fail today), never a crash or another code.
    let audit_passed =
        json["audit_passed"].as_bool().unwrap_or_else(|| panic!("no audit_passed\n{context}"));
    assert_eq!(audit_passed, count("Failed") == 0, "audit_passed vs failed rows\n{context}");
    assert_eq!(
        output.status.code(),
        Some(if audit_passed { 0 } else { 1 }),
        "exit code must be the audit verdict\n{context}"
    );
    eprintln!(
        "targo-trust standalone: exit {:?}, {functions_found} functions, {} rows ({} failed)",
        output.status.code(),
        rows.len(),
        count("Failed")
    );
}

/// The `targo-trust` binary these tests run: the file `TRUST_TARGO_TRUST_BIN`
/// names. Unset, empty, relative, or not a file panics; there is no search and
/// no skip (docs/issues/2026-09-29-binary-to-trust-ir-e2e-golden-stale-and-passes-without-its-binary.md,
/// defect 2). The search this replaces took whatever binary it found, built from
/// whatever tree, and when it found none the test returned early, which libtest
/// counts as a pass. scripts/check_crates_tests_scoped.py, scripts/dev-test.sh and
/// `targo trust gate check-all --run-tests` build targo-trust from the tree under
/// test and set the variable to a private copy of it. A relative value is
/// refused: `is_file` would check it against the test's cwd, but `Command::new`
/// looks a slash-free one up on PATH, so the file checked would not be the file
/// run. binary_to_trust_ir_e2e.rs has the same helper.
fn require_targo_trust_binary() -> PathBuf {
    const HOW: &str = "build it from this tree with `targo --unverified build --manifest-path \
        targo-trust/Cargo.toml --bin targo-trust --locked` and set TRUST_TARGO_TRUST_BIN to the \
        absolute path of that binary (the `executable` of cargo's compiler-artifact message under \
        --message-format json). Use the binary built from this tree and commit. \
        To leave this test out of a local run, pass \
        libtest's `--skip <test name>`";
    let Some(value) = std::env::var_os("TRUST_TARGO_TRUST_BIN").filter(|v| !v.is_empty()) else {
        panic!("TRUST_TARGO_TRUST_BIN is unset or empty, and this test runs targo-trust: {HOW}");
    };
    let path = PathBuf::from(value);
    assert!(
        path.is_absolute() && path.is_file(),
        "TRUST_TARGO_TRUST_BIN={} is not the absolute path of an existing file: {HOW}",
        path.display()
    );
    path
}

// ===========================================================================
// Test 6: Module-level function distribution
// ===========================================================================

#[test]
fn test_fixture_module_distribution() {
    let root = fixture_crate_root();
    let src_dir = root.join("src");

    // Each module directory should have at least 1 function
    let mut module_counts: Vec<(String, usize)> = Vec::new();
    let module_dirs = std::fs::read_dir(&src_dir)
        .expect("read src dir")
        .filter_map(|e| e.ok())
        .filter(|e| e.path().is_dir())
        .collect::<Vec<_>>();

    assert!(
        module_dirs.len() >= 20,
        "should have >= 20 module directories, got {}",
        module_dirs.len()
    );

    for entry in &module_dirs {
        let mod_file = entry.path().join("mod.rs");
        if mod_file.exists() {
            let content = std::fs::read_to_string(&mod_file).expect("read mod.rs");
            let stats = count_functions(&content);
            let name = entry.file_name().to_string_lossy().to_string();
            module_counts.push((name, stats.total));
        }
    }

    // Every module should have at least 5 functions
    for (name, count) in &module_counts {
        assert!(*count >= 5, "module {} should have >= 5 functions, got {}", name, count);
    }

    eprintln!("=== Module Distribution ===");
    for (name, count) in &module_counts {
        eprintln!("  {name}: {count} functions");
    }
    let total: usize = module_counts.iter().map(|(_, c)| c).sum();
    eprintln!("  TOTAL: {total} functions across {} modules", module_counts.len());
    eprintln!("===========================");
}
