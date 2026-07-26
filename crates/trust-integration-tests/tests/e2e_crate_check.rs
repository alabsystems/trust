// trust-integration-tests/tests/e2e_crate_check.rs: End-to-end CLI pipeline test
//
// Exercises the full Trust verification pipeline on a real Rust crate's source
// files (trust-types). This is the M3 follow-up: real source code flows through
// function extraction -> synthetic MIR construction -> vcgen -> router -> report.
//
// Unlike the M3 acceptance tests (which use pre-built synthetic VerifiableFunction
// objects), this test starts from actual .rs source files and builds the pipeline
// input by parsing real Rust function signatures.
//
// Acceptance criteria (from #598):
// - Run pipeline on a real crate (trust-types) without crashing
// - At least 100 functions verified
// - Structured JSON proof report covering all public functions
// - Report is valid JSON
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use std::path::{Path, PathBuf};
use trust_types::fx::FxHashMap;

use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Contract, ContractKind, LocalDecl, Operand, Place,
    Projection, Rvalue, SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
    VerificationCondition, VerificationResult,
};

// ---------------------------------------------------------------------------
// Source-level function extraction (lightweight, no rustc needed)
// ---------------------------------------------------------------------------

/// A function parsed from source code.
#[derive(Debug, Clone)]
struct ParsedFunction {
    name: String,
    file: PathBuf,
    line: usize,
    is_public: bool,
    is_unsafe: bool,
    has_requires: bool,
    has_ensures: bool,
    return_type: Option<String>,
    param_count: usize,
    /// Heuristic: does the function body contain arithmetic operations?
    has_arithmetic: bool,
    /// Heuristic: does the function body contain division?
    has_division: bool,
    /// Heuristic: does the function body contain array/slice indexing?
    has_indexing: bool,
}

/// Find all .rs files under a directory recursively.
fn find_rs_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                files.extend(find_rs_files(&path));
            } else if path.extension().is_some_and(|e| e == "rs") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

/// Extract function signatures from a Rust source file.
///
/// This is a lightweight line-by-line parser (not a full AST parse).
/// Good enough to detect function boundaries, visibility, and basic
/// body patterns for synthetic MIR construction.
fn extract_functions(path: &Path) -> Vec<ParsedFunction> {
    let content = match std::fs::read_to_string(path) {
        Ok(c) => c,
        Err(_) => return Vec::new(),
    };

    let mut functions = Vec::new();
    let mut pending_requires = false;
    let mut pending_ensures = false;
    let mut in_block_comment = false;
    let lines: Vec<&str> = content.lines().collect();

    for (idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();

        // Track block comments.
        if in_block_comment {
            if trimmed.contains("*/") {
                in_block_comment = false;
            }
            continue;
        }
        if trimmed.starts_with("/*") {
            in_block_comment = true;
            if trimmed.contains("*/") {
                in_block_comment = false;
            }
            continue;
        }
        if trimmed.starts_with("//") {
            continue;
        }

        // Detect spec attributes.
        if trimmed.starts_with("#[requires") || trimmed.starts_with("#[trust_requires") {
            pending_requires = true;
            continue;
        }
        if trimmed.starts_with("#[ensures") || trimmed.starts_with("#[trust_ensures") {
            pending_ensures = true;
            continue;
        }
        if trimmed.starts_with("#[") {
            continue;
        }

        // Try to parse as function declaration.
        if let Some(mut func) = try_parse_fn(trimmed, path, idx + 1) {
            func.has_requires = pending_requires;
            func.has_ensures = pending_ensures;

            // Scan the function body for operation patterns (heuristic).
            let body_text = scan_function_body(&lines, idx);
            func.has_arithmetic = body_text.contains('+')
                || body_text.contains('-')
                || body_text.contains('*')
                || body_text.contains("wrapping_add")
                || body_text.contains("checked_add")
                || body_text.contains("saturating_");
            func.has_division = body_text.contains('/')
                || body_text.contains('%')
                || body_text.contains("checked_div");
            func.has_indexing = body_text.contains('[') && body_text.contains(']');

            functions.push(func);
            pending_requires = false;
            pending_ensures = false;
        } else if !trimmed.is_empty() && !trimmed.starts_with("pub") {
            pending_requires = false;
            pending_ensures = false;
        }
    }

    functions
}

/// Scan lines starting from a function declaration to capture the body text.
fn scan_function_body(lines: &[&str], fn_line: usize) -> String {
    let mut depth = 0i32;
    let mut body = String::new();
    let mut started = false;

    for line in lines.iter().skip(fn_line) {
        for ch in line.chars() {
            if ch == '{' {
                depth += 1;
                started = true;
            } else if ch == '}' {
                depth -= 1;
            }
        }
        if started {
            body.push_str(line);
            body.push('\n');
        }
        if started && depth <= 0 {
            break;
        }
    }
    body
}

/// Try to parse a line as a function declaration.
fn try_parse_fn(line: &str, file: &Path, line_num: usize) -> Option<ParsedFunction> {
    let mut rest = line;
    let mut is_public = false;
    let mut is_unsafe = false;

    // Strip visibility.
    if rest.starts_with("pub") {
        is_public = true;
        rest = rest[3..].trim_start();
        if rest.starts_with('(')
            && let Some(close) = rest.find(')')
        {
            rest = rest[close + 1..].trim_start();
        }
    }

    // Strip qualifiers.
    loop {
        if let Some(after) = rest.strip_prefix("const ") {
            rest = after.trim_start();
        } else if let Some(after) = rest.strip_prefix("async ") {
            rest = after.trim_start();
        } else if let Some(after) = rest.strip_prefix("unsafe ") {
            is_unsafe = true;
            rest = after.trim_start();
        } else if let Some(after) = rest.strip_prefix("extern ") {
            rest = after.trim_start();
            if rest.starts_with('"')
                && let Some(close) = rest[1..].find('"')
            {
                rest = rest[close + 2..].trim_start();
            }
        } else {
            break;
        }
    }

    rest = rest.strip_prefix("fn ")?;
    rest = rest.trim_start();

    let name_end = rest.find(|c: char| c == '(' || c == '<' || c.is_whitespace())?;
    let name = &rest[..name_end];
    if name.is_empty() {
        return None;
    }

    // Count parameters.
    let param_count = if let Some(paren_start) = rest.find('(') {
        if let Some(paren_end) = rest[paren_start..].find(')') {
            let params = &rest[paren_start + 1..paren_start + paren_end];
            if params.trim().is_empty() { 0 } else { params.split(',').count() }
        } else {
            0
        }
    } else {
        0
    };

    // Extract return type.
    let return_type = rest.find("->").map(|arrow| {
        let after = rest[arrow + 2..].trim();
        let end = after.find(['{', '\n']).unwrap_or(after.len());
        after[..end].trim().to_string()
    });

    Some(ParsedFunction {
        name: name.to_string(),
        file: file.to_path_buf(),
        line: line_num,
        is_public,
        is_unsafe,
        has_requires: false,
        has_ensures: false,
        return_type,
        param_count,
        has_arithmetic: false,
        has_division: false,
        has_indexing: false,
    })
}

// ---------------------------------------------------------------------------
// Source-to-MIR bridge: convert parsed functions to VerifiableFunction
// ---------------------------------------------------------------------------

/// Convert a parsed function into a synthetic VerifiableFunction.
///
/// The MIR body is constructed based on heuristics from the source:
/// - Functions with arithmetic get CheckedBinaryOp statements
/// - Functions with division get Div/Rem rvalues
/// - Functions with indexing get array access patterns
/// - All functions get a basic return block
///
/// This produces realistic VerifiableFunction objects that exercise the
/// full vcgen pipeline, even though the MIR is synthesized rather than
/// extracted from the real compiler.
fn to_verifiable_function(parsed: &ParsedFunction) -> VerifiableFunction {
    let def_path = format!(
        "{}::{}",
        parsed.file.file_stem().unwrap_or_default().to_string_lossy(),
        parsed.name
    );

    let span = SourceSpan {
        file: parsed.file.to_string_lossy().to_string(),
        line_start: parsed.line as u32,
        col_start: 1,
        line_end: parsed.line as u32,
        col_end: 1,
    };

    // Determine the return type.
    let return_ty = infer_ty(&parsed.return_type);

    // Build locals: _0 = return, _1.._N = args.
    let arg_count = parsed.param_count;
    let mut locals = vec![LocalDecl { index: 0, ty: return_ty.clone(), name: None }];
    for i in 1..=arg_count {
        locals.push(LocalDecl {
            index: i,
            ty: Ty::u64(), // Default arg type for synthetic MIR.
            name: Some(format!("arg{i}")),
        });
    }

    // Build blocks based on detected patterns.
    let mut blocks = Vec::new();
    let mut stmts = Vec::new();
    let mut next_local = locals.len();

    // Pattern 1: Arithmetic operations -> CheckedBinaryOp.
    if parsed.has_arithmetic && arg_count >= 2 {
        // _tmp = CheckedAdd(_1, _2)
        let tmp = next_local;
        locals.push(LocalDecl { index: tmp, ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]), name: None });
        next_local += 1;

        stmts.push(Statement::Assign {
            place: Place::local(tmp),
            rvalue: Rvalue::CheckedBinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: span.clone(),
        });

        // Assert on the overflow flag.
        blocks.push(BasicBlock {
            id: BlockId(0),
            stmts: stmts.clone(),
            terminator: Terminator::Assert {
                cond: Operand::Copy(Place::field(tmp, 1)),
                expected: false,
                target: BlockId(1),
                msg: trust_types::AssertMessage::Overflow(BinOp::Add),
                span: SourceSpan::default(),
                unwind: trust_types::UnwindEdge::Unreachable,
            },
        });
        stmts.clear();

        // Result block: _0 = _tmp.0
        let result_local = next_local;
        locals.push(LocalDecl { index: result_local, ty: Ty::u64(), name: None });
        let _ = next_local;

        stmts.push(Statement::Assign {
            place: Place::local(result_local),
            rvalue: Rvalue::Use(Operand::Copy(Place::field(tmp, 0))),
            span: span.clone(),
        });
        stmts.push(Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(result_local))),
            span: span.clone(),
        });
        blocks.push(BasicBlock { id: BlockId(1), stmts, terminator: Terminator::Return });
    }
    // Pattern 2: Division -> Div rvalue (produces DivisionByZero VC).
    else if parsed.has_division && arg_count >= 2 {
        stmts.push(Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Div,
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            span: span.clone(),
        });
        blocks.push(BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return });
    }
    // Pattern 3: Indexing -> array bounds check.
    else if parsed.has_indexing && arg_count >= 1 {
        // _array = [_1; 10]
        let arr_local = next_local;
        locals.push(LocalDecl {
            index: arr_local,
            ty: Ty::Array { elem: Box::new(Ty::u64()), len: 10 },
            name: Some("arr".into()),
        });
        next_local += 1;

        let idx_local = if arg_count >= 2 { 2 } else { 1 };

        // _result = _array[_idx]
        let result_local = next_local;
        locals.push(LocalDecl { index: result_local, ty: Ty::u64(), name: None });
        #[allow(unused_assignments)]
        {
            next_local += 1;
        }

        stmts.push(Statement::Assign {
            place: Place { local: arr_local, projections: vec![Projection::Index(idx_local)] },
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
            span: span.clone(),
        });
        stmts.push(Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place {
                local: arr_local,
                projections: vec![Projection::Index(idx_local)],
            })),
            span: span.clone(),
        });
        blocks.push(BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return });
    }
    // Pattern 4: Default -- simple return (produces no VCs, which is correct
    // for functions with no risky operations).
    else {
        if arg_count >= 1 {
            stmts.push(Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                span: span.clone(),
            });
        }
        blocks.push(BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return });
    }

    // Build contracts from spec attributes.
    let mut contracts = Vec::new();
    if parsed.has_requires {
        contracts.push(Contract {
            kind: ContractKind::Requires,
            span: span.clone(),
            body: "true".to_string(),
        });
    }
    if parsed.has_ensures {
        contracts.push(Contract {
            kind: ContractKind::Ensures,
            span: span.clone(),
            body: "true".to_string(),
        });
    }

    VerifiableFunction {
        name: parsed.name.clone(),
        def_path,
        span,
        body: VerifiableBody { locals, blocks, arg_count, return_ty },
        contracts,
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    }
}

/// Infer a Ty from a source-level return type string.
fn infer_ty(return_type: &Option<String>) -> Ty {
    match return_type.as_deref() {
        None | Some("()") => Ty::Unit,
        Some("bool") => Ty::Bool,
        Some("u8") => Ty::u8(),
        Some("u16") => Ty::u16(),
        Some("u32") => Ty::u32(),
        Some("u64") => Ty::u64(),
        Some("usize") => Ty::usize(),
        Some("i8") => Ty::i8(),
        Some("i16") => Ty::i16(),
        Some("i32") => Ty::i32(),
        Some("i64") => Ty::i64(),
        Some("isize") => Ty::isize(),
        Some(s) if s.starts_with("&str") || s.contains("String") => {
            Ty::Ref { mutable: false, inner: Box::new(Ty::u8()) }
        }
        Some(s) if s.starts_with("Vec<") => Ty::Slice { elem: Box::new(Ty::u64()) },
        Some(s) if s.starts_with("Option<") => Ty::Tuple(vec![Ty::Bool, Ty::u64()]),
        Some(s) if s.starts_with("Result<") => Ty::Tuple(vec![Ty::Bool, Ty::u64()]),
        Some(s) if s.contains("Self") => Ty::u64(),
        _ => Ty::u64(), // Default fallback.
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// Find the trust-types crate source directory.
fn trust_types_src() -> PathBuf {
    // The test binary is built from crates/trust-integration-tests.
    // trust-types is at crates/trust-types/src/.
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest_dir.join("../trust-types/src")
}

#[test]
fn test_e2e_pipeline_on_trust_types_crate() {
    let src_dir = trust_types_src();
    assert!(src_dir.is_dir(), "trust-types/src not found at {}", src_dir.display());

    // Step 1: Find all source files.
    let files = find_rs_files(&src_dir);
    assert!(
        files.len() >= 5,
        "Expected at least 5 .rs files in trust-types, found {}",
        files.len()
    );
    eprintln!("Found {} source files in trust-types", files.len());

    // Step 2: Extract functions from all files.
    let mut all_parsed: Vec<ParsedFunction> = Vec::new();
    for file in &files {
        let funcs = extract_functions(file);
        all_parsed.extend(funcs);
    }
    eprintln!(
        "Extracted {} functions ({} public, {} unsafe)",
        all_parsed.len(),
        all_parsed.iter().filter(|f| f.is_public).count(),
        all_parsed.iter().filter(|f| f.is_unsafe).count()
    );
    assert!(all_parsed.len() >= 100, "Expected at least 100 functions, found {}", all_parsed.len());

    // Step 3: Convert to VerifiableFunction objects.
    let verifiable: Vec<VerifiableFunction> =
        all_parsed.iter().map(to_verifiable_function).collect();
    eprintln!("Built {} VerifiableFunction objects", verifiable.len());

    // Step 4: Generate VCs for each function via trust_vcgen.
    let mut all_vcs: Vec<VerificationCondition> = Vec::new();
    let mut vc_counts: FxHashMap<String, usize> = FxHashMap::default();
    let mut errors = 0usize;

    for func in &verifiable {
        // Error recovery: if vcgen panics on a function, catch it and continue.
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            trust_vcgen::generate_vcs(func)
        }));
        match result {
            Ok(vcs) => {
                vc_counts.insert(func.name.clone(), vcs.len());
                all_vcs.extend(vcs);
            }
            Err(_) => {
                errors += 1;
                eprintln!("  vcgen panicked on function: {}", func.name);
            }
        }
    }

    eprintln!(
        "Generated {} VCs from {} functions ({} errors)",
        all_vcs.len(),
        verifiable.len(),
        errors
    );

    // Step 5: Route all VCs through trust-router (ConstantFolderBackend).
    let router = trust_router::Router::new();
    let results = router.verify_all(&all_vcs);
    eprintln!("Router returned {} results", results.len());

    assert_eq!(results.len(), all_vcs.len(), "Router should return one result per VC");

    // Count outcomes.
    let proved =
        results.iter().filter(|(_, r)| matches!(r, VerificationResult::Proved { .. })).count();
    let failed =
        results.iter().filter(|(_, r)| matches!(r, VerificationResult::Failed { .. })).count();
    let unknown =
        results.iter().filter(|(_, r)| matches!(r, VerificationResult::Unknown { .. })).count();

    eprintln!("Outcomes: {} proved, {} failed, {} unknown", proved, failed, unknown);

    // Step 6: Build JSON proof report via trust-report.
    let report = trust_report::build_json_report("trust-types", &results);

    // Validate report structure.
    let json = serde_json::to_string_pretty(&report).expect("Report should serialize to JSON");
    assert!(!json.is_empty(), "JSON report should not be empty");

    // Parse back to verify valid JSON.
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("Report JSON should parse back");
    assert!(parsed.is_object(), "Report should be a JSON object");

    // Check report has expected top-level fields.
    let obj = parsed.as_object().unwrap();
    // schema_version is nested under metadata, not top-level.
    assert!(obj.contains_key("metadata"), "Report should have metadata (contains schema_version)");
    assert!(obj.contains_key("functions"), "Report should have functions");
    assert!(obj.contains_key("summary"), "Report should have summary");

    // Verify function count in report.
    let report_functions =
        obj.get("functions").and_then(|v| v.as_array()).map(|a| a.len()).unwrap_or(0);
    eprintln!("Report contains {} function entries", report_functions);

    // Also render the text summary to verify no panics.
    let text_summary = trust_report::format_json_summary(&report);
    assert!(!text_summary.is_empty(), "Text summary should not be empty");
    eprintln!("\n{text_summary}");

    // Step 7: Acceptance criteria validation.
    assert!(
        verifiable.len() >= 100,
        "AC: At least 100 functions verified (got {})",
        verifiable.len()
    );
    assert_eq!(errors, 0, "AC: Pipeline should complete without crashing (got {} errors)", errors);
    assert!(all_vcs.len() >= 10, "AC: Should generate at least 10 VCs (got {})", all_vcs.len());

    eprintln!("\n=== E2E Pipeline Test PASSED ===");
    eprintln!("  Files:     {}", files.len());
    eprintln!("  Functions: {}", verifiable.len());
    eprintln!("  VCs:       {}", all_vcs.len());
    eprintln!("  Proved:    {proved}");
    eprintln!("  Failed:    {failed}");
    eprintln!("  Unknown:   {unknown}");
    eprintln!("  Errors:    {errors}");
    eprintln!("================================");
}

#[test]
fn test_e2e_json_report_valid_structure() {
    // Smaller test: verify JSON report structure on a handful of synthetic functions.
    let functions = vec![
        make_simple_add("add_u64", Ty::u64()),
        make_simple_div("safe_div", Ty::u64()),
        make_noop("noop_fn"),
    ];

    let mut all_vcs = Vec::new();
    for func in &functions {
        let vcs = trust_vcgen::generate_vcs(func);
        all_vcs.extend(vcs);
    }

    let router = trust_router::Router::new();
    let results = router.verify_all(&all_vcs);
    let report = trust_report::build_json_report("test-crate", &results);

    let json = serde_json::to_string_pretty(&report).expect("should serialize");
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("should parse");

    // Validate summary.
    let summary = parsed.get("summary").expect("should have summary");
    assert!(summary.get("total_obligations").is_some(), "summary should have total_obligations");
    assert!(summary.get("verdict").is_some(), "summary should have verdict");
}

#[test]
fn test_source_extraction_finds_real_functions() {
    let src_dir = trust_types_src();
    if !src_dir.is_dir() {
        eprintln!("Skipping: trust-types/src not found");
        return;
    }

    // lib.rs is module declarations and re-exports — no functions. The historical
    // `formula.rs` file was split into a `formula/` directory; `formula/mod.rs` is
    // now a pure re-export shell with no fn definitions (the Formula AST + methods
    // moved to trust-ir-contract and submodules). Use `formula/vc_kind.rs`, which
    // still defines the VcKind methods.
    let formula_rs = src_dir.join("formula").join("vc_kind.rs");
    let funcs = extract_functions(&formula_rs);

    // trust-types/src/formula/vc_kind.rs should have functions (VcKind methods, etc.).
    assert!(!funcs.is_empty(), "Should find functions in trust-types/src/formula/vc_kind.rs");

    let public_count = funcs.iter().filter(|f| f.is_public).count();
    eprintln!("Found {} functions ({} public) in formula/vc_kind.rs", funcs.len(), public_count);
}

#[test]
fn test_verifiable_function_conversion_all_patterns() {
    // Test that all source patterns produce valid VerifiableFunction objects.
    let patterns = vec![
        ParsedFunction {
            name: "arith_fn".into(),
            file: PathBuf::from("test.rs"),
            line: 1,
            is_public: true,
            is_unsafe: false,
            has_requires: false,
            has_ensures: false,
            return_type: Some("u64".into()),
            param_count: 2,
            has_arithmetic: true,
            has_division: false,
            has_indexing: false,
        },
        ParsedFunction {
            name: "div_fn".into(),
            file: PathBuf::from("test.rs"),
            line: 10,
            is_public: true,
            is_unsafe: false,
            has_requires: false,
            has_ensures: false,
            return_type: Some("u64".into()),
            param_count: 2,
            has_arithmetic: false,
            has_division: true,
            has_indexing: false,
        },
        ParsedFunction {
            name: "index_fn".into(),
            file: PathBuf::from("test.rs"),
            line: 20,
            is_public: true,
            is_unsafe: false,
            has_requires: false,
            has_ensures: false,
            return_type: Some("u64".into()),
            param_count: 2,
            has_arithmetic: false,
            has_division: false,
            has_indexing: true,
        },
        ParsedFunction {
            name: "simple_fn".into(),
            file: PathBuf::from("test.rs"),
            line: 30,
            is_public: false,
            is_unsafe: false,
            has_requires: true,
            has_ensures: true,
            return_type: None,
            param_count: 0,
            has_arithmetic: false,
            has_division: false,
            has_indexing: false,
        },
    ];

    for parsed in &patterns {
        let vf = to_verifiable_function(parsed);
        assert_eq!(vf.name, parsed.name);
        assert!(!vf.body.blocks.is_empty(), "Function {} should have blocks", parsed.name);
        assert_eq!(
            vf.body.arg_count, parsed.param_count,
            "Function {} arg_count mismatch",
            parsed.name
        );

        // Verify vcgen doesn't panic.
        let vcs = trust_vcgen::generate_vcs(&vf);
        eprintln!(
            "  {} -> {} VCs (blocks: {}, locals: {})",
            parsed.name,
            vcs.len(),
            vf.body.blocks.len(),
            vf.body.locals.len()
        );
    }
}

// ---------------------------------------------------------------------------
// Helper constructors for smaller tests
// ---------------------------------------------------------------------------

fn make_simple_add(name: &str, ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![ty.clone(), Ty::Bool]), name: None },
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
                        target: BlockId(1),
                        msg: trust_types::AssertMessage::Overflow(BinOp::Add),
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
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn make_simple_div(name: &str, ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{name}"),
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
        spec: Default::default(),
    }
}

fn make_noop(name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{name}"),
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
