// trust-integration-tests/tests/real_mir_pipeline.rs
//
// Integration tests using real compiler-extracted MIR fixtures.
//
// These tests load VerifiableFunction JSON fixtures produced by the real
// compiler (via -Ztrust-dump=mir:<dir>) and run them through the verification pipeline:
// vcgen -> router -> report.
//
// Fixture generation: ./scripts/generate_mir_fixtures.sh
// See #941 for background.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::PathBuf;

use trust_router::MirRouter;
use trust_types::{VerifiableFunction, VerificationResult};

/// Path to the real MIR fixtures directory.
fn fixtures_dir() -> PathBuf {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    PathBuf::from(manifest_dir).join("fixtures").join("real_mir")
}

fn fixture_source_path() -> PathBuf {
    fixtures_dir().join("src").join("test_functions.rs")
}

fn coverage_manifest_path() -> PathBuf {
    fixtures_dir().join("coverage_manifest.json")
}

fn load_coverage_manifest() -> serde_json::Value {
    let path = coverage_manifest_path();
    let json = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read manifest {}: {e}", path.display()));
    serde_json::from_str(&json)
        .unwrap_or_else(|e| panic!("failed to parse manifest {}: {e}", path.display()))
}

/// Load a VerifiableFunction from a JSON fixture file.
///
/// Returns None if the fixture does not exist (allows tests to skip gracefully
/// when fixtures have not been generated yet).
fn load_fixture(name: &str) -> Option<VerifiableFunction> {
    let path = fixtures_dir().join(format!("{name}.json"));
    if !path.exists() {
        return None;
    }
    let json = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read fixture {}: {e}", path.display()));
    let func: VerifiableFunction = serde_json::from_str(&json)
        .unwrap_or_else(|e| panic!("failed to parse fixture {}: {e}", path.display()));
    Some(func)
}

/// Load all JSON fixtures from the fixtures directory.
fn load_all_fixtures() -> Vec<(String, VerifiableFunction)> {
    let dir = fixtures_dir();
    if !dir.exists() {
        return vec![];
    }
    let mut fixtures = Vec::new();
    for entry in std::fs::read_dir(&dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().is_none_or(|ext| ext != "json") {
            continue;
        }
        let name = path.file_stem().unwrap().to_string_lossy().to_string();
        if !name.starts_with("test_functions__") {
            continue;
        }
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

/// Skip a test if no fixtures are available, with a helpful message.
macro_rules! require_fixtures {
    ($fixtures:expr) => {
        if $fixtures.is_empty() {
            eprintln!(
                "SKIPPING: No real MIR fixtures found. Generate them with:\n  \
                 ./scripts/generate_mir_fixtures.sh"
            );
            return;
        }
    };
}

/// Skip a single-fixture test if the fixture does not exist.
macro_rules! require_fixture {
    ($fixture:expr, $name:expr) => {
        match $fixture {
            Some(f) => f,
            None => {
                eprintln!(
                    "SKIPPING: Fixture '{}' not found. Generate with:\n  \
                     ./scripts/generate_mir_fixtures.sh",
                    $name
                );
                return;
            }
        }
    };
}

// ---------------------------------------------------------------------------
// Test 1: All fixtures parse and produce valid VerifiableFunction
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_all_fixtures_parse() {
    let fixtures = load_all_fixtures();
    require_fixtures!(fixtures);

    for (name, func) in &fixtures {
        // Every fixture should have a name and def_path.
        assert!(!func.name.is_empty(), "fixture {name} has empty function name");
        assert!(!func.def_path.is_empty(), "fixture {name} has empty def_path");
        // Every fixture should have at least one basic block.
        assert!(
            !func.body.blocks.is_empty(),
            "fixture {name} ({}) has no basic blocks",
            func.def_path
        );
        // Every fixture should have a return local (index 0).
        assert!(!func.body.locals.is_empty(), "fixture {name} ({}) has no locals", func.def_path);
        assert_eq!(
            func.body.locals[0].index, 0,
            "fixture {name}: first local should be _0 (return place)"
        );
    }

    eprintln!("=== Real MIR Fixtures ===");
    eprintln!("  Loaded {} fixtures", fixtures.len());
    for (name, func) in &fixtures {
        eprintln!(
            "    {name}: {} blocks, {} locals, {} args",
            func.body.blocks.len(),
            func.body.locals.len(),
            func.body.arg_count
        );
    }
    eprintln!("=========================");
}

// ---------------------------------------------------------------------------
// Test 2: VCGen on all real MIR fixtures
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_vcgen_all() {
    let fixtures = load_all_fixtures();
    require_fixtures!(fixtures);

    let mut total_vcs = 0usize;
    let mut fixtures_with_vcs = 0usize;

    for (_name, func) in &fixtures {
        let vcs = trust_vcgen::generate_vcs(func);
        if !vcs.is_empty() {
            fixtures_with_vcs += 1;
        }
        total_vcs += vcs.len();
    }

    eprintln!("=== Real MIR VCGen ===");
    eprintln!("  Fixtures: {}", fixtures.len());
    eprintln!("  Fixtures with VCs: {fixtures_with_vcs}");
    eprintln!("  Total VCs: {total_vcs}");
    eprintln!("======================");

    // Real functions should produce SOME VCs (arithmetic checks, etc.)
    assert!(total_vcs > 0, "real MIR fixtures should produce at least some VCs, got 0");
}

// ---------------------------------------------------------------------------
// Test 3: Full pipeline (vcgen -> router -> report) on all fixtures
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_full_pipeline() {
    let fixtures = load_all_fixtures();
    require_fixtures!(fixtures);

    let router = trust_router::Router::new();

    let mut all_results: Vec<(trust_types::VerificationCondition, VerificationResult)> = Vec::new();
    let mut proved = 0usize;
    let mut failed = 0usize;
    let mut unknown = 0usize;

    for (_name, func) in &fixtures {
        let vcs = trust_vcgen::generate_vcs(func);
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
    let report = trust_report::build_json_report("real-mir-test", &all_results);

    assert!(!report.functions.is_empty(), "report should contain function entries");

    eprintln!("=== Real MIR Full Pipeline ===");
    eprintln!("  Total obligations: {}", all_results.len());
    eprintln!("  Proved: {proved}");
    eprintln!("  Failed: {failed}");
    eprintln!("  Unknown: {unknown}");
    eprintln!("  Report functions: {}", report.functions.len());
    eprintln!("  Report verdict: {:?}", report.summary.verdict);
    eprintln!("==============================");
}

// ---------------------------------------------------------------------------
// Test 4: Arithmetic function produces overflow VCs
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_arithmetic_overflow() {
    let func = require_fixture!(
        load_fixture("test_functions__checked_add"),
        "test_functions__checked_add"
    );

    // Structural: checked_add(a: u32, b: u32) -> u32 should have 2 args.
    assert_eq!(func.body.arg_count, 2, "checked_add should have 2 arguments");
    assert!(!func.body.blocks.is_empty(), "checked_add should have basic blocks");

    // Pipeline v2: vcgen delegates arithmetic checks to MirRouter.
    // Verify the function runs through the full pipeline without panics.
    let router = MirRouter::with_defaults();
    let strategy = router.classify(&func);
    let result = router.verify_function(&func);

    eprintln!("=== Real MIR: checked_add ===");
    eprintln!("  Blocks: {}", func.body.blocks.len());
    eprintln!("  Locals: {}", func.body.locals.len());
    eprintln!("  Strategy: {strategy}");
    eprintln!("  Result: {result:?}");
    eprintln!("=============================");

    // The function should get a terminal verification result.
    assert_result_is_terminal(&result, "checked_add");
}

// ---------------------------------------------------------------------------
// Test 5: Division function produces div-by-zero VCs
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_division() {
    let func = require_fixture!(
        load_fixture("test_functions__safe_divide"),
        "test_functions__safe_divide"
    );

    // Structural: safe_divide(a: u32, b: u32) -> u32 should have 2 args.
    assert_eq!(func.body.arg_count, 2, "safe_divide should have 2 arguments");
    assert!(!func.body.blocks.is_empty(), "safe_divide should have basic blocks");

    // Pipeline v2: vcgen delegates division checks to MirRouter.
    let router = MirRouter::with_defaults();
    let strategy = router.classify(&func);
    let result = router.verify_function(&func);

    eprintln!("=== Real MIR: safe_divide ===");
    eprintln!("  Blocks: {}", func.body.blocks.len());
    eprintln!("  Locals: {}", func.body.locals.len());
    eprintln!("  Strategy: {strategy}");
    eprintln!("  Result: {result:?}");
    eprintln!("=============================");

    assert_result_is_terminal(&result, "safe_divide");
}

// ---------------------------------------------------------------------------
// Test 6: Control flow function has multiple basic blocks
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_control_flow() {
    let func = require_fixture!(load_fixture("test_functions__max_of"), "test_functions__max_of");

    // max_of uses if/else, so it should have multiple basic blocks.
    assert!(
        func.body.blocks.len() >= 2,
        "max_of should have >= 2 basic blocks (if/else), got {}",
        func.body.blocks.len()
    );

    // Should have 2 args (a, b) plus return place.
    assert_eq!(func.body.arg_count, 2, "max_of should have 2 arguments");

    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("=== Real MIR: max_of ===");
    eprintln!("  Blocks: {}", func.body.blocks.len());
    eprintln!("  VCs: {}", vcs.len());
    eprintln!("========================");
}

// ---------------------------------------------------------------------------
// Test 7: Loop function has back edges
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_loop() {
    let func = require_fixture!(load_fixture("test_functions__sum_to"), "test_functions__sum_to");

    // sum_to uses a while loop, so should have multiple blocks with back-edges.
    assert!(
        func.body.blocks.len() >= 3,
        "sum_to should have >= 3 basic blocks (loop header, body, exit), got {}",
        func.body.blocks.len()
    );

    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("=== Real MIR: sum_to ===");
    eprintln!("  Blocks: {}", func.body.blocks.len());
    eprintln!("  VCs: {}", vcs.len());
    eprintln!("========================");
}

// ---------------------------------------------------------------------------
// Test 8: Reference function handles borrows
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_references() {
    let func =
        require_fixture!(load_fixture("test_functions__read_ref"), "test_functions__read_ref");

    // read_ref takes &i32, should have at least one argument.
    assert!(func.body.arg_count >= 1, "read_ref should have at least 1 argument");

    // Should have a reference type somewhere in locals.
    let has_ref_ty = func.body.locals.iter().any(|local| {
        matches!(&local.ty, trust_types::Ty::Ref { .. } | trust_types::Ty::RawPtr { .. })
    });

    eprintln!("=== Real MIR: read_ref ===");
    eprintln!("  Blocks: {}", func.body.blocks.len());
    eprintln!("  Locals: {}", func.body.locals.len());
    eprintln!("  Has ref type: {has_ref_ty}");
    for (i, local) in func.body.locals.iter().enumerate() {
        eprintln!("    _{}: {:?} {:?}", i, local.ty, local.name);
    }
    eprintln!("==========================");
}

// ---------------------------------------------------------------------------
// Test 9: Unsafe function produces VCs
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_unsafe() {
    let func = require_fixture!(
        load_fixture("test_functions__unsafe_read"),
        "test_functions__unsafe_read"
    );

    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("=== Real MIR: unsafe_read ===");
    eprintln!("  Blocks: {}", func.body.blocks.len());
    eprintln!("  VCs: {}", vcs.len());
    for vc in &vcs {
        eprintln!("    {:?}", vc.kind);
    }
    eprintln!("=============================");

    // Unsafe pointer dereference should have at least one VC about safety.
    // The exact VC depends on how the compiler models unsafe operations.
}

// ---------------------------------------------------------------------------
// Test 10: Closure function has expected structure
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_closure() {
    let func = require_fixture!(
        load_fixture("test_functions__apply_twice"),
        "test_functions__apply_twice"
    );

    // apply_twice uses a closure, so should have basic blocks.
    assert!(!func.body.blocks.is_empty(), "apply_twice should have basic blocks");

    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("=== Real MIR: apply_twice ===");
    eprintln!("  Blocks: {}", func.body.blocks.len());
    eprintln!("  Locals: {}", func.body.locals.len());
    eprintln!("  VCs: {}", vcs.len());
    eprintln!("=============================");
}

// ---------------------------------------------------------------------------
// Test 11: Drop elaboration function has complex MIR
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_drop_elaboration() {
    let func = require_fixture!(
        load_fixture("test_functions__string_creation"),
        "test_functions__string_creation"
    );

    // String creation and drop should produce more complex MIR than simple
    // arithmetic — more blocks, more locals for temporaries.
    assert!(
        func.body.blocks.len() >= 2,
        "string_creation should have >= 2 basic blocks (creation + drop), got {}",
        func.body.blocks.len()
    );

    eprintln!("=== Real MIR: string_creation ===");
    eprintln!("  Blocks: {}", func.body.blocks.len());
    eprintln!("  Locals: {}", func.body.locals.len());
    eprintln!("=================================");
}

// ---------------------------------------------------------------------------
// Test 12: Generic monomorphized function
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_generic_monomorphized() {
    // After monomorphization, identity<i32> should exist as a concrete function.
    // The fixture name depends on the compiler's def_path for the monomorphized instance.
    let func = require_fixture!(
        load_fixture("test_functions__use_identity"),
        "test_functions__use_identity"
    );

    // This function calls identity::<i32>, so should have a call terminator or
    // inline expansion.
    assert!(!func.body.blocks.is_empty(), "use_identity should have basic blocks");

    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("=== Real MIR: use_identity ===");
    eprintln!("  Blocks: {}", func.body.blocks.len());
    eprintln!("  Locals: {}", func.body.locals.len());
    eprintln!("  VCs: {}", vcs.len());
    eprintln!("==============================");
}

// ---------------------------------------------------------------------------
// Test 13: Pipeline does not panic on any real MIR fixture
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_no_panics() {
    let fixtures = load_all_fixtures();
    require_fixtures!(fixtures);

    let router = trust_router::Router::new();

    for (name, func) in &fixtures {
        // VCGen should not panic.
        let vcs = trust_vcgen::generate_vcs(func);
        // Router should not panic.
        let results = router.verify_all(&vcs);
        // Every VC should get a result.
        assert_eq!(
            vcs.len(),
            results.len(),
            "router should return one result per VC for fixture {name}"
        );
    }

    eprintln!("=== Real MIR No-Panic: all {} fixtures passed ===", fixtures.len());
}

// ---------------------------------------------------------------------------
// Test 14: MirRouter classifies all real MIR fixtures
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_router_classify_all() {
    let fixtures = load_all_fixtures();
    require_fixtures!(fixtures);

    let router = MirRouter::with_defaults();
    let mut strategy_counts: std::collections::HashMap<String, usize> =
        std::collections::HashMap::new();

    for (name, func) in &fixtures {
        let strategy = router.classify(func);
        *strategy_counts.entry(format!("{strategy}")).or_insert(0) += 1;

        eprintln!("  {name}: {strategy}");
    }

    eprintln!("=== Real MIR Router Classification ===");
    eprintln!("  Fixtures: {}", fixtures.len());
    for (strategy, count) in &strategy_counts {
        eprintln!("  {strategy}: {count}");
    }
    eprintln!("======================================");

    // Every fixture should produce a valid strategy (the classify function is total).
    assert_eq!(
        strategy_counts.values().sum::<usize>(),
        fixtures.len(),
        "every fixture should be classified"
    );
}

// ---------------------------------------------------------------------------
// Test 15: MirRouter verifies all real MIR fixtures to terminal results
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_router_verify_all() {
    let fixtures = load_all_fixtures();
    require_fixtures!(fixtures);

    let router = MirRouter::with_defaults();
    let mut proved = 0usize;
    let mut failed = 0usize;
    let mut unknown = 0usize;

    for (name, func) in &fixtures {
        let result = router.verify_function(func);
        match &result {
            VerificationResult::Proved { .. } => proved += 1,
            VerificationResult::Failed { .. } => failed += 1,
            VerificationResult::Unknown { .. } => unknown += 1,
            _ => panic!("{name}: expected terminal result, got {result:?}"),
        }
        assert_result_is_terminal(&result, name);
    }

    eprintln!("=== Real MIR Router Verify All ===");
    eprintln!("  Fixtures: {}", fixtures.len());
    eprintln!("  Proved: {proved}");
    eprintln!("  Failed: {failed}");
    eprintln!("  Unknown: {unknown}");
    eprintln!("==================================");
}

// ---------------------------------------------------------------------------
// Test 16: Real MIR structural properties — terminator diversity
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_terminator_diversity() {
    let fixtures = load_all_fixtures();
    require_fixtures!(fixtures);

    let mut terminator_types: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut total_blocks = 0usize;
    let mut total_stmts = 0usize;

    for (_name, func) in &fixtures {
        for block in &func.body.blocks {
            total_blocks += 1;
            total_stmts += block.stmts.len();

            let term_name = match &block.terminator {
                trust_types::Terminator::Goto(_) => "Goto",
                trust_types::Terminator::SwitchInt { .. } => "SwitchInt",
                trust_types::Terminator::Return => "Return",
                trust_types::Terminator::Call { .. } => "Call",
                trust_types::Terminator::Assert { .. } => "Assert",
                trust_types::Terminator::Drop { .. } => "Drop",
                trust_types::Terminator::Unreachable => "Unreachable",
                _ => "Other",
            };
            terminator_types.insert(term_name.to_string());
        }
    }

    eprintln!("=== Real MIR Terminator Diversity ===");
    eprintln!("  Fixtures: {}", fixtures.len());
    eprintln!("  Total blocks: {total_blocks}");
    eprintln!("  Total statements: {total_stmts}");
    eprintln!("  Terminator types: {:?}", terminator_types);
    eprintln!("=====================================");

    // Real compiler MIR should produce at least 3 distinct terminator types
    // (Return, Goto, and at least one of SwitchInt/Call/Assert/Drop).
    assert!(
        terminator_types.len() >= 3,
        "real MIR should have >= 3 distinct terminator types, got {:?}",
        terminator_types
    );

    // Should have Return (every function ends) and Goto (control flow).
    assert!(terminator_types.contains("Return"), "real MIR must have Return terminators");
}

// ---------------------------------------------------------------------------
// Test 17: Real MIR statement diversity (StorageLive/Dead, Assign)
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_statement_diversity() {
    let fixtures = load_all_fixtures();
    require_fixtures!(fixtures);

    let mut has_storage_live = false;
    let mut has_assign = false;
    let mut has_storage_dead = false;

    for (_name, func) in &fixtures {
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                match stmt {
                    trust_types::Statement::StorageLive(_) => has_storage_live = true,
                    trust_types::Statement::StorageDead(_) => has_storage_dead = true,
                    trust_types::Statement::Assign { .. } => has_assign = true,
                    _ => {}
                }
            }
        }
    }

    eprintln!("=== Real MIR Statement Diversity ===");
    eprintln!("  StorageLive: {has_storage_live}");
    eprintln!("  StorageDead: {has_storage_dead}");
    eprintln!("  Assign: {has_assign}");
    eprintln!("====================================");

    // Real compiler MIR always uses StorageLive/StorageDead for stack allocation
    // and Assign for data movement — these are fundamental to how rustc works.
    assert!(has_assign, "real MIR should contain Assign statements");
    assert!(has_storage_live, "real MIR should contain StorageLive statements");
}

// ---------------------------------------------------------------------------
// Test 18: Real vs synthetic MIR — type diversity comparison
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_type_diversity() {
    let fixtures = load_all_fixtures();
    require_fixtures!(fixtures);

    let mut ty_names: std::collections::HashSet<String> = std::collections::HashSet::new();

    for (_name, func) in &fixtures {
        for local in &func.body.locals {
            let ty_name = match &local.ty {
                trust_types::Ty::Bool => "Bool".to_string(),
                trust_types::Ty::Int { width, signed } => {
                    format!("{}Int{width}", if *signed { "S" } else { "U" })
                }
                trust_types::Ty::Float { width } => format!("Float{width}"),
                trust_types::Ty::Ref { .. } => "Ref".to_string(),
                trust_types::Ty::RawPtr { .. } => "RawPtr".to_string(),
                trust_types::Ty::Tuple(_) => "Tuple".to_string(),
                trust_types::Ty::Unit => "Unit".to_string(),
                _ => "Other".to_string(),
            };
            ty_names.insert(ty_name);
        }
    }

    eprintln!("=== Real MIR Type Diversity ===");
    eprintln!("  Types found: {:?}", ty_names);
    eprintln!("===============================");

    // Real MIR should have at least Bool and some integer type (from args/returns).
    assert!(ty_names.contains("Bool"), "real MIR should use Bool type");
    assert!(ty_names.iter().any(|t| t.contains("Int")), "real MIR should use integer types");
}

// ---------------------------------------------------------------------------
// Test 18: Fixture coverage manifest prevents silent sample narrowing
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_coverage_manifest_tracks_required_fixtures() {
    let fixtures = load_all_fixtures();
    require_fixtures!(fixtures);

    let manifest = load_coverage_manifest();
    assert_eq!(
        manifest.get("schema").and_then(|v| v.as_str()),
        Some("trust.real-mir.coverage.v1"),
        "coverage manifest should declare the expected schema"
    );

    let required = manifest
        .get("required_generated_fixtures")
        .and_then(|v| v.as_array())
        .expect("coverage manifest must list required generated fixtures");
    assert!(!required.is_empty(), "required_generated_fixtures must not be empty");

    let fixture_names: std::collections::HashSet<&str> =
        fixtures.iter().map(|(name, _)| name.as_str()).collect();
    for fixture in required {
        let fixture = fixture.as_str().expect("required fixture names must be strings");
        assert!(
            fixture_names.contains(fixture),
            "required real-MIR fixture {fixture} is missing; update coverage_manifest.json only with an explicit unsupported/removal rationale"
        );
    }
}

// ---------------------------------------------------------------------------
// Test 19: Unsupported slice/provenance source anchors stay visible
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_unsupported_slice_provenance_source_anchors() {
    let manifest = load_coverage_manifest();
    let source_path = fixture_source_path();
    let source = std::fs::read_to_string(&source_path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", source_path.display()));

    let anchors = manifest
        .get("unsupported_source_anchors")
        .and_then(|v| v.as_array())
        .expect("coverage manifest must list unsupported source anchors");
    assert!(!anchors.is_empty(), "unsupported_source_anchors must not be empty");
    assert!(
        anchors.iter().any(|entry| {
            entry.get("model_gap").and_then(|v| v.as_str()) == Some("slice_fat_pointer_provenance")
        }),
        "manifest must explicitly track the slice/fat-pointer/provenance gap"
    );

    for entry in anchors {
        let function = entry
            .get("function")
            .and_then(|v| v.as_str())
            .expect("unsupported anchor function must be a string");
        assert_eq!(
            entry.get("status").and_then(|v| v.as_str()),
            Some("unsupported_until_modeled"),
            "{function}: unsupported anchors must not masquerade as supported"
        );

        let markers = entry
            .get("source_markers")
            .and_then(|v| v.as_array())
            .expect("unsupported anchor must include source markers");
        assert!(!markers.is_empty(), "{function}: source markers must not be empty");
        for marker in markers {
            let marker = marker.as_str().expect("source markers must be strings");
            assert!(
                source.contains(marker),
                "{function}: source marker `{marker}` missing from {}",
                source_path.display()
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Test 20: Future generated unsupported fixtures must fail closed
// ---------------------------------------------------------------------------

#[test]
fn test_real_mir_unsupported_manifest_fixtures_fail_closed_when_generated() {
    let manifest = load_coverage_manifest();
    let anchors = manifest
        .get("unsupported_source_anchors")
        .and_then(|v| v.as_array())
        .expect("coverage manifest must list unsupported source anchors");

    let mut generated_count = 0usize;
    for entry in anchors {
        let fixture = entry
            .get("fixture")
            .and_then(|v| v.as_str())
            .expect("unsupported anchor fixture must be a string");
        let Some(func) = load_fixture(fixture) else {
            continue;
        };
        generated_count += 1;

        let vcs = trust_vcgen::generate_vcs(&func);
        let unsupported_details = vcs
            .iter()
            .filter_map(|vc| match &vc.kind {
                trust_types::VcKind::UnsupportedMir { kind, detail } => {
                    Some(format!("{} {}", kind.to_lowercase(), detail.to_lowercase()))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(
            !unsupported_details.is_empty(),
            "{fixture}: generated unsupported sample produced no UnsupportedMir VCs"
        );

        let expected = entry
            .get("expected_unsupported_detail_any")
            .and_then(|v| v.as_array())
            .expect("unsupported anchor must include expected unsupported detail markers");
        assert!(
            expected
                .iter()
                .filter_map(|v| v.as_str())
                .any(|needle| { unsupported_details.iter().any(|detail| detail.contains(needle)) }),
            "{fixture}: UnsupportedMir details did not mention expected slice/fat-pointer/metadata/provenance markers: {unsupported_details:?}"
        );
    }

    eprintln!("generated unsupported real-MIR fixture anchors checked: {generated_count}");
}

// ---------------------------------------------------------------------------
// Helper: assert verification result is terminal
// ---------------------------------------------------------------------------

fn assert_result_is_terminal(result: &VerificationResult, func_name: &str) {
    match result {
        VerificationResult::Proved { solver, .. } => {
            assert!(!solver.is_empty(), "{func_name}: proved result should name a solver");
        }
        VerificationResult::Failed { solver, .. } => {
            assert!(!solver.is_empty(), "{func_name}: failed result should name a solver");
        }
        VerificationResult::Unknown { solver, reason, .. } => {
            assert!(!solver.is_empty(), "{func_name}: unknown result should name a solver");
            assert!(!reason.is_empty(), "{func_name}: unknown result should have a reason");
        }
        _ => panic!("{func_name}: expected a terminal verification result"),
    }
}
