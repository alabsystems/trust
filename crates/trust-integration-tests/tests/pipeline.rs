// trust-integration-tests/tests/pipeline.rs: Cross-crate pipeline integration tests
//
// Exercises the full Trust verification pipeline:
//   extract (synthetic) -> vcgen -> router -> report
// plus cache hit/miss, level filtering, and symex path constraints.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_integration_tests::{
    array_access_function, contract_function, division_function, midpoint_function, noop_function,
    ay_test_support::require_ay,
};

use trust_types::{
    BinOp, Counterexample, CounterexampleValue, Formula, FunctionVerdict,
    ProofLevel, ProofStrength, Sort, SourceSpan, VcKind, VerificationCondition, VerificationResult,
};

// A router pinned to the deterministic `ConstantFolderBackend` only. These
// plumbing tests assert mock behavior (Unknown for variable formulas); pinning
// the backend keeps them independent of workspace feature unification, which
// otherwise registers the real in-process ay backend via `Router::new()`.
fn mock_router() -> trust_router::Router {
    trust_router::Router::with_backends(vec![Box::new(
        trust_router::constant_folder::ConstantFolderBackend,
    )])
}

// ---------------------------------------------------------------------------
// 1. VCGen -> Router: generate VCs from synthetic MIR, route through ConstantFolderBackend
// ---------------------------------------------------------------------------

#[test]
fn test_vcgen_to_router_midpoint_overflow() {
    let func = midpoint_function();

    // Step 1: Generate VCs
    let vcs = trust_vcgen::generate_vcs(&func);
    assert_eq!(vcs.len(), 1, "midpoint should produce exactly 1 VC");
    assert!(
        matches!(vcs[0].kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }),
        "VC should be arithmetic overflow for Add"
    );
    assert_eq!(vcs[0].function, "get_midpoint");
    assert_eq!(vcs[0].kind.proof_level(), ProofLevel::L0Safety);

    // Step 2: Route through ConstantFolderBackend
    let router = mock_router();
    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), 1);

    // ConstantFolderBackend returns Unknown for variable-containing formulas
    let (ref vc, ref result) = results[0];
    assert_eq!(vc.function, "get_midpoint");
    assert!(
        matches!(result, VerificationResult::Unknown { .. }),
        "mock backend should return Unknown for formula with variables"
    );
}

#[test]
fn test_vcgen_to_router_division_by_zero() {
    let func = division_function();

    // Step 1: Generate VCs
    let vcs = trust_vcgen::generate_vcs(&func);
    let div_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).collect();
    assert_eq!(div_vcs.len(), 1, "divide should produce 1 DivisionByZero VC");
    assert_eq!(div_vcs[0].function, "divide");

    // Step 2: Route through ConstantFolderBackend
    let router = mock_router();
    let result = router.verify_one(div_vcs[0]);
    // The formula contains variables so ConstantFolderBackend returns Unknown
    assert!(
        matches!(result, VerificationResult::Unknown { .. }),
        "mock backend should return Unknown for formula with variables"
    );
}

#[test]
fn test_vcgen_to_router_array_bounds() {
    let func = array_access_function();

    // Step 1: Generate VCs
    let vcs = trust_vcgen::generate_vcs(&func);
    let bounds_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds)).collect();
    assert_eq!(bounds_vcs.len(), 1, "lookup should produce 1 IndexOutOfBounds VC");
    assert_eq!(bounds_vcs[0].function, "lookup");
    assert_eq!(bounds_vcs[0].kind.proof_level(), ProofLevel::L0Safety);

    // Step 2: Route through ConstantFolderBackend
    let router = mock_router();
    let result = router.verify_one(bounds_vcs[0]);
    assert!(
        matches!(result, VerificationResult::Unknown { .. }),
        "mock backend should return Unknown for formula with variables"
    );
}

#[test]
fn test_vcgen_noop_produces_no_vcs() {
    let func = noop_function();
    let vcs = trust_vcgen::generate_vcs(&func);
    assert!(vcs.is_empty(), "noop function should produce 0 VCs");
}

// ---------------------------------------------------------------------------
// 2. Full pipeline: vcgen -> router -> report
// ---------------------------------------------------------------------------

#[test]
fn test_full_pipeline_midpoint_report() {
    let func = midpoint_function();

    // Step 1: Generate VCs
    let vcs = trust_vcgen::generate_vcs(&func);

    // Step 2: Route through ConstantFolderBackend
    let router = mock_router();
    let results = router.verify_all(&vcs);

    // Step 3: Build report
    let report = trust_report::build_json_report("midpoint_crate", &results);

    assert_eq!(report.crate_name, "midpoint_crate");
    assert_eq!(report.summary.functions_analyzed, 1);
    assert_eq!(report.summary.total_obligations, 1);
    assert!(report.functions[0].function == "get_midpoint");

    // Verify JSON serialization roundtrip
    let json = serde_json::to_string_pretty(&report).expect("serialize");
    let roundtrip: trust_types::JsonProofReport = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(roundtrip.crate_name, "midpoint_crate");
    assert_eq!(roundtrip.summary.total_obligations, 1);
}

#[test]
fn test_full_pipeline_division_report() {
    let func = division_function();

    let vcs = trust_vcgen::generate_vcs(&func);
    let router = mock_router();
    let results = router.verify_all(&vcs);
    let report = trust_report::build_json_report("arith_crate", &results);

    assert_eq!(report.crate_name, "arith_crate");
    assert!(report.summary.total_obligations >= 1);
    // Report should contain the divide function
    assert!(
        report.functions.iter().any(|f| f.function == "divide"),
        "report should contain the 'divide' function"
    );

    // Verify the text summary works
    let text = trust_report::format_json_summary(&report);
    assert!(text.contains("divide"), "text summary should mention 'divide'");
    assert!(text.contains("Verdict:"), "text summary should contain verdict");
}

#[test]
fn test_full_pipeline_with_proved_trivial_vc() {
    // Create a VC with a trivially false formula (mock proves it)
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "safe_div".into(),
        location: SourceSpan {
            file: "src/safe.rs".to_string(),
            line_start: 5,
            col_start: 1,
            line_end: 5,
            col_end: 20,
        },
        formula: Formula::Bool(false),
        contract_metadata: None,
        obligation: None,
    };

    let router = mock_router();
    let result = router.verify_one(&vc);
    assert!(result.is_proved(), "mock should prove trivially false formula");

    let results = vec![(vc.clone(), result)];
    let report = trust_report::build_json_report("safe_crate", &results);
    assert_eq!(report.summary.total_proved, 1);
    assert_eq!(report.summary.verdict, trust_types::CrateVerdict::Verified);

    let text = trust_report::format_json_summary(&report);
    assert!(text.contains("PROVED"));
    assert!(text.contains("Verdict: VERIFIED"));
}

#[test]
fn test_full_pipeline_multi_function_report() {
    let midpoint = midpoint_function();
    let divide = division_function();
    let lookup = array_access_function();

    let mut all_vcs = Vec::new();
    all_vcs.extend(trust_vcgen::generate_vcs(&midpoint));
    all_vcs.extend(trust_vcgen::generate_vcs(&divide));
    all_vcs.extend(trust_vcgen::generate_vcs(&lookup));

    assert!(all_vcs.len() >= 3, "3 functions should produce at least 3 VCs total");

    let router = mock_router();
    let results = router.verify_all(&all_vcs);
    let report = trust_report::build_json_report("multi_crate", &results);

    assert_eq!(report.summary.functions_analyzed, 3);
    assert!(report.summary.total_obligations >= 3);

    // All 3 function names should appear
    let func_names: Vec<&str> = report.functions.iter().map(|f| f.function.as_str()).collect();
    assert!(func_names.contains(&"get_midpoint"));
    assert!(func_names.contains(&"divide"));
    assert!(func_names.contains(&"lookup"));
}

// ---------------------------------------------------------------------------
// 3. Cache integration: hit/miss with pipeline results
// ---------------------------------------------------------------------------

#[test]
fn test_cache_miss_then_hit_with_vcgen() {
    let func = midpoint_function();
    let mut cache = trust_cache::VerificationCache::in_memory();

    // First lookup: miss
    let lookup = cache.lookup_function(&func, "");
    assert_eq!(lookup, trust_cache::CacheLookup::Miss);

    // Simulate verification and store result
    let vcs = trust_vcgen::generate_vcs(&func);
    cache.store_function(&func, FunctionVerdict::Verified, vcs.len(), vcs.len(), 0, 0, 0, "");

    // Second lookup: hit
    let lookup = cache.lookup_function(&func, "");
    match lookup {
        trust_cache::CacheLookup::Hit(entry) => {
            assert_eq!(entry.verdict, FunctionVerdict::Verified);
            assert_eq!(entry.total_obligations, 1);
        }
        trust_cache::CacheLookup::Miss => panic!("expected cache hit after store"),
    }

    assert_eq!(cache.hits(), 1);
    assert_eq!(cache.misses(), 1);
}

#[test]
fn test_cache_invalidation_on_body_change() {
    let func_v1 = midpoint_function();
    let mut cache = trust_cache::VerificationCache::in_memory();

    // Store v1
    cache.store_function(&func_v1, FunctionVerdict::Verified, 1, 1, 0, 0, 0, "");

    // Create v2 with modified body (different arg_count)
    let mut func_v2 = midpoint_function();
    func_v2.body.arg_count = 5;

    // Lookup v2: miss (body changed)
    let lookup = cache.lookup_function(&func_v2, "");
    assert_eq!(lookup, trust_cache::CacheLookup::Miss);
}

#[test]
fn test_cache_with_full_pipeline() {
    let funcs = vec![midpoint_function(), division_function(), array_access_function()];
    let mut cache = trust_cache::VerificationCache::in_memory();
    let router = mock_router();

    // First pass: all misses, verify and store
    for func in &funcs {
        assert_eq!(cache.lookup_function(func, ""), trust_cache::CacheLookup::Miss);

        let vcs = trust_vcgen::generate_vcs(func);
        let results = router.verify_all(&vcs);
        let proved = results.iter().filter(|(_, r)| r.is_proved()).count();
        let failed = results.iter().filter(|(_, r)| r.is_failed()).count();
        let unknown = results.len() - proved - failed;

        let verdict = if failed > 0 {
            FunctionVerdict::HasViolations
        } else if unknown > 0 {
            FunctionVerdict::Inconclusive
        } else {
            FunctionVerdict::Verified
        };

        cache.store_function(func, verdict, results.len(), proved, failed, unknown, 0, "");
    }

    // Second pass: all hits
    for func in &funcs {
        assert!(matches!(
            cache.lookup_function(func, ""),
            trust_cache::CacheLookup::Hit(_)
        ));
    }

    assert_eq!(cache.hits(), 3);
    assert_eq!(cache.misses(), 3);
    assert_eq!(cache.len(), 3);
}

// ---------------------------------------------------------------------------
// 4. Filter by level + routing combo
// ---------------------------------------------------------------------------

#[test]
fn test_filter_vcs_by_level_then_route() {
    let func = contract_function();
    let all_vcs = trust_vcgen::generate_vcs(&func);

    // Filter to L0 safety only (should exclude postcondition VCs)
    let l0_vcs = trust_vcgen::filter_vcs_by_level(all_vcs.clone(), ProofLevel::L0Safety);
    for vc in &l0_vcs {
        assert_eq!(
            vc.kind.proof_level(),
            ProofLevel::L0Safety,
            "all filtered VCs should be L0 safety"
        );
        assert!(
            !matches!(vc.kind, VcKind::Postcondition),
            "postcondition VCs should be filtered out at L0"
        );
    }

    // Route L0 VCs
    let router = mock_router();
    let l0_results = router.verify_all(&l0_vcs);
    let l0_report = trust_report::build_json_report("l0_only", &l0_results);
    assert!(
        l0_report
            .functions
            .iter()
            .all(|f| { f.obligations.iter().all(|o| o.proof_level == ProofLevel::L0Safety) }),
        "L0 report should only contain L0 obligations"
    );

    // Now route all VCs (including functional)
    let all_results = router.verify_all(&all_vcs);
    let full_report = trust_report::build_json_report("full", &all_results);
    assert!(
        full_report.summary.total_obligations >= l0_report.summary.total_obligations,
        "full report should have at least as many obligations as L0"
    );
}

// ---------------------------------------------------------------------------
// 5. Multi-backend dispatch
// ---------------------------------------------------------------------------

#[test]
fn test_multi_backend_dispatch_selects_appropriate_backend() {
    use trust_router::constant_folder::ConstantFolderBackend;

    // Pipeline-v2: TrustMcBackend/TrustWpBackend gated behind not(pipeline-v2).
    // Use IncrementalAYSession for L0, ConstantFolderBackend as fallback.
    let router = trust_router::Router::with_backends(vec![
        Box::new(require_ay()),
        Box::new(trust_router::ty_backend::TyBackend),
        Box::new(ConstantFolderBackend),
    ]);

    // L0 Safety VC
    let safety_vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "safe_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
        obligation: None,
    };

    let plan = router.backend_plan(&safety_vc);
    assert!(!plan.is_empty(), "L0 safety should have at least one backend in the plan",);

    // L1 Functional VC
    let functional_vc = VerificationCondition {
        kind: VcKind::Postcondition,
        function: "contract_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
        obligation: None,
    };

    let plan = router.backend_plan(&functional_vc);
    assert!(!plan.is_empty(), "should have at least one backend in the plan");

    // L2 Domain VC — should prefer ty (Temporal)
    let domain_vc = VerificationCondition {
        kind: VcKind::Temporal { property: "eventually done".to_string(), machine: None },
        function: "temporal_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
        obligation: None,
    };

    let plan = router.backend_plan(&domain_vc);
    assert_eq!(plan[0].name, "ty", "L2 domain should prefer ty");
}

// ---------------------------------------------------------------------------
// 7. Symex path constraints feed back to VCs
// ---------------------------------------------------------------------------

#[test]
fn test_symex_path_constraint_to_formula() {
    use trust_symex::{PathConstraint, SymbolicValue};

    // Build a path constraint: (x > 0) AND NOT(y == 0)
    let mut pc = PathConstraint::new();
    pc.add_constraint(
        SymbolicValue::BinOp(
            Box::new(SymbolicValue::Symbol("x".into())),
            BinOp::Gt,
            Box::new(SymbolicValue::Concrete(0)),
        ),
        true, // branch taken: x > 0
    );
    pc.add_constraint(
        SymbolicValue::BinOp(
            Box::new(SymbolicValue::Symbol("y".into())),
            BinOp::Eq,
            Box::new(SymbolicValue::Concrete(0)),
        ),
        false, // branch not taken: NOT(y == 0)
    );

    // Convert to Formula (same type used in VCs)
    let formula = pc.to_formula();

    // The formula should be an And of two clauses
    match &formula {
        Formula::And(clauses) => {
            assert_eq!(clauses.len(), 2, "should have 2 path constraints");
            // Second should be negated
            assert!(matches!(&clauses[1], Formula::Not(_)), "second clause should be negated");
        }
        _ => panic!("expected And formula from 2 path constraints, got: {formula:?}"),
    }

    // This formula can be used as a VC formula for solver dispatch
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "path constraint holds".to_string() },
        function: "symex_test".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    };

    let router = mock_router();
    let result = router.verify_one(&vc);
    // ConstantFolderBackend returns Unknown for complex formulas with variables
    assert!(
        matches!(result, VerificationResult::Unknown { .. }),
        "mock backend should return Unknown for symbolic path constraints"
    );
}

#[test]
fn test_symex_executor_block_coverage() {
    use trust_symex::SymbolicExecutor;

    let func = division_function();
    let mut executor = SymbolicExecutor::new(100);

    // Execute the single basic block
    let result = executor.execute_block(&func.body.blocks[0]);
    assert!(result.is_ok(), "executing a simple block should succeed");

    // Coverage should include block 0
    assert!(executor.coverage.contains(&0), "coverage should include block 0");

    // Path constraint should be updated (possibly empty for straight-line code)
    let formula = executor.path.to_formula();
    // Straight-line code produces no branch constraints, so formula is true
    assert!(
        matches!(formula, Formula::Bool(true)),
        "straight-line code should produce trivial path constraint"
    );
}

// ---------------------------------------------------------------------------
// 8. Report JSON structure validation
// ---------------------------------------------------------------------------

#[test]
fn test_report_json_schema_fields() {
    let func = midpoint_function();
    let vcs = trust_vcgen::generate_vcs(&func);
    let router = mock_router();
    let results = router.verify_all(&vcs);
    let report = trust_report::build_json_report("schema_test", &results);

    let json_value: serde_json::Value = serde_json::to_value(&report).expect("serialize to Value");

    // Top-level required fields
    assert!(json_value.get("metadata").is_some());
    assert!(json_value.get("crate_name").is_some());
    assert!(json_value.get("summary").is_some());
    assert!(json_value.get("functions").is_some());

    // Metadata fields
    let meta = &json_value["metadata"];
    assert!(meta.get("schema_version").is_some());
    assert!(meta.get("trust_version").is_some());
    assert!(meta.get("timestamp").is_some());
    assert!(meta.get("total_time_ms").is_some());

    // Summary fields
    let summary = &json_value["summary"];
    assert!(summary.get("verdict").is_some());
    assert!(summary.get("total_obligations").is_some());
    assert!(summary.get("total_proved").is_some());
    assert!(summary.get("total_failed").is_some());

    // Function fields
    let func_val = &json_value["functions"][0];
    assert!(func_val.get("function").is_some());
    assert!(func_val.get("summary").is_some());
    assert!(func_val.get("obligations").is_some());

    // Obligation fields
    let ob = &func_val["obligations"][0];
    assert!(ob.get("description").is_some());
    assert!(ob.get("kind").is_some());
    assert!(ob.get("proof_level").is_some());
    assert!(ob.get("outcome").is_some());
    assert!(ob.get("solver").is_some());
    assert!(ob.get("time_ms").is_some());
}

#[test]
fn test_report_ndjson_streaming() {
    let func = midpoint_function();
    let vcs = trust_vcgen::generate_vcs(&func);
    let router = mock_router();
    let results = router.verify_all(&vcs);
    let report = trust_report::build_json_report("ndjson_test", &results);

    let mut buf = Vec::new();
    trust_report::write_ndjson(&report, &mut buf).expect("write ndjson");
    let output = String::from_utf8(buf).expect("utf8");

    let lines: Vec<&str> = output.trim_end().split('\n').collect();
    // header + 1 function + footer = 3 lines
    assert_eq!(lines.len(), 3, "expected 3 NDJSON lines");

    // Each line must be valid JSON
    for (i, line) in lines.iter().enumerate() {
        let parsed: serde_json::Value =
            serde_json::from_str(line).unwrap_or_else(|e| panic!("line {i} not valid JSON: {e}"));
        assert!(parsed.get("record_type").is_some());
    }
}

// ---------------------------------------------------------------------------
// 9. Parallel verification
// ---------------------------------------------------------------------------

#[test]
fn test_parallel_verification_matches_sequential() {
    let midpoint = midpoint_function();
    let divide = division_function();
    let lookup = array_access_function();

    let mut all_vcs = Vec::new();
    all_vcs.extend(trust_vcgen::generate_vcs(&midpoint));
    all_vcs.extend(trust_vcgen::generate_vcs(&divide));
    all_vcs.extend(trust_vcgen::generate_vcs(&lookup));

    let router = mock_router();

    let seq_results = router.verify_all(&all_vcs);
    let par_results = router.verify_all_parallel(&all_vcs, 4);

    assert_eq!(seq_results.len(), par_results.len());

    // Same VCs, same solver names
    for (seq, par) in seq_results.iter().zip(par_results.iter()) {
        assert_eq!(seq.0.function, par.0.function);
        assert_eq!(seq.1.solver_name(), par.1.solver_name());
    }
}

// ---------------------------------------------------------------------------
// 10. Validated function produces typed error
// ---------------------------------------------------------------------------

#[test]
fn test_validate_function_empty_body() {
    let mut func = noop_function();
    func.body.blocks.clear(); // Make body empty

    let err = trust_vcgen::validate_function(&func);
    assert!(err.is_err());

    let try_result = trust_vcgen::try_generate_vcs(&func);
    assert!(try_result.is_err());
}

#[test]
fn test_validate_function_valid() {
    let func = midpoint_function();
    let result = trust_vcgen::validate_function(&func);
    assert!(result.is_ok());

    let vcs = trust_vcgen::try_generate_vcs(&func);
    assert!(vcs.is_ok());
    assert_eq!(vcs.unwrap().len(), 1);
}

// ---------------------------------------------------------------------------
// 11. Query cache (solver-level caching)
// ---------------------------------------------------------------------------

#[test]
fn test_query_cache_hit_miss() {
    use trust_cache::QueryCache;

    let mut qcache = QueryCache::new();

    // Create a VC to cache
    let vc = VerificationCondition {
        kind: VcKind::ArithmeticOverflow {
            op: trust_types::BinOp::Add,
            operand_tys: (
                trust_types::Ty::Int { width: 32, signed: true },
                trust_types::Ty::Int { width: 32, signed: true },
            ),
        },
        function: "test_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(42)),
        ),
        contract_metadata: None,
        obligation: None,
    };

    // Miss
    assert!(qcache.lookup(&vc).is_none());

    // Store a result
    let result = VerificationResult::Proved {
        solver: "ay".into(),
        time_ms: 5,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };
    qcache.insert(&vc, result.clone());

    // Hit
    let cached = qcache.lookup(&vc);
    assert!(cached.is_some());
    assert!(cached.unwrap().is_proved());

    let stats = qcache.stats();
    assert_eq!(stats.hits, 1);
    assert_eq!(stats.misses, 1);
}

// ---------------------------------------------------------------------------
// 12. End-to-end: vcgen -> filter -> route -> report with counterexample
// ---------------------------------------------------------------------------

#[test]
fn test_end_to_end_with_synthetic_counterexample() {
    // Simulate a full pipeline where ay finds a counterexample
    let func = midpoint_function();
    let vcs = trust_vcgen::generate_vcs(&func);

    // Simulate ay finding the overflow counterexample
    let results: Vec<(VerificationCondition, VerificationResult)> = vcs
        .into_iter()
        .map(|vc| {
            let result = VerificationResult::Failed {
                solver: "ay".into(),
                time_ms: 8,
                counterexample: Some(Counterexample::new(vec![
                    ("a".to_string(), CounterexampleValue::Uint(u64::MAX as u128)),
                    ("b".to_string(), CounterexampleValue::Uint(1)),
                ])),
            };
            (vc, result)
        })
        .collect();

    // Build report
    let report = trust_report::build_json_report("midpoint", &results);
    assert_eq!(report.summary.total_failed, 1);
    assert_eq!(report.summary.verdict, trust_types::CrateVerdict::HasViolations);

    // Verify counterexample appears in report
    let text = trust_report::format_json_summary(&report);
    assert!(text.contains("FAILED"));
    assert!(text.contains("counterexample"));
    assert!(text.contains("18446744073709551615")); // u64::MAX
}
