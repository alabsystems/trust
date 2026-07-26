// trust-integration-tests/tests/misc_vc_pipeline.rs: Pipeline-routing tests for miscellaneous
// L1 Functional VcKind variants
//
// Tests 5 VcKind variants with zero or unit-only coverage:
//   1. FunctionalCorrectness — zero pipeline coverage
//   2. TaintViolation — zero pipeline coverage
//   3. ResilienceViolation — zero pipeline coverage
//   4. NonTermination — unit tests only, no pipeline coverage
//   5. TranslationValidation — unit tests only, no pipeline coverage
//
// Each test: hand-construct VC -> route through Router (ConstantFolderBackend) -> verify proof_level
// classification (all L1Functional) -> verify description() in Report formatting.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_types::{
    Formula, ProofLevel, ProofStrength, Sort, SourceSpan, VcKind, VerificationCondition,
    VerificationResult,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// A router pinned to the deterministic `ConstantFolderBackend` only, so these
/// plumbing tests stay independent of workspace feature unification (which
/// otherwise registers the real in-process ay backend via `Router::new()`).
fn mock_router() -> trust_router::Router {
    trust_router::Router::with_backends(vec![Box::new(
        trust_router::constant_folder::ConstantFolderBackend,
    )])
}

/// Build a VC with the given kind, using a variable-containing formula so the
/// ConstantFolderBackend returns `Unknown` (variables prevent trivial evaluation).
fn make_vc(kind: VcKind, function: &str) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: function.into(),
        location: SourceSpan::default(),
        // Formula with a free variable — ConstantFolderBackend cannot decide this.
        formula: Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
        contract_metadata: None,
    }
}

/// Build a VC with a trivially false formula so ConstantFolderBackend proves it.
fn make_vc_trivial(kind: VcKind, function: &str) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: function.into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    }
}

// ===========================================================================
// 1. FunctionalCorrectness
// ===========================================================================

#[test]
fn test_functional_correctness_proof_level() {
    let kind = VcKind::FunctionalCorrectness {
        property: "result_correctness".to_string(),
        context: "binary_search: input not sorted".to_string(),
    };
    assert_eq!(kind.proof_level(), ProofLevel::L1Functional);
}

#[test]
fn test_functional_correctness_description() {
    let kind = VcKind::FunctionalCorrectness {
        property: "result_correctness".to_string(),
        context: "binary_search: input not sorted".to_string(),
    };
    let desc = kind.description();
    assert!(
        desc.contains("functional correctness"),
        "description should contain 'functional correctness', got: {desc}"
    );
    assert!(
        desc.contains("result_correctness"),
        "description should contain property name, got: {desc}"
    );
    assert!(desc.contains("binary_search"), "description should contain context, got: {desc}");
}

// NOTE: FunctionalCorrectness cannot be routed through Router::verify_one() because
// trust-router/src/termination_dispatch.rs:classify_property() lacks an arm for it
// (hits unreachable!). Tests below bypass the Router and construct results directly
// to verify the Report pipeline handles this VcKind correctly.

#[test]
fn test_functional_correctness_report_proved() {
    let vc = make_vc_trivial(
        VcKind::FunctionalCorrectness {
            property: "sort_order".to_string(),
            context: "output must be sorted".to_string(),
        },
        "sort_check",
    );

    // Bypass Router — construct a Proved result directly
    let result = VerificationResult::Proved {
        solver: "constant-folder".into(),
        time_ms: 1,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };
    let results = vec![(vc, result)];
    let report = trust_report::build_json_report("fc_crate", &results);

    assert_eq!(report.summary.total_obligations, 1);
    assert_eq!(report.summary.total_proved, 1);
    assert_eq!(report.functions.len(), 1);
    assert_eq!(report.functions[0].function, "sort_check");

    // Verify description appears in obligations
    let ob = &report.functions[0].obligations[0];
    assert_eq!(ob.proof_level, ProofLevel::L1Functional);
    assert!(
        ob.description.contains("functional correctness"),
        "obligation description should contain 'functional correctness', got: {}",
        ob.description
    );

    // Verify text summary
    let text = trust_report::format_json_summary(&report);
    assert!(text.contains("sort_check"), "summary should mention function name");
    assert!(text.contains("PROVED"), "summary should show proved status");
}

#[test]
fn test_functional_correctness_report_unknown() {
    let vc = make_vc(
        VcKind::FunctionalCorrectness {
            property: "result_correctness".to_string(),
            context: "input not validated".to_string(),
        },
        "check_correctness",
    );

    let result = VerificationResult::Unknown {
        solver: "constant-folder".into(),
        time_ms: 1,
        reason: "variable formula".to_string(),
    };
    let results = vec![(vc, result)];
    let report = trust_report::build_json_report("fc_unknown_crate", &results);

    assert_eq!(report.summary.total_obligations, 1);
    assert_eq!(report.summary.total_proved, 0);
    assert_eq!(report.functions[0].function, "check_correctness");

    let ob = &report.functions[0].obligations[0];
    assert_eq!(ob.proof_level, ProofLevel::L1Functional);
    assert!(
        ob.description.contains("functional correctness"),
        "obligation description should contain 'functional correctness', got: {}",
        ob.description
    );
}

// ===========================================================================
// 2. TaintViolation
// ===========================================================================

#[test]
fn test_taint_violation_proof_level() {
    let kind = VcKind::TaintViolation {
        source_label: "user_input".to_string(),
        sink_kind: "sql_query".to_string(),
        path_length: 3,
    };
    assert_eq!(kind.proof_level(), ProofLevel::L1Functional);
}

#[test]
fn test_taint_violation_description() {
    let kind = VcKind::TaintViolation {
        source_label: "user_input".to_string(),
        sink_kind: "sql_query".to_string(),
        path_length: 3,
    };
    let desc = kind.description();
    assert!(
        desc.contains("taint violation"),
        "description should contain 'taint violation', got: {desc}"
    );
    assert!(desc.contains("user_input"), "description should contain source label, got: {desc}");
    assert!(desc.contains("sql_query"), "description should contain sink kind, got: {desc}");
    assert!(desc.contains("3"), "description should contain path length, got: {desc}");
}

#[test]
fn test_taint_violation_router_unknown() {
    let vc = make_vc(
        VcKind::TaintViolation {
            source_label: "http_header".to_string(),
            sink_kind: "exec".to_string(),
            path_length: 5,
        },
        "handle_request",
    );

    let router = mock_router();
    let result = router.verify_one(&vc);
    assert!(
        matches!(result, VerificationResult::Unknown { .. }),
        "ConstantFolderBackend should return Unknown for variable formula, got: {result:?}"
    );
}

#[test]
fn test_taint_violation_report() {
    let vc = make_vc_trivial(
        VcKind::TaintViolation {
            source_label: "user_input".to_string(),
            sink_kind: "sql_query".to_string(),
            path_length: 2,
        },
        "sanitized_query",
    );

    let router = mock_router();
    let result = router.verify_one(&vc);
    let results = vec![(vc, result)];
    let report = trust_report::build_json_report("taint_crate", &results);

    assert_eq!(report.summary.total_obligations, 1);
    assert_eq!(report.summary.total_proved, 1);
    assert_eq!(report.functions[0].function, "sanitized_query");

    let ob = &report.functions[0].obligations[0];
    assert_eq!(ob.proof_level, ProofLevel::L1Functional);
    assert!(
        ob.description.contains("taint violation"),
        "obligation description should contain 'taint violation', got: {}",
        ob.description
    );

    let text = trust_report::format_json_summary(&report);
    assert!(text.contains("sanitized_query"), "summary should mention function name");
}

// ===========================================================================
// 3. ResilienceViolation
// ===========================================================================

#[test]
fn test_resilience_violation_proof_level() {
    let kind = VcKind::ResilienceViolation {
        service: "payment_service".to_string(),
        failure_mode: "timeout".to_string(),
        reason: "no retry logic".to_string(),
    };
    assert_eq!(kind.proof_level(), ProofLevel::L1Functional);
}

#[test]
fn test_resilience_violation_description() {
    let kind = VcKind::ResilienceViolation {
        service: "payment_service".to_string(),
        failure_mode: "timeout".to_string(),
        reason: "no retry logic".to_string(),
    };
    let desc = kind.description();
    assert!(desc.contains("resilience"), "description should contain 'resilience', got: {desc}");
    assert!(
        desc.contains("payment_service"),
        "description should contain service name, got: {desc}"
    );
    assert!(desc.contains("timeout"), "description should contain failure mode, got: {desc}");
    assert!(desc.contains("no retry logic"), "description should contain reason, got: {desc}");
}

#[test]
fn test_resilience_violation_router_unknown() {
    let vc = make_vc(
        VcKind::ResilienceViolation {
            service: "auth_service".to_string(),
            failure_mode: "connection_reset".to_string(),
            reason: "missing circuit breaker".to_string(),
        },
        "call_auth",
    );

    let router = mock_router();
    let result = router.verify_one(&vc);
    assert!(
        matches!(result, VerificationResult::Unknown { .. }),
        "ConstantFolderBackend should return Unknown for variable formula, got: {result:?}"
    );
}

#[test]
fn test_resilience_violation_report() {
    let vc = make_vc_trivial(
        VcKind::ResilienceViolation {
            service: "cache_service".to_string(),
            failure_mode: "eviction".to_string(),
            reason: "fallback to source".to_string(),
        },
        "resilient_cache_get",
    );

    let router = mock_router();
    let result = router.verify_one(&vc);
    let results = vec![(vc, result)];
    let report = trust_report::build_json_report("resilience_crate", &results);

    assert_eq!(report.summary.total_obligations, 1);
    assert_eq!(report.summary.total_proved, 1);
    assert_eq!(report.functions[0].function, "resilient_cache_get");

    let ob = &report.functions[0].obligations[0];
    assert_eq!(ob.proof_level, ProofLevel::L1Functional);
    assert!(
        ob.description.contains("resilience"),
        "obligation description should contain 'resilience', got: {}",
        ob.description
    );

    let text = trust_report::format_json_summary(&report);
    assert!(text.contains("resilient_cache_get"), "summary should mention function name");
}

// ===========================================================================
// 4. NonTermination
// ===========================================================================

#[test]
fn test_non_termination_proof_level() {
    let kind = VcKind::NonTermination { context: "loop".to_string(), measure: "n".to_string() };
    assert_eq!(kind.proof_level(), ProofLevel::L1Functional);
}

#[test]
fn test_non_termination_description() {
    let kind =
        VcKind::NonTermination { context: "recursion".to_string(), measure: "len - i".to_string() };
    let desc = kind.description();
    assert!(
        desc.contains("non-termination"),
        "description should contain 'non-termination', got: {desc}"
    );
    assert!(desc.contains("recursion"), "description should contain context, got: {desc}");
    assert!(desc.contains("len - i"), "description should contain measure, got: {desc}");
}

#[test]
fn test_non_termination_router_unknown() {
    let vc = make_vc(
        VcKind::NonTermination { context: "loop".to_string(), measure: "counter".to_string() },
        "infinite_loop",
    );

    let router = mock_router();
    let result = router.verify_one(&vc);
    assert!(
        matches!(result, VerificationResult::Unknown { .. }),
        "ConstantFolderBackend should return Unknown for variable formula, got: {result:?}"
    );
}

#[test]
fn test_non_termination_report() {
    let vc = make_vc_trivial(
        VcKind::NonTermination { context: "loop".to_string(), measure: "items.len()".to_string() },
        "drain_loop",
    );

    let router = mock_router();
    let result = router.verify_one(&vc);
    let results = vec![(vc, result)];
    let report = trust_report::build_json_report("termination_crate", &results);

    assert_eq!(report.summary.total_obligations, 1);
    assert_eq!(report.summary.total_proved, 1);
    assert_eq!(report.functions[0].function, "drain_loop");

    let ob = &report.functions[0].obligations[0];
    assert_eq!(ob.proof_level, ProofLevel::L1Functional);
    assert!(
        ob.description.contains("non-termination"),
        "obligation description should contain 'non-termination', got: {}",
        ob.description
    );

    let text = trust_report::format_json_summary(&report);
    assert!(text.contains("drain_loop"), "summary should mention function name");
}

// ===========================================================================
// 5. TranslationValidation
// ===========================================================================

#[test]
fn test_translation_validation_proof_level() {
    let kind = VcKind::TranslationValidation {
        pass: "constant_folding".to_string(),
        check: "output equivalence".to_string(),
    };
    assert_eq!(kind.proof_level(), ProofLevel::L1Functional);
}

#[test]
fn test_translation_validation_description() {
    let kind = VcKind::TranslationValidation {
        pass: "dce".to_string(),
        check: "side-effect preservation".to_string(),
    };
    let desc = kind.description();
    assert!(
        desc.contains("translation validation"),
        "description should contain 'translation validation', got: {desc}"
    );
    assert!(desc.contains("dce"), "description should contain pass name, got: {desc}");
    assert!(
        desc.contains("side-effect preservation"),
        "description should contain check description, got: {desc}"
    );
}

#[test]
fn test_translation_validation_router_unknown() {
    let vc = make_vc(
        VcKind::TranslationValidation {
            pass: "inlining".to_string(),
            check: "call semantics preserved".to_string(),
        },
        "inline_small_fn",
    );

    let router = mock_router();
    let result = router.verify_one(&vc);
    assert!(
        matches!(result, VerificationResult::Unknown { .. }),
        "ConstantFolderBackend should return Unknown for variable formula, got: {result:?}"
    );
}

#[test]
fn test_translation_validation_report() {
    let vc = make_vc_trivial(
        VcKind::TranslationValidation {
            pass: "constant_folding".to_string(),
            check: "output equivalence".to_string(),
        },
        "fold_constants",
    );

    let router = mock_router();
    let result = router.verify_one(&vc);
    let results = vec![(vc, result)];
    let report = trust_report::build_json_report("tv_crate", &results);

    assert_eq!(report.summary.total_obligations, 1);
    assert_eq!(report.summary.total_proved, 1);
    assert_eq!(report.functions[0].function, "fold_constants");

    let ob = &report.functions[0].obligations[0];
    assert_eq!(ob.proof_level, ProofLevel::L1Functional);
    assert!(
        ob.description.contains("translation validation"),
        "obligation description should contain 'translation validation', got: {}",
        ob.description
    );

    let text = trust_report::format_json_summary(&report);
    assert!(text.contains("fold_constants"), "summary should mention function name");
}

// ===========================================================================
// 6. Cross-cutting: all 5 VcKinds in a single pipeline run
// ===========================================================================

#[test]
fn test_all_five_misc_vcs_multi_function_report() {
    // Route 4 VcKinds through the Router (FunctionalCorrectness excluded —
    // classify_property() in trust-router lacks an arm for it).
    let routable_vcs = vec![
        make_vc_trivial(
            VcKind::TaintViolation {
                source_label: "env_var".to_string(),
                sink_kind: "file_path".to_string(),
                path_length: 1,
            },
            "taint_fn",
        ),
        make_vc_trivial(
            VcKind::ResilienceViolation {
                service: "db".to_string(),
                failure_mode: "disconnect".to_string(),
                reason: "reconnect logic".to_string(),
            },
            "resilience_fn",
        ),
        make_vc_trivial(
            VcKind::NonTermination { context: "loop".to_string(), measure: "fuel".to_string() },
            "termination_fn",
        ),
        make_vc_trivial(
            VcKind::TranslationValidation {
                pass: "mem2reg".to_string(),
                check: "load-store equivalence".to_string(),
            },
            "tv_fn",
        ),
    ];

    let router = mock_router();
    let mut results = router.verify_all(&routable_vcs);

    // Add FunctionalCorrectness with a directly-constructed Proved result
    // (Router::verify_one panics on this variant — see note in section 1)
    let fc_vc = make_vc_trivial(
        VcKind::FunctionalCorrectness {
            property: "output".to_string(),
            context: "identity".to_string(),
        },
        "fc_fn",
    );
    let fc_result = VerificationResult::Proved {
        solver: "constant-folder".into(),
        time_ms: 1,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    };
    results.push((fc_vc, fc_result));

    assert_eq!(results.len(), 5);

    // All should be L1Functional
    for (vc, _) in &results {
        assert_eq!(
            vc.kind.proof_level(),
            ProofLevel::L1Functional,
            "VC kind {:?} should be L1Functional",
            vc.kind
        );
    }

    // All should be proved
    for (vc, result) in &results {
        assert!(result.is_proved(), "should be proved for {}: {result:?}", vc.function);
    }

    let report = trust_report::build_json_report("misc_l1_crate", &results);
    assert_eq!(report.summary.functions_analyzed, 5);
    assert_eq!(report.summary.total_obligations, 5);
    assert_eq!(report.summary.total_proved, 5);

    // All function names should appear
    let func_names: Vec<&str> = report.functions.iter().map(|f| f.function.as_str()).collect();
    assert!(func_names.contains(&"fc_fn"));
    assert!(func_names.contains(&"taint_fn"));
    assert!(func_names.contains(&"resilience_fn"));
    assert!(func_names.contains(&"termination_fn"));
    assert!(func_names.contains(&"tv_fn"));

    // All obligations should be L1Functional
    for func_report in &report.functions {
        for ob in &func_report.obligations {
            assert_eq!(
                ob.proof_level,
                ProofLevel::L1Functional,
                "obligation in {} should be L1Functional",
                func_report.function
            );
        }
    }

    // Verify JSON serialization roundtrip
    let json = serde_json::to_string_pretty(&report).expect("serialize");
    let roundtrip: trust_types::JsonProofReport = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(roundtrip.summary.total_obligations, 5);
    assert_eq!(roundtrip.summary.total_proved, 5);

    // Verify text summary mentions all function names
    let text = trust_report::format_json_summary(&report);
    assert!(text.contains("fc_fn"));
    assert!(text.contains("taint_fn"));
    assert!(text.contains("resilience_fn"));
    assert!(text.contains("termination_fn"));
    assert!(text.contains("tv_fn"));
}
