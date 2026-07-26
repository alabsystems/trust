//! Tests for the Router and backend selection logic.

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use trust_types::*;

use crate::*;

fn assert_proved_artifacts(
    result: &VerificationResult,
    expected_solver: &str,
    expected_certificate: &[u8],
    expected_warnings: &[&str],
) {
    match result {
        VerificationResult::Proved { solver, proof_certificate, solver_warnings, .. } => {
            assert_eq!(solver.as_str(), expected_solver);
            assert_eq!(proof_certificate.as_deref(), Some(expected_certificate));
            let actual_warnings = solver_warnings
                .as_ref()
                .map(|warnings| warnings.iter().map(String::as_str).collect::<Vec<_>>());
            assert_eq!(actual_warnings.as_deref(), Some(expected_warnings));
        }
        other => panic!("expected proved evidence from {expected_solver}, got {other:?}"),
    }
}

#[test]
fn test_router_with_constant_folder() {
    let router = Router::with_backends(vec![Box::new(constant_folder::ConstantFolderBackend)]);

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let result = router.verify_one(&vc);
    assert!(result.is_proved() || result.is_failed());
}

#[test]
fn test_unsupported_mir_is_unknown_even_with_trivial_formula() {
    let vc = VerificationCondition {
        kind: VcKind::UnsupportedMir {
            kind: "TerminatorKind::Yield".to_string(),
            detail: "valid MIR terminator preserved as opaque TrustIr".to_string(),
        },
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let router = Router::with_backends(vec![Box::new(constant_folder::ConstantFolderBackend)]);
    assert!(
        matches!(router.verify_one(&vc), VerificationResult::Unknown { reason, .. } if reason.contains("unsupported MIR"))
    );

    let backend = constant_folder::ConstantFolderBackend;
    assert!(
        matches!(backend.verify(&vc), VerificationResult::Unknown { reason, .. } if reason.contains("unsupported MIR"))
    );
}

#[test]
fn test_aarch64_atomic_unsupported_mir_is_classified_and_reported() {
    let detail = "opcode=ldar; proof obligation: consume AArch64 acquire ordering event, synchronization edge, thread identity, and happens-before witness; access=Read; ordering=Acquire; exclusive_monitor=None; reports_status=false";
    let vc = VerificationCondition {
        kind: VcKind::UnsupportedMir {
            kind: "AArch64AtomicSemanticFactNotProofConsumed".to_string(),
            detail: detail.to_string(),
        },
        function: "aarch64_atomic".into(),
        location: SourceSpan::binary_address(0x2230),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let router = Router::with_backends(vec![Box::new(constant_folder::ConstantFolderBackend)]);
    assert!(
        router.backend_plan(&vc).is_empty(),
        "unsupported atomic metadata must not be dispatched to a solver backend"
    );
    let result = router.verify_one(&vc);
    assert!(
        matches!(
            &result,
            VerificationResult::Unknown { reason, .. }
                if reason.contains("aarch64_atomic_acquire_ordering_unsupported")
                    && reason.contains("happens-before witness")
                    && reason.contains("exclusive_monitor=None")
        ),
        "router must preserve atomic ordering witness detail in the fail-closed reason: {result:?}"
    );

    let report = trust_report::build_json_report("atomic_router", &[(vc, result)]);
    let obligation = &report.functions[0].obligations[0];
    assert_eq!(obligation.kind, "aarch64_atomic_acquire_ordering_unsupported");
    assert!(obligation.description.contains("synchronization edge"));
    assert!(matches!(
        &obligation.outcome,
        ObligationOutcome::Unknown { reason }
            if reason.contains("aarch64_atomic_acquire_ordering_unsupported")
    ));
}

#[test]
fn test_source_backpropagation_gate_blockers_are_classified_and_reported() {
    let labels = [
        "missing_reconstruction",
        "exact_source_provenance",
        "target_validation",
        "checked_certificate_identity",
        "replay_identity",
    ];
    let vcs = labels
        .iter()
        .enumerate()
        .map(|(idx, label)| VerificationCondition {
            kind: VcKind::UnsupportedMir {
                kind: "SourceBackpropagationGateBlocker".to_string(),
                detail: format!(
                    "source_backpropagation_gate label={label}; source backpropagation evidence `{label}` is missing"
                ),
            },
            function: "source_backprop".into(),
            location: SourceSpan::binary_address(0x401000 + (idx as u64) * 4),
            formula: Formula::Bool(false),
            contract_metadata: None,
        })
        .collect::<Vec<_>>();

    let router = Router::with_backends(vec![Box::new(constant_folder::ConstantFolderBackend)]);
    assert!(
        vcs.iter().all(|vc| router.backend_plan(vc).is_empty()),
        "source backpropagation gate blockers must remain fail-closed and bypass solver dispatch"
    );
    let results = router.verify_all(&vcs);
    for ((_, result), label) in results.iter().zip(labels) {
        assert!(
            matches!(
                result,
                VerificationResult::Unknown { reason, .. }
                    if reason.contains("SourceBackpropagationGateBlocker")
                        && reason.contains(label)
            ),
            "router must preserve source-backpropagation gate label `{label}`: {result:?}"
        );
    }

    let report = trust_report::build_json_report("source_backprop_router", &results);
    let obligations = &report.functions[0].obligations;
    let kinds = obligations.iter().map(|obligation| obligation.kind.as_str()).collect::<Vec<_>>();

    assert_eq!(
        kinds,
        vec![
            "source_backpropagation_missing_reconstruction",
            "source_backpropagation_exact_source_provenance",
            "source_backpropagation_target_validation",
            "source_backpropagation_checked_certificate_identity",
            "source_backpropagation_replay_identity",
        ]
    );
    assert!(obligations.iter().zip(labels).all(|(obligation, label)| {
        obligation.description.contains(label)
            && matches!(
                &obligation.outcome,
                ObligationOutcome::Unknown { reason } if reason.contains(label)
            )
    }));
}

#[test]
fn test_source_backpropagation_gate_hyphenated_disabled_reasons_are_classified() {
    let cases = [
        (
            "checked-certificate identity is missing from manifest-backed coverage",
            "source_backpropagation_checked_certificate_identity",
        ),
        (
            "replay byte/range identity is missing from source-backprop replay readiness",
            "source_backpropagation_replay_identity",
        ),
        (
            "checked proof-cert readback row accepted for proof-grade release; manifest_identity_sha256=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa; source_backpropagation_gate_sha256=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
            "source_backpropagation_checked_certificate_identity",
        ),
        (
            "source-backprop requires machine-effect witnesses consumed for every replayed instruction step: machine-code replay backend omitted memory_write effect witness memory_access#0:8B; concrete scalar memory address/width evidence is required",
            "source_backpropagation_replay_identity",
        ),
        (
            "trust-cg target proof consumer consumed binary proof inputs, but binary-proof-obligation-pending-refinement-metadata remains; bidirectional refinement metadata is missing",
            "source_backpropagation_target_validation",
        ),
    ];
    let vcs = cases
        .iter()
        .enumerate()
        .map(|(idx, (detail, _))| VerificationCondition {
            kind: VcKind::UnsupportedMir {
                kind: "SourceBackpropagationGateBlocker".to_string(),
                detail: format!("source-backpropagation disabled: {detail}"),
            },
            function: "source_backprop".into(),
            location: SourceSpan::binary_address(0x401100 + (idx as u64) * 4),
            formula: Formula::Bool(false),
            contract_metadata: None,
        })
        .collect::<Vec<_>>();

    let router = Router::with_backends(vec![Box::new(constant_folder::ConstantFolderBackend)]);
    let results = router.verify_all(&vcs);
    for ((_, result), (_, expected)) in results.iter().zip(cases) {
        assert!(
            matches!(
                result,
                VerificationResult::Unknown { reason, .. } if reason.contains(expected)
            ),
            "router must classify hyphenated source-backprop disabled reason as `{expected}`: {result:?}"
        );
    }

    let report = trust_report::build_json_report("source_backprop_router_hyphenated", &results);
    let kinds = report.functions[0]
        .obligations
        .iter()
        .map(|obligation| obligation.kind.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        kinds,
        vec![
            "source_backpropagation_checked_certificate_identity",
            "source_backpropagation_replay_identity",
            "source_backpropagation_checked_certificate_identity",
            "source_backpropagation_replay_identity",
            "source_backpropagation_target_validation",
        ]
    );
}

#[test]
fn test_source_backpropagation_missing_contract_consumers_remain_blocked() {
    let cases = [
        (
            "source-backprop blocked: exact source/type-fact ownership is missing; recovered source span has no bridge-owned type-fact owner",
            "source_backpropagation_type_ownership",
            "type-fact owner",
        ),
        (
            "source-backprop blocked: replay attestation is missing; no replay backend attested byte/range identity or step witnesses for this source range",
            "source_backpropagation_replay_identity",
            "replay attestation",
        ),
        (
            "source-backprop blocked: certificate identity is missing; checked production proof certificate identity was not bound to the source-backprop gate",
            "source_backpropagation_checked_certificate_identity",
            "certificate identity",
        ),
        (
            "source-backprop blocked: target/formula consumers are missing; preserved trust_symbolic.formula payloads have no target proof consumer",
            "source_backpropagation_target_validation",
            "target/formula consumers",
        ),
    ];
    let vcs = cases
        .iter()
        .enumerate()
        .map(|(idx, (detail, _, _))| VerificationCondition {
            kind: VcKind::UnsupportedMir {
                kind: "SourceBackpropagationGateBlocker".to_string(),
                detail: (*detail).to_string(),
            },
            function: "source_backprop_contract".into(),
            location: SourceSpan::binary_address(0x401200 + (idx as u64) * 4),
            formula: Formula::Bool(false),
            contract_metadata: None,
        })
        .collect::<Vec<_>>();

    let router = Router::with_backends(vec![Box::new(constant_folder::ConstantFolderBackend)]);
    assert!(
        vcs.iter().all(|vc| router.backend_plan(vc).is_empty()),
        "source-backprop contract blockers must bypass solver dispatch"
    );

    let results = router.verify_all(&vcs);
    for ((_, result), (_, expected, marker)) in results.iter().zip(cases) {
        assert!(
            !result.is_proved()
                && matches!(
                    result,
                    VerificationResult::Unknown { reason, .. }
                        if reason.contains(expected)
                            && reason.contains(marker)
                            && reason.contains("SourceBackpropagationGateBlocker")
                ),
            "source-backprop blocker must stay unknown as `{expected}`: {result:?}"
        );
    }

    let report = trust_report::build_json_report("source_backprop_contract", &results);
    assert_eq!(report.summary.total_unknown, cases.len());
    let obligations = &report.functions[0].obligations;
    assert_eq!(obligations.len(), cases.len());
    for (obligation, (detail, expected, marker)) in obligations.iter().zip(cases) {
        assert_eq!(obligation.kind, expected);
        assert!(obligation.description.contains(marker));
        assert!(obligation.description.contains(detail));
        assert!(obligation.proof_evidence.is_none());
        assert!(matches!(
            &obligation.outcome,
            ObligationOutcome::Unknown { reason }
                if reason.contains(expected)
                    && reason.contains(marker)
                    && reason.contains("SourceBackpropagationGateBlocker")
        ));
    }
}

#[test]
fn test_symbolic_formula_consumer_blocker_is_classified_and_reported() {
    let detail = "trust_symbolic.formula location=bb0[1].rvalue; structured formula payload is preserved but no schema-aware proof consumer accepted it; rejecting instead of lowering to Undef";
    let vc = VerificationCondition {
        kind: VcKind::UnsupportedMir {
            kind: "TrustSymbolicFormulaNotProofConsumed".to_string(),
            detail: detail.to_string(),
        },
        function: "binary::symbolic_formula".into(),
        location: SourceSpan::binary_address(0x401030),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let router = Router::with_backends(vec![Box::new(constant_folder::ConstantFolderBackend)]);
    assert!(
        router.backend_plan(&vc).is_empty(),
        "unconsumed symbolic formulas must not be discharged by solver dispatch"
    );

    let result = router.verify_one(&vc);
    assert!(
        matches!(
            &result,
            VerificationResult::Unknown { reason, .. }
                if reason.contains("trust_symbolic_formula_not_consumed")
                    && reason.contains("trust_symbolic.formula")
                    && reason.contains("rejecting instead of lowering to Undef")
        ),
        "router must surface the symbolic-formula consumer blocker: {result:?}"
    );

    let report = trust_report::build_json_report("symbolic_formula_router", &[(vc, result)]);
    let obligation = &report.functions[0].obligations[0];
    assert_eq!(obligation.kind, "trust_symbolic_formula_not_consumed");
    assert!(obligation.description.contains("trust_symbolic.formula"));
    assert!(matches!(
        &obligation.outcome,
        ObligationOutcome::Unknown { reason }
            if reason.contains("trust_symbolic_formula_not_consumed")
                && reason.contains("Undef")
    ));
}

#[test]
fn test_router_verify_all() {
    let router = Router::with_backends(vec![Box::new(constant_folder::ConstantFolderBackend)]);

    let vcs = vec![
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        },
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        },
    ];

    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), 2);
}

#[test]
fn test_router_verify_all_parallel() {
    let router = Router::with_backends(vec![Box::new(constant_folder::ConstantFolderBackend)]);

    let vcs: Vec<_> = (0..8)
        .map(|i| VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: format!("fn_{i}").into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        })
        .collect();

    let results = router.verify_all_parallel(&vcs, 4);
    assert_eq!(results.len(), 8);
    for (_, result) in &results {
        assert!(result.is_proved());
    }
}

#[test]
fn test_router_verify_all_parallel_fallback_single() {
    let router = Router::new();
    let vcs = vec![VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    }];

    // Single VC should use sequential path
    let results = router.verify_all_parallel(&vcs, 4);
    assert_eq!(results.len(), 1);
}

#[test]
fn test_router_verify_all_parallel_panics_preserve_one_result_per_vc() {
    struct PanickingBackend;

    impl VerificationBackend for PanickingBackend {
        fn name(&self) -> &str {
            "panicking"
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            panic!("intentional router isolation test panic");
        }
    }

    let router = Router::with_backends(vec![Box::new(PanickingBackend)]);
    let vcs: Vec<_> = (0..6)
        .map(|i| VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: format!("panic_fn_{i}").into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        })
        .collect();

    let results = router.verify_all_parallel(&vcs, 3);

    assert_eq!(results.len(), vcs.len());
    assert!(
        results.iter().all(|(_, result)| {
            matches!(
                result,
                VerificationResult::Unknown { solver, reason, .. }
                    if solver.as_str() == "router-parallel" && reason.contains("panicked")
            )
        }),
        "panicking workers must fail closed per VC: {results:?}"
    );
}

#[test]
fn test_router_with_arc_backends() {
    let backends: Vec<Arc<dyn VerificationBackend>> =
        vec![Arc::new(constant_folder::ConstantFolderBackend)];
    let router = Router::with_arc_backends(backends);

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };
    assert!(router.verify_one(&vc).is_proved());
}

#[test]
fn test_router_arc_backends_accessor() {
    let router = Router::new();
    let arcs = router.arc_backends();
    assert_eq!(arcs[0].name(), "constant-folder");
    // The `ay-backend` feature (off by default) registers the in-process ay
    // backend alongside the constant folder, so the count is feature-dependent.
    #[cfg(feature = "ay-backend")]
    assert_eq!(arcs.len(), 2, "ay-backend registers the in-process ay backend too");
    #[cfg(not(feature = "ay-backend"))]
    assert_eq!(arcs.len(), 1);
}

#[test]
fn test_backend_plan_prefers_solver_family_before_fallback() {
    struct PreferredBackend;
    struct FallbackBackend;

    impl VerificationBackend for PreferredBackend {
        fn name(&self) -> &str {
            "preferred"
        }

        fn role(&self) -> BackendRole {
            BackendRole::SmtSolver
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Proved {
                solver: "preferred".into(),
                time_ms: 0,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            }
        }
    }

    impl VerificationBackend for FallbackBackend {
        fn name(&self) -> &str {
            "fallback"
        }

        fn role(&self) -> BackendRole {
            BackendRole::General
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Failed {
                solver: "fallback".into(),
                time_ms: 0,
                counterexample: None,
            }
        }
    }

    let router = Router::with_backends(vec![Box::new(FallbackBackend), Box::new(PreferredBackend)]);
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let plan = router.backend_plan(&vc);
    assert_eq!(plan[0].name, "preferred");
    assert_eq!(plan[0].role, BackendRole::SmtSolver);
    assert!(plan[0].can_handle);
    assert_eq!(plan[1].name, "fallback");

    let result = router.verify_one(&vc);
    assert!(result.is_proved());
    assert_eq!(result.solver_name(), "preferred");
}

#[test]
fn test_verify_one_falls_back_after_unknown() {
    struct UnknownBackend {
        calls: Arc<AtomicUsize>,
    }
    struct ProvingBackend {
        calls: Arc<AtomicUsize>,
    }

    impl VerificationBackend for UnknownBackend {
        fn name(&self) -> &str {
            "unknown-primary"
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            self.calls.fetch_add(1, Ordering::SeqCst);
            VerificationResult::Unknown {
                solver: "unknown-primary".into(),
                time_ms: 1,
                reason: "inconclusive".to_string(),
            }
        }
    }

    impl VerificationBackend for ProvingBackend {
        fn name(&self) -> &str {
            "proving-fallback"
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            self.calls.fetch_add(1, Ordering::SeqCst);
            VerificationResult::Proved {
                solver: "proving-fallback".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            }
        }
    }

    let unknown_calls = Arc::new(AtomicUsize::new(0));
    let proving_calls = Arc::new(AtomicUsize::new(0));
    let router = Router::with_backends(vec![
        Box::new(UnknownBackend { calls: unknown_calls.clone() }),
        Box::new(ProvingBackend { calls: proving_calls.clone() }),
    ]);
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "fallback_unknown".into(),
        location: SourceSpan::default(),
        formula: Formula::Var("x".into(), Sort::Bool),
        contract_metadata: None,
    };

    let result = router.verify_one(&vc);

    assert!(result.is_proved(), "later backend should prove after Unknown: {result:?}");
    assert_eq!(result.solver_name(), "proving-fallback");
    assert_eq!(unknown_calls.load(Ordering::SeqCst), 1);
    assert_eq!(proving_calls.load(Ordering::SeqCst), 1);
}

#[test]
fn test_verify_one_falls_back_after_timeout() {
    struct TimeoutBackend {
        calls: Arc<AtomicUsize>,
    }
    struct ProvingBackend {
        calls: Arc<AtomicUsize>,
    }

    impl VerificationBackend for TimeoutBackend {
        fn name(&self) -> &str {
            "timeout-primary"
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            self.calls.fetch_add(1, Ordering::SeqCst);
            VerificationResult::Timeout { solver: "timeout-primary".into(), timeout_ms: 10 }
        }
    }

    impl VerificationBackend for ProvingBackend {
        fn name(&self) -> &str {
            "timeout-fallback"
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            self.calls.fetch_add(1, Ordering::SeqCst);
            VerificationResult::Proved {
                solver: "timeout-fallback".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            }
        }
    }

    let timeout_calls = Arc::new(AtomicUsize::new(0));
    let proving_calls = Arc::new(AtomicUsize::new(0));
    let router = Router::with_backends(vec![
        Box::new(TimeoutBackend { calls: timeout_calls.clone() }),
        Box::new(ProvingBackend { calls: proving_calls.clone() }),
    ]);
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "fallback_timeout".into(),
        location: SourceSpan::default(),
        formula: Formula::Var("x".into(), Sort::Bool),
        contract_metadata: None,
    };

    let result = router.verify_one(&vc);

    assert!(result.is_proved(), "later backend should prove after Timeout: {result:?}");
    assert_eq!(result.solver_name(), "timeout-fallback");
    assert_eq!(timeout_calls.load(Ordering::SeqCst), 1);
    assert_eq!(proving_calls.load(Ordering::SeqCst), 1);
}

#[test]
fn test_verify_one_stops_after_failed() {
    struct FailingBackend {
        calls: Arc<AtomicUsize>,
    }
    struct LaterBackend {
        calls: Arc<AtomicUsize>,
    }

    impl VerificationBackend for FailingBackend {
        fn name(&self) -> &str {
            "failing-primary"
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            self.calls.fetch_add(1, Ordering::SeqCst);
            VerificationResult::Failed {
                solver: "failing-primary".into(),
                time_ms: 1,
                counterexample: None,
            }
        }
    }

    impl VerificationBackend for LaterBackend {
        fn name(&self) -> &str {
            "later"
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            self.calls.fetch_add(1, Ordering::SeqCst);
            VerificationResult::Proved {
                solver: "later".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            }
        }
    }

    let failing_calls = Arc::new(AtomicUsize::new(0));
    let later_calls = Arc::new(AtomicUsize::new(0));
    let router = Router::with_backends(vec![
        Box::new(FailingBackend { calls: failing_calls.clone() }),
        Box::new(LaterBackend { calls: later_calls.clone() }),
    ]);
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "failed_stops".into(),
        location: SourceSpan::default(),
        formula: Formula::Var("x".into(), Sort::Bool),
        contract_metadata: None,
    };

    let result = router.verify_one(&vc);

    assert!(result.is_failed(), "Failed should remain terminal: {result:?}");
    assert_eq!(result.solver_name(), "failing-primary");
    assert_eq!(failing_calls.load(Ordering::SeqCst), 1);
    assert_eq!(later_calls.load(Ordering::SeqCst), 0);
}

#[test]
fn test_fallback_proof_artifacts_survive_materialized_dispatch_paths() {
    struct UnknownBackend;
    struct EvidenceBackend;

    impl VerificationBackend for UnknownBackend {
        fn name(&self) -> &str {
            "unknown-primary"
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Unknown {
                solver: "unknown-primary".into(),
                time_ms: 1,
                reason: "inconclusive".to_string(),
            }
        }
    }

    impl VerificationBackend for EvidenceBackend {
        fn name(&self) -> &str {
            "evidence-fallback"
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Proved {
                solver: "evidence-fallback".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: Some(vec![9, 8, 7]),
                solver_warnings: Some(vec!["fallback warning".to_string()]),
                native_proof_envelope: None,
            }
        }
    }

    let router = Router::with_backends(vec![Box::new(UnknownBackend), Box::new(EvidenceBackend)]);
    let vcs: Vec<_> = (0..4)
        .map(|i| VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: format!("fallback_artifacts_{i}").into(),
            location: SourceSpan::default(),
            formula: Formula::Var("x".into(), Sort::Bool),
            contract_metadata: None,
        })
        .collect();

    assert_proved_artifacts(
        &router.verify_one(&vcs[0]),
        "evidence-fallback",
        &[9, 8, 7],
        &["fallback warning"],
    );

    let sequential_results = router.verify_all(&vcs);
    assert_eq!(sequential_results.len(), vcs.len());
    for (_, result) in &sequential_results {
        assert_proved_artifacts(result, "evidence-fallback", &[9, 8, 7], &["fallback warning"]);
    }

    let parallel_results = router.verify_all_parallel(&vcs, 2);
    assert_eq!(parallel_results.len(), vcs.len());
    for (_, result) in &parallel_results {
        assert_proved_artifacts(result, "evidence-fallback", &[9, 8, 7], &["fallback warning"]);
    }
}

// -----------------------------------------------------------------------
// validate_dispatch integration tests
// -----------------------------------------------------------------------

#[test]
fn test_validate_dispatch_blocks_safety_solver_for_termination_vc() {
    // A backend named "pdr" claims can_handle=true for all VCs,
    // but validate_dispatch must block it for NonTermination because PDR
    // only proves safety (AG !bad), not termination.
    struct PdrBackend;

    impl VerificationBackend for PdrBackend {
        fn name(&self) -> &str {
            "pdr"
        }
        fn role(&self) -> BackendRole {
            BackendRole::SmtSolver
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true // claims to handle everything
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Proved {
                solver: "pdr".into(),
                time_ms: 0,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            }
        }
    }

    let router = Router::with_backends(vec![
        Box::new(PdrBackend),
        Box::new(constant_folder::ConstantFolderBackend),
    ]);

    let vc = VerificationCondition {
        kind: VcKind::NonTermination {
            context: "while loop".to_string(),
            measure: "n".to_string(),
        },
        function: "loop_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    // PDR can_handle returns true, but validate_dispatch should block it.
    // The router should fall through to the mock backend instead.
    let result = router.verify_one(&vc);
    assert_ne!(
        result.solver_name(),
        "pdr",
        "PDR must not handle NonTermination VC even if can_handle=true"
    );
    assert_eq!(
        result.solver_name(),
        "constant-folder",
        "constant-folder should handle NonTermination when PDR is blocked by validate_dispatch"
    );
}

#[test]
fn test_validate_dispatch_allows_valid_solver_for_safety_vc() {
    // validate_dispatch should allow all solvers for safety VCs.
    struct PdrBackend;

    impl VerificationBackend for PdrBackend {
        fn name(&self) -> &str {
            "pdr"
        }
        fn role(&self) -> BackendRole {
            BackendRole::SmtSolver
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Proved {
                solver: "pdr".into(),
                time_ms: 0,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            }
        }
    }

    let router = Router::with_backends(vec![
        Box::new(PdrBackend),
        Box::new(constant_folder::ConstantFolderBackend),
    ]);

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "div_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    // PDR is valid for safety VCs — validate_dispatch should allow it.
    let result = router.verify_one(&vc);
    assert_eq!(
        result.solver_name(),
        "pdr",
        "PDR should handle safety VCs (validate_dispatch allows it)"
    );
}

#[test]
fn test_validate_dispatch_blocks_all_safety_only_solvers_for_liveness() {
    // Safety-only solvers (ic3, bmc, k-induction) must be blocked
    // for liveness properties too, not just termination.
    struct Ic3Backend;

    impl VerificationBackend for Ic3Backend {
        fn name(&self) -> &str {
            "ic3"
        }
        fn role(&self) -> BackendRole {
            BackendRole::SmtSolver
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Proved {
                solver: "ic3".into(),
                time_ms: 0,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            }
        }
    }

    let router = Router::with_backends(vec![
        Box::new(Ic3Backend),
        Box::new(constant_folder::ConstantFolderBackend),
    ]);

    let vc = VerificationCondition {
        kind: VcKind::Temporal { property: "eventually done".to_string(), machine: None },
        function: "live_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let result = router.verify_one(&vc);
    assert_ne!(
        result.solver_name(),
        "ic3",
        "IC3 must not handle liveness VC (#422 validate_dispatch)"
    );
}

#[test]
fn test_select_backend_returns_none_when_all_invalid() {
    // If every backend is blocked by validate_dispatch, router
    // dispatch returns Unknown.
    struct BmcBackend;

    impl VerificationBackend for BmcBackend {
        fn name(&self) -> &str {
            "bmc"
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Proved {
                solver: "bmc".into(),
                time_ms: 0,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            }
        }
    }

    // Only a BMC backend: can_handle=true but invalid for termination.
    let router = Router::with_backends(vec![Box::new(BmcBackend)]);

    let vc = VerificationCondition {
        kind: VcKind::NonTermination { context: "loop".to_string(), measure: "n".to_string() },
        function: "stuck_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let result = router.verify_one(&vc);
    assert!(
        matches!(result, VerificationResult::Unknown { .. }),
        "should return Unknown when all backends are blocked: {result:?}"
    );
    assert_eq!(result.solver_name(), "none");
}

// test_first_class_backend_families_are_selected_by_kind removed — it exercised
// the v1 subprocess backends (trust_vc_backend, trust_wp_backend, trust_mc_backend)
// which are dead code under pipeline-v2.

// -----------------------------------------------------------------------
// #426: HigherOrder variant exists and clean_backend uses it
// -----------------------------------------------------------------------

#[test]
fn test_higher_order_variant_exists_and_is_distinct() {
    // Verify the HigherOrder variant is a distinct BackendRole
    // and can be round-tripped through equality checks.
    let role = BackendRole::HigherOrder;
    assert_ne!(role, BackendRole::General);
    assert_ne!(role, BackendRole::SmtSolver);
    assert_ne!(role, BackendRole::Deductive);
    assert_ne!(role, BackendRole::Temporal);
    assert_ne!(role, BackendRole::Ownership);
    assert_ne!(role, BackendRole::BoundedModelChecker);
    assert_eq!(role, BackendRole::HigherOrder);
}

// clean_backend tests removed — clean cluster deleted.
// test_clean_backend_returns_higher_order_role, test_l2domain_ranks_higher_order_above_deductive,
// test_l2domain_ranks_temporal_first moved to clean crate when available.

// ay_direct tests removed — ay integration now via trust-bmc (Pipeline v2).

// -----------------------------------------------------------------------
// #882: MemoryGuard integration tests
// -----------------------------------------------------------------------

#[test]
fn test_router_with_memory_guard_builder() {
    use crate::memory_guard::MemoryGuard;

    let guard = MemoryGuard::new(2048);
    let router = Router::with_backends(vec![Box::new(constant_folder::ConstantFolderBackend)])
        .with_memory_guard(guard);

    assert_eq!(router.memory_guard().limit_mb(), 2048);
}

#[test]
fn test_router_default_memory_guard() {
    use crate::memory_guard::MemoryGuard;
    let router = Router::new();
    // The default MemoryGuard is RAM-derived (machine_budget_bytes, floored),
    // not a hardcoded constant; Router::new() must use exactly that default.
    assert_eq!(router.memory_guard().limit_mb(), MemoryGuard::default().limit_mb());
    assert!(router.memory_guard().limit_mb() >= 1024, "default guard keeps a sane floor");
}

#[test]
fn test_router_memory_guard_unlimited_passes() {
    use crate::memory_guard::MemoryGuard;

    let guard = MemoryGuard::new(0); // unlimited
    let router = Router::with_backends(vec![Box::new(constant_folder::ConstantFolderBackend)])
        .with_memory_guard(guard);

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    // With unlimited guard, dispatch should proceed normally.
    let result = router.verify_one(&vc);
    assert!(result.is_proved(), "unlimited memory guard should not block dispatch");
    assert_eq!(result.solver_name(), "constant-folder");
}

#[test]
fn test_router_memory_guard_high_limit_passes() {
    use crate::memory_guard::MemoryGuard;

    let guard = MemoryGuard::new(64 * 1024); // 64 GB — well above any test process
    let router = Router::with_backends(vec![Box::new(constant_folder::ConstantFolderBackend)])
        .with_memory_guard(guard);

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let result = router.verify_one(&vc);
    assert!(result.is_proved(), "high limit should not block dispatch");
    assert_eq!(result.solver_name(), "constant-folder");
}

#[test]
fn test_router_memory_guard_low_limit_blocks_dispatch() {
    use crate::memory_guard::MemoryGuard;

    // 1 MB limit — the test process uses more than this.
    let guard = MemoryGuard::new(1);
    let router = Router::with_backends(vec![Box::new(constant_folder::ConstantFolderBackend)])
        .with_memory_guard(guard);

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let result = router.verify_one(&vc);
    assert!(
        matches!(result, VerificationResult::Unknown { .. }),
        "1MB limit should block dispatch: {result:?}"
    );
    assert_eq!(result.solver_name(), "memory-guard");
    let reason = match &result {
        VerificationResult::Unknown { reason, .. } => reason.as_str(),
        _ => panic!("expected Unknown"),
    };
    assert!(reason.contains("memory limit exceeded"), "reason: {reason}");
}

#[test]
fn test_router_memory_guard_blocks_verify_all() {
    use crate::memory_guard::MemoryGuard;

    let guard = MemoryGuard::new(1); // 1 MB — will exceed
    let router = Router::with_backends(vec![Box::new(constant_folder::ConstantFolderBackend)])
        .with_memory_guard(guard);

    let vcs = vec![
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "fn1".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        },
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "fn2".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        },
    ];

    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), 2);
    for (_, result) in &results {
        assert_eq!(
            result.solver_name(),
            "memory-guard",
            "all VCs should be blocked by memory guard"
        );
    }
}

#[test]
fn test_router_memory_guard_blocks_verify_all_parallel() {
    use crate::memory_guard::MemoryGuard;

    let guard = MemoryGuard::new(1); // 1 MB — will exceed
    let router = Router::with_backends(vec![Box::new(constant_folder::ConstantFolderBackend)])
        .with_memory_guard(guard);

    let vcs: Vec<_> = (0..4)
        .map(|i| VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: format!("parallel_guard_fn_{i}").into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        })
        .collect();

    let results = router.verify_all_parallel(&vcs, 2);

    assert_eq!(results.len(), vcs.len());
    for (_, result) in &results {
        assert_eq!(
            result.solver_name(),
            "memory-guard",
            "parallel dispatch should be blocked by memory guard"
        );
    }
}

#[test]
fn test_router_memory_guard_peak_tracked_after_dispatch() {
    use crate::memory_guard::MemoryGuard;

    let guard = MemoryGuard::new(64 * 1024); // high limit
    let router = Router::with_backends(vec![Box::new(constant_folder::ConstantFolderBackend)])
        .with_memory_guard(guard);

    assert_eq!(router.memory_guard().peak_rss_bytes(), 0, "peak should be 0 before any check");

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let _ = router.verify_one(&vc);
    assert!(
        router.memory_guard().peak_rss_bytes() > 0,
        "peak RSS should be tracked after dispatch"
    );
}

// -- Shared-prefix batch dispatch routing tests --

/// A backend that records whether the router reached it via the batch entry
/// (`verify_batch`) or the per-VC entry (`verify`), and advertises shared-prefix
/// batch support so the single-backend router prefers the batch path.
struct BatchProbeBackend {
    batch_calls: Arc<AtomicUsize>,
    single_calls: Arc<AtomicUsize>,
    supports_batch: bool,
}

impl VerificationBackend for BatchProbeBackend {
    fn name(&self) -> &str {
        "batch-probe"
    }

    fn can_handle(&self, _vc: &VerificationCondition) -> bool {
        true
    }

    fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
        self.single_calls.fetch_add(1, Ordering::SeqCst);
        VerificationResult::Proved {
            solver: "batch-probe".into(),
            time_ms: 0,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    fn supports_shared_prefix_batch(&self) -> bool {
        self.supports_batch
    }

    fn verify_batch(
        &self,
        vcs: &[VerificationCondition],
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        self.batch_calls.fetch_add(1, Ordering::SeqCst);
        // Batch entry still produces one verdict per VC (here: trivially Proved),
        // so verdicts are identical to the per-VC path.
        vcs.iter().map(|vc| (vc.clone(), self.verify(vc))).collect()
    }
}

fn probe_vc(function: &str) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: function.into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    }
}

#[test]
fn sole_shared_prefix_batch_backend_routes_through_verify_batch() {
    let batch_calls = Arc::new(AtomicUsize::new(0));
    let single_calls = Arc::new(AtomicUsize::new(0));
    let router = Router::with_backends(vec![Box::new(BatchProbeBackend {
        batch_calls: batch_calls.clone(),
        single_calls: single_calls.clone(),
        supports_batch: true,
    })]);

    let vcs = vec![probe_vc("f"), probe_vc("f"), probe_vc("g")];
    let results = router.verify_all(&vcs);

    assert_eq!(results.len(), 3);
    assert!(results.iter().all(|(_, r)| r.is_proved()));
    // The router engaged the batch entry exactly once.
    assert_eq!(batch_calls.load(Ordering::SeqCst), 1, "single batch backend ⇒ verify_batch");
    // verify() is still called per VC INSIDE verify_batch (3 obligations).
    assert_eq!(single_calls.load(Ordering::SeqCst), 3);
}

#[test]
fn multi_backend_router_does_not_engage_batch_path() {
    let batch_calls = Arc::new(AtomicUsize::new(0));
    let single_calls = Arc::new(AtomicUsize::new(0));
    // Two backends ⇒ NOT the sole-backend configuration ⇒ per-VC dispatch.
    let router = Router::with_backends(vec![
        Box::new(BatchProbeBackend {
            batch_calls: batch_calls.clone(),
            single_calls: single_calls.clone(),
            supports_batch: true,
        }),
        Box::new(constant_folder::ConstantFolderBackend),
    ]);

    let vcs = vec![probe_vc("f"), probe_vc("f")];
    let _ = router.verify_all(&vcs);

    assert_eq!(batch_calls.load(Ordering::SeqCst), 0, "multi-backend ⇒ no batch entry");
}

#[test]
fn sole_non_batch_backend_uses_per_vc_path() {
    let batch_calls = Arc::new(AtomicUsize::new(0));
    let single_calls = Arc::new(AtomicUsize::new(0));
    // A sole backend that does NOT support shared-prefix batch ⇒ per-VC dispatch.
    let router = Router::with_backends(vec![Box::new(BatchProbeBackend {
        batch_calls: batch_calls.clone(),
        single_calls: single_calls.clone(),
        supports_batch: false,
    })]);

    // Structural dedup (244e089c66) collapses alpha-equivalent VCs before
    // sequential dispatch, and function name is NOT part of the equivalence
    // key — so the two probe_vc("f") duplicates share ONE solve while the
    // structurally distinct obligation gets its own.
    let distinct = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "g".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    let vcs = vec![probe_vc("f"), probe_vc("f"), distinct];
    let results = router.verify_all(&vcs);

    assert_eq!(results.len(), 3, "one result per input VC (duplicates fan out)");
    assert!(results.iter().all(|(_, r)| r.is_proved()));
    assert_eq!(batch_calls.load(Ordering::SeqCst), 0, "no batch support ⇒ no batch entry");
    assert_eq!(single_calls.load(Ordering::SeqCst), 2, "per-VC verify once per unique obligation");
}

#[test]
fn batch_path_skips_unsupported_mir_vcs() {
    let batch_calls = Arc::new(AtomicUsize::new(0));
    let single_calls = Arc::new(AtomicUsize::new(0));
    let router = Router::with_backends(vec![Box::new(BatchProbeBackend {
        batch_calls: batch_calls.clone(),
        single_calls: single_calls.clone(),
        supports_batch: true,
    })]);

    let unsupported = VerificationCondition {
        kind: VcKind::UnsupportedMir {
            kind: "TerminatorKind::Yield".to_string(),
            detail: "opaque".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };
    let vcs = vec![probe_vc("f"), unsupported, probe_vc("f")];
    let results = router.verify_all(&vcs);

    assert_eq!(results.len(), 3);
    // The unsupported-MIR VC is Unknown and never reached the backend; the two
    // real VCs are proved.
    assert!(results[0].1.is_proved());
    assert!(matches!(results[1].1, VerificationResult::Unknown { .. }));
    assert!(results[2].1.is_proved());
    // Only the two supported VCs were batched; verify() ran twice.
    assert_eq!(single_calls.load(Ordering::SeqCst), 2);
}
