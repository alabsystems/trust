//! Test execution consumes the same sealed frontend decision as publication.

use super::*;

/// This value cannot be deserialized or minted from a saved report. Creation
/// seals the current native report after its ordinary frontend gates ran.
pub(super) struct QualifiedTestExecution {
    verification_session: String,
}

impl QualifiedTestExecution {
    pub(super) fn seal(
        report: &mut VerificationReport,
        session: &str,
    ) -> Result<Option<Self>, crate::report::SealRefusal> {
        report.seal_publication_state()?;
        let passing = report.authenticates_verification_session(session)
            && report.success
            && report.exit_code == 0
            && report.gate.as_ref().is_some_and(|gate| {
                gate.exit_code == 0 && matches!(gate.decision.as_str(), "pass" | "conditional-pass")
            });
        Ok(passing.then(|| Self { verification_session: session.to_owned() }))
    }

    pub(super) fn require_session(&self, session: &str) -> Result<(), String> {
        if self.verification_session == session {
            Ok(())
        } else {
            Err("test qualification belongs to another verification session".into())
        }
    }

    pub(super) fn dispatch<T>(
        qualified: Option<&Self>,
        session: &str,
        execute: impl FnOnce(&Self) -> Result<T, ChildSetupError>,
    ) -> Result<T, ChildSetupError> {
        let qualified = qualified.ok_or_else(|| {
            ChildSetupError::Setup("current frontend proof qualification did not pass".into())
        })?;
        qualified.require_session(session)?;
        execute(qualified)
    }

    #[cfg(test)]
    pub(super) fn for_authority_writer_test(session: &str) -> Self {
        Self { verification_session: session.to_owned() }
    }
}

/// Inputs shared by the pre-execution decision and the final decision that
/// includes the observed test outcome. Proof rows and their policy do not change.
pub(super) struct RunGateInputs<'a> {
    pub(super) lane: GateLane,
    pub(super) decision: GateDecision,
    pub(super) counts: OutcomeCounts,
    pub(super) verification_level: &'a str,
    pub(super) coverage: Option<trust_types::VerificationCoverage>,
    pub(super) verification_concluded: bool,
    pub(super) every_unit_concluded: bool,
    pub(super) hardened_gate_failed: bool,
    pub(super) evidence_setup_failed: bool,
    pub(super) cargo_exclusion_gate_failure: bool,
}

/// The existing run exit policy, used before authorization and after execution.
pub(super) fn finalize_run_gate(
    report: &mut VerificationReport,
    input: &RunGateInputs<'_>,
    compiler_exit: i32,
    compiler_signal_exit: Option<u8>,
    orchestration_error: Option<&ChildSetupError>,
) -> ExitCode {
    let run_exit = RunExit::decide(RunExitFacts {
        report_success: report.success,
        compiler_exit,
        verification_concluded: input.verification_concluded,
        fail_closed_rows_observed: input.verification_concluded
            && input.counts.total > input.counts.proved,
        every_unit_concluded: input.every_unit_concluded,
        rows_fail_the_lane: !evaluate_verification_gate(input.lane, 0, input.counts).is_success(),
        tests_failed: tests_failed(report.test_execution.as_ref()),
        configuration_gate_failed: input.hardened_gate_failed || input.cargo_exclusion_gate_failure,
        refuted: report.failed > 0,
        outcome: report.determinism().outcome,
    });
    let process_exit_code = if let Some(error) = orchestration_error {
        error.exit_code()
    } else if let Some(signal_exit) = compiler_signal_exit {
        signal_exit
    } else if input.evidence_setup_failed {
        2
    } else {
        run_exit.code()
    };
    let could_not_run = match orchestration_error {
        Some(error) => matches!(error, ChildSetupError::CouldNotRun(_)),
        None => {
            compiler_signal_exit.is_none()
                && !input.evidence_setup_failed
                && run_exit == RunExit::CouldNotRun
        }
    };
    if could_not_run {
        report.success = false;
    }
    let decision = if could_not_run {
        GateDecision::CouldNotRun
    } else if input.hardened_gate_failed
        || input.evidence_setup_failed
        || report.failed > 0
        || compiler_exit != 0
    {
        GateDecision::Fail
    } else if input.cargo_exclusion_gate_failure {
        GateDecision::Inconclusive
    } else if report.success {
        input.decision
    } else {
        GateDecision::Inconclusive
    };
    let mut gate = build_verification_gate_report(
        input.lane,
        input.verification_level,
        decision,
        input.counts,
        process_exit_code,
        &report.dep_assumptions,
        input.coverage,
    );
    gate.test_execution = report.test_execution.clone();
    gate.exclusions = report.test_harness_exclusions.clone();
    report.install_gate(gate);
    report.record_determinism();
    ExitCode::from(process_exit_code)
}

/// Preserve the existing fail-closed publication path on either seal boundary.
pub(super) fn publish_seal_refusal(
    report: &mut VerificationReport,
    refusal: &crate::report::SealRefusal,
) -> bool {
    const SEAL_REFUSAL_EXIT: u8 = 2;
    eprintln!(
        "targo trust: could not seal the final compiler rows, coverage, policy, gate, and exit state for canonical publication: {refusal}"
    );
    match report.grade_every_row_unproved_and_reseal(&refusal, SEAL_REFUSAL_EXIT) {
        Ok(()) => {
            eprintln!(
                "targo trust: publishing a FAIL-CLOSED verdict rather than nothing: every obligation below is graded UNKNOWN and carries no proof credit, while the coverage row and `Gate:` line are this run's real ones. The run neither proved nor REFUTED anything."
            );
            eprintln!(
                "targo trust: fix options: (1) re-run with `--format json --report-dir <dir>` to capture the full row inventory beside the refused precondition; (2) if the precondition names a rejected proof certificate, the obligation is UNPROVED — a refused certificate is not a counterexample; (3) if it names a missing artifact or receipt, the run's private proof store did not survive to publication — re-run without clearing the target directory between compile and publish."
            );
            true
        }
        Err(unrepairable) => {
            eprintln!("targo trust: the run cannot be published even fail-closed: {unrepairable}");
            eprintln!(
                "targo trust: established before the refusal: {} obligation(s) — {} proved, {} failed, {} unknown; coverage {}. This is NOT a verdict: nothing was refuted.",
                report.total,
                report.proved,
                report.failed,
                report.unknown,
                report.coverage.as_ref().map_or_else(
                    || "UNKNOWN (no coverage row)".to_string(),
                    |coverage| format!(
                        "{}/{} eligible function bodies verified{}",
                        coverage.processed,
                        coverage.eligible,
                        if coverage.coverage_complete { " (complete)" } else { " (INCOMPLETE)" }
                    )
                )
            );
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use super::*;

    const SESSION: &str = "869d776e3865bf366d82d01e8ea24393d3d76063c2bfd4b71e9e93809d2a8511";

    /// Use the production parser, exact coverage authentication, publication
    /// normalization and live authority mint over a real compiler capture.
    fn report_fixture(
        row: Option<(trust_types::VcKind, trust_types::Outcome)>,
    ) -> VerificationReport {
        let stream = include_str!("../../fixtures/zero_obligation_fn_transport.jsonl")
            .lines()
            .map(|line| {
                let mut value: serde_json::Value =
                    serde_json::from_str(line.strip_prefix("TRUST_JSON:").unwrap()).unwrap();
                // Function/terminal scope is Option<String>; coverage scope
                // uses the empty String for the same raw compiler context.
                value["package_name"] = if value["type"] == "coverage_summary" {
                    serde_json::json!("")
                } else {
                    serde_json::Value::Null
                };
                value["primary_package"] = serde_json::json!(false);
                if let Some((kind, outcome)) = row.as_ref() {
                    if value["type"] == "function_result" {
                        value["results"] = serde_json::json!([{
                            "kind": kind.transport_tag(),
                            "typed_kind": kind,
                            "description": kind.description(),
                            "outcome": outcome,
                            "solver": "mir-verify-full",
                            "time_ms": 0,
                            "reason": "native qualification regression fixture"
                        }]);
                        value["proved"] = serde_json::json!(0);
                        value["unknown"] = serde_json::json!(usize::from(
                            *outcome == trust_types::Outcome::Unknown
                        ));
                        value["runtime_checked"] = serde_json::json!(usize::from(
                            *outcome == trust_types::Outcome::RuntimeChecked
                        ));
                    } else if value["type"] == "crate_summary" {
                        value["functions_verified"] = serde_json::json!(0);
                        value["total_proved"] = serde_json::json!(0);
                        value["total_unknown"] = serde_json::json!(usize::from(
                            *outcome == trust_types::Outcome::Unknown
                        ));
                        value["total_runtime_checked"] = serde_json::json!(usize::from(
                            *outcome == trust_types::Outcome::RuntimeChecked
                        ));
                    }
                }
                format!("TRUST_JSON:{value}\n")
            })
            .collect::<String>();
        let parsed = parse_compiler_stderr(Cursor::new(stream), false)
            .require_structured_json_transport(true)
            .require_raw_coverage_authentication(SESSION, true)
            .unwrap();
        assert!(parsed.raw_terminal_inventory_complete());
        let authenticated = parsed.verification_results;
        let zero_obligation_functions =
            crate::types::authenticated_zero_obligation_inventory(&authenticated);
        let mut results = authenticated.clone();
        let boundary =
            crate::types::normalize_authenticated_results_for_publication(&mut results, None);
        let (counts, defects) = partition_outcome_counts(&results);
        assert!(defects.is_empty());
        let authority = LiveTransportAuthority::capture_authenticated_projection(
            "one",
            SESSION,
            authenticated,
            &results,
            None,
            TestTargetPanicPolicy::Strict,
        )
        .expect("native fixture has exact current row authority");
        VerificationReport {
            report_subject: "one".into(),
            success: true,
            exit_code: 0,
            proved: counts.proved,
            failed: counts.failed,
            unknown: counts.unknown,
            runtime_checked: counts.runtime_checked,
            assumed: counts.assumed,
            mandated: counts.mandated,
            contract_panics: counts.contract_panics,
            cached: 0,
            total: counts.total,
            results,
            publication_boundary: Some(boundary),
            zero_obligation_functions,
            compiler_diagnostics: parsed.compiler_diagnostics,
            duration_ms: 0,
            config: ReportConfig {
                level: "L2".into(),
                budget_profile: crate::determinism_report::test_budget_profile(),
                enabled: true,
                hardened: false,
                trust_profile: None,
                project_requirements: None,
            },
            dep_assumptions: Vec::new(),
            gate: None,
            noted_stops: Vec::new(),
            coverage: aggregate_coverage(&parsed.coverage_rows),
            coverage_dropped: parsed.dropped_coverage,
            test_execution: None,
            cargo_proof_inventory: None,
            proof_artifact_root: None,
            live_transport_authority: Some(authority),
            test_harness_exclusions: Vec::new(),
        }
    }

    fn gate_inputs(report: &VerificationReport, lane: GateLane) -> RunGateInputs<'static> {
        let (counts, _) = partition_outcome_counts(&report.results);
        let decision = evaluate_run_gate(
            lane,
            0,
            counts,
            report.coverage.as_ref(),
            false,
            true,
            &report.zero_obligation_functions,
            &[],
        );
        RunGateInputs {
            lane,
            decision,
            counts,
            verification_level: "L2",
            coverage: report.coverage,
            verification_concluded: true,
            every_unit_concluded: true,
            hardened_gate_failed: report.hardened_proof_gate_failure().is_some(),
            evidence_setup_failed: false,
            cargo_exclusion_gate_failure: false,
        }
    }

    fn finalize_fixture(report: &mut VerificationReport, input: &RunGateInputs<'_>) -> ExitCode {
        report.success = input.decision.is_success()
            && !input.evidence_setup_failed
            && !input.hardened_gate_failed
            && !input.cargo_exclusion_gate_failure;
        finalize_run_gate(report, input, 0, None, None)
    }

    fn dispatch_marker(qualified: Option<&QualifiedTestExecution>, path: &Path) -> bool {
        QualifiedTestExecution::dispatch(qualified, SESSION, |_| {
            std::fs::write(path, b"authorized execution callback").unwrap();
            Ok(())
        })
        .is_ok()
    }

    #[test]
    fn preexecution_rejected_lane_and_selected_root_never_dispatch() {
        let root = tempfile::tempdir().unwrap();
        let marker = root.path().join("executed");
        let mut report = report_fixture(Some((
            trust_types::VcKind::DivisionByZero,
            trust_types::Outcome::RuntimeChecked,
        )));
        assert_eq!(report.runtime_checked, 1);
        let input = gate_inputs(&report, GateLane::Certify);
        assert!(!input.decision.is_success());
        // The injected runtime row has no compiler stable key, so the existing
        // exit policy also refuses to call it a reproducible measurement.
        assert_eq!(finalize_fixture(&mut report, &input), ExitCode::from(3));
        let qualified = QualifiedTestExecution::seal(&mut report, SESSION).unwrap();
        assert!(!dispatch_marker(qualified.as_ref(), &marker));
        assert!(!marker.exists());

        // A successful native process without its declared selected-root
        // inventory is refused by the actual compiler-evidence validator.
        let evidence = CargoCompilerEvidence {
            parsed: ParsedCompilerOutput::default(),
            compiled_targets: BTreeSet::new(),
            test_executables: BTreeSet::new(),
            prepared_tests: None,
            build_succeeded: Some(true),
            declared_inventory: None,
            authenticated_transport_messages: Vec::new(),
            compile_errors: Vec::new(),
        };
        let selected = [("path+file:///one#one@0.1.0".into(), "one".into())].into_iter().collect();
        assert!(evidence.require_successful_selected_roots(&selected, true).is_err());
        let mut report = report_fixture(None);
        let mut input = gate_inputs(&report, GateLane::Strict);
        input.evidence_setup_failed = true;
        assert_eq!(finalize_fixture(&mut report, &input), ExitCode::from(2));
        let qualified = QualifiedTestExecution::seal(&mut report, SESSION).unwrap();
        assert!(!dispatch_marker(qualified.as_ref(), &marker));
        assert!(!marker.exists());
    }

    #[test]
    fn preexecution_hardened_gap_and_active_exclusions_never_dispatch() {
        let root = tempfile::tempdir().unwrap();
        let marker = root.path().join("executed");
        let mut report = report_fixture(Some((
            trust_types::VcKind::HardenedBoundary {
                category: trust_types::HardenedVcCategory::ByteLoss,
                callee: "Path::to_string_lossy".into(),
                detail: "lossy path conversion".into(),
            },
            trust_types::Outcome::Unknown,
        )));
        report.config.hardened = true;
        report.config.trust_profile = Some("unix_hardened".into());
        assert!(report.hardened_proof_gate_failure().is_none(), "unknown is not a proof claim");
        // A favorable internal claim with no corresponding native proof must
        // fail the hardened gate AND the independently sealed row authority.
        report.results[0].outcome = crate::types::VerificationOutcome::Proved;
        report.proved = 1;
        report.unknown = 0;
        let input = gate_inputs(&report, GateLane::Advisory);
        assert!(input.decision.is_success(), "the advisory row gate alone passes");
        assert!(input.hardened_gate_failed);
        assert_eq!(finalize_fixture(&mut report, &input), ExitCode::from(1));
        assert!(QualifiedTestExecution::seal(&mut report, SESSION).is_err());
        assert!(!dispatch_marker(None, &marker));
        assert!(!marker.exists());

        let mut report = report_fixture(None);
        let mut input = gate_inputs(&report, GateLane::Strict);
        input.cargo_exclusion_gate_failure = true;
        assert_eq!(finalize_fixture(&mut report, &input), ExitCode::from(1));
        let qualified = QualifiedTestExecution::seal(&mut report, SESSION).unwrap();
        assert!(!dispatch_marker(qualified.as_ref(), &marker));
        assert!(!marker.exists());
    }

    #[test]
    fn preexecution_qualified_run_dispatches_and_refuses_a_foreign_session_or_missing_authority() {
        let root = tempfile::tempdir().unwrap();
        let marker = root.path().join("executed");
        let mut report = report_fixture(None);
        let input = gate_inputs(&report, GateLane::Strict);
        assert_eq!(finalize_fixture(&mut report, &input), ExitCode::SUCCESS);
        let qualified = QualifiedTestExecution::seal(&mut report, SESSION).unwrap();
        assert!(dispatch_marker(qualified.as_ref(), &marker));
        assert!(marker.exists());
        let wrong_session = QualifiedTestExecution::seal(&mut report, "foreign").unwrap();
        assert!(wrong_session.is_none(), "a sealed report cannot qualify a foreign session");
        let foreign = root.path().join("foreign");
        assert!(
            QualifiedTestExecution::dispatch(qualified.as_ref(), "foreign", |_| {
                std::fs::write(&foreign, b"must not execute").unwrap();
                Ok(())
            })
            .is_err()
        );
        assert!(!foreign.exists());
        report.live_transport_authority = None;
        assert!(QualifiedTestExecution::seal(&mut report, SESSION).is_err());
    }

    #[test]
    fn preexecution_test_failure_keeps_its_own_exit_and_fresh_final_seal() {
        let mut report = report_fixture(None);
        let input = gate_inputs(&report, GateLane::Strict);
        assert_eq!(finalize_fixture(&mut report, &input), ExitCode::SUCCESS);
        let qualified = QualifiedTestExecution::seal(&mut report, SESSION).unwrap();
        assert!(qualified.is_some());
        report.test_execution = Some(CertifiedTestExecutionReport {
            schema: trust_types::CERTIFIED_TEST_EXECUTION_SCHEMA_VERSION.into(),
            completion_scope: CertifiedTestExecutionCompletionScope::TopLevelCargoChildExitOnlyV1,
            requested: true,
            scope: trust_types::CERTIFIED_TEST_EXECUTION_SCOPE.into(),
            compile_only: false,
            phase_a_status: 0,
            phase_a_success: true,
            phase_b_state: CertifiedTestExecutionPhaseState::CargoInvocationExited,
            blocker: None,
            phase_b_exit: Some(101),
            authorized_executables: Vec::new(),
            authorized_inventory_sha256: None,
            target_directory: None,
        });
        report.success = false;
        report.exit_code = 101;
        assert_eq!(finalize_run_gate(&mut report, &input, 101, None, None), ExitCode::from(101));
        report.seal_publication_state().unwrap();
        let live = report.sealed_canonical_report().unwrap();
        let gate = live.for_self_improve_reduction().verification_gate.as_ref().unwrap();
        assert_eq!(gate.exit_code, 101);
        assert_eq!(gate.decision, "fail");
        assert_eq!(gate.test_execution.as_ref().unwrap().phase_b_exit, Some(101));
    }
}
