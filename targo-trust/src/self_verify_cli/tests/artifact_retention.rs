use super::*;

fn capture(source: &Path, duplicate_unit: bool) -> TransportSummary {
    capture_shared_payload(source, duplicate_unit, false)
}

fn capture_shared_payload(
    source: &Path,
    duplicate_unit: bool,
    distinct_bindings: bool,
) -> TransportSummary {
    capture_shared_payload_with_mutation(source, duplicate_unit, distinct_bindings, None)
}

fn capture_shared_payload_with_mutation(
    source: &Path,
    duplicate_unit: bool,
    distinct_bindings: bool,
    mutate_later: Option<(usize, fn(&mut trust_types::TransportEvidenceArtifact))>,
) -> TransportSummary {
    let mut summary = TransportSummary {
        artifact_stage_label: "retention-fixture".into(),
        ..TransportSummary::default()
    };
    let mut row = clean_cic_binding::kernel_transport();
    row.outcome = trust_types::Outcome::Unknown;
    let proof = row.proof_evidence.as_mut().unwrap();
    proof.suite = "trust-mc".into();
    proof.backend = "trust-mc".into();
    proof.status = trust_types::TransportProofStatus::Unknown;
    proof.artifacts = vec![bound_transport_artifact(
        "NormalizedObligation",
        b"retained diagnostic input",
        "fixture-binding",
        row.obligation_id.as_deref().unwrap(),
        vec![],
        Some(source),
    )];
    // The same bytes can be referenced from both carriers and Cargo units;
    // storage deduplicates bytes while retaining every exact row owner.
    row.native_trust_ir = Some(trust_types::TransportNativeTrustIrEvidence {
        suite: "trust-mc".into(),
        backend: "trust-mc".into(),
        request_id: None,
        native_id: Some("fixture-binding".into()),
        present: true,
        artifacts: proof.artifacts.clone(),
        diagnostics: Vec::new(),
    });
    for (index, target) in std::iter::once(cargo_identity_fixture(0, "primary"))
        .chain(duplicate_unit.then(|| cargo_identity_fixture(1, "dependency")))
        .enumerate()
    {
        if index > 0 {
            for (artifact_index, artifact) in row
                .proof_evidence
                .as_mut()
                .unwrap()
                .artifacts
                .iter_mut()
                .chain(&mut row.native_trust_ir.as_mut().unwrap().artifacts)
                .enumerate()
            {
                if distinct_bindings {
                    artifact.materialization.as_mut().unwrap().proof_binding_id =
                        "other-row-binding".into();
                }
                if let Some((_, mutate)) =
                    mutate_later.filter(|(index, _)| *index == artifact_index)
                {
                    mutate(artifact);
                }
            }
        }
        ingest_result_rows(
            &mut summary,
            &target,
            &json!({"total":1,"results":[row.clone()]}),
            source,
            "captured.stdout.log",
            1,
            Some("shared::same_function"),
        );
    }
    summary
}

fn report(summary: &TransportSummary) -> Value {
    let suite = solver_suite_json(summary);
    json!({"schema": SCHEMA, "status":"incomplete",
        "proof":{"status":"incomplete", "complete":false, "timeout_is_incomplete_proof":true},
        "stages":[{"label":"retention-fixture", "solver_suite":suite}],
        "solver_suite":suite})
}

fn publish(source: &Path, destination: &Path, duplicate_unit: bool) -> (PathBuf, Value) {
    let mut summary = capture(source, duplicate_unit);
    let mut report = report(&summary);
    let bundle = retention::prepare_bundle(
        destination,
        source,
        std::mem::take(&mut summary.retained_artifact_rows),
    )
    .unwrap();
    report["evidence_retention"] = bundle.summary(&report).unwrap();
    validate_report_payload(&report).unwrap();
    let path = destination.join(REPORT_NAME);
    bundle.publish(&path, &report).unwrap();
    (path, report)
}

fn private_output(parent: &Path, name: &str) -> PathBuf {
    create_private_report_directory(&parent.join(name)).unwrap()
}

fn first_artifact(report: &Value, root: &Path) -> PathBuf {
    root.join(
        report["stages"][0]["solver_suite"]["verification_rows"][0]["proof_evidence"]["artifacts"]
            [0]["materialization"]["materialized_path"]
            .as_str()
            .unwrap(),
    )
}

#[test]
fn accepted_deep_transport_metadata_survives_report_wrappers_and_source_cleanup() {
    let source = tempfile::tempdir().unwrap();
    let parent = tempfile::tempdir().unwrap();
    let output = private_output(parent.path(), "bundle");
    let mut row = clean_cic_binding::kernel_transport();
    row.outcome = trust_types::Outcome::Unknown;
    let mut nested = json!(0);
    for _ in 0..120 {
        nested = Value::Array(vec![nested]);
    }
    let proof = row.proof_evidence.as_mut().unwrap();
    proof.suite = "trust-mc".into();
    proof.backend = "trust-mc".into();
    proof.status = trust_types::TransportProofStatus::Unknown;
    let mut artifact = bound_transport_artifact(
        "NormalizedObligation",
        b"depth diagnostic",
        "fixture-binding",
        row.obligation_id.as_deref().unwrap(),
        vec![],
        Some(source.path()),
    );
    artifact.metadata = Some(nested);
    proof.artifacts = vec![artifact];
    let wire = serde_json::to_string(
        &json!({"type":"function_result", "function":"shared::same_function",
        "results":[row], "proved":0, "failed":0, "unknown":1, "runtime_checked":0, "total":1}),
    )
    .unwrap();
    assert!(trust_types::json_depth::json_nesting_depth(&wire) <= 127);
    let parsed = trust_types::parse_transport_payload(&wire)
        .expect("actual typed transport parser accepts input");
    let mut summary = TransportSummary {
        artifact_stage_label: "retention-fixture".into(),
        ..TransportSummary::default()
    };
    ingest_transport_message(
        &mut summary,
        &cargo_identity_fixture(0, "primary"),
        &serde_json::to_value(parsed).unwrap(),
        source.path(),
        "captured.stdout.log",
        1,
    );
    assert_eq!(summary.verification_rows[0]["artifact_collection_status"], "typed");
    assert!(!summary.retained_artifact_rows.is_empty());
    let mut report = report(&summary);
    let bundle = retention::prepare_bundle(
        &output,
        source.path(),
        std::mem::take(&mut summary.retained_artifact_rows),
    )
    .unwrap();
    report["evidence_retention"] = bundle.summary(&report).unwrap();
    let path = output.join(REPORT_NAME);
    bundle.publish(&path, &report).unwrap();
    let bytes = fs::read(&path).unwrap();
    assert!(
        trust_types::json_depth::json_nesting_depth(std::str::from_utf8(&bytes).unwrap()) > 127
    );
    assert!(
        serde_json::from_slice::<Value>(&bytes)
            .unwrap_err()
            .to_string()
            .contains("recursion limit")
    );
    trust_types::json_depth::from_slice_deep::<Value>(&bytes)
        .expect("existing bounded decoder accepts report");
    drop(source);
    let checked = retention::inspect_saved_report(&path).unwrap();
    assert_eq!(checked["complete"], true);
    assert_eq!(checked["persisted_artifacts"], 1);
    assert_eq!(checked["observational_only"], true);
    assert_eq!(checked["execution_identity_bound"], false);
    assert_eq!(checked["source_provenance_bound"], false);
    assert_eq!(report["proof"]["complete"], false);
}

#[test]
fn shared_payload_keeps_distinct_per_row_binding_metadata() {
    let source = tempfile::tempdir().unwrap();
    let parent = tempfile::tempdir().unwrap();
    let output = private_output(parent.path(), "bundle");
    let mut summary = capture_shared_payload(source.path(), true, true);
    let mut report = report(&summary);
    let bundle = retention::prepare_bundle(
        &output,
        source.path(),
        std::mem::take(&mut summary.retained_artifact_rows),
    )
    .unwrap();
    report["evidence_retention"] = bundle.summary(&report).unwrap();
    let rows = report["stages"][0]["solver_suite"]["verification_rows"].as_array().unwrap();
    assert_ne!(
        rows[0]["proof_evidence"]["artifacts"][0]["materialization"]["proof_binding_id"],
        rows[1]["proof_evidence"]["artifacts"][0]["materialization"]["proof_binding_id"]
    );
    let path = output.join(REPORT_NAME);
    bundle.publish(&path, &report).unwrap();
    drop(source);
    let checked = retention::inspect_saved_report(&path).unwrap();
    assert_eq!(checked["persisted_artifacts"], 1);
    assert_eq!(checked["complete"], true);
    assert_eq!(checked["observational_only"], true);
}

#[test]
fn shared_payload_rejects_malformed_later_descriptors_before_publication() {
    type Mutation = (&'static str, fn(&mut trust_types::TransportEvidenceArtifact));
    let mutations: &[Mutation] = &[
        ("empty binding", |artifact| {
            artifact.materialization.as_mut().unwrap().proof_binding_id.clear()
        }),
        ("wrong encoding", |artifact| {
            artifact.materialization.as_mut().unwrap().encoding = "bad".into()
        }),
        ("wrong algorithm", |artifact| artifact.digest.as_mut().unwrap().algorithm = "bad".into()),
        ("noncanonical path", |artifact| {
            let path =
                artifact.materialization.as_mut().unwrap().materialized_path.as_mut().unwrap();
            *path = path.replace("/sha256/", "/sha256/./");
        }),
    ];
    for (name, mutate) in mutations {
        for carrier in 0..2 {
            let source = tempfile::tempdir().unwrap();
            let parent = tempfile::tempdir().unwrap();
            let output = private_output(parent.path(), "bundle");
            let mut summary = capture_shared_payload_with_mutation(
                source.path(),
                true,
                false,
                Some((carrier, *mutate)),
            );
            assert_eq!(summary.retained_artifact_rows.len(), 2, "{name}: actual typed ingestion");
            assert!(
                retention::prepare_bundle(
                    &output,
                    source.path(),
                    std::mem::take(&mut summary.retained_artifact_rows),
                )
                .is_err(),
                "{name}, carrier={carrier}: invalid later descriptor must prevent publication"
            );
            assert!(!output.join(REPORT_NAME).exists(), "{name}");
            assert!(!output.join("self-verify.evidence-bundle.json").exists(), "{name}");
        }
    }
}

#[test]
fn malformed_transport_rows_remain_saved_diagnostics_without_artifact_credit() {
    for mutation in ["carrier", "outer-row"] {
        let source = tempfile::tempdir().unwrap();
        let parent = tempfile::tempdir().unwrap();
        let output = private_output(parent.path(), "bundle");
        let mut summary = TransportSummary {
            artifact_stage_label: "retention-fixture".into(),
            ..TransportSummary::default()
        };
        let mut raw = serde_json::to_value(clean_cic_binding::kernel_transport()).unwrap();
        if mutation == "carrier" {
            raw["proof_evidence"]["status"] = json!("not-a-typed-status");
        } else {
            raw["time_ms"] = json!("not-a-number");
        }
        ingest_result_rows(
            &mut summary,
            &cargo_identity_fixture(0, "primary"),
            &json!({"total":1,"results":[raw.clone()]}),
            source.path(),
            "captured.stdout.log",
            1,
            Some("shared::same_function"),
        );
        assert!(!summary.inconsistencies.is_empty());
        assert_eq!(summary.verification_rows.len(), 1);
        assert_eq!(summary.verification_rows[0]["artifact_collection_status"], "rejected");
        assert!(summary.retained_artifact_rows.is_empty());
        let mut report = report(&summary);
        let bundle = retention::prepare_bundle(
            &output,
            source.path(),
            std::mem::take(&mut summary.retained_artifact_rows),
        )
        .unwrap();
        report["evidence_retention"] = bundle.summary(&report).unwrap();
        assert_eq!(report["evidence_retention"]["complete"], false);
        assert_eq!(report["evidence_retention"]["untyped_transport_rows"], 1);
        let path = output.join(REPORT_NAME);
        bundle.publish(&path, &report).unwrap();
        drop(source);
        let checked = retention::inspect_saved_report(&path).unwrap();
        assert_eq!(checked["complete"], false);
        assert_eq!(checked["collection_complete"], false);
        assert_eq!(checked["untyped_transport_rows"], 1);
        let saved: Value = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
        assert_eq!(
            saved["stages"][0]["solver_suite"]["verification_rows"][0]["proof_evidence"],
            raw["proof_evidence"]
        );
        assert_eq!(saved["proof"]["complete"], false);
    }
}

fn rewrite_bound_report(path: &Path, report: &Value) {
    let bytes = serde_json::to_vec(report).unwrap();
    let sidecar_path = path.parent().unwrap().join("self-verify.evidence-bundle.json");
    let mut sidecar: Value = serde_json::from_slice(&fs::read(&sidecar_path).unwrap()).unwrap();
    sidecar["report_sha256"] = json!(format!("{:x}", Sha256::digest(&bytes)));
    sidecar["report_bytes"] = json!(bytes.len());
    fs::write(sidecar_path, serde_json::to_vec(&sidecar).unwrap()).unwrap();
    fs::write(path, bytes).unwrap();
}

#[test]
fn saved_report_refuses_traversal_scoped_name_and_claimed_topology_forgeries() {
    for mutation in ["traversal", "scoped-name", "topology"] {
        let source = tempfile::tempdir().unwrap();
        let parent = tempfile::tempdir().unwrap();
        let output = private_output(parent.path(), "bundle");
        let (path, mut report) = publish(source.path(), &output, false);
        let row = &mut report["stages"][0]["solver_suite"]["verification_rows"][0];
        match mutation {
            "traversal" => {
                row["proof_evidence"]["artifacts"][0]["materialization"]["materialized_path"] =
                    json!("../outside")
            }
            "scoped-name" => row["function"] = json!("unrelated-cargo-unit::same_function"),
            _ => {
                row["proof_binding"]["accepted"] = json!(true);
                row["proof_binding"]["publication_grade_native_proof"] = json!(true);
            }
        }
        // The saved bundle remains observational even when an attacker edits
        // BOTH files consistently; replay still checks paths, scopes and DAGs.
        rewrite_bound_report(&path, &report);
        assert!(retention::inspect_saved_report(&path).is_err(), "{mutation}");
    }
}

#[test]
fn empty_and_legacy_reports_never_acquire_proof_authority() {
    let source = tempfile::tempdir().unwrap();
    let parent = tempfile::tempdir().unwrap();
    let output = private_output(parent.path(), "empty");
    let mut report = report(&TransportSummary::default());
    let bundle = retention::prepare_bundle(&output, source.path(), Vec::new()).unwrap();
    report["evidence_retention"] = bundle.summary(&report).unwrap();
    let path = output.join(REPORT_NAME);
    bundle.publish(&path, &report).unwrap();
    let checked = retention::inspect_saved_report(&path).unwrap();
    assert_eq!(checked["complete"], true);
    assert_eq!(checked["persisted_artifacts"], 0);
    assert_eq!(checked["source_provenance_bound"], false);
    assert_eq!(report["proof"]["complete"], false);

    let legacy = private_output(parent.path(), "legacy").join(REPORT_NAME);
    write_report(&legacy, &self::report(&TransportSummary::default())).unwrap();
    let checked = retention::inspect_saved_report(&legacy).unwrap();
    assert_eq!(checked["status"], "unavailable");
    assert_eq!(checked["complete"], false);
}

#[test]
fn saved_artifacts_survive_private_root_deletion_with_exact_cargo_row_owners() {
    let source = tempfile::tempdir().unwrap();
    let parent = tempfile::tempdir().unwrap();
    let output = private_output(parent.path(), "bundle");
    let (path, report) = publish(source.path(), &output, true);
    let sidecar: Value =
        serde_json::from_slice(&fs::read(output.join("self-verify.evidence-bundle.json")).unwrap())
            .unwrap();
    assert_eq!(sidecar["rows"].as_array().unwrap().len(), 2);
    assert_ne!(sidecar["rows"][0]["cargo_target"], sidecar["rows"][1]["cargo_target"]);
    assert_ne!(sidecar["rows"][0]["row_ordinal"], sidecar["rows"][1]["row_ordinal"]);
    assert_eq!(sidecar["rows"][0]["raw_function"], sidecar["rows"][1]["raw_function"]);
    drop(source);
    let checked = retention::inspect_saved_report(&path).unwrap();
    assert_eq!(checked["complete"], true);
    assert_eq!(checked["persisted_artifacts"], 1);
    assert_eq!(checked["observational_only"], true);
    assert_eq!(checked["source_provenance_bound"], false);
    assert_eq!(checked["execution_identity_bound"], false);
    assert_eq!(report["proof"]["complete"], false);
}

#[test]
fn copy_cap_omissions_keep_scoped_diagnostics_without_retention_credit() {
    crate::report::with_artifact_store_policy_for_test(0, false, || {
        let source = tempfile::tempdir().unwrap();
        let parent = tempfile::tempdir().unwrap();
        let output = private_output(parent.path(), "bundle");
        let (path, report) = publish(source.path(), &output, true);
        drop(source);
        let checked = retention::inspect_saved_report(&path).unwrap();
        assert_eq!(checked["complete"], false);
        assert_eq!(checked["persisted_artifacts"], 0);
        assert_eq!(checked["omitted_artifacts"], 1);
        let bundle = &report["evidence_retention"]["bundle"];
        assert_eq!(bundle["omitted"][0]["rows"].as_array().unwrap().len(), 2);
        assert_eq!(report["solver_suite"]["outcomes"]["unknown"], 2);
        assert_eq!(report["proof"]["complete"], false);
    });
}

#[test]
fn saved_bundle_rejects_changed_missing_or_oversized_artifact_bytes() {
    for mutation in ["changed", "missing", "oversized"] {
        let source = tempfile::tempdir().unwrap();
        let parent = tempfile::tempdir().unwrap();
        let output = private_output(parent.path(), "bundle");
        let (path, report) = publish(source.path(), &output, false);
        let artifact = first_artifact(&report, &output);
        drop(source);
        match mutation {
            "changed" => fs::write(&artifact, b"different bytes").unwrap(),
            "missing" => fs::remove_file(&artifact).unwrap(),
            _ => File::options()
                .write(true)
                .open(&artifact)
                .unwrap()
                .set_len(trust_types::MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES as u64 + 1)
                .unwrap(),
        }
        assert!(retention::inspect_saved_report(&path).is_err(), "{mutation}");
    }
}

#[test]
fn sidecar_binds_exact_report_bytes_and_all_scoped_rows() {
    let source = tempfile::tempdir().unwrap();
    let parent = tempfile::tempdir().unwrap();
    let output = private_output(parent.path(), "bundle");
    let (path, _) = publish(source.path(), &output, true);
    let original = fs::read(&path).unwrap();
    let mut changed = original.clone();
    changed.push(b' ');
    fs::write(&path, changed).unwrap();
    assert!(retention::inspect_saved_report(&path).unwrap_err().contains("exact report bytes"));
    fs::write(&path, original).unwrap();
    let sidecar_path = output.join("self-verify.evidence-bundle.json");
    let mut sidecar: Value = serde_json::from_slice(&fs::read(&sidecar_path).unwrap()).unwrap();
    sidecar["rows"].as_array_mut().unwrap().pop();
    fs::write(sidecar_path, serde_json::to_vec(&sidecar).unwrap()).unwrap();
    assert!(retention::inspect_saved_report(&path).unwrap_err().contains("row locators"));
}

#[test]
fn interrupted_bundle_has_no_json_commit_marker() {
    let source = tempfile::tempdir().unwrap();
    let parent = tempfile::tempdir().unwrap();
    let output = private_output(parent.path(), "bundle");
    let mut summary = capture(source.path(), false);
    let mut report = report(&summary);
    let bundle = retention::prepare_bundle(
        &output,
        source.path(),
        std::mem::take(&mut summary.retained_artifact_rows),
    )
    .unwrap();
    report["evidence_retention"] = bundle.summary(&report).unwrap();
    assert!(!output.join(REPORT_NAME).exists());
    assert!(retention::inspect_saved_report(&output.join(REPORT_NAME)).is_err());
    fs::create_dir(output.join(REPORT_NAME)).unwrap();
    assert!(bundle.publish(&output.join(REPORT_NAME), &report).is_err());
    assert!(output.join("self-verify.evidence-bundle.json").is_file());
    assert!(!output.join(REPORT_NAME).is_file());
    assert!(retention::inspect_saved_report(&output.join(REPORT_NAME)).is_err());
}

#[cfg(unix)]
#[test]
fn saved_bundle_refuses_symlinked_files_ancestors_and_fifo_sidecars() {
    use std::os::unix::fs::symlink;
    for mutation in ["artifact-symlink", "parent-symlink", "sidecar-fifo"] {
        let source = tempfile::tempdir().unwrap();
        let parent = tempfile::tempdir().unwrap();
        let output = private_output(parent.path(), "bundle");
        let (path, report) = publish(source.path(), &output, false);
        let mut inspect_path = path;
        match mutation {
            "artifact-symlink" => {
                let artifact = first_artifact(&report, &output);
                let moved = output.join("moved-artifact");
                fs::rename(&artifact, &moved).unwrap();
                symlink(moved, artifact).unwrap();
            }
            "parent-symlink" => {
                let alias = parent.path().join("alias");
                symlink(&output, &alias).unwrap();
                inspect_path = alias.join(REPORT_NAME);
            }
            _ => {
                let sidecar = output.join("self-verify.evidence-bundle.json");
                fs::remove_file(&sidecar).unwrap();
                let name = std::ffi::CString::new(sidecar.as_os_str().as_encoded_bytes()).unwrap();
                assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
            }
        }
        assert!(retention::inspect_saved_report(&inspect_path).is_err(), "{mutation}");
    }
}
