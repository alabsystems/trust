use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use serde::Deserialize;
use serde_json::Value;
use sha2::{Digest, Sha256};

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofConcurrencyAuditReport {
    schema: String,
    mode: String,
    proof_authority: String,
    proof_pass: bool,
    validator_available: bool,
    validation_performed: bool,
    replay_performed: bool,
    blocker_code: String,
    blocker: String,
    generated_at: String,
    repo_head: String,
    repo_dirty: bool,
    repo_dirty_metadata: DirtyMetadata,
    runner: Value,
    summary: Summary,
    obligations: Vec<Obligation>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct DirtyMetadata {
    available: bool,
    dirty: bool,
    porcelain_v1: Vec<String>,
    untracked_files: String,
    ignore_submodules: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Summary {
    total_obligations: u64,
    artifact_sets_present: u64,
    artifact_sets_hash_bound: u64,
    authenticated_validations: u64,
    replays_performed: u64,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Obligation {
    id: String,
    kind: String,
    status: String,
    source: String,
    memory_model: String,
    artifacts: Option<ArtifactInventory>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ArtifactInventory {
    declared_solver: String,
    source_sha256: String,
    certificate_sha256: String,
    transcript_sha256: String,
    dispatch_sha256: String,
    validation_status: String,
    replay_status: String,
}

#[test]
fn proof_concurrency_without_stub_fails_closed() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "proof-concurrency", "--format", "json"])
        .output()
        .expect("run proof-concurrency without stub mode");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert_eq!(
        output.status.code(),
        Some(2),
        "proof-concurrency should fail closed without explicit stub mode\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "fail-closed path should not emit evidence JSON");
    assert!(
        stderr.contains("reports/proof/concurrency-inputs.json")
            && stderr.contains("--manifest")
            && stderr.contains("--demo-audit"),
        "stderr should name the default release manifest, override, and explicit demo mode\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[test]
fn proof_concurrency_default_manifest_emits_nonproof_artifact_audit() {
    let repo = clean_git_repo("proof-concurrency-default-manifest-contract");
    let manifest = write_default_concurrency_manifest(&repo, ManifestOptions::default());
    run_git(&repo, &["add", "."]);
    run_git(&repo, &["commit", "-m", "default proof concurrency artifacts"]);
    let expected_head = git_stdout(&repo, &["rev-parse", "HEAD"]);

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "proof-concurrency",
            "--format",
            "json",
            "--repo-root",
            repo.to_str().expect("temp path should be utf-8"),
        ])
        .output()
        .expect("run proof-concurrency default artifact producer");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "default artifact producer should emit contract JSON from clean repo\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stderr.trim().is_empty(), "successful JSON mode should keep stderr empty");

    let report: ProofConcurrencyAuditReport =
        serde_json::from_slice(&output.stdout).expect("proof-concurrency JSON should parse");
    assert_eq!(report.schema, "trust.proof-concurrency.artifact-audit.v1");
    assert_eq!(report.proof_authority, "none");
    assert!(!report.proof_pass);
    assert!(!report.validation_performed);
    assert!(!report.replay_performed);
    assert_eq!(report.repo_head, expected_head);
    assert_eq!(report.runner["command"], "targo trust proof-concurrency --format json");
    assert!(
        !report.runner["argv"]
            .as_array()
            .expect("runner argv should be an array")
            .iter()
            .any(|arg| arg == "--manifest")
    );
    assert_eq!(report.runner["mode"], "artifact_inventory_audit");
    assert_eq!(report.summary.total_obligations, 3);
    assert_eq!(report.summary.artifact_sets_present, 3);
    assert_eq!(report.summary.artifact_sets_hash_bound, 3);
    assert_eq!(report.summary.authenticated_validations, 0);
    assert_eq!(report.summary.replays_performed, 0);

    let proof_dir = manifest.parent().expect("manifest should have a parent");
    let first = report
        .obligations
        .iter()
        .find(|obligation| obligation.id == "race_free_arc_mutex")
        .expect("race-free obligation should be present");
    assert_eq!(first.status, "present_unvalidated");
    assert_eq!(first.source, "reports/proof/race_free_arc_mutex.source.rs");
    let artifacts = first.artifacts.as_ref().expect("artifact inventory");
    assert_eq!(
        artifacts.source_sha256,
        file_sha256(&proof_dir.join("race_free_arc_mutex.source.rs"))
    );
    assert_eq!(
        artifacts.certificate_sha256,
        file_sha256(&proof_dir.join("race_free_arc_mutex.cert"))
    );
    assert_eq!(
        artifacts.transcript_sha256,
        file_sha256(&proof_dir.join("race_free_arc_mutex.proof"))
    );
    assert_eq!(
        artifacts.dispatch_sha256,
        file_sha256(&proof_dir.join("race_free_arc_mutex.dispatch"))
    );

    let _ = fs::remove_dir_all(&repo);
}

#[test]
fn proof_concurrency_materialize_input_manifest_writes_default_manifest() {
    let repo = clean_git_repo("proof-concurrency-materialize-manifest");
    let artifact_dir = write_default_concurrency_artifacts(&repo);

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "proof-concurrency",
            "--materialize-input-manifest",
            "--solver",
            "trust-concurrency-prover-test-v1",
            "--format",
            "json",
            "--repo-root",
            repo.to_str().expect("temp path should be utf-8"),
        ])
        .output()
        .expect("run proof-concurrency input materializer");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "materializer should write default manifest from complete artifacts\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stderr.trim().is_empty(), "successful materializer should keep stderr empty");

    let materialization: Value =
        serde_json::from_slice(&output.stdout).expect("materialization JSON should parse");
    assert_eq!(materialization["schema"], "trust.proof-concurrency.input-materialization.v1");
    assert_eq!(materialization["status"], "artifact_inventory_materialized");
    assert_eq!(materialization["proof_authority"], "none");
    assert_eq!(materialization["proof_pass"], false);
    assert_eq!(materialization["validation_performed"], false);
    assert_eq!(materialization["manifest_path"], "reports/proof/concurrency-inputs.json");
    assert_eq!(materialization["artifact_dir"], "reports/proof/concurrency-artifacts");
    assert_eq!(materialization["solver"], "trust-concurrency-prover-test-v1");
    assert_eq!(materialization["obligations"], 3);

    let manifest_path = repo.join("reports").join("proof").join("concurrency-inputs.json");
    let manifest: Value = serde_json::from_slice(
        &fs::read(&manifest_path).expect("materialized manifest should exist"),
    )
    .expect("materialized manifest should parse");
    assert_eq!(manifest["schema"], "trust.proof-concurrency.inputs.v1");
    assert_eq!(manifest["solver"], "trust-concurrency-prover-test-v1");
    let obligations = manifest["obligations"].as_array().expect("obligations should be an array");
    assert_eq!(obligations.len(), 3);
    let first = obligations
        .iter()
        .find(|obligation| obligation["id"] == "race_free_arc_mutex")
        .expect("race-free obligation should be materialized");
    assert_eq!(first["kind"], "data_race_free");
    assert_eq!(first["source"], "concurrency-artifacts/race_free_arc_mutex.source.rs");
    assert_eq!(first["source_artifact"], "concurrency-artifacts/race_free_arc_mutex.source.rs");
    assert_eq!(
        first["source_sha256"],
        file_sha256(&artifact_dir.join("race_free_arc_mutex.source.rs"))
    );
    assert_eq!(
        first["certificate_sha256"],
        file_sha256(&artifact_dir.join("race_free_arc_mutex.cert"))
    );

    run_git(&repo, &["add", "."]);
    run_git(&repo, &["commit", "-m", "materialized concurrency inputs"]);

    let report_output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "proof-concurrency",
            "--format",
            "json",
            "--repo-root",
            repo.to_str().expect("temp path should be utf-8"),
        ])
        .output()
        .expect("run proof-concurrency with materialized default manifest");
    let report_stdout = String::from_utf8_lossy(&report_output.stdout);
    let report_stderr = String::from_utf8_lossy(&report_output.stderr);
    assert_eq!(
        report_output.status.code(),
        Some(0),
        "materialized default manifest should feed proof report emission\nstdout:\n{report_stdout}\nstderr:\n{report_stderr}"
    );
    let report: ProofConcurrencyAuditReport =
        serde_json::from_slice(&report_output.stdout).expect("proof report should parse");
    assert_eq!(report.summary.total_obligations, 3);
    assert_eq!(report.summary.artifact_sets_present, 3);
    assert_eq!(report.summary.authenticated_validations, 0);

    let _ = fs::remove_dir_all(&repo);
}

#[test]
fn proof_concurrency_materialize_input_manifest_reports_missing_artifacts() {
    let repo = clean_git_repo("proof-concurrency-materialize-missing");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "proof-concurrency",
            "--materialize-input-manifest",
            "--solver",
            "trust-concurrency-prover-test-v1",
            "--repo-root",
            repo.to_str().expect("temp path should be utf-8"),
        ])
        .output()
        .expect("run proof-concurrency input materializer without artifacts");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "materializer should fail closed without complete artifacts\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "missing artifacts should not emit materialization JSON");
    assert!(
        stderr.contains("missing or invalid release artifacts")
            && stderr.contains("race_free_arc_mutex.source.rs")
            && stderr.contains("channel_happens_before.dispatch"),
        "stderr should list concrete missing artifact paths\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !repo.join("reports").join("proof").join("concurrency-inputs.json").exists(),
        "failed materialization should not write the default manifest"
    );

    let _ = fs::remove_dir_all(&repo);
}

#[test]
fn proof_concurrency_materialize_input_manifest_rejects_manual_solver_identity() {
    let repo = clean_git_repo("proof-concurrency-materialize-manual-solver");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "proof-concurrency",
            "--materialize-input-manifest",
            "--solver",
            "manual",
            "--repo-root",
            repo.to_str().expect("temp path should be utf-8"),
        ])
        .output()
        .expect("run proof-concurrency input materializer with manual solver");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "manual solver identities must fail closed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "manual solver rejection should not emit JSON");
    assert!(
        stderr.contains("concrete non-manual solver identity"),
        "stderr should explain solver identity rejection\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let _ = fs::remove_dir_all(&repo);
}

#[cfg(unix)]
#[test]
fn proof_concurrency_materializer_never_follows_manifest_output_symlinks() {
    use std::os::unix::fs::symlink;

    let repo = clean_git_repo("proof-concurrency-materialize-output-symlink");
    write_default_concurrency_artifacts(&repo);
    let proof_dir = repo.join("reports").join("proof");
    let victim = proof_dir.join("victim.json");
    let manifest = proof_dir.join("concurrency-inputs.json");
    fs::write(&victim, b"safe").expect("write output-symlink victim");
    symlink(&victim, &manifest).expect("create manifest output symlink");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "proof-concurrency",
            "--materialize-input-manifest",
            "--solver",
            "trust-concurrency-prover-test-v1",
            "--repo-root",
            repo.to_str().expect("temp path should be utf-8"),
        ])
        .output()
        .expect("reject symlinked materialization output");

    assert_eq!(output.status.code(), Some(2));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("symbolic link"), "stderr:\n{stderr}");
    assert_eq!(fs::read(&victim).expect("read victim"), b"safe");

    let _ = fs::remove_dir_all(&repo);
}

#[test]
fn proof_concurrency_manifest_emits_hash_bound_nonproof_audit() {
    let repo = clean_git_repo("proof-concurrency-manifest-contract");
    let manifest = write_concurrency_manifest(&repo, ManifestOptions::default());
    run_git(&repo, &["add", "."]);
    run_git(&repo, &["commit", "-m", "proof artifacts"]);
    let expected_head = git_stdout(&repo, &["rev-parse", "HEAD"]);

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "proof-concurrency",
            "--format",
            "json",
            "--manifest",
            manifest.to_str().expect("temp path should be utf-8"),
            "--repo-root",
            repo.to_str().expect("temp path should be utf-8"),
        ])
        .output()
        .expect("run proof-concurrency artifact producer");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "artifact producer should emit contract JSON from clean repo\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stderr.trim().is_empty(), "successful JSON mode should keep stderr empty");

    let report: ProofConcurrencyAuditReport =
        serde_json::from_slice(&output.stdout).expect("proof-concurrency JSON should parse");
    assert_eq!(report.schema, "trust.proof-concurrency.artifact-audit.v1");
    assert_eq!(report.mode, "artifact_inventory_audit");
    assert_eq!(report.proof_authority, "none");
    assert!(!report.proof_pass);
    assert!(!report.validator_available);
    assert_eq!(report.blocker_code, "missing_trust_concurrency_authenticated_validator");
    assert!(report.blocker.contains("do not validate a certificate"));
    assert_eq!(report.repo_head, expected_head);
    assert!(!report.repo_dirty);
    assert!(report.repo_dirty_metadata.porcelain_v1.is_empty());
    assert_eq!(report.runner["implementation"], "rust");
    assert_eq!(report.runner["entrypoint"], "targo trust proof-concurrency");
    assert_eq!(report.runner["mode"], "artifact_inventory_audit");
    assert_eq!(report.runner["audit_kind"], "presence_and_digest_only");
    assert_eq!(report.summary.total_obligations, 3);
    assert_eq!(report.summary.artifact_sets_present, 3);
    assert_eq!(report.summary.artifact_sets_hash_bound, 3);
    assert_eq!(report.summary.authenticated_validations, 0);
    assert_eq!(report.summary.replays_performed, 0);

    let obligations: BTreeMap<String, Obligation> = report
        .obligations
        .into_iter()
        .map(|obligation| (obligation.id.clone(), obligation))
        .collect();
    assert_eq!(
        obligations.keys().map(String::as_str).collect::<BTreeSet<_>>(),
        BTreeSet::from(["atomic_release_acquire", "channel_happens_before", "race_free_arc_mutex"])
    );
    for (id, obligation) in obligations {
        let proof_dir = repo.join("proofs").join("concurrency");
        assert_eq!(obligation.status, "present_unvalidated");
        assert_eq!(obligation.source, format!("proofs/concurrency/{id}.source.rs"));
        let artifacts = obligation.artifacts.expect("artifact inventory");
        assert_eq!(
            artifacts.source_sha256,
            file_sha256(&proof_dir.join(format!("{id}.source.rs")))
        );
        assert_eq!(obligation.memory_model, "rust-abstract-machine+llvm-atomics");
        assert_eq!(artifacts.declared_solver, "trust-concurrency-prover-test-v1");
        assert_eq!(
            artifacts.certificate_sha256,
            file_sha256(&proof_dir.join(format!("{id}.cert")))
        );
        assert_eq!(
            artifacts.transcript_sha256,
            file_sha256(&proof_dir.join(format!("{id}.proof")))
        );
        assert_eq!(
            artifacts.dispatch_sha256,
            file_sha256(&proof_dir.join(format!("{id}.dispatch")))
        );
        assert!(is_sha256_hex(&artifacts.source_sha256));
        assert!(is_sha256_hex(&artifacts.certificate_sha256));
        assert!(is_sha256_hex(&artifacts.transcript_sha256));
        assert!(is_sha256_hex(&artifacts.dispatch_sha256));
        assert_eq!(artifacts.validation_status, "not_performed");
        assert_eq!(artifacts.replay_status, "not_performed");
    }

    let _ = fs::remove_dir_all(&repo);
}

#[test]
fn proof_concurrency_manifest_rejects_tampered_artifact_hash() {
    let repo = clean_git_repo("proof-concurrency-manifest-tampered");
    let manifest = write_concurrency_manifest(
        &repo,
        ManifestOptions { wrong_certificate_hash: true, ..Default::default() },
    );
    run_git(&repo, &["add", "."]);
    run_git(&repo, &["commit", "-m", "tampered proof artifacts"]);

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "proof-concurrency",
            "--json",
            "--manifest",
            manifest.to_str().expect("temp path should be utf-8"),
            "--repo-root",
            repo.to_str().expect("temp path should be utf-8"),
        ])
        .output()
        .expect("run proof-concurrency artifact producer with tampered hash");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "tampered hash must fail closed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "tampered manifest should not emit proof JSON");
    assert!(
        stderr.contains("hash mismatch"),
        "stderr should explain tampered hash rejection\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let _ = fs::remove_dir_all(&repo);
}

#[test]
fn proof_concurrency_manifest_rejects_missing_artifact() {
    let repo = clean_git_repo("proof-concurrency-manifest-missing");
    let manifest = write_concurrency_manifest(
        &repo,
        ManifestOptions { missing_dispatch_artifact: true, ..Default::default() },
    );
    run_git(&repo, &["add", "."]);
    run_git(&repo, &["commit", "-m", "missing proof artifact manifest"]);

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "proof-concurrency",
            "--json",
            "--manifest",
            manifest.to_str().expect("temp path should be utf-8"),
            "--repo-root",
            repo.to_str().expect("temp path should be utf-8"),
        ])
        .output()
        .expect("run proof-concurrency artifact producer with missing artifact");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "missing artifact must fail closed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "missing artifact should not emit proof JSON");
    assert!(
        stderr.contains("missing or cannot be resolved"),
        "stderr should explain missing artifact rejection\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let _ = fs::remove_dir_all(&repo);
}

#[test]
fn proof_concurrency_manifest_rejects_unknown_obligation_kind() {
    let repo = clean_git_repo("proof-concurrency-manifest-unknown-kind");
    let manifest = write_concurrency_manifest(
        &repo,
        ManifestOptions { unknown_obligation_kind: true, ..Default::default() },
    );
    run_git(&repo, &["add", "."]);
    run_git(&repo, &["commit", "-m", "unknown proof kind manifest"]);

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "proof-concurrency",
            "--json",
            "--manifest",
            manifest.to_str().expect("temp path should be utf-8"),
            "--repo-root",
            repo.to_str().expect("temp path should be utf-8"),
        ])
        .output()
        .expect("run proof-concurrency artifact producer with unknown kind");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "unknown obligation kind must fail closed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "unknown kind should not emit proof JSON");
    assert!(
        stderr.contains("failed to parse proof-concurrency manifest"),
        "stderr should explain unknown-kind manifest rejection\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let _ = fs::remove_dir_all(&repo);
}

#[test]
fn arbitrary_artifact_files_can_only_yield_nonproof_audit_and_domination_rejects_it() {
    let repo = clean_git_repo("proof-concurrency-arbitrary-artifacts");
    let manifest = write_concurrency_manifest(&repo, ManifestOptions::default());
    run_git(&repo, &["add", "."]);
    run_git(&repo, &["commit", "-m", "arbitrary presence-only artifacts"]);

    let audit = Command::new(targo_trust_binary())
        .args([
            "trust",
            "proof-concurrency",
            "--json",
            "--manifest",
            manifest.to_str().expect("temp path should be utf-8"),
            "--repo-root",
            repo.to_str().expect("temp path should be utf-8"),
        ])
        .output()
        .expect("audit arbitrary files");
    assert!(audit.status.success(), "artifact inventory itself should be auditable");
    let payload: Value = serde_json::from_slice(&audit.stdout).expect("artifact audit JSON");
    assert_eq!(payload["schema"], "trust.proof-concurrency.artifact-audit.v1");
    assert_eq!(payload["proof_authority"], "none");
    assert_eq!(payload["proof_pass"], false);
    assert_eq!(payload["summary"]["authenticated_validations"], 0);

    let audit_path = repo.join("artifact-audit.json");
    fs::write(&audit_path, &audit.stdout).expect("write audit for consumer adversary");
    let domination = Command::new(targo_trust_binary())
        .args([
            "trust",
            "domination",
            "--json",
            "--proof-concurrency-report",
            audit_path.to_str().expect("temp path should be utf-8"),
        ])
        .output()
        .expect("attempt to consume artifact audit as proof");
    assert_eq!(domination.status.code(), Some(2));
    let stderr = String::from_utf8_lossy(&domination.stderr);
    assert!(stderr.contains("non-admissible schema"), "stderr:\n{stderr}");
    assert!(stderr.contains("no proof authority"), "stderr:\n{stderr}");
    assert!(domination.stdout.is_empty());

    let _ = fs::remove_dir_all(&repo);
}

#[cfg(unix)]
#[test]
fn proof_concurrency_rejects_symlinked_manifest_and_artifacts() {
    use std::os::unix::fs::symlink;

    let repo = clean_git_repo("proof-concurrency-symlink-rejection");
    let manifest = write_concurrency_manifest(&repo, ManifestOptions::default());
    let real_manifest = manifest.with_extension("real.json");
    fs::rename(&manifest, &real_manifest).expect("move manifest target");
    symlink(&real_manifest, &manifest).expect("symlink manifest");
    run_git(&repo, &["add", "."]);
    run_git(&repo, &["commit", "-m", "symlinked manifest"]);

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "proof-concurrency",
            "--json",
            "--manifest",
            manifest.to_str().expect("temp path should be utf-8"),
            "--repo-root",
            repo.to_str().expect("temp path should be utf-8"),
        ])
        .output()
        .expect("reject symlinked manifest");
    assert_eq!(output.status.code(), Some(2));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("symbolic link"), "stderr:\n{stderr}");

    let _ = fs::remove_dir_all(&repo);

    let repo = clean_git_repo("proof-concurrency-artifact-symlink-rejection");
    let manifest = write_concurrency_manifest(&repo, ManifestOptions::default());
    let source = repo.join("proofs").join("concurrency").join("race_free_arc_mutex.source.rs");
    let external_dir = temp_test_dir("proof-concurrency-external-artifact");
    fs::create_dir_all(&external_dir).expect("create external artifact directory");
    let external_source = external_dir.join("race_free_arc_mutex.source.rs");
    fs::rename(&source, &external_source).expect("move source outside repository");
    symlink(&external_source, &source).expect("symlink source artifact");
    run_git(&repo, &["add", "."]);
    run_git(&repo, &["commit", "-m", "symlinked source artifact"]);

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "proof-concurrency",
            "--json",
            "--manifest",
            manifest.to_str().expect("temp path should be utf-8"),
            "--repo-root",
            repo.to_str().expect("temp path should be utf-8"),
        ])
        .output()
        .expect("reject symlinked artifact");
    assert_eq!(output.status.code(), Some(2));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("source_artifact"), "stderr:\n{stderr}");
    assert!(stderr.contains("symbolic link"), "stderr:\n{stderr}");

    let _ = fs::remove_dir_all(&repo);
    let _ = fs::remove_dir_all(&external_dir);
}

#[test]
fn proof_concurrency_stub_alias_emits_unmistakable_nonproof_demo_audit() {
    let repo = clean_git_repo("proof-concurrency-stub-contract");
    let expected_head = git_stdout(&repo, &["rev-parse", "HEAD"]);

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "proof-concurrency",
            "--format",
            "json",
            "--stub-proved",
            "--repo-root",
            repo.to_str().expect("temp path should be utf-8"),
        ])
        .output()
        .expect("run proof-concurrency stub producer");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "stub producer should emit contract JSON from clean repo\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stderr.trim().is_empty(), "successful JSON mode should keep stderr empty");

    let report: ProofConcurrencyAuditReport =
        serde_json::from_slice(&output.stdout).expect("proof-concurrency JSON should parse");
    assert_eq!(report.schema, "trust.proof-concurrency.demo-audit.v1");
    assert_eq!(report.mode, "synthetic_demo_audit");
    assert_eq!(report.proof_authority, "none");
    assert!(!report.proof_pass);
    assert!(!report.validator_available);
    assert!(!report.validation_performed);
    assert!(!report.replay_performed);
    assert!(!report.generated_at.trim().is_empty());
    assert_eq!(report.repo_head, expected_head);
    assert!(is_full_git_sha(&report.repo_head));
    assert!(!report.repo_dirty);
    assert!(report.repo_dirty_metadata.available);
    assert!(!report.repo_dirty_metadata.dirty);
    assert!(report.repo_dirty_metadata.porcelain_v1.is_empty());
    assert_eq!(report.repo_dirty_metadata.untracked_files, "all");
    assert_eq!(report.repo_dirty_metadata.ignore_submodules, "none");

    assert_eq!(report.runner["python_used"], false);
    assert_eq!(report.runner["implementation"], "rust");
    assert_eq!(report.runner["entrypoint"], "targo trust proof-concurrency");
    assert_eq!(report.runner["mode"], "synthetic_demo_audit");
    assert_eq!(report.runner["audit_kind"], "nonproof_contract_shape_only");

    assert_eq!(report.summary.total_obligations, 3);
    assert_eq!(report.summary.artifact_sets_present, 0);
    assert_eq!(report.summary.artifact_sets_hash_bound, 0);
    assert_eq!(report.summary.authenticated_validations, 0);
    assert_eq!(report.summary.replays_performed, 0);

    let kinds: BTreeSet<&str> =
        report.obligations.iter().map(|obligation| obligation.kind.as_str()).collect();
    assert_eq!(kinds, BTreeSet::from(["atomic_ordering", "data_race_free", "happens_before"]));
    for obligation in report.obligations {
        assert!(!obligation.id.trim().is_empty());
        assert_eq!(obligation.status, "synthetic_demo_only");
        assert_eq!(obligation.source, "not-generated");
        assert!(!obligation.memory_model.trim().is_empty());
        assert!(obligation.artifacts.is_none());
    }

    let _ = fs::remove_dir_all(&repo);
}

#[test]
fn proof_concurrency_stub_rejects_dirty_repo() {
    let repo = clean_git_repo("proof-concurrency-dirty-rejection");
    fs::write(repo.join("untracked.rs"), "fn main() {}\n").expect("write untracked file");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "proof-concurrency",
            "--json",
            "--stub-proved",
            "--repo-root",
            repo.to_str().expect("temp path should be utf-8"),
        ])
        .output()
        .expect("run proof-concurrency stub producer on dirty repo");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "dirty repo must fail closed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "dirty repo should not emit proof JSON");
    assert!(
        stderr.contains("repo must be clean"),
        "stderr should explain clean provenance requirement\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let _ = fs::remove_dir_all(&repo);
}

fn clean_git_repo(label: &str) -> PathBuf {
    let repo = temp_test_dir(label);
    fs::create_dir_all(&repo).expect("create temp repo");
    run_git(&repo, &["init"]);
    run_git(&repo, &["config", "user.email", "trust-tests@example.invalid"]);
    run_git(&repo, &["config", "user.name", "Trust Tests"]);
    fs::write(repo.join("proof.rs"), "use std::sync::{Arc, Mutex};\n").expect("write fixture");
    run_git(&repo, &["add", "."]);
    run_git(&repo, &["commit", "-m", "fixture"]);
    repo
}

#[derive(Debug, Clone, Copy, Default)]
struct ManifestOptions {
    wrong_certificate_hash: bool,
    missing_dispatch_artifact: bool,
    unknown_obligation_kind: bool,
}

fn write_concurrency_manifest(repo: &Path, options: ManifestOptions) -> PathBuf {
    write_concurrency_manifest_in(
        repo.join("proofs").join("concurrency"),
        "manifest.json",
        "proofs/concurrency",
        options,
    )
}

fn write_default_concurrency_manifest(repo: &Path, options: ManifestOptions) -> PathBuf {
    write_concurrency_manifest_in(
        repo.join("reports").join("proof"),
        "concurrency-inputs.json",
        "reports/proof",
        options,
    )
}

fn write_default_concurrency_artifacts(repo: &Path) -> PathBuf {
    let proof_dir = repo.join("reports").join("proof").join("concurrency-artifacts");
    fs::create_dir_all(&proof_dir).expect("create proof artifact dir");
    for id in ["race_free_arc_mutex", "atomic_release_acquire", "channel_happens_before"] {
        fs::write(
            proof_dir.join(format!("{id}.source.rs")),
            format!("// {id} source fixture\nfn {id}_fixture() {{}}\n"),
        )
        .expect("write source artifact");
        fs::write(proof_dir.join(format!("{id}.proof")), format!("proof transcript for {id}\n"))
            .expect("write proof transcript");
        fs::write(proof_dir.join(format!("{id}.cert")), format!("checked certificate for {id}\n"))
            .expect("write certificate artifact");
        fs::write(proof_dir.join(format!("{id}.dispatch")), format!("solver dispatch for {id}\n"))
            .expect("write dispatch artifact");
    }
    proof_dir
}

fn write_concurrency_manifest_in(
    proof_dir: PathBuf,
    manifest_name: &str,
    source_prefix: &str,
    options: ManifestOptions,
) -> PathBuf {
    fs::create_dir_all(&proof_dir).expect("create proof dir");

    let mut obligations = Vec::new();
    for (id, kind) in [
        ("race_free_arc_mutex", "data_race_free"),
        ("atomic_release_acquire", "atomic_ordering"),
        ("channel_happens_before", "happens_before"),
    ] {
        let source = format!("{id}.source.rs");
        let proof = format!("{id}.proof");
        let certificate = format!("{id}.cert");
        let dispatch = format!("{id}.dispatch");
        fs::write(
            proof_dir.join(&source),
            format!("// {id} source fixture\nfn {id}_fixture() {{}}\n"),
        )
        .expect("write source artifact");
        fs::write(proof_dir.join(&proof), format!("proof transcript for {id}\n"))
            .expect("write proof transcript");
        fs::write(proof_dir.join(&certificate), format!("checked certificate for {id}\n"))
            .expect("write certificate artifact");
        if !(options.missing_dispatch_artifact && id == "channel_happens_before") {
            fs::write(proof_dir.join(&dispatch), format!("solver dispatch for {id}\n"))
                .expect("write dispatch artifact");
        }

        let certificate_sha256 = if options.wrong_certificate_hash && id == "atomic_release_acquire"
        {
            "0000000000000000000000000000000000000000000000000000000000000000".to_string()
        } else {
            file_sha256(&proof_dir.join(&certificate))
        };
        let manifest_kind = if options.unknown_obligation_kind && id == "atomic_release_acquire" {
            "temporal_ordering"
        } else {
            kind
        };
        obligations.push(serde_json::json!({
            "id": id,
            "kind": manifest_kind,
            "source": format!("{source_prefix}/{source}"),
            "source_artifact": source,
            "proof_artifact": proof,
            "certificate_artifact": certificate,
            "dispatch_artifact": dispatch,
            "source_sha256": file_sha256(&proof_dir.join(format!("{id}.source.rs"))),
            "proof_sha256": file_sha256(&proof_dir.join(format!("{id}.proof"))),
            "certificate_sha256": certificate_sha256,
            "dispatch_sha256": if options.missing_dispatch_artifact && id == "channel_happens_before" {
                "1111111111111111111111111111111111111111111111111111111111111111".to_string()
            } else {
                file_sha256(&proof_dir.join(format!("{id}.dispatch")))
            }
        }));
    }

    let manifest = serde_json::json!({
        "schema": "trust.proof-concurrency.inputs.v1",
        "solver": "trust-concurrency-prover-test-v1",
        "memory_model": "rust-abstract-machine+llvm-atomics",
        "obligations": obligations
    });
    let manifest_path = proof_dir.join(manifest_name);
    fs::write(&manifest_path, serde_json::to_vec_pretty(&manifest).expect("serialize manifest"))
        .expect("write manifest");
    manifest_path
}

fn run_git(repo: &Path, args: &[&str]) {
    let output = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("run git {}: {error}", args.join(" ")));
    assert!(
        output.status.success(),
        "git {} failed\nstdout:\n{}\nstderr:\n{}",
        args.join(" "),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn git_stdout(repo: &Path, args: &[&str]) -> String {
    let output = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("run git {}: {error}", args.join(" ")));
    assert!(
        output.status.success(),
        "git {} failed\nstdout:\n{}\nstderr:\n{}",
        args.join(" "),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).trim().to_string()
}

fn is_full_git_sha(value: &str) -> bool {
    value.len() == 40 && value.chars().all(|ch| ch.is_ascii_hexdigit())
}

fn is_sha256_hex(value: &str) -> bool {
    value.len() == 64 && value.chars().all(|ch| ch.is_ascii_hexdigit() && !ch.is_ascii_uppercase())
}

fn file_sha256(path: &Path) -> String {
    let bytes = fs::read(path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    let digest = hasher.finalize();
    hex_digest(&digest)
}

fn hex_digest(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        output.push(HEX[(byte >> 4) as usize] as char);
        output.push(HEX[(byte & 0x0f) as usize] as char);
    }
    output
}

fn temp_test_dir(label: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after epoch")
        .as_nanos();
    std::env::temp_dir().join(format!("targo-trust-{label}-{}-{unique}", std::process::id()))
}

fn targo_trust_binary() -> PathBuf {
    if let Some(path) = option_env!("CARGO_BIN_EXE_targo-trust") {
        return PathBuf::from(path);
    }

    let mut path = std::env::current_exe().expect("current test executable path");
    path.pop();
    if path.ends_with("deps") {
        path.pop();
    }
    path.push(format!("targo-trust{}", std::env::consts::EXE_SUFFIX));
    path
}
