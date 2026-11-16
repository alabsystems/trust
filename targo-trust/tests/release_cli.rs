#[path = "support/release_fixture.rs"]
mod release_fixture;

use std::path::PathBuf;
use std::process::Command;

use release_fixture::ReleaseFixture;
use serde_json::Value;

#[test]
fn trustd_evidence_collector_is_public_and_requires_a_candidate() {
    let release_help = Command::new(targo_trust_binary())
        .args(["trust", "release", "--help"])
        .output()
        .expect("run release help");
    assert!(release_help.status.success(), "release help must succeed");
    assert!(
        String::from_utf8_lossy(&release_help.stdout)
            .contains("targo trust release collect-trustd-evidence"),
        "release help must advertise the production trustd evidence collector"
    );

    let help = Command::new(targo_trust_binary())
        .args(["trust", "release", "collect-trustd-evidence", "--help"])
        .output()
        .expect("run trustd evidence collector help");
    assert!(help.status.success(), "collector help must succeed");
    let help_stdout = String::from_utf8_lossy(&help.stdout);
    assert!(
        help_stdout.contains("targo trust release collect-trustd-evidence")
            && help_stdout.contains("--candidate-commit <40-hex>")
            && help_stdout.contains("build/product-proof"),
        "collector help must document its candidate and ignored-output contract: {help_stdout}"
    );

    let missing = Command::new(targo_trust_binary())
        .args(["trust", "release", "collect-trustd-evidence", "--json"])
        .output()
        .expect("run collector without candidate");
    assert_eq!(missing.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&missing.stderr).contains("--candidate-commit is required"),
        "collector must fail closed when candidate authority is absent"
    );
}

#[cfg(unix)]
#[test]
fn trustd_evidence_collector_rejects_worktree_dirtying_output_as_argument_error() {
    let repo = tempfile::tempdir().expect("temporary Git repository");
    let init = Command::new("git")
        .args(["init", "-q"])
        .arg(repo.path())
        .output()
        .expect("initialize temporary Git repository");
    assert!(init.status.success(), "git init failed: {}", String::from_utf8_lossy(&init.stderr));
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "release",
            "collect-trustd-evidence",
            "--candidate-commit",
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            "--repo-root",
        ])
        .arg(repo.path())
        .args(["--out", "release/unsafe-collector-output.json"])
        .output()
        .expect("run collector with unignored output");
    assert_eq!(output.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("is not ignored by a tracked .gitignore"),
        "collector must reject an output that would dirty the candidate: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn metadata_release_check_is_machine_readable_and_non_blocking() {
    let repo_root = discovered_repo_root_for_test();
    let output = Command::new(targo_trust_binary())
        .args(["trust", "release", "check", "--profile=metadata", "--format=json", "--repo-root"])
        .arg(&repo_root)
        .output()
        .expect("run metadata release check");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "metadata release check should not block local diagnostics\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stderr.is_empty(), "JSON release check should stay on stdout");

    let json: Value = serde_json::from_slice(&output.stdout).expect("parse release check json");
    assert_eq!(json["schema_version"], "trust.release-report.v1");
    assert!(json["generated_at"].as_u64().is_some());
    assert_eq!(json["profile"], "metadata");
    assert_eq!(json["visibility"], "private");
    assert_eq!(json["evidence_mode"], "diagnostic-only");
    assert_eq!(json["release_evidence"]["claim"], "diagnostic-only");
    assert_eq!(json["release_evidence"]["golden_path"], false);
    assert_eq!(json["repo_root"], repo_root.display().to_string());
    assert!(json["repo_dirty_metadata"]["porcelain_v1"].as_array().is_some());
    if json["repo_dirty_metadata"]["available"] == true {
        assert!(json["repo_dirty_metadata"]["dirty"].as_bool().is_some());
        assert_eq!(json["repo_dirty_metadata"]["untracked_files"], "all");
        assert_eq!(json["repo_dirty_metadata"]["ignore_submodules"], "none");
    } else {
        assert_eq!(json["repo_dirty_metadata"]["available"], false);
        assert_eq!(json["repo_dirty_metadata"]["dirty"], Value::Null);
        assert_eq!(json["repo_dirty"], true);
    }
    assert_eq!(json["candidate_command"], "targo trust release check");
    assert_eq!(json["candidate_command_version"], 1);
    assert_eq!(json["tools"]["frontend"]["name"], "targo");
    assert_eq!(json["tools"]["extension"]["name"], "targo-trust");
    assert_eq!(json["tools"]["compiler"]["name"], "trustc");
    assert_eq!(json["tools"]["documentation"]["name"], "trustdoc");
    assert_eq!(json["tools"]["formatter"]["name"], "trustfmt");
    assert_eq!(json["tools"]["tippy"]["name"], "tippy");
    assert_eq!(json["tools"]["targo_tippy"]["name"], "targo-tippy");
    assert_eq!(json["tools"]["tippy_driver"]["name"], "tippy-driver");
    assert_eq!(json["tools"]["analyzer"]["name"], "trust-analyzer");
    assert_eq!(json["tools"]["daemon"]["name"], "trustd");
    assert_eq!(json["tools"]["miri"]["name"], "trust-miri");
    assert_eq!(json["tools"]["targo_miri"]["name"], "targo-miri");
    assert_eq!(
        json["toolchain_surface_proof"]["schema"],
        "trust.targo.toolchain-surface-sysroot.v1"
    );
    assert!(
        json["toolchain_surface_proof"]["same_sysroot"].as_bool().is_some(),
        "release JSON should carry same-sysroot proof: {json}"
    );
    assert!(
        json["toolchain_surface_proof"]["required_tools"].as_array().is_some_and(|tools| tools
            .iter()
            .any(|tool| tool["name"] == "trustc" && tool["canonical_name"].as_bool().is_some())),
        "release JSON should classify canonical Trust tools: {json}"
    );
    assert_eq!(json["version_identity"]["tools"]["frontend"]["name"], "targo");
    assert_eq!(json["version_identity"]["tools"]["extension"]["name"], "targo-trust");
    assert_eq!(json["version_identity"]["tools"]["compiler"]["name"], "trustc");
    assert_eq!(json["version_identity"]["tools"]["documentation"]["name"], "trustdoc");
    assert_eq!(json["version_identity"]["tools"]["formatter"]["name"], "trustfmt");
    assert_eq!(json["version_identity"]["tools"]["tippy"]["name"], "tippy");
    assert_eq!(json["version_identity"]["tools"]["targo_tippy"]["name"], "targo-tippy");
    assert_eq!(json["version_identity"]["tools"]["tippy_driver"]["name"], "tippy-driver");
    assert_eq!(json["version_identity"]["tools"]["analyzer"]["name"], "trust-analyzer");
    assert_eq!(json["version_identity"]["tools"]["daemon"]["name"], "trustd");
    assert_eq!(json["version_identity"]["tools"]["miri"]["name"], "trust-miri");
    assert_eq!(json["version_identity"]["tools"]["targo_miri"]["name"], "targo-miri");
    assert!(json["reports"].as_array().is_some_and(|reports| !reports.is_empty()));
    assert!(
        json["reports"]
            .as_array()
            .unwrap()
            .iter()
            .all(|report| report["release_critical"].as_bool().is_some())
    );
}

#[test]
fn metadata_private_terminal_release_check_renders_evidence_semantics() {
    let fixture = ReleaseFixture::new(&discovered_repo_root_for_test());
    let repo_root = fixture.path();
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "release",
            "check",
            "--profile=metadata",
            "--visibility=private",
            "--format=terminal",
            "--repo-root",
        ])
        .arg(&repo_root)
        .output()
        .expect("run metadata private terminal release check");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    fixture.assert_clean_terminal(&stdout);
    assert!(
        output.status.success(),
        "metadata private terminal release check should not block diagnostics\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stderr.is_empty(), "terminal release check should stay on stdout");
    assert!(
        stdout.contains("Trust release check metadata [private]"),
        "terminal output should identify metadata/private mode\nstdout:\n{stdout}"
    );
    assert!(
        stdout.contains("evidence mode: diagnostic-only"),
        "terminal output should render evidence_mode\nstdout:\n{stdout}"
    );
    assert!(
        stdout.contains("release evidence claim: diagnostic-only"),
        "terminal output should render release_evidence.claim\nstdout:\n{stdout}"
    );
    assert!(
        stdout.contains(
            "release evidence reason: release check output is local metadata diagnostics, not golden-path release evidence"
        ),
        "terminal output should explain why the output is diagnostic-only\nstdout:\n{stdout}"
    );
    assert!(
        !stdout.contains("release evidence claim: golden-path"),
        "metadata/private terminal output must not claim golden-path evidence\nstdout:\n{stdout}"
    );
}

#[test]
fn public_visibility_is_explicit_in_release_check_output() {
    let fixture = ReleaseFixture::new(&discovered_repo_root_for_test());
    let output = Command::new(targo_trust_binary())
        .current_dir(fixture.path())
        .args([
            "trust",
            "release",
            "check",
            "--profile=metadata",
            "--visibility=public",
            "--format=json",
        ])
        .output()
        .expect("run public metadata release check");

    let json: Value = serde_json::from_slice(&output.stdout).expect("parse release check json");
    fixture.assert_clean_report(&json);
    assert_eq!(json["profile"], "metadata");
    assert_eq!(json["visibility"], "public");
    assert_eq!(json["evidence_mode"], "diagnostic-only");
    assert_eq!(json["release_evidence"]["claim"], "diagnostic-only");
    assert_eq!(json["release_evidence"]["golden_path"], false);
    assert!(
        json["reports"]
            .as_array()
            .is_some_and(|reports| { reports.iter().any(|report| report["gate"] == "tool-names") }),
        "public release check should include public tool-name evidence"
    );
    #[cfg(unix)]
    fixture.assert_submodule_content_is_checked(&targo_trust_binary());
}

#[test]
fn publication_profile_requires_explicit_public_visibility() {
    for args in [
        vec!["trust", "release", "check", "--profile=publication", "--json"],
        vec![
            "trust",
            "release",
            "check",
            "--profile=publication",
            "--visibility=private",
            "--format=terminal",
        ],
    ] {
        let output = Command::new(targo_trust_binary())
            .args(args)
            .output()
            .expect("run publication release check without public visibility");

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(2),
            "publication profile should require explicit public visibility\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stdout.trim().is_empty(),
            "publication visibility setup failure should not emit a release report\nstdout:\n{stdout}"
        );
        assert!(
            stderr.contains("--profile publication requires explicit --visibility public"),
            "{stderr}"
        );
    }
}

#[test]
fn release_check_rejects_removed_audience_alias() {
    for args in [
        vec!["trust", "release", "check", "--audience", "public"],
        vec!["trust", "release", "check", "--audience=public"],
    ] {
        let output = Command::new(targo_trust_binary())
            .args(args)
            .output()
            .expect("run release check with removed audience alias");

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(2),
            "removed release audience alias should be rejected\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stdout.trim().is_empty(),
            "removed alias should not emit a release report\nstdout:\n{stdout}"
        );
        assert!(stderr.contains("--audience has been removed; use --visibility"), "{stderr}");
    }
}

#[test]
fn release_check_rejects_removed_visibility_aliases() {
    for (alias, replacement) in
        [("--private", "--visibility private"), ("--public", "--visibility public")]
    {
        let output = Command::new(targo_trust_binary())
            .args(["trust", "release", "check", alias])
            .output()
            .expect("run release check with removed visibility alias");

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(2),
            "removed release visibility alias should be rejected\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stdout.trim().is_empty(),
            "removed alias should not emit a release report\nstdout:\n{stdout}"
        );
        assert!(
            stderr.contains(&format!("{alias} has been removed; use {replacement}")),
            "{stderr}"
        );
    }
}

#[test]
fn release_check_rejects_removed_visibility_values() {
    for args in [
        vec!["trust", "release", "check", "--visibility", "local"],
        vec!["trust", "release", "check", "--visibility=internal"],
    ] {
        let output = Command::new(targo_trust_binary())
            .args(args)
            .output()
            .expect("run release check with removed visibility value");

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(2),
            "removed release visibility value should be rejected\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stdout.trim().is_empty(),
            "removed visibility value should not emit a release report\nstdout:\n{stdout}"
        );
        assert!(stderr.contains("--visibility must be private or public"), "{stderr}");
    }
}

#[test]
fn release_check_records_gate_filter_and_fails_closed_for_unknown_gate() {
    let fixture = ReleaseFixture::new(&discovered_repo_root_for_test());
    let repo_root = fixture.path();
    // A passing known filter makes ignored filtering observable. The unknown
    // case below must still produce its one explicit gate-filter failure.
    let known = Command::new(targo_trust_binary())
        .args(["trust", "release", "check", "--profile=metadata", "--json", "--repo-root"])
        .arg(repo_root)
        .args(["--gate", "required-metadata"])
        .output()
        .expect("run known metadata gate filter");
    assert!(
        known.status.success(),
        "known metadata filter: {}",
        String::from_utf8_lossy(&known.stderr)
    );
    assert!(known.stderr.is_empty(), "known JSON filter should stay on stdout");
    let known_json: Value = serde_json::from_slice(&known.stdout).expect("parse known gate filter");
    fixture.assert_clean_report(&known_json);
    let known_reports = known_json["reports"].as_array().expect("known reports array");
    assert_eq!(known_reports.len(), 2, "known filter must omit unrelated reports: {known_json}");
    for gate in ["required-metadata", "repository-state"] {
        assert!(
            known_reports.iter().any(|report| report["gate"] == gate && report["status"] == "pass"),
            "known filter must keep passing `{gate}`: {known_json}"
        );
    }

    assert_eq!(known_json["status"], "pass");

    let output = Command::new(targo_trust_binary())
        .args(["trust", "release", "check", "--profile=metadata", "--json", "--repo-root"])
        .arg(&repo_root)
        .args(["--gate", "not-a-release-gate"])
        .output()
        .expect("run release check with unknown gate filter");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "unknown release gate must fail closed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stderr.is_empty(), "JSON release check should stay on stdout");

    let json: Value = serde_json::from_slice(&output.stdout).expect("parse release check json");
    fixture.assert_clean_report(&json);
    assert_eq!(json["gate_filter"], "not-a-release-gate");
    assert_eq!(json["status"], "fail");
    assert_eq!(json["exit_code_kind"], "release_blocked");
    let reports = json["reports"].as_array().expect("reports array");
    assert_eq!(reports.len(), 1);
    assert_eq!(reports[0]["gate"], "gate-filter");
    assert_eq!(reports[0]["findings"][0]["code"], "unknown-gate");
}

#[test]
fn product_proof_gate_filter_cannot_hide_mandatory_failures() {
    let fixture = ReleaseFixture::new(&discovered_repo_root_for_test());
    let repo_root = fixture.path();
    let output = Command::new(targo_trust_binary())
        .args(["trust", "release", "check", "--profile=product-proof", "--json", "--repo-root"])
        .arg(&repo_root)
        .args(["--gate", "required-metadata"])
        .output()
        .expect("run filtered product-proof release check");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "product-proof gate filter must not hide mandatory blockers\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stderr.is_empty(), "JSON release check should stay on stdout");

    let json: Value = serde_json::from_slice(&output.stdout).expect("parse release check json");
    fixture.assert_clean_report(&json);
    assert_eq!(json["profile"], "product-proof");
    assert_eq!(json["gate_filter"], "required-metadata");
    assert!(
        matches!(json["status"].as_str(), Some("blocked" | "fail")),
        "filtered product-proof status must remain non-pass: {json}"
    );
    assert!(
        matches!(json["exit_code_kind"].as_str(), Some("missing_evidence" | "release_blocked")),
        "filtered product-proof exit kind must remain blocking: {json}"
    );
    let reports = json["reports"].as_array().expect("reports array");
    for expected in [
        "required-metadata",
        "version-identity",
        "bound-tool-files",
        "toolchain-surface-sysroot",
        "tool-names",
        "owned-deps",
        "trust-extra",
        "product-proof-coverage",
    ] {
        assert!(
            reports.iter().any(|report| report["gate"] == expected),
            "filtered product-proof output must include `{expected}`: {json}"
        );
    }
    assert!(
        reports.iter().any(|report| {
            report["gate"] == "trust-extra" && report["status"].as_str() == Some("blocked")
        }),
        "trust-extra blocker must stay in aggregate status: {json}"
    );
    assert!(
        json["product_proof_evidence_classes"]
            .as_array()
            .is_some_and(|classes| !classes.is_empty()),
        "filtered product-proof output should keep product-proof matrix semantics: {json}"
    );
}

#[test]
fn publication_gate_filter_cannot_hide_common_release_failures() {
    let fixture = ReleaseFixture::new(&discovered_repo_root_for_test());
    let repo_root = fixture.path();
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "release",
            "check",
            "--profile=publication",
            "--visibility=public",
            "--json",
            "--repo-root",
        ])
        .arg(&repo_root)
        .args(["--gate", "required-metadata"])
        .output()
        .expect("run filtered publication release check");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "publication gate filter must not hide common release blockers\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stderr.is_empty(), "JSON release check should stay on stdout");

    let json: Value = serde_json::from_slice(&output.stdout).expect("parse release check json");
    fixture.assert_clean_report(&json);
    assert_eq!(json["profile"], "publication");
    assert_eq!(json["visibility"], "public");
    assert_eq!(json["gate_filter"], "required-metadata");
    assert_eq!(json["status"], "fail");
    assert_eq!(json["exit_code_kind"], "release_blocked");
    let reports = json["reports"].as_array().expect("reports array");
    for gate in ["required-metadata", "repository-state"] {
        assert!(
            reports.iter().any(|report| report["gate"] == gate && report["status"] == "pass"),
            "unrelated fixture failures must not mask mandatory gates: {json}"
        );
    }
    for expected in [
        "required-metadata",
        "version-identity",
        "bound-tool-files",
        "toolchain-surface-sysroot",
        "tool-names",
        "owned-deps",
        "publication-inputs",
        "publication-artifacts",
        "publication-ledger",
    ] {
        assert!(
            reports.iter().any(|report| report["gate"] == expected),
            "filtered publication output must include `{expected}`: {json}"
        );
    }
    assert!(
        reports.iter().any(|report| {
            matches!(
                report["gate"].as_str(),
                Some("bound-tool-files" | "toolchain-surface-sysroot")
            ) && report["status"].as_str() != Some("pass")
        }),
        "bound toolchain blockers must stay in aggregate status: {json}"
    );
    assert!(
        reports.iter().any(|report| {
            matches!(
                report["gate"].as_str(),
                Some("publication-inputs" | "publication-artifacts" | "publication-ledger")
            )
        }),
        "publication blockers must stay in aggregate status: {json}"
    );
}

#[test]
fn public_product_proof_gate_filter_cannot_hide_publication_failures() {
    let fixture = ReleaseFixture::new(&discovered_repo_root_for_test());
    let repo_root = fixture.path();
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "release",
            "check",
            "--profile=product-proof",
            "--visibility=public",
            "--json",
            "--repo-root",
        ])
        .arg(&repo_root)
        .args(["--gate", "required-metadata"])
        .output()
        .expect("run filtered public product-proof release check");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "public product-proof gate filter must not hide mandatory blockers\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stderr.is_empty(), "JSON release check should stay on stdout");

    let json: Value = serde_json::from_slice(&output.stdout).expect("parse release check json");
    fixture.assert_clean_report(&json);
    assert_eq!(json["profile"], "product-proof");
    assert_eq!(json["visibility"], "public");
    assert_eq!(json["evidence_mode"], "golden-path");
    assert_eq!(json["release_evidence"]["claim"], "golden-path");
    assert_eq!(json["release_evidence"]["golden_path"], true);
    assert_eq!(json["gate_filter"], "required-metadata");
    assert_eq!(json["status"], "fail");
    assert_eq!(json["exit_code_kind"], "release_blocked");
    let reports = json["reports"].as_array().expect("reports array");
    for expected in [
        "required-metadata",
        "version-identity",
        "bound-tool-files",
        "toolchain-surface-sysroot",
        "tool-names",
        "owned-deps",
        "publication-inputs",
        "publication-artifacts",
        "publication-ledger",
        "trust-extra",
        "product-proof-coverage",
    ] {
        assert!(
            reports.iter().any(|report| report["gate"] == expected),
            "filtered public product-proof output must include `{expected}`: {json}"
        );
    }
    assert!(
        reports.iter().any(|report| {
            report["gate"] == "publication-ledger" && report["status"].as_str() != Some("pass")
        }),
        "publication-ledger blocker must stay in aggregate status: {json}"
    );
}

#[test]
fn product_proof_release_check_reports_complete_missing_matrix() {
    let fixture = ReleaseFixture::new(&discovered_repo_root_for_test());
    let output = Command::new(targo_trust_binary())
        .current_dir(fixture.path())
        .args(["trust", "release", "check", "--profile", "product-proof", "--json"])
        .output()
        .expect("run product-proof release check");

    let json: Value = serde_json::from_slice(&output.stdout).expect("parse release check json");
    fixture.assert_clean_report(&json);
    assert!(!output.status.success(), "product-proof should fail closed without evidence");
    assert_eq!(json["profile"], "product-proof");
    assert_eq!(json["visibility"], "private");
    assert_eq!(json["evidence_mode"], "diagnostic-only");
    assert_eq!(json["release_evidence"]["claim"], "diagnostic-only");
    assert_eq!(json["release_evidence"]["golden_path"], false);
    if json["repo_dirty_metadata"]["available"] == true {
        assert_eq!(json["repo_dirty_metadata"]["untracked_files"], "all");
        assert_eq!(json["repo_dirty_metadata"]["ignore_submodules"], "none");
    } else {
        assert_eq!(json["repo_dirty"], true);
        assert_eq!(json["repo_dirty_metadata"]["dirty"], Value::Null);
    }
    assert!(
        json["reports"]
            .as_array()
            .is_some_and(|reports| reports.iter().any(|report| report["gate"] == "trust-extra")),
        "product-proof release check should expose the trust-extra gate binding"
    );
    let evidence_classes =
        json["product_proof_evidence_classes"].as_array().expect("evidence-class matrix");
    for expected in [
        "no-verification compatibility",
        "strict Tier-0 proof",
        "native proof engines",
        "hardened proof",
        "trust-cg",
        "dependency integrity",
        "upstream compatibility",
        "distribution install",
        "self-build",
    ] {
        assert!(
            evidence_classes.iter().any(|evidence_class| evidence_class["class"] == expected),
            "missing evidence class {expected}"
        );
    }
    let strict_tier0 = evidence_classes
        .iter()
        .find(|evidence_class| evidence_class["class"] == "strict Tier-0 proof")
        .expect("strict Tier-0 proof evidence class");
    assert_eq!(strict_tier0["status"], "missing_evidence");
    assert_eq!(strict_tier0["release_claim"], "proof");
    assert_eq!(strict_tier0["gates"].as_array().expect("strict gates").len(), 1);
    assert!(
        strict_tier0["required_evidence"].as_array().is_some_and(|required| !required.is_empty())
    );

    let components = json["product_proof_components"].as_array().expect("component matrix");
    for expected in [
        "trustc compiler",
        "targo frontend",
        "targo-trust subcommand implementation",
        "trustdoc",
        "trustfmt",
        "tippy",
        "targo-tippy",
        "tippy-driver",
        "trust-analyzer",
        "trust-miri",
        "targo-miri",
        "std",
        "source/docs",
        "LLVM/trust-cg",
        "stage0",
        "verifier engines",
        "upstream tests",
        "binary/decomp gates",
    ] {
        assert!(
            components.iter().any(|component| component["component"] == expected),
            "missing {expected}"
        );
    }
}

/// The filter cases need real release/Git validation, but no compiler source
/// tree. Keep the requested metadata gate and repository-state gate passing so
/// unrelated fixture failures cannot mask a lost mandatory gate or bad aggregate.
fn release_metadata_git_fixture() -> (tempfile::TempDir, String) {
    let repo = tempfile::tempdir().expect("temporary release Git repository");
    for (relative, contents) in [
        ("release/trust-version.toml", include_str!("../../release/trust-version.toml")),
        ("src/version", include_str!("../../src/version")),
        ("src/rust-compat-version", include_str!("../../src/rust-compat-version")),
        ("src/ci/channel", include_str!("../../src/ci/channel")),
    ] {
        let path = repo.path().join(relative);
        std::fs::create_dir_all(path.parent().expect("metadata parent"))
            .expect("create release metadata parent");
        std::fs::write(path, contents).expect("write regular release metadata file");
    }
    fixture_git(
        repo.path(),
        &["init", "--quiet", "--template=", "--object-format=sha1", "--initial-branch=main"],
    );
    fixture_git(repo.path(), &["add", "--", "release", "src"]);
    fixture_git(repo.path(), &["commit", "--quiet", "-m", "release metadata fixture"]);
    let head = fixture_git(repo.path(), &["rev-parse", "HEAD"]);
    let commit = String::from_utf8(head.stdout).expect("fixture HEAD UTF-8").trim().to_owned();
    (repo, commit)
}

fn fixture_git(root: &std::path::Path, args: &[&str]) -> std::process::Output {
    let mut command = Command::new("git");
    // A test can run inside a Git hook. Its inherited index/worktree/object
    // routing must never turn fixture setup into a write to the caller's repo.
    for (key, _) in std::env::vars_os() {
        if key.to_string_lossy().starts_with("GIT_") {
            command.env_remove(key);
        }
    }
    let output = command
        .current_dir(root)
        // Global/system Git configuration can install filters or fsmonitor
        // commands even in a freshly initialized repository.
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_SYSTEM", "/dev/null")
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_ATTR_NOSYSTEM", "1")
        .args([
            "-c",
            "user.name=Trust test fixture",
            "-c",
            "user.email=trust-fixture@example.invalid",
            "-c",
            "core.hooksPath=/dev/null",
            "-c",
            "commit.gpgsign=false",
        ])
        .args(args)
        .output()
        .expect("run real Git for release fixture");
    assert!(
        output.status.success(),
        "fixture Git {args:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

fn assert_clean_release_fixture(json: &Value, root: &std::path::Path, commit: &str) {
    assert_eq!(json["candidate_commit"], commit);
    assert_eq!(
        json["repo_root"],
        root.canonicalize().expect("canonical fixture root").display().to_string()
    );
    assert_eq!(json["repo_dirty"], false);
    assert_eq!(json["repo_dirty_metadata"]["available"], true);
    assert_eq!(json["repo_dirty_metadata"]["dirty"], false);
    assert_eq!(json["repo_dirty_metadata"]["porcelain_v1"], serde_json::json!([]));
}

fn discovered_repo_root_for_test() -> PathBuf {
    let mut current = std::env::current_dir().expect("current dir");
    loop {
        if current.join("release/trust-version.toml").is_file()
            && current.join("src/version").is_file()
        {
            return current;
        }
        if !current.pop() {
            return std::env::current_dir().expect("current dir fallback");
        }
    }
}

/// `release validate ledger` was renamed to `ledger-expirations`, and the
/// removed spelling must keep naming its replacement instead of falling through
/// to the generic `unknown command` usage dump.
///
/// This arm has no in-repo caller by construction — only users type the old
/// name — so a dead-code sweep reads it as dead. fc5a9655a0 deleted it for
/// exactly that reason, and no test noticed. This is that test.
#[test]
fn removed_release_validate_ledger_alias_points_to_ledger_expirations() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "release", "validate", "ledger", "--help"])
        .output()
        .expect("run removed release validate ledger alias");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "release validate ledger alias should be removed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "removed alias should not run help\nstdout:\n{stdout}");
    assert!(
        stderr.contains(
            "targo trust release validate ledger: removed alias; \
             use `targo trust release validate ledger-expirations`"
        ),
        "release validate ledger alias should explain the canonical command\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// `release validate conformance` runs no tool: every trust-conformance check
/// reads committed files only (a fixture exists, or a field of a committed JSON
/// fixture equals a manifest literal or another committed file's sha256). The
/// command must say NOT EVIDENCE before it runs, and the report it writes must
/// mark each such case `static_only`, so neither the terminal nor a consumer of
/// `trust-conformance-report/v1` can present fixture text ("unsat",
/// "kernel_checked: true") as tool output.
#[test]
fn release_validate_conformance_says_not_evidence_and_marks_static_cases() {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("targo-trust sits in the Trust checkout")
        .to_path_buf();
    let out_dir = tempfile::tempdir().expect("temporary report directory");
    let report_path = out_dir.path().join("trust-conformance-report.json");
    let output = Command::new(targo_trust_binary())
        .args(["trust", "release", "validate", "conformance", "--output"])
        .arg(&report_path)
        .arg("--allow-outside-root")
        .env("TRUST_REPO_ROOT", &repo_root)
        .output()
        .expect("run release validate conformance");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "the committed corpus passes its static checks\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("targo trust release validate conformance: NOT EVIDENCE: "),
        "the command must say NOT EVIDENCE before it runs\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("trust-conformance NOT EVIDENCE: "),
        "the runner must name its static cases\nstderr:\n{stderr}"
    );

    let report: Value = serde_json::from_str(
        &std::fs::read_to_string(&report_path).expect("the runner wrote its report"),
    )
    .expect("the report is JSON");
    assert_eq!(report["schema_version"], "trust-conformance-report/v1");
    let results = report["results"].as_array().expect("report results");
    assert!(!results.is_empty(), "the corpus has cases: {report}");
    for result in results {
        // The NOT EVIDENCE label above claims every check is static. When a case
        // gains a check that runs a tool, this flips for it, and the label must
        // be narrowed in the same change.
        assert_eq!(
            result["static_only"],
            Value::Bool(true),
            "every case is static today, so every case must say so: {result}"
        );
    }
}

/// Where `release validate conformance` may read in this checkout. The test
/// above runs it over the real tree, and the runner reads every `path` and
/// `target_path` the manifest names, which is data. The landing gate's audit of
/// this file (scripts/gates/land-escape-audits.toml) declares exactly these
/// prefixes as its reads, so the next test holds that declaration: a manifest
/// that names a path outside them fails here, in the leg that reads it.
const CONFORMANCE_READ_PREFIXES: &[&str] =
    &["trust-conformance/", "crates/trust-vc-bridge/fixtures/trust_ir_adapter/"];

#[test]
fn conformance_manifest_reads_stay_under_the_audited_prefixes() {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("targo-trust sits in the Trust checkout")
        .canonicalize()
        .expect("the checkout resolves");
    let manifest: Value = serde_json::from_str(
        &std::fs::read_to_string(repo_root.join("trust-conformance/manifest.json"))
            .expect("the conformance manifest is committed"),
    )
    .expect("the manifest is JSON");
    let mut named = 0;
    for case in manifest["cases"].as_array().expect("manifest cases") {
        for check in case["checks"].as_array().into_iter().flatten() {
            for field in ["path", "target_path"] {
                let Some(raw) = check.get(field).and_then(Value::as_str) else {
                    continue;
                };
                named += 1;
                // What the runner opens: the path resolved, links followed.
                let opened = repo_root
                    .join(raw)
                    .canonicalize()
                    .unwrap_or_else(|err| panic!("{field} {raw} does not resolve: {err}"));
                assert!(
                    CONFORMANCE_READ_PREFIXES
                        .iter()
                        .any(|prefix| opened.starts_with(repo_root.join(prefix))),
                    "{field} {raw} opens {} outside {CONFORMANCE_READ_PREFIXES:?}: widen the \
                     prefixes and the audit row of tests/release_cli.rs together",
                    opened.display()
                );
            }
        }
    }
    assert!(named > 0, "the manifest names the files its checks read");
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
