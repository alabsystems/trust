use std::collections::BTreeSet;
use std::fs;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde_json::Value;

const HARDENED_CLAIM_IDS: &[&str] = &[
    "path-re-resolution",
    "path-identity",
    "permission-create",
    "permission-change",
    "permission-window",
    "byte-loss",
    "strict-utf8",
    "panic-dos",
    "error-discard",
    "compatibility-oracle",
    "process-signal-semantics",
    "trust-boundary",
    "trust-domain-order",
    "unsafe-operation",
    "ffi-boundary",
];

const HARDENED_CLAIM_CATEGORIES: &[&str] = &[
    "raw_path_api",
    "path_identity",
    "permission_create",
    "permission_change",
    "permission_window",
    "byte_loss",
    "utf8_reject",
    "panic_boundary",
    "error_discard",
    "compat_observable",
    "process_semantics",
    "trust_domain",
    "trust_domain_order",
    "unsafe_operation",
    "ffi_boundary",
];

const STANDALONE_HARDENED_KINDS: &[&str] = &[
    "HardenedRawPathApi",
    "HardenedPathIdentity",
    "HardenedPermissionChange",
    "HardenedPermissionCreate",
    "HardenedPermissionWindow",
    "HardenedByteLoss",
    "HardenedUtf8Boundary",
    "HardenedErrorDiscard",
    "HardenedPanic",
    "HardenedTrustBoundary",
    "HardenedTrustDomainOrder",
    "HardenedCompatibility",
    "HardenedProcessSemantics",
    "HardenedUnsafeOperation",
    "HardenedFfiBoundary",
];

const NATIVE_HARDENED_KINDS: &[&str] = &[
    "hardened_raw_path_api",
    "hardened_path_identity",
    "hardened_permission_change",
    "hardened_permission_create",
    "hardened_permission_window",
    "hardened_utf8_reject",
    "hardened_byte_loss",
    "hardened_error_discard",
    "hardened_panic_boundary",
    "hardened_compat_observable",
    "hardened_process_semantics",
    "hardened_trust_domain",
    "hardened_trust_domain_order",
    "hardened_unsafe_operation",
    "hardened_ffi_boundary",
];

#[test]
fn hardened_lab_json_reports_every_hardened_category_claim() {
    let manifest = workspace_root().join("examples/hardened/Cargo.toml");
    let cargo_target = TempDir::new("trust-hardened-lab-show-vcs-target");
    let targo_root = TempDir::new("trust-hardened-lab-targo");
    let cargo_target_dir = cargo_target.path().join("target");

    let output = hardened_lab_command(targo_root.path())
        .args(["trust", "hardened-lab", "--format", "json", "--show-vcs", "--manifest-path"])
        .arg(&manifest)
        .env("CARGO_TARGET_DIR", &cargo_target_dir)
        .output()
        .expect("run targo trust hardened-lab");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "hardened-lab should succeed for {}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        manifest.display()
    );

    let json: Value = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!("hardened-lab should emit JSON: {error}\nstdout:\n{stdout}\nstderr:\n{stderr}")
    });
    assert_eq!(json["schema_version"], "trust.hardened_lab.v1");
    assert_eq!(json["claims_passed"], true);
    assert_eq!(json["walkthroughs_passed"], true);

    let raw_vcs = json["vcs"]
        .as_array()
        .unwrap_or_else(|| panic!("--show-vcs JSON should contain raw vcs array: {json}"));
    assert_eq!(
        json["summary"]["total_vcs"].as_u64(),
        Some(raw_vcs.len() as u64),
        "summary total_vcs should count raw analyzer VCs\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let hardened_raw_vc_rows: Vec<(&str, &str, &str, &str, &str)> = raw_vcs
        .iter()
        .filter(|vc| vc["outcome"] == "Failed")
        .filter_map(|vc| {
            let kind = vc["kind"].as_str()?;
            kind.starts_with("Hardened").then_some((
                kind,
                vc["function"].as_str()?,
                vc["file"].as_str()?,
                vc["description"].as_str()?,
                vc["outcome"].as_str()?,
            ))
        })
        .collect();
    let hardened_raw_vc_count = hardened_raw_vc_rows.len();
    let hardened_raw_vcs: BTreeSet<(&str, &str, &str, &str, &str)> =
        hardened_raw_vc_rows.into_iter().collect();
    assert_eq!(
        json["summary"]["hardened_vcs"].as_u64(),
        Some(hardened_raw_vc_count as u64),
        "summary hardened_vcs should count failed hardened rows from raw analyzer VCs\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let claims = json["claims"]
        .as_array()
        .unwrap_or_else(|| panic!("hardened-lab JSON should contain claims array: {json}"));
    let claim_ids: BTreeSet<&str> =
        claims.iter().filter_map(|claim| claim["id"].as_str()).collect();
    let expected_claim_ids: BTreeSet<&str> = HARDENED_CLAIM_IDS.iter().copied().collect();
    assert_eq!(
        claim_ids, expected_claim_ids,
        "hardened-lab JSON claim IDs should stay exact\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let missing: Vec<&str> =
        HARDENED_CLAIM_IDS.iter().copied().filter(|claim| !claim_ids.contains(claim)).collect();
    assert!(
        missing.is_empty(),
        "hardened-lab JSON missing claim(s): {missing:?}\nobserved: {claim_ids:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let claim_categories: BTreeSet<&str> =
        claims.iter().filter_map(|claim| claim["category"].as_str()).collect();
    let expected_categories: BTreeSet<&str> = HARDENED_CLAIM_CATEGORIES.iter().copied().collect();
    assert_eq!(
        claim_categories, expected_categories,
        "hardened-lab JSON claim categories should stay exact\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let walkthroughs = json["walkthroughs"].as_array().unwrap_or_else(|| {
        panic!("hardened-lab JSON should contain walkthrough execution records: {json}")
    });
    assert!(
        !walkthroughs.is_empty(),
        "hardened-lab JSON should report discovered walkthrough executions\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let walkthrough_bins: BTreeSet<&str> =
        walkthroughs.iter().filter_map(|walkthrough| walkthrough["bin"].as_str()).collect();

    for claim in claims {
        assert_eq!(claim["passed"], true, "claim should pass: {claim}");
        assert!(
            claim["category"].as_str().is_some_and(|category| !category.is_empty()),
            "claim should include a hardened category tag: {claim}"
        );
        assert!(
            claim["matches"].as_array().is_some_and(|matches| !matches.is_empty()),
            "passing claim should include at least one real analyzer match: {claim}"
        );
        let evidence = claim["walkthrough_evidence"]
            .as_array()
            .unwrap_or_else(|| panic!("claim should include walkthrough_evidence array: {claim}"));
        assert!(
            !evidence.is_empty(),
            "passing claim should include claim-specific runnable walkthrough evidence: {claim}"
        );
        for entry in evidence {
            assert_eq!(entry["passed"], true, "claim walkthrough evidence should pass: {entry}");
            let bin = entry["bin"]
                .as_str()
                .unwrap_or_else(|| panic!("claim walkthrough evidence should name bin: {entry}"));
            assert!(
                walkthrough_bins.contains(bin),
                "claim evidence should reference executed walkthrough bin `{bin}`\nclaim: {claim}\nwalkthroughs: {walkthrough_bins:?}"
            );
            let requirements = entry["requirements"].as_array().unwrap_or_else(|| {
                panic!("claim walkthrough evidence should list transcript requirements: {entry}")
            });
            assert!(
                !requirements.is_empty(),
                "claim walkthrough evidence should include concrete key=value requirements: {entry}"
            );
            for requirement in requirements {
                assert_eq!(
                    requirement["found"], true,
                    "claim walkthrough transcript requirement should be found: {requirement}"
                );
                assert!(
                    requirement["key"].as_str().is_some_and(|key| !key.is_empty())
                        && requirement["value"].as_str().is_some_and(|value| !value.is_empty()),
                    "claim walkthrough transcript requirement should name key and value: {requirement}"
                );
            }
        }
        let source_example = claim["source_example"]
            .as_str()
            .unwrap_or_else(|| panic!("claim should record a source_example: {claim}"));
        for analyzer_match in claim["matches"]
            .as_array()
            .unwrap_or_else(|| panic!("claim should include matches array: {claim}"))
        {
            assert_eq!(
                analyzer_match["function"].as_str(),
                Some(source_example),
                "claim matches must bind to the advertised fixture function: {claim}"
            );
            let raw_key = (
                claim["kind"]
                    .as_str()
                    .unwrap_or_else(|| panic!("claim should record VC kind: {claim}")),
                analyzer_match["function"]
                    .as_str()
                    .unwrap_or_else(|| panic!("claim match should record function: {claim}")),
                analyzer_match["file"]
                    .as_str()
                    .unwrap_or_else(|| panic!("claim match should record source file: {claim}")),
                analyzer_match["description"]
                    .as_str()
                    .unwrap_or_else(|| panic!("claim match should record description: {claim}")),
                "Failed",
            );
            assert!(
                hardened_raw_vcs.contains(&raw_key),
                "claim match should be backed by a failed raw analyzer VC with the same kind/function/file/description/outcome\nclaim: {claim}\nraw_vcs: {raw_vcs:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
            );
        }
    }

    assert!(
        walkthrough_bins.contains("path_identity_toctou"),
        "hardened-lab should execute the path identity walkthrough\nobserved: {walkthrough_bins:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        walkthrough_bins.contains("byte_utf8_walkthrough"),
        "hardened-lab should execute the byte/UTF-8 walkthrough\nobserved: {walkthrough_bins:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    if workspace_root().join("examples/hardened/src/bin/additional_walkthroughs.rs").is_file() {
        assert!(
            walkthrough_bins.contains("additional_walkthroughs"),
            "hardened-lab should execute the additional rootless walkthroughs when present\nobserved: {walkthrough_bins:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }
    assert_eq!(
        json["summary"]["walkthroughs_total"].as_u64(),
        Some(walkthroughs.len() as u64),
        "summary should count walkthrough execution records\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        json["summary"]["walkthroughs_passed"].as_u64(),
        Some(walkthroughs.len() as u64),
        "summary should count passing walkthrough execution records\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        json["summary"]["walkthroughs_failed"].as_u64(),
        Some(0),
        "summary should report no failed walkthrough execution records\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    for walkthrough in walkthroughs {
        let bin = walkthrough["bin"]
            .as_str()
            .unwrap_or_else(|| panic!("walkthrough record should name the bin: {walkthrough}"));
        assert_eq!(walkthrough["success"], true, "walkthrough should pass: {walkthrough}");
        assert_eq!(
            walkthrough["status_code"].as_i64(),
            Some(0),
            "walkthrough should exit zero: {walkthrough}"
        );
        assert_eq!(
            walkthrough["process_success"], true,
            "walkthrough process should succeed for {bin}: {walkthrough}"
        );
        assert_eq!(
            walkthrough["transcript_passed"], true,
            "walkthrough transcript should pass for {bin}: {walkthrough}"
        );
        assert!(
            walkthrough
                .get("transcript_errors")
                .and_then(Value::as_array)
                .map_or(true, |errors| errors.is_empty()),
            "walkthrough transcript should not include validation errors for {bin}: {walkthrough}"
        );
        assert!(
            walkthrough["source"].as_str().is_some_and(|source| source
                .replace('\\', "/")
                .contains("examples/hardened/src/bin/")),
            "walkthrough record should include the source bin path: {walkthrough}"
        );
        assert!(
            // `targo` (post tcargo->targo rename, d1ee06b315) — the old
            // `contains("cargo")` only matched the tcargo-era binary name.
            walkthrough["command"].as_str().is_some_and(|command| command.contains("targo")
                && command.contains("build")
                && command.contains("--bin")),
            "walkthrough record should include the Trust Cargo build command: {walkthrough}"
        );
        assert!(
            walkthrough["stdout"]
                .as_str()
                .is_some_and(|walkthrough_stdout| walkthrough_stdout.contains("walkthrough=")),
            "walkthrough record should capture stdout for {bin}: {walkthrough}"
        );
        assert!(
            walkthrough["stderr"].as_str().is_some(),
            "walkthrough record should capture stderr for {bin}: {walkthrough}"
        );
    }
}

#[test]
fn hardened_lab_json_fails_closed_when_tracked_walkthrough_bin_is_missing() {
    let source = workspace_root().join("examples/hardened");
    let temp = TempDir::new("trust-hardened-lab-missing-walkthrough");
    let targo_root = TempDir::new("trust-hardened-lab-missing-targo");
    let fixture = temp.path().join("hardened");
    copy_dir_all(&source, &fixture).unwrap_or_else(|error| {
        panic!("copy hardened fixture {} to {}: {error}", source.display(), fixture.display())
    });

    let missing_bin = fixture.join("src/bin/byte_utf8_walkthrough.rs");
    fs::remove_file(&missing_bin)
        .unwrap_or_else(|error| panic!("remove {}: {error}", missing_bin.display()));
    let manifest = fixture.join("Cargo.toml");
    let cargo_target_dir = temp.path().join("target");

    let output = hardened_lab_command(targo_root.path())
        .args(["trust", "hardened-lab", "--format", "json", "--manifest-path"])
        .arg(&manifest)
        .env("CARGO_TARGET_DIR", &cargo_target_dir)
        .output()
        .expect("run targo trust hardened-lab with missing walkthrough bin");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "hardened-lab should fail closed when a tracked walkthrough bin is missing\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let json: Value = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!("hardened-lab should emit JSON for missing tracked walkthrough: {error}\nstdout:\n{stdout}\nstderr:\n{stderr}")
    });
    assert_eq!(json["schema_version"], "trust.hardened_lab.v1");
    assert_eq!(json["claims_passed"], false);
    assert_eq!(json["walkthroughs_passed"], false);
    assert_eq!(
        json["summary"]["walkthroughs_failed"].as_u64(),
        Some(1),
        "summary should count the missing tracked walkthrough as failed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let walkthroughs = json["walkthroughs"]
        .as_array()
        .unwrap_or_else(|| panic!("hardened-lab JSON should contain walkthrough records: {json}"));
    let missing = walkthroughs
        .iter()
        .find(|walkthrough| walkthrough["bin"] == "byte_utf8_walkthrough")
        .unwrap_or_else(|| {
            panic!(
                "hardened-lab should report the removed tracked walkthrough bin\nwalkthroughs: {walkthroughs:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
            )
        });
    assert_eq!(missing["success"], false);
    assert_eq!(missing["process_success"], false);
    assert_eq!(missing["transcript_passed"], false);
    assert_eq!(missing["status"], "missing tracked walkthrough bin");
    assert!(missing["status_code"].is_null(), "missing bin should have no status code: {missing}");
    assert_eq!(missing["command"], "");
    assert_eq!(missing["stdout"], "");
    assert_eq!(missing["stderr"], "");
    assert!(
        missing["source"].as_str().is_some_and(|source| source
            .replace('\\', "/")
            .ends_with("src/bin/byte_utf8_walkthrough.rs")),
        "missing walkthrough should report the expected source path: {missing}"
    );
    assert!(
        missing["transcript_errors"]
            .as_array()
            .is_some_and(|errors| errors.iter().any(|error| error.as_str()
                == Some("required walkthrough bin `byte_utf8_walkthrough` is missing"))),
        "missing walkthrough should explain the fail-closed error: {missing}"
    );

    let claims = json["claims"]
        .as_array()
        .unwrap_or_else(|| panic!("hardened-lab JSON should contain claim records: {json}"));
    for claim_id in ["byte-loss", "strict-utf8"] {
        let claim = claims
            .iter()
            .find(|claim| claim["id"] == claim_id)
            .unwrap_or_else(|| panic!("missing claim `{claim_id}` in {claims:?}"));
        assert_eq!(claim["passed"], false, "claim should fail without byte walkthrough: {claim}");
        assert!(
            claim["walkthrough_evidence"].as_array().is_some_and(|evidence| evidence.iter().any(
                |entry| entry["bin"] == "byte_utf8_walkthrough"
                    && entry["passed"] == false
                    && entry["failure_message"]
                        .as_str()
                        .is_some_and(|message| message.contains("did not pass"))
            )),
            "claim should identify missing byte walkthrough evidence: {claim}"
        );
    }
}

#[test]
fn standalone_hardened_check_json_exits_one_with_real_findings() {
    let fixture_dir = workspace_root().join("examples/hardened");

    let output = Command::new(targo_trust_binary())
        .args(["trust", "check", "--standalone", "--format", "json"])
        .current_dir(&fixture_dir)
        .output()
        .expect("run targo trust check --standalone");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "standalone hardened check should fail closed with findings\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("hardened profile `unix_hardened` enabled"),
        "standalone check should enable the default hardened profile without an explicit flag\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let json: Value = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!("standalone hardened check should emit JSON: {error}\nstdout:\n{stdout}\nstderr:\n{stderr}")
    });
    assert_source_audit_envelope(&json);
    assert!(
        json["failed"].as_u64().is_some_and(|failed| failed > 0),
        "standalone hardened JSON should report failed findings\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let vcs = json["audit_rows"]
        .as_array()
        .unwrap_or_else(|| panic!("standalone hardened JSON should contain audit rows: {json}"));
    let hardened_findings: Vec<&Value> =
        vcs.iter().filter(|vc| is_failed_hardened_finding(vc)).collect();
    assert!(
        !hardened_findings.is_empty(),
        "standalone hardened check should emit failed hardened VC findings\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    for finding in hardened_findings {
        assert!(
            finding["function"].as_str().is_some_and(|value| !value.is_empty()),
            "hardened finding should name the function: {finding}"
        );
        assert!(
            finding["description"].as_str().is_some_and(|value| !value.is_empty()),
            "hardened finding should include a diagnostic description: {finding}"
        );
        assert!(
            finding.get("help").is_none(),
            "source-audit JSON schema must not grow terminal-only help fields: {finding}"
        );
    }

    let kinds: BTreeSet<&str> = vcs
        .iter()
        .filter_map(|vc| vc["kind"].as_str())
        .filter(|kind| kind.starts_with("Hardened"))
        .collect();
    let expected_kinds: BTreeSet<&str> = STANDALONE_HARDENED_KINDS.iter().copied().collect();
    assert_eq!(
        kinds, expected_kinds,
        "standalone hardened JSON kind set should stay exact\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let missing: Vec<&str> =
        STANDALONE_HARDENED_KINDS.iter().copied().filter(|kind| !kinds.contains(kind)).collect();
    assert!(
        missing.is_empty(),
        "standalone hardened JSON missing kind(s): {missing:?}\nobserved: {kinds:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[test]
fn standalone_check_no_hardened_opts_out_of_default_profile() {
    let fixture_dir = workspace_root().join("examples/hardened");

    let output = Command::new(targo_trust_binary())
        .args(["trust", "check", "--standalone", "--no-hardened", "--format", "json"])
        .env_remove("TRUST_HARDENED")
        .env_remove("TRUST_PROFILE")
        .current_dir(&fixture_dir)
        .output()
        .expect("run targo trust check --standalone --no-hardened");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "--no-hardened opts out of hardened findings, but baseline unknown obligations still fail closed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("hardened profile"),
        "--no-hardened should not enable or announce a hardened profile\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let json: Value = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!("standalone no-hardened check should emit JSON: {error}\nstdout:\n{stdout}\nstderr:\n{stderr}")
    });
    assert_source_audit_envelope(&json);
    assert_eq!(
        json["failed"].as_u64(),
        Some(0),
        "--no-hardened should leave only non-failing baseline standalone obligations\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        json["unknown"].as_u64().is_some_and(|unknown| unknown > 0),
        "baseline standalone unknown obligations must be reported and fail closed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let vcs = json["audit_rows"]
        .as_array()
        .unwrap_or_else(|| panic!("standalone no-hardened JSON should contain audit rows: {json}"));
    assert!(
        vcs.iter().any(|vc| vc["kind"] == "UnspecifiedPublicApi"),
        "--no-hardened should still run the baseline standalone analyzer\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let hardened_kinds: BTreeSet<&str> = vcs
        .iter()
        .filter_map(|vc| vc["kind"].as_str())
        .filter(|kind| kind.starts_with("Hardened"))
        .collect();
    assert!(
        hardened_kinds.is_empty(),
        "--no-hardened should suppress hardened obligations\nobserved: {hardened_kinds:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[test]
fn standalone_check_fails_closed_with_zero_obligations() {
    let temp = TempDir::new("trust-standalone-zero-vcs");
    let src_dir = temp.path().join("src");
    fs::create_dir(&src_dir)
        .unwrap_or_else(|error| panic!("create fixture src dir {}: {error}", src_dir.display()));
    fs::write(
        temp.path().join("Cargo.toml"),
        "[package]\nname = \"zero-vcs\"\nversion = \"0.0.0\"\nedition = \"2021\"\n",
    )
    .expect("write zero-vcs manifest");
    fs::write(src_dir.join("lib.rs"), "fn private_helper() -> usize { 1 }\n")
        .expect("write zero-vcs source");

    let output = Command::new(targo_trust_binary())
        .args(["trust", "check", "--standalone", "--no-hardened", "--format", "json"])
        .current_dir(temp.path())
        .output()
        .expect("run targo trust check --standalone on zero-vcs fixture");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "standalone mode must fail closed when no obligations are generated\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let json: Value = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!("standalone zero-vcs check should emit JSON: {error}\nstdout:\n{stdout}\nstderr:\n{stderr}")
    });
    assert_source_audit_envelope(&json);
    assert_eq!(json["total_audit_rows"].as_u64(), Some(0));
}

#[test]
fn standalone_hardened_check_terminal_prints_category_help() {
    let fixture_dir = workspace_root().join("examples/hardened");

    let output = Command::new(targo_trust_binary())
        .args(["trust", "check", "--standalone", "--hardened", "--format", "terminal"])
        .current_dir(&fixture_dir)
        .output()
        .expect("run targo trust check --standalone --hardened --format terminal");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "standalone hardened terminal check should fail closed with findings\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.trim().is_empty(),
        "terminal format should keep the standalone report on stderr\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    for (category, help) in [
        (
            "hardened:path",
            "help: use a verified dirfd/handle-relative wrapper and carry identity evidence",
        ),
        (
            "hardened:utf8",
            "help: accept bytes/OsStr at Unix boundaries or prove UTF-8 before conversion",
        ),
        (
            "hardened:error",
            "help: propagate the Result or record an explicit checked-discard policy",
        ),
        (
            "hardened:ffi",
            "help: state ABI, ownership, lifetime, and trust assumptions for the extern boundary",
        ),
    ] {
        assert!(
            stderr.contains(category) && stderr.contains(help),
            "standalone hardened terminal output should include actionable help for {category}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }
}

#[test]
fn native_hardened_check_json_uses_default_compiler_workflow_when_available() {
    assert_native_hardened_json_uses_default_compiler_workflow_when_available(
        "check",
        &[],
        "unix_hardened",
    );
}

#[test]
fn native_hardened_report_json_uses_default_compiler_workflow_when_available() {
    assert_native_hardened_json_uses_default_compiler_workflow_when_available(
        "report",
        &[],
        "unix_hardened",
    );
}

#[test]
fn native_hardened_check_json_honors_explicit_trust_profile_when_available() {
    assert_native_hardened_json_uses_default_compiler_workflow_when_available(
        "check",
        &["--trust-profile", "coreutils_hardened"],
        "coreutils_hardened",
    );
}

fn assert_native_hardened_json_uses_default_compiler_workflow_when_available(
    subcommand: &str,
    profile_args: &[&str],
    expected_profile: &str,
) {
    let manifest = workspace_root().join("examples/hardened/Cargo.toml");

    let mut command = Command::new(targo_trust_binary());
    command.args(["trust", subcommand]).args(profile_args).args([
        "--format",
        "json",
        "--manifest-path",
    ]);
    command.arg(&manifest);
    let output = command.output().unwrap_or_else(|error| {
        panic!(
            "run targo trust {subcommand} {profile_args:?} with native compiler workflow: {error}"
        )
    });

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_stdout_does_not_report_source_audit(&stdout, &stderr);

    if assert_missing_native_trustc_setup_error(&output, &stdout, &stderr) {
        return;
    }

    assert!(
        matches!(output.status.code(), Some(0) | Some(1)),
        "native hardened {subcommand} should either pass or fail with verification findings, not a setup/internal error\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let json: Value = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!("native hardened {subcommand} should emit canonical JSON: {error}\nstdout:\n{stdout}\nstderr:\n{stderr}")
    });
    assert!(
        !matches!(json["mode"].as_str(), Some("source-audit" | "standalone")),
        "native hardened {subcommand} must not emit a non-proof source-audit report\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        json["metadata"]["schema_version"].as_str(),
        Some("trust.report.v1"),
        "native hardened {subcommand} should emit canonical trust-report schema version\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        json["functions"].as_array().is_some(),
        "native hardened {subcommand} should emit canonical trust-report JSON, not standalone JSON\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let kinds = obligation_kind_set(&json);
    let standalone_style: Vec<&str> =
        kinds.iter().copied().filter(|kind| kind.starts_with("Hardened")).collect();
    assert!(
        standalone_style.is_empty(),
        "native hardened report should use canonical hardened_ kind tags, not standalone enum names: {standalone_style:?}\nobserved: {kinds:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let hardened_kinds: BTreeSet<&str> =
        kinds.iter().copied().filter(|kind| kind.starts_with("hardened_")).collect();
    assert!(
        !hardened_kinds.is_empty(),
        "native hardened {subcommand} should emit hardened_ obligations when native trustc is available\nobserved: {kinds:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let missing: Vec<&str> = NATIVE_HARDENED_KINDS
        .iter()
        .copied()
        .filter(|kind| !hardened_kinds.contains(kind))
        .collect();
    assert!(
        missing.is_empty(),
        "native hardened JSON missing hardened kind(s): {missing:?}\nobserved hardened kinds: {hardened_kinds:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_native_hardened_context(&json, subcommand, expected_profile, &stdout, &stderr);
}

fn assert_native_hardened_context(
    json: &Value,
    subcommand: &str,
    expected_profile: &str,
    stdout: &str,
    stderr: &str,
) {
    let hardened = json
        .get("hardened")
        .and_then(Value::as_object)
        .unwrap_or_else(|| {
            panic!(
                "native hardened {subcommand} JSON should include hardened context\njson:\n{json}\nstdout:\n{stdout}\nstderr:\n{stderr}"
            )
        });
    let profile = hardened
        .get("profile")
        .and_then(Value::as_object)
        .unwrap_or_else(|| {
            panic!(
                "native hardened {subcommand} JSON should include hardened.profile\nhardened:\n{}\nstdout:\n{stdout}\nstderr:\n{stderr}",
                Value::Object(hardened.clone())
            )
        });
    assert_eq!(
        profile.get("name").and_then(Value::as_str),
        Some(expected_profile),
        "native hardened {subcommand} JSON should carry the selected trust profile\nprofile:\n{}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        Value::Object(profile.clone())
    );

    let enabled_categories: BTreeSet<&str> = profile
        .get("enabled_categories")
        .and_then(Value::as_array)
        .unwrap_or_else(|| {
            panic!(
                "native hardened {subcommand} JSON should include profile.enabled_categories\nprofile:\n{}\nstdout:\n{stdout}\nstderr:\n{stderr}",
                Value::Object(profile.clone())
            )
        })
        .iter()
        .filter_map(Value::as_str)
        .collect();
    let expected_categories: BTreeSet<&str> = NATIVE_HARDENED_KINDS
        .iter()
        .copied()
        .map(|kind| kind.strip_prefix("hardened_").unwrap_or(kind))
        .collect();
    let missing_categories: Vec<&str> = expected_categories
        .iter()
        .copied()
        .filter(|category| !enabled_categories.contains(category))
        .collect();
    assert!(
        missing_categories.is_empty(),
        "native hardened {subcommand} JSON missing hardened profile category/categories: {missing_categories:?}\nobserved: {enabled_categories:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let summary = hardened
        .get("summary")
        .and_then(Value::as_object)
        .unwrap_or_else(|| {
            panic!(
                "native hardened {subcommand} JSON should include hardened.summary\nhardened:\n{}\nstdout:\n{stdout}\nstderr:\n{stderr}",
                Value::Object(hardened.clone())
            )
        });
    let hardened_obligations =
        summary.get("hardened_obligations").and_then(Value::as_u64).unwrap_or(0);
    let proved_hardened_obligations =
        summary.get("proved_hardened_obligations").and_then(Value::as_u64).unwrap_or(0);
    let proof_evidence_entries =
        summary.get("proof_evidence_entries").and_then(Value::as_u64).unwrap_or(0);
    assert!(
        hardened_obligations >= NATIVE_HARDENED_KINDS.len() as u64,
        "native hardened {subcommand} JSON should count hardened obligations\nsummary:\n{}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        Value::Object(summary.clone())
    );
    assert_eq!(
        proved_hardened_obligations,
        proof_evidence_entries,
        "native hardened {subcommand} JSON should count proved hardened obligations only when proof evidence is present\nsummary:\n{}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        Value::Object(summary.clone())
    );
    let assurance = hardened
        .get("assurance")
        .and_then(Value::as_object)
        .unwrap_or_else(|| {
            panic!(
                "native hardened {subcommand} JSON should include hardened.assurance\nhardened:\n{}\nstdout:\n{stdout}\nstderr:\n{stderr}",
                Value::Object(hardened.clone())
            )
        });
    let expected_level = if proof_evidence_entries == 0 {
        "inventory_only"
    } else if proof_evidence_entries == hardened_obligations {
        "proof_backed"
    } else {
        "partial_proof_evidence"
    };
    assert_eq!(
        assurance.get("level").and_then(Value::as_str),
        Some(expected_level),
        "native hardened {subcommand} JSON should derive assurance from publishable proof evidence coverage\nassurance:\n{}\nsummary:\n{}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        Value::Object(assurance.clone()),
        Value::Object(summary.clone())
    );

    let inventory = hardened
        .get("boundary_inventory")
        .and_then(Value::as_array)
        .unwrap_or_else(|| {
            panic!(
                "native hardened {subcommand} JSON should include hardened.boundary_inventory\nhardened:\n{}\nstdout:\n{stdout}\nstderr:\n{stderr}",
                Value::Object(hardened.clone())
            )
        });
    assert!(
        !inventory.is_empty(),
        "native hardened {subcommand} JSON should include hardened inventory entries\nhardened:\n{}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        Value::Object(hardened.clone())
    );
}

fn is_failed_hardened_finding(value: &Value) -> bool {
    value["outcome"] == "Failed"
        && value
            .get("kind")
            .and_then(Value::as_str)
            .is_some_and(|kind| kind.starts_with("Hardened"))
}

fn assert_source_audit_envelope(json: &Value) {
    assert_eq!(json["schema_version"], "trust.source-audit.v1");
    assert_eq!(json["mode"], "source-audit");
    assert_eq!(json["proof_authority"], "none");
    assert_eq!(json["compiler_verification_performed"], false);
    assert!(
        json.get("proved").is_none(),
        "non-proof source audit must not expose a proof verdict: {json}"
    );
}

fn assert_stdout_does_not_report_source_audit(stdout: &str, stderr: &str) {
    if stdout.trim().is_empty() {
        return;
    }

    if let Ok(json) = serde_json::from_str::<Value>(stdout) {
        assert!(
            !matches!(json["mode"].as_str(), Some("source-audit" | "standalone")),
            "native/default hardened check must not fall back to non-proof source-audit mode\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        return;
    }

    assert!(
        !stdout.contains(r#""mode":"source-audit""#)
            && !stdout.contains(r#""mode": "source-audit""#)
            && !stdout.contains(r#""mode":"standalone""#)
            && !stdout.contains(r#""mode": "standalone""#),
        "native/default hardened check must not report non-proof source-audit mode\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

fn assert_missing_native_trustc_setup_error(output: &Output, stdout: &str, stderr: &str) -> bool {
    let setup_error = output.status.code() == Some(2)
        && (stderr.contains("Trust compiler not found")
            || stderr.contains("discovered compiler does not support Trust verification"));
    if !setup_error {
        return false;
    }

    assert!(
        stdout.trim().is_empty(),
        "missing or misconfigured native trustc should fail before emitting a JSON report\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("trustc"),
        "native compiler setup error should explicitly identify trustc discovery/setup\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    true
}

fn obligation_kind_set(json: &Value) -> BTreeSet<&str> {
    let functions = json["functions"]
        .as_array()
        .unwrap_or_else(|| panic!("canonical JSON should contain functions array: {json}"));
    functions
        .iter()
        .flat_map(|function| {
            function["obligations"]
                .as_array()
                .unwrap_or_else(|| panic!("function should contain obligations array: {function}"))
        })
        .filter_map(|obligation| obligation["kind"].as_str())
        .collect()
}

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(prefix: &str) -> Self {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system time should be after Unix epoch")
            .as_nanos();
        let path = std::env::temp_dir().join(format!("{prefix}-{}-{nanos}", std::process::id()));
        fs::create_dir(&path)
            .unwrap_or_else(|error| panic!("create temp dir {}: {error}", path.display()));
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn copy_dir_all(source: &Path, destination: &Path) -> std::io::Result<()> {
    fs::create_dir_all(destination)?;
    for entry in fs::read_dir(source)? {
        let entry = entry?;
        let file_type = entry.file_type()?;
        let source_path = entry.path();
        let destination_path = destination.join(entry.file_name());
        if file_type.is_dir() {
            copy_dir_all(&source_path, &destination_path)?;
        } else if file_type.is_file() {
            fs::copy(&source_path, &destination_path)?;
        }
    }
    Ok(())
}

fn hardened_lab_command(targo_root: &Path) -> Command {
    let targo = install_test_targo(targo_root);
    let mut command = Command::new(targo_trust_binary());
    command.env("TARGO", targo);
    command
        .env("TRUST_TEST_HOST_CARGO", std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()));
    command
}

fn install_test_targo(targo_root: &Path) -> PathBuf {
    let path = targo_root.join(format!("targo{}", std::env::consts::EXE_SUFFIX));
    #[cfg(unix)]
    {
        fs::write(&path, "#!/bin/sh\nexec \"$TRUST_TEST_HOST_CARGO\" \"$@\"\n")
            .unwrap_or_else(|error| panic!("write test targo {}: {error}", path.display()));
        let mut permissions = fs::metadata(&path).expect("test targo metadata").permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&path, permissions).expect("chmod test targo");
    }
    #[cfg(not(unix))]
    {
        let host_cargo = PathBuf::from(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()));
        fs::copy(&host_cargo, &path).unwrap_or_else(|error| {
            panic!("copy host cargo {:?} to test targo {}: {error}", host_cargo, path.display())
        });
    }
    path
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

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .expect("workspace root should be canonicalizable")
}
