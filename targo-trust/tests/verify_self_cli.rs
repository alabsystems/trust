use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;
use sha2::{Digest as _, Sha256};
use trust_types::{
    NATIVE_TRUST_IR_MATERIALIZATION_SCHEMA, ProofEvidence, ProofStrength,
    TRANSPORT_ARTIFACT_STORE_DIRECTORY, TransportArtifactDigest, TransportArtifactMaterialization,
    TransportArtifactReference, TransportEvidenceArtifact, TransportNativeTrustIrEvidence,
    TransportProofEvidence, TransportProofStatus,
};

const FIXTURE_TIMEOUT_SEC: &str = "10";
const FIXTURE_VERSION_COMMIT: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const FIXTURE_VERSION_HOST: &str = "test-host";
const FIXTURE_VERSION_RELEASE: &str = "1.99.0-test";

#[test]
fn verify_self_help_lists_rust_routed_command() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "verify", "--help"])
        .output()
        .expect("run verify help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "verify help should succeed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("targo trust verify <command>"));
    assert!(stdout.contains("Rust-native Trust self-verification harness"));
}

#[test]
fn verify_self_help_keeps_python_bootstrap_runner_internal() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "verify", "self", "--help"])
        .output()
        .expect("run verify self help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "verify self help should succeed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("targo trust verify self --full-verifier"));
    assert!(stdout.contains("still executes"));
    assert!(stdout.contains("Targo/trustc/trustdoc version probes"));
    assert!(stdout.contains("trustd"));
    assert!(stdout.contains("PING/IDENTITY/STATUS"));
    assert!(
        !stdout.contains("x.py") && !stdout.to_ascii_lowercase().contains("python"),
        "verify self help must not expose Python/bootstrap runner names\nstdout:\n{stdout}"
    );
}

#[test]
fn verify_self_legacy_aliases_are_rejected() {
    for alias in ["self-harness", "self-verify", "self-verify-harness"] {
        let output = Command::new(targo_trust_binary())
            .args(["trust", "verify", alias])
            .output()
            .expect("run legacy verify alias");

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(2),
            "legacy alias {alias} should be rejected\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        let expected = format!("unknown command `{alias}`");
        assert!(stderr.contains(&expected), "{stderr}");
    }
}

#[test]
fn verify_self_full_verifier_rejects_every_custom_stage_dispatch() {
    let cases: &[(&str, &[&str])] = &[
        (
            "external-subcommand",
            &["trust-external-proof", "--manifest-path", "/tmp/untrusted/Cargo.toml"],
        ),
        ("doc-subcommand", &["doc", "--manifest-path", "compiler/rustc_middle/Cargo.toml"]),
        ("cargo-alias", &["untrusted-proof-alias"]),
        (
            "config-override",
            &[
                "--config",
                "build.rustc=\"/tmp/untrusted-rustc\"",
                "build",
                "--manifest-path",
                "compiler/rustc_middle/Cargo.toml",
            ],
        ),
    ];

    for (case, stage_args) in cases {
        let fixture = Fixture::new(&format!("targo-trust-verify-self-custom-stage-{case}"));
        let stage2_targo = fixture.install_stage2_targo();
        let execution_marker = fixture.temp.path().join("forbidden-stage-executed");
        let output = Command::new(targo_trust_binary())
            .args([
                "trust",
                "verify",
                "self",
                "--repo-root",
                fixture.repo_str(),
                "--report-dir",
                fixture.report_str(),
                "--full-verifier",
                "--stage-command",
            ])
            .arg(&stage2_targo)
            .args(*stage_args)
            .env("SELF_VERIFY_EXECUTION_MARKER", &execution_marker)
            .output()
            .expect("run full verifier with forbidden custom stage dispatch");

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(2),
            "{case} should be rejected before planning\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stderr.contains("--full-verifier does not permit --stage-command"),
            "{case} stderr should identify the closed dispatch policy\nstderr:\n{stderr}"
        );
        assert!(
            stderr.contains("exclusively executes the fixed repository stage2 Targo build command"),
            "{case} stderr should identify the only permitted dispatch\nstderr:\n{stderr}"
        );
        assert!(
            !fixture.report_dir.join("self-verify-harness.report.json").exists(),
            "{case} must not leave a self-verification report"
        );
        assert!(!execution_marker.exists(), "{case} executed the forbidden stage process");
    }
}

#[test]
fn verify_self_full_verifier_default_stage_is_rust_native() {
    let fixture = Fixture::new("targo-trust-verify-self-native-default");
    let stage2_targo = fixture.install_stage2_targo();
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "self",
            "--repo-root",
            fixture.repo_str(),
            "--report-dir",
            fixture.report_str(),
            "--full-verifier",
            "--dry-run",
        ])
        .output()
        .expect("run verify self dry run");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "dry-run full verifier should plan successfully\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let report = fixture.report();
    let argv = report["stages"][0]["command"]["argv"]
        .as_array()
        .expect("stage argv")
        .iter()
        .map(|value| value.as_str().expect("argv string"))
        .collect::<Vec<_>>();
    assert_eq!(
        argv.first().copied(),
        Some(stage2_targo.to_str().expect("stage2 path should be utf-8")),
        "default full-verifier argv must use repo-local stage2 Targo: {argv:?}"
    );
    assert!(
        argv.iter().any(|arg| *arg == "build"),
        "argv should invoke Targo's Cargo-compatible build command: {argv:?}"
    );
    assert!(
        argv.iter().any(|arg| *arg == "--message-format=json"),
        "argv should request canonical Cargo JSON evidence: {argv:?}"
    );
    assert!(
        argv.iter().all(|arg| *arg != "--message-format=json-render-diagnostics"),
        "proof transport must remain inside Cargo compiler-message envelopes: {argv:?}"
    );
    assert!(
        argv.windows(2)
            .any(|window| window == ["--manifest-path", "compiler/rustc_middle/Cargo.toml"]),
        "argv should target the compiler crate manifest: {argv:?}"
    );
    assert!(
        argv.iter().all(|arg| {
            let lower = arg.to_ascii_lowercase();
            !lower.contains("x.py") && !lower.contains("python")
        }),
        "implicit full-verifier default must not use Python/bootstrap runners: {argv:?}"
    );
    let flags = report["stages"][0]["env_policy"]["verification_flags"]
        .as_array()
        .expect("verification flags");
    assert!(
        !flags.iter().any(|flag| flag == "-Z trust-verify"),
        "full verifier mode activates verification without the advisory flag: {flags:?}"
    );
    assert!(
        !flags.iter().any(|flag| flag == "-Z trust-verify-full"),
        "`-Z trust-verify-full` was deleted; self verification is strict by default and must NOT pass it: {flags:?}"
    );
    let stage2_tool = report["toolchain"]["tools"]
        .as_array()
        .expect("toolchain tools")
        .iter()
        .find(|tool| tool["tool"] == "targo")
        .expect("targo toolchain entry");
    assert_eq!(stage2_tool["path"], format!("build/host/stage2/bin/{}", stage2_file_name("targo")));
    assert_eq!(stage2_tool["available"], true);
    assert_eq!(stage2_tool["regular_file"], true);
    assert_eq!(stage2_tool["executable"], true);
    assert_eq!(stage2_tool["symlink"], false);
    assert_eq!(stage2_tool["identity_matches_expected"], true);
    assert_eq!(stage2_tool["sha256"].as_str().expect("stage2 Targo SHA-256").len(), 64);
    let trustc_tool = report["toolchain"]["tools"]
        .as_array()
        .expect("toolchain tools")
        .iter()
        .find(|tool| tool["tool"] == "trustc")
        .expect("trustc toolchain entry");
    assert_eq!(
        trustc_tool["path"],
        format!("build/host/stage2/bin/{}", stage2_file_name("trustc"))
    );
    assert_eq!(trustc_tool["identity_matches_expected"], true);
    let trustdoc_tool = report["toolchain"]["tools"]
        .as_array()
        .expect("toolchain tools")
        .iter()
        .find(|tool| tool["tool"] == "trustdoc")
        .expect("trustdoc toolchain entry");
    assert_eq!(
        trustdoc_tool["path"],
        format!("build/host/stage2/bin/{}", stage2_file_name("trustdoc"))
    );
    assert_eq!(trustdoc_tool["available"], true);
    assert_eq!(trustdoc_tool["regular_file"], true);
    assert_eq!(trustdoc_tool["executable"], true);
    assert_eq!(trustdoc_tool["symlink"], false);
    assert_eq!(trustdoc_tool["identity_matches_expected"], true);
    assert_eq!(trustdoc_tool["sha256"].as_str().expect("stage2 trustdoc SHA-256").len(), 64);
    let trustd_tool = report["toolchain"]["tools"]
        .as_array()
        .expect("toolchain tools")
        .iter()
        .find(|tool| tool["tool"] == "trustd")
        .expect("trustd toolchain entry");
    assert_eq!(
        trustd_tool["path"],
        format!("build/host/stage2/bin/{}", stage2_file_name("trustd"))
    );
    assert_eq!(trustd_tool["available"], true);
    assert_eq!(trustd_tool["regular_file"], true);
    assert_eq!(trustd_tool["executable"], true);
    assert_eq!(trustd_tool["symlink"], false);
    assert_eq!(trustd_tool["identity_matches_expected"], true);
    assert_eq!(trustd_tool["sha256"].as_str().expect("stage2 trustd SHA-256").len(), 64);
    let stage2_identity = &report["stages"][0]["stage2_toolchain_identity"];
    assert_eq!(
        stage2_identity["trustdoc"]["path"],
        stage2_targo.with_file_name(stage2_file_name("trustdoc")).display().to_string()
    );
    assert_eq!(stage2_identity["trustdoc"]["size_bytes"].as_u64().unwrap_or(0) > 0, true);
    assert_eq!(stage2_identity["trustdoc"]["sha256"], trustdoc_tool["sha256"]);
    assert_eq!(stage2_identity["trustdoc_commit"], stage2_identity["trustc_commit"]);
    assert_eq!(stage2_identity["trustd_commit"], stage2_identity["trustc_commit"]);
    assert_eq!(stage2_identity["targo_commit"], stage2_identity["trustc_commit"]);
    assert_eq!(stage2_identity["version_labels_match"], true);
    assert_eq!(stage2_identity["targo_verbose_version_identity"]["binary"], "targo");
    assert_eq!(stage2_identity["trustc_verbose_version_identity"]["binary"], "trustc");
    assert_eq!(stage2_identity["trustdoc_verbose_version_identity"]["binary"], "trustdoc");
    assert_eq!(stage2_identity["trustd_version_identity"]["binary"], "trustd");
    assert_eq!(
        stage2_identity["trustd_version_identity"]["protocol"],
        trust_router::coordinator::STATUS_VERSION
    );
    assert_eq!(stage2_identity["trustd"]["sha256"], trustd_tool["sha256"]);
    assert_eq!(stage2_identity["trustd_protocol_smoke_required_on_this_platform"], cfg!(unix));
    assert_eq!(stage2_identity["trustd_protocol_smoke_completed"], cfg!(unix));
    if cfg!(unix) {
        assert_eq!(
            stage2_identity["trustd_protocol_smoke"]["schema"],
            "trust.self-verify.trustd-protocol-smoke.v1"
        );
        assert_eq!(stage2_identity["trustd_protocol_smoke"]["ping_response"], "PONG");
        assert_eq!(
            stage2_identity["trustd_protocol_smoke"]["fresh_owner_private_endpoint_required"],
            true
        );
        assert_eq!(
            stage2_identity["trustd_protocol_smoke"]["existing_endpoint_reuse_permitted"],
            false
        );
        assert_eq!(
            stage2_identity["trustd_protocol_smoke"]["canonical_child_spawn_required"],
            true
        );
        assert_eq!(stage2_identity["trustd_protocol_smoke"]["reservation_bytes"], 1);
        assert_eq!(
            stage2_identity["trustd_protocol_smoke"]["requests"],
            serde_json::json!([
                "PING", "IDENTITY", "STATUS", "RESERVE", "STATUS", "RELEASE", "STATUS"
            ])
        );
        assert_eq!(
            stage2_identity["trustd_protocol_smoke"]["reservation_label"],
            "product-proof-live-smoke"
        );
        assert!(
            stage2_identity["trustd_protocol_smoke"]["reservation_token"]
                .as_u64()
                .is_some_and(|token| token > 0)
        );
        assert_eq!(
            stage2_identity["trustd_protocol_smoke"]["status_reserved"]["active"][0]["pid"],
            stage2_identity["trustd_protocol_smoke"]["reservation_pid"]
        );
        assert_eq!(
            stage2_identity["trustd_protocol_smoke"]["status_reserved"]["active"][0]["token"],
            stage2_identity["trustd_protocol_smoke"]["reservation_token"]
        );
        assert_eq!(
            stage2_identity["trustd_protocol_smoke"]["status_released"]["active"],
            serde_json::json!([])
        );
        assert_eq!(
            stage2_identity["trustd_protocol_smoke"]["identity_response"]["version"],
            trust_router::coordinator::IDENTITY_VERSION
        );
        assert_eq!(
            stage2_identity["trustd_protocol_smoke"]["status_released"]["version"],
            trust_router::coordinator::STATUS_VERSION
        );
        assert_eq!(
            stage2_identity["trustd_protocol_smoke"]["identity_response"]["executable_sha256"],
            trustd_tool["sha256"]
        );
        assert_eq!(stage2_identity["trustd_protocol_smoke"]["status_semantically_valid"], true);
        let transcript = stage2_identity["trustd_protocol_smoke"]["transcript"]
            .as_str()
            .expect("trustd smoke transcript");
        assert!(transcript.contains("> RESERVE 1 "), "{transcript}");
        let reservation_token = stage2_identity["trustd_protocol_smoke"]["reservation_token"]
            .as_u64()
            .expect("trustd smoke reservation token");
        assert!(transcript.contains(&format!("\n< GRANTED {reservation_token}\n")), "{transcript}");
        assert!(
            transcript.contains(&format!("\n> RELEASE {reservation_token}\n< OK\n")),
            "{transcript}"
        );
        assert_eq!(
            sha256_text(transcript),
            stage2_identity["trustd_protocol_smoke"]["transcript_sha256"]
        );
        let smoke = &stage2_identity["trustd_protocol_smoke"];
        let expected_transcript = format!(
            "> PING\n< PONG\n> IDENTITY\n< {}\n> STATUS\n< {}\n> RESERVE 1 {} product-proof-live-smoke\n< GRANTED {}\n> STATUS\n< {}\n> RELEASE {}\n< OK\n> STATUS\n< {}\n",
            serde_json::to_string(&smoke["identity_response"]).unwrap(),
            serde_json::to_string(&smoke["status_before"]).unwrap(),
            smoke["reservation_pid"].as_u64().unwrap(),
            smoke["reservation_token"].as_u64().unwrap(),
            serde_json::to_string(&smoke["status_reserved"]).unwrap(),
            smoke["reservation_token"].as_u64().unwrap(),
            serde_json::to_string(&smoke["status_released"]).unwrap(),
        );
        assert_eq!(transcript, expected_transcript);
    }
    assert_eq!(
        stage2_identity["targo_verbose_version_identity"]["host"],
        stage2_identity["trustc_verbose_version_identity"]["host"]
    );
    assert_eq!(
        stage2_identity["trustc_verbose_version_identity"]["release"],
        stage2_identity["trustdoc_verbose_version_identity"]["release"]
    );
    assert_eq!(stage2_identity["source_provenance_bound"], false);
    assert_eq!(report["git"]["authority"], "not consulted by self-verification");
    assert_eq!(report["git"]["source_provenance_bound"], false);
    assert_eq!(stage2_identity["stage2_bin_plain_directory_required"], true);
    assert_eq!(report["toolchain"]["external_trust_anchor_present"], false);
    assert_eq!(report["toolchain"]["execution_identity_bound"], false);
    assert_eq!(report["toolchain"]["report_time_path_reopen"], false);
    assert_eq!(report["toolchain"]["report_time_hashing"], false);
    assert_eq!(report["toolchain"]["transient_swap_restore_detected"], false);
    assert_eq!(
        report["toolchain"]["endpoint_snapshot_equality_detects_persistent_change_only"],
        true
    );
    let residual =
        report["toolchain"]["residual_assumption"].as_str().expect("toolchain residual assumption");
    assert!(residual.contains("replace/execute/restore"), "{residual}");
    assert!(residual.contains("execution isolation"), "{residual}");
    assert_eq!(report["stages"][0]["env_policy"]["stage2_execution_identity_bound"], false);
    assert_eq!(report["configuration"]["dry_run_identity_probes_executed"], true);
    assert_eq!(report["stages"][0]["identity_probes"]["executed_during_planning"], true);
}

#[cfg(unix)]
#[test]
fn verify_self_dry_run_executes_only_documented_identity_probes() {
    let fixture = Fixture::new("targo-trust-verify-self-dry-run-probes");
    fixture.install_stage2_targo();
    let label = FIXTURE_VERSION_COMMIT;
    let trustc_marker = fixture.temp.path().join("trustc-probed");
    let trustdoc_marker = fixture.temp.path().join("trustdoc-probed");
    let stage_marker = fixture.temp.path().join("stage-executed");
    for (tool, marker) in [("trustc", &trustc_marker), ("trustdoc", &trustdoc_marker)] {
        install_stage2_file(
            &fixture.repo_root,
            tool,
            &format!(
                "#!/bin/sh\n[ \"${{1:-}}\" = \"-Vv\" ] || exit 2\nprintf probed > '{}'\nprintf 'rustc {FIXTURE_VERSION_RELEASE} ({tool})\\nbinary: {tool}\\ncommit-hash: {label}\\nhost: {FIXTURE_VERSION_HOST}\\nrelease: {FIXTURE_VERSION_RELEASE}\\n'\n",
                marker.display()
            ),
            true,
        );
    }

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "self",
            "--repo-root",
            fixture.repo_str(),
            "--report-dir",
            fixture.report_str(),
            "--full-verifier",
            "--dry-run",
        ])
        .env("SELF_VERIFY_EXECUTION_MARKER", &stage_marker)
        .output()
        .expect("run dry-run probe fixture");

    assert_eq!(
        output.status.code(),
        Some(0),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(trustc_marker.exists(), "dry run omitted the documented trustc identity probe");
    assert!(trustdoc_marker.exists(), "dry run omitted the documented trustdoc identity probe");
    assert!(!stage_marker.exists(), "dry run executed the planned stage command");
    let report = fixture.report();
    assert_eq!(report["configuration"]["dry_run"], true);
    assert_eq!(report["configuration"]["dry_run_identity_probes_executed"], true);
    assert_eq!(report["stages"][0]["identity_probes"]["executed_during_planning"], true);
}

#[test]
fn verify_self_full_verifier_pins_validated_stage2_trustc_and_trustdoc_for_cargo() {
    let fixture = Fixture::new("targo-trust-verify-self-pinned-stage2-trustc");
    let stage2_targo = fixture.install_stage2_targo();
    let stage2_trustc = stage2_targo
        .with_file_name(stage2_file_name("trustc"))
        .canonicalize()
        .expect("canonical stage2 trustc");
    let stage2_trustc = stage2_trustc.to_str().expect("stage2 trustc path should be utf-8");
    let stage2_trustdoc = stage2_targo
        .with_file_name(stage2_file_name("trustdoc"))
        .canonicalize()
        .expect("canonical stage2 trustdoc");
    let stage2_trustdoc = stage2_trustdoc.to_str().expect("stage2 trustdoc path should be utf-8");
    let stage2_trustd = stage2_targo
        .with_file_name(stage2_file_name("trustd"))
        .canonicalize()
        .expect("canonical stage2 trustd");
    let stage2_trustd = stage2_trustd.to_str().expect("stage2 trustd path should be utf-8");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "self",
            "--repo-root",
            fixture.repo_str(),
            "--report-dir",
            fixture.report_str(),
            "--full-verifier",
            "--dry-run",
        ])
        .env("RUSTC", "/untrusted/ambient/rustc")
        .env("CARGO_BUILD_RUSTC", "/untrusted/cargo-config/rustc")
        .env("RUSTDOC", "/untrusted/ambient/rustdoc")
        .env("CARGO_BUILD_RUSTDOC", "/untrusted/cargo-config/rustdoc")
        .env("TRUST_TRUSTDOC_BIN", "/untrusted/trustdoc")
        .env("TRUST_SELF_VERIFY_TRUSTDOC_SHA256", "attacker-controlled")
        .env("TRUST_TRUSTD_BIN", "/untrusted/trustd")
        .env("TRUST_SELF_VERIFY_TRUSTD_SHA256", "attacker-controlled")
        .env("CARGO_CACHE_RUSTC_INFO", "1")
        .output()
        .expect("run full verifier compiler-environment dry run");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "full verifier compiler pinning should plan successfully\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let report = fixture.report();
    let environment = &report["stages"][0]["environment"];
    assert_eq!(environment["RUSTC"], stage2_trustc);
    assert_eq!(environment["CARGO_BUILD_RUSTC"], stage2_trustc);
    assert_eq!(environment["RUSTDOC"], stage2_trustdoc);
    assert_eq!(environment["CARGO_BUILD_RUSTDOC"], stage2_trustdoc);
    assert_eq!(environment["TRUST_TRUSTDOC_BIN"], stage2_trustdoc);
    assert_eq!(environment["TRUST_SELF_VERIFY_TRUSTDOC_SHA256"].as_str().map(str::len), Some(64));
    assert_eq!(environment["TRUST_TRUSTD_BIN"], stage2_trustd);
    assert_eq!(environment["TRUST_SELF_VERIFY_TRUSTD_SHA256"].as_str().map(str::len), Some(64));
    assert_eq!(environment["CARGO_CACHE_RUSTC_INFO"], "0");
    for key in [
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "CARGO_BUILD_RUSTC_WRAPPER",
        "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
    ] {
        assert_eq!(environment[key], "", "effective {key} pin was not recorded");
    }

    let policy = &report["stages"][0]["env_policy"]["pinned_compiler_environment"];
    assert_eq!(policy["authority"], "validated canonical stage2 trustc");
    assert_eq!(policy["RUSTC"], stage2_trustc);
    assert_eq!(policy["CARGO_BUILD_RUSTC"], stage2_trustc);
    assert_eq!(policy["CARGO_CACHE_RUSTC_INFO"], "0");
    assert_eq!(policy["cargo_rustc_info_cache_disabled"], true);
    for key in [
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "CARGO_BUILD_RUSTC_WRAPPER",
        "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
    ] {
        assert_eq!(policy[key], "", "effective {key} policy was not recorded");
    }
    assert_eq!(policy["compiler_wrappers_disabled"], true);
    let rustdoc_policy = &report["stages"][0]["env_policy"]["pinned_rustdoc_environment"];
    assert_eq!(rustdoc_policy["authority"], "validated canonical stage2 trustdoc");
    assert_eq!(rustdoc_policy["RUSTDOC"], stage2_trustdoc);
    assert_eq!(rustdoc_policy["CARGO_BUILD_RUSTDOC"], stage2_trustdoc);
    let trustd_policy = &report["stages"][0]["env_policy"]["pinned_trustd_environment"];
    assert_eq!(trustd_policy["authority"], "validated canonical same-stage2-bin trustd");
    assert_eq!(trustd_policy["TRUST_TRUSTD_BIN"], stage2_trustd);
    assert_eq!(trustd_policy["ambient_lookup_permitted"], false);
    assert_eq!(trustd_policy["live_protocol_smoke_required"], cfg!(unix));
    assert_eq!(trustd_policy["live_protocol_smoke_completed"], cfg!(unix));
    let removed = report["stages"][0]["env_policy"]["removed_toolchain_override_environment"]
        .as_array()
        .expect("removed compiler environment overrides");
    for key in [
        "RUSTC",
        "CARGO_BUILD_RUSTC",
        "RUSTDOC",
        "CARGO_BUILD_RUSTDOC",
        "TRUST_TRUSTDOC_BIN",
        "TRUST_SELF_VERIFY_TRUSTDOC_SHA256",
        "TRUST_TRUSTD_BIN",
        "TRUST_SELF_VERIFY_TRUSTD_SHA256",
        "CARGO_CACHE_RUSTC_INFO",
    ] {
        assert!(removed.iter().any(|removed| removed == key), "missing removed {key}: {removed:?}");
    }
    assert_eq!(report["stages"][0]["env_policy"]["stage2_execution_identity_bound"], false);
}

#[test]
fn verify_self_full_verifier_default_requires_repo_local_stage2_targo() {
    let fixture = Fixture::new("targo-trust-verify-self-missing-stage2-targo");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "self",
            "--repo-root",
            fixture.repo_str(),
            "--report-dir",
            fixture.report_str(),
            "--full-verifier",
            "--dry-run",
        ])
        .output()
        .expect("run verify self dry run without stage2 targo");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "missing repo-local stage2 Targo should fail before planning\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("default --full-verifier requires a repo-local stage2 Targo endpoint"),
        "{stderr}"
    );
    assert!(
        stderr.contains(&format!("build/host/stage2/bin/{}", stage2_file_name("targo"))),
        "{stderr}"
    );
    assert!(
        !fixture.report_dir.join("self-verify-harness.report.json").exists(),
        "missing default stage2 Targo must not leave a self-verification report"
    );
}

#[test]
fn verify_self_full_verifier_requires_executable_sibling_trustc() {
    let fixture = Fixture::new("targo-trust-verify-self-missing-stage2-trustc");
    install_stage2_file(&fixture.repo_root, "targo", fake_stage(), true);
    let output = run_full_dry_run(&fixture);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr:\n{stderr}");
    assert!(stderr.contains("requires stage2 `trustc`"), "{stderr}");
    assert!(
        stderr.contains(&format!("build/host/stage2/bin/{}", stage2_file_name("trustc"))),
        "{stderr}"
    );
    assert!(!fixture.report_dir.join("self-verify-harness.report.json").exists());
}

#[test]
fn verify_self_full_verifier_requires_executable_sibling_trustdoc() {
    let fixture = Fixture::new("targo-trust-verify-self-missing-stage2-trustdoc");
    install_stage2_file(&fixture.repo_root, "targo", fake_stage(), true);
    install_stage2_file(&fixture.repo_root, "trustc", "#!/bin/sh\nexit 0\n", true);
    let output = run_full_dry_run(&fixture);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr:\n{stderr}");
    assert!(stderr.contains("requires stage2 `trustdoc`"), "{stderr}");
    assert!(
        stderr.contains(&format!("build/host/stage2/bin/{}", stage2_file_name("trustdoc"))),
        "{stderr}"
    );
    assert!(!fixture.report_dir.join("self-verify-harness.report.json").exists());
}

#[test]
fn verify_self_full_verifier_requires_executable_sibling_trustd() {
    let fixture = Fixture::new("targo-trust-verify-self-missing-stage2-trustd");
    install_stage2_file(&fixture.repo_root, "targo", fake_stage(), true);
    install_stage2_file(
        &fixture.repo_root,
        "trustc",
        &fake_compiler_version_script("trustc", FIXTURE_VERSION_COMMIT),
        true,
    );
    install_stage2_file(
        &fixture.repo_root,
        "trustdoc",
        &fake_compiler_version_script("trustdoc", FIXTURE_VERSION_COMMIT),
        true,
    );
    let output = run_full_dry_run(&fixture);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr:\n{stderr}");
    assert!(stderr.contains("requires stage2 `trustd`"), "{stderr}");
    assert!(
        stderr.contains(&format!("build/host/stage2/bin/{}", stage2_file_name("trustd"))),
        "{stderr}"
    );
    assert!(!fixture.report_dir.join("self-verify-harness.report.json").exists());
}

#[test]
fn verify_self_full_verifier_rejects_nonregular_sibling_trustc() {
    let fixture = Fixture::new("targo-trust-verify-self-directory-stage2-trustc");
    install_stage2_file(&fixture.repo_root, "targo", fake_stage(), true);
    let trustc = fixture.repo_root.join("build/host/stage2/bin").join(stage2_file_name("trustc"));
    fs::create_dir_all(&trustc).expect("create trustc directory");
    let output = run_full_dry_run(&fixture);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr:\n{stderr}");
    assert!(stderr.contains("stage2 `trustc` to be a regular file"), "{stderr}");
}

#[test]
fn verify_self_full_verifier_rejects_nonregular_sibling_trustdoc() {
    let fixture = Fixture::new("targo-trust-verify-self-directory-stage2-trustdoc");
    install_stage2_file(&fixture.repo_root, "targo", fake_stage(), true);
    install_stage2_file(&fixture.repo_root, "trustc", "#!/bin/sh\nexit 0\n", true);
    let trustdoc =
        fixture.repo_root.join("build/host/stage2/bin").join(stage2_file_name("trustdoc"));
    fs::create_dir_all(&trustdoc).expect("create trustdoc directory");
    let output = run_full_dry_run(&fixture);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr:\n{stderr}");
    assert!(stderr.contains("stage2 `trustdoc` to be a regular file"), "{stderr}");
}

#[cfg(unix)]
#[test]
fn verify_self_full_verifier_rejects_nonexecutable_stage2_tools() {
    for nonexecutable in ["targo", "trustc", "trustdoc", "trustd"] {
        let fixture =
            Fixture::new(&format!("targo-trust-verify-self-nonexec-stage2-{nonexecutable}"));
        install_stage2_file(&fixture.repo_root, "targo", fake_stage(), nonexecutable != "targo");
        install_stage2_file(
            &fixture.repo_root,
            "trustc",
            "#!/bin/sh\nexit 0\n",
            nonexecutable != "trustc",
        );
        install_stage2_file(
            &fixture.repo_root,
            "trustdoc",
            "#!/bin/sh\nexit 0\n",
            nonexecutable != "trustdoc",
        );
        install_stage2_file(
            &fixture.repo_root,
            "trustd",
            &fake_trustd_version_and_server_script(FIXTURE_VERSION_COMMIT, FIXTURE_VERSION_RELEASE),
            nonexecutable != "trustd",
        );
        let output = run_full_dry_run(&fixture);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(2), "{nonexecutable}: {stderr}");
        assert!(
            stderr.contains(&format!("requires executable stage2 `{nonexecutable}`")),
            "{nonexecutable}: {stderr}"
        );
    }
}

#[cfg(unix)]
#[test]
fn verify_self_full_verifier_rejects_symlinked_stage2_tools() {
    use std::os::unix::fs::symlink;

    for symlinked in ["targo", "trustc", "trustdoc", "trustd"] {
        let fixture = Fixture::new(&format!("targo-trust-verify-self-symlink-stage2-{symlinked}"));
        let external = fixture.temp.path().join(format!("external-{symlinked}"));
        fs::write(&external, "#!/bin/sh\nexit 0\n").expect("write external tool");
        {
            use std::os::unix::fs::PermissionsExt;
            let mut permissions = fs::metadata(&external).expect("external metadata").permissions();
            permissions.set_mode(0o755);
            fs::set_permissions(&external, permissions).expect("chmod external tool");
        }
        let target =
            fixture.repo_root.join("build/host/stage2/bin").join(stage2_file_name(symlinked));
        fs::create_dir_all(target.parent().expect("stage2 bin")).expect("create stage2 bin");
        symlink(&external, &target).expect("symlink stage2 tool");
        for other in ["targo", "trustc", "trustdoc", "trustd"] {
            if other != symlinked {
                let contents = if other == "trustd" {
                    fake_trustd_version_and_server_script(
                        FIXTURE_VERSION_COMMIT,
                        FIXTURE_VERSION_RELEASE,
                    )
                } else {
                    "#!/bin/sh\nexit 0\n".to_string()
                };
                install_stage2_file(&fixture.repo_root, other, &contents, true);
            }
        }

        let output = run_full_dry_run(&fixture);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(2), "{symlinked}: {stderr}");
        assert!(
            stderr.contains(&format!("rejects symlinked stage2 `{symlinked}`")),
            "{symlinked}: {stderr}"
        );
    }
}

#[cfg(unix)]
#[test]
fn verify_self_full_verifier_rejects_stage2_bin_redirected_out_of_repo() {
    use std::os::unix::fs::symlink;

    let fixture = Fixture::new("targo-trust-verify-self-redirected-stage2-bin");
    let external_bin = fixture.temp.path().join("external-stage2-bin");
    fs::create_dir_all(&external_bin).expect("create external stage2 bin");
    let external_targo = external_bin.join(stage2_file_name("targo"));
    let external_trustc = external_bin.join(stage2_file_name("trustc"));
    let external_trustdoc = external_bin.join(stage2_file_name("trustdoc"));
    fs::write(&external_targo, fake_stage()).expect("write external targo");
    fs::write(&external_trustc, "#!/bin/sh\nexit 0\n").expect("write external trustc");
    fs::write(&external_trustdoc, "#!/bin/sh\nexit 0\n").expect("write external trustdoc");
    {
        use std::os::unix::fs::PermissionsExt;
        for path in [&external_targo, &external_trustc, &external_trustdoc] {
            let mut permissions = fs::metadata(path).expect("external tool metadata").permissions();
            permissions.set_mode(0o755);
            fs::set_permissions(path, permissions).expect("chmod external tool");
        }
    }
    let stage2 = fixture.repo_root.join("build/host/stage2");
    fs::create_dir_all(&stage2).expect("create stage2 parent");
    symlink(&external_bin, stage2.join("bin")).expect("redirect stage2 bin");

    let output = run_full_dry_run(&fixture);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr:\n{stderr}");
    assert!(stderr.contains("rejects symlinked stage2 directory"), "{stderr}");
}

#[test]
fn verify_self_full_verifier_rejects_mismatched_stage2_verbose_identities() {
    let fixture = Fixture::new("targo-trust-verify-self-mismatched-stage2-labels");
    fixture.install_stage2_targo();
    let stale = "1111111111111111111111111111111111111111";
    install_stage2_file(
        &fixture.repo_root,
        "trustdoc",
        &fake_compiler_version_script("trustdoc", stale),
        true,
    );

    let output = run_full_dry_run(&fixture);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr:\n{stderr}");
    assert!(stderr.contains("commit-label consistency"), "{stderr}");
    assert!(stderr.contains("not source provenance"), "{stderr}");
    assert!(stderr.contains(stale), "{stderr}");
    assert!(stderr.contains(FIXTURE_VERSION_COMMIT), "{stderr}");
}

#[test]
fn verify_self_full_verifier_rejects_mismatched_stage2_trustd_identity() {
    let fixture = Fixture::new("targo-trust-verify-self-mismatched-stage2-trustd-label");
    fixture.install_stage2_targo();
    let stale = "1111111111111111111111111111111111111111";
    install_stage2_file(
        &fixture.repo_root,
        "trustd",
        &fake_trustd_version_and_server_script(stale, FIXTURE_VERSION_RELEASE),
        true,
    );

    let output = run_full_dry_run(&fixture);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr:\n{stderr}");
    assert!(stderr.contains("trustd/trustc commit-label consistency"), "{stderr}");
    assert!(stderr.contains("not source provenance"), "{stderr}");
    assert!(stderr.contains(stale), "{stderr}");
    assert!(stderr.contains(FIXTURE_VERSION_COMMIT), "{stderr}");
}

#[cfg(unix)]
#[test]
fn verify_self_full_verifier_rejects_trustd_live_identity_or_status_mismatch() {
    for (case, mutate, expected) in [
        (
            "wrong-live-executable-hash",
            "executable_sha256 = hashlib.sha256(executable.read()).hexdigest()",
            "executable_sha256 = \"0\" * 64",
        ),
        (
            "invalid-live-status",
            "\"free_bytes\": state[\"budget_bytes\"] - state[\"reserved_bytes\"],",
            "\"free_bytes\": state[\"budget_bytes\"] - state[\"reserved_bytes\"] - 1,",
        ),
    ] {
        let fixture = Fixture::new(&format!("targo-trust-verify-self-trustd-{case}"));
        fixture.install_stage2_targo();
        let script =
            fake_trustd_version_and_server_script(FIXTURE_VERSION_COMMIT, FIXTURE_VERSION_RELEASE)
                .replace(mutate, expected);
        install_stage2_file(&fixture.repo_root, "trustd", &script, true);

        let output = run_full_dry_run(&fixture);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(2), "{case}: {stderr}");
        assert!(
            stderr.contains("trustd") && (stderr.contains("IDENTITY") || stderr.contains("STATUS")),
            "{case}: {stderr}"
        );
        assert!(!fixture.report_dir.join("self-verify-harness.report.json").exists());
    }
}

#[test]
fn verify_self_rejects_wrong_program_and_incomplete_verbose_identities() {
    let cases = [
        (
            "wrong-trustdoc-binary",
            "trustdoc",
            format!(
                "#!/bin/sh\nprintf 'rustc {FIXTURE_VERSION_RELEASE}\\nbinary: rustdoc\\ncommit-hash: {FIXTURE_VERSION_COMMIT}\\nhost: {FIXTURE_VERSION_HOST}\\nrelease: {FIXTURE_VERSION_RELEASE}\\n'\n"
            ),
            "instead of required `trustdoc`",
        ),
        (
            "wrong-targo-brand",
            "targo",
            format!(
                "#!/bin/sh\nprintf 'cargo {FIXTURE_VERSION_RELEASE}\\nrelease: {FIXTURE_VERSION_RELEASE}\\ncommit-hash: {FIXTURE_VERSION_COMMIT}\\nhost: {FIXTURE_VERSION_HOST}\\n'\n"
            ),
            "exact `targo` branding",
        ),
        (
            "missing-targo-commit",
            "targo",
            format!(
                "#!/bin/sh\nprintf 'targo {FIXTURE_VERSION_RELEASE}\\nrelease: {FIXTURE_VERSION_RELEASE}\\nhost: {FIXTURE_VERSION_HOST}\\n'\n"
            ),
            "CARGO_COMMIT_HASH wiring",
        ),
        (
            "wrong-trustd-protocol",
            "trustd",
            format!(
                "#!/bin/sh\nprintf 'trustd {FIXTURE_VERSION_RELEASE}\\ntrust.identity=trustd\\ntrust.protocol=wrong.v1\\ncommit-hash: {FIXTURE_VERSION_COMMIT}\\n'\n"
            ),
            "instead of required `trustd.status.v1`",
        ),
        (
            "wrong-trustd-identity",
            "trustd",
            format!(
                "#!/bin/sh\nprintf 'trustd {FIXTURE_VERSION_RELEASE}\\ntrust.identity=other\\ntrust.protocol=trustd.status.v1\\ncommit-hash: {FIXTURE_VERSION_COMMIT}\\n'\n"
            ),
            "instead of required `trustd`",
        ),
    ];

    for (case, tool, script, expected) in cases {
        let fixture = Fixture::new(&format!("targo-trust-verify-self-{case}"));
        fixture.install_stage2_targo();
        install_stage2_file(&fixture.repo_root, tool, &script, true);
        let output = run_full_dry_run(&fixture);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(2), "{case}: {stderr}");
        assert!(stderr.contains(expected), "{case}: {stderr}");
    }
}

#[test]
fn verify_self_matching_tool_labels_are_not_misreported_as_git_provenance() {
    let fixture = Fixture::new("targo-trust-verify-self-labels-not-git-provenance");
    fixture.install_stage2_targo();
    let diagnostic_label = FIXTURE_VERSION_COMMIT;
    assert_ne!(diagnostic_label, fixture_git_head(&fixture.repo_root));
    for tool in ["trustc", "trustdoc"] {
        install_stage2_file(
            &fixture.repo_root,
            tool,
            &fake_compiler_version_script(tool, diagnostic_label),
            true,
        );
    }

    let output = run_full_dry_run(&fixture);
    assert_eq!(
        output.status.code(),
        Some(0),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report = fixture.report();
    let identity = &report["stages"][0]["stage2_toolchain_identity"];
    assert_eq!(identity["targo_commit"], diagnostic_label);
    assert_eq!(identity["trustc_commit"], diagnostic_label);
    assert_eq!(identity["trustdoc_commit"], diagnostic_label);
    assert_eq!(identity["trustd_commit"], diagnostic_label);
    assert_eq!(identity["version_labels_match"], true);
    assert_eq!(identity["source_provenance_bound"], false);
    assert_eq!(report["git"]["head_available"], false);
    assert_eq!(report["git"]["authority"], "not consulted by self-verification");
}

#[cfg(unix)]
#[test]
fn verify_self_version_label_validation_does_not_execute_path_git() {
    use std::os::unix::fs::PermissionsExt as _;

    let fixture = Fixture::new("targo-trust-verify-self-path-git-forgery");
    fixture.install_stage2_targo();
    let expected_label = FIXTURE_VERSION_COMMIT;
    let forged_head = "1111111111111111111111111111111111111111";
    install_stage2_file(
        &fixture.repo_root,
        "trustdoc",
        &fake_compiler_version_script("trustdoc", forged_head),
        true,
    );
    let shim_dir = fixture.temp.path().join("hostile-path");
    fs::create_dir(&shim_dir).expect("hostile PATH directory");
    let marker = fixture.temp.path().join("ambient-git-executed");
    let git = shim_dir.join("git");
    fs::write(
        &git,
        format!(
            "#!/bin/sh\nprintf executed > '{}'\nprintf '%s\\n' '{forged_head}'\n",
            marker.display()
        ),
    )
    .expect("hostile git shim");
    fs::set_permissions(&git, fs::Permissions::from_mode(0o755)).expect("chmod hostile git shim");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "self",
            "--repo-root",
            fixture.repo_str(),
            "--report-dir",
            fixture.report_str(),
            "--full-verifier",
            "--dry-run",
        ])
        .env("PATH", &shim_dir)
        .output()
        .expect("run full verifier with hostile PATH git");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr:\n{stderr}");
    assert!(stderr.contains("commit-label consistency"), "{stderr}");
    assert!(stderr.contains(expected_label), "{stderr}");
    assert!(stderr.contains(forged_head), "{stderr}");
    assert!(!marker.exists(), "self-verification executed ambient PATH git");
}

#[cfg(unix)]
#[test]
fn verify_self_trustd_smoke_never_executes_ambient_path_daemon() {
    use std::os::unix::fs::PermissionsExt as _;

    let fixture = Fixture::new("targo-trust-verify-self-no-ambient-trustd");
    fixture.install_stage2_targo();
    let shim_dir = fixture.temp.path().join("hostile-path");
    fs::create_dir(&shim_dir).expect("hostile PATH directory");
    let marker = fixture.temp.path().join("ambient-trustd-executed");
    let trustd = shim_dir.join("trustd");
    fs::write(&trustd, format!("#!/bin/sh\nprintf executed > '{}'\nexit 99\n", marker.display()))
        .expect("hostile trustd shim");
    fs::set_permissions(&trustd, fs::Permissions::from_mode(0o755))
        .expect("chmod hostile trustd shim");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "self",
            "--repo-root",
            fixture.repo_str(),
            "--report-dir",
            fixture.report_str(),
            "--full-verifier",
            "--dry-run",
        ])
        .env("PATH", &shim_dir)
        .output()
        .expect("run no-ambient-trustd fixture");

    assert_eq!(
        output.status.code(),
        Some(0),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!marker.exists(), "self-verify executed ambient PATH trustd");
    let report = fixture.report();
    assert_eq!(
        report["stages"][0]["stage2_toolchain_identity"]["trustd_protocol_smoke"]["ambient_lookup_permitted"],
        false
    );
}

#[test]
fn verify_self_rejects_removed_allow_incomplete_option() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "verify", "self", "--allow-incomplete"])
        .output()
        .expect("run verify self");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "removed allow-incomplete option must fail closed\nstderr:\n{stderr}"
    );
    assert!(stderr.contains("--allow-incomplete was removed"), "{stderr}");
}

#[test]
fn verify_self_refuses_complete_claim_without_execution_bound_stage2_bytes() {
    let fixture = Fixture::new("targo-trust-verify-self-complete");
    fixture.install_stage2_targo();
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "self",
            "--repo-root",
            fixture.repo_str(),
            "--report-dir",
            fixture.report_str(),
            "--timeout",
            FIXTURE_TIMEOUT_SEC,
            "--full-verifier",
        ])
        .env("SELF_VERIFY_FAKE_MODE", "native-proved")
        .env("TRUST_VERIFY_WORKER_THREADS", "3")
        .output()
        .expect("run verify self");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let report = fixture.report();
    let cargo_stdout = fs::read_to_string(
        report["stages"][0]["logs"]["stdout"].as_str().expect("stage stdout log path"),
    )
    .expect("read stage stdout log");
    assert_eq!(
        output.status.code(),
        Some(1),
        "endpoint-only identity must not claim a complete proof\nstdout:\n{stdout}\nstderr:\n{stderr}\nstage stdout:\n{cargo_stdout}\nreport:\n{report:#}"
    );

    assert_eq!(report["schema"], "trust.self-verify-harness.report.v1");
    assert_eq!(report["status"], "incomplete");
    assert_eq!(report["proof"]["status"], "incomplete");
    assert_eq!(report["proof"]["complete"], false);
    assert_eq!(report["solver_suite"]["stage2_toolchain_identity_verified"], true);
    assert_eq!(report["solver_suite"]["stage2_execution_identity_bound"], false);
    assert_eq!(report["solver_suite"]["source_provenance_bound"], false);
    assert_eq!(report["configuration"]["full_verifier"], true);
    assert_eq!(report["configuration"]["worker_threads"], "3");
    assert!(
        report["stages"][0]["environment"].get("TRUST_VERIFY_WORKER_THREADS").is_none(),
        "retired compiler environment input must not reach the stage"
    );
    assert_eq!(report["stages"][0]["env_policy"]["worker_threads"], "3");
    assert!(
        report["stages"][0]["env_policy"]["verification_flags"]
            .as_array()
            .expect("verification flags")
            .iter()
            .any(|flag| flag == "-Z trust-verify-worker-threads=3"),
        "worker setting must be translated into a tracked rustc option"
    );
    assert_eq!(report["solver_suite"]["obligation_rows"], 1);
    assert_eq!(report["solver_suite"]["outcomes"]["proved"], 1);
    let aggregate_inventories = report["solver_suite"]["cargo_proof_inventories"]
        .as_array()
        .expect("aggregate Cargo proof inventories");
    let stage_inventories = report["stages"][0]["solver_suite"]["cargo_proof_inventories"]
        .as_array()
        .expect("stage Cargo proof inventories");
    assert_eq!(aggregate_inventories, stage_inventories);
    assert_eq!(aggregate_inventories.len(), 1);
    let inventory = &aggregate_inventories[0];
    assert_eq!(inventory["include_dependencies"], true);
    assert_eq!(inventory["declared"], inventory["completed"]);
    assert_eq!(inventory["declared"], inventory["covered"]);
    assert!(
        inventory["excluded_active_units"].as_array().expect("excluded Cargo units").is_empty()
    );
    assert_eq!(
        report["solver_suite"]["verification_rows"][0]["proof_binding"]["accepted"], true,
        "{:#}",
        report["solver_suite"]["verification_rows"][0]["proof_binding"]
    );
    assert_eq!(
        report["solver_suite"]["verification_rows"][0]["proof_binding"]["publication_grade_native_proof"],
        true
    );
    assert_eq!(
        report["solver_suite"]["verification_rows"][0]["proof_binding"]["canonical_sha256_digest_binding"],
        true
    );
    assert_eq!(
        report["solver_suite"]["verification_rows"][0]["proof_binding"]["repo_local_readable_path_binding"],
        true
    );
    assert_eq!(
        report["solver_suite"]["verification_rows"][0]["proof_binding"]["materialized_artifact_or_transcript_binding"],
        true
    );
    assert_eq!(
        report["solver_suite"]["verification_rows"][0]["proof_binding"]["required_artifact_materialization"]
            ["solver_transcript_bound"],
        true
    );
    assert_eq!(
        report["solver_suite"]["verification_rows"][0]["proof_binding"]["required_artifact_materialization"]
            ["replay_or_check_bound"],
        true
    );
    assert!(
        report["proof"]["reasons"]
            .as_array()
            .expect("proof reasons")
            .iter()
            .filter_map(Value::as_str)
            .any(|reason| reason.contains("exact executable bytes")),
        "execution identity gap must be explicit: {}",
        report["proof"]
    );
    assert!(
        report["proof"]["reasons"]
            .as_array()
            .expect("proof reasons")
            .iter()
            .filter_map(Value::as_str)
            .any(|reason| reason.contains("verbose-version agreement")
                && reason.contains("not source provenance")),
        "source provenance gap must be explicit: {}",
        report["proof"]
    );
    assert_eq!(report["exit"]["exit_code"], 1);
}

#[test]
fn verify_self_fails_closed_on_incomplete_and_unrecognized_outcomes() {
    let cases = [
        ("timed-out", "timed-out", "timed_out", "timed out"),
        ("unknown", "unknown", "unknown", "unknown"),
        ("skipped", "skipped", "skipped", "skipped"),
        ("runtime-checked", "runtime checked", "runtime_checked", "runtime_checked"),
        ("no-verification", "no verification", "no_verification", "no_verification"),
        ("unverified", "Unverified", "unverified", "unverified"),
        ("unrecognized", "solver_gave_up", "solver_gave_up", "unrecognized outcome"),
    ];

    for (case, emitted_outcome, normalized_outcome, reason_fragment) in cases {
        let fixture = Fixture::new(&format!("targo-trust-verify-self-outcome-{case}"));
        fixture.install_stage2_targo();
        let output = Command::new(targo_trust_binary())
            .args([
                "trust",
                "verify",
                "self",
                "--repo-root",
                fixture.repo_str(),
                "--report-dir",
                fixture.report_str(),
                "--timeout",
                FIXTURE_TIMEOUT_SEC,
                "--full-verifier",
            ])
            .env("SELF_VERIFY_FAKE_MODE", "outcome")
            .env("SELF_VERIFY_FAKE_OUTCOME", emitted_outcome)
            .output()
            .expect("run verify self with incomplete outcome");

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(1),
            "{case} should fail closed\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );

        let report = fixture.report();
        assert_eq!(report["status"], "incomplete", "{case} report status");
        assert_eq!(report["proof"]["complete"], false, "{case} proof completeness");
        assert_eq!(
            report["solver_suite"]["outcomes"][normalized_outcome], 1,
            "{case} normalized outcome count"
        );
        let reasons = report["proof"]["reasons"]
            .as_array()
            .expect("proof reasons")
            .iter()
            .filter_map(Value::as_str)
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            reasons.contains(reason_fragment),
            "{case} reasons should mention {reason_fragment:?}\n{reasons}"
        );
    }
}

#[test]
fn verify_self_complete_proof_requires_row_level_proof_binding() {
    let fixture = Fixture::new("targo-trust-verify-self-missing-proof-binding");
    fixture.install_stage2_targo();
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "self",
            "--repo-root",
            fixture.repo_str(),
            "--report-dir",
            fixture.report_str(),
            "--timeout",
            FIXTURE_TIMEOUT_SEC,
            "--full-verifier",
        ])
        .env("SELF_VERIFY_FAKE_MODE", "no-proof-binding")
        .output()
        .expect("run verify self with missing proof binding");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "missing row proof binding should fail closed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let report = fixture.report();
    assert_eq!(report["status"], "incomplete");
    assert_eq!(report["proof"]["complete"], false);
    assert_eq!(report["solver_suite"]["outcomes"]["proved"], 1);
    assert_eq!(report["solver_suite"]["verification_rows"][0]["proof_binding"]["accepted"], false);
    assert!(
        report["solver_suite"]["coverage_blockers"]
            .as_array()
            .expect("coverage blockers")
            .iter()
            .any(|blocker| blocker["kind"] == "missing_proof_binding"),
        "missing proof binding should be a structured coverage blocker"
    );
    let reasons = report["proof"]["reasons"]
        .as_array()
        .expect("proof reasons")
        .iter()
        .filter_map(Value::as_str)
        .collect::<Vec<_>>()
        .join("\n");
    assert!(reasons.contains("proof artifact/transcript binding"), "{reasons}");
}

#[test]
fn verify_self_complete_proof_rejects_string_only_proof_binding() {
    let fixture = Fixture::new("targo-trust-verify-self-string-only-proof-binding");
    fixture.install_stage2_targo();
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "self",
            "--repo-root",
            fixture.repo_str(),
            "--report-dir",
            fixture.report_str(),
            "--timeout",
            FIXTURE_TIMEOUT_SEC,
            "--full-verifier",
        ])
        .env("SELF_VERIFY_FAKE_MODE", "string-only-proof-binding")
        .output()
        .expect("run verify self with string-only proof binding");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "string-only proof binding should fail closed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let report = fixture.report();
    let binding = &report["solver_suite"]["verification_rows"][0]["proof_binding"];
    assert_eq!(report["status"], "incomplete");
    assert_eq!(report["proof"]["complete"], false);
    assert_eq!(report["solver_suite"]["outcomes"]["proved"], 1);
    assert_eq!(binding["canonical_sha256_digest_binding"], true);
    assert_eq!(binding["publication_grade_native_proof"], false);
    assert_eq!(binding["repo_local_readable_path_binding"], false);
    assert_eq!(binding["materialized_artifact_or_transcript_binding"], false);
    assert_eq!(binding["accepted"], false);
    assert!(
        binding["path_evidence"].as_array().expect("path evidence").is_empty(),
        "nested metadata paths must not become typed artifact paths"
    );
    assert!(
        report["solver_suite"]["coverage_blockers"]
            .as_array()
            .expect("coverage blockers")
            .iter()
            .any(|blocker| blocker["kind"] == "missing_proof_binding"),
        "string-only proof binding should be a structured coverage blocker"
    );
}

#[test]
fn verify_self_fails_closed_without_transport() {
    let fixture = Fixture::new("targo-trust-verify-self-no-transport");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "self",
            "--repo-root",
            fixture.repo_str(),
            "--report-dir",
            fixture.report_str(),
            "--timeout",
            FIXTURE_TIMEOUT_SEC,
            "--stage-command",
            "sh",
            fixture.stage_str(),
            "no-transport",
        ])
        .output()
        .expect("run verify self");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "missing TRUST_JSON must fail closed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let report = fixture.report();
    assert_eq!(report["status"], "incomplete");
    assert_eq!(report["proof"]["complete"], false);
    assert_eq!(report["solver_suite"]["transport_message_count"], 0);
    assert!(
        report["proof"]["reasons"]
            .as_array()
            .expect("proof reasons")
            .iter()
            .filter_map(Value::as_str)
            .any(|reason| reason.contains("no authenticated Cargo compiler-message transport")),
        "raw or absent transport must not establish proof authority: {}",
        report["proof"]["reasons"]
    );
    assert_eq!(report["exit"]["exit_code"], 1);
}

#[test]
fn verify_self_rejects_canonical_transport_from_unpinned_stage_runner() {
    let fixture = Fixture::new("targo-trust-verify-self-unpinned-runner");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "self",
            "--repo-root",
            fixture.repo_str(),
            "--report-dir",
            fixture.report_str(),
            "--timeout",
            FIXTURE_TIMEOUT_SEC,
            "--stage-command",
            "sh",
            fixture.stage_str(),
            "native-proved",
        ])
        .output()
        .expect("run unpinned stage fixture");
    assert_eq!(output.status.code(), Some(1), "unpinned runner must never earn proof credit");

    let report = fixture.report();
    assert_eq!(report["proof"]["complete"], false);
    assert_eq!(report["solver_suite"]["authenticated_cargo_transport"], true);
    assert_eq!(report["solver_suite"]["stage2_toolchain_identity_verified"], false);
    assert!(
        report["proof"]["reasons"]
            .as_array()
            .expect("proof reasons")
            .iter()
            .filter_map(Value::as_str)
            .any(|reason| reason.contains("lacked a captured and rechecked")),
        "proof reasons must identify the missing toolchain boundary"
    );
}

#[test]
fn verify_self_ignores_raw_stderr_transport_forgery() {
    let fixture = Fixture::new("targo-trust-verify-self-stderr-forgery");
    let output = run_full_fixture_mode(&fixture, "stderr-forgery");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "a raw stderr forgery must neither inject failure nor displace authenticated proof\nstderr:\n{stderr}"
    );

    let report = fixture.report();
    assert_eq!(report["proof"]["complete"], false);
    assert_eq!(report["solver_suite"]["authenticated_cargo_transport"], true);
    assert_eq!(report["solver_suite"]["outcomes"]["proved"], 1);
    assert!(report["solver_suite"]["outcomes"].get("failed").is_none());
}

#[test]
fn verify_self_rejects_raw_stdout_transport_forgery() {
    let fixture = Fixture::new("targo-trust-verify-self-stdout-forgery");
    let output = run_full_fixture_mode(&fixture, "stdout-forgery");
    assert_eq!(
        output.status.code(),
        Some(1),
        "a raw stdout TRUST_JSON line must invalidate canonical Cargo JSON evidence"
    );

    let report = fixture.report();
    assert_eq!(report["proof"]["complete"], false);
    assert_eq!(report["solver_suite"]["authenticated_cargo_transport"], false);
    assert!(
        report["solver_suite"]["parse_errors"]
            .as_array()
            .expect("parse errors")
            .iter()
            .filter_map(Value::as_str)
            .any(|error| error.contains("not a Cargo JSON envelope")),
        "raw stdout must be reported as noncanonical Cargo output"
    );
}

#[test]
fn verify_self_ignores_build_script_transport_forgery() {
    let fixture = Fixture::new("targo-trust-verify-self-build-script-forgery");
    let output = run_full_fixture_mode(&fixture, "build-script-forgery");
    assert_eq!(
        output.status.code(),
        Some(1),
        "build-script JSON and stderr cannot become proof transport"
    );

    let report = fixture.report();
    assert_eq!(report["proof"]["complete"], false);
    assert_eq!(report["solver_suite"]["transport_message_count"], 2);
    assert_eq!(report["solver_suite"]["outcomes"]["proved"], 1);
    assert!(report["solver_suite"]["outcomes"].get("failed").is_none());
}

#[test]
fn verify_self_rejects_materialized_artifact_with_mismatched_digest() {
    let fixture = Fixture::new("targo-trust-verify-self-mismatched-digest");
    let output = run_full_fixture_mode(&fixture, "mismatched-digest");
    assert_eq!(output.status.code(), Some(1), "digest mismatch must fail closed");

    let report = fixture.report();
    let binding = &report["solver_suite"]["verification_rows"][0]["proof_binding"];
    assert_eq!(report["solver_suite"]["outcomes"]["proved"], 1);
    assert_eq!(binding["canonical_sha256_digest_binding"], true);
    assert_eq!(binding["repo_local_readable_path_binding"], false);
    assert_eq!(binding["publication_grade_native_proof"], false);
    assert_eq!(binding["required_artifact_materialization"]["solver_transcript_bound"], false);
    assert_eq!(binding["required_artifact_materialization"]["replay_or_check_bound"], false);
    assert_eq!(binding["accepted"], false);
    assert_eq!(report["proof"]["complete"], false);
}

#[test]
fn verify_self_rejects_nonpublishable_and_confused_deputy_proof_evidence() {
    for mode in [
        "identity-mismatch",
        "backend-mismatch",
        "native-wrong-kind",
        "native-wrong-uri",
        "weak-strength",
        "missing-replay",
        "wrong-artifact-kind",
        "error-diagnostic",
        "cross-artifact",
        "uri-only",
        "metadata-only",
        "string-only-proof-binding",
    ] {
        let fixture = Fixture::new(&format!("targo-trust-verify-self-proof-contract-{mode}"));
        let output = run_full_fixture_mode(&fixture, mode);
        assert_eq!(output.status.code(), Some(1), "{mode} must fail closed");

        let report = fixture.report();
        let binding = &report["solver_suite"]["verification_rows"][0]["proof_binding"];
        assert_eq!(binding["accepted"], false, "{mode}: {binding:#}");
        assert_eq!(report["proof"]["complete"], false, "{mode}");
        match mode {
            "identity-mismatch"
            | "backend-mismatch"
            | "native-wrong-kind"
            | "native-wrong-uri"
            | "weak-strength"
            | "missing-replay"
            | "wrong-artifact-kind"
            | "error-diagnostic" => {
                assert_eq!(binding["publication_grade_native_proof"], false, "{mode}");
            }
            "cross-artifact" | "uri-only" | "metadata-only" | "string-only-proof-binding" => {
                assert_eq!(binding["publication_grade_native_proof"], false, "{mode}");
                assert_eq!(
                    binding["required_artifact_materialization"]["complete"], false,
                    "{mode}: {binding:#}"
                );
            }
            _ => unreachable!(),
        }
    }
}

#[test]
fn verify_self_requires_complete_coverage_and_terminal_summary() {
    for (mode, expected_fragment) in [
        ("incomplete-coverage", "coverage"),
        ("zero-coverage", "coverage"),
        ("no-terminal-summary", "terminal summary"),
    ] {
        let fixture = Fixture::new(&format!("targo-trust-verify-self-{mode}"));
        let output = run_full_fixture_mode(&fixture, mode);
        assert_eq!(output.status.code(), Some(1), "{mode} must fail closed");

        let report = fixture.report();
        assert_eq!(report["proof"]["complete"], false, "{mode}");
        let reasons = report["proof"]["reasons"]
            .as_array()
            .expect("proof reasons")
            .iter()
            .filter_map(Value::as_str)
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            reasons.contains(expected_fragment),
            "{mode} reasons should mention {expected_fragment:?}: {reasons}"
        );
    }
}

#[test]
fn verify_self_authenticates_session_and_compiler_diagnostic_tag() {
    for mode in
        ["wrong-session", "stale-function-session", "stale-terminal-session", "bad-diagnostic-tag"]
    {
        let fixture = Fixture::new(&format!("targo-trust-verify-self-{mode}"));
        let output = run_full_fixture_mode(&fixture, mode);
        assert_eq!(output.status.code(), Some(1), "{mode} must fail closed");

        let report = fixture.report();
        assert_eq!(report["proof"]["complete"], false, "{mode}");
        assert_eq!(report["solver_suite"]["authenticated_cargo_transport"], false, "{mode}");
        assert!(
            !report["solver_suite"]["parse_errors"].as_array().expect("parse errors").is_empty(),
            "{mode} must retain a structured authentication error"
        );
    }
}

#[test]
fn verify_self_rejects_stage2_toolchain_mutation_during_run() {
    let fixture = Fixture::new("targo-trust-verify-self-toolchain-mutation");
    let output = run_full_fixture_mode(&fixture, "mutate-trustc");
    assert_eq!(output.status.code(), Some(1), "toolchain mutation must fail closed");

    let report = fixture.report();
    assert_eq!(report["status"], "failed");
    assert_eq!(report["proof"]["complete"], false);
    assert!(
        report["stages"][0]["error"]
            .as_str()
            .is_some_and(|error| error.contains("identity changed during self-verification")),
        "mutation failure must be explicit: {}",
        report["stages"][0]
    );
    let trustc = report["toolchain"]["tools"]
        .as_array()
        .expect("tools")
        .iter()
        .find(|tool| tool["tool"] == "trustc")
        .expect("trustc");
    assert_eq!(trustc["identity_matches_expected"], true);
    assert_eq!(
        trustc["snapshot_source"],
        "captured validated bounded endpoint snapshot; no report-time reopen"
    );
}

#[test]
fn verify_self_rejects_stage2_trustdoc_mutation_during_run() {
    let fixture = Fixture::new("targo-trust-verify-self-trustdoc-mutation");
    let output = run_full_fixture_mode(&fixture, "mutate-trustdoc");
    assert_eq!(output.status.code(), Some(1), "trustdoc mutation must fail closed");

    let report = fixture.report();
    assert_eq!(report["status"], "failed");
    assert_eq!(report["proof"]["complete"], false);
    assert!(
        report["stages"][0]["error"]
            .as_str()
            .is_some_and(|error| error.contains("identity changed during self-verification")),
        "trustdoc mutation failure must be explicit: {}",
        report["stages"][0]
    );
    let trustdoc = report["toolchain"]["tools"]
        .as_array()
        .expect("tools")
        .iter()
        .find(|tool| tool["tool"] == "trustdoc")
        .expect("trustdoc");
    assert_eq!(trustdoc["identity_matches_expected"], true);
    assert_eq!(
        trustdoc["snapshot_source"],
        "captured validated bounded endpoint snapshot; no report-time reopen"
    );
}

#[test]
fn verify_self_rejects_stage2_trustd_mutation_during_run() {
    let fixture = Fixture::new("targo-trust-verify-self-trustd-mutation");
    let output = run_full_fixture_mode(&fixture, "mutate-trustd");
    assert_eq!(output.status.code(), Some(1), "trustd mutation must fail closed");

    let report = fixture.report();
    assert_eq!(report["status"], "failed");
    assert_eq!(report["proof"]["complete"], false);
    assert!(
        report["stages"][0]["error"]
            .as_str()
            .is_some_and(|error| error.contains("identity changed during self-verification")),
        "trustd mutation failure must be explicit: {}",
        report["stages"][0]
    );
    let trustd = report["toolchain"]["tools"]
        .as_array()
        .expect("tools")
        .iter()
        .find(|tool| tool["tool"] == "trustd")
        .expect("trustd");
    assert_eq!(trustd["identity_matches_expected"], true);
    assert_eq!(
        trustd["snapshot_source"],
        "captured validated bounded endpoint snapshot; no report-time reopen"
    );
}

#[cfg(unix)]
#[test]
fn verify_self_rejects_same_bytes_stage2_trustdoc_replacement_during_run() {
    let fixture = Fixture::new("targo-trust-verify-self-trustdoc-same-bytes-replacement");
    let output = run_full_fixture_mode(&fixture, "replace-trustdoc-same-bytes");
    assert_eq!(output.status.code(), Some(1), "same-bytes replacement must fail closed");

    let report = fixture.report();
    assert_eq!(report["status"], "failed");
    assert!(
        report["stages"][0]["error"]
            .as_str()
            .is_some_and(|error| error.contains("identity changed during self-verification")),
        "same-byte file-object replacement must be explicit: {}",
        report["stages"][0]
    );
}

#[cfg(unix)]
#[test]
fn verify_self_never_executes_replaced_trustdoc_during_post_stage_recheck() {
    let fixture = Fixture::new("targo-trust-verify-self-trustdoc-replacement-marker");
    fixture.install_stage2_targo();
    let marker = fixture.temp.path().join("replacement-trustdoc-executed");
    let (native_evidence, proof_evidence) = publication_grade_fixture_evidence(&fixture.repo_root);
    let output = Command::new(targo_trust_binary())
        .env(
            "SELF_VERIFY_NATIVE_JSON",
            serde_json::to_string(&native_evidence).expect("serialize native fixture evidence"),
        )
        .env(
            "SELF_VERIFY_PROOF_JSON",
            serde_json::to_string(&proof_evidence).expect("serialize proof fixture evidence"),
        )
        .env("SELF_VERIFY_FAKE_MODE", "replace-trustdoc-probe-marker")
        .env("SELF_VERIFY_REPLACEMENT_PROBE_MARKER", &marker)
        .args([
            "trust",
            "verify",
            "self",
            "--repo-root",
            fixture.repo_str(),
            "--report-dir",
            fixture.report_str(),
            "--timeout",
            FIXTURE_TIMEOUT_SEC,
            "--full-verifier",
        ])
        .output()
        .expect("run replacement-marker self-verification fixture");

    assert_eq!(output.status.code(), Some(1), "replacement must fail closed");
    assert!(!marker.exists(), "post-stage validation executed the replacement trustdoc");
    let report = fixture.report();
    let error = report["stages"][0]["error"].as_str().expect("stage identity error");
    assert!(
        error.contains("refusing to execute any replacement version or protocol identity probe"),
        "{error}"
    );
}

#[test]
fn verify_self_strips_disable_flags_and_preserves_encoded_rustflags() {
    let fixture = Fixture::new("targo-trust-verify-self-env");
    fixture.install_stage2_targo();
    let capture = fixture.temp.path().join("env.txt");
    let encoded_disable = ["-Clink-arg=-z", "-Ztrust-verify=off"].join("\x1f");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "self",
            "--repo-root",
            fixture.repo_str(),
            "--report-dir",
            fixture.report_str(),
            "--timeout",
            FIXTURE_TIMEOUT_SEC,
            "--full-verifier",
        ])
        .env("SELF_VERIFY_FAKE_MODE", "env")
        .env("SELF_VERIFY_CAPTURE", &capture)
        .env("TRUST_VERIFY", "1")
        .env("TRUST_DUMP_ONLY", "1")
        .env("ld_preload", "attacker")
        .env("DyLd_Insert_Libraries", "attacker")
        .env("libpath", "attacker")
        .env("shlib_path", "attacker")
        .env("ldr_preload", "attacker")
        .env("_rld_list", "attacker")
        .env("RUSTFLAGS", "-Cdebuginfo=0 -Z trust-verify=off")
        .env("CARGO_ENCODED_RUSTFLAGS", encoded_disable)
        .env("RUSTC_WRAPPER", "/tmp/forged-rustc-wrapper")
        .env("CARGO_TARGET_TEST_HOST_RUSTFLAGS", "-Ztrust-verify=off")
        .output()
        .expect("run verify self");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "environment capture should succeed while the unbound execution identity remains incomplete\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let captured = fs::read_to_string(&capture).expect("env capture");
    assert!(!captured.lines().any(|line| line == "TRUST_VERIFY=1"), "{captured}");
    assert!(!captured.lines().any(|line| line == "TRUST_DUMP_ONLY=1"), "{captured}");
    assert!(!captured.contains("trust-verify=off"), "{captured}");
    assert!(
        !captured.split_whitespace().any(|word| {
            matches!(word, "trust-verify" | "-Ztrust-verify" | "trust-verify-full")
                || word.starts_with("-Ztrust-verify-full=")
                || word.starts_with("trust-verify-target=")
                || word.starts_with("-Ztrust-verify-target=")
        }),
        "{captured}"
    );
    assert!(captured.contains("-Z trust-verify-output=json"), "{captured}");
    assert!(captured.contains("-Z trust-verify-level=1"), "{captured}");
    assert!(captured.contains("-Z trust-verify-session=self-verify-"), "{captured}");
    assert!(captured.contains("-Clink-arg=-z"), "{captured}");
    assert!(captured.contains('\x1f'), "encoded rustflags should remain encoded");
    for key in
        ["ld_preload", "DyLd_Insert_Libraries", "libpath", "shlib_path", "ldr_preload", "_rld_list"]
    {
        assert!(captured.lines().any(|line| line == format!("{key}=<unset>")), "{key}: {captured}");
    }

    let report = fixture.report();
    assert_eq!(report["stages"][0]["env_policy"]["stripped_no_trust_verify"]["RUSTFLAGS"], true);
    assert_eq!(
        report["stages"][0]["env_policy"]["stripped_no_trust_verify"]["CARGO_ENCODED_RUSTFLAGS"],
        true
    );
    let removed = report["stages"][0]["env_policy"]["removed_toolchain_override_environment"]
        .as_array()
        .expect("removed toolchain overrides");
    assert!(removed.iter().any(|key| key == "RUSTC_WRAPPER"), "{removed:?}");
    assert!(removed.iter().any(|key| key == "CARGO_TARGET_TEST_HOST_RUSTFLAGS"), "{removed:?}");
    for key in
        ["ld_preload", "DyLd_Insert_Libraries", "libpath", "shlib_path", "ldr_preload", "_rld_list"]
    {
        assert!(removed.iter().any(|removed| removed == key), "missing {key}: {removed:?}");
    }
}

#[test]
fn verify_self_rejects_uninspectable_rustc_and_rustdoc_environment_vectors() {
    for (case, variable, value) in [
        ("rustflags-argfile", "RUSTFLAGS", "@policy.args"),
        ("rustdocflags-shell-argfile", "RUSTDOCFLAGS", "@shell:policy.args"),
        ("bootstrap-rustdocflags-argfile", "RUSTDOCFLAGS_BOOTSTRAP", "@policy.args"),
        (
            "encoded-rustflags-separator",
            "CARGO_ENCODED_RUSTFLAGS",
            "-Copt-level=2\x1f--\x1f-Ztrust-verify=off",
        ),
        ("encoded-rustdocflags-argfile", "CARGO_ENCODED_RUSTDOCFLAGS", "@hidden.args"),
    ] {
        let fixture = Fixture::new(&format!("targo-trust-verify-self-{case}"));
        let output = Command::new(targo_trust_binary())
            .args([
                "trust",
                "verify",
                "self",
                "--repo-root",
                fixture.repo_str(),
                "--report-dir",
                fixture.report_str(),
                "--dry-run",
                "--stage-command",
                "sh",
                fixture.stage_str(),
            ])
            .env(variable, value)
            .output()
            .expect("run verify self with uninspectable inherited flags");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(2), "{case}\nstderr:\n{stderr}");
        assert!(stderr.contains(variable), "{case}\nstderr:\n{stderr}");
        assert!(
            stderr.contains("argfile") || stderr.contains("semantic `--` separator"),
            "{case}\nstderr:\n{stderr}"
        );
    }
}

#[test]
fn verify_self_rejects_worker_thread_argument_injection() {
    let fixture = Fixture::new("targo-trust-verify-self-worker-injection");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "self",
            "--repo-root",
            fixture.repo_str(),
            "--report-dir",
            fixture.report_str(),
            "--dry-run",
            "--stage-command",
            "sh",
            fixture.stage_str(),
        ])
        .env("TRUST_VERIFY_WORKER_THREADS", "3 -Z trust-verify=off")
        .output()
        .expect("run verify self with worker-thread injection");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr:\n{stderr}");
    assert!(stderr.contains("TRUST_VERIFY_WORKER_THREADS"), "{stderr}");
    assert!(stderr.contains("1 through 256"), "{stderr}");
}

#[test]
fn verify_self_rejects_flag_like_option_value() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "verify", "self", "--target", "--full-verifier"])
        .output()
        .expect("run verify self with malformed option value");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr:\n{stderr}");
    assert!(stderr.contains("--target requires a value"), "{stderr}");
}

#[test]
fn verify_self_rejects_zero_timeout_before_stage_execution() {
    let fixture = Fixture::new("targo-trust-verify-self-zero-timeout");
    let execution_marker = fixture.temp.path().join("stage-executed");
    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "self",
            "--repo-root",
            fixture.repo_str(),
            "--report-dir",
            fixture.report_str(),
            "--timeout",
            "0",
            "--stage-command",
            "sh",
            fixture.stage_str(),
            "env",
        ])
        .env("SELF_VERIFY_CAPTURE", &execution_marker)
        .output()
        .expect("reject zero self-verification timeout");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr:\n{stderr}");
    assert!(stderr.contains("--timeout requires a finite value greater than zero"), "{stderr}");
    assert!(!execution_marker.exists(), "zero timeout executed the stage command");
    assert!(
        !fixture.report_dir.join("self-verify-harness.report.json").exists(),
        "zero timeout created a self-verification report"
    );
}

struct Fixture {
    temp: TempDir,
    repo_root: PathBuf,
    report_dir: PathBuf,
    stage: PathBuf,
}

impl Fixture {
    fn new(prefix: &str) -> Self {
        let temp = TempDir::new(prefix);
        let repo_root = temp.path().join("repo");
        let report_dir = temp.path().join("report");
        let package_root = repo_root.join("compiler/rustc_middle");
        fs::create_dir_all(package_root.join("src")).expect("create fixture package source");
        fs::write(
            package_root.join("Cargo.toml"),
            "[package]\nname = \"rustc_middle\"\nversion = \"0.0.0\"\nedition = \"2021\"\n\n[lib]\npath = \"src/lib.rs\"\n",
        )
        .expect("write fixture package manifest");
        fs::write(package_root.join("src/lib.rs"), "pub fn fixture() {}\n")
            .expect("write fixture package source");
        initialize_fixture_git(&repo_root);
        write_publication_grade_fixture_evidence(&repo_root);
        let stage = temp.path().join("trust-self-verify");
        fs::write(&stage, fake_stage()).expect("write fake stage");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mut permissions = fs::metadata(&stage).expect("stage metadata").permissions();
            permissions.set_mode(0o755);
            fs::set_permissions(&stage, permissions).expect("mark fake stage executable");
        }
        Self { temp, repo_root, report_dir, stage }
    }

    fn repo_str(&self) -> &str {
        self.repo_root.to_str().expect("repo path should be utf-8")
    }

    fn report_str(&self) -> &str {
        self.report_dir.to_str().expect("report path should be utf-8")
    }

    fn stage_str(&self) -> &str {
        self.stage.to_str().expect("stage path should be utf-8")
    }

    fn install_stage2_targo(&self) -> PathBuf {
        let stage2_targo = install_stage2_file(&self.repo_root, "targo", fake_stage(), true);
        install_stage2_file(
            &self.repo_root,
            "trustc",
            &fake_compiler_version_script("trustc", FIXTURE_VERSION_COMMIT),
            true,
        );
        install_stage2_file(
            &self.repo_root,
            "trustdoc",
            &fake_compiler_version_script("trustdoc", FIXTURE_VERSION_COMMIT),
            true,
        );
        install_matching_stage2_trustd(&self.repo_root);
        write_publication_grade_fixture_evidence(&self.repo_root);
        stage2_targo.canonicalize().expect("canonicalize stage2 targo")
    }

    fn report(&self) -> Value {
        let path = self.report_dir.join("self-verify-harness.report.json");
        serde_json::from_slice(&fs::read(&path).expect("read report")).expect("parse report")
    }
}

fn initialize_fixture_git(repo_root: &Path) {
    run_fixture_git(repo_root, &["init", "-b", "main"]);
    run_fixture_git(repo_root, &["config", "user.email", "self-verify@example.invalid"]);
    run_fixture_git(repo_root, &["config", "user.name", "Self Verify Fixture"]);
    run_fixture_git(repo_root, &["add", "compiler/rustc_middle/Cargo.toml"]);
    run_fixture_git(repo_root, &["add", "compiler/rustc_middle/src/lib.rs"]);
    run_fixture_git(repo_root, &["commit", "-m", "fixture"]);
}

fn fixture_git_head(repo_root: &Path) -> String {
    run_fixture_git(repo_root, &["rev-parse", "HEAD"])
}

fn run_fixture_git(repo_root: &Path, args: &[&str]) -> String {
    let output =
        Command::new("git").args(args).current_dir(repo_root).output().expect("run fixture git");
    assert!(
        output.status.success(),
        "git {args:?} failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("fixture git output UTF-8").trim().to_string()
}

fn install_stage2_file(repo_root: &Path, tool: &str, contents: &str, executable: bool) -> PathBuf {
    let path = repo_root.join("build/host/stage2/bin").join(stage2_file_name(tool));
    fs::create_dir_all(path.parent().expect("stage2 bin parent")).expect("create stage2 bin");
    fs::write(&path, contents).expect("write stage2 tool");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut permissions = fs::metadata(&path).expect("stage2 tool metadata").permissions();
        permissions.set_mode(if executable { 0o755 } else { 0o644 });
        fs::set_permissions(&path, permissions).expect("set stage2 tool permissions");
    }
    let _ = executable;
    path
}

fn stage2_file_name(tool: &str) -> String {
    format!("{tool}{}", std::env::consts::EXE_SUFFIX)
}

fn sha256_text(text: &str) -> String {
    format!("{:x}", Sha256::digest(text.as_bytes()))
}

fn fake_compiler_version_script(tool: &str, commit: &str) -> String {
    format!(
        "#!/bin/sh\n[ \"${{1:-}}\" = \"-Vv\" ] || exit 2\nprintf 'rustc {FIXTURE_VERSION_RELEASE} ({tool})\\nbinary: {tool}\\ncommit-hash: {commit}\\nhost: {FIXTURE_VERSION_HOST}\\nrelease: {FIXTURE_VERSION_RELEASE}\\n'\n"
    )
}

fn install_matching_stage2_trustd(repo_root: &Path) -> PathBuf {
    install_stage2_file(
        repo_root,
        "trustd",
        &fake_trustd_version_and_server_script(FIXTURE_VERSION_COMMIT, FIXTURE_VERSION_RELEASE),
        true,
    )
}

fn fake_trustd_version_and_server_script(commit: &str, release: &str) -> String {
    let python = test_python_interpreter();
    let release = serde_json::to_string(release).expect("quote fake trustd release");
    let commit = serde_json::to_string(commit).expect("quote fake trustd commit");
    let status_version = serde_json::to_string(trust_router::coordinator::STATUS_VERSION)
        .expect("quote fake trustd status version");
    let identity_version = serde_json::to_string(trust_router::coordinator::IDENTITY_VERSION)
        .expect("quote fake trustd identity version");
    r#"#!__PYTHON__
import hashlib
import json
import os
import socket
import sys
import threading
import time

RELEASE = __RELEASE__
COMMIT = __COMMIT__
STATUS_VERSION = __STATUS_VERSION__
IDENTITY_VERSION = __IDENTITY_VERSION__

if sys.argv[1:] == ["--version"]:
    print(f"trustd {RELEASE}")
    print("trust.identity=trustd")
    print(f"trust.protocol={STATUS_VERSION}")
    print(f"commit-hash: {COMMIT}")
    raise SystemExit(0)

if len(sys.argv) != 3 or sys.argv[1] != "--socket" or not sys.argv[2]:
    raise SystemExit(2)

with open(sys.argv[0], "rb") as executable:
    executable_sha256 = hashlib.sha256(executable.read()).hexdigest()
identity = {
    "version": IDENTITY_VERSION,
    "protocol": STATUS_VERSION,
    "release": RELEASE,
    "commit": COMMIT,
    "executable_sha256": executable_sha256,
}
state_lock = threading.Lock()
state = {
    "budget_bytes": 1024,
    "reserved_bytes": 0,
    "granted_total": 0,
    "released_total": 0,
    "started_at": max(1, int(time.time())),
    "next_token": 1,
    "active": [],
}

def status_snapshot():
    return {
        "version": STATUS_VERSION,
        "budget_bytes": state["budget_bytes"],
        "reserved_bytes": state["reserved_bytes"],
        "free_bytes": state["budget_bytes"] - state["reserved_bytes"],
        "queue_depth": 0,
        "granted_total": state["granted_total"],
        "released_total": state["released_total"],
        "started_at": state["started_at"],
        "active": [dict(entry) for entry in state["active"]],
    }

def handle(connection):
    with connection:
        stream = connection.makefile("rwb", buffering=0)
        for raw in stream:
            request = raw.decode("utf-8").rstrip("\r\n")
            if request == "PING":
                response = "PONG"
            elif request == "IDENTITY":
                response = json.dumps(identity, separators=(",", ":"))
            elif request == "STATUS":
                with state_lock:
                    response = json.dumps(status_snapshot(), separators=(",", ":"))
            elif request.startswith("RESERVE "):
                parts = request.split(" ", 3)
                if len(parts) != 4:
                    response = "ERR malformed"
                else:
                    byte_count = int(parts[1])
                    pid = int(parts[2])
                    label = parts[3]
                    with state_lock:
                        if byte_count <= 0 or state["reserved_bytes"] + byte_count > state["budget_bytes"]:
                            response = "DEGRADED"
                        else:
                            token = state["next_token"]
                            state["next_token"] += 1
                            state["reserved_bytes"] += byte_count
                            state["granted_total"] += 1
                            state["active"].append({
                                "pid": pid,
                                "bytes": byte_count,
                                "label": label,
                                "since_secs": 0,
                                "token": token,
                            })
                            response = f"GRANTED {token}"
            elif request.startswith("RELEASE "):
                token = int(request.split(" ", 1)[1])
                with state_lock:
                    released = next(
                        (entry for entry in state["active"] if entry["token"] == token),
                        None,
                    )
                    if released is not None:
                        state["active"].remove(released)
                        state["reserved_bytes"] -= released["bytes"]
                        state["released_total"] += 1
                response = "OK"
            else:
                response = "ERR unsupported"
            stream.write(response.encode("utf-8") + b"\n")

listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
try:
    os.unlink(sys.argv[2])
except FileNotFoundError:
    pass
listener.bind(sys.argv[2])
os.chmod(sys.argv[2], 0o600)
listener.listen(8)
while True:
    connection, _ = listener.accept()
    threading.Thread(target=handle, args=(connection,), daemon=True).start()
"#
    .replace("__PYTHON__", &python)
    .replace("__RELEASE__", &release)
    .replace("__COMMIT__", &commit)
    .replace("__STATUS_VERSION__", &status_version)
    .replace("__IDENTITY_VERSION__", &identity_version)
}

fn test_python_interpreter() -> String {
    static PYTHON: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    PYTHON
        .get_or_init(|| {
            let output = Command::new("python3")
                .args(["-c", "import os,sys; print(os.path.realpath(sys.executable))"])
                .output()
                .expect("locate Python 3 for the fake trustd endpoint");
            assert!(output.status.success(), "Python 3 discovery failed");
            let path = String::from_utf8(output.stdout).expect("Python path is UTF-8");
            let path = path.trim();
            assert!(path.starts_with('/'), "Python path is not absolute: {path}");
            assert!(
                !path.chars().any(|character| matches!(character, '\n' | '\r')),
                "Python path contains a newline"
            );
            path.to_string()
        })
        .clone()
}

const FIXTURE_BINDING_ENVELOPE_MAGIC: &[u8] = b"trust.evidence-artifact-binding-envelope.v1\0";

fn write_publication_grade_fixture_evidence(repo_root: &Path) {
    let (native_evidence, proof_evidence) = publication_grade_fixture_evidence(repo_root);
    fs::write(
        repo_root.join(".self-verify-native-fixture.json"),
        serde_json::to_vec(&native_evidence).expect("serialize native fixture evidence"),
    )
    .expect("write native fixture evidence");
    fs::write(
        repo_root.join(".self-verify-proof-fixture.json"),
        serde_json::to_vec(&proof_evidence).expect("serialize proof fixture evidence"),
    )
    .expect("write proof fixture evidence");
}

fn publication_grade_fixture_evidence(
    repo_root: &Path,
) -> (TransportNativeTrustIrEvidence, TransportProofEvidence) {
    const SUITE: &str = "trust-wp";
    const REQUEST_ID: &str = "1";
    const PROOF_ID: &str = "1";
    const OBLIGATION_ID: &str = "self-verify-obligation-1";
    const NATIVE_ID: &str = "trust_ir-native-trust-wp-request-1-proof-1";

    let native_artifacts = native_fixture_artifacts(SUITE, REQUEST_ID, PROOF_ID, NATIVE_ID);
    let native = TransportNativeTrustIrEvidence {
        suite: SUITE.to_string(),
        backend: SUITE.to_string(),
        request_id: Some(REQUEST_ID.to_string()),
        native_id: Some(NATIVE_ID.to_string()),
        present: true,
        artifacts: native_artifacts.clone(),
        diagnostics: Vec::new(),
    };

    let structural_input = bound_fixture_artifact(
        repo_root,
        "NormalizedObligation",
        b"exact normalized self-verification input",
        NATIVE_ID,
        OBLIGATION_ID,
        Vec::new(),
        false,
    );
    let transcript = bound_fixture_artifact(
        repo_root,
        "SolverTranscript",
        b"exact self-verification solver transcript",
        NATIVE_ID,
        OBLIGATION_ID,
        vec![fixture_artifact_reference(&structural_input)],
        true,
    );
    let check = bound_fixture_artifact(
        repo_root,
        "ProofCheckReport",
        b"exact self-verification proof-check report",
        NATIVE_ID,
        OBLIGATION_ID,
        vec![fixture_artifact_reference(&transcript)],
        true,
    );
    let mut artifacts = vec![structural_input, transcript, check];
    artifacts.extend(native_artifacts);

    let strength = ProofStrength::deductive();
    let proof = TransportProofEvidence {
        suite: SUITE.to_string(),
        backend: SUITE.to_string(),
        request_id: Some(REQUEST_ID.to_string()),
        proof_id: Some(PROOF_ID.to_string()),
        native_id: Some(NATIVE_ID.to_string()),
        status: TransportProofStatus::Proved,
        strength: Some(strength.clone()),
        evidence: Some(ProofEvidence::from(strength)),
        artifacts,
        diagnostics: Vec::new(),
    };
    (native, proof)
}

fn fixture_artifact_reference(artifact: &TransportEvidenceArtifact) -> TransportArtifactReference {
    TransportArtifactReference {
        kind: artifact.kind.clone(),
        digest: artifact.digest.clone().expect("fixture artifact digest"),
    }
}

fn bound_fixture_artifact(
    repo_root: &Path,
    kind: &str,
    payload: &[u8],
    binding: &str,
    owner: &str,
    mut references: Vec<TransportArtifactReference>,
    path_backed: bool,
) -> TransportEvidenceArtifact {
    references.sort();
    let mut bytes = FIXTURE_BINDING_ENVELOPE_MAGIC.to_vec();
    push_fixture_binding_field(&mut bytes, kind.as_bytes());
    push_fixture_binding_field(&mut bytes, owner.as_bytes());
    push_fixture_binding_field(&mut bytes, binding.as_bytes());
    bytes.extend_from_slice(&(references.len() as u32).to_be_bytes());
    for reference in &references {
        push_fixture_binding_field(&mut bytes, reference.kind.as_bytes());
        push_fixture_binding_field(&mut bytes, reference.digest.algorithm.as_bytes());
        push_fixture_binding_field(&mut bytes, reference.digest.value.as_bytes());
    }
    bytes.extend_from_slice(&(payload.len() as u64).to_be_bytes());
    bytes.extend_from_slice(payload);

    let digest = fixture_digest(&bytes);
    let mut materialization =
        TransportArtifactMaterialization::from_exact_bytes(&bytes, binding, references)
            .expect("valid fixture proof materialization");
    if path_backed {
        let store = repo_root.join(TRANSPORT_ARTIFACT_STORE_DIRECTORY).join("sha256");
        fs::create_dir_all(&store).expect("create fixture proof store");
        fs::write(store.join(&digest.value), &bytes).expect("write fixture proof artifact");
        materialization = materialization
            .with_materialized_path(format!(
                "{TRANSPORT_ARTIFACT_STORE_DIRECTORY}/sha256/{}",
                digest.value
            ))
            .expect("valid fixture proof-store path");
    }
    TransportEvidenceArtifact {
        kind: kind.to_string(),
        format: Some("binary".to_string()),
        artifact_id: Some(kind.to_string()),
        digest: Some(digest.clone()),
        uri: Some(format!("artifact://self-verify/{kind}/{}", digest.value)),
        materialization: Some(materialization),
        metadata: None,
    }
}

fn push_fixture_binding_field(bytes: &mut Vec<u8>, value: &[u8]) {
    bytes.extend_from_slice(&(value.len() as u32).to_be_bytes());
    bytes.extend_from_slice(value);
}

fn native_fixture_artifacts(
    suite: &str,
    request_id: &str,
    proof_id: &str,
    native_id: &str,
) -> Vec<TransportEvidenceArtifact> {
    let bundle = native_fixture_materialization(
        "bundle",
        None,
        None,
        None,
        serde_json::json!({"bundle": "exact"}),
        native_id,
        Vec::new(),
    );
    let bundle_uri = format!("trust_ir-native://verification-bundle/{}", bundle.1.value);
    let request = native_fixture_materialization(
        "request",
        Some(suite),
        Some(request_id),
        None,
        serde_json::json!({"request": "exact"}),
        native_id,
        vec![TransportArtifactReference {
            kind: "EngineInput".to_string(),
            digest: bundle.1.clone(),
        }],
    );
    let request_digest = request.1.value.clone();
    let normalized = native_fixture_materialization(
        "normalized_obligation",
        Some(suite),
        Some(request_id),
        Some(proof_id),
        serde_json::json!({"obligation": "exact"}),
        native_id,
        vec![TransportArtifactReference {
            kind: "EngineInput".to_string(),
            digest: request.1.clone(),
        }],
    );
    vec![
        native_fixture_artifact("EngineInput", bundle, bundle_uri.clone()),
        native_fixture_artifact(
            "EngineInput",
            request,
            format!("{bundle_uri}/{suite}/request/{request_id}/{request_digest}"),
        ),
        native_fixture_artifact(
            "NormalizedObligation",
            normalized.clone(),
            format!(
                "{bundle_uri}/{suite}/request/{request_id}/{request_digest}/proof/{proof_id}/{}",
                normalized.1.value
            ),
        ),
    ]
}

fn native_fixture_materialization(
    role: &str,
    suite: Option<&str>,
    request_id: Option<&str>,
    proof_id: Option<&str>,
    payload: Value,
    native_id: &str,
    references: Vec<TransportArtifactReference>,
) -> (TransportArtifactMaterialization, TransportArtifactDigest) {
    let mut value = serde_json::json!({
        "schema": NATIVE_TRUST_IR_MATERIALIZATION_SCHEMA,
        "role": role,
        "suite": suite,
        "request_id": request_id,
        "proof_id": proof_id,
        "payload": payload,
    });
    canonicalize_fixture_json(&mut value);
    let bytes = serde_json::to_vec(&value).expect("serialize native fixture materialization");
    let digest = fixture_digest(&bytes);
    let materialization =
        TransportArtifactMaterialization::from_exact_bytes(&bytes, native_id, references)
            .expect("valid native fixture materialization");
    (materialization, digest)
}

fn native_fixture_artifact(
    kind: &str,
    materialized: (TransportArtifactMaterialization, TransportArtifactDigest),
    uri: String,
) -> TransportEvidenceArtifact {
    TransportEvidenceArtifact {
        kind: kind.to_string(),
        format: Some("trust_ir-json".to_string()),
        artifact_id: None,
        digest: Some(materialized.1),
        uri: Some(uri),
        materialization: Some(materialized.0),
        metadata: None,
    }
}

fn fixture_digest(bytes: &[u8]) -> TransportArtifactDigest {
    TransportArtifactDigest {
        algorithm: "sha256".to_string(),
        value: format!("{:x}", Sha256::digest(bytes)),
    }
}

fn canonicalize_fixture_json(value: &mut Value) {
    match value {
        Value::Array(values) => values.iter_mut().for_each(canonicalize_fixture_json),
        Value::Object(object) => {
            let mut entries = std::mem::take(object).into_iter().collect::<Vec<_>>();
            entries.sort_by(|left, right| left.0.cmp(&right.0));
            for (key, mut value) in entries {
                canonicalize_fixture_json(&mut value);
                object.insert(key, value);
            }
        }
        _ => {}
    }
}

fn run_full_fixture_mode(fixture: &Fixture, mode: &str) -> std::process::Output {
    fixture.install_stage2_targo();
    let (native_evidence, proof_evidence) = publication_grade_fixture_evidence(&fixture.repo_root);
    Command::new(targo_trust_binary())
        .env(
            "SELF_VERIFY_NATIVE_JSON",
            serde_json::to_string(&native_evidence).expect("serialize native fixture evidence"),
        )
        .env(
            "SELF_VERIFY_PROOF_JSON",
            serde_json::to_string(&proof_evidence).expect("serialize proof fixture evidence"),
        )
        .args([
            "trust",
            "verify",
            "self",
            "--repo-root",
            fixture.repo_str(),
            "--report-dir",
            fixture.report_str(),
            "--timeout",
            FIXTURE_TIMEOUT_SEC,
            "--full-verifier",
        ])
        .env("SELF_VERIFY_FAKE_MODE", mode)
        .output()
        .expect("run full self-verification fixture")
}

fn run_full_dry_run(fixture: &Fixture) -> std::process::Output {
    Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "self",
            "--repo-root",
            fixture.repo_str(),
            "--report-dir",
            fixture.report_str(),
            "--full-verifier",
            "--dry-run",
        ])
        .output()
        .expect("run dry-run full self-verification fixture")
}

fn fake_stage() -> &'static str {
    r#"#!/bin/sh
if [ "${1:-}" = "-Vv" ]; then
  printf 'targo 1.99.0-test\nrelease: 1.99.0-test\ncommit-hash: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\nhost: test-host\n'
  exit 0
fi
if [ -n "${SELF_VERIFY_EXECUTION_MARKER:-}" ]; then
  printf 'executed\n' > "$SELF_VERIFY_EXECUTION_MARKER"
fi
mode="${1:-native-proved}"
if [ "$mode" = "build" ]; then
  mode="${SELF_VERIFY_FAKE_MODE:-native-proved}"
fi

repo="$(pwd -P)"
package_id="path+file://$repo/compiler/rustc_middle#rustc_middle@0.0.0"
src_path="$repo/compiler/rustc_middle/src/lib.rs"
compile_target="test-host"
compile_mode="build"
compile_kind="target"
unit_identity_sha256="cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
diagnostic_code="trust_verification_transport_v1"
unit_semantics='{"schema":"targo.trust-unit-semantics.v1","features":[],"target_cfg":["unix"],"cfg_test":false,"target_edition":"2024","target_crate_types":["rlib"],"target_harness":false,"target_proc_macro":false,"profile":{"opt_level":"0","requested_lto":"false","effective_lto":"only-object","debuginfo":"0","debug_assertions":false,"overflow_checks":false,"rpath":false,"incremental":false,"panic":"unwind","strip":"none","rustflags":[]},"compiler":{"frontend":"rustc","codegen_backend":"trust-cg","rustc_release":"1.99.0-nightly","rustc_host":"test-host","rustc_verbose_version_sha256":"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"},"unit_rustflags":["-Zcodegen-backend=trust-cg"],"manifest_lint_rustflags":[],"extra_compiler_args":[]}'
semantics_sha256="67fbdb2e7e098b6c27117b599ec42fc343d9b18b8a040b3f570e03e6da417f94"
proof_unit="{\"schema\":\"targo.trust-proof-unit.v2\",\"index\":0,\"mode\":\"build\",\"role\":\"primary\",\"package_name\":\"rustc_middle\",\"semantics_sha256\":\"$semantics_sha256\"}"
session="$(printf '%s\n' "$RUSTFLAGS" | sed -n 's/.*trust-verify-session=\([^ ]*\).*/\1/p' | tail -n 1)"
proof_root="$(printf '%s\n' "$RUSTFLAGS" | sed -n 's/.*trust-proof-artifact-root=\([^ ]*\).*/\1/p' | tail -n 1)"
function_session="$session"
coverage_session="$session"
terminal_session="$session"
solver_path="target/trust/proofs/solver-transcript.smt2"
solver_digest="f4b4de64f1186a4b57577700a8f1219b7b6b1680d3ebb0e7ec7739f8df009717"
check_path="target/trust/proofs/proof-check.json"
check_digest="5050381c76fe3ad455174df3ade39c8ce8d384e6ffdf9e5c818350b6dfc3cedf"

if [ -n "$proof_root" ] && [ -d "$repo/.trust-proof-artifacts/sha256" ]; then
  mkdir -p "$proof_root/.trust-proof-artifacts/sha256"
  cp "$repo/.trust-proof-artifacts/sha256/"* "$proof_root/.trust-proof-artifacts/sha256/"
fi

emit_compiler_message() {
  payload="$1"
  escaped_payload="$(printf '%s' "$payload" | sed 's/"/\\"/g')"
  printf '%s\n' "{\"reason\":\"compiler-message\",\"package_id\":\"$package_id\",\"target\":{\"kind\":[\"lib\"],\"name\":\"rustc_middle\",\"src_path\":\"$src_path\"},\"trust_compile_target\":\"$compile_target\",\"trust_compile_mode\":\"$compile_mode\",\"trust_compile_kind\":\"$compile_kind\",\"trust_unit_identity_sha256\":\"$unit_identity_sha256\",\"trust_proof_unit\":$proof_unit,\"message\":{\"message\":\"TRUST_JSON:$escaped_payload\",\"code\":{\"code\":\"$diagnostic_code\"},\"level\":\"note\",\"rendered\":null}}"
}

emit_artifact() {
  printf '%s\n' "{\"reason\":\"compiler-artifact\",\"package_id\":\"$package_id\",\"target\":{\"kind\":[\"lib\"],\"name\":\"rustc_middle\",\"src_path\":\"$src_path\"},\"trust_compile_target\":\"$compile_target\",\"trust_compile_mode\":\"$compile_mode\",\"trust_compile_kind\":\"$compile_kind\",\"trust_unit_identity_sha256\":\"$unit_identity_sha256\",\"trust_proof_unit\":$proof_unit,\"profile\":{\"opt_level\":\"0\",\"debuginfo\":0,\"debug_assertions\":false,\"overflow_checks\":false,\"test\":false},\"features\":[],\"fresh\":false}"
}

emit_inventory() {
  printf '%s\n' "{\"reason\":\"trust-proof-inventory\",\"schema\":\"targo.trust-proof-inventory.v2\",\"include_dependencies\":true,\"units\":[{\"trust_proof_unit\":$proof_unit,\"semantics\":$unit_semantics,\"package_id\":\"$package_id\",\"target_name\":\"rustc_middle\",\"target_kinds\":[\"lib\"],\"compile_target\":\"$compile_target\",\"trust_compile_mode\":\"$compile_mode\",\"trust_compile_kind\":\"$compile_kind\",\"trust_unit_identity_sha256\":\"$unit_identity_sha256\"}],\"excluded_units\":[]}"
}

emit_build_finished() {
  printf '%s\n' '{"reason":"build-finished","success":true}'
}

if [ "$mode" = "env" ]; then
  {
    printf '%s\n' "$RUSTFLAGS"
    printf '%s\n' "$CARGO_ENCODED_RUSTFLAGS"
    printf 'ld_preload=%s\n' "${ld_preload-<unset>}"
    printf 'DyLd_Insert_Libraries=%s\n' "${DyLd_Insert_Libraries-<unset>}"
    printf 'libpath=%s\n' "${libpath-<unset>}"
    printf 'shlib_path=%s\n' "${shlib_path-<unset>}"
    printf 'ldr_preload=%s\n' "${ldr_preload-<unset>}"
    printf '_rld_list=%s\n' "${_rld_list-<unset>}"
  } > "$SELF_VERIFY_CAPTURE"
fi

emit_inventory

if [ "$mode" = "no-transport" ]; then
  emit_artifact
  emit_build_finished
  exit 0
fi

outcome="proved"
evidence_mode="materialized"
coverage_eligible=1
coverage_processed=1
emit_terminal=yes
case "$mode" in
  outcome)
    outcome="${SELF_VERIFY_FAKE_OUTCOME:-${2:-unknown}}"
    ;;
  no-proof-binding)
    evidence_mode="missing"
    ;;
  string-only-proof-binding)
    evidence_mode="string-only"
    ;;
  mismatched-digest)
    evidence_mode="mismatched"
    ;;
  identity-mismatch|backend-mismatch|native-wrong-kind|native-wrong-uri|weak-strength|missing-replay|wrong-artifact-kind|error-diagnostic|cross-artifact|uri-only|metadata-only)
    evidence_mode="$mode"
    ;;
  incomplete-coverage)
    coverage_processed=0
    ;;
  zero-coverage)
    coverage_eligible=0
    coverage_processed=0
    ;;
  no-terminal-summary)
    emit_terminal=no
    ;;
  wrong-session)
    function_session="attacker-controlled-session"
    coverage_session="attacker-controlled-session"
    terminal_session="attacker-controlled-session"
    ;;
  stale-function-session)
    function_session="stale-function-session"
    ;;
  stale-terminal-session)
    terminal_session="stale-terminal-session"
    ;;
  bad-diagnostic-tag)
    diagnostic_code="forged_user_diagnostic"
    ;;
esac

mkdir -p "target/trust/proofs"
printf '%s\n' '{"kind":"solver-transcript","proved":true}' > "$solver_path"
printf '%s\n' '{"kind":"proof-check","accepted":true}' > "$check_path"

request_id="1"
native_id="trust_ir-native-trust-wp-request-1-proof-1"
proof_native_id="$native_id"
native_backend="trust-full-verifier"
native_bundle_digest="dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
native_request_digest="eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee"
native_bundle_uri="trust_ir-native://verification-bundle/$native_bundle_digest"
native_artifacts="[{\"kind\":\"EngineInput\",\"digest\":{\"algorithm\":\"trust_ir-stable-v1\",\"value\":\"$native_bundle_digest\"},\"uri\":\"$native_bundle_uri\"},{\"kind\":\"EngineInput\",\"digest\":{\"algorithm\":\"trust_ir-stable-v1\",\"value\":\"$native_request_digest\"},\"uri\":\"$native_bundle_uri/trust-wp/request/$request_id\"},{\"kind\":\"NormalizedObligation\",\"digest\":{\"algorithm\":\"trust_ir-stable-v1\",\"value\":\"$native_request_digest\"},\"uri\":\"$native_bundle_uri/trust-wp/request/$request_id/proof/1\"}]"
solver_uri="$solver_path"
check_uri="$check_path"
solver_declared_digest="$solver_digest"
check_declared_digest="$check_digest"
proof_strength='{"reasoning":"Deductive","assurance":"Sound"}'
proof_assurance='{"reasoning":"Deductive","assurance":"SmtBacked"}'
proof_diagnostics='[]'
proof_artifacts="[{\"kind\":\"SolverTranscript\",\"digest\":{\"algorithm\":\"sha256\",\"value\":\"$solver_declared_digest\"},\"uri\":\"$solver_uri\"},{\"kind\":\"ProofCheckReport\",\"digest\":{\"algorithm\":\"sha256\",\"value\":\"$check_declared_digest\"},\"uri\":\"$check_uri\"}]"
case "$evidence_mode" in
  missing)
    proof_evidence='{"suite":"trust-wp","backend":"trust-full-verifier","status":"proved"}'
    ;;
  string-only)
    solver_uri='artifact://trust-wp/solver-transcript'
    check_uri='artifact://trust-wp/proof-check'
    proof_artifacts="[{\"kind\":\"SolverTranscript\",\"digest\":{\"algorithm\":\"sha256\",\"value\":\"$solver_digest\"},\"uri\":\"$solver_uri\"},{\"kind\":\"ProofCheckReport\",\"digest\":{\"algorithm\":\"sha256\",\"value\":\"$check_digest\"},\"uri\":\"$check_uri\"},{\"kind\":\"clean_cic\",\"metadata\":{\"artifact_digest\":\"sha256:$solver_digest\",\"artifact_path\":\"$solver_path\"}}]"
    ;;
  mismatched)
    solver_declared_digest="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    proof_artifacts="[{\"kind\":\"SolverTranscript\",\"digest\":{\"algorithm\":\"sha256\",\"value\":\"$solver_declared_digest\"},\"uri\":\"$solver_uri\"},{\"kind\":\"ProofCheckReport\",\"digest\":{\"algorithm\":\"sha256\",\"value\":\"$check_digest\"},\"uri\":\"$check_uri\"}]"
    ;;
  identity-mismatch)
    proof_native_id="attacker-native-id"
    ;;
  backend-mismatch)
    native_backend="attacker-backend"
    ;;
  native-wrong-kind)
    native_artifacts="[{\"kind\":\"EngineInput\",\"digest\":{\"algorithm\":\"trust_ir-stable-v1\",\"value\":\"$native_bundle_digest\"},\"uri\":\"$native_bundle_uri\"},{\"kind\":\"EngineInput\",\"digest\":{\"algorithm\":\"trust_ir-stable-v1\",\"value\":\"$native_request_digest\"},\"uri\":\"$native_bundle_uri/trust-wp/request/$request_id\"},{\"kind\":\"banana\",\"digest\":{\"algorithm\":\"trust_ir-stable-v1\",\"value\":\"$native_request_digest\"},\"uri\":\"$native_bundle_uri/trust-wp/request/$request_id/proof/1\"}]"
    ;;
  native-wrong-uri)
    native_artifacts="[{\"kind\":\"EngineInput\",\"digest\":{\"algorithm\":\"trust_ir-stable-v1\",\"value\":\"$native_bundle_digest\"},\"uri\":\"$native_bundle_uri\"},{\"kind\":\"EngineInput\",\"digest\":{\"algorithm\":\"trust_ir-stable-v1\",\"value\":\"$native_request_digest\"},\"uri\":\"$native_bundle_uri/trust-wp/request/attacker\"},{\"kind\":\"NormalizedObligation\",\"digest\":{\"algorithm\":\"trust_ir-stable-v1\",\"value\":\"$native_request_digest\"},\"uri\":\"$native_bundle_uri/trust-wp/request/attacker/proof/1\"}]"
    ;;
  weak-strength)
    proof_assurance='{"reasoning":"Deductive","assurance":"Unchecked"}'
    ;;
  missing-replay)
    proof_artifacts="[{\"kind\":\"SolverTranscript\",\"digest\":{\"algorithm\":\"sha256\",\"value\":\"$solver_digest\"},\"uri\":\"$solver_uri\"}]"
    ;;
  wrong-artifact-kind)
    proof_artifacts="[{\"kind\":\"SolverTranscript\",\"digest\":{\"algorithm\":\"sha256\",\"value\":\"$solver_digest\"},\"uri\":\"$solver_uri\"},{\"kind\":\"proof\",\"digest\":{\"algorithm\":\"sha256\",\"value\":\"$check_digest\"},\"uri\":\"$check_uri\"}]"
    ;;
  error-diagnostic)
    proof_diagnostics='[{"code":"proof.rejected","severity":"error","message":"proof checker rejected evidence"}]'
    ;;
  cross-artifact)
    proof_artifacts="[{\"kind\":\"SolverTranscript\",\"digest\":{\"algorithm\":\"sha256\",\"value\":\"$check_digest\"},\"uri\":\"$solver_uri\"},{\"kind\":\"ProofCheckReport\",\"digest\":{\"algorithm\":\"sha256\",\"value\":\"$solver_digest\"},\"uri\":\"$check_uri\"}]"
    ;;
  uri-only)
    proof_artifacts="[{\"kind\":\"SolverTranscript\",\"digest\":{\"algorithm\":\"sha256\",\"value\":\"$solver_digest\"},\"uri\":\"artifact://trust-wp/solver-transcript\"},{\"kind\":\"ProofCheckReport\",\"digest\":{\"algorithm\":\"sha256\",\"value\":\"$check_digest\"},\"uri\":\"artifact://trust-wp/proof-check\"}]"
    ;;
  metadata-only)
    proof_artifacts='[{"kind":"SolverTranscript","digest":{"algorithm":"sha256","value":"2f92c544693c749e38d49de497b5b54eebcce349b4defcf5e716a5703b2b1816"},"uri":"artifact://trust-wp/solver-transcript","metadata":"solver metadata"},{"kind":"ProofCheckReport","digest":{"algorithm":"sha256","value":"a31f9a85de1bf6b0d75e31e76fdd500f7e864ad0187d90f58fc9435d892ea680"},"uri":"artifact://trust-wp/proof-check","metadata":"check metadata"}]'
    ;;
esac

native_trust_ir="{\"suite\":\"trust-wp\",\"backend\":\"$native_backend\",\"request_id\":\"$request_id\",\"native_id\":\"$native_id\",\"present\":true,\"artifacts\":$native_artifacts}"
if [ "$evidence_mode" = "materialized" ]; then
  if [ -n "${SELF_VERIFY_NATIVE_JSON:-}" ] && [ -n "${SELF_VERIFY_PROOF_JSON:-}" ]; then
    native_trust_ir="$SELF_VERIFY_NATIVE_JSON"
    proof_evidence="$SELF_VERIFY_PROOF_JSON"
  else
    native_trust_ir="$(cat "$repo/.self-verify-native-fixture.json")"
    proof_evidence="$(cat "$repo/.self-verify-proof-fixture.json")"
  fi
elif [ "$evidence_mode" != "missing" ]; then
  proof_evidence="{\"suite\":\"trust-wp\",\"backend\":\"trust-full-verifier\",\"request_id\":\"$request_id\",\"proof_id\":\"self-verify-proof-1\",\"native_id\":\"$proof_native_id\",\"status\":\"proved\",\"strength\":$proof_strength,\"evidence\":$proof_assurance,\"artifacts\":$proof_artifacts,\"diagnostics\":$proof_diagnostics}"
fi

proved=0
failed=0
unknown=0
timed_out=0
skipped=0
runtime_checked=0
functions_verified=0
case "$outcome" in
  proved)
    proved=1
    functions_verified=1
    ;;
  failed)
    failed=1
    ;;
  timeout|timed_out)
    unknown=1
    timed_out=1
    ;;
  skipped)
    unknown=1
    skipped=1
    ;;
  runtime_checked)
    runtime_checked=1
    ;;
  *)
    unknown=1
    ;;
esac

function_result="$(printf '%s' "{\"type\":\"function_result\",\"function\":\"rustc_middle::fixture::ok\",\"package_name\":\"rustc_middle\",\"crate_name\":\"rustc_middle\",\"primary_package\":true,\"verification_session\":\"$function_session\",\"results\":[{\"obligation_id\":\"self-verify-obligation-1\",\"kind\":\"self-build\",\"description\":\"native proof\",\"outcome\":\"$outcome\",\"solver\":\"trust-full-verifier\",\"time_ms\":1,\"native_trust_ir\":$native_trust_ir,\"proof_evidence\":$proof_evidence}],\"proved\":$proved,\"failed\":$failed,\"unknown\":$unknown,\"timed_out\":$timed_out,\"skipped\":$skipped,\"runtime_checked\":$runtime_checked,\"cached\":0,\"total\":1}")"
coverage_eligible_functions='[]'
coverage_processed_functions='[]'
if [ "$coverage_eligible" -eq 1 ]; then
  coverage_eligible_functions='["rustc_middle::fixture::ok"]'
fi
if [ "$coverage_processed" -eq 1 ]; then
  coverage_processed_functions='["rustc_middle::fixture::ok"]'
fi
coverage_summary="$(printf '%s' "{\"type\":\"coverage_summary\",\"crate_name\":\"rustc_middle\",\"package_name\":\"rustc_middle\",\"primary_package\":true,\"verification_session\":\"$coverage_session\",\"eligible\":$coverage_eligible,\"processed\":$coverage_processed,\"function_identities\":{\"schema\":\"trustc.coverage-function-identities.v1\",\"eligible_functions\":$coverage_eligible_functions,\"processed_functions\":$coverage_processed_functions}}")"
crate_summary="$(printf '%s' "{\"type\":\"crate_summary\",\"crate_name\":\"rustc_middle\",\"package_name\":\"rustc_middle\",\"primary_package\":true,\"verification_session\":\"$terminal_session\",\"functions_analyzed\":1,\"functions_verified\":$functions_verified,\"total_proved\":$proved,\"total_failed\":$failed,\"total_unknown\":$unknown,\"total_timed_out\":$timed_out,\"total_skipped\":$skipped,\"total_runtime_checked\":$runtime_checked,\"total_obligations\":1}")"

emit_compiler_message "$function_result"
emit_compiler_message "$coverage_summary"
if [ "$emit_terminal" = yes ]; then
  emit_compiler_message "$crate_summary"
fi
emit_artifact

case "$mode" in
  stderr-forgery)
    printf '%s\n' 'TRUST_JSON:{"type":"function_result","function":"forged::failure","results":[{"outcome":"failed"}]}' >&2
    ;;
  stdout-forgery)
    printf '%s\n' 'TRUST_JSON:{"type":"function_result","function":"forged::proof","results":[{"outcome":"proved"}]}'
    ;;
  build-script-forgery)
    printf '%s\n' '{"reason":"build-script-executed","package_id":"forged-build-script 0.0.0","linked_libs":[],"linked_paths":[],"cfgs":[],"env":[["TRUST_JSON","forged-proof"]],"out_dir":"target/forged"}'
    printf '%s\n' 'TRUST_JSON:{"type":"function_result","function":"build_script::forged","results":[{"outcome":"failed"}]}' >&2
    ;;
  mutate-trustc)
    printf '%s\n' '# changed during verification' >> "$TRUST_TRUSTC_BIN"
    ;;
  mutate-trustdoc)
    printf '%s\n' '# changed during verification' >> "$TRUST_TRUSTDOC_BIN"
    ;;
  mutate-trustd)
    printf '%s\n' '# changed during verification' >> "$TRUST_TRUSTD_BIN"
    ;;
  replace-trustdoc-same-bytes)
    replacement="${TRUST_TRUSTDOC_BIN}.replacement"
    /bin/cp "$TRUST_TRUSTDOC_BIN" "$replacement"
    /bin/chmod 755 "$replacement"
    /bin/mv "$replacement" "$TRUST_TRUSTDOC_BIN"
    ;;
  replace-trustdoc-probe-marker)
    replacement="${TRUST_TRUSTDOC_BIN}.replacement"
    {
      printf '#!/bin/sh\n'
      printf 'printf executed > "%s"\n' "$SELF_VERIFY_REPLACEMENT_PROBE_MARKER"
      printf "printf 'trustdoc replacement\\ncommit-hash: 1111111111111111111111111111111111111111\\n'\n"
    } > "$replacement"
    /bin/chmod 755 "$replacement"
    /bin/mv "$replacement" "$TRUST_TRUSTDOC_BIN"
    ;;
esac
emit_build_finished
"#
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

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(prefix: &str) -> Self {
        let unique = format!(
            "{}-{}-{}",
            prefix,
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("system time")
                .as_nanos()
        );
        let path = std::env::temp_dir().join(unique);
        fs::create_dir_all(&path).expect("create temp dir");
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
