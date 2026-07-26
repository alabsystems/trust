use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

#[test]
fn verify_examples_help_is_rust_owned() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "verify", "examples", "--help"])
        .output()
        .expect("run verify examples help");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "help should succeed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("targo trust verify examples"));
    assert!(stdout.contains("--metadata-only"));
    assert!(stdout.contains("--trustc"));
    assert!(stdout.contains("--json-output"));
    assert!(!stdout.contains("--allow-level0-gaps"));
}

#[test]
fn verify_examples_rejects_removed_level0_gap_alias() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "verify", "examples", "--allow-level0-gaps"])
        .output()
        .expect("run verify examples with removed gap alias");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "removed gap alias should be rejected\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stderr.contains("--allow-level0-gaps has been removed; use --allow-l0-gaps"));
}

#[test]
fn verify_examples_metadata_only_parses_multiline_headers() {
    let temp = TempDir::new("trust-verify-examples-metadata");
    let root = temp.path().join("repo");
    write_repo_fixture(&root);

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "examples",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--metadata-only",
            "--json",
        ])
        .output()
        .expect("run metadata-only verifier-example diagnostic");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "metadata-only diagnostic should pass\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let report: Value = serde_json::from_slice(&output.stdout).expect("json report");
    assert_eq!(report["schema"], "trust.verify-examples.report.v2");
    assert_metadata_only_non_proof_report(&report);
    assert_eq!(report["checked"], 2);
    assert!(
        report["examples"].as_array().expect("examples array").iter().any(|row| row["terms"]
            .as_array()
            .expect("terms")
            .iter()
            .any(|term| term == "Sub"))
    );
}

#[test]
fn verify_examples_metadata_only_json_output_marks_header_validation_as_non_proof() {
    let temp = TempDir::new("trust-verify-examples-metadata-json-output");
    let root = temp.path().join("repo");
    let report_path = temp.path().join("reports/verify-examples.json");
    write_repo_fixture(&root);

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "examples",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--metadata-only",
            "--json-output",
            report_path.to_str().expect("report should be utf-8"),
        ])
        .output()
        .expect("run metadata-only verifier-example diagnostic with durable report");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "metadata-only diagnostic should keep success exit behavior\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.trim().is_empty(),
        "--json-output should not force stdout JSON\nstdout:\n{stdout}"
    );
    let report: Value =
        serde_json::from_slice(&fs::read(&report_path).expect("read report")).expect("json report");
    assert_metadata_only_non_proof_report(&report);
}

#[test]
fn verify_examples_metadata_only_rejects_expected_vckind_mismatch() {
    let temp = TempDir::new("trust-verify-examples-metadata-mismatch");
    let root = temp.path().join("repo");
    fs::create_dir_all(root.join("targo-trust")).expect("create targo-trust dir");
    fs::create_dir_all(root.join("examples")).expect("create examples dir");
    fs::write(root.join("targo-trust/Cargo.toml"), "[package]\nname='fixture'\n")
        .expect("write cargo manifest");
    fs::write(
        root.join("examples/verify_mismatch.rs"),
        "\
// VcKind: SliceBoundsCheck
// Expected: IndexOutOfBounds PROVED
fn main() {}
",
    )
    .expect("write mismatched verify example");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "examples",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--metadata-only",
            "--json",
        ])
        .output()
        .expect("run metadata-only verifier-example diagnostic");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1),
        "metadata-only diagnostic should reject stale VcKind headers\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let report: Value = serde_json::from_slice(&output.stdout).expect("json report");
    assert_eq!(report["status"], "diagnostic_failed");
    assert!(
        report["failures"]
            .as_array()
            .expect("failures")
            .iter()
            .any(|failure| failure.as_str().is_some_and(|text| text.contains("VcKind header"))),
        "failure should explain the stale VcKind mismatch: {stdout}"
    );
}

#[test]
#[cfg(unix)]
fn verify_examples_live_diagnostic_runs_repo_local_stage2_trustc_without_claiming_evidence() {
    let temp = TempDir::new("trust-verify-examples-compiler");
    let root = temp.path().join("repo");
    let stage2_trustc = root.join("build/host/stage2/bin/trustc");
    write_repo_fixture(&root);
    fs::create_dir_all(stage2_trustc.parent().expect("stage2 parent")).expect("create stage2 bin");
    write_fake_trustc(&stage2_trustc);

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "examples",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--json",
        ])
        .env("TRUST_VERIFY", "1")
        .env("TRUST_DUMP_ONLY", "1")
        .output()
        .expect("run live verifier-example regression diagnostic");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "live diagnostic should pass\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let report: Value = serde_json::from_slice(&output.stdout).expect("json report");
    assert_non_evidence_diagnostic_report(&report);
    assert_eq!(report["mode"], "compiler-regression-diagnostic");
    assert_eq!(report["status"], "diagnostic_passed");
    assert_eq!(report["checked"], 2);
    assert_eq!(report["trustc"]["stage"], "stage2");
    assert_eq!(report["trustc"]["exact_regular_executable"], true);
    assert_eq!(report["trustc"]["post_use_sha256_verified"], true);
    assert!(
        report["trustc"]["sha256"].as_str().is_some_and(|digest| digest.len() == 64),
        "trustc digest must be bound: {}",
        report["trustc"]
    );
    assert!(
        report["examples"]
            .as_array()
            .expect("examples array")
            .iter()
            .all(|row| row["trustc_exit"] == 0)
    );
}

#[test]
#[cfg(unix)]
fn verify_examples_rejects_explicit_external_trustc() {
    let temp = TempDir::new("trust-verify-examples-external-trustc");
    let root = temp.path().join("repo");
    let fake_trustc = temp.path().join("fake-trustc");
    write_repo_fixture(&root);
    write_fake_trustc(&fake_trustc);

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "examples",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--trustc",
            fake_trustc.to_str().expect("trustc should be utf-8"),
            "--json",
        ])
        .output()
        .expect("run live verifier-example diagnostic with external trustc");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "external trustc must not satisfy the bounded diagnostic policy\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "rejected external trustc should not emit JSON");
    assert!(stderr.contains("external trustc is not accepted"), "{stderr}");
    assert!(stderr.contains("build/host/stage2/bin/trustc"), "{stderr}");
}

#[test]
#[cfg(unix)]
fn verify_examples_rejects_external_trustc_bin_env() {
    let temp = TempDir::new("trust-verify-examples-external-trustc-bin");
    let root = temp.path().join("repo");
    let fake_trustc = temp.path().join("fake-trustc");
    write_repo_fixture(&root);
    write_fake_trustc(&fake_trustc);

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "examples",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
        ])
        .env("TRUSTC_BIN", &fake_trustc)
        .output()
        .expect("run live verifier-example diagnostic with external TRUSTC_BIN");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "external TRUSTC_BIN must not satisfy the bounded diagnostic policy\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "rejected external TRUSTC_BIN should not emit JSON");
    assert!(stderr.contains("external trustc is not accepted"), "{stderr}");
    assert!(stderr.contains("build/host/stage2/bin/trustc"), "{stderr}");
}

#[test]
#[cfg(unix)]
fn verify_examples_rejects_symlinked_stage2_trustc_resolving_outside_repo() {
    let temp = TempDir::new("trust-verify-examples-symlinked-stage2");
    let root = temp.path().join("repo");
    let stage2_trustc = root.join("build/host/stage2/bin/trustc");
    let external_trustc = temp.path().join("external-trustc");
    write_repo_fixture(&root);
    fs::create_dir_all(stage2_trustc.parent().expect("stage2 parent")).expect("create stage2 bin");
    write_fake_trustc(&external_trustc);
    std::os::unix::fs::symlink(&external_trustc, &stage2_trustc).expect("symlink stage2 trustc");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "examples",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
        ])
        .output()
        .expect("run live verifier-example diagnostic with symlinked stage2 trustc");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "symlinked stage2 trustc resolving outside repo must be rejected\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.trim().is_empty(), "rejected symlinked trustc should not emit JSON");
    assert!(stderr.contains("must not use symlinks for stage2 trustc identity"), "{stderr}");
    assert!(stderr.contains(stage2_trustc.to_str().expect("stage2 trustc utf-8")), "{stderr}");
}

#[test]
#[cfg(unix)]
fn verify_examples_rejects_symlinked_stage2_trustc_even_when_target_is_in_repo() {
    let temp = TempDir::new("trust-verify-examples-in-repo-symlinked-stage2");
    let root = temp.path().join("repo");
    let stage2_trustc = root.join("build/host/stage2/bin/trustc");
    let real_trustc = root.join("build/other/stage2/bin/trustc");
    write_repo_fixture(&root);
    fs::create_dir_all(stage2_trustc.parent().expect("stage2 parent")).expect("create stage2 bin");
    fs::create_dir_all(real_trustc.parent().expect("real stage2 parent"))
        .expect("create real stage2 bin");
    write_fake_trustc(&real_trustc);
    std::os::unix::fs::symlink(&real_trustc, &stage2_trustc).expect("symlink stage2 trustc");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "examples",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--trustc",
            stage2_trustc.to_str().expect("trustc should be utf-8"),
        ])
        .output()
        .expect("run live verifier-example diagnostic with in-repo symlink");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr:\n{stderr}");
    assert!(stderr.contains("is a symlink"), "{stderr}");
}

#[test]
#[cfg(unix)]
fn verify_examples_accepts_explicit_stage2_trustc_through_symlinked_repo_root() {
    let temp = TempDir::new("trust-verify-examples-symlinked-root");
    let root = temp.path().join("repo");
    let root_link = temp.path().join("repo-link");
    let stage2_trustc = root.join("build/host/stage2/bin/trustc");
    let stage2_trustc_through_link = root_link.join("build/host/stage2/bin/trustc");
    write_repo_fixture(&root);
    fs::create_dir_all(stage2_trustc.parent().expect("stage2 parent")).expect("create stage2 bin");
    write_fake_trustc(&stage2_trustc);
    std::os::unix::fs::symlink(&root, &root_link).expect("symlink repo root");

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "examples",
            "--repo-root",
            root_link.to_str().expect("root link should be utf-8"),
            "--trustc",
            stage2_trustc_through_link.to_str().expect("trustc should be utf-8"),
            "--json",
        ])
        .output()
        .expect("run live verifier-example diagnostic with symlinked repo root");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "canonical in-repo stage2 trustc should pass through a symlinked root\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let report: Value = serde_json::from_slice(&output.stdout).expect("json report");
    assert_eq!(report["trustc"]["stage"], "stage2");
    let canonical_stage2_trustc = stage2_trustc.canonicalize().expect("canonical stage2 trustc");
    assert_eq!(
        report["trustc"]["path"],
        canonical_stage2_trustc.to_str().expect("stage2 trustc utf-8")
    );
}

#[test]
#[cfg(unix)]
fn verify_examples_json_output_writes_durable_report() {
    let temp = TempDir::new("trust-verify-examples-json-output");
    let root = temp.path().join("repo");
    let stage2_trustc = root.join("build/host/stage2/bin/trustc");
    let report = temp.path().join("reports/verify-examples.json");
    write_repo_fixture(&root);
    fs::create_dir_all(stage2_trustc.parent().expect("stage2 parent")).expect("create stage2 bin");
    write_fake_trustc(&stage2_trustc);

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "examples",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--trustc",
            stage2_trustc.to_str().expect("trustc should be utf-8"),
            "--json-output",
            report.to_str().expect("report should be utf-8"),
        ])
        .output()
        .expect("run live verifier-example regression diagnostic");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "live diagnostic should pass\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.trim().is_empty(),
        "--json-output should not force stdout JSON\nstdout:\n{stdout}"
    );
    let report: Value =
        serde_json::from_slice(&fs::read(&report).expect("read report")).expect("json report");
    assert_non_evidence_diagnostic_report(&report);
    assert_eq!(report["status"], "diagnostic_passed");
    assert_eq!(report["verification_mode"], "strict");
    assert_eq!(report["fail_closed"], true);
    assert_eq!(report["trustc"]["post_use_sha256_verified"], true);
}

#[test]
#[cfg(unix)]
fn verify_examples_default_refuses_stage1_without_developer_flag() {
    let temp = TempDir::new("trust-verify-examples-stage1");
    let root = temp.path().join("repo");
    let stage1_trustc = root.join("build/host/stage1/bin/trustc");
    write_repo_fixture(&root);
    fs::create_dir_all(stage1_trustc.parent().expect("stage1 parent")).expect("create stage1 bin");
    write_fake_trustc(&stage1_trustc);

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "examples",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
        ])
        .output()
        .expect("run verifier-example diagnostic");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(2),
        "stage1 should be refused by default\nstderr:\n{stderr}"
    );
    assert!(stderr.contains("--allow-stage1-developer"));

    let output = Command::new(targo_trust_binary())
        .args([
            "trust",
            "verify",
            "examples",
            "--repo-root",
            root.to_str().expect("root should be utf-8"),
            "--allow-stage1-developer",
            "--json",
        ])
        .output()
        .expect("run verifier-example diagnostic with stage1 developer flag");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "stage1 developer diagnostic should pass with explicit flag\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let report: Value = serde_json::from_slice(&output.stdout).expect("json report");
    assert_eq!(report["trustc"]["stage"], "stage1-developer");
    assert_eq!(report["trustc"]["stage1_developer_allowed"], true);
}

fn write_repo_fixture(root: &Path) {
    fs::create_dir_all(root.join("targo-trust")).expect("create targo-trust dir");
    fs::create_dir_all(root.join("examples")).expect("create examples dir");
    fs::write(root.join("targo-trust/Cargo.toml"), "[package]\nname='fixture'\n")
        .expect("write cargo manifest");
    fs::write(
        root.join("examples/verify_alpha.rs"),
        "\
// Expected: ArithmeticOverflow(Add) FAILED
// ArithmeticOverflow(Sub) PROVED
fn main() {}
",
    )
    .expect("write verify alpha");
    fs::write(
        root.join("examples/verify_beta.rs"),
        "\
// Expected: BoundsCheck UNKNOWN
fn main() {}
",
    )
    .expect("write verify beta");
}

#[cfg(unix)]
fn write_fake_trustc(path: &Path) {
    use std::os::unix::fs::PermissionsExt;

    fs::write(
        path,
        "\
#!/usr/bin/env sh
if [ \"${TRUST_VERIFY+x}\" = x ]; then
  echo 'ambient verifier activation leaked to raw trustc' >&2
  exit 13
fi
if [ \"${TRUST_DUMP_ONLY+x}\" = x ]; then
  echo 'ambient dump-only policy leaked to raw trustc' >&2
  exit 14
fi
case \" $* \" in
  *\" --crate-name trust_verify_example_\"*) ;;
  *) echo 'missing Trust-owned crate name' >&2; exit 9 ;;
esac
case \" $* \" in
  *\" -Z trust-verify-timeout-ms=5000 \"*) ;;
  *) echo 'missing tracked verifier timeout option' >&2; exit 10 ;;
esac
case \" $* \" in
  *\" -Z trust-verify-full \"*) echo 'removed flag -Z trust-verify-full must not be passed' >&2; exit 11 ;;
  *) ;;
esac
case \" $* \" in
  *\" -Z trust-verify \"*|*\" trust-verify-target=\"*) echo 'retired activation/scope option must not be passed' >&2; exit 12 ;;
  *) ;;
esac
verification_session=''
for arg in \"$@\"; do
  case \"$arg\" in
    trust-verify-session=*) verification_session=${arg#trust-verify-session=} ;;
    *) ;;
  esac
done
case \"$verification_session\" in
  ''|*[!0-9a-f]*) echo 'missing or malformed verifier session' >&2; exit 15 ;;
  *) ;;
esac
if [ \"${#verification_session}\" -ne 64 ]; then
  echo 'verifier session must be 256-bit lowercase hex' >&2
  exit 16
fi
printf 'TRUST_JSON:{\"type\":\"function_result\",\"function\":\"alpha\",\"verification_session\":\"%s\",\"results\":[{\"kind\":\"overflow:add\",\"description\":\"arithmetic overflow (Add)\",\"outcome\":\"failed\",\"obligation_id\":\"alpha:add:1\",\"location\":{\"file\":\"verify_alpha.rs\",\"line\":1,\"column\":1}},{\"kind\":\"overflow:sub\",\"description\":\"arithmetic overflow (Sub)\",\"outcome\":\"proved\",\"obligation_id\":\"alpha:sub:1\",\"location\":{\"file\":\"verify_alpha.rs\",\"line\":1,\"column\":1}}],\"total\":2}\\n' \"$verification_session\"
printf 'TRUST_JSON:{\"type\":\"function_result\",\"function\":\"beta\",\"verification_session\":\"%s\",\"results\":[{\"kind\":\"bounds\",\"description\":\"bounds check\",\"outcome\":\"unknown\",\"obligation_id\":\"beta:bounds:1\",\"location\":{\"file\":\"verify_beta.rs\",\"line\":1,\"column\":1}}],\"total\":1}\\n' \"$verification_session\"
exit 0
",
    )
    .expect("write fake trustc");
    let mut permissions = fs::metadata(path).expect("metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).expect("chmod fake trustc");
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

fn assert_metadata_only_non_proof_report(report: &Value) {
    assert_non_evidence_diagnostic_report(report);
    assert_eq!(report["mode"], "metadata-regression-diagnostic");
    assert_eq!(report["verification_mode"], "metadata-only");
    assert_eq!(report["status"], "diagnostic_passed");
    assert_ne!(report["status"], "passed");
    assert_eq!(report["evidence"]["kind"], "verifier-example-header-regression-diagnostic");
    assert_eq!(report["evidence"]["status"], "diagnostic_passed");
    assert_eq!(report["evidence"]["proof_evidence"], false);
    assert_eq!(report["evidence"]["release_evidence"], false);
    assert_eq!(report["evidence"]["trustc_invocation_attempted"], false);
    assert_eq!(report["evidence"]["trustc_completed_runs"], 0);
    assert_eq!(report["fail_closed"], false);
    assert!(report["trustc"].is_null());
}

fn assert_non_evidence_diagnostic_report(report: &Value) {
    assert_eq!(report["schema"], "trust.verify-examples.report.v2");
    assert_eq!(report["report_kind"], "regression_diagnostic");
    assert_eq!(report["proof_evidence"], false);
    assert_eq!(report["release_evidence"], false);
    assert_eq!(report["source_provenance_authenticated"], false);
    assert_eq!(report["tool_provenance_authenticated"], false);
    assert_eq!(
        report["fail_closed_scope"],
        "declared-expected-row-regression-matching-only"
    );
    assert!(
        report["provenance_limit"]
            .as_str()
            .is_some_and(|text| text.contains("cannot be promoted to proof or release evidence"))
    );
}
