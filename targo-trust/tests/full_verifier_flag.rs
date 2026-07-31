#![cfg(unix)]

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::Value;
use sha2::{Digest, Sha256};

#[path = "support/fake_trustd.rs"]
mod fake_trustd;
#[path = "support/publication_transport.rs"]
mod publication_transport;

#[derive(Debug)]
struct CapturedTCargoInvocation {
    program: String,
    args: Vec<String>,
    exported_rustc: String,
    rustflags_env: String,
    encoded_rustflags_env: String,
    trust_no_verify: String,
    trust_hardened: String,
    trust_profile: String,
    trust_verify_memory_safe: String,
    trust_verify_survey: String,
}

#[test]
fn full_verifier_flag_is_rejected_before_targo() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_maybe_capture(
        "targo-trust-full-verifier",
        &["--full-verifier"],
        &[],
    );
    assert_eq!(
        status,
        Some(2),
        "removed --full-verifier must fail before dispatch\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("--full-verifier has been removed")
            && stderr.contains("strict verification runs by default"),
        "rejection must explain the batteries-on replacement: {stderr}"
    );
    assert!(capture.is_none(), "removed mode must be rejected before invoking targo");
}

#[test]
fn memory_safe_and_allow_l0_gaps_are_rejected_before_targo() {
    for args in [["--memory-safe", "--allow-l0-gaps"], ["--allow-l0-gaps", "--memory-safe"]] {
        let (capture, stdout, stderr, status) =
            run_targo_trust_check_with_fake_toolchain_maybe_capture(
                "targo-trust-conflicting-advisory-modes",
                &args,
                &[],
            );
        assert_eq!(
            status,
            Some(2),
            "incoherent advisory composition must fail before dispatch\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(stderr.contains("--memory-safe conflicts with --allow-l0-gaps"), "{stderr}");
        assert!(capture.is_none(), "conflicting policy must not invoke Targo");
    }
}

#[test]
fn default_targo_check_uses_batteries_on_strict_policy() {
    let (capture, stdout, stderr, status) =
        run_targo_trust_check_with_fake_toolchain_args("targo-trust-default-verifier", &[]);
    assert_eq!(
        status,
        Some(0),
        "targo-trust check should complete with the fake toolchain\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        Path::new(&capture.exported_rustc).file_name().is_some_and(|name| name == "trustc"),
        "child cargo must get RUSTC pinned to the canonical selected Trust compiler: {capture:?}"
    );

    assert!(
        capture.program == "targo",
        "crate-mode dispatch should re-exec the Trust-owned targo binary: {capture:?}"
    );
    assert!(
        !capture.args.iter().any(|arg| arg == "--full-verifier"),
        "default targo invocation should not receive the public full-verifier flag: {capture:?}"
    );
    assert!(
        !capture_has_z_flag(&capture, "trust-verify-full")
            && !capture_has_z_flag(&capture, "trust-verify"),
        "batteries-on verification must not emit either retired activator: {capture:?}"
    );
    assert!(
        !capture_has_z_flag(&capture, "trust-policy=advisory"),
        "the default lane is strict, never advisory: {capture:?}"
    );
    assert!(
        !capture_has_z_flag(&capture, "trust-verify-hardened"),
        "the selected profile is the sole hardened-policy carrier: {capture:?}"
    );
    assert!(capture_has_z_flag(&capture, "trust-verify-profile=unix_hardened"));
    assert!(!capture_has_z_flag(&capture, "trust-compiler-cache=no"));
    assert!(capture_has_z_flag(&capture, "trust-verify-timeout-ms=5000"));
    assert!(capture_has_z_flag(&capture, "trust-verify-function-budget-ms=120000"));
    assert!(capture_has_z_option_prefix(&capture, "trust-verify-session="));
    assert_eq!(capture_codegen_option_values(&capture, "overflow-checks"), ["yes"]);
    assert_eq!(capture_codegen_option_values(&capture, "debug-assertions"), ["yes"]);
    assert_eq!(capture.trust_hardened, "", "legacy hardened env must be scrubbed");
    assert_eq!(capture.trust_profile, "", "legacy profile env must be scrubbed");
}

#[test]
fn ambient_no_verify_cannot_downgrade_verified_targo_subprocess() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-ambient-no-verify",
        &[],
        &[("TRUST_NO_VERIFY", "1")],
    );
    assert_eq!(
        status,
        Some(0),
        "verified Targo should complete after removing ambient compiler authority\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        capture.trust_no_verify, "",
        "the proof subprocess must not inherit TRUST_NO_VERIFY: {capture:?}"
    );
    assert!(
        !capture_has_z_flag(&capture, "trust-verify=off"),
        "verified rustflags must not contain the compiler off-switch: {capture:?}"
    );
}

#[test]
fn strict_single_file_invokes_fake_trustc_with_one_canonical_safety_policy() {
    let tmp_dir = temp_test_dir("targo-trust-direct-safety-policy");
    let source_dir = tmp_dir.join("source");
    let bin_dir = tmp_dir.join("toolchain").join("bin");
    fs::create_dir_all(&source_dir).expect("create fixture source dir");
    fs::create_dir_all(&bin_dir).expect("create fake toolchain bin dir");
    let source = source_dir.join("fixture.rs");
    fs::write(&source, "pub fn add(a: usize, b: usize) -> usize { a + b }\n")
        .expect("write fixture source");

    let capture_path = tmp_dir.join("capture.txt");
    let targo_trust = install_targo_trust_binary(&bin_dir);
    write_executable(&bin_dir.join("trustc"), fake_trustc_script());
    write_executable(&bin_dir.join("ay"), "#!/bin/sh\nprintf 'ay 0.0.0\\n'\n");

    let output = Command::new(&targo_trust)
        .arg("check")
        .arg(&source)
        // Equivalent true spellings are accepted, removed, and replaced with
        // one canonical pair at the end of the actual trustc argv.
        .arg("-Coverflow-checks=true")
        .args(["-C", "debug-assertions=on"])
        .current_dir(&source_dir)
        .env("TRUST_CAPTURE_FILE", &capture_path)
        .env("TRUST_CACHE_DIR", tmp_dir.join("cache"))
        .env("TRUST_FAKE_TRUSTC_CRATE_SUMMARY", "1")
        .env_remove("CARGO")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .output()
        .expect("run strict single-file check with fake trustc");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "strict direct check should complete with fake proof evidence\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let capture = fs::read_to_string(&capture_path).expect("read fake trustc capture");
    let invocations = parse_trustc_invocations(&capture);
    let actual = invocations
        .iter()
        .find(|args| args.iter().any(|arg| arg == source.to_string_lossy().as_ref()))
        .unwrap_or_else(|| panic!("missing direct strict invocation: {invocations:?}"));
    assert_eq!(codegen_option_values(actual, "overflow-checks"), ["yes"]);
    assert_eq!(codegen_option_values(actual, "debug-assertions"), ["yes"]);
    let safety_tail = actual
        .windows(4)
        .rposition(|window| {
            window[0] == "-C"
                && window[1] == "overflow-checks=yes"
                && window[2] == "-C"
                && window[3] == "debug-assertions=yes"
        })
        .expect("canonical safety pair must be contiguous");
    assert!(
        codegen_option_values(&actual[safety_tail + 4..], "overflow-checks").is_empty()
            && codegen_option_values(&actual[safety_tail + 4..], "debug-assertions").is_empty(),
        "no later codegen argument may override the canonical safety policy: {actual:?}"
    );

    fs::write(&capture_path, "").expect("reset capture for rejection probe");
    let rejected = Command::new(&targo_trust)
        .arg("check")
        .arg(&source)
        .arg("-Coverflow-checks=no")
        .current_dir(&source_dir)
        .env("TRUST_CAPTURE_FILE", &capture_path)
        .env("TRUST_CACHE_DIR", tmp_dir.join("cache"))
        .env_remove("CARGO")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .output()
        .expect("run conflicting strict single-file check");
    assert_eq!(rejected.status.code(), Some(2));
    let rejected_stderr = String::from_utf8_lossy(&rejected.stderr);
    assert!(
        rejected_stderr.contains("conflicts with strict verification's required overflow checks"),
        "{rejected_stderr}"
    );
    let rejected_capture = fs::read_to_string(&capture_path).unwrap_or_default();
    assert!(
        parse_trustc_invocations(&rejected_capture)
            .iter()
            .all(|args| !args.iter().any(|arg| arg == source.to_string_lossy().as_ref())),
        "conflicting direct compilation must be rejected before trustc receives the source"
    );

    let _ = fs::remove_dir_all(&tmp_dir);
}

#[test]
fn exact_report_unsafe_memory_writes_domination_wrapper() {
    let tmp_dir = temp_test_dir("targo-trust-unsafe-memory-wrapper");
    let crate_dir = tmp_dir.join("crate");
    let src_dir = crate_dir.join("src");
    let bin_dir = tmp_dir.join("toolchain").join("bin");
    fs::create_dir_all(&src_dir).expect("create fixture src dir");
    fs::create_dir_all(&bin_dir).expect("create fake toolchain bin dir");

    fs::write(
        crate_dir.join("Cargo.toml"),
        "[package]\nname = \"unsafe-memory-wrapper-fixture\"\nversion = \"0.0.0\"\nedition = \"2021\"\n",
    )
    .expect("write fixture manifest");
    fs::write(
        src_dir.join("lib.rs"),
        "pub unsafe fn read_ptr(ptr: *const u8) -> u8 { unsafe { *ptr } }\n",
    )
    .expect("write fixture source");
    init_clean_git_repo(&crate_dir);
    let expected_head = git_stdout(&crate_dir, &["rev-parse", "HEAD"]);

    let capture_path = tmp_dir.join("capture.txt");
    let targo_trust = install_targo_trust_binary(&bin_dir);
    write_executable(&bin_dir.join("trustc"), fake_trustc_script());
    write_executable(&bin_dir.join("targo"), fake_targo_script());
    let _trustd = fake_trustd::install(&bin_dir);

    let output = Command::new(targo_trust)
        .args(["report", "--unsafe-memory"])
        .current_dir(&crate_dir)
        .env("TRUST_CAPTURE_FILE", &capture_path)
        .env("TRUST_FAKE_TARGO_FULL_VERIFIER_EVIDENCE", "1")
        .env_remove("CARGO")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .output()
        .expect("run exact unsafe-memory report");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(0),
        "exact report --unsafe-memory should emit proof artifacts with fake native evidence\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let capture_text = fs::read_to_string(&capture_path).expect("read fake targo capture");
    let capture = parse_targo_capture(&capture_text);
    assert!(
        !capture.args.iter().any(|arg| arg == "--unsafe-memory"),
        "wrapper-only unsafe-memory flag must be consumed before invoking targo: {capture:?}"
    );
    assert!(
        !capture_has_z_flag(&capture, "trust-verify-full"),
        "`-Z trust-verify-full` was deleted; strict is the default for the crate under check, so it must NOT be requested: {capture:?}"
    );

    let proof_dir = crate_dir.join("reports").join("proof");
    let wrapper_path = proof_dir.join("unsafe-memory.json");
    let proof_report_path = proof_dir.join("report.json");
    assert!(proof_report_path.is_file(), "canonical proof report should be written");
    assert!(wrapper_path.is_file(), "unsafe-memory wrapper should be written");

    let wrapper: Value = serde_json::from_slice(&fs::read(&wrapper_path).expect("read wrapper"))
        .expect("parse unsafe-memory wrapper");
    assert_eq!(wrapper["schema"], "trust.proof-unsafe-memory-report.v1");
    assert_eq!(wrapper["candidate_commit"], expected_head);
    assert_eq!(wrapper["repo_dirty"], false);
    assert_eq!(wrapper["producer"]["native"], true);
    assert_eq!(wrapper["producer"]["command"], "targo trust report --unsafe-memory");
    assert_eq!(wrapper["proof_report_path"], "report.json");
    assert_eq!(wrapper["proof_report_hash"], format!("sha256:{}", file_sha256(&proof_report_path)));
    assert_eq!(wrapper["coverage"]["unsafe_blocks_total"], 1);
    assert_eq!(wrapper["coverage"]["unsafe_blocks_proved"], 1);
    assert_eq!(wrapper["coverage"]["unsafe_operations_total"], 1);
    assert_eq!(wrapper["coverage"]["unsafe_operations_proved"], 1);
    assert_eq!(wrapper["coverage"]["memory_obligations_total"], 1);
    assert_eq!(wrapper["coverage"]["memory_obligations_proved"], 1);
    assert!(wrapper["unsupported"].as_array().is_some_and(Vec::is_empty));

    let _ = fs::remove_dir_all(&tmp_dir);
}

#[test]
fn allow_l0_gaps_omits_full_verifier() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args(
        "targo-trust-allow-l0-gaps",
        &["--allow-l0-gaps"],
    );
    assert_eq!(
        status,
        Some(0),
        "targo-trust check --allow-l0-gaps should complete with the fake toolchain\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !capture_has_z_flag(&capture, "trust-verify-full"),
        "--allow-l0-gaps should run raw warning mode instead of full verifier mode: {capture:?}"
    );
    assert!(
        !capture_has_z_flag(&capture, "trust-verify"),
        "batteries-on advisory mode must not resurrect the retired activator: {capture:?}"
    );
    assert!(
        capture_has_z_flag(&capture, "trust-policy=advisory"),
        "--allow-l0-gaps must select the advisory verifier policy: {capture:?}"
    );
    assert!(capture_codegen_option_values(&capture, "overflow-checks").is_empty());
    assert!(capture_codegen_option_values(&capture, "debug-assertions").is_empty());
}

#[test]
fn public_modes_override_ambient_memory_safe_and_survey_policy() {
    let (default_capture, _, _, default_status) =
        run_targo_trust_check_with_fake_toolchain_args_env(
            "targo-trust-ambient-survey",
            &[],
            &[("TRUST_VERIFY_SURVEY", "1")],
        );
    assert_eq!(default_status, Some(0));
    assert_eq!(default_capture.trust_verify_survey, "");
    assert_eq!(default_capture.trust_verify_memory_safe, "");
    assert!(
        !capture_has_z_flag(&default_capture, "trust-policy=memory-safe"),
        "default/explicit full verification must not carry the advisory memory-safe policy: {default_capture:?}"
    );

    let (strict_capture, _, _, strict_status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-ambient-memory-safe",
        &["--strict"],
        &[("TRUST_VERIFY_MEMORY_SAFE", "1")],
    );
    assert_eq!(strict_status, Some(0));
    assert_eq!(strict_capture.trust_verify_memory_safe, "");
    assert_eq!(strict_capture.trust_verify_survey, "");
    assert!(!capture_has_z_flag(&strict_capture, "trust-policy=memory-safe"));

    let (advisory_capture, _, _, advisory_status) =
        run_targo_trust_check_with_fake_toolchain_args_env(
            "targo-trust-advisory-memory-safe",
            &["--memory-safe"],
            &[("TRUST_VERIFY_MEMORY_SAFE", "1")],
        );
    assert_eq!(advisory_status, Some(0));
    assert_eq!(advisory_capture.trust_verify_memory_safe, "");
    assert!(
        capture_has_z_flag(&advisory_capture, "trust-policy=memory-safe"),
        "the advisory memory-safe policy must be a tracked compiler flag: {advisory_capture:?}"
    );

    let (survey_capture, _, _, survey_status) = run_targo_trust_check_with_fake_toolchain_args(
        "targo-trust-explicit-survey",
        &["--survey"],
    );
    assert_eq!(survey_status, Some(0));
    assert_eq!(survey_capture.trust_verify_survey, "");
    assert!(capture_has_z_flag(&survey_capture, "trust-policy=advisory"));
    assert_eq!(survey_capture.trust_verify_memory_safe, "");
    assert!(!capture_has_z_flag(&survey_capture, "trust-policy=memory-safe"));
}

#[test]
fn default_targo_check_preserves_fail_closed_flags_with_encoded_rustflags() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-encoded-rustflags",
        &[],
        &[(
            "CARGO_ENCODED_RUSTFLAGS",
            "-C\x1fdebuginfo=1\x1f-Coverflow-checks=no\x1f-C\x1fdebug-assertions=off",
        )],
    );
    assert_eq!(
        status,
        Some(0),
        "targo-trust check should complete with inherited encoded flags\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    assert_eq!(
        capture.rustflags_env, "",
        "when encoded flags are inherited, targo-trust should not also export plain RUSTFLAGS"
    );
    assert!(
        capture.encoded_rustflags_env.split('\x1f').any(|arg| arg == "debuginfo=1"),
        "inherited encoded flags should be preserved: {capture:?}"
    );
    assert!(!capture_has_z_flag(&capture, "trust-verify-full"));
    assert!(!capture_has_z_flag(&capture, "trust-verify"));
    assert!(
        capture
            .encoded_rustflags_env
            .split('\x1f')
            .any(|arg| arg.starts_with("trust-verify-level=")),
        "encoded Cargo flags must still configure the verification level: {capture:?}"
    );
    assert_eq!(capture_codegen_option_values(&capture, "overflow-checks"), ["yes"]);
    assert_eq!(capture_codegen_option_values(&capture, "debug-assertions"), ["yes"]);
}

#[test]
fn default_targo_check_fails_closed_on_unknown_transport() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-unknown-transport",
        &[],
        &[("TRUST_FAKE_TARGO_OUTCOME", "unknown")],
    );
    assert_eq!(
        status,
        Some(1),
        "targo-trust check must fail when the compiler emits unknown proof rows despite exit 0\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !capture_has_z_flag(&capture, "trust-verify-full")
            && !capture_has_z_flag(&capture, "trust-verify"),
        "fail-closed behavior must come from authenticated batteries-on scope, not retired flags: {capture:?}"
    );
}

#[test]
fn default_targo_check_fails_closed_without_coverage_summary() {
    let (_, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-missing-coverage-summary",
        &[],
        &[("TRUST_FAKE_TARGO_NO_COVERAGE", "1")],
    );
    assert_eq!(
        status,
        Some(2),
        "a declared Cargo proof unit with a terminal summary before coverage must be rejected as a malformed authority channel\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("invalid canonical Cargo evidence channel")
            && stderr.contains("terminal crate summary before the required coverage summary"),
        "{stderr}"
    );
}

#[test]
fn default_targo_check_rejects_non_primary_coverage_for_root_target() {
    let (_, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-non-primary-coverage",
        &[],
        &[("TRUST_FAKE_TARGO_NON_PRIMARY_COVERAGE", "1")],
    );
    assert_eq!(
        status,
        Some(2),
        "a host/dependency coverage row must not satisfy root-target completeness\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("invalid canonical Cargo evidence channel")
            && stderr.contains("Trust transport scope/session does not match Cargo envelope"),
        "{stderr}"
    );
}

#[test]
fn legacy_json_coverage_is_advisory_only_and_never_receives_coverage_credit() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_maybe_capture(
        "targo-trust-legacy-coverage-strict",
        &[],
        &[("TRUST_FAKE_LEGACY_COVERAGE", "1")],
    );
    assert_eq!(
        status,
        Some(2),
        "strict verification must reject a compiler that only has generic/legacy JSON coverage\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr
            .contains("strict native verification requires authenticated, session-bound coverage")
            && stderr.contains("supports generic Trust JSON"),
        "{stderr}"
    );
    assert!(capture.is_none(), "strict capability rejection must happen before Targo dispatch");

    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-legacy-coverage-advisory",
        &["--allow-l0-gaps"],
        &[("TRUST_FAKE_LEGACY_COVERAGE", "1")],
    );
    assert_eq!(
        status,
        Some(0),
        "explicit advisory mode should retain generic JSON compatibility while treating legacy coverage as unknown\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(capture_has_z_flag(&capture, "trust-policy=advisory"));
}

#[test]
fn default_targo_check_fails_closed_on_recorded_assumptions() {
    let (_, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-assumption-transport",
        &[],
        &[("TRUST_FAKE_TARGO_OUTCOME", "assumption")],
    );
    assert_eq!(
        status,
        Some(1),
        "batteries-on strict checking must not turn an explicit assumption into a successful exit\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let (_, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-advisory-assumption-transport",
        &["--allow-l0-gaps"],
        &[("TRUST_FAKE_TARGO_OUTCOME", "assumption")],
    );
    assert_eq!(
        status,
        Some(0),
        "only the explicit advisory lane may return a conditional success for a recorded assumption\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-memory-safe-assumption-transport",
        &["--memory-safe"],
        &[("TRUST_FAKE_TARGO_OUTCOME", "assumption")],
    );
    assert_eq!(
        status,
        Some(0),
        "the narrow memory-safe lane must permit its authenticated safe-code assumption as a conditional success\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(capture_has_z_flag(&capture, "trust-policy=memory-safe"));
    assert!(!capture_has_z_flag(&capture, "trust-policy=advisory"));
    assert_eq!(capture_codegen_option_values(&capture, "overflow-checks"), ["yes"]);
    assert_eq!(capture_codegen_option_values(&capture, "debug-assertions"), ["yes"]);

    let (_, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-memory-safe-unmarked-assumption-transport",
        &["--memory-safe"],
        &[
            ("TRUST_FAKE_TARGO_OUTCOME", "assumption"),
            ("TRUST_FAKE_TARGO_UNMARKED_ASSUMPTION", "1"),
        ],
    );
    assert_eq!(
        status,
        Some(1),
        "memory-safe policy must reject assumptions not stamped by the compiler's safe-code demotion\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stderr.contains("memory-safe policy rejected unmarked assumption"), "{stderr}");

    let (_, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-memory-safe-unknown-transport",
        &["--memory-safe"],
        &[("TRUST_FAKE_TARGO_OUTCOME", "unknown")],
    );
    assert_eq!(
        status,
        Some(1),
        "memory-safe policy must still fail on genuine unknown evidence, including gaps from unsafe functions\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[test]
fn default_targo_check_rejects_text_only_proved_diagnostics() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-text-only-proved",
        &[],
        &[("TRUST_FAKE_TARGO_TEXT_ONLY_PROVED", "1")],
    );
    assert_eq!(
        status,
        Some(2),
        "a crate-mode run with zero per-function TRUST_JSON rows means verification never ran; \
         text-only PROVED diagnostics must be a hard setup error\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        capture_has_z_flag(&capture, "trust-verify-output=json"),
        "default native run should request structured JSON transport: {capture:?}"
    );
    assert!(
        stderr.contains("note: Trust [test]: test -- PROVED")
            && stderr.contains("invalid canonical Cargo evidence channel"),
        "stderr should preserve the untrusted text diagnostic while rejecting its malformed declared proof unit\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains(
            "Cargo proof unit ended before its required coverage summary, terminal crate summary, and compiler-artifact"
        ),
        "stderr should identify the incomplete authenticated Cargo lifecycle\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[test]
fn default_native_rejects_text_only_proved_when_json_transport_capability_is_missing() {
    let tmp_dir = temp_test_dir("targo-trust-text-proved-no-json-capability");
    let crate_dir = tmp_dir.join("crate");
    let src_dir = crate_dir.join("src");
    let bin_dir = tmp_dir.join("toolchain").join("bin");
    fs::create_dir_all(&src_dir).expect("create fixture src dir");
    fs::create_dir_all(&bin_dir).expect("create fake toolchain bin dir");

    fs::write(
        crate_dir.join("Cargo.toml"),
        "[package]\nname = \"no-json-capability-fixture\"\nversion = \"0.0.0\"\nedition = \"2021\"\n",
    )
    .expect("write fixture manifest");
    fs::write(src_dir.join("lib.rs"), "pub fn id(x: usize) -> usize { x }\n")
        .expect("write fixture source");

    let capture_path = tmp_dir.join("capture.txt");
    let cache_dir = tmp_dir.join("cache");
    let targo_trust = install_targo_trust_binary(&bin_dir);
    write_executable(&bin_dir.join("trustc"), fake_trustc_script());
    write_executable(&bin_dir.join("targo"), fake_targo_script());
    let _trustd = fake_trustd::install(&bin_dir);

    let output = Command::new(targo_trust)
        .arg("check")
        .current_dir(&crate_dir)
        .env("TRUST_CAPTURE_FILE", &capture_path)
        .env("TRUST_CACHE_DIR", &cache_dir)
        .env("TRUST_FAKE_TRUSTC_NO_JSON_CAPABILITY", "1")
        .env_remove("CARGO")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .output()
        .expect("run targo-trust check with no-json fake compiler");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert_eq!(
        output.status.code(),
        Some(2),
        "missing JSON transport capability should be a setup error\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("native source verification requires structured Trust JSON transport")
            && stderr.contains("Human-readable Trust diagnostics are not accepted")
            && stderr.contains("--standalone"),
        "stderr should explain the JSON transport requirement\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !stdout.contains("standalone analysis") && !stderr.contains("standalone analysis"),
        "default native rejection must not run standalone/source-only analysis\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let capture_text = fs::read_to_string(&capture_path).unwrap_or_default();
    assert!(
        !capture_text.contains("kind=targo"),
        "targo must not run after no-JSON capability rejection\ncapture:\n{capture_text}"
    );

    let _ = fs::remove_dir_all(&tmp_dir);
}

#[test]
fn default_targo_check_preserves_underlying_compile_exit_code() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-compiler-exit-code",
        &[],
        &[("TRUST_FAKE_TARGO_EXIT", "101")],
    );
    assert_eq!(
        status,
        Some(101),
        "targo-trust check should preserve Cargo/rustc compile exit codes\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !capture_has_z_flag(&capture, "trust-verify-full")
            && !capture_has_z_flag(&capture, "trust-verify"),
        "compile failure must be preserved without retired verifier activators: {capture:?}"
    );
}

#[test]
fn disabled_policy_fails_closed_before_targo() {
    let (capture, stdout, stderr, status) =
        run_targo_trust_check_with_trust_table("targo-trust-disabled-config", "enabled = false\n");

    assert_eq!(
        status,
        Some(2),
        "disabled verification should be a setup error\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("verification disabled"),
        "stderr should explain the fail-closed config error\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(capture.is_none(), "fake targo must not run when verification is disabled");
}

#[test]
fn an_unknown_key_fails_closed_before_targo() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_trust_table(
        "targo-trust-invalid-config",
        "unexpected = \"value\"\n",
    );

    assert_eq!(
        status,
        Some(2),
        "an unknown key should be a setup error\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("unknown field `unexpected`") && stderr.contains("supported keys"),
        "stderr should name the typo and the spellings that exist\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(capture.is_none(), "fake targo must not run on an unreadable policy");
}

#[test]
fn unknown_codegen_backend_fails_closed_before_targo() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_trust_table(
        "targo-trust-invalid-codegen-backend",
        "codegen_backend = \"cranelift\"\n",
    );

    assert_eq!(
        status,
        Some(2),
        "unknown codegen_backend should be a setup error\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("unknown codegen backend") && stderr.contains("cranelift"),
        "stderr should explain the invalid backend\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(capture.is_none(), "fake targo must not run when codegen_backend is invalid");
}

#[test]
fn function_budget_reaches_tracked_compiler_policy() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_trust_table(
        "targo-trust-function-budget-config",
        "function_budget_ms = 45000\n",
    );
    assert_eq!(
        status,
        Some(0),
        "valid function budget should dispatch\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let capture = capture.expect("fake targo must receive a valid configured run");
    assert!(capture_has_z_flag(&capture, "trust-verify-function-budget-ms=45000"));
}

#[test]
fn the_deprecated_file_still_configures_a_run_and_says_where_to_move() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_legacy_file(
        "targo-trust-legacy-config",
        "function_budget_ms = 45000\n",
    );
    assert_eq!(
        status,
        Some(0),
        "the deprecated file must keep working for one release\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("`trust.toml` is deprecated") && stderr.contains("[trust]"),
        "the warning must name the replacement\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let capture = capture.expect("fake targo must receive a valid configured run");
    assert!(capture_has_z_flag(&capture, "trust-verify-function-budget-ms=45000"));
}

#[test]
fn declaring_policy_on_both_surfaces_fails_closed_before_targo() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_policy(
        "targo-trust-two-policy-surfaces",
        Some("level = \"L1\"\n"),
        Some("level = \"L0\"\n"),
    );

    assert_eq!(
        status,
        Some(2),
        "two live policy surfaces must be a setup error\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("declared twice"),
        "stderr should say which two surfaces collide\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(capture.is_none(), "fake targo must not run on an ambiguous policy");
}

#[test]
fn no_hardened_disables_default_hardened_options() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args(
        "targo-trust-no-hardened",
        &["--no-hardened"],
    );
    assert_eq!(
        status,
        Some(0),
        "targo-trust check --no-hardened should complete with the fake toolchain\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    assert_eq!(capture.trust_hardened, "", "--no-hardened should suppress TRUST_HARDENED");
    assert_eq!(capture.trust_profile, "", "--no-hardened should suppress TRUST_PROFILE");
    assert!(!capture_has_z_flag(&capture, "trust-verify-hardened"));
    assert!(!capture_has_z_flag(&capture, "trust-verify-profile=unix_hardened"));
}

#[test]
fn trust_profile_sets_tracked_hardened_options() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args(
        "targo-trust-profile-hardened",
        &["--trust-profile", "coreutils_hardened"],
    );
    assert_eq!(
        status,
        Some(0),
        "targo-trust check --trust-profile should complete with the fake toolchain\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    assert_eq!(capture.trust_hardened, "");
    assert_eq!(capture.trust_profile, "");
    assert!(
        !capture_has_z_flag(&capture, "trust-verify-hardened"),
        "the selected profile is the sole hardened-policy carrier: {capture:?}"
    );
    assert!(capture_has_z_flag(&capture, "trust-verify-profile=coreutils_hardened"));
}

#[test]
fn solver_selection_is_carried_by_tracked_path_option() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args(
        "targo-trust-tracked-ay-path",
        &["--solver", "ay"],
    );
    assert_eq!(
        status,
        Some(0),
        "tracked AY selection should complete with the fake toolchain\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(capture_has_z_option_prefix(&capture, "trust-verify-ay-path="));
}

#[test]
fn crate_mode_ignores_inherited_cargo_env() {
    let tmp_dir = temp_test_dir("targo-trust-ignore-cargo-env");
    let crate_dir = tmp_dir.join("crate");
    let src_dir = crate_dir.join("src");
    let bin_dir = tmp_dir.join("toolchain").join("bin");
    fs::create_dir_all(&src_dir).expect("create fixture src dir");
    fs::create_dir_all(&bin_dir).expect("create fake toolchain bin dir");

    fs::write(
        crate_dir.join("Cargo.toml"),
        "[package]\nname = \"ignore-cargo-env-fixture\"\nversion = \"0.0.0\"\nedition = \"2021\"\n",
    )
    .expect("write fixture manifest");
    fs::write(src_dir.join("lib.rs"), "pub fn id(x: usize) -> usize { x }\n")
        .expect("write fixture source");

    let targo_trust = install_targo_trust_binary(&bin_dir);
    write_executable(&bin_dir.join("trustc"), fake_trustc_script());
    write_executable(&bin_dir.join("targo"), fake_targo_script());
    let _trustd = fake_trustd::install(&bin_dir);

    let cargo = bin_dir.join("cargo");
    let capture_path = tmp_dir.join("capture.txt");
    let bad_capture_path = tmp_dir.join("bad-cargo-capture.txt");
    write_executable(
        &cargo,
        r#"#!/bin/sh
echo bad-cargo-invoked > "$TRUST_BAD_CAPTURE"
exit 99
"#,
    );

    let output = Command::new(&targo_trust)
        .arg("check")
        .current_dir(&crate_dir)
        .env("CARGO", &cargo)
        .env("TRUST_CAPTURE_FILE", &capture_path)
        .env("TRUST_BAD_CAPTURE", &bad_capture_path)
        .output()
        .expect("run targo-trust check with CARGO pointing at inherited cargo");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "targo-trust should ignore CARGO and use sibling targo\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(!bad_capture_path.exists(), "CARGO env cargo must not be invoked");
    let capture_text = fs::read_to_string(&capture_path).unwrap_or_else(|error| {
        panic!(
            "fake targo should write capture file at {}\nerror: {error}\nstdout:\n{stdout}\nstderr:\n{stderr}",
            capture_path.display()
        )
    });
    let capture = parse_targo_capture(&capture_text);
    assert_eq!(capture.program, "targo");

    let _ = fs::remove_dir_all(&tmp_dir);
}

#[test]
fn crate_mode_rejects_path_targo_when_sibling_targo_is_missing() {
    let tmp_dir = temp_test_dir("targo-trust-missing-sibling-targo");
    let crate_dir = tmp_dir.join("crate");
    let src_dir = crate_dir.join("src");
    let bin_dir = tmp_dir.join("toolchain").join("bin");
    let path_bin_dir = tmp_dir.join("path-bin");
    fs::create_dir_all(&src_dir).expect("create fixture src dir");
    fs::create_dir_all(&bin_dir).expect("create fake toolchain bin dir");
    fs::create_dir_all(&path_bin_dir).expect("create fake PATH bin dir");

    fs::write(
        crate_dir.join("Cargo.toml"),
        "[package]\nname = \"missing-sibling-targo-fixture\"\nversion = \"0.0.0\"\nedition = \"2021\"\n",
    )
    .expect("write fixture manifest");
    fs::write(src_dir.join("lib.rs"), "pub fn id(x: usize) -> usize { x }\n")
        .expect("write fixture source");

    let capture_path = tmp_dir.join("capture.txt");
    let path_targo_marker = tmp_dir.join("path-targo-invoked.txt");
    let targo_trust = install_targo_trust_binary(&bin_dir);
    write_executable(&bin_dir.join("trustc"), fake_trustc_script());
    write_executable(
        &path_bin_dir.join("targo"),
        "#!/bin/sh\necho path-targo-invoked > \"$TRUST_PATH_TARGO_MARKER\"\nexit 99\n",
    );

    let fake_path = std::env::join_paths([path_bin_dir.as_path()])
        .expect("fake PATH should contain one valid entry");
    let output = Command::new(&targo_trust)
        .arg("check")
        .current_dir(&crate_dir)
        .env("PATH", fake_path)
        .env("TRUST_CAPTURE_FILE", &capture_path)
        .env("TRUST_PATH_TARGO_MARKER", &path_targo_marker)
        .env_remove("CARGO")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .output()
        .expect("run targo-trust check without sibling targo");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert_eq!(
        output.status.code(),
        Some(2),
        "missing sibling targo should be a setup error even with targo on PATH\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("linked Trust Cargo frontend is missing or not executable"),
        "stderr should explain the missing sibling targo\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("will not use PATH fallback"),
        "stderr should make PATH fallback rejection explicit\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(!path_targo_marker.exists(), "targo from PATH must not be invoked");

    let _ = fs::remove_dir_all(&tmp_dir);
}

fn run_targo_trust_check_with_fake_toolchain_args(
    prefix: &str,
    extra_args: &[&str],
) -> (CapturedTCargoInvocation, String, String, Option<i32>) {
    run_targo_trust_check_with_fake_toolchain_args_env(prefix, extra_args, &[])
}

fn run_targo_trust_check_with_fake_toolchain_args_env(
    prefix: &str,
    extra_args: &[&str],
    extra_env: &[(&str, &str)],
) -> (CapturedTCargoInvocation, String, String, Option<i32>) {
    let (capture, stdout, stderr, status) =
        run_targo_trust_check_with_fake_toolchain_maybe_capture(prefix, extra_args, extra_env);
    let capture = capture.unwrap_or_else(|| {
        panic!("fake targo did not write a capture file\nstdout:\n{stdout}\nstderr:\n{stderr}")
    });
    (capture, stdout, stderr, status)
}

fn run_targo_trust_check_with_fake_toolchain_maybe_capture(
    prefix: &str,
    extra_args: &[&str],
    extra_env: &[(&str, &str)],
) -> (Option<CapturedTCargoInvocation>, String, String, Option<i32>) {
    let tmp_dir = temp_test_dir(prefix);
    let crate_dir = tmp_dir.join("crate");
    let src_dir = crate_dir.join("src");
    let bin_dir = tmp_dir.join("toolchain").join("bin");
    fs::create_dir_all(&src_dir).expect("create fixture src dir");
    fs::create_dir_all(&bin_dir).expect("create fake toolchain bin dir");

    fs::write(
        crate_dir.join("Cargo.toml"),
        "[package]\nname = \"full-verifier-flag-fixture\"\nversion = \"0.0.0\"\nedition = \"2021\"\n",
    )
    .expect("write fixture manifest");
    fs::write(
        src_dir.join("lib.rs"),
        "pub fn midpoint(a: usize, b: usize) -> usize { a + (b - a) / 2 }\n",
    )
    .expect("write fixture source");

    let capture_path = tmp_dir.join("capture.txt");
    let targo_trust = install_targo_trust_binary(&bin_dir);
    write_executable(&bin_dir.join("trustc"), fake_trustc_script());
    write_executable(&bin_dir.join("targo"), fake_targo_script());
    // Retain a rustc-named compatibility file to prove child-RUSTC authority
    // stays on canonical trustc even when an alias is present.
    write_executable(&bin_dir.join("rustc"), fake_trustc_script());
    write_executable(&bin_dir.join("ay"), "#!/bin/sh\nprintf 'ay 0.0.0\\n'\n");
    let _trustd = fake_trustd::install(&bin_dir);

    let mut command = Command::new(targo_trust);
    command
        .arg("check")
        .current_dir(&crate_dir)
        .env("TRUST_CAPTURE_FILE", &capture_path)
        .env("TRUST_CACHE_DIR", tmp_dir.join("cache"))
        .env("AY_PATH", bin_dir.join("ay"))
        .env_remove("CARGO")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS");
    for (key, value) in extra_env {
        command.env(key, value);
    }
    command.args(extra_args);

    let output = command.output().expect("run targo-trust check with fake toolchain");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let capture = fs::read_to_string(&capture_path).ok().and_then(|text| {
        text.lines().any(|line| line == "kind=targo").then(|| parse_targo_capture(&text))
    });

    let _ = fs::remove_dir_all(&tmp_dir);
    (capture, stdout, stderr, output.status.code())
}

/// Drive `targo trust check` against a fixture whose policy lives in the
/// manifest's `[trust]` table.
fn run_targo_trust_check_with_trust_table(
    prefix: &str,
    trust_table: &str,
) -> (Option<CapturedTCargoInvocation>, String, String, Option<i32>) {
    run_targo_trust_check_with_policy(prefix, Some(trust_table), None)
}

/// Drive the same check against the deprecated stand-alone `trust.toml`.
fn run_targo_trust_check_with_legacy_file(
    prefix: &str,
    trust_toml: &str,
) -> (Option<CapturedTCargoInvocation>, String, String, Option<i32>) {
    run_targo_trust_check_with_policy(prefix, None, Some(trust_toml))
}

fn run_targo_trust_check_with_policy(
    prefix: &str,
    trust_table: Option<&str>,
    trust_toml: Option<&str>,
) -> (Option<CapturedTCargoInvocation>, String, String, Option<i32>) {
    let tmp_dir = temp_test_dir(prefix);
    let crate_dir = tmp_dir.join("crate");
    let src_dir = crate_dir.join("src");
    let bin_dir = tmp_dir.join("toolchain").join("bin");
    fs::create_dir_all(&src_dir).expect("create fixture src dir");
    fs::create_dir_all(&bin_dir).expect("create fake toolchain bin dir");

    let mut manifest =
        "[package]\nname = \"trust-config-fixture\"\nversion = \"0.0.0\"\nedition = \"2021\"\n"
            .to_string();
    if let Some(trust_table) = trust_table {
        manifest.push_str("\n[trust]\n");
        manifest.push_str(trust_table);
    }
    fs::write(crate_dir.join("Cargo.toml"), manifest).expect("write fixture manifest");
    fs::write(src_dir.join("lib.rs"), "pub fn id(x: usize) -> usize { x }\n")
        .expect("write fixture source");
    if let Some(trust_toml) = trust_toml {
        fs::write(crate_dir.join("trust.toml"), trust_toml).expect("write trust.toml");
    }

    let capture_path = tmp_dir.join("capture.txt");
    let targo_trust = install_targo_trust_binary(&bin_dir);
    write_executable(&bin_dir.join("trustc"), fake_trustc_script());
    write_executable(&bin_dir.join("targo"), fake_targo_script());
    let _trustd = fake_trustd::install(&bin_dir);

    let output = Command::new(targo_trust)
        .arg("check")
        .current_dir(&crate_dir)
        .env("TRUST_CAPTURE_FILE", &capture_path)
        .env_remove("CARGO")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .output()
        .expect("run targo-trust check with the policy fixture");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let capture = capture_path.exists().then(|| {
        let text = fs::read_to_string(&capture_path).expect("read fake targo capture");
        parse_targo_capture(&text)
    });

    let _ = fs::remove_dir_all(&tmp_dir);
    (capture, stdout, stderr, output.status.code())
}

fn fake_trustc_script() -> String {
    r#"#!/bin/sh
verification_session=
crate_name=fixture
previous=
for arg in "$@"; do
  if [ "$previous" = "--crate-name" ]; then
    crate_name="$arg"
  fi
  case "$arg" in
    trust-verify|trust-verify=*|trust-verify-full|trust-verify-full=*|trust-verify-target=*|trust-verify-crate-role=*|trust-verify-package-name=*)
      echo "raw compiler invocation carried retired activation/scope or Cargo-owned metadata: $arg" >&2
      exit 97
      ;;
    trust-verify-session=*) verification_session=${arg#trust-verify-session=} ;;
  esac
  previous="$arg"
done
{
  echo "kind=trustc"
  printf 'trustc_arg=%s\n' "$@"
} >> "$TRUST_CAPTURE_FILE"
if [ "${TRUST_FAKE_TRUSTC_NO_JSON_CAPABILITY:-0}" = "1" ] || [ "${TRUST_FAKE_TRUSTC_TEXT_ONLY_PROVED:-0}" = "1" ]; then
  echo 'note: Trust [test]: test -- PROVED (test, 0ms)' >&2
  exit 0
fi
if [ "$crate_name" = "trust_verify_probe" ]; then
  printf 'TRUST_JSON:{"type":"function_result","function":"trust_verify_probe::trust_verify_probe","package_name":null,"crate_name":"trust_verify_probe","primary_package":false,"verification_session":"%s","results":[],"proved":0,"failed":0,"unknown":0,"timed_out":0,"skipped":0,"runtime_checked":0,"cached":0,"total":0}\n' "$verification_session" >&2
  if [ "${TRUST_FAKE_LEGACY_COVERAGE:-0}" = "1" ]; then
    printf 'TRUST_JSON:{"type":"coverage_summary","crate_name":"%s","eligible":1,"processed":1}\n' "$crate_name" >&2
  else
    printf 'TRUST_JSON:{"type":"coverage_summary","crate_name":"trust_verify_probe","package_name":"","primary_package":false,"verification_session":"%s","eligible":1,"processed":1,"function_identities":{"schema":"trustc.coverage-function-identities.v1","eligible_functions":["trust_verify_probe::trust_verify_probe"],"processed_functions":["trust_verify_probe::trust_verify_probe"]}}\n' "$verification_session" >&2
  fi
  exit 0
fi
  payload=$(printf '%s' '__TRUST_DIRECT_PROVED_PAYLOAD__' | sed "s/__TRUST_VERIFICATION_SESSION__/$verification_session/g")
printf 'TRUST_JSON:%s\n' "$payload" >&2
if [ "${TRUST_FAKE_LEGACY_COVERAGE:-0}" = "1" ]; then
  printf 'TRUST_JSON:{"type":"coverage_summary","crate_name":"%s","eligible":1,"processed":1}\n' "$crate_name" >&2
else
  printf 'TRUST_JSON:{"type":"coverage_summary","crate_name":"%s","package_name":"","primary_package":false,"verification_session":"%s","eligible":1,"processed":1,"function_identities":{"schema":"trustc.coverage-function-identities.v1","eligible_functions":["fixture::test"],"processed_functions":["fixture::test"]}}\n' "$crate_name" "$verification_session" >&2
fi
if [ "${TRUST_FAKE_TRUSTC_CRATE_SUMMARY:-0}" = "1" ]; then
  printf 'TRUST_JSON:{"type":"crate_summary","package_name":null,"crate_name":"%s","primary_package":false,"verification_session":"%s","functions_analyzed":1,"functions_verified":1,"total_proved":1,"total_failed":0,"total_unknown":0,"total_timed_out":0,"total_skipped":0,"total_runtime_checked":0,"total_obligations":1}\n' "$crate_name" "$verification_session" >&2
fi
exit 0
"#
    .replace("__TRUST_DIRECT_PROVED_PAYLOAD__", &fake_direct_proved_payload())
}

fn fake_targo_script() -> String {
    r#"#!/bin/sh
outcome="${TRUST_FAKE_TARGO_OUTCOME:-proved}"
exit_code="${TRUST_FAKE_TARGO_EXIT:-0}"
package_name=$(sed -n 's/^name[[:space:]]*=[[:space:]]*"\([^"]*\)".*/\1/p' Cargo.toml | head -n 1)
crate_name=$(printf '%s' "$package_name" | tr '-' '_')
verification_session=$(printf '%s\n%s\n' "$RUSTFLAGS" "$CARGO_ENCODED_RUSTFLAGS" | tr '\037' ' ' | sed -n 's/.*trust-verify-session=\([^ ]*\).*/\1/p' | head -n 1)
manifest="$PWD/Cargo.toml"
source="$PWD/src/lib.rs"
package_id="path+file://$PWD#$package_name@0.0.0"
compile_target="test-host"
compile_mode="build"
compile_kind="target"
unit_identity_sha256="cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
unit_semantics='{"schema":"targo.trust-unit-semantics.v1","features":[],"target_cfg":["unix"],"cfg_test":false,"target_edition":"2024","target_crate_types":["rlib"],"target_harness":false,"target_proc_macro":false,"profile":{"opt_level":"0","requested_lto":"false","effective_lto":"only-object","debuginfo":"0","debug_assertions":false,"overflow_checks":false,"rpath":false,"incremental":false,"panic":"unwind","strip":"none","rustflags":[]},"compiler":{"frontend":"rustc","codegen_backend":"trust-cg","rustc_release":"1.99.0-nightly","rustc_host":"test-host","rustc_verbose_version_sha256":"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"},"unit_rustflags":["-Zcodegen-backend=trust-cg"],"manifest_lint_rustflags":[],"extra_compiler_args":[]}'
semantics_sha256="67fbdb2e7e098b6c27117b599ec42fc343d9b18b8a040b3f570e03e6da417f94"
proof_unit="{\"schema\":\"targo.trust-proof-unit.v2\",\"index\":0,\"mode\":\"$compile_mode\",\"role\":\"primary\",\"package_name\":\"$package_name\",\"semantics_sha256\":\"$semantics_sha256\"}"
mode=build
for arg in "$@"; do
  case "$arg" in
    metadata) mode=metadata ;;
    pkgid) mode=pkgid ;;
  esac
done
{
  echo "kind=targo"
  echo "program=$(basename "$0")"
  printf 'targo_arg=%s\n' "$@"
  echo "exported_rustc=$RUSTC"
  echo "rustflags=$RUSTFLAGS"
  echo "encoded_rustflags=$CARGO_ENCODED_RUSTFLAGS"
  echo "trust_no_verify=$TRUST_NO_VERIFY"
  echo "trust_hardened=$TRUST_HARDENED"
  echo "trust_profile=$TRUST_PROFILE"
  echo "trust_verify_memory_safe=$TRUST_VERIFY_MEMORY_SAFE"
  echo "trust_verify_survey=$TRUST_VERIFY_SURVEY"
} >> "$TRUST_CAPTURE_FILE"
if [ "$mode" = "metadata" ]; then
  printf '{"packages":[{"id":"%s","name":"%s","version":"0.0.0","manifest_path":"%s","targets":[{"kind":["lib"],"crate_types":["lib"],"name":"%s","src_path":"%s","edition":"2021","doc":true,"doctest":true,"test":true}]}],"workspace_members":["%s"],"workspace_default_members":["%s"],"workspace_root":"%s","target_directory":"%s/target","resolve":{"nodes":[{"id":"%s","deps":[]}]},"version":1}\n' \
    "$package_id" "$package_name" "$manifest" "$crate_name" "$source" "$package_id" "$package_id" "$PWD" "$PWD" "$package_id"
  exit 0
fi
if [ "$mode" = "pkgid" ]; then
  printf '%s\n' "$package_id"
  exit 0
fi

emit_transport() {
  escaped=$(printf '%s' "$1" | sed 's/\\/\\\\/g; s/"/\\"/g')
  printf '{"reason":"compiler-message","package_id":"%s","trust_compile_target":"%s","trust_compile_mode":"%s","trust_compile_kind":"%s","trust_unit_identity_sha256":"%s","trust_proof_unit":%s,"target":{"name":"%s","kind":["lib"]},"message":{"message":"TRUST_JSON:%s","level":"note","code":{"code":"trust_verification_transport_v1","explanation":null},"rendered":null,"spans":[],"children":[]}}\n' \
    "$package_id" "$compile_target" "$compile_mode" "$compile_kind" "$unit_identity_sha256" "$proof_unit" "$crate_name" "$escaped"
}
emit_summary() {
  summary=$(printf '{"type":"crate_summary","crate_name":"%s","package_name":"%s","primary_package":true,"verification_session":"%s","functions_analyzed":1,"functions_verified":%s,"total_proved":%s,"total_failed":0,"total_unknown":%s,"total_timed_out":0,"total_skipped":0,"total_runtime_checked":0,"total_obligations":1}' "$crate_name" "$package_name" "$verification_session" "$1" "$1" "$2")
  emit_transport "$summary"
}
emit_coverage() {
  if [ "${TRUST_FAKE_TARGO_NO_COVERAGE:-0}" != "1" ]; then
    if [ "${TRUST_FAKE_LEGACY_COVERAGE:-0}" = "1" ]; then
      coverage=$(printf '{"type":"coverage_summary","crate_name":"%s","eligible":1,"processed":1}' "$crate_name")
    else
      coverage_primary=true
      if [ "${TRUST_FAKE_TARGO_NON_PRIMARY_COVERAGE:-0}" = "1" ]; then
        coverage_primary=false
      fi
      coverage=$(printf '{"type":"coverage_summary","crate_name":"%s","package_name":"%s","primary_package":%s,"verification_session":"%s","eligible":1,"processed":1,"function_identities":{"schema":"trustc.coverage-function-identities.v1","eligible_functions":["%s"],"processed_functions":["%s"]}}' "$crate_name" "$package_name" "$coverage_primary" "$verification_session" "$1" "$1")
    fi
    emit_transport "$coverage"
  fi
}
emit_artifact() {
  printf '{"reason":"compiler-artifact","package_id":"%s","trust_compile_target":"%s","trust_compile_mode":"%s","trust_compile_kind":"%s","trust_unit_identity_sha256":"%s","trust_proof_unit":%s,"target":{"name":"%s","kind":["lib"]},"profile":{"opt_level":"0","debuginfo":0,"debug_assertions":false,"overflow_checks":false,"test":false},"features":[],"fresh":false}\n' \
    "$package_id" "$compile_target" "$compile_mode" "$compile_kind" "$unit_identity_sha256" "$proof_unit" "$crate_name"
  printf '{"reason":"build-finished","success":true}\n'
}
printf '{"reason":"trust-proof-inventory","schema":"targo.trust-proof-inventory.v2","include_dependencies":true,"units":[{"trust_proof_unit":%s,"semantics":%s,"package_id":"%s","target_name":"%s","target_kinds":["lib"],"compile_target":"%s","trust_compile_mode":"%s","trust_compile_kind":"%s","trust_unit_identity_sha256":"%s"}],"excluded_units":[]}\n' \
  "$proof_unit" "$unit_semantics" "$package_id" "$crate_name" "$compile_target" "$compile_mode" "$compile_kind" "$unit_identity_sha256"
if [ "${TRUST_FAKE_TARGO_TEXT_ONLY_PROVED:-0}" = "1" ]; then
  echo 'note: Trust [test]: test -- PROVED (test, 0ms)' >&2
  exit "$exit_code"
fi
if [ "${TRUST_FAKE_TARGO_FULL_VERIFIER_EVIDENCE:-0}" = "1" ]; then
  payload=$(printf '%s' '__TRUST_FULL_VERIFIER_PAYLOAD__' | sed "s/__TRUST_VERIFICATION_SESSION__/$verification_session/g")
  emit_transport "$payload"
  emit_coverage "$crate_name::unsafe_owner"
  emit_summary 1 0
  emit_artifact
  exit "$exit_code"
fi
kind=test
result_outcome="$outcome"
solver=test
if [ "$outcome" = "proved" ]; then
  proved=1
  unknown=0
elif [ "$outcome" = "assumption" ]; then
  kind=assumption:test
  result_outcome=unknown
  proved=0
  unknown=1
else
  proved=0
  unknown=1
fi
if [ "$outcome" = "assumption" ] && [ "${TRUST_FAKE_TARGO_UNMARKED_ASSUMPTION:-0}" != "1" ]; then
  case "$RUSTFLAGS$CARGO_ENCODED_RUSTFLAGS" in
    *trust-policy=memory-safe*)
      solver=trust-memory-safe
      kind=assumption:memory-safe-panic
      ;;
  esac
fi
if [ "$outcome" = "proved" ]; then
  payload=$(printf '%s' '__TRUST_PROVED_PAYLOAD__' | sed "s/__TRUST_CRATE_NAME__/$crate_name/g; s/__TRUST_PACKAGE_NAME__/$package_name/g; s/__TRUST_VERIFICATION_SESSION__/$verification_session/g")
  function_identity="fixture::test"
else
  payload=$(printf '{"type":"function_result","function":"%s::test","package_name":"%s","crate_name":"%s","primary_package":true,"verification_session":"%s","results":[{"kind":"%s","description":"test","outcome":"%s","solver":"%s","time_ms":0}],"proved":%s,"failed":0,"unknown":%s,"timed_out":0,"skipped":0,"runtime_checked":0,"cached":0,"total":1}' "$crate_name" "$package_name" "$crate_name" "$verification_session" "$kind" "$result_outcome" "$solver" "$proved" "$unknown")
  function_identity="$crate_name::test"
fi
emit_transport "$payload"
emit_coverage "$function_identity"
emit_summary "$proved" "$unknown"
emit_artifact
exit "$exit_code"
"#
    .replace("__TRUST_FULL_VERIFIER_PAYLOAD__", &fake_full_verifier_payload())
    .replace("__TRUST_PROVED_PAYLOAD__", &fake_proved_payload())
}

fn fake_proved_payload() -> String {
    const CRATE_NAME: &str = "__TRUST_CRATE_NAME__";
    const PACKAGE_NAME: &str = "__TRUST_PACKAGE_NAME__";
    const SESSION_PLACEHOLDER: &str = "__TRUST_VERIFICATION_SESSION__";

    let function = "fixture::test".to_string();
    let result = publication_transport::proved_result(
        trust_types::VcKind::Assertion { message: "test".to_string() },
        &function,
        "test-req-1",
        "1",
    );
    let message =
        trust_types::TransportMessage::FunctionResult(trust_types::FunctionTransportResult {
            function,
            package_name: Some(PACKAGE_NAME.to_string()),
            crate_name: Some(CRATE_NAME.to_string()),
            primary_package: true,
            verification_session: SESSION_PLACEHOLDER.to_string(),
            results: vec![result],
            proved: 1,
            failed: 0,
            unknown: 0,
            timed_out: 0,
            skipped: 0,
            runtime_checked: 0,
            cached: 0,
            total: 1,
        });
    let payload = serde_json::to_string(&message).expect("serialize fake proved payload");
    assert!(
        !payload.contains('\''),
        "payload must remain safe for the shell single-quoted literal"
    );
    payload
}

fn fake_direct_proved_payload() -> String {
    const CRATE_NAME: &str = "fixture";
    const SESSION_PLACEHOLDER: &str = "__TRUST_VERIFICATION_SESSION__";

    let function = "fixture::test".to_string();
    let result = publication_transport::proved_result(
        trust_types::VcKind::Assertion { message: "test".to_string() },
        &function,
        "test-req-1",
        "1",
    );
    let message =
        trust_types::TransportMessage::FunctionResult(trust_types::FunctionTransportResult {
            function,
            package_name: None,
            crate_name: Some(CRATE_NAME.to_string()),
            primary_package: false,
            verification_session: SESSION_PLACEHOLDER.to_string(),
            results: vec![result],
            proved: 1,
            failed: 0,
            unknown: 0,
            timed_out: 0,
            skipped: 0,
            runtime_checked: 0,
            cached: 0,
            total: 1,
        });
    let payload = serde_json::to_string(&message).expect("serialize fake direct proved payload");
    assert!(
        !payload.contains('\''),
        "payload must remain safe for the shell single-quoted literal"
    );
    payload
}

fn fake_full_verifier_payload() -> String {
    const CRATE_NAME: &str = "unsafe_memory_wrapper_fixture";
    const PACKAGE_NAME: &str = "unsafe-memory-wrapper-fixture";
    const REQUEST_ID: &str = "unsafe-req-1";
    const PROOF_ID: &str = "unsafe-proof-1";
    const SESSION_PLACEHOLDER: &str = "__TRUST_VERIFICATION_SESSION__";

    let function = format!("{CRATE_NAME}::unsafe_owner");
    let result = publication_transport::proved_result(
        trust_types::VcKind::UnsafeOperation {
            desc: "unsafe memory operation is proved".to_string(),
        },
        &function,
        REQUEST_ID,
        PROOF_ID,
    );
    let message =
        trust_types::TransportMessage::FunctionResult(trust_types::FunctionTransportResult {
            function,
            package_name: Some(PACKAGE_NAME.to_string()),
            crate_name: Some(CRATE_NAME.to_string()),
            primary_package: true,
            verification_session: SESSION_PLACEHOLDER.to_string(),
            results: vec![result],
            proved: 1,
            failed: 0,
            unknown: 0,
            timed_out: 0,
            skipped: 0,
            runtime_checked: 0,
            cached: 0,
            total: 1,
        });
    let payload = serde_json::to_string(&message).expect("serialize fake full-verifier payload");
    assert!(
        !payload.contains('\''),
        "payload must remain safe for the shell single-quoted literal"
    );
    payload
}

fn write_executable(path: &Path, contents: impl AsRef<[u8]>) {
    fs::write(path, contents).expect("write fake executable");
    let mut permissions = fs::metadata(path).expect("fake executable metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).expect("chmod fake executable");
}

fn parse_targo_capture(capture: &str) -> CapturedTCargoInvocation {
    let mut in_targo = false;
    let mut program = None;
    let mut args = Vec::new();
    let mut exported_rustc = None;
    let mut rustflags = None;
    let mut encoded_rustflags = None;
    let mut trust_no_verify = None;
    let mut trust_hardened = None;
    let mut trust_profile = None;
    let mut trust_verify_memory_safe = None;
    let mut trust_verify_survey = None;

    for line in capture.lines() {
        if line == "kind=targo" {
            in_targo = true;
            continue;
        }
        if line.starts_with("kind=") {
            in_targo = false;
            continue;
        }
        if !in_targo {
            continue;
        }

        if let Some(value) = line.strip_prefix("program=") {
            program = Some(value.to_string());
        } else if let Some(arg) = line.strip_prefix("targo_arg=") {
            args.push(arg.to_string());
        } else if let Some(value) = line.strip_prefix("exported_rustc=") {
            exported_rustc = Some(value.to_string());
        } else if let Some(value) = line.strip_prefix("rustflags=") {
            rustflags = Some(value.to_string());
        } else if let Some(value) = line.strip_prefix("encoded_rustflags=") {
            encoded_rustflags = Some(value.to_string());
        } else if let Some(value) = line.strip_prefix("trust_no_verify=") {
            trust_no_verify = Some(value.to_string());
        } else if let Some(value) = line.strip_prefix("trust_hardened=") {
            trust_hardened = Some(value.to_string());
        } else if let Some(value) = line.strip_prefix("trust_profile=") {
            trust_profile = Some(value.to_string());
        } else if let Some(value) = line.strip_prefix("trust_verify_memory_safe=") {
            trust_verify_memory_safe = Some(value.to_string());
        } else if let Some(value) = line.strip_prefix("trust_verify_survey=") {
            trust_verify_survey = Some(value.to_string());
        }
    }

    CapturedTCargoInvocation {
        program: program.expect("fake targo capture should include program name"),
        args,
        exported_rustc: exported_rustc.unwrap_or_default(),
        rustflags_env: rustflags.expect("fake targo capture should include RUSTFLAGS"),
        encoded_rustflags_env: encoded_rustflags.unwrap_or_default(),
        trust_no_verify: trust_no_verify.unwrap_or_default(),
        trust_hardened: trust_hardened.unwrap_or_default(),
        trust_profile: trust_profile.unwrap_or_default(),
        trust_verify_memory_safe: trust_verify_memory_safe.unwrap_or_default(),
        trust_verify_survey: trust_verify_survey.unwrap_or_default(),
    }
}

fn capture_has_z_flag(capture: &CapturedTCargoInvocation, flag: &str) -> bool {
    let rustflags = capture.rustflags_env.split_whitespace().collect::<Vec<_>>();
    let encoded = capture
        .encoded_rustflags_env
        .split('\x1f')
        .filter(|arg| !arg.is_empty())
        .collect::<Vec<_>>();

    has_z_flag(&rustflags, flag) || has_z_flag(&encoded, flag)
}

fn capture_has_z_option_prefix(capture: &CapturedTCargoInvocation, prefix: &str) -> bool {
    let rustflags = capture.rustflags_env.split_whitespace().collect::<Vec<_>>();
    let encoded = capture
        .encoded_rustflags_env
        .split('\x1f')
        .filter(|arg| !arg.is_empty())
        .collect::<Vec<_>>();
    has_z_option_prefix(&rustflags, prefix) || has_z_option_prefix(&encoded, prefix)
}

fn capture_codegen_option_values(capture: &CapturedTCargoInvocation, name: &str) -> Vec<String> {
    let args = if capture.encoded_rustflags_env.is_empty() {
        capture.rustflags_env.split_whitespace().collect::<Vec<_>>()
    } else {
        capture
            .encoded_rustflags_env
            .split('\x1f')
            .filter(|argument| !argument.is_empty())
            .collect::<Vec<_>>()
    };
    let prefix = format!("{name}=");
    let mut values = Vec::new();
    let mut index = 0;
    while index < args.len() {
        let option = if args[index] == "-C" {
            index += 1;
            args.get(index).copied()
        } else {
            args[index].strip_prefix("-C").filter(|option| !option.is_empty())
        };
        if let Some(value) = option.and_then(|option| option.strip_prefix(&prefix)) {
            values.push(value.to_string());
        }
        index += 1;
    }
    values
}

fn parse_trustc_invocations(capture: &str) -> Vec<Vec<String>> {
    let mut invocations = Vec::new();
    let mut current: Option<Vec<String>> = None;
    for line in capture.lines() {
        if line == "kind=trustc" {
            if let Some(args) = current.replace(Vec::new()) {
                invocations.push(args);
            }
        } else if line.starts_with("kind=") {
            if let Some(args) = current.take() {
                invocations.push(args);
            }
        } else if let (Some(args), Some(argument)) =
            (current.as_mut(), line.strip_prefix("trustc_arg="))
        {
            args.push(argument.to_string());
        }
    }
    if let Some(args) = current {
        invocations.push(args);
    }
    invocations
}

fn codegen_option_values(args: &[String], name: &str) -> Vec<String> {
    let prefix = format!("{name}=");
    let mut values = Vec::new();
    let mut index = 0;
    while index < args.len() {
        let option = if args[index] == "-C" {
            index += 1;
            args.get(index).map(String::as_str)
        } else {
            args[index].strip_prefix("-C").filter(|option| !option.is_empty())
        };
        if let Some(value) = option.and_then(|option| option.strip_prefix(&prefix)) {
            values.push(value.to_string());
        }
        index += 1;
    }
    values
}

fn has_z_option_prefix(args: &[&str], prefix: &str) -> bool {
    args.windows(2).any(|pair| pair[0] == "-Z" && pair[1].starts_with(prefix))
        || args
            .iter()
            .any(|arg| arg.strip_prefix("-Z").is_some_and(|option| option.starts_with(prefix)))
}

fn has_z_flag(args: &[&str], flag: &str) -> bool {
    let compact = format!("-Z{flag}");
    args.windows(2).any(|pair| pair[0] == "-Z" && pair[1] == flag)
        || args.iter().any(|arg| *arg == compact.as_str())
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

fn install_targo_trust_binary(bin_dir: &Path) -> PathBuf {
    let path = bin_dir.join(format!("targo-trust{}", std::env::consts::EXE_SUFFIX));
    fs::copy(targo_trust_binary(), &path).expect("copy targo-trust into fake Trust root");
    let mut permissions = fs::metadata(&path).expect("targo-trust metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&path, permissions).expect("chmod targo-trust");
    path
}

fn temp_test_dir(prefix: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock after Unix epoch")
        .as_nanos();
    std::env::temp_dir().join(format!("{prefix}-{}-{nanos}", std::process::id()))
}

fn init_clean_git_repo(repo: &Path) {
    // Match an ordinary Cargo repository: observational verification snapshots
    // live below `target/` and must not make the source tree dirty before the
    // exact-report evidence gate inspects it.
    fs::write(repo.join(".gitignore"), "/target/\n").expect("write fixture gitignore");
    run_git(repo, &["init"]);
    run_git(repo, &["config", "user.email", "trust-tests@example.invalid"]);
    run_git(repo, &["config", "user.name", "Trust Tests"]);
    run_git(repo, &["add", "."]);
    run_git(repo, &["commit", "-m", "fixture"]);
}

fn git_stdout(repo: &Path, args: &[&str]) -> String {
    let output = git_output(repo, args);
    assert!(
        output.status.success(),
        "git {} failed\nstdout:\n{}\nstderr:\n{}",
        args.join(" "),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).trim().to_string()
}

fn run_git(repo: &Path, args: &[&str]) {
    let output = git_output(repo, args);
    assert!(
        output.status.success(),
        "git {} failed\nstdout:\n{}\nstderr:\n{}",
        args.join(" "),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn git_output(repo: &Path, args: &[&str]) -> std::process::Output {
    Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(args)
        .output()
        .unwrap_or_else(|error| panic!("run git {}: {error}", args.join(" ")))
}

fn file_sha256(path: &Path) -> String {
    let bytes = fs::read(path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hex_digest(hasher.finalize().as_slice())
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
