#![cfg(unix)]

use std::fs;
use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::Value;
use sha2::{Digest, Sha256};

#[path = "support/compiler_overrides.rs"]
mod compiler_overrides;
#[path = "support/fake_trustd.rs"]
mod fake_trustd;
#[path = "support/publication_transport.rs"]
mod publication_transport;

fn create_fixture_dir(path: &Path) {
    // These directories contain the selected trustd executable. Every new
    // ancestor must satisfy its private-package check, independent of umask.
    fs::DirBuilder::new()
        .recursive(true)
        .mode(0o700)
        .create(path)
        .expect("create private fixture directory");
}

fn fixture_command(program: &Path) -> Command {
    let mut command = Command::new(program);
    // The fixture selects its own sibling trustc. Compiler settings used to
    // build this test must not override that selection; individual controls
    // can still inject an override after this fixture setup.
    compiler_overrides::remove_inherited_compiler_overrides(&mut command);
    // The fake targo honours it as Cargo does; a test that wants one (the
    // stability verb's legs) sets it, and the runner's own never leaks in.
    command.env_remove("CARGO_TARGET_DIR");
    command
}

#[derive(Debug)]
struct CapturedTCargoInvocation {
    program: String,
    args: Vec<String>,
    exported_rustc: String,
    rustflags_env: String,
    encoded_rustflags_env: String,
    /// `TRUST_TARGO_LANE_RUSTFLAGS`: the lane targo trust hands Cargo, which
    /// the sibling Targo appends to the project's own flags (T14a).
    lane_env: String,
    trust_no_verify: String,
    trust_hardened: String,
    trust_profile: String,
    trust_verify_memory_safe: String,
    trust_verify_survey: String,
}

#[test]
fn workspace_selector_precedes_forwarded_cargo_arguments() {
    for child_argument in ["--nocapture", "--workspace", "--all"] {
        let toolchain = SharedFakeToolchain::install("targo-trust-workspace-separator");
        let crate_dir = toolchain.fixture_crate("ws", "workspace-separator-fixture");
        let (stdout, stderr, status) =
            toolchain.run(&crate_dir, &["check", "--all", "--", "--", child_argument], &[]);
        assert_eq!(status, Some(0), "stdout:\n{stdout}\nstderr:\n{stderr}");
        let capture = fs::read_to_string(toolchain.tmp_dir.join("capture.txt"))
            .expect("read actual child invocations");
        let compile = capture
            .split("kind=targo\n")
            .find(|invocation| invocation.starts_with("targo_mode=build\n"))
            .expect("actual compile invocation");
        let args: Vec<_> =
            compile.lines().filter_map(|line| line.strip_prefix("targo_arg=")).collect();
        let separator = args.iter().position(|arg| *arg == "--").expect("Cargo separator");
        assert_eq!(
            args[..separator].iter().filter(|arg| **arg == "--workspace").count(),
            1,
            "Cargo must select the workspace before its child arguments: {args:?}"
        );
        assert_eq!(&args[separator + 1..], &[child_argument]);
    }
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
fn explicit_compiler_overrides_are_rejected_before_targo() {
    for key in [
        "RUSTC",
        "CARGO_BUILD_RUSTC",
        "RUSTC_WRAPPER",
        "CARGO_BUILD_RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
    ] {
        let (capture, stdout, stderr, status) =
            run_targo_trust_check_with_fake_toolchain_maybe_capture(
                "targo-trust-explicit-compiler-override",
                &[],
                &[(key, "/unselected/fixture-compiler")],
            );
        assert_eq!(status, Some(2), "{key}: stdout:\n{stdout}\nstderr:\n{stderr}");
        assert!(stderr.contains(&format!("{key} is set")), "{key}: {stderr}");
        assert!(capture.is_none(), "{key}: rejected override must not invoke Targo");
    }
}

#[test]
fn strict_single_file_invokes_fake_trustc_with_one_canonical_safety_policy() {
    let tmp_dir = temp_test_dir("targo-trust-direct-safety-policy");
    let source_dir = tmp_dir.join("source");
    let bin_dir = tmp_dir.join("toolchain").join("bin");
    create_fixture_dir(&source_dir);
    create_fixture_dir(&bin_dir);
    let source = source_dir.join("fixture.rs");
    fs::write(&source, "pub fn add(a: usize, b: usize) -> usize { a + b }\n")
        .expect("write fixture source");

    let capture_path = tmp_dir.join("capture.txt");
    let targo_trust = install_targo_trust_binary(&bin_dir);
    write_executable(&bin_dir.join("trustc"), fake_trustc_script());
    write_executable(&bin_dir.join("ay"), "#!/bin/sh\nprintf 'ay 0.0.0\\n'\n");

    let output = fixture_command(&targo_trust)
        .arg("check")
        .arg(&source)
        // Equivalent true spellings are accepted, removed, and replaced with
        // one canonical pair at the end of the actual trustc argv.
        .arg("-Coverflow-checks=true")
        .args(["-C", "debug-assertions=on"])
        .current_dir(&source_dir)
        .env("TRUST_CAPTURE_FILE", &capture_path)
        .env("CARGO_HOME", tmp_dir.join("cargo-home"))
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
    let rejected = fixture_command(&targo_trust)
        .arg("check")
        .arg(&source)
        .arg("-Coverflow-checks=no")
        .current_dir(&source_dir)
        .env("TRUST_CAPTURE_FILE", &capture_path)
        .env("CARGO_HOME", tmp_dir.join("cargo-home"))
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
    create_fixture_dir(&src_dir);
    create_fixture_dir(&bin_dir);

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

    let output = fixture_command(&targo_trust)
        .args(["report", "--unsafe-memory"])
        .current_dir(&crate_dir)
        .env(fake_trustd::RUNTIME_DIR_ENV, _trustd.runtime_dir())
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

    // Drop the guard FIRST: it shuts the stub down on its private endpoint and
    // removes that runtime directory while the stub's executable (in tmp_dir)
    // still exists.
    drop(_trustd);
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

/// DECISION_QUEUE T7a: TRUSTFLAGS is not read. Every option it used to carry,
/// in both spellings and including values it used to refuse outright, is
/// ignored with ONE notice naming it; the compile runs the lane, profile and
/// level the command line and the project resolved, and the run is neither
/// refused nor silently different. Before T7a this exact environment was a
/// setup error (exit 2) naming the policy conflict.
#[test]
fn an_ambient_trustflags_is_ignored_with_one_notice() {
    let ambient = "-Ztrust-policy=advisory -Ztrust-verify-profile=default \
                   -Ztrust-verify-level=0 -Ztrust-verify-worker-threads=1 \
                   -Ztrust-ir-lower=strict -Ztrust-verify-include-dependencies=yes \
                   -Ztrust-verify-effort=1 -Ztrust-verify-session=forged -Copt-level=3";
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-ambient-trustflags-ignored",
        &[],
        &[("TRUSTFLAGS", ambient), ("CARGO_ENCODED_TRUSTFLAGS", "-Z\x1ftrust-policy=memory-safe")],
    );
    assert_eq!(
        status,
        Some(0),
        "an ambient TRUSTFLAGS is ignored, never a refusal\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        stderr.matches("ignored: targo trust no longer reads TRUSTFLAGS").count(),
        1,
        "exactly one notice\n{stderr}"
    );
    assert!(
        stderr.contains("TRUSTFLAGS=\"-Ztrust-policy=advisory")
            && stderr.contains("CARGO_ENCODED_TRUSTFLAGS=\"-Z trust-policy=memory-safe\""),
        "the notice names what it ignored\n{stderr}"
    );
    assert!(stderr.contains("--worker-threads") && stderr.contains("--config"), "{stderr}");
    // The compile is the one the command line resolved: the strict lane, the
    // default hardened profile, level 2, and nothing TRUSTFLAGS named.
    for absent in [
        "trust-policy=advisory",
        "trust-policy=memory-safe",
        "trust-verify-profile=default",
        "trust-verify-level=0",
        "trust-ir-lower=strict",
        "trust-verify-include-dependencies=yes",
        "trust-verify-effort=1",
        "trust-verify-session=forged",
    ] {
        assert!(!capture_has_z_flag(&capture, absent), "{absent} reached the compile: {capture:?}");
    }
    assert!(!capture_has_z_option_prefix(&capture, "trust-verify-worker-threads="), "{capture:?}");
    assert_eq!(capture_z_flag_values(&capture, "trust-verify-profile"), ["unix_hardened"]);
    assert_eq!(capture_z_flag_values(&capture, "trust-verify-level"), ["2"]);
    assert!(
        stderr.contains("hardened profile `unix_hardened` enabled"),
        "the banner names the profile the compile ran\n{stderr}"
    );

    // An empty TRUSTFLAGS selects nothing and is not named.
    let (_, _, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-empty-trustflags",
        &[],
        &[("TRUSTFLAGS", "")],
    );
    assert_eq!(status, Some(0), "{stderr}");
    assert!(!stderr.contains("TRUSTFLAGS"), "{stderr}");
}

/// T7a: the strict-gate scripts selected certify as `TRUSTFLAGS=-Ztrust-policy=certify`;
/// they now pass `--certify`. That flag puts the compiler's `certify` policy on
/// the compile exactly once and the Gate line names the certify lane, while the
/// old spelling alone selects nothing: the run stays on the strict lane.
#[test]
fn the_certify_lane_the_strict_gates_select_reaches_the_compiler() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-certify-flag-route",
        &["--certify"],
        &[],
    );
    let text = format!("{stdout}\n{stderr}");
    assert_eq!(status, Some(0), "{text}");
    assert_eq!(capture_z_flag_values(&capture, "trust-policy"), ["certify"], "{capture:?}");
    assert!(text.contains("Gate: PASS [certify lane, exit 0]"), "{text}");

    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-certify-trustflags-route",
        &[],
        &[("TRUSTFLAGS", "-Ztrust-policy=certify")],
    );
    let text = format!("{stdout}\n{stderr}");
    assert_eq!(status, Some(0), "{text}");
    assert!(capture_z_flag_values(&capture, "trust-policy").is_empty(), "{capture:?}");
    assert!(text.contains("Gate: PASS [strict lane, exit 0]"), "{text}");
    assert!(text.contains("ignored: targo trust no longer reads TRUSTFLAGS"), "{text}");
}

/// T7a: the worker-thread cap TRUSTFLAGS used to carry is `--worker-threads`.
/// It reaches the compiler once, and the published budget profile records
/// the same count; without the flag nothing is passed and the record is 0.
#[test]
fn the_worker_thread_cap_reaches_the_compiler_from_the_command_line() {
    for (label, cli, expected) in [
        ("targo-trust-worker-threads-serial", &["--worker-threads", "1"][..], Some("1")),
        ("targo-trust-worker-threads-joined", &["--worker-threads=4"][..], Some("4")),
        ("targo-trust-worker-threads-default", &[][..], None),
    ] {
        let report_dir = temp_test_dir(&format!("{label}-report"));
        let report_dir_arg = report_dir.to_string_lossy().into_owned();
        let mut args = cli.to_vec();
        args.extend(["--report-dir", report_dir_arg.as_str()]);
        let (capture, stdout, stderr, status) =
            run_targo_trust_check_with_fake_toolchain_args_env(label, &args, &[]);
        assert_eq!(status, Some(0), "{label}\nstdout:\n{stdout}\nstderr:\n{stderr}");
        assert_eq!(
            capture_z_flag_values(&capture, "trust-verify-worker-threads"),
            expected.map(str::to_string).into_iter().collect::<Vec<_>>(),
            "{label}: {capture:?}"
        );
        let report = fs::read_to_string(report_dir.join("report.json")).unwrap_or_else(|error| {
            panic!("{label}: report.json missing ({error})\nstderr:\n{stderr}")
        });
        let json: Value = serde_json::from_str(&report).expect("report.json parses");
        let recorded =
            &json["verification_gate"]["determinism"]["budget_profile"]["worker_threads"];
        assert_eq!(
            recorded.as_u64(),
            Some(expected.map_or(0, |count| count.parse::<u64>().unwrap())),
            "{label}: the profile records the count the compiler got: {recorded}"
        );
        let _ = fs::remove_dir_all(&report_dir);
    }

    let (capture, _, stderr, status) = run_targo_trust_check_with_fake_toolchain_maybe_capture(
        "targo-trust-worker-threads-out-of-domain",
        &["--worker-threads", "257"],
        &[],
    );
    assert_eq!(status, Some(2), "{stderr}");
    assert!(stderr.contains("from 0 through 256"), "{stderr}");
    assert!(capture.is_none(), "no compile under a refused flag: {capture:?}");
}

/// D21: proc macros of a verified unit expand in the isolated worker unless
/// the run says otherwise. The lane names the option only to turn it off:
/// Targo adds the positive form to each unit whose host has the sandbox, so a
/// default lane carries no value, and `--no-proc-macro-isolation` carries
/// exactly one `no`, on the certify lane as on the strict one.
#[test]
fn proc_macro_isolation_is_turned_off_only_from_the_command_line() {
    for (label, cli, expected) in [
        ("targo-trust-proc-macro-isolation-default", &[][..], None),
        ("targo-trust-proc-macro-isolation-off", &["--no-proc-macro-isolation"][..], Some("no")),
        (
            "targo-trust-proc-macro-isolation-off-certify",
            &["--certify", "--no-proc-macro-isolation"][..],
            Some("no"),
        ),
    ] {
        let (capture, stdout, stderr, status) =
            run_targo_trust_check_with_fake_toolchain_args_env(label, cli, &[]);
        assert_eq!(status, Some(0), "{label}\nstdout:\n{stdout}\nstderr:\n{stderr}");
        assert_eq!(
            capture_z_flag_values(&capture, "trust-proc-macro-isolation"),
            expected.map(str::to_string).into_iter().collect::<Vec<_>>(),
            "{label}: {capture:?}"
        );
        assert!(
            !capture_has_z_flag(&capture, "trust-proc-macro-isolation"),
            "{label}: the lane never spells the bare option: {capture:?}"
        );
    }
}

/// T7a: a tightening TRUSTFLAGS used to carry (a dependency scope, a strict
/// lowering, a restated level) is Cargo configuration. The project-policy
/// query answers with it, the run discloses it, and targo carries each
/// requirement to the compile exactly once.
#[test]
fn a_cargo_configuration_tightening_reaches_the_compiler() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-project-tightening",
        &[],
        &[(
            "TRUST_FAKE_PROJECT_POLICY",
            r#"{"schema":"trust.project-policy.v1","policy":null,"level":2,"profile":null,"include_dependencies":true,"ir_lower":"strict","verification_required":false}"#,
        )],
    );
    assert_eq!(status, Some(0), "stdout:\n{stdout}\nstderr:\n{stderr}");
    assert!(
        stderr.contains(
            "Cargo project configuration requirements adopted for this run: level=L2, \
             include-dependencies=yes, ir-lower=strict"
        ),
        "{stderr}"
    );
    assert_eq!(capture_z_flag_values(&capture, "trust-verify-include-dependencies"), ["yes"]);
    assert_eq!(capture_z_flag_values(&capture, "trust-ir-lower"), ["strict"]);
    assert_eq!(capture_z_flag_values(&capture, "trust-verify-level"), ["2"]);

    // A loosening is refused before any compile, naming no TRUSTFLAGS route.
    let (capture, _, stderr, status) = run_targo_trust_check_with_fake_toolchain_maybe_capture(
        "targo-trust-project-loosening",
        &[],
        &[(
            "TRUST_FAKE_PROJECT_POLICY",
            r#"{"schema":"trust.project-policy.v1","policy":null,"level":null,"profile":null,"include_dependencies":null,"ir_lower":"off","verification_required":false}"#,
        )],
    );
    assert_eq!(status, Some(2), "{stderr}");
    assert!(stderr.contains("requires -Ztrust-ir-lower=off"), "{stderr}");
    assert!(stderr.contains("no per-run selection lowers it"), "{stderr}");
    assert!(capture.is_none(), "{capture:?}");
}

/// T7a: a level below the resolved one is `[trust] level`, and nothing
/// else: the configured level reaches the compiler, and a TRUSTFLAGS level
/// beside it is ignored, not checked.
#[test]
fn a_lower_level_is_the_trust_tables_alone() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_policy_env(
        "targo-trust-level-from-table",
        Some("level = \"L1\"\n"),
        None,
        &[("TRUSTFLAGS", "-Ztrust-verify-level=2")],
    );
    assert_eq!(status, Some(0), "stdout:\n{stdout}\nstderr:\n{stderr}");
    let capture = capture.expect("fake targo ran");
    assert_eq!(
        capture_z_flag_values(&capture, "trust-verify-level"),
        vec!["1".to_string()],
        "exactly one level reaches the compiler, the configured one"
    );
    assert!(stderr.contains("ignored: targo trust no longer reads TRUSTFLAGS"), "{stderr}");
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

    // T14a: the caller's encoded flags reach Cargo exactly as the caller set
    // them, and no plain RUSTFLAGS is invented; the sibling Targo resolves
    // them, drops the safety overrides the lane owns (with a notice), and
    // appends the lane, which carries the level and the forced checks.
    assert_eq!(capture.rustflags_env, "", "targo-trust must not invent a plain RUSTFLAGS");
    assert_eq!(
        capture.encoded_rustflags_env,
        "-C\x1fdebuginfo=1\x1f-Coverflow-checks=no\x1f-C\x1fdebug-assertions=off",
        "inherited encoded flags must reach Cargo unchanged: {capture:?}"
    );
    assert!(!capture_has_z_flag(&capture, "trust-verify-full"));
    assert!(!capture_has_z_flag(&capture, "trust-verify"));
    assert!(
        capture_lane_args(&capture).iter().any(|arg| arg.starts_with("trust-verify-level=")),
        "the lane must configure the verification level: {capture:?}"
    );
    assert_eq!(capture_codegen_option_values(&capture, "overflow-checks"), ["yes"]);
    assert_eq!(capture_codegen_option_values(&capture, "debug-assertions"), ["yes"]);
}

/// The load sensitivity behind a one-off failure of the test above (exit
/// status assertion in a 324 s loaded full run; it passes alone in 5 s), and
/// of `trust_profile_sets_tracked_hardened_options` on 2026-09-29 at load
/// average 60: "did not establish exact-identity readiness within 5s". When
/// `targo trust check` had to spawn the fake trustd itself, its spawn path
/// gave the Python stub SPAWN_READY_TIMEOUT (5 s) to become ready. Here the
/// stub is made slower than that on purpose, standing in for a host too loaded
/// to start it in time: the check must still complete, because the harness
/// starts the stub and waits for it to serve before the command runs.
#[test]
fn fake_toolchain_check_does_not_race_the_trustd_spawn_deadline() {
    let (capture, stdout, stderr, status) =
        run_targo_trust_check_with_fake_toolchain_and_stub_delay(
            "targo-trust-slow-stub",
            &[],
            &[],
            Some(7),
        );
    assert_eq!(
        status,
        Some(0),
        "a stub slower than the spawn deadline must not fail the check\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(capture.is_some(), "the check must reach Cargo\nstdout:\n{stdout}\nstderr:\n{stderr}");
}

/// `install` returns a stub that already serves on the private endpoint as
/// exactly the installed bytes, which is what lets the command under test reuse
/// it instead of spawning one under a deadline.
#[test]
fn fake_trustd_install_returns_a_serving_stub() {
    let tmp_dir = temp_test_dir("targo-trust-fake-trustd-ready");
    let bin_dir = tmp_dir.join("toolchain").join("bin");
    create_fixture_dir(&bin_dir);
    let guard = fake_trustd::install(&bin_dir);
    let serving = trust_router::coordinator::daemon_matches_executable(
        guard.socket(),
        &bin_dir.join("trustd"),
    );
    let socket = guard.socket().to_path_buf();
    drop(guard);
    let _ = fs::remove_dir_all(&tmp_dir);
    assert!(serving, "fake_trustd::install returned before its stub served {}", socket.display());
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

// Ramp (2026-09-07): the advisory lane reports an unknown instead of failing
// on it. Same fake toolchain and the same unknown row as the strict test above,
// plus `--allow-l0-gaps`: exit 0, a conditional pass whose conditions NAME the
// unproved obligation on the `Result:` line, the Gate line and its note, and the
// flag recorded in report.json. The strict twin keeps exit 1.
#[test]
fn allow_l0_gaps_reports_unknown_transport_as_a_conditional_pass() {
    let report_dir = temp_test_dir("targo-trust-ramp-unknown-report");
    let report_dir_arg = report_dir.to_string_lossy().into_owned();
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-ramp-unknown-transport",
        &["--allow-l0-gaps", "--report-dir", &report_dir_arg],
        &[("TRUST_FAKE_TARGO_OUTCOME", "unknown")],
    );
    assert_eq!(
        status,
        Some(0),
        "the ramp must exit 0 on an unproved obligation\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        capture_has_z_flag(&capture, "trust-policy=advisory"),
        "--allow-l0-gaps must select the advisory verifier policy: {capture:?}"
    );
    let text = format!("{stdout}\n{stderr}");
    assert!(
        text.contains("Result: PASS (conditional: 1 unproved"),
        "the Result line must lead with the unproved count\n{text}"
    );
    assert!(text.contains("Gate: CONDITIONAL-PASS [advisory lane, exit 0]"), "{text}");
    assert!(text.contains("Gate note: 1 obligation(s) UNPROVED"), "{text}");

    let report = fs::read_to_string(report_dir.join("report.json")).unwrap_or_else(|error| {
        let listing: Vec<String> = fs::read_dir(&report_dir)
            .map(|dir| {
                dir.filter_map(Result::ok)
                    .map(|entry| entry.file_name().to_string_lossy().into_owned())
                    .collect()
            })
            .unwrap_or_default();
        panic!(
            "report.json missing ({error}); report dir holds {listing:?}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        )
    });
    let json: serde_json::Value = serde_json::from_str(&report).expect("report.json parses");
    let gate = &json["verification_gate"];
    assert_eq!(gate["lane"], "advisory", "{gate}");
    assert_eq!(gate["decision"], "conditional-pass", "{gate}");
    assert_eq!(gate["exit_code"], 0, "{gate}");
    assert_eq!(gate["counts"]["unknown"], 1, "{gate}");
    assert_eq!(gate["conditional_on_unknown_rows"], true, "{gate}");
    let _ = fs::remove_dir_all(&report_dir);
}

// T7b: a run whose rows are no measurement exits 3, COULD NOT RUN, in every
// lane — distinct from 1 (a verdict) and 0 (a pass). The same unknown row as
// the two tests above, but its search ended on a clock, a solver fault or a
// stop it does not explain: the strict lane would have exited 1 on it and the
// advisory ramp 0, and neither is a reading of what the code does.
#[test]
fn an_unknown_that_is_no_measurement_could_not_run_in_every_lane() {
    for (stop, outcome) in [
        ("wall-backstop", "not-reproducible"),
        ("solver-fault", "not-reproducible"),
        ("", "not-reproducible"),
    ] {
        for (lane, args) in [("strict", &[][..]), ("advisory", &["--allow-l0-gaps"][..])] {
            let (_, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
                "targo-trust-unknown-not-measured",
                args,
                &[("TRUST_FAKE_TARGO_OUTCOME", "unknown"), ("TRUST_FAKE_TARGO_STOP", stop)],
            );
            let text = format!("{stdout}\n{stderr}");
            assert_eq!(status, Some(3), "stop `{stop}`, {lane} lane\n{text}");
            assert!(
                text.contains(&format!("Gate: COULD-NOT-RUN [{lane} lane, exit 3]")),
                "stop `{stop}`, {lane} lane\n{text}"
            );
            assert!(
                text.contains(&format!("Result: COULD NOT RUN (outcome {outcome}")),
                "stop `{stop}`, {lane} lane\n{text}"
            );
            assert!(!text.contains("Result: PASS"), "{text}");
        }
    }

    // The sealed report records the same decision and exit.
    let report_dir = temp_test_dir("targo-trust-not-measured-report");
    let report_dir_arg = report_dir.to_string_lossy().into_owned();
    let (_, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-not-measured-report-run",
        &["--allow-l0-gaps", "--report-dir", &report_dir_arg],
        &[("TRUST_FAKE_TARGO_OUTCOME", "unknown"), ("TRUST_FAKE_TARGO_STOP", "wall-backstop")],
    );
    assert_eq!(status, Some(3), "stdout:\n{stdout}\nstderr:\n{stderr}");
    let report = fs::read_to_string(report_dir.join("report.json"))
        .unwrap_or_else(|error| panic!("report.json ({error})\nstderr:\n{stderr}"));
    let json: serde_json::Value = serde_json::from_str(&report).expect("report.json parses");
    let gate = &json["verification_gate"];
    assert_eq!(gate["decision"], "could-not-run", "{gate}");
    assert_eq!(gate["exit_code"], 3, "{gate}");
    assert_eq!(gate["determinism"]["outcome"], "not-reproducible", "{gate}");
    let _ = fs::remove_dir_all(&report_dir);
}

// T7b: a backstop that fired in work that published no row (the compiler's
// backstop ledger, carried on the coverage transport) makes the run no
// measurement, so even an all-proved run exits 3. A refuted row still exits 1:
// a counterexample is a verdict whatever else stopped on a clock. A counted,
// deterministic stop in the ledger is no backstop and changes nothing.
#[test]
fn a_backstop_in_the_ledger_could_not_run_unless_a_row_was_refuted() {
    let run = |outcome: &str, noted: &str| {
        run_targo_trust_check_with_fake_toolchain_args_env(
            "targo-trust-noted-backstop",
            &[],
            &[("TRUST_FAKE_TARGO_OUTCOME", outcome), ("TRUST_FAKE_TARGO_NOTED_STOP", noted)],
        )
    };

    let (_, stdout, stderr, status) = run("proved", "wall-backstop");
    let text = format!("{stdout}\n{stderr}");
    assert_eq!(status, Some(3), "an all-proved run whose ledger saw a backstop\n{text}");
    assert!(text.contains("backstops fired: fixture-lane wall-backstop=1"), "{text}");
    assert!(text.contains("Gate: COULD-NOT-RUN [strict lane, exit 3]"), "{text}");

    let (_, stdout, stderr, status) = run("failed", "wall-backstop");
    let text = format!("{stdout}\n{stderr}");
    assert_eq!(status, Some(1), "a refutation outranks the missing measurement\n{text}");
    assert!(text.contains("Gate: FAIL [strict lane, exit 1]"), "{text}");

    let (_, stdout, stderr, status) = run("proved", "effort");
    assert_eq!(
        status,
        Some(0),
        "a counted stop is no backstop\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// T7b: rows that are no measurement exit 3 only when they alone failed the
// run. A failure they do not account for is no question of measurement, and
// re-running cannot change it, so it exits as a measured run with the same
// failure does, however its rows were decided.
#[test]
fn a_failure_the_rows_do_not_account_for_never_could_not_run() {
    let run = |args: &[&str], env: &[(&str, &str)]| {
        let (_, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
            "targo-trust-unaccounted-failure",
            args,
            env,
        );
        (status, format!("{stdout}\n{stderr}"))
    };
    let clock_stopped_unknown =
        [("TRUST_FAKE_TARGO_OUTCOME", "unknown"), ("TRUST_FAKE_TARGO_STOP", "wall-backstop")];

    // The strict lane fails closed on the unknown: trustc's error is the
    // compile's nonzero exit, the row accounts for it, and the run could not
    // run.
    let (status, text) = run(
        &[],
        &[clock_stopped_unknown[0], clock_stopped_unknown[1], ("TRUST_FAKE_TARGO_EXIT", "101")],
    );
    assert_eq!(status, Some(3), "{text}");
    assert!(text.contains("Gate: COULD-NOT-RUN [strict lane, exit 3]"), "{text}");

    // The advisory ramp passes the same unknown, so trustc fails nothing on it:
    // the nonzero exit is a compile failure the row cannot account for.
    let (status, text) = run(
        &["--allow-l0-gaps"],
        &[clock_stopped_unknown[0], clock_stopped_unknown[1], ("TRUST_FAKE_TARGO_EXIT", "101")],
    );
    assert_eq!(status, Some(1), "{text}");
    assert!(text.contains("Gate: FAIL [advisory lane, exit 1]"), "{text}");

    // A workspace in which a second declared unit failed to compile and never
    // concluded: the concluded unit's rows cannot account for it.
    let unfinished = ("TRUST_FAKE_TARGO_UNFINISHED_UNIT", "1");
    let (status, text) = run(
        &[],
        &[
            clock_stopped_unknown[0],
            clock_stopped_unknown[1],
            unfinished,
            ("TRUST_FAKE_TARGO_EXIT", "101"),
        ],
    );
    assert_eq!(status, Some(1), "beside an unknown that fails the lane, 1 as before T7b\n{text}");
    assert!(text.contains("cannot find value `missing` in this scope"), "{text}");
    assert!(text.contains("Gate: FAIL [strict lane, exit 1]"), "{text}");
    let (status, text) = run(
        &[],
        &[
            ("TRUST_FAKE_TARGO_OUTCOME", "proved"),
            ("TRUST_FAKE_TARGO_NOTED_STOP", "wall-backstop"),
            unfinished,
            ("TRUST_FAKE_TARGO_EXIT", "101"),
        ],
    );
    assert_eq!(
        status,
        Some(101),
        "beside rows that proved, under a backstop, the compiler's own status\n{text}"
    );
    assert!(!text.contains("COULD-NOT-RUN"), "{text}");
}

// T7b: `check --rewrite` passes only over a measurement. A loop whose final
// frontier proved everything, but whose rows carry no stable key, could not
// run: before T7b it exited 0 on them.
#[test]
fn a_rewrite_loop_over_rows_that_are_no_measurement_could_not_run() {
    let (_, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-rewrite-keyless",
        &["--rewrite", "--max-iterations", "1"],
        &[("TRUST_FAKE_TARGO_NO_STABLE_IDS", "1")],
    );
    let text = format!("{stdout}\n{stderr}");
    assert_eq!(status, Some(3), "{text}");
    assert!(text.contains("the rewrite loop's final frontier is no measurement"), "{text}");

    let (_, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-rewrite-measured",
        &["--rewrite", "--max-iterations", "1"],
        &[],
    );
    assert_eq!(
        status,
        Some(0),
        "a measured pass still passes\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// T7b: a row with no T9 stable key makes the unit could-not-run (no verdict of
// it can be compared): no `Summary:` line, and exit 3 — where before T7b the
// same run printed COULD NOT RUN and still exited 0.
#[test]
fn a_row_without_a_stable_key_could_not_run() {
    let (_, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-keyless-row",
        &[],
        &[("TRUST_FAKE_TARGO_NO_STABLE_IDS", "1")],
    );
    let text = format!("{stdout}\n{stderr}");
    assert_eq!(status, Some(3), "{text}");
    assert!(text.contains("COULD NOT RUN: verification did not run to a measurement"), "{text}");
    assert!(text.contains("published obligations with no stable key"), "{text}");
    assert!(!text.lines().any(|line| line.starts_with("Summary:")), "{text}");
    assert!(text.contains("Result: COULD NOT RUN (outcome could-not-run"), "{text}");
}

// T7b: an obligation the memory authority refused to dispatch is a run that
// could not run (3), not a setup error (2, before T7b) and not an Unknown.
#[test]
fn a_refused_admission_could_not_run() {
    let (_, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-admission-refused",
        &[],
        &[("TRUST_FAKE_TARGO_OUTCOME", "unknown"), ("TRUST_FAKE_TARGO_STOP", "admission-refused")],
    );
    let text = format!("{stdout}\n{stderr}");
    assert_eq!(status, Some(3), "{text}");
    assert!(text.contains("1 obligation(s) were refused solver admission"), "{text}");
    assert!(text.contains("Gate: COULD-NOT-RUN [strict lane, exit 3]"), "{text}");
}

// T7b: when the trustd that admits this run's solvers cannot be established —
// here a live daemon of another build owns the socket — the run could not run:
// exit 3, before any compile, with the daemon named. The test's own private
// memory domain is the only one addressed.
#[test]
fn a_daemon_that_cannot_be_established_could_not_run() {
    let tmp_dir = temp_test_dir("targo-trust-refusing-trustd");
    let crate_dir = tmp_dir.join("crate");
    let src_dir = crate_dir.join("src");
    let bin_dir = tmp_dir.join("toolchain").join("bin");
    create_fixture_dir(&src_dir);
    create_fixture_dir(&bin_dir);
    fs::write(
        crate_dir.join("Cargo.toml"),
        "[package]\nname = \"refusing-trustd-fixture\"\nversion = \"0.0.0\"\nedition = \"2021\"\n",
    )
    .expect("write fixture manifest");
    fs::write(src_dir.join("lib.rs"), "pub fn id(x: usize) -> usize { x }\n")
        .expect("write fixture source");
    let capture_path = tmp_dir.join("capture.txt");
    let targo_trust = install_targo_trust_binary(&bin_dir);
    write_executable(&bin_dir.join("trustc"), fake_trustc_script());
    write_executable(&bin_dir.join("targo"), fake_targo_script());
    let refusing = fake_trustd::install_refusing(&bin_dir);

    let output = fixture_command(&targo_trust)
        .arg("check")
        .current_dir(&crate_dir)
        .env(fake_trustd::RUNTIME_DIR_ENV, refusing.runtime_dir())
        .env("TRUST_CAPTURE_FILE", &capture_path)
        .env_remove("CARGO")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .output()
        .expect("run targo-trust check against a refusing trustd");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let compiled = fs::read_to_string(&capture_path)
        .is_ok_and(|text| text.lines().any(|line| line == "targo_mode=build"));
    drop(refusing);
    let _ = fs::remove_dir_all(&tmp_dir);

    assert_eq!(output.status.code(), Some(3), "{stderr}");
    assert!(stderr.contains("targo trust: COULD NOT RUN:"), "{stderr}");
    assert!(stderr.contains("trustd memory authority"), "{stderr}");
    assert!(!compiled, "no compile may start without the memory authority\n{stderr}");
}

// T7b: `compiler_timeout_secs` is retired into `backstop`: a table that still
// names it is refused before any compile, and the refusal names the
// replacement.
#[test]
fn the_retired_compiler_timeout_fails_closed_before_targo_naming_the_backstop() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_trust_table(
        "targo-trust-retired-compiler-timeout",
        "compiler_timeout_secs = 72000\n",
    );
    assert_eq!(status, Some(2), "stdout:\n{stdout}\nstderr:\n{stderr}");
    assert!(
        stderr.contains("`compiler_timeout_secs` was retired") && stderr.contains("`backstop`"),
        "{stderr}"
    );
    assert!(capture.is_none(), "fake targo must not run on a retired key");
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

// Trust (2026-09-16, `f2a47900ec`): a recorded assumption is CONDITIONAL
// evidence on the default lane, not a failure. Under the batteries-on strict
// policy the `assumed` bucket can only hold rows the compiler itself publishes
// as conditional evidence — a `#[trust::assume_total]` axiom, a
// definition-entry `requires`, the b59 `fmt::format` leg, a discharged
// contract row — and the compiler's own default policy already tolerated
// exactly those rows, so `targo trust check` grades the run a conditional PASS
// (exit 0) that NAMES the assumption on the `Result:` line, on the `Gate:`
// line and in the Assumptions ledger, while the crate verdict lattice stays
// fail-closed (`INCONCLUSIVE`). Only `--certify`, full static discharge,
// refuses it. This test pinned exit 1 here from 2026-07-10 (when the strict
// lane never conditional-passed) until the gate moved; the unit pin
// `gate_strict_conditionally_passes_the_ledger_buckets_and_nothing_else` is
// the same contract one layer down.
//
// The row is one the strict compiler really publishes: a call to a
// `#[trust::assume_total]` wrapper, as the bridge demotion stamps it. Since
// 2026-09-24 the strict lane admits only such rows. The fixture's invented
// `assumption:test` row is refused on the default lane; see
// `default_targo_check_refuses_assumption_rows_the_strict_policy_never_publishes`.
#[test]
fn default_targo_check_conditionally_passes_a_recorded_assumption_and_certify_refuses_it() {
    let report_dir = temp_test_dir("targo-trust-assumption-report");
    let report_dir_arg = report_dir.to_string_lossy().into_owned();
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-assumption-transport",
        &["--report-dir", &report_dir_arg],
        &[
            ("TRUST_FAKE_TARGO_OUTCOME", "assumption"),
            ("TRUST_FAKE_TARGO_ASSUMPTION_KIND", "assumption:assumed-total-callee"),
            ("TRUST_FAKE_TARGO_ASSUMPTION_SOLVER", "trust-bridge"),
        ],
    );
    assert_eq!(
        status,
        Some(0),
        "the default lane grades a recorded assumption a CONDITIONAL pass, never a failure (2026-09-16)\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !capture_has_z_flag(&capture, "trust-policy=advisory")
            && !capture_has_z_flag(&capture, "trust-policy=memory-safe"),
        "the conditional pass must come from the batteries-on strict policy, not a loosened lane: {capture:?}"
    );
    let text = format!("{stdout}\n{stderr}");
    assert!(
        text.contains("Result: PASS (conditional: 0 unproved, 1 assumption,"),
        "the Result line must name the assumption the exit-0 is conditional on\n{text}"
    );
    assert!(
        text.contains(
            "Gate: CONDITIONAL-PASS [strict lane, exit 0] (0 proved, 0 failed, 0 runtime-checked, 1 assumed, 0 mandated, 0 contract-panic, 0 unknown / 1 total)"
        ),
        "the Gate line must carry every bucket the pass is conditional on\n{text}"
    );
    assert!(
        !text.contains("Gate note:"),
        "a ledger row is not an unproved obligation; the ramp's UNPROVED note must not appear\n{text}"
    );
    assert!(
        text.contains("Verdict: INCONCLUSIVE"),
        "the crate verdict lattice stays fail-closed under a conditional gate pass\n{text}"
    );
    let report = fs::read_to_string(report_dir.join("report.json")).unwrap_or_else(|error| {
        panic!("report.json missing ({error})\nstdout:\n{stdout}\nstderr:\n{stderr}")
    });
    let json: serde_json::Value = serde_json::from_str(&report).expect("report.json parses");
    let gate = &json["verification_gate"];
    assert_eq!(gate["lane"], "strict", "{gate}");
    assert_eq!(gate["decision"], "conditional-pass", "{gate}");
    assert_eq!(gate["exit_code"], 0, "{gate}");
    assert_eq!(gate["counts"]["assumed"], 1, "{gate}");
    assert_eq!(gate["counts"]["unknown"], 0, "{gate}");
    assert_eq!(gate["conditional_on_assumption_rows"], true, "{gate}");
    assert_eq!(gate["conditional_on_unknown_rows"], false, "{gate}");
    let ledger = json["assumptions"].as_array().expect("the Assumptions ledger is an array");
    assert!(
        ledger
            .iter()
            .any(|entry| entry["scope"] == "function" && entry["tag"] == "assumed-total-callee"),
        "the Assumptions ledger must carry the recorded row under its own tag: {ledger:?}"
    );
    let _ = fs::remove_dir_all(&report_dir);

    // `--certify` is the release gate — full static discharge — so the same
    // assumption row is INCONCLUSIVE there (never FAIL: nothing was refuted).
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-certify-assumption-transport",
        &["--certify"],
        &[("TRUST_FAKE_TARGO_OUTCOME", "assumption")],
    );
    assert_eq!(
        status,
        Some(1),
        "--certify must refuse a recorded assumption: shipping requires full static discharge\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(!capture_has_z_flag(&capture, "trust-policy=advisory"), "{capture:?}");
    let text = format!("{stdout}\n{stderr}");
    assert!(text.contains("Result: INCONCLUSIVE"), "{text}");
    assert!(text.contains("Gate: INCONCLUSIVE [certify lane, exit 1]"), "{text}");

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

// Trust (2026-09-24): the default lane's conditional pass rests on the rows
// coming from the compiler's STRICT policy. `TRUSTFLAGS` could set
// `-Ztrust-policy` for one run while the gate lane followed the CLI, so an
// advisory or memory-safe compiler run used to be graded on the strict lane:
// its advisory-only rows (a `#[trust::skip]` opt-out here, which strict policy
// refuses with a compile error) passed it CONDITIONALLY, exit 0. The strict lane
// now admits only the shapes the strict policy publishes and counts every other
// `assumption:*` row as a genuine unknown, the way the memory-safe lane admits
// only its own stamped rows.
//
// Trust (2026-10-01): two layers kept those rows off the strict lane. Since
// 1516a6229d a TRUSTFLAGS nonfatal policy was refused at setup, and since T7a
// (2026-10-11) TRUSTFLAGS is not read at all
// (`an_ambient_trustflags_is_ignored_with_one_notice`), so no compile runs a
// policy its lane does not select. The grader below stays the second layer for
// any row that reaches the strict lane by another route: each leg presents a
// foreign row shape directly on a strict-policy compile, exactly as the policy
// it belongs to mints it (the shapes the fake toolchain used to stamp under
// TRUSTFLAGS).
#[test]
fn default_targo_check_refuses_assumption_rows_the_strict_policy_never_publishes() {
    // Layer 2: the advisory `#[trust::skip]` opt-out row, as advisory policy
    // records it (measured with trustc 0.10.0+g450403669), on the strict lane.
    let report_dir = temp_test_dir("targo-trust-advisory-row-strict-report");
    let report_dir_arg = report_dir.to_string_lossy().into_owned();
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-advisory-row-strict-lane",
        &["--report-dir", &report_dir_arg],
        &[
            ("TRUST_FAKE_TARGO_OUTCOME", "assumption"),
            ("TRUST_FAKE_TARGO_ASSUMPTION_KIND", "assumption:user-opt-out"),
            ("TRUST_FAKE_TARGO_ASSUMPTION_SOLVER", "trust-policy"),
        ],
    );
    assert!(
        !capture_has_z_flag(&capture, "trust-policy=advisory")
            && !capture_has_z_flag(&capture, "trust-policy=memory-safe"),
        "the row must reach the grader on a strict-policy compile, or this leg measures nothing: {capture:?}"
    );
    assert_eq!(
        status,
        Some(1),
        "an advisory-policy row must not pass the strict lane\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains(
            "strict policy rejected assumption `assumption:user-opt-out` (source `trust-policy`)"
        ),
        "the refusal must name the row and its source\n{stderr}"
    );
    let text = format!("{stdout}\n{stderr}");
    assert!(
        text.contains(
            "Gate: INCONCLUSIVE [strict lane, exit 1] (0 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 mandated, 0 contract-panic, 1 unknown / 1 total)"
        ),
        "the refused row is a genuine unknown on the Gate line\n{text}"
    );
    let report = fs::read_to_string(report_dir.join("report.json")).unwrap_or_else(|error| {
        panic!("report.json missing ({error})\nstdout:\n{stdout}\nstderr:\n{stderr}")
    });
    let json: serde_json::Value = serde_json::from_str(&report).expect("report.json parses");
    let gate = &json["verification_gate"];
    assert_eq!(gate["lane"], "strict", "{gate}");
    assert_eq!(gate["decision"], "inconclusive", "{gate}");
    assert_eq!(gate["exit_code"], 1, "{gate}");
    assert_eq!(gate["counts"]["assumed"], 0, "{gate}");
    assert_eq!(gate["counts"]["unknown"], 1, "{gate}");
    let _ = fs::remove_dir_all(&report_dir);

    // The memory-safe demotion's row, on the strict lane.
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-memory-safe-row-strict-lane",
        &[],
        &[
            ("TRUST_FAKE_TARGO_OUTCOME", "assumption"),
            ("TRUST_FAKE_TARGO_ASSUMPTION_KIND", "assumption:memory-safe-panic"),
            ("TRUST_FAKE_TARGO_ASSUMPTION_SOLVER", "trust-memory-safe"),
        ],
    );
    assert!(!capture_has_z_flag(&capture, "trust-policy=memory-safe"), "{capture:?}");
    assert_eq!(
        status,
        Some(1),
        "a memory-safe demotion must not pass the strict lane\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("strict policy rejected assumption `assumption:memory-safe-panic`"),
        "{stderr}"
    );

    // A tag no compiler policy mints at all.
    let (_, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args_env(
        "targo-trust-invented-assumption-tag",
        &[],
        &[("TRUST_FAKE_TARGO_OUTCOME", "assumption")],
    );
    assert_eq!(
        status,
        Some(1),
        "an invented assumption tag must not pass the strict lane\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("strict policy rejected assumption `assumption:test` (source `test`)"),
        "{stderr}"
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
    create_fixture_dir(&src_dir);
    create_fixture_dir(&bin_dir);

    fs::write(
        crate_dir.join("Cargo.toml"),
        "[package]\nname = \"no-json-capability-fixture\"\nversion = \"0.0.0\"\nedition = \"2021\"\n",
    )
    .expect("write fixture manifest");
    fs::write(src_dir.join("lib.rs"), "pub fn id(x: usize) -> usize { x }\n")
        .expect("write fixture source");

    let capture_path = tmp_dir.join("capture.txt");
    let cargo_home = tmp_dir.join("cargo-home");
    let targo_trust = install_targo_trust_binary(&bin_dir);
    write_executable(&bin_dir.join("trustc"), fake_trustc_script());
    write_executable(&bin_dir.join("targo"), fake_targo_script());
    let _trustd = fake_trustd::install(&bin_dir);

    let output = fixture_command(&targo_trust)
        .arg("check")
        .current_dir(&crate_dir)
        .env(fake_trustd::RUNTIME_DIR_ENV, _trustd.runtime_dir())
        .env("TRUST_CAPTURE_FILE", &capture_path)
        .env("CARGO_HOME", &cargo_home)
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

    // Drop the guard FIRST: it shuts the stub down on its private endpoint and
    // removes that runtime directory while the stub's executable (in tmp_dir)
    // still exists.
    drop(_trustd);
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
fn the_backstop_reaches_tracked_compiler_policy() {
    // 375 per mille of the reference clocks: 1,875 ms per query, 45,000 ms per
    // function.
    let (capture, stdout, stderr, status) =
        run_targo_trust_check_with_trust_table("targo-trust-backstop-config", "backstop = 375\n");
    assert_eq!(
        status,
        Some(0),
        "a valid backstop should dispatch\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let capture = capture.expect("fake targo must receive a valid configured run");
    assert!(capture_has_z_flag(&capture, "trust-verify-timeout-ms=1875"));
    assert!(capture_has_z_flag(&capture, "trust-verify-function-budget-ms=45000"));
}

#[test]
fn the_deprecated_file_still_configures_a_run_and_says_where_to_move() {
    let (capture, stdout, stderr, status) =
        run_targo_trust_check_with_legacy_file("targo-trust-legacy-config", "level = \"L1\"\n");
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
    assert_eq!(capture_z_flag_values(&capture, "trust-verify-level"), vec!["1".to_string()]);
}

/// A budget is set in one place, the workspace root's `[trust]` table: the
/// deprecated file is not a second spelling of `effort` or `backstop`.
#[test]
fn the_deprecated_file_cannot_set_a_budget() {
    for budget in ["backstop = 375\n", "effort = 6\n"] {
        let (capture, stdout, stderr, status) =
            run_targo_trust_check_with_legacy_file("targo-trust-legacy-budget", budget);
        assert_eq!(
            status,
            Some(2),
            "a budget in the deprecated file is a setup error\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stderr.contains("cannot set effort or backstop") && stderr.contains("[trust]"),
            "the refusal names where a budget goes\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(capture.is_none(), "fake targo must not run on a refused budget");
    }
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

/// Plan P4 / T4.1: trustc links its ay and selects no solver executable, so
/// `--solver ay` names the linked solver and passes no solver path to Cargo.
#[test]
fn solver_selection_names_the_linked_solver_and_passes_no_path() {
    let (capture, stdout, stderr, status) = run_targo_trust_check_with_fake_toolchain_args(
        "targo-trust-linked-ay",
        &["--solver", "ay"],
    );
    assert_eq!(
        status,
        Some(0),
        "`--solver ay` should complete with the fake toolchain\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        capture_has_z_option_prefix(&capture, "trust-verify-session="),
        "control: the capture carries the run's host-policy options: {capture:?}"
    );
    assert!(
        !capture_has_z_option_prefix(&capture, "trust-verify-ay-path"),
        "trustc has no solver-path option; none may reach Cargo: {capture:?}"
    );
    assert!(
        stderr.contains("requesting solver `ay`, the one linked into the compiler"),
        "stderr:\n{stderr}"
    );
}

#[test]
fn crate_mode_ignores_inherited_cargo_env() {
    let tmp_dir = temp_test_dir("targo-trust-ignore-cargo-env");
    let crate_dir = tmp_dir.join("crate");
    let src_dir = crate_dir.join("src");
    let bin_dir = tmp_dir.join("toolchain").join("bin");
    create_fixture_dir(&src_dir);
    create_fixture_dir(&bin_dir);

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

    let output = fixture_command(&targo_trust)
        .arg("check")
        .current_dir(&crate_dir)
        .env(fake_trustd::RUNTIME_DIR_ENV, _trustd.runtime_dir())
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

    // Drop the guard FIRST: it shuts the stub down on its private endpoint and
    // removes that runtime directory while the stub's executable (in tmp_dir)
    // still exists.
    drop(_trustd);
    let _ = fs::remove_dir_all(&tmp_dir);
}

#[test]
fn crate_mode_rejects_path_targo_when_sibling_targo_is_missing() {
    let tmp_dir = temp_test_dir("targo-trust-missing-sibling-targo");
    let crate_dir = tmp_dir.join("crate");
    let src_dir = crate_dir.join("src");
    let bin_dir = tmp_dir.join("toolchain").join("bin");
    let path_bin_dir = tmp_dir.join("path-bin");
    create_fixture_dir(&src_dir);
    create_fixture_dir(&bin_dir);
    create_fixture_dir(&path_bin_dir);

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
    let output = fixture_command(&targo_trust)
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

/// One fake toolchain (targo-trust, trustc, targo and a private trustd) that
/// several crate-mode checks share, for tests that compare runs (T7c).
struct SharedFakeToolchain {
    tmp_dir: PathBuf,
    bin_dir: PathBuf,
    targo_trust: PathBuf,
    trustd: Option<fake_trustd::FakeTrustd>,
}

impl SharedFakeToolchain {
    fn install(prefix: &str) -> Self {
        let tmp_dir = temp_test_dir(prefix);
        let bin_dir = tmp_dir.join("toolchain").join("bin");
        create_fixture_dir(&bin_dir);
        let targo_trust = install_targo_trust_binary(&bin_dir);
        write_executable(&bin_dir.join("trustc"), fake_trustc_script());
        write_executable(&bin_dir.join("targo"), fake_targo_script());
        write_executable(&bin_dir.join("ay"), "#!/bin/sh\nprintf 'ay 0.0.0\\n'\n");
        let trustd = Some(fake_trustd::install(&bin_dir));
        Self { tmp_dir, bin_dir, targo_trust, trustd }
    }

    /// A package `name` with one library, at `<tmp>/<at>/crate`.
    fn fixture_crate(&self, at: &str, name: &str) -> PathBuf {
        let crate_dir = self.tmp_dir.join(at).join("crate");
        create_fixture_dir(&crate_dir.join("src"));
        fs::write(
            crate_dir.join("Cargo.toml"),
            format!("[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2021\"\n"),
        )
        .expect("write fixture manifest");
        fs::write(crate_dir.join("src/lib.rs"), "pub fn id(x: usize) -> usize { x }\n")
            .expect("write fixture source");
        crate_dir
    }

    /// `targo trust check` in `crate_dir`: (stdout, stderr, exit status).
    fn check(&self, crate_dir: &Path) -> (String, String, Option<i32>) {
        self.run(crate_dir, &["check"], &[])
    }

    /// `targo trust <args>` in `crate_dir`, with `env` on top of the fixture's
    /// own: (stdout, stderr, exit status).
    fn run(
        &self,
        crate_dir: &Path,
        args: &[&str],
        env: &[(&str, &str)],
    ) -> (String, String, Option<i32>) {
        let trustd = self.trustd.as_ref().expect("the stub is running");
        let mut command = fixture_command(&self.targo_trust);
        for (key, value) in env {
            command.env(key, value);
        }
        let output = command
            .args(args)
            .current_dir(crate_dir)
            .env(fake_trustd::RUNTIME_DIR_ENV, trustd.runtime_dir())
            .env("TRUST_CAPTURE_FILE", self.tmp_dir.join("capture.txt"))
            .env("CARGO_HOME", self.tmp_dir.join("cargo-home"))
            .env("AY_PATH", self.bin_dir.join("ay"))
            .env_remove("CARGO")
            .env_remove("RUSTFLAGS")
            .env_remove("CARGO_ENCODED_RUSTFLAGS")
            .output()
            .expect("run targo-trust with the shared fake toolchain");
        (
            String::from_utf8_lossy(&output.stdout).into_owned(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
            output.status.code(),
        )
    }
}

impl Drop for SharedFakeToolchain {
    fn drop(&mut self) {
        // The stub first, while its executable (in tmp_dir) still exists.
        drop(self.trustd.take());
        let _ = fs::remove_dir_all(&self.tmp_dir);
    }
}

/// The package record and the obligation record a check wrote for `package`.
fn written_records(crate_dir: &Path, package: &str) -> (String, String) {
    let read = |path: PathBuf| {
        fs::read_to_string(&path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
    };
    (
        read(crate_dir.join(format!("target/trust/packages/{package}.json"))),
        read(crate_dir.join(format!("target/trust/obligations/{package}.ndjson"))),
    )
}

/// A package record without its wall-clock `cost`, which is the one field
/// that is not a function of the run's inputs.
fn record_without_cost(record: &str) -> Value {
    let mut value: Value = serde_json::from_str(record).expect("a JSON package record");
    let cost = value.as_object_mut().expect("an object").remove("cost");
    assert!(cost.is_some_and(|cost| cost["wall_clock_ms"].is_u64()), "{record}");
    value
}

// T7c: a crate-mode check writes `trust.package.v1` beside its obligation
// record. The record agrees with the run's own `Summary:` line and with the
// obligation record's header (one source of truth); a second run of the same
// check writes the same records but for the wall-clock `cost`; and the same
// crate at another absolute path writes the same records too (no path, no
// package ID in any field).
#[test]
fn a_check_writes_a_package_record_that_agrees_with_its_summary_and_does_not_move() {
    const PACKAGE: &str = "package-record-fixture";
    let toolchain = SharedFakeToolchain::install("targo-trust-package-record");
    let crate_dir = toolchain.fixture_crate("first", PACKAGE);

    let (stdout, stderr, status) = toolchain.check(&crate_dir);
    assert_eq!(status, Some(0), "{stdout}\n{stderr}");
    let (record, obligations) = written_records(&crate_dir, PACKAGE);
    let value: Value = serde_json::from_str(&record).expect("a JSON package record");
    let header: Value = serde_json::from_str(obligations.lines().next().expect("a header line"))
        .expect("a JSON header");
    assert_eq!(value["schema"], "trust.package.v1");
    assert_eq!(value["package"], PACKAGE);
    assert_eq!(value["outcome"], "measured", "{record}");
    assert_eq!(value["coverage"]["complete"], true, "{record}");
    assert_eq!(value["result_key"]["absent"], "T10", "{record}");
    assert!(record.ends_with("}\n"), "{record}");
    assert!(!record.contains(crate_dir.to_str().unwrap()), "no absolute path: {record}");

    // The Summary line, the obligation header and the record agree.
    let text = format!("{stdout}\n{stderr}");
    let summary = text
        .lines()
        .find(|line| line.trim_start().starts_with("Summary: "))
        .map(str::trim_start)
        .unwrap_or_else(|| panic!("a Summary line\n{text}"));
    let short = |field: &str| value[field].as_str().unwrap()[..12].to_string();
    assert!(
        summary.ends_with(&format!(
            "; {}; profile {}; vector {}",
            value["outcome"].as_str().unwrap(),
            short("profile"),
            short("vector")
        )),
        "{summary}\n{record}"
    );
    let counts = &value["counts"];
    assert!(
        summary.starts_with(&format!(
            "Summary: {} proved, {} failed, {} runtime-checked, {} assumed, {} mandated, {} \
             contract-panic, {} inconclusive ({} total)",
            counts["proved"],
            counts["failed"],
            counts["runtime_checked"],
            counts["assumed"],
            counts["mandated"],
            counts["contract_panics"],
            counts["unknown"],
            counts["total"],
        )),
        "{summary}\n{record}"
    );
    for field in [
        "outcome",
        "vector",
        "profile",
        "seal",
        "targo_trust_commit",
        "lane",
        "policy",
        "selection",
    ] {
        assert_eq!(header[field], value[field], "{field}: {obligations}\n{record}");
    }
    // The commit targo-trust was built from is not the seal's identity, which
    // no installed toolchain can state yet: the seal is absent, naming A8.
    assert_eq!(value["seal"]["absent"], "A8", "{record}");
    assert!(value["targo_trust_commit"].is_string(), "{record}");
    assert_eq!(header["coverage_complete"], value["coverage"]["complete"]);

    // The same check again: the same bytes, but for `cost`.
    let (stdout_again, stderr_again, status) = toolchain.check(&crate_dir);
    assert_eq!(status, Some(0), "{stdout_again}\n{stderr_again}");
    let (record_again, obligations_again) = written_records(&crate_dir, PACKAGE);
    assert_eq!(record_without_cost(&record_again), record_without_cost(&record));
    assert_eq!(obligations_again, obligations);

    // The same crate at another absolute path.
    let moved_dir = toolchain.fixture_crate("elsewhere/deeper", PACKAGE);
    let (stdout_moved, stderr_moved, status) = toolchain.check(&moved_dir);
    assert_eq!(status, Some(0), "{stdout_moved}\n{stderr_moved}");
    let (record_moved, obligations_moved) = written_records(&moved_dir, PACKAGE);
    assert_eq!(record_without_cost(&record_moved), record_without_cost(&record));
    assert_eq!(obligations_moved, obligations);
}

/// `targo trust stability` over the shared fake toolchain in a fixture crate:
/// the exit status and the `trust.stability.v1` JSON report.
fn stability(
    toolchain: &SharedFakeToolchain,
    crate_dir: &Path,
    axes: &str,
    env: &[(&str, &str)],
) -> (Option<i32>, Value, String) {
    let scratch = toolchain.tmp_dir.join("scratch");
    create_fixture_dir(&scratch);
    let scratch = scratch.to_str().expect("a UTF-8 path");
    let (stdout, stderr, status) = toolchain.run(
        crate_dir,
        &["stability", "--axes", axes, "--scratch", scratch, "--format", "json", "--allow-l0-gaps"],
        env,
    );
    let report: Value = serde_json::from_str(&stdout).unwrap_or_else(|error| {
        panic!("a JSON report ({error})\nstdout:\n{stdout}\nstderr:\n{stderr}")
    });
    (status, report, stderr)
}

// T4.7: `targo trust stability` runs each leg as this targo-trust's own
// `check` — a fresh process, a fresh target directory — and compares the
// records each writes. Over the fake toolchain, whose verdicts are a function
// of the source alone, every axis this test runs is equal, the negative
// control (`[trust] backstop = 1`, which the fake answers with a wall-backstop
// in its ledger as the compiler would) is caught, and the serial leg's record
// states the one worker thread it ran with. (The load axis runs in the unit
// tests, with a two-loop generator: 2 x cores busy loops here would load
// every other test of this binary.)
#[test]
fn stability_reports_every_axis_equal_on_a_deterministic_fixture() {
    let toolchain = SharedFakeToolchain::install("targo-trust-stability-equal");
    let crate_dir = toolchain.fixture_crate("ws", "stability-fixture");
    let (status, report, stderr) =
        stability(&toolchain, &crate_dir, "repetition,parallelism,path,version", &[]);
    assert_eq!(status, Some(0), "{report:#}\n{stderr}");
    assert_eq!(report["schema"], "trust.stability.v1");
    assert_eq!(report["control"]["verdict"], "caught", "{report:#}");
    assert_ne!(report["control"]["units"][0]["outcome"], "measured", "{report:#}");
    assert_eq!(report["control"]["units"][0]["wall_backstop_stops"], 1, "{report:#}");
    let axes: Vec<(&str, &str)> = report["axes"]
        .as_array()
        .expect("axes")
        .iter()
        .map(|axis| (axis["axis"].as_str().unwrap(), axis["verdict"].as_str().unwrap()))
        .collect();
    assert_eq!(
        axes,
        [
            ("repetition", "equal"),
            ("parallelism", "equal"),
            ("path", "equal"),
            ("version", "equal")
        ],
        "{report:#}"
    );
    let legs: Vec<&str> =
        report["legs"].as_array().unwrap().iter().map(|leg| leg["leg"].as_str().unwrap()).collect();
    assert_eq!(legs, ["control", "base", "repeat", "serial", "moved", "bumped"]);
    for axis in report["axes"].as_array().unwrap() {
        let unit = &axis["units"][0];
        assert_eq!(unit["package"], "stability-fixture", "{axis:#}");
        assert_eq!(unit["vector"], report["axes"][0]["units"][0]["vector"], "one vector");
    }
    // The serial leg's compile ran with one worker thread and one job.
    let capture = fs::read_to_string(toolchain.tmp_dir.join("capture.txt")).expect("capture");
    assert!(capture.contains("trust-verify-worker-threads=1"), "{capture}");
    // Each leg's progress is on stderr; the caller's checkout gained no record.
    assert!(stderr.contains("leg 6/6 `bumped`: running"), "{stderr}");
    assert!(!crate_dir.join("target").exists(), "every leg has its own target directory");
}

// T4.7's negative control: a deliberately nondeterministic test-only input
// (the fake compiler's TRUST_FAKE_TARGO_NONDETERMINISTIC_STOP_FILE, which
// stops its unknown row on `effort` on every other compile) makes the
// repetition axis differ, and the verb names the key and both verdicts, and
// exits 1.
#[test]
fn stability_names_the_key_a_nondeterministic_fixture_moves() {
    let toolchain = SharedFakeToolchain::install("targo-trust-stability-differs");
    let crate_dir = toolchain.fixture_crate("ws", "stability-fixture");
    let counter = toolchain.tmp_dir.join("compiles");
    let (status, report, stderr) = stability(
        &toolchain,
        &crate_dir,
        "repetition",
        &[
            ("TRUST_FAKE_TARGO_OUTCOME", "unknown"),
            ("TRUST_FAKE_TARGO_NONDETERMINISTIC_STOP_FILE", counter.to_str().unwrap()),
        ],
    );
    assert_eq!(status, Some(1), "{report:#}\n{stderr}");
    assert_eq!(report["control"]["verdict"], "caught", "{report:#}");
    let axis = &report["axes"][0];
    assert_eq!(axis["axis"], "repetition");
    assert_eq!(axis["verdict"], "differing", "{report:#}");
    let unit = &axis["units"][0];
    assert_eq!(unit["verdict"], "differing");
    assert_ne!(unit["vectors"][0], unit["vectors"][1]);
    assert_eq!(unit["profiles"][0], unit["profiles"][1], "only a verdict moved");
    let keys = unit["differing_keys"].as_array().expect("keys");
    assert_eq!(keys.len(), 1, "{report:#}");
    assert!(
        keys[0]["key"].as_str().unwrap().ends_with(&format!("::test#{FIXTURE_STABLE_ID}")),
        "{report:#}"
    );
    // Compiles: the control's first (0), then base (1, odd: `effort`), then
    // repeat (2).
    assert_eq!(keys[0]["left"], serde_json::json!({ "status": "unknown", "stop": "effort" }));
    assert_eq!(
        keys[0]["right"],
        serde_json::json!({ "status": "unknown", "stop": "solver-incomplete" })
    );
}

// STABILITY-COPY-1 / T4.7-16: a workspace whose manifest names a path
// dependency outside its root (here `../../helper`, which the fake reads as
// Cargo does) is copied with that dependency at the same relative position, so
// every copied leg resolves: the control is caught and every axis is equal.
// The copies carry no build output and nothing the resolve does not read, and
// nothing outside the scratch directory is written.
#[test]
fn stability_copies_a_path_dependency_outside_the_workspace_root() {
    let toolchain = SharedFakeToolchain::install("targo-trust-stability-closure");
    let crate_dir = toolchain.fixture_crate("repo/ws", "stability-fixture");
    let manifest = crate_dir.join("Cargo.toml");
    let package = fs::read_to_string(&manifest).expect("read the fixture manifest");
    fs::write(
        &manifest,
        format!("{package}\n[dependencies]\nhelper = {{ path = \"../../helper\" }}\n"),
    )
    .expect("name the dependency");
    let repo = toolchain.tmp_dir.join("repo");
    let helper = repo.join("helper");
    create_fixture_dir(&helper.join("src"));
    create_fixture_dir(&helper.join("target"));
    create_fixture_dir(&repo.join("unrelated"));
    for (path, text) in [
        (helper.join("Cargo.toml"), "[package]\nname = \"helper\"\nversion = \"0.3.0\"\n"),
        (helper.join("src/lib.rs"), "pub fn helper() {}\n"),
        (helper.join("target/CACHEDIR.TAG"), "Signature: 8a477f597d28d172789f06886806bc55\n"),
        (repo.join("unrelated/big.bin"), "never read\n"),
    ] {
        fs::write(path, text).expect("write the fixture");
    }
    let listing = |dir: &Path| {
        let mut files = Vec::new();
        let mut pending = vec![dir.to_path_buf()];
        while let Some(next) = pending.pop() {
            for entry in fs::read_dir(&next).expect("read_dir") {
                let path = entry.expect("entry").path();
                if path.is_dir() {
                    pending.push(path);
                } else {
                    files.push((path.clone(), fs::read(&path).expect("read")));
                }
            }
        }
        files.sort();
        files
    };
    let before = listing(&repo);

    let scratch = toolchain.tmp_dir.join("scratch");
    create_fixture_dir(&scratch);
    let (stdout, stderr, status) = toolchain.run(
        &crate_dir,
        &[
            "stability",
            "--axes",
            "repetition,path,version",
            "--scratch",
            scratch.to_str().expect("a UTF-8 path"),
            "--keep",
            "--format",
            "json",
            "--allow-l0-gaps",
        ],
        &[],
    );
    let report: Value = serde_json::from_str(&stdout)
        .unwrap_or_else(|error| panic!("a JSON report ({error})\n{stdout}\n{stderr}"));
    assert_eq!(status, Some(0), "{report:#}\n{stderr}");
    assert_eq!(report["control"]["verdict"], "caught", "{report:#}");
    let verdicts: Vec<&str> = report["axes"]
        .as_array()
        .expect("axes")
        .iter()
        .map(|axis| axis["verdict"].as_str().unwrap())
        .collect();
    assert_eq!(verdicts, ["equal", "equal", "equal"], "{report:#}");
    assert_eq!(report["copy"]["workspace"], "ws/crate", "{report:#}");
    assert_eq!(report["copy"]["trees"], serde_json::json!(["helper", "ws/crate"]), "{report:#}");

    // The kept copies: the dependency beside the workspace, as in the original.
    let kept = PathBuf::from(report["scratch"].as_str().expect("kept"));
    for copy in ["checkouts/moved/elsewhere/deeper/repo", "checkouts/control/repo"] {
        let copy = kept.join(copy);
        assert_eq!(
            fs::read(copy.join("helper/src/lib.rs")).expect("the dependency is carried"),
            b"pub fn helper() {}\n"
        );
        assert!(copy.join("ws/crate/src/lib.rs").is_file());
        assert!(!copy.join("helper/target").exists(), "no build output");
        assert!(!copy.join("unrelated").exists(), "nothing the resolve does not read");
    }
    let moved_cwd = report["legs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|leg| leg["leg"] == "moved")
        .and_then(|leg| leg["cwd"].as_str())
        .expect("the moved leg");
    assert!(moved_cwd.ends_with("elsewhere/deeper/repo/ws/crate"), "{moved_cwd}");
    assert_eq!(listing(&repo), before, "nothing outside the scratch directory is written");
}

// T4.7: a record that states a solver fault is plan §2's `not-reproducible`,
// a defect to fix at its producer, never a host that could not run: the axis
// reads not-reproducible, names the cause and both vectors, and the verb exits
// 1, not 3.
#[test]
fn stability_reads_a_solver_fault_as_not_reproducible_and_exits_1() {
    let toolchain = SharedFakeToolchain::install("targo-trust-stability-fault");
    let crate_dir = toolchain.fixture_crate("ws", "stability-fixture");
    let (status, report, stderr) = stability(
        &toolchain,
        &crate_dir,
        "repetition",
        &[("TRUST_FAKE_TARGO_OUTCOME", "unknown"), ("TRUST_FAKE_TARGO_STOP", "solver-fault")],
    );
    assert_eq!(status, Some(1), "{report:#}\n{stderr}");
    let axis = &report["axes"][0];
    assert_eq!(axis["verdict"], "not-reproducible", "{report:#}");
    let unit = &axis["units"][0];
    assert_eq!(unit["verdict"], "not-reproducible", "{report:#}");
    assert!(unit["reason"].as_str().unwrap().contains("solver-fault=1"), "{report:#}");
    assert_eq!(unit["seen"]["agree"], true, "both vectors are carried: {report:#}");
    assert_eq!(report["legs"][1]["packages"][0]["outcome"], "not-reproducible", "{report:#}");
}

// T7c: a selected package's records are this run's or absent. A check that
// stops before it can write them (here the trustd that admits its solvers
// cannot be established: exit 3, no compile) removes the records an earlier
// run of the package left, so they cannot be read as this run's.
#[test]
fn a_run_that_could_not_run_leaves_no_earlier_record_of_its_package() {
    const PACKAGE: &str = "stale-record-fixture";
    let mut toolchain = SharedFakeToolchain::install("targo-trust-stale-record");
    let crate_dir = toolchain.fixture_crate("crate", PACKAGE);
    let (stdout, stderr, status) = toolchain.check(&crate_dir);
    assert_eq!(status, Some(0), "{stdout}\n{stderr}");
    let records = [
        crate_dir.join(format!("target/trust/packages/{PACKAGE}.json")),
        crate_dir.join(format!("target/trust/obligations/{PACKAGE}.ndjson")),
    ];
    assert!(records.iter().all(|path| path.is_file()), "{stderr}");
    // A record of a package this run does not select is left alone.
    let unrelated = crate_dir.join("target/trust/packages/unrelated.json");
    fs::write(&unrelated, "{}\n").expect("write an unrelated record");

    drop(toolchain.trustd.take());
    let refusing = fake_trustd::install_refusing(&toolchain.bin_dir);
    let output = fixture_command(&toolchain.targo_trust)
        .arg("check")
        .current_dir(&crate_dir)
        .env(fake_trustd::RUNTIME_DIR_ENV, refusing.runtime_dir())
        .env("TRUST_CAPTURE_FILE", toolchain.tmp_dir.join("capture.txt"))
        .env_remove("CARGO")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .output()
        .expect("run targo-trust check against a refusing trustd");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    drop(refusing);
    assert_eq!(output.status.code(), Some(3), "{stderr}");
    for path in &records {
        assert!(!path.exists(), "{} survived a run that wrote nothing\n{stderr}", path.display());
    }
    assert!(unrelated.is_file(), "a record of an unselected package is not this run's to remove");
}

// T7c: one workspace, one policy. A run started in a workspace member whose
// manifest carries a [trust] table of its own is refused before targo runs,
// naming the table's keys and the root's manifest; without the table, the run
// compiles at the root's level, as a run started in the root would.
#[test]
fn a_members_own_trust_table_is_refused_and_the_roots_policy_governs_it() {
    let toolchain = SharedFakeToolchain::install("targo-trust-root-only-policy");
    let workspace = toolchain.tmp_dir.join("ws");
    create_fixture_dir(&workspace);
    fs::write(
        workspace.join("Cargo.toml"),
        "[workspace]\nmembers = [\"crate\"]\n\n[trust]\nlevel = \"L1\"\n",
    )
    .expect("write the workspace root");
    let member = toolchain.fixture_crate("ws", "root-only-member");
    let manifest = member.join("Cargo.toml");
    let capture = toolchain.tmp_dir.join("capture.txt");

    let package = fs::read_to_string(&manifest).expect("read the member manifest");
    fs::write(&manifest, format!("{package}\n[trust]\nlevel = \"L0\"\n"))
        .expect("give the member a table");
    let (stdout, stderr, status) = toolchain.check(&member);
    assert_eq!(status, Some(2), "{stdout}\n{stderr}");
    assert!(
        stderr.contains("this workspace member declares a [trust] table (`level`)")
            && stderr.contains("workspace policy")
            && stderr.contains(&workspace.join("Cargo.toml").display().to_string()),
        "{stderr}"
    );
    assert!(!capture.exists(), "targo must not run under a refused policy\n{stderr}");

    fs::write(&manifest, package).expect("drop the member's table");
    let (stdout, stderr, status) = toolchain.check(&member);
    assert_eq!(status, Some(0), "{stdout}\n{stderr}");
    let capture = parse_targo_capture(&fs::read_to_string(&capture).expect("fake targo ran"));
    assert_eq!(
        capture_z_flag_values(&capture, "trust-verify-level"),
        vec!["1".to_string()],
        "the root's level reaches the compile\n{stderr}"
    );
    assert!(
        stderr.contains("is a workspace member; its policy is the workspace root's"),
        "{stderr}"
    );
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
    run_targo_trust_check_with_fake_toolchain_and_stub_delay(prefix, extra_args, extra_env, None)
}

/// As above; `stub_start_delay` makes the fake trustd sleep that many seconds
/// before it binds (see `fake_trustd::delay_start`).
fn run_targo_trust_check_with_fake_toolchain_and_stub_delay(
    prefix: &str,
    extra_args: &[&str],
    extra_env: &[(&str, &str)],
    stub_start_delay: Option<u32>,
) -> (Option<CapturedTCargoInvocation>, String, String, Option<i32>) {
    let tmp_dir = temp_test_dir(prefix);
    let crate_dir = tmp_dir.join("crate");
    let src_dir = crate_dir.join("src");
    let bin_dir = tmp_dir.join("toolchain").join("bin");
    create_fixture_dir(&src_dir);
    create_fixture_dir(&bin_dir);

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
    if let Some(seconds) = stub_start_delay {
        fake_trustd::delay_start(&bin_dir, seconds);
    }
    let _trustd = fake_trustd::install(&bin_dir);

    let mut command = fixture_command(&targo_trust);
    command
        .arg("check")
        .current_dir(&crate_dir)
        .env(fake_trustd::RUNTIME_DIR_ENV, _trustd.runtime_dir())
        .env("TRUST_CAPTURE_FILE", &capture_path)
        .env("CARGO_HOME", tmp_dir.join("cargo-home"))
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
    // Cargo fan-out is gated on an authenticated daemon, so a run that reached
    // the fake targo was served by one — and it must be THIS test's stub on
    // THIS test's private endpoint, never the host's shared one. `install`
    // started that stub; a run that looked anywhere else would have spawned
    // another, which records its own bind.
    if capture.is_some() {
        assert_eq!(
            _trustd.served_sockets(),
            [_trustd.socket().to_path_buf()],
            "targo-trust must use the stub inside the per-test {} domain and spawn none elsewhere\nstderr:\n{stderr}",
            fake_trustd::RUNTIME_DIR_ENV
        );
        assert!(
            stderr.contains("selects a separate trustd memory domain"),
            "a relocated memory domain must be disclosed\nstderr:\n{stderr}"
        );
    }

    // Drop the guard FIRST: it shuts the stub down on its private endpoint and
    // removes that runtime directory while the stub's executable (in tmp_dir)
    // still exists.
    drop(_trustd);
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
    run_targo_trust_check_with_policy_env(prefix, trust_table, trust_toml, &[])
}

fn run_targo_trust_check_with_policy_env(
    prefix: &str,
    trust_table: Option<&str>,
    trust_toml: Option<&str>,
    extra_env: &[(&str, &str)],
) -> (Option<CapturedTCargoInvocation>, String, String, Option<i32>) {
    let tmp_dir = temp_test_dir(prefix);
    let crate_dir = tmp_dir.join("crate");
    let src_dir = crate_dir.join("src");
    let bin_dir = tmp_dir.join("toolchain").join("bin");
    create_fixture_dir(&src_dir);
    create_fixture_dir(&bin_dir);

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

    let mut command = fixture_command(&targo_trust);
    command
        .arg("check")
        .current_dir(&crate_dir)
        .env(fake_trustd::RUNTIME_DIR_ENV, _trustd.runtime_dir())
        .env("TRUST_CAPTURE_FILE", &capture_path)
        .env_remove("CARGO")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS");
    for (key, value) in extra_env {
        command.env(key, value);
    }
    let output = command.output().expect("run targo-trust check with the policy fixture");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let capture = capture_path.exists().then(|| {
        let text = fs::read_to_string(&capture_path).expect("read fake targo capture");
        parse_targo_capture(&text)
    });

    // Drop the guard FIRST: it shuts the stub down on its private endpoint and
    // removes that runtime directory while the stub's executable (in tmp_dir)
    // still exists.
    drop(_trustd);
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
    printf 'TRUST_JSON:{"type":"coverage_summary","crate_name":"%s","eligible":1,"processed":1,"memory":{"schema":"trust-memory-summary/v1","counters":{}}}\n' "$crate_name" >&2
  else
    printf 'TRUST_JSON:{"type":"coverage_summary","crate_name":"trust_verify_probe","package_name":"","primary_package":false,"verification_session":"%s","eligible":1,"processed":1,"function_identities":{"schema":"trustc.coverage-function-identities.v1","eligible_functions":["trust_verify_probe::trust_verify_probe"],"processed_functions":["trust_verify_probe::trust_verify_probe"]},"memory":{"schema":"trust-memory-summary/v1","counters":{}}}\n' "$verification_session" >&2
  fi
  exit 0
fi
  payload=$(printf '%s' '__TRUST_DIRECT_PROVED_PAYLOAD__' | sed "s/__TRUST_VERIFICATION_SESSION__/$verification_session/g")
printf 'TRUST_JSON:%s\n' "$payload" >&2
if [ "${TRUST_FAKE_LEGACY_COVERAGE:-0}" = "1" ]; then
  printf 'TRUST_JSON:{"type":"coverage_summary","crate_name":"%s","eligible":1,"processed":1,"memory":{"schema":"trust-memory-summary/v1","counters":{}}}\n' "$crate_name" >&2
else
  printf 'TRUST_JSON:{"type":"coverage_summary","crate_name":"%s","package_name":"","primary_package":false,"verification_session":"%s","eligible":1,"processed":1,"function_identities":{"schema":"trustc.coverage-function-identities.v1","eligible_functions":["fixture::test"],"processed_functions":["fixture::test"]},"memory":{"schema":"trust-memory-summary/v1","counters":{}}}\n' "$crate_name" "$verification_session" >&2
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
verification_session=$(printf '%s\n' "${TRUST_TARGO_LANE_RUSTFLAGS-}" | tr '\037' ' ' | sed -n 's/.*trust-verify-session=\([^ ]*\).*/\1/p' | head -n 1)
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
previous_arg=
for arg in "$@"; do
  case "$arg" in
    metadata) mode=metadata ;;
    pkgid) mode=pkgid ;;
    trust-policy) if [ "$previous_arg" = "config" ]; then mode=trust-policy; fi ;;
  esac
  previous_arg="$arg"
done
# The authenticated project-policy query (`targo -Zunstable-options config
# trust-policy`) runs before lane selection and compiles nothing. Answer it
# with the real producer's `trust.project-policy.v1` shape for a project with
# no configured Trust requirements. It is deliberately not recorded: the
# capture is the record of Cargo invocations (compile and metadata/pkgid
# probes), and "fake targo must not run" assertions mean the compile.
if [ "$mode" = "trust-policy" ]; then
  # TRUST_FAKE_PROJECT_POLICY: a project whose Cargo configuration states
  # requirements, as the real producer prints them.
  if [ -n "${TRUST_FAKE_PROJECT_POLICY:-}" ]; then
    printf '%s\n' "$TRUST_FAKE_PROJECT_POLICY"
  else
    printf '%s\n' '__TRUST_EMPTY_PROJECT_POLICY__'
  fi
  exit 0
fi
# Cargo reads each path dependency's manifest before it resolves anything, in
# every mode: one that names nothing fails, as Cargo fails ("failed to read").
# A dependency is an inline `{ path = "..." }`, or a `path` key under a
# `[dependencies.<name>]` header (how a rewritten copy's manifest spells it).
for dependency in $(awk '
  /^\[/ { section = ($0 ~ /dependencies\./) }
  (section && /^path[[:space:]]*=/) || /\{.*path[[:space:]]*=/ {
    line = $0
    sub(/.*path[[:space:]]*=[[:space:]]*"/, "", line)
    sub(/".*/, "", line)
    print line
  }' Cargo.toml); do
  if [ ! -f "$dependency/Cargo.toml" ]; then
    printf 'error: failed to read `%s/%s/Cargo.toml`\n' "$PWD" "$dependency" >&2
    exit 101
  fi
done
{
  echo "kind=targo"
  echo "targo_mode=$mode"
  echo "program=$(basename "$0")"
  printf 'targo_arg=%s\n' "$@"
  echo "exported_rustc=$RUSTC"
  echo "rustflags=$RUSTFLAGS"
  echo "encoded_rustflags=$CARGO_ENCODED_RUSTFLAGS"
  echo "lane=${TRUST_TARGO_LANE_RUSTFLAGS-}"
  echo "trust_no_verify=$TRUST_NO_VERIFY"
  echo "trust_hardened=$TRUST_HARDENED"
  echo "trust_profile=$TRUST_PROFILE"
  echo "trust_verify_memory_safe=$TRUST_VERIFY_MEMORY_SAFE"
  echo "trust_verify_survey=$TRUST_VERIFY_SURVEY"
} >> "$TRUST_CAPTURE_FILE"
if [ "$mode" = "metadata" ]; then
  target_directory="${CARGO_TARGET_DIR:-$PWD/target}"
  printf '{"packages":[{"id":"%s","name":"%s","version":"0.0.0","manifest_path":"%s","targets":[{"kind":["lib"],"crate_types":["lib"],"name":"%s","src_path":"%s","edition":"2021","doc":true,"doctest":true,"test":true}]}],"workspace_members":["%s"],"workspace_default_members":["%s"],"workspace_root":"%s","target_directory":"%s","resolve":{"nodes":[{"id":"%s","deps":[]}]},"version":1}\n' \
    "$package_id" "$package_name" "$manifest" "$crate_name" "$source" "$package_id" "$package_id" "$PWD" "$target_directory" "$package_id"
  exit 0
fi
if [ "$mode" = "pkgid" ]; then
  printf '%s\n' "$package_id"
  exit 0
fi
# A compile that never ends by itself (T5a's lifecycle tests): a background
# descendant in the driver's own group, and `<driver> <descendant>` published
# once both run. TRUST_FAKE_TARGO_HANG_IGNORE_TERM makes both ignore SIGTERM.
if [ -n "${TRUST_FAKE_TARGO_HANG_PIDFILE:-}" ]; then
  if [ "${TRUST_FAKE_TARGO_HANG_IGNORE_TERM:-0}" = "1" ]; then
    trap '' TERM
  fi
  sleep 600 &
  printf '%s %s\n' "$$" "$!" > "$TRUST_FAKE_TARGO_HANG_PIDFILE.tmp"
  mv "$TRUST_FAKE_TARGO_HANG_PIDFILE.tmp" "$TRUST_FAKE_TARGO_HANG_PIDFILE"
  wait
  exit 0
fi

# The backstop ledger: what a test names, else what the run's own clock does.
# A per-query clock under 100 ms (`[trust] backstop = 1` passes 5 ms) fires on
# every solve, as the real compiler's does, so the stability verb's negative
# control reads the stop it must catch.
noted_stop="${TRUST_FAKE_TARGO_NOTED_STOP:-}"
vc_clock_ms=$(printf '%s\n' "${TRUST_TARGO_LANE_RUSTFLAGS-}" | tr '\037' '\n' | sed -n 's/.*trust-verify-timeout-ms=\([0-9][0-9]*\).*/\1/p' | head -n 1)
if [ -z "$noted_stop" ] && [ -n "$vc_clock_ms" ] && [ "$vc_clock_ms" -lt 100 ]; then
  noted_stop=wall-backstop
fi

emit_transport() {
  escaped=$(printf '%s' "$1" | sed 's/\\/\\\\/g; s/"/\\"/g')
  printf '{"reason":"compiler-message","package_id":"%s","trust_compile_target":"%s","trust_compile_mode":"%s","trust_compile_kind":"%s","trust_unit_identity_sha256":"%s","trust_proof_unit":%s,"target":{"name":"%s","kind":["lib"]},"message":{"message":"TRUST_JSON:%s","level":"note","code":{"code":"trust_verification_transport_v1","explanation":null},"rendered":null,"spans":[],"children":[]}}\n' \
    "$package_id" "$compile_target" "$compile_mode" "$compile_kind" "$unit_identity_sha256" "$proof_unit" "$crate_name" "$escaped"
}
emit_summary() {
  summary=$(printf '{"type":"crate_summary","crate_name":"%s","package_name":"%s","primary_package":true,"verification_session":"%s","functions_analyzed":1,"functions_verified":%s,"total_proved":%s,"total_failed":%s,"total_unknown":%s,"total_timed_out":0,"total_skipped":0,"total_runtime_checked":0,"total_obligations":1}' "$crate_name" "$package_name" "$verification_session" "$1" "$1" "${3:-0}" "$2")
  emit_transport "$summary"
}
emit_coverage() {
  if [ "${TRUST_FAKE_TARGO_NO_COVERAGE:-0}" != "1" ]; then
    if [ "${TRUST_FAKE_LEGACY_COVERAGE:-0}" = "1" ]; then
      coverage=$(printf '{"type":"coverage_summary","crate_name":"%s","eligible":1,"processed":1,"memory":{"schema":"trust-memory-summary/v1","counters":{}}}' "$crate_name")
    else
      coverage_primary=true
      if [ "${TRUST_FAKE_TARGO_NON_PRIMARY_COVERAGE:-0}" = "1" ]; then
        coverage_primary=false
      fi
      noted_stops=
      if [ -n "$noted_stop" ]; then
        noted_stops=$(printf ',"noted_stops":[{"lane":"fixture-lane","cause":"%s","count":1}]' "$noted_stop")
      fi
      coverage=$(printf '{"type":"coverage_summary","crate_name":"%s","package_name":"%s","primary_package":%s,"verification_session":"%s","eligible":1,"processed":1,"function_identities":{"schema":"trustc.coverage-function-identities.v1","eligible_functions":["%s"],"processed_functions":["%s"]},"memory":{"schema":"trust-memory-summary/v1","counters":{}}%s}' "$crate_name" "$package_name" "$coverage_primary" "$verification_session" "$1" "$1" "$noted_stops")
    fi
    emit_transport "$coverage"
  fi
}
# A test may declare a second proof unit -- another view of the same library
# -- that fails to compile: it is in the inventory, it never concludes, and the
# build finishes unsuccessfully (`TRUST_FAKE_TARGO_UNFINISHED_UNIT`).
build_success=true
unfinished_unit_identity="dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
unfinished_proof_unit="{\"schema\":\"targo.trust-proof-unit.v2\",\"index\":1,\"mode\":\"$compile_mode\",\"role\":\"primary\",\"package_name\":\"$package_name\",\"semantics_sha256\":\"$semantics_sha256\"}"
if [ "${TRUST_FAKE_TARGO_UNFINISHED_UNIT:-0}" = "1" ]; then
  build_success=false
fi
emit_artifact() {
  printf '{"reason":"compiler-artifact","package_id":"%s","trust_compile_target":"%s","trust_compile_mode":"%s","trust_compile_kind":"%s","trust_unit_identity_sha256":"%s","trust_proof_unit":%s,"target":{"name":"%s","kind":["lib"]},"profile":{"opt_level":"0","debuginfo":0,"debug_assertions":false,"overflow_checks":false,"test":false},"features":[],"fresh":false}\n' \
    "$package_id" "$compile_target" "$compile_mode" "$compile_kind" "$unit_identity_sha256" "$proof_unit" "$crate_name"
  if [ "$build_success" = false ]; then
    printf '{"reason":"compiler-message","package_id":"%s","trust_compile_target":"%s","trust_compile_mode":"%s","trust_compile_kind":"%s","trust_unit_identity_sha256":"%s","trust_proof_unit":%s,"target":{"name":"%s","kind":["lib"]},"message":{"message":"cannot find value `missing` in this scope","level":"error","code":{"code":"E0425","explanation":null},"rendered":"error[E0425]: cannot find value `missing` in this scope\\n","spans":[],"children":[]}}\n' \
      "$package_id" "$compile_target" "$compile_mode" "$compile_kind" "$unfinished_unit_identity" "$unfinished_proof_unit" "$crate_name"
  fi
  printf '{"reason":"build-finished","success":%s}\n' "$build_success"
}
inventory_unit() { # inventory_unit <proof unit> <unit identity>
  printf '{"trust_proof_unit":%s,"semantics":%s,"package_id":"%s","target_name":"%s","target_kinds":["lib"],"compile_target":"%s","trust_compile_mode":"%s","trust_compile_kind":"%s","trust_unit_identity_sha256":"%s"}' \
    "$1" "$unit_semantics" "$package_id" "$crate_name" "$compile_target" "$compile_mode" "$compile_kind" "$2"
}
inventory_units=$(inventory_unit "$proof_unit" "$unit_identity_sha256")
if [ "$build_success" = false ]; then
  inventory_units="$inventory_units,$(inventory_unit "$unfinished_proof_unit" "$unfinished_unit_identity")"
fi
printf '{"reason":"trust-proof-inventory","schema":"targo.trust-proof-inventory.v2","include_dependencies":true,"units":[%s],"excluded_units":[]}\n' "$inventory_units"
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
  kind="${TRUST_FAKE_TARGO_ASSUMPTION_KIND:-assumption:test}"
  solver="${TRUST_FAKE_TARGO_ASSUMPTION_SOLVER:-test}"
  result_outcome=unknown
  proved=0
  unknown=1
elif [ "$outcome" = "failed" ]; then
  proved=0
  unknown=0
else
  proved=0
  unknown=1
fi
failed=0
if [ "$outcome" = "failed" ]; then
  failed=1
fi
# Every row carries its T9 stable id unless a test asks for a keyless one, and
# a plain unknown row states a reproducible stop unless a test names another
# (`TRUST_FAKE_TARGO_STOP=` with no value states none, which is `unclassified`).
stable_ids='"stable_ids":["__FIXTURE_STABLE_ID__"],'
if [ "${TRUST_FAKE_TARGO_NO_STABLE_IDS:-0}" = "1" ]; then
  stable_ids=
fi
reason=
stop="${TRUST_FAKE_TARGO_STOP-solver-incomplete}"
# A deliberately NONDETERMINISTIC input, for the stability verb's negative
# control and nowhere else: each compile reads and advances a counter in this
# file, and an odd count stops the unknown row on `effort` instead.
if [ -n "${TRUST_FAKE_TARGO_NONDETERMINISTIC_STOP_FILE:-}" ]; then
  compiles=$(cat "$TRUST_FAKE_TARGO_NONDETERMINISTIC_STOP_FILE" 2>/dev/null || echo 0)
  printf '%s\n' "$((compiles + 1))" > "$TRUST_FAKE_TARGO_NONDETERMINISTIC_STOP_FILE"
  if [ $((compiles % 2)) -eq 1 ]; then
    stop=effort
  fi
fi
if [ "$outcome" = "unknown" ] && [ -n "$stop" ]; then
  reason=",\"reason\":\"fixture search ended [stop:$stop]\""
fi
if [ "$outcome" = "failed" ]; then
  reason=",\"counterexample\":\"x = 0\""
fi
if [ "$outcome" = "assumption" ] && [ "${TRUST_FAKE_TARGO_UNMARKED_ASSUMPTION:-0}" != "1" ]; then
  case "${TRUST_TARGO_LANE_RUSTFLAGS-}" in
    *trust-policy=memory-safe*)
      solver=trust-memory-safe
      kind=assumption:memory-safe-panic
      ;;
    *trust-policy=advisory*)
      # What advisory policy records for a `#[trust::skip]` function (measured
      # with trustc 0.10.0+g450403669); strict policy refuses that function with
      # a compile error.
      solver=trust-policy
      kind=assumption:user-opt-out
      ;;
  esac
fi
if [ "$outcome" = "proved" ]; then
  payload=$(printf '%s' '__TRUST_PROVED_PAYLOAD__' | sed "s/__TRUST_CRATE_NAME__/$crate_name/g; s/__TRUST_PACKAGE_NAME__/$package_name/g; s/__TRUST_VERIFICATION_SESSION__/$verification_session/g")
  if [ -z "$stable_ids" ]; then
    payload=$(printf '%s' "$payload" | sed 's/"stable_ids":\["__FIXTURE_STABLE_ID__"\],//')
  fi
  function_identity="fixture::test"
else
  payload=$(printf '{"type":"function_result","function":"%s::test",%s"package_name":"%s","crate_name":"%s","primary_package":true,"verification_session":"%s","results":[{"kind":"%s","description":"test","outcome":"%s","solver":"%s","time_ms":0%s}],"proved":%s,"failed":%s,"unknown":%s,"timed_out":0,"skipped":0,"runtime_checked":0,"cached":0,"total":1}' "$crate_name" "$stable_ids" "$package_name" "$crate_name" "$verification_session" "$kind" "$result_outcome" "$solver" "$reason" "$proved" "$failed" "$unknown")
  function_identity="$crate_name::test"
fi
emit_transport "$payload"
emit_coverage "$function_identity"
emit_summary "$proved" "$unknown" "$failed"
emit_artifact
exit "$exit_code"
"#
    .replace("__TRUST_FULL_VERIFIER_PAYLOAD__", &fake_full_verifier_payload())
    .replace("__TRUST_PROVED_PAYLOAD__", &fake_proved_payload())
    .replace("__TRUST_EMPTY_PROJECT_POLICY__", EMPTY_PROJECT_POLICY_RESPONSE)
    .replace("__FIXTURE_STABLE_ID__", FIXTURE_STABLE_ID)
}

/// What the native producer
/// (`src/tools/targo/src/cargo/core/compiler/build_context/project_policy.rs`,
/// `ProjectTrustPolicy::default()` serialized by `targo -Zunstable-options
/// config trust-policy`) answers for a project that configures no Trust
/// requirements: every requirement `null`, verification not required. The
/// consumer parses it with `deny_unknown_fields`, so this must stay the exact
/// `trust.project-policy.v1` field set — never a Cargo build message.
/// The T9 stable local id every fixture row carries (one row per function
/// envelope). A row without one makes the run could-not-run (exit 3), which
/// only the tests that ask for it (`TRUST_FAKE_TARGO_NO_STABLE_IDS`) want.
const FIXTURE_STABLE_ID: &str = "00000000000000a1";

const EMPTY_PROJECT_POLICY_RESPONSE: &str = r#"{"schema":"trust.project-policy.v1","policy":null,"level":null,"profile":null,"include_dependencies":null,"ir_lower":null,"verification_required":false}"#;

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
            stable_ids: vec![FIXTURE_STABLE_ID.to_string()],
            source_sha256: None,
            expanded_function_identity: None,
            modeled_facts: Vec::new(),
            function,
            package_name: Some(PACKAGE_NAME.to_string()),
            crate_name: Some(CRATE_NAME.to_string()),
            primary_package: true,
            verification_session: SESSION_PLACEHOLDER.to_string(),
            runtime_checks: None,
            results: vec![result],
            proved: 1,
            failed: 0,
            unknown: 0,
            timed_out: 0,
            skipped: 0,
            runtime_checked: 0,
            cached: 0,
            total: 1,
            transport_budget: None,
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
            stable_ids: vec![FIXTURE_STABLE_ID.to_string()],
            source_sha256: None,
            expanded_function_identity: None,
            modeled_facts: Vec::new(),
            function,
            package_name: None,
            crate_name: Some(CRATE_NAME.to_string()),
            primary_package: false,
            verification_session: SESSION_PLACEHOLDER.to_string(),
            runtime_checks: None,
            results: vec![result],
            proved: 1,
            failed: 0,
            unknown: 0,
            timed_out: 0,
            skipped: 0,
            runtime_checked: 0,
            cached: 0,
            total: 1,
            transport_budget: None,
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
            stable_ids: vec![FIXTURE_STABLE_ID.to_string()],
            source_sha256: None,
            expanded_function_identity: None,
            modeled_facts: Vec::new(),
            function,
            package_name: Some(PACKAGE_NAME.to_string()),
            crate_name: Some(CRATE_NAME.to_string()),
            primary_package: true,
            verification_session: SESSION_PLACEHOLDER.to_string(),
            runtime_checks: None,
            results: vec![result],
            proved: 1,
            failed: 0,
            unknown: 0,
            timed_out: 0,
            skipped: 0,
            runtime_checked: 0,
            cached: 0,
            total: 1,
            transport_budget: None,
        });
    let payload = serde_json::to_string(&message).expect("serialize fake full-verifier payload");
    assert!(
        !payload.contains('\''),
        "payload must remain safe for the shell single-quoted literal"
    );
    payload
}

/// Write a fake executable and execute it once, before the test hands it to
/// `targo-trust`.
///
/// macOS assesses a freshly written executable on its FIRST `execve`, and that
/// assessment is serialized system-wide (measured 2026-10-04: thirty new
/// two-line scripts exec'd concurrently finished 0.16 s apart, 4.8 s for the
/// last; a second exec of each took no measurable time). With the suite's
/// tests running in parallel, each copying a fresh `targo-trust` and writing
/// fresh fakes, that queue reached tens of seconds — and the first exec of the
/// fake `trustc`/`targo` now happens inside `targo-trust`'s fixed 30 s
/// project-policy setup allowance, which then expired on OS latency the
/// product never sees with an installed toolchain. Paying the first exec here,
/// outside every product deadline, leaves each deadline measuring only what
/// the fixture does. The prewarm line exits before any side effect, so a fake
/// that "must not run" still records nothing.
fn write_executable(path: &Path, contents: impl AsRef<[u8]>) {
    let contents = contents.as_ref();
    let shebang: &[u8] = b"#!/bin/sh\n";
    let contents = match contents.strip_prefix(shebang) {
        Some(body) => [shebang, PREWARM_EXIT, body].concat(),
        None => panic!("fake executables are /bin/sh scripts: {}", path.display()),
    };
    fs::write(path, contents).expect("write fake executable");
    let mut permissions = fs::metadata(path).expect("fake executable metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).expect("chmod fake executable");
    let status = Command::new(path)
        .env("TRUST_FIXTURE_PREWARM", "1")
        .status()
        .expect("prewarm fake executable");
    assert!(status.success(), "prewarm of {} failed: {status}", path.display());
}

const PREWARM_EXIT: &[u8] = b"[ \"${TRUST_FIXTURE_PREWARM:-}\" = 1 ] && exit 0\n";

/// The environment one fake `targo` invocation saw.
#[derive(Default, Clone)]
struct TargoInvocationEnv {
    exported_rustc: Option<String>,
    rustflags: Option<String>,
    encoded_rustflags: Option<String>,
    lane: Option<String>,
    trust_no_verify: Option<String>,
    trust_hardened: Option<String>,
    trust_profile: Option<String>,
    trust_verify_memory_safe: Option<String>,
    trust_verify_survey: Option<String>,
}

/// Every invocation's arguments are kept, in order. The environment fields
/// describe the COMPILE invocation (the last non-`metadata`/`pkgid` one):
/// `targo trust check` and `build` also run `targo metadata` probes after the
/// compile (the Kani/Creusot disclosures, TRUST-26), and those run with the
/// sanitized probe environment, which is not what these tests pin. A capture
/// with no compile invocation falls back to the last probe's environment.
fn parse_targo_capture(capture: &str) -> CapturedTCargoInvocation {
    let mut in_targo = false;
    let mut program = None;
    let mut args = Vec::new();
    let mut compile_env: Option<TargoInvocationEnv> = None;
    let mut probe_env: Option<TargoInvocationEnv> = None;
    let mut current = TargoInvocationEnv::default();
    let mut current_is_probe = false;

    {
        let mut finish = |current: &mut TargoInvocationEnv, is_probe: bool| {
            let env = std::mem::take(current);
            if is_probe {
                probe_env = Some(env);
            } else {
                compile_env = Some(env);
            }
        };

        for line in capture.lines() {
            if line == "kind=targo" {
                if in_targo {
                    finish(&mut current, current_is_probe);
                }
                in_targo = true;
                current_is_probe = false;
                continue;
            }
            if line.starts_with("kind=") {
                if in_targo {
                    finish(&mut current, current_is_probe);
                }
                in_targo = false;
                continue;
            }
            if !in_targo {
                continue;
            }

            if let Some(mode) = line.strip_prefix("targo_mode=") {
                current_is_probe = matches!(mode, "metadata" | "pkgid");
            } else if let Some(value) = line.strip_prefix("program=") {
                program = Some(value.to_string());
            } else if let Some(arg) = line.strip_prefix("targo_arg=") {
                args.push(arg.to_string());
            } else if let Some(value) = line.strip_prefix("exported_rustc=") {
                current.exported_rustc = Some(value.to_string());
            } else if let Some(value) = line.strip_prefix("rustflags=") {
                current.rustflags = Some(value.to_string());
            } else if let Some(value) = line.strip_prefix("encoded_rustflags=") {
                current.encoded_rustflags = Some(value.to_string());
            } else if let Some(value) = line.strip_prefix("lane=") {
                current.lane = Some(value.to_string());
            } else if let Some(value) = line.strip_prefix("trust_no_verify=") {
                current.trust_no_verify = Some(value.to_string());
            } else if let Some(value) = line.strip_prefix("trust_hardened=") {
                current.trust_hardened = Some(value.to_string());
            } else if let Some(value) = line.strip_prefix("trust_profile=") {
                current.trust_profile = Some(value.to_string());
            } else if let Some(value) = line.strip_prefix("trust_verify_memory_safe=") {
                current.trust_verify_memory_safe = Some(value.to_string());
            } else if let Some(value) = line.strip_prefix("trust_verify_survey=") {
                current.trust_verify_survey = Some(value.to_string());
            }
        }
        if in_targo {
            finish(&mut current, current_is_probe);
        }
    }

    let env = compile_env.or(probe_env).unwrap_or_default();
    CapturedTCargoInvocation {
        program: program.expect("fake targo capture should include program name"),
        args,
        exported_rustc: env.exported_rustc.unwrap_or_default(),
        rustflags_env: env.rustflags.expect("fake targo capture should include RUSTFLAGS"),
        encoded_rustflags_env: env.encoded_rustflags.unwrap_or_default(),
        lane_env: env.lane.unwrap_or_default(),
        trust_no_verify: env.trust_no_verify.unwrap_or_default(),
        trust_hardened: env.trust_hardened.unwrap_or_default(),
        trust_profile: env.trust_profile.unwrap_or_default(),
        trust_verify_memory_safe: env.trust_verify_memory_safe.unwrap_or_default(),
        trust_verify_survey: env.trust_verify_survey.unwrap_or_default(),
    }
}

/// The lane's arguments: the verifier policy targo trust hands the compile.
/// The caller's RUSTFLAGS and CARGO_ENCODED_RUSTFLAGS reach Cargo unchanged
/// (T14a), and the sibling Targo resolves them; these helpers read the lane.
fn capture_lane_args(capture: &CapturedTCargoInvocation) -> Vec<&str> {
    capture.lane_env.split('\x1f').filter(|argument| !argument.is_empty()).collect()
}

fn capture_has_z_flag(capture: &CapturedTCargoInvocation, flag: &str) -> bool {
    has_z_flag(&capture_lane_args(capture), flag)
}

fn capture_has_z_option_prefix(capture: &CapturedTCargoInvocation, prefix: &str) -> bool {
    has_z_option_prefix(&capture_lane_args(capture), prefix)
}

/// Every value the lane gives `-Z<name>`, in argv order.
fn capture_z_flag_values(capture: &CapturedTCargoInvocation, name: &str) -> Vec<String> {
    let args = capture_lane_args(capture);
    let prefix = format!("{name}=");
    let mut values = Vec::new();
    let mut index = 0;
    while index < args.len() {
        let option = if args[index] == "-Z" {
            index += 1;
            args.get(index).copied()
        } else {
            args[index].strip_prefix("-Z").filter(|option| !option.is_empty())
        };
        if let Some(value) = option.and_then(|option| option.strip_prefix(&prefix)) {
            values.push(value.to_string());
        }
        index += 1;
    }
    values
}

fn capture_codegen_option_values(capture: &CapturedTCargoInvocation, name: &str) -> Vec<String> {
    let args = capture_lane_args(capture);
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
        || args.contains(&compact.as_str())
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

/// T5a: the process lifecycle of a real `targo-trust check`, driven through the
/// fake toolchain with a compile that never ends by itself
/// (`TRUST_FAKE_TARGO_HANG_PIDFILE`). The compile's driver and its background
/// descendant must outlive neither a SIGTERM nor a SIGKILL to targo-trust, nor
/// the end of the process that started it; a second SIGINT cuts the stop's
/// grace short; and every stop names its cause. Each run has its own fake
/// trustd on a private endpoint, so no test here starts, stops or signals a
/// trustd on the per-user socket.
///
/// targo-trust keeps a signal that was IGNORED when it started ignored, and
/// with SIGHUP ignored it does not watch its parent either (by design:
/// `process_lifecycle/signals.rs`). Whoever runs this test binary decides
/// those dispositions -- `nohup` hands on SIGHUP ignored, a shell's background
/// job SIGINT and SIGQUIT -- so each test names the signals whose disposition
/// it asserts on, and the fixture puts exactly those back to their default in
/// the child it starts ([`HangingCheck::start`]). The tests whose point IS an
/// inherited ignore, one per signal in `a_signal_ignored_at_start_stays_ignored`,
/// set that ignore themselves ([`HangingCheck::start_with_dispositions`]).
mod process_lifecycle {
    use std::fs;
    use std::io::Read as _;
    use std::os::unix::process::{CommandExt as _, ExitStatusExt as _};
    use std::path::{Path, PathBuf};
    use std::process::{Child, ExitStatus, Stdio};
    use std::sync::{Arc, Mutex};
    use std::thread::JoinHandle;
    use std::time::{Duration, Instant};

    use super::{
        create_fixture_dir, fake_targo_script, fake_trustc_script, fake_trustd, fixture_command,
        install_targo_trust_binary, temp_test_dir, write_executable,
    };

    /// Hang detectors, not latency budgets. Reaching the compile runs the whole
    /// preflight of a freshly copied executable, which a loaded host can hold
    /// at its first exec for minutes.
    const REACH_COMPILE: Duration = Duration::from_secs(15 * 60);
    const HANG: Duration = Duration::from_secs(120);

    struct HangingCheck {
        /// targo-trust itself, or the shell that started it.
        child: Child,
        targo_trust: u32,
        driver: u32,
        descendant: u32,
        stderr: Arc<Mutex<String>>,
        reader: Option<JoinHandle<()>>,
        tmp_dir: PathBuf,
        trustd: Option<fake_trustd::FakeTrustd>,
    }

    impl HangingCheck {
        /// Start `targo-trust check` on a fixture crate whose compile hangs,
        /// directly or (`behind_shell`) as the background job of a shell, and
        /// return once the compile's driver and descendant both run.
        ///
        /// `asserts_on` names the signals whose DISPOSITION the test asserts
        /// on: the started process gets each of them at its default action,
        /// whatever this test binary inherited, and passes that on to
        /// everything under it (a shell hands SIGHUP and SIGTERM to its
        /// background job as it has them). Nothing else is reset.
        fn start(
            prefix: &str,
            extra_env: &[(&str, &str)],
            behind_shell: bool,
            asserts_on: &[libc::c_int],
        ) -> Self {
            Self::start_with_dispositions(prefix, extra_env, behind_shell, asserts_on, &[])
        }

        /// As [`Self::start`], and the started process also gets each signal
        /// in `ignored` IGNORED, as `nohup` or a shell's background job hands
        /// it on: for a test whose point is what targo-trust does with an
        /// inherited ignore.
        fn start_with_dispositions(
            prefix: &str,
            extra_env: &[(&str, &str)],
            behind_shell: bool,
            asserts_on: &[libc::c_int],
            ignored: &[libc::c_int],
        ) -> Self {
            let tmp_dir = temp_test_dir(prefix);
            let crate_dir = tmp_dir.join("crate");
            let src_dir = crate_dir.join("src");
            let bin_dir = tmp_dir.join("toolchain").join("bin");
            create_fixture_dir(&src_dir);
            create_fixture_dir(&bin_dir);
            fs::write(
                crate_dir.join("Cargo.toml"),
                "[package]\nname = \"lifecycle-fixture\"\nversion = \"0.0.0\"\nedition = \"2021\"\n",
            )
            .expect("write fixture manifest");
            fs::write(src_dir.join("lib.rs"), "pub fn id(x: usize) -> usize { x }\n")
                .expect("write fixture source");
            let targo_trust = install_targo_trust_binary(&bin_dir);
            write_executable(&bin_dir.join("trustc"), fake_trustc_script());
            write_executable(&bin_dir.join("targo"), fake_targo_script());
            write_executable(&bin_dir.join("ay"), "#!/bin/sh\nprintf 'ay 0.0.0\\n'\n");
            let trustd = fake_trustd::install(&bin_dir);
            let pid_file = tmp_dir.join("hang.pids");

            let mut command = if behind_shell {
                let mut command = fixture_command(Path::new("/bin/sh"));
                command.args(["-c", "\"$0\" check & wait"]).arg(&targo_trust);
                command
            } else {
                let mut command = fixture_command(&targo_trust);
                command.arg("check");
                command
            };
            command
                .current_dir(&crate_dir)
                .env(fake_trustd::RUNTIME_DIR_ENV, trustd.runtime_dir())
                .env("TRUST_CAPTURE_FILE", tmp_dir.join("capture.txt"))
                .env("CARGO_HOME", tmp_dir.join("cargo-home"))
                .env("AY_PATH", bin_dir.join("ay"))
                .env("TRUST_FAKE_TARGO_HANG_PIDFILE", &pid_file)
                .env_remove("CARGO")
                .env_remove("RUSTFLAGS")
                .env_remove("CARGO_ENCODED_RUSTFLAGS")
                .stdin(Stdio::null())
                .stdout(Stdio::null())
                .stderr(Stdio::piped());
            for (key, value) in extra_env {
                command.env(key, value);
            }
            let asserted = asserts_on.to_vec();
            let ignored = ignored.to_vec();
            // SAFETY: the hook runs between fork and exec and calls only
            // `signal`, which is async-signal-safe; `asserted` and `ignored`
            // were built before the fork and are only read, so nothing
            // allocates.
            unsafe {
                command.pre_exec(move || {
                    for (signals, disposition) in
                        [(&asserted, libc::SIG_DFL), (&ignored, libc::SIG_IGN)]
                    {
                        for &signal in signals {
                            if libc::signal(signal, disposition) == libc::SIG_ERR {
                                return Err(std::io::Error::last_os_error());
                            }
                        }
                    }
                    Ok(())
                });
            }
            let mut child = command.spawn().expect("start targo-trust check");
            let stderr = Arc::new(Mutex::new(String::new()));
            let mut pipe = child.stderr.take().expect("stderr pipe");
            let sink = Arc::clone(&stderr);
            let reader = std::thread::spawn(move || {
                let mut chunk = [0_u8; 4096];
                while let Ok(read) = pipe.read(&mut chunk) {
                    if read == 0 {
                        break;
                    }
                    sink.lock()
                        .expect("stderr sink")
                        .push_str(&String::from_utf8_lossy(&chunk[..read]));
                }
            });
            let mut run = HangingCheck {
                child,
                targo_trust: 0,
                driver: 0,
                descendant: 0,
                stderr,
                reader: Some(reader),
                tmp_dir,
                trustd: Some(trustd),
            };
            let deadline = Instant::now() + REACH_COMPILE;
            let pids = loop {
                if let Ok(text) = fs::read_to_string(&pid_file) {
                    break text;
                }
                if let Ok(Some(status)) = run.child.try_wait() {
                    panic!("the check ended before its compile ({status:?}):\n{}", run.stderr());
                }
                assert!(Instant::now() < deadline, "the compile never started:\n{}", run.stderr());
                std::thread::sleep(Duration::from_millis(20));
            };
            let mut fields = pids.split_whitespace().map(|pid| pid.parse::<u32>().expect("pid"));
            run.driver = fields.next().expect("driver pid");
            run.descendant = fields.next().expect("descendant pid");
            run.targo_trust = if behind_shell {
                children_of(run.child.id(), "targo-trust")
                    .into_iter()
                    .next()
                    .expect("the shell's targo-trust")
            } else {
                run.child.id()
            };
            assert!(running(run.driver) && running(run.descendant), "the compile must be running");
            run
        }

        fn stderr(&self) -> String {
            self.stderr.lock().expect("stderr sink").clone()
        }

        fn signal(&self, pid: u32, signal: libc::c_int) {
            // SAFETY: a pid this test started (or its targo-trust); no pointers.
            assert_eq!(unsafe { libc::kill(pid as libc::pid_t, signal) }, 0, "signal {pid}");
        }

        /// Wait for the started process and for its stderr to close.
        fn wait(&mut self) -> ExitStatus {
            let deadline = Instant::now() + HANG;
            let status = loop {
                if let Some(status) = self.child.try_wait().expect("poll targo-trust") {
                    break status;
                }
                assert!(Instant::now() < deadline, "targo-trust never exited:\n{}", self.stderr());
                std::thread::sleep(Duration::from_millis(10));
            };
            await_gone(self.targo_trust, "targo-trust");
            if let Some(reader) = self.reader.take() {
                let _ = reader.join();
            }
            status
        }

        fn assert_compile_stopped(&self) {
            await_gone(self.driver, "the compile's driver");
            await_gone(self.descendant, "the compile's background descendant");
        }
    }

    impl Drop for HangingCheck {
        fn drop(&mut self) {
            // Whatever a failed assertion left running, this test started it.
            for pid in [self.descendant, self.driver, self.targo_trust] {
                if pid != 0 && running(pid) {
                    // SAFETY: as in `signal`.
                    unsafe { libc::kill(pid as libc::pid_t, libc::SIGKILL) };
                }
            }
            let _ = self.child.kill();
            let _ = self.child.wait();
            drop(self.trustd.take());
            let _ = fs::remove_dir_all(&self.tmp_dir);
        }
    }

    /// Running, and not a zombie (`ps` prints nothing for a pid that is gone).
    fn running(pid: u32) -> bool {
        let output = std::process::Command::new("ps")
            .args(["-o", "stat=", "-p", &pid.to_string()])
            .output()
            .expect("run ps");
        let state = String::from_utf8_lossy(&output.stdout).trim().to_string();
        !state.is_empty() && !state.starts_with('Z')
    }

    fn await_gone(pid: u32, what: &str) {
        let deadline = Instant::now() + HANG;
        while running(pid) {
            assert!(Instant::now() < deadline, "{what} (pid {pid}) outlived the stop");
            std::thread::sleep(Duration::from_millis(20));
        }
    }

    /// `parent`'s children whose command line contains `needle`.
    fn children_of(parent: u32, needle: &str) -> Vec<u32> {
        let output = std::process::Command::new("pgrep")
            .args(["-P", &parent.to_string(), "-f", needle])
            .output()
            .expect("run pgrep");
        String::from_utf8_lossy(&output.stdout)
            .split_whitespace()
            .filter_map(|pid| pid.parse().ok())
            .collect()
    }

    #[test]
    fn sigterm_stops_the_compile_and_the_run_could_not_run() {
        // Asserts that SIGTERM stops the run and that the compile honours it.
        let mut run = HangingCheck::start("targo-trust-t5a-sigterm", &[], false, &[libc::SIGTERM]);
        run.signal(run.targo_trust, libc::SIGTERM);
        let status = run.wait();
        let stderr = run.stderr();
        run.assert_compile_stopped();
        assert_eq!(status.code(), Some(3), "an interrupted run exits 3:\n{stderr}");
        // The driver and its descendant, both of which honour SIGTERM.
        assert!(
            stderr.contains(
                "COULD NOT RUN: interrupted by SIGTERM; stopped 1 child process tree(s): SIGTERM \
                 to 2 process(es). The run"
            ),
            "the stop must say what it stopped, and that nothing needed SIGKILL:\n{stderr}"
        );
        assert!(
            stderr.contains("(stop cause: signal SIGTERM)"),
            "the cause is recorded:\n{stderr}"
        );
    }

    #[test]
    fn sigkill_leaves_the_stop_to_the_sentinel() {
        // SIGKILL has no disposition, and the sentinel sets its own.
        let mut run = HangingCheck::start("targo-trust-t5a-sigkill", &[], false, &[]);
        let sentinels = children_of(run.targo_trust, "__targo_stop_sentinel");
        assert_eq!(sentinels.len(), 1, "one stop sentinel per run:\n{}", run.stderr());
        run.signal(run.targo_trust, libc::SIGKILL);
        let status = run.wait();
        run.assert_compile_stopped();
        await_gone(sentinels[0], "the stop sentinel");
        assert_eq!(status.signal(), Some(libc::SIGKILL));
    }

    /// The compile ignores SIGTERM, so only a second signal ends it before
    /// the 10 s grace does. Both signals are sent at once, so nothing here
    /// races the grace: the stopper reads the first as the cause and finds the
    /// second waiting at its first look during the grace. They are two
    /// different signals because two pending SIGINTs merge into one.
    #[test]
    fn a_second_signal_sends_sigkill_at_once() {
        // Asserts that BOTH signals count: an inherited ignore of either
        // leaves one signal, and then only the 10 s grace ends the compile.
        let mut run = HangingCheck::start(
            "targo-trust-t5a-second-signal",
            &[("TRUST_FAKE_TARGO_HANG_IGNORE_TERM", "1")],
            false,
            &[libc::SIGINT, libc::SIGTERM],
        );
        run.signal(run.targo_trust, libc::SIGINT);
        run.signal(run.targo_trust, libc::SIGTERM);
        let status = run.wait();
        let stderr = run.stderr();
        run.assert_compile_stopped();
        assert_eq!(status.code(), Some(3), "{stderr}");
        let (first, second) = if stderr.contains("(stop cause: signal SIGINT)") {
            ("SIGINT", "SIGTERM")
        } else {
            ("SIGTERM", "SIGINT")
        };
        assert!(stderr.contains(&format!("(stop cause: signal {first})")), "{stderr}");
        assert!(
            stderr.contains(&format!("then SIGKILL to 2 at once on a second signal ({second})")),
            "the second signal must escalate:\n{stderr}"
        );
    }

    /// A signal that was IGNORED when targo-trust started stays ignored: the
    /// `nohup` or the shell that handed it on asked for that
    /// (`process_lifecycle/signals.rs`), and targo-trust keeps it for each of
    /// the three signals it otherwise stops on. Nothing else in this suite
    /// would notice if targo-trust installed its handlers anyway.
    ///
    /// The ignored signal and one other, at its default, are sent at once to
    /// a compile that ignores SIGTERM, as in
    /// `a_second_signal_sends_sigkill_at_once`. With the ignore kept, the
    /// other signal is the only one: it is the cause, and only the end of the
    /// grace kills the compile. With the ignore lost, the ignored signal
    /// counts too, and whichever of the two comes second escalates, in either
    /// order. Each test sets the ignore itself, and the other signal, which
    /// it asserts on, to its default; the point of these tests IS an
    /// inherited disposition.
    mod a_signal_ignored_at_start_stays_ignored {
        use super::*;

        /// A window for a parent watch that should not exist to show itself:
        /// four of the 250ms polls with which targo-trust watches its parent
        /// when SIGHUP was not ignored. Not a bound the product must meet: a
        /// run that keeps the ignore does nothing in it, so the window can
        /// only fail to catch a defect on a host too loaded to poll, never
        /// fail a correct run.
        const PARENT_WATCH_WINDOW: Duration = Duration::from_secs(1);

        /// Send `ignored` and then `counted` to the run's targo-trust, and
        /// check that only `counted` counted. Returns the started process's
        /// exit status and targo-trust's stderr.
        fn assert_only_the_other_signal_counts(
            mut run: HangingCheck,
            ignored: libc::c_int,
            counted: (libc::c_int, &str),
        ) -> (ExitStatus, String) {
            let (counted, name) = counted;
            run.signal(run.targo_trust, ignored);
            run.signal(run.targo_trust, counted);
            let status = run.wait();
            let stderr = run.stderr();
            run.assert_compile_stopped();
            assert!(
                stderr.contains(&format!("(stop cause: signal {name})")),
                "the other signal was ignored at start, so {name} is the cause:\n{stderr}"
            );
            // Not the announcement ("... or at once on a second signal)"):
            // the account of what the stop did, which names the second signal.
            assert!(
                !stderr.contains("at once on a second signal ("),
                "a signal ignored at start must not count, first or second:\n{stderr}"
            );
            // The time is the one measured: the 10 s grace (`STOP_GRACE`) and
            // the walk after it. So it is at least the grace, which is what
            // says the grace ended the compile; how far past it a loaded host's
            // poll and walk run is no bound the product must meet.
            let after_sigterm = stderr
                .split_once("then SIGKILL to 2 still running ")
                .and_then(|(_, rest)| rest.split_once(" s after the SIGTERM"))
                .and_then(|(seconds, _)| seconds.parse::<f64>().ok());
            assert!(
                after_sigterm.is_some_and(|seconds| seconds >= 10.0),
                "with no second signal only the grace ends a compile that ignores SIGTERM:\n{stderr}"
            );
            (status, stderr)
        }

        #[test]
        fn sigint() {
            let run = HangingCheck::start_with_dispositions(
                "targo-trust-t5a-ignored-int",
                &[("TRUST_FAKE_TARGO_HANG_IGNORE_TERM", "1")],
                false,
                &[libc::SIGTERM],
                &[libc::SIGINT],
            );
            let (status, stderr) =
                assert_only_the_other_signal_counts(run, libc::SIGINT, (libc::SIGTERM, "SIGTERM"));
            assert_eq!(status.code(), Some(3), "an interrupted run exits 3:\n{stderr}");
        }

        #[test]
        fn sigterm() {
            let run = HangingCheck::start_with_dispositions(
                "targo-trust-t5a-ignored-term",
                &[("TRUST_FAKE_TARGO_HANG_IGNORE_TERM", "1")],
                false,
                &[libc::SIGINT],
                &[libc::SIGTERM],
            );
            let (status, stderr) =
                assert_only_the_other_signal_counts(run, libc::SIGTERM, (libc::SIGINT, "SIGINT"));
            assert_eq!(status.code(), Some(3), "an interrupted run exits 3:\n{stderr}");
        }

        /// With SIGHUP ignored targo-trust does not watch its parent either:
        /// a `nohup`ed run is meant to outlive whoever started it. So this run
        /// starts behind a shell that hands it SIGHUP ignored, the shell is
        /// killed first, and only then do the two signals come.
        #[test]
        fn sighup() {
            let mut run = HangingCheck::start_with_dispositions(
                "targo-trust-t5a-ignored-hup",
                &[("TRUST_FAKE_TARGO_HANG_IGNORE_TERM", "1")],
                true,
                &[libc::SIGTERM],
                &[libc::SIGHUP],
            );
            let shell = run.child.id();
            run.signal(shell, libc::SIGKILL);
            run.child.wait().expect("reap the shell");
            let deadline = Instant::now() + HANG;
            while parent_of(run.targo_trust) == Some(shell) {
                assert!(Instant::now() < deadline, "targo-trust was never reparented");
                std::thread::sleep(Duration::from_millis(20));
            }
            std::thread::sleep(PARENT_WATCH_WINDOW);
            assert!(
                !run.stderr().contains("the process that started targo-trust"),
                "SIGHUP was ignored at start, so the end of the parent must not stop the run:\n{}",
                run.stderr()
            );
            // The started process is the shell, killed above; targo-trust's
            // own exit (3) is no longer this test's to read, so its last line
            // stands for it.
            let (_, stderr) =
                assert_only_the_other_signal_counts(run, libc::SIGHUP, (libc::SIGTERM, "SIGTERM"));
            assert!(
                stderr.contains("COULD NOT RUN: interrupted by SIGTERM"),
                "an interrupted run says so:\n{stderr}"
            );
            assert!(
                !stderr.contains("(stop cause: parent-ended)"),
                "SIGHUP was ignored at start, so the end of the parent must not stop the run:\n{stderr}"
            );
        }

        /// `pid`'s parent, while `pid` runs.
        fn parent_of(pid: u32) -> Option<u32> {
            let output = std::process::Command::new("ps")
                .args(["-o", "ppid=", "-p", &pid.to_string()])
                .output()
                .expect("run ps");
            String::from_utf8_lossy(&output.stdout).trim().parse().ok()
        }
    }

    /// The shell that started targo-trust ends by `signal`.
    ///
    /// Asserts that targo-trust watches its parent, which it does only when
    /// SIGHUP was not ignored at its start, and that the shell DIES of
    /// `signal`, which a shell that inherited it ignored would not.
    fn assert_the_end_of_the_parent_stops_the_run(prefix: &str, signal: libc::c_int) {
        let asserts_on: &[libc::c_int] =
            if signal == libc::SIGKILL { &[libc::SIGHUP] } else { &[libc::SIGHUP, signal] };
        let mut run = HangingCheck::start(prefix, &[], true, asserts_on);
        let shell = run.child.id();
        run.signal(shell, signal);
        let status = run.wait();
        let stderr = run.stderr();
        run.assert_compile_stopped();
        assert_eq!(status.signal(), Some(signal), "the shell ended by the signal");
        assert!(
            stderr.contains(&format!(
                "COULD NOT RUN: the process that started targo-trust (pid {shell}) ended"
            )),
            "{stderr}"
        );
        assert!(stderr.contains("(stop cause: parent-ended)"), "{stderr}");
    }

    #[test]
    fn the_end_of_the_parent_by_sigkill_stops_the_run() {
        assert_the_end_of_the_parent_stops_the_run("targo-trust-t5a-parent-kill", libc::SIGKILL);
    }

    #[test]
    fn the_end_of_the_parent_by_sigterm_stops_the_run() {
        assert_the_end_of_the_parent_stops_the_run("targo-trust-t5a-parent-term", libc::SIGTERM);
    }
}
