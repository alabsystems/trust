// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Native execution/evidence fixtures, not compiler or source-proof evidence.

use std::fs;
use std::io::{Read, Write};
use std::os::unix::process::ExitStatusExt as _;
use std::process::ExitStatus;
use std::sync::Mutex;
use std::time::Duration;

use super::*;

const CHILD_ROLE: &str = "__TRUST_QUALIFIER_CAPTURE_CHILD_ROLE";
const CHILD_OUTPUT: &str = "__TRUST_QUALIFIER_CAPTURE_CHILD_OUTPUT";
const STDOUT_PAYLOAD: &[u8] = b"OWNED-STDOUT\0\xff\x80\nfinal-out-tail\xfe";
const STDERR_PAYLOAD: &[u8] = b"OWNED-STDERR\0\xff\nfinal-err-tail\xfd";
static NATIVE_CAPTURE: Mutex<()> = Mutex::new(());

fn actor(role: &str, output: &Path) -> ProcessBuilder {
    let mut process = ProcessBuilder::new(std::env::current_exe().unwrap());
    process
        .args(&[
            "--ignored",
            "--exact",
            "extraction::tests::native_child_actor",
            "--nocapture",
            "--quiet",
        ])
        .env(CHILD_ROLE, role)
        .env(CHILD_OUTPUT, output);
    process
}

fn small_limits() -> StreamingOutputLimits {
    StreamingOutputLimits::new(256, 1024).with_child_exit_cleanup()
}

fn record(output: &Path) -> serde_json::Value {
    serde_json::from_slice(&fs::read(output.join("compiler-execution.json")).unwrap()).unwrap()
}

#[test]
#[ignore = "native fixture entry; executed only by the parent process tests"]
fn native_child_actor() {
    let role = std::env::var(CHILD_ROLE).expect("parent selected a native fixture role");
    let output = std::path::PathBuf::from(std::env::var_os(CHILD_OUTPUT).unwrap());
    let mut stdin = Vec::new();
    std::io::stdin().read_to_end(&mut stdin).unwrap();
    assert!(stdin.is_empty(), "compiler-like children receive null stdin");
    fs::write(output.join("source_qualification.trust-ir.bin"), b"fixture artifact, not actual IR")
        .unwrap();
    match role.as_str() {
        "binary-success" | "binary-nonzero" => {
            std::io::stdout().write_all(STDOUT_PAYLOAD).unwrap();
            std::io::stdout().flush().unwrap();
            std::io::stderr().write_all(STDERR_PAYLOAD).unwrap();
            std::io::stderr().flush().unwrap();
            std::process::exit(if role == "binary-success" { 0 } else { 7 });
        }
        "flood" => {
            std::io::stdout().write_all(&[b'f'; 4096]).unwrap();
            std::io::stdout().flush().unwrap();
            // HANG detector only. A correct owner rejects and settles this
            // child before it emits its deliberately wrong fallback exit.
            std::thread::sleep(Duration::from_secs(60));
            std::process::exit(73);
        }
        _ => panic!("unknown native fixture role"),
    }
}

fn assert_raw_binary(output: &Path) {
    let stdout = fs::read(output.join("compiler.stdout")).unwrap();
    let start = stdout
        .windows(b"OWNED-STDOUT".len())
        .position(|window| window == b"OWNED-STDOUT")
        .expect("native payload after libtest framing");
    assert_eq!(&stdout[start..], STDOUT_PAYLOAD, "exact final unterminated stdout tail");
    assert_eq!(fs::read(output.join("compiler.stderr")).unwrap(), STDERR_PAYLOAD);
}

#[test]
fn native_success_retains_exact_binary_outputs_and_final_tails() {
    let _serial = NATIVE_CAPTURE.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let output = tempfile::tempdir().unwrap();
    execute(&actor("binary-success", output.path()), output.path(), small_limits()).unwrap();
    assert_raw_binary(output.path());
    let metadata = record(output.path());
    assert_eq!(metadata["execution_admitted"], true);
    assert_eq!(metadata["capture_complete"], true);
    assert_eq!(metadata["stdout_end"], "eof");
    assert_eq!(metadata["stderr_end"], "eof");
    assert_eq!(metadata["exit_code"], 0);
}

#[test]
fn native_nonzero_retains_binary_evidence_and_never_admits_an_existing_artifact() {
    let _serial = NATIVE_CAPTURE.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let output = tempfile::tempdir().unwrap();
    let error = execute(&actor("binary-nonzero", output.path()), output.path(), small_limits())
        .unwrap_err();
    assert!(error.to_string().contains("source compiler failed"));
    assert!(output.path().join("source_qualification.trust-ir.bin").is_file());
    assert_raw_binary(output.path());
    let metadata = record(output.path());
    assert_eq!(metadata["execution_admitted"], false);
    assert_eq!(metadata["capture_complete"], true);
    assert_eq!(metadata["exit_code"], 7);
}

#[test]
fn native_flood_refusal_keeps_bounded_raw_prefix_and_cannot_admit_artifact() {
    let _serial = NATIVE_CAPTURE.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let output = tempfile::tempdir().unwrap();
    execute(&actor("flood", output.path()), output.path(), small_limits()).unwrap_err();
    let prefix = fs::read(output.path().join("compiler.stdout")).unwrap();
    assert!(!prefix.is_empty());
    assert!(prefix.len() <= 1024);
    assert!(prefix.contains(&b'f'));
    let metadata = record(output.path());
    assert_eq!(metadata["execution_admitted"], false);
    assert_eq!(metadata["capture_complete"], false);
    assert_eq!(metadata["actual_stream_bytes"], 1024);
    assert!(metadata["failure"].is_string());
    assert!(output.path().join("source_qualification.trust-ir.bin").is_file());
}

#[test]
fn native_spawn_failure_preserves_empty_evidence_and_unavailable_status() {
    let _serial = NATIVE_CAPTURE.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let output = tempfile::tempdir().unwrap();
    let process = ProcessBuilder::new(output.path().join("missing-compiler"));
    execute(&process, output.path(), small_limits()).unwrap_err();
    assert!(fs::read(output.path().join("compiler.stdout")).unwrap().is_empty());
    assert!(fs::read(output.path().join("compiler.stderr")).unwrap().is_empty());
    let metadata = record(output.path());
    assert_eq!(metadata["started"], false);
    assert_eq!(metadata["status_available"], false);
    assert_eq!(metadata["execution_admitted"], false);
    assert_eq!(metadata["capture_complete"], false);
    assert!(metadata["failure"].is_string());
}

fn observed(
    status: ExitStatus,
    stdout_end: CaptureStreamEnd,
    stderr_end: CaptureStreamEnd,
) -> CapturedProcess {
    CapturedProcess {
        stdout: b"retained\0\xfftail".to_vec(),
        stderr: vec![],
        started: true,
        status: Some(status),
        stdout_end,
        stderr_end,
        stdout_truncated: false,
        stderr_truncated: false,
        failure: None,
        read_error: None,
        cleanup_error: None,
        owner_observation: None,
        limits: Some(small_limits()),
    }
}

#[test]
fn zero_status_with_drained_or_incomplete_stream_never_admits_ir() {
    for (stdout, stderr) in [
        (CaptureStreamEnd::LeaderExitDrained, CaptureStreamEnd::Eof),
        (CaptureStreamEnd::Eof, CaptureStreamEnd::LeaderExitDrained),
        (CaptureStreamEnd::Incomplete, CaptureStreamEnd::Eof),
    ] {
        let output = tempfile::tempdir().unwrap();
        fs::write(output.path().join("source_qualification.trust-ir.bin"), b"purported IR")
            .unwrap();
        retain_and_admit(
            observed(ExitStatus::from_raw(0), stdout, stderr),
            output.path(),
            small_limits(),
        )
        .unwrap_err();
        let metadata = record(output.path());
        assert_eq!(metadata["status_success"], true);
        assert_eq!(metadata["capture_complete"], false);
        assert_eq!(metadata["execution_admitted"], false);
        assert_eq!(fs::read(output.path().join("compiler.stdout")).unwrap(), b"retained\0\xfftail");
    }
}

#[test]
fn complete_zero_status_with_cleanup_error_still_refuses_ir() {
    let output = tempfile::tempdir().unwrap();
    let mut capture =
        observed(ExitStatus::from_raw(0), CaptureStreamEnd::Eof, CaptureStreamEnd::Eof);
    capture.cleanup_error = Some("cleanup remains uncertain".to_owned());
    retain_and_admit(capture, output.path(), small_limits()).unwrap_err();
    let metadata = record(output.path());
    assert_eq!(metadata["capture_complete"], true);
    assert_eq!(metadata["execution_admitted"], false);
    assert_eq!(metadata["cleanup_error"], "cleanup remains uncertain");
}

#[test]
fn physical_eof_with_a_truncated_prefix_still_refuses_ir() {
    let output = tempfile::tempdir().unwrap();
    let mut capture =
        observed(ExitStatus::from_raw(0), CaptureStreamEnd::Eof, CaptureStreamEnd::Eof);
    capture.stdout_truncated = true;
    retain_and_admit(capture, output.path(), small_limits()).unwrap_err();
    let metadata = record(output.path());
    assert_eq!(metadata["stdout_truncated"], true);
    assert_eq!(metadata["capture_complete"], false);
    assert_eq!(metadata["execution_admitted"], false);
}

#[test]
fn compiler_arguments_and_policy_preserve_existing_extraction_contract() {
    let output = tempfile::tempdir().unwrap();
    let process = compiler_command(Path::new("/actual/compiler"), output.path());
    assert_eq!(process.get_program(), "/actual/compiler");
    assert_eq!(process.get_cwd(), Some(output.path()));
    let mut expected = EXTRACTION_FLAGS.iter().map(std::ffi::OsString::from).collect::<Vec<_>>();
    expected.extend(["--out-dir".into(), output.path().as_os_str().to_owned(), "source.rs".into()]);
    assert_eq!(process.get_args().cloned().collect::<Vec<_>>(), expected);
    assert!(process.get_stdin().is_none());
    let limits = compiler_limits();
    assert_eq!(limits.line_bytes(), 128 * 1024 * 1024);
    assert_eq!(limits.stream_bytes(), 512 * 1024 * 1024);
    assert_eq!(limits.runtime_timeout(), None);
}

#[test]
#[ignore = "explicit actual compiler/source/new evidence/expected IR inputs required"]
fn actual_custody_source_compile_only() {
    let required = |name| {
        std::path::PathBuf::from(
            std::env::var_os(name).unwrap_or_else(|| panic!("missing required {name}")),
        )
    };
    let compiler = required("TRUST_QUALIFIER_CAPTURE_COMPILER");
    let source = required("TRUST_QUALIFIER_CAPTURE_SOURCE");
    let evidence = required("TRUST_QUALIFIER_CAPTURE_EVIDENCE");
    let expected_ir = required("TRUST_QUALIFIER_CAPTURE_EXPECTED_IR");
    // Read the independently retained expected bytes before creating fresh
    // evidence. This is comparison data, never the new compiler's IR output.
    let expected = fs::read(&expected_ir).unwrap();
    let (origin, bytes) = super::super::capture_source(&source).unwrap();
    fs::create_dir(&evidence)
        .expect("actual extraction requires a new persistent evidence directory");
    let identity = super::super::compiler_identity(&compiler, &evidence).unwrap();
    super::super::reuse::write_new(
        &evidence.join("identity.json"),
        &serde_json::to_vec_pretty(&identity).unwrap(),
    )
    .unwrap();
    super::super::reuse::write_new(
        &evidence.join("request.json"),
        &serde_json::to_vec_pretty(&serde_json::json!({
            "schema": "trust.source-compile-only-request/v1",
            "compiler": compiler,
            "source": origin,
            "source_sha256": super::super::sha256(&bytes),
            "expected_ir": expected_ir,
            "expected_ir_sha256": super::super::sha256(&expected),
            "proofs_generated": 0,
        }))
        .unwrap(),
    )
    .unwrap();
    let module =
        super::super::compile(&compiler, &identity, &bytes, &evidence.join("positive")).unwrap();
    assert_eq!(module, expected, "owned extraction changed the actual production-source IR");
    let suite: super::super::Suite =
        serde_json::from_str(include_str!("../../cleanup_permission.json")).unwrap();
    let function_id = super::super::function(&module, &suite).unwrap();
    let execution = record(&evidence.join("positive"));
    assert_eq!(execution["execution_admitted"], true);
    assert_eq!(execution["capture_complete"], true);
    super::super::reuse::write_new(
        &evidence.join("result.json"),
        &serde_json::to_vec_pretty(&serde_json::json!({
            "schema": "trust.source-compile-only/v1",
            "source_sha256": super::super::sha256(&bytes),
            "module_sha256": super::super::sha256(&module),
            "function_id": function_id,
            "exact_expected_ir": true,
            "proofs_generated": 0,
            "project_authority": false,
            "binary_authority": false,
        }))
        .unwrap(),
    )
    .unwrap();
}
