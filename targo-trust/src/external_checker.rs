//! Authenticated, bounded execution boundary for external certificate checkers.
//!
//! The proof-cert runner records a useful typed transcript, but an exit status
//! alone cannot establish that the selected checker saw the exact certificate
//! and solver-proof artifacts. Targo therefore runs the selected checker
//! through a private copy of this executable. The supervisor snapshots and
//! validates all three concrete inputs, derives a content-bound challenge,
//! and accepts only an exact challenge acknowledgement from the selected
//! checker. Subprocess output, lifetime, and descendants are bounded by the
//! shared process helper.

use std::collections::BTreeMap;
use std::io::{self, Write as _};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::time::Duration;

use trust_proof_cert::{
    CheckedBinaryCertificateArtifact, CheckedBinaryCertificateExternalCheckerRunner,
};

use crate::bounded_process;
use crate::durable_io::atomic_write_private;
use crate::input_limits::{
    EXTERNAL_CHECKER_TIMEOUT_MS, MAX_BINARY_ARTIFACT_BYTES, MAX_SAVED_PROOF_REPORT_BYTES,
    read_bounded_file,
};

pub(crate) const INTERNAL_CHECKER_SUPERVISOR_SUBCOMMAND: &str =
    "__targo_checked_certificate_checker";
const CHECKER_ACK_PREFIX: &str = "TRUST_CHECKED_CERTIFICATE_ACCEPTED:";
const CHECKER_CHALLENGE_FLAG: &str = "--targo-evidence-challenge";
const CHECKER_MAX_STREAM_BYTES: usize = 16 * 1024 * 1024;
const OUTER_CHECKER_TIMEOUT_MS: u64 = EXTERNAL_CHECKER_TIMEOUT_MS + 60_000;

pub(crate) struct ExecutableSnapshot {
    _root: tempfile::TempDir,
    path: PathBuf,
    sha256: String,
}

pub(crate) struct PreparedExternalChecker {
    _checker: ExecutableSnapshot,
    _supervisor: Option<ExecutableSnapshot>,
    pub(crate) runner: CheckedBinaryCertificateExternalCheckerRunner,
    pub(crate) checker_sha256: String,
}

pub(crate) fn prepare_external_checker(
    path: &Path,
    checked_at_unix_ms: u64,
) -> Result<PreparedExternalChecker, String> {
    let checker = snapshot_executable(path, "targo-trust-checker")
        .map_err(|error| format!("could not snapshot checker {}: {error}", path.display()))?;
    #[cfg(test)]
    {
        // Unit-test executables are libtest harnesses, not the Targo CLI and
        // cannot dispatch the private supervisor subcommand. Core supervisor
        // validation is tested directly below; binary integration tests cover
        // the real self-supervised route.
        let checker_sha256 = checker.sha256.clone();
        let runner = CheckedBinaryCertificateExternalCheckerRunner::from_command_path(
            &checker.path,
            std::iter::empty::<String>(),
            checked_at_unix_ms,
        )
        .map_err(|error| format!("could not initialize checker: {error}"))?
        .with_timeout_ms(OUTER_CHECKER_TIMEOUT_MS);
        return Ok(PreparedExternalChecker {
            _checker: checker,
            _supervisor: None,
            runner,
            checker_sha256,
        });
    }

    #[cfg(not(test))]
    {
        let current_exe = std::env::current_exe()
            .map_err(|error| format!("could not locate checker supervisor executable: {error}"))?;
        let supervisor = snapshot_executable(&current_exe, "targo-trust-checker-supervisor")
            .map_err(|error| format!("could not snapshot checker supervisor: {error}"))?;
        let checker_sha256 = checker.sha256.clone();
        let runner = CheckedBinaryCertificateExternalCheckerRunner::from_command_path(
            &supervisor.path,
            [
                INTERNAL_CHECKER_SUPERVISOR_SUBCOMMAND.to_string(),
                checker.path.display().to_string(),
                checker_sha256.clone(),
            ],
            checked_at_unix_ms,
        )
        .map_err(|error| format!("could not initialize checker supervisor: {error}"))?
        .with_checker_config_sha256(checker_sha256.clone())
        .with_timeout_ms(OUTER_CHECKER_TIMEOUT_MS);
        Ok(PreparedExternalChecker {
            _checker: checker,
            _supervisor: Some(supervisor),
            runner,
            checker_sha256,
        })
    }
}

pub(crate) fn run_checker_supervisor(args: &[String]) -> ExitCode {
    match run_checker_supervisor_inner(args) {
        Ok(code) => code,
        Err(error) => {
            eprintln!("targo trust checked-certificate checker supervisor: {error}");
            ExitCode::from(2)
        }
    }
}

fn run_checker_supervisor_inner(args: &[String]) -> Result<ExitCode, String> {
    run_checker_supervisor_inner_with_timeout(
        args,
        Duration::from_millis(EXTERNAL_CHECKER_TIMEOUT_MS),
    )
}

fn run_checker_supervisor_inner_with_timeout(
    args: &[String],
    checker_timeout: Duration,
) -> Result<ExitCode, String> {
    let checker_path = args
        .first()
        .map(PathBuf::from)
        .ok_or_else(|| "missing private checker path".to_string())?;
    let expected_checker_sha256 =
        args.get(1).ok_or_else(|| "missing checker digest".to_string())?;
    validate_sha256("checker digest", expected_checker_sha256)?;
    let bound_args = parse_bound_checker_args(&args[2..])?;

    let checker_bytes = read_bounded_file(&checker_path, MAX_BINARY_ARTIFACT_BYTES)
        .map_err(|error| format!("private checker is not readable: {error}"))?;
    if trust_types::digest::stable_sha256_hex(&checker_bytes) != *expected_checker_sha256 {
        return Err("private checker bytes do not match the selected checker digest".to_string());
    }

    let certificate_bytes = read_bounded_file(
        Path::new(bound_args.required("--checked-certificate")?),
        MAX_SAVED_PROOF_REPORT_BYTES,
    )
    .map_err(|error| format!("checked certificate input is not a stable bounded file: {error}"))?;
    let metadata_bytes = read_bounded_file(
        Path::new(bound_args.required("--solver-proof-export-metadata")?),
        MAX_SAVED_PROOF_REPORT_BYTES,
    )
    .map_err(|error| format!("solver proof metadata is not a stable bounded file: {error}"))?;
    let proof_bytes = read_bounded_file(
        Path::new(bound_args.required("--solver-proof-payload")?),
        MAX_SAVED_PROOF_REPORT_BYTES,
    )
    .map_err(|error| format!("solver proof payload is not a stable bounded file: {error}"))?;

    let certificate_text = std::str::from_utf8(&certificate_bytes)
        .map_err(|error| format!("checked certificate is not UTF-8 JSON: {error}"))?;
    let certificate = CheckedBinaryCertificateArtifact::from_json(certificate_text)
        .map_err(|error| format!("checked certificate input is invalid: {error}"))?;
    certificate
        .validate_integrity()
        .map_err(|error| format!("checked certificate integrity validation failed: {error}"))?;

    for (label, actual, expected) in [
        ("vc", certificate.vc_sha256.as_str(), bound_args.required("--vc-sha256")?),
        ("origin", certificate.origin_sha256.as_str(), bound_args.required("--origin-sha256")?),
        (
            "assumption",
            certificate.assumption_digest.as_str(),
            bound_args.required("--assumption-digest")?,
        ),
        (
            "certificate",
            certificate.certificate_sha256.as_str(),
            bound_args.required("--certificate-sha256")?,
        ),
        (
            "proof export",
            certificate.proof_export_sha256.as_str(),
            bound_args.required("--proof-export-sha256")?,
        ),
        (
            "proof payload",
            certificate.proof_sha256.as_str(),
            bound_args.required("--proof-sha256")?,
        ),
    ] {
        validate_sha256(&format!("{label} digest"), expected)?;
        if actual != expected {
            return Err(format!(
                "checked certificate {label} digest does not match the checker invocation"
            ));
        }
    }
    let metadata_sha256 = trust_types::digest::stable_sha256_hex(&metadata_bytes);
    if metadata_sha256 != certificate.proof_export_sha256 {
        return Err("solver proof metadata bytes do not match proof_export_sha256".to_string());
    }
    let proof_sha256 = trust_types::digest::stable_sha256_hex(&proof_bytes);
    if proof_sha256 != certificate.proof_sha256 {
        return Err("solver proof payload bytes do not match proof_sha256".to_string());
    }

    // The checker receives private immutable copies of exactly the bytes that
    // were validated above, closing the validate-then-reopen race on a
    // caller-writable export directory.
    let artifacts = tempfile::Builder::new()
        .prefix("targo-trust-checker-inputs-")
        .tempdir()
        .map_err(|error| format!("could not create private checker input directory: {error}"))?;
    let certificate_path = artifacts.path().join("checked-certificate.json");
    let metadata_path = artifacts.path().join("solver-proof-export-metadata.json");
    let proof_path = artifacts.path().join("solver-proof-payload.bin");
    atomic_write_private(&certificate_path, &certificate_bytes)
        .map_err(|error| format!("could not snapshot checked certificate: {error}"))?;
    atomic_write_private(&metadata_path, &metadata_bytes)
        .map_err(|error| format!("could not snapshot solver proof metadata: {error}"))?;
    atomic_write_private(&proof_path, &proof_bytes)
        .map_err(|error| format!("could not snapshot solver proof payload: {error}"))?;

    let challenge = checker_challenge(
        expected_checker_sha256,
        &certificate_bytes,
        &metadata_bytes,
        &proof_bytes,
        &bound_args,
    );
    let checker_args =
        bound_args.checker_args(&certificate_path, &metadata_path, &proof_path, &challenge);
    let mut command = Command::new(&checker_path);
    command.args(checker_args).env_clear();
    let output = bounded_process::output(
        &mut command,
        "checked-certificate external checker",
        CHECKER_MAX_STREAM_BYTES,
        checker_timeout,
    )?;
    if !output.status.success() {
        return Err(format!("selected checker exited with {}", output.status));
    }
    let stdout = std::str::from_utf8(&output.stdout)
        .map_err(|error| format!("selected checker stdout is not UTF-8: {error}"))?;
    let expected_ack = format!("{CHECKER_ACK_PREFIX}{challenge}");
    let acknowledgements = stdout.lines().filter(|line| line.trim() == expected_ack).count();
    if acknowledgements != 1 {
        return Err(format!(
            "selected checker must emit exactly one `{CHECKER_ACK_PREFIX}<bound-challenge>` acknowledgement; observed {acknowledgements}"
        ));
    }

    io::stdout()
        .write_all(&output.stdout)
        .map_err(|error| format!("could not forward checker stdout: {error}"))?;
    io::stderr()
        .write_all(&output.stderr)
        .map_err(|error| format!("could not forward checker stderr: {error}"))?;
    Ok(ExitCode::SUCCESS)
}

struct BoundCheckerArgs {
    values: BTreeMap<&'static str, String>,
}

impl BoundCheckerArgs {
    fn required(&self, key: &'static str) -> Result<&str, String> {
        self.values.get(key).map(String::as_str).ok_or_else(|| format!("missing {key}"))
    }

    fn checker_args(
        &self,
        certificate: &Path,
        metadata: &Path,
        proof: &Path,
        challenge: &str,
    ) -> Vec<String> {
        let mut args = Vec::new();
        for key in BOUND_CHECKER_FLAGS {
            let value = match key {
                "--checked-certificate" => certificate.display().to_string(),
                "--solver-proof-export-metadata" => metadata.display().to_string(),
                "--solver-proof-payload" => proof.display().to_string(),
                _ => self.values[key].clone(),
            };
            args.extend([key.to_string(), value]);
        }
        args.extend([CHECKER_CHALLENGE_FLAG.to_string(), challenge.to_string()]);
        args
    }
}

const BOUND_CHECKER_FLAGS: [&str; 9] = [
    "--checked-certificate",
    "--solver-proof-export-metadata",
    "--solver-proof-payload",
    "--vc-sha256",
    "--origin-sha256",
    "--assumption-digest",
    "--certificate-sha256",
    "--proof-export-sha256",
    "--proof-sha256",
];

fn parse_bound_checker_args(args: &[String]) -> Result<BoundCheckerArgs, String> {
    if args.len() % 2 != 0 {
        return Err("checker artifact arguments must be flag/value pairs".to_string());
    }
    let mut values = BTreeMap::new();
    for pair in args.chunks_exact(2) {
        let key = BOUND_CHECKER_FLAGS
            .iter()
            .copied()
            .find(|key| *key == pair[0])
            .ok_or_else(|| format!("unexpected checker supervisor argument `{}`", pair[0]))?;
        if pair[1].is_empty() {
            return Err(format!("{key} requires a non-empty value"));
        }
        if values.insert(key, pair[1].clone()).is_some() {
            return Err(format!("duplicate checker supervisor argument `{key}`"));
        }
    }
    for key in BOUND_CHECKER_FLAGS {
        if !values.contains_key(key) {
            return Err(format!("missing checker supervisor argument `{key}`"));
        }
    }
    Ok(BoundCheckerArgs { values })
}

fn checker_challenge(
    checker_sha256: &str,
    certificate: &[u8],
    metadata: &[u8],
    proof: &[u8],
    args: &BoundCheckerArgs,
) -> String {
    let mut material = Vec::new();
    material.extend_from_slice(b"targo.checked-certificate.external-check.v1\0");
    let certificate_sha256 = trust_types::digest::stable_sha256_hex(certificate);
    let metadata_sha256 = trust_types::digest::stable_sha256_hex(metadata);
    let proof_sha256 = trust_types::digest::stable_sha256_hex(proof);
    for value in [
        checker_sha256,
        certificate_sha256.as_str(),
        metadata_sha256.as_str(),
        proof_sha256.as_str(),
        args.values["--vc-sha256"].as_str(),
        args.values["--origin-sha256"].as_str(),
        args.values["--assumption-digest"].as_str(),
        args.values["--certificate-sha256"].as_str(),
        args.values["--proof-export-sha256"].as_str(),
        args.values["--proof-sha256"].as_str(),
    ] {
        material.extend_from_slice(value.as_bytes());
        material.push(0);
    }
    trust_types::digest::stable_sha256_hex(&material)
}

fn validate_sha256(label: &str, value: &str) -> Result<(), String> {
    if value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        Ok(())
    } else {
        Err(format!("{label} is not canonical lowercase SHA-256 hex"))
    }
}

fn snapshot_executable(path: &Path, prefix: &str) -> io::Result<ExecutableSnapshot> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::{MetadataExt as _, PermissionsExt as _};

        let metadata = std::fs::symlink_metadata(path)?;
        if metadata.file_type().is_symlink() || !metadata.file_type().is_file() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "executable is not a regular file",
            ));
        }
        if metadata.mode() & 0o111 == 0 {
            return Err(io::Error::new(io::ErrorKind::PermissionDenied, "file is not executable"));
        }
        let bytes = read_bounded_file(path, MAX_BINARY_ARTIFACT_BYTES)?;
        if bytes.is_empty() {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "executable is empty"));
        }
        let root = tempfile::Builder::new().prefix(prefix).tempdir()?;
        let snapshot_path = root.path().join("executable");
        atomic_write_private(&snapshot_path, &bytes)?;
        std::fs::set_permissions(&snapshot_path, std::fs::Permissions::from_mode(0o700))?;
        Ok(ExecutableSnapshot { _root: root, path: snapshot_path, sha256: trust_types::digest::stable_sha256_hex(&bytes) })
    }

    #[cfg(not(unix))]
    {
        let _ = (path, prefix);
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "authenticated external checker execution is not implemented on this platform",
        ))
    }
}

#[cfg(all(test, unix))]
mod tests {
    use std::os::unix::fs::{PermissionsExt as _, symlink};

    use trust_proof_cert::{
        BinaryCertificateCheckRequest, SolverProofExport, StructuralBinaryCertificateChecker,
        check_binary_certificate, persist_solver_proof_export_artifacts,
    };
    use trust_types::{
        BinaryArtifactDigest, BinaryArtifactDigestIdentity, BinaryOrigin,
        BinarySelectedImageIdentity, Formula, SerializableVc, SolverDispatchRecord,
        SolverDispatchStatus, SolverQuerySemantics, SourceSpan, VcKind, VerificationCondition,
    };

    use super::*;

    fn supervisor_fixture(root: &Path, checker_source: &[u8]) -> Vec<String> {
        let checker_path = root.join("checker.sh");
        std::fs::write(&checker_path, checker_source).expect("write checker");
        std::fs::set_permissions(&checker_path, std::fs::Permissions::from_mode(0o700))
            .expect("make checker executable");

        let digest = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "main".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        let serializable_vc = SerializableVc::from_vc(&vc);
        let canonical_vc = crate::verify_binary_evidence::canonical_vc_bytes(&serializable_vc)
            .expect("serialize VC");
        let dispatch = SolverDispatchRecord {
            id: "external-checker-fixture:vc0".to_string(),
            function: Some("main".to_string()),
            origin: Some(BinaryOrigin {
                binary_path: Some("fixture.bin".to_string()),
                function_entry: Some(0x401000),
                instruction_address: 0x401010,
                instruction_size: Some(1),
                encoding: Some(0x90),
                instruction_bytes: vec![0x90],
                source: Some(SourceSpan::binary_address(0x401010)),
            }),
            vc_kind: Some(vc.kind),
            vc: Some(serializable_vc),
            solver: "fixture-solver".to_string(),
            backend: Some("fixture-backend".to_string()),
            status: SolverDispatchStatus::Unsat,
            query_semantics: SolverQuerySemantics::SatIsCounterexample,
            binary_artifact_digest_identity: Some(BinaryArtifactDigestIdentity {
                root_artifact_digest: Some(BinaryArtifactDigest::sha256(digest)),
                selected_image: Some(BinarySelectedImageIdentity {
                    file_offset: 0,
                    file_size: 64,
                    sha256: digest.to_string(),
                }),
            }),
            ..Default::default()
        };
        let export = SolverProofExport::new(
            &dispatch,
            &canonical_vc,
            "lrat",
            b"bounded external checker proof".to_vec(),
            Some("fixture-1".to_string()),
            1_777_070_400_000,
        );
        let structural_checker = StructuralBinaryCertificateChecker::new(
            "fixture-structural-checker",
            "1",
            vec!["lrat".to_string()],
            1_777_070_401_000,
        );
        let checked = check_binary_certificate(
            &structural_checker,
            BinaryCertificateCheckRequest::from_export(&dispatch, &canonical_vc, &export),
        );
        assert!(checked.accepted, "{:?}", checked.error);
        let certificate = checked.certificate.expect("checked certificate");
        let certificate_path = root.join("checked-certificate.json");
        std::fs::write(
            &certificate_path,
            certificate.to_json().expect("serialize checked certificate"),
        )
        .expect("write checked certificate");
        let proof_artifacts = persist_solver_proof_export_artifacts(root, &export)
            .expect("persist solver proof export artifacts");

        vec![
            checker_path.display().to_string(),
            trust_types::digest::stable_sha256_hex(checker_source),
            "--checked-certificate".to_string(),
            certificate_path.display().to_string(),
            "--solver-proof-export-metadata".to_string(),
            proof_artifacts.metadata_path.display().to_string(),
            "--solver-proof-payload".to_string(),
            proof_artifacts.proof_path.display().to_string(),
            "--vc-sha256".to_string(),
            certificate.vc_sha256,
            "--origin-sha256".to_string(),
            certificate.origin_sha256,
            "--assumption-digest".to_string(),
            certificate.assumption_digest,
            "--certificate-sha256".to_string(),
            certificate.certificate_sha256,
            "--proof-export-sha256".to_string(),
            certificate.proof_export_sha256,
            "--proof-sha256".to_string(),
            certificate.proof_sha256,
        ]
    }

    #[test]
    fn executable_snapshot_binds_bytes_and_rejects_symlinks() {
        let root = tempfile::tempdir().expect("checker fixture");
        let checker = root.path().join("checker.sh");
        let original = b"#!/bin/sh\nexit 0\n";
        std::fs::write(&checker, original).expect("write checker");
        std::fs::set_permissions(&checker, std::fs::Permissions::from_mode(0o700))
            .expect("make checker executable");

        let snapshot = snapshot_executable(&checker, "checker-test").expect("snapshot checker");
        std::fs::write(&checker, b"#!/bin/sh\nexit 1\n").expect("replace checker");
        assert_eq!(
            read_bounded_file(&snapshot.path, MAX_BINARY_ARTIFACT_BYTES).expect("read snapshot"),
            original
        );
        assert_eq!(snapshot.sha256, trust_types::digest::stable_sha256_hex(original));

        let linked = root.path().join("linked-checker.sh");
        symlink(&checker, &linked).expect("link checker");
        let error = snapshot_executable(&linked, "checker-test")
            .err()
            .expect("symlinked checker must fail closed");
        assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
    }

    #[test]
    fn supervisor_accepts_only_a_content_bound_acknowledgement() {
        let root = tempfile::tempdir().expect("supervisor fixture");
        let args = supervisor_fixture(
            root.path(),
            b"#!/bin/sh\nchallenge=\nwhile [ \"$#\" -gt 0 ]; do\n  if [ \"$1\" = \"--targo-evidence-challenge\" ]; then shift; challenge=$1; fi\n  shift\ndone\nprintf 'TRUST_CHECKED_CERTIFICATE_ACCEPTED:%s\\n' \"$challenge\"\n",
        );
        let status = run_checker_supervisor_inner(&args).expect("bound checker should pass");
        assert_eq!(status, ExitCode::SUCCESS);
    }

    #[test]
    fn supervisor_rejects_bare_exit_zero_checker() {
        let root = tempfile::tempdir().expect("supervisor fixture");
        let args = supervisor_fixture(root.path(), b"#!/bin/sh\nexit 0\n");
        let error = run_checker_supervisor_inner(&args)
            .expect_err("a no-argument exit-zero checker must not establish evidence");
        assert!(error.contains("exactly one"), "{error}");
    }

    #[test]
    fn supervisor_terminates_a_checker_at_its_deadline() {
        let root = tempfile::tempdir().expect("supervisor fixture");
        let args = supervisor_fixture(root.path(), b"#!/bin/sh\nwhile :; do :; done\n");
        let error = run_checker_supervisor_inner_with_timeout(&args, Duration::from_millis(50))
            .expect_err("checker deadline must fail closed");
        assert!(error.contains("timeout"), "{error}");
    }

    #[test]
    fn supervisor_rejects_oversized_concrete_artifact() {
        let root = tempfile::tempdir().expect("supervisor fixture");
        let args = supervisor_fixture(root.path(), b"#!/bin/sh\nexit 0\n");
        let certificate_index = args
            .iter()
            .position(|arg| arg == "--checked-certificate")
            .expect("certificate argument")
            + 1;
        let certificate = std::fs::OpenOptions::new()
            .write(true)
            .open(&args[certificate_index])
            .expect("open certificate");
        certificate
            .set_len(MAX_SAVED_PROOF_REPORT_BYTES as u64 + 1)
            .expect("make sparse oversized certificate");

        let error = run_checker_supervisor_inner(&args)
            .expect_err("oversized concrete artifact must fail before checker execution");
        assert!(error.contains("exceeds"), "{error}");
    }
}
