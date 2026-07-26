//! Production collection of candidate-bound `trustd` protocol evidence.

use std::ffi::OsStr;
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};
use std::time::{Duration, Instant};

use serde_json::{Value, json};
use trust_version::{BoundToolIdentity, TrustVersionIdentity};

use crate::bounded_process;
use crate::controlled_git;
use crate::durable_io::atomic_write_private;
use crate::pipeline::probe::{
    TrustdRuntimeClosure, apply_trustd_runtime_closure, inspect_trustd_runtime_closure,
};

use super::identity::{
    bound_file_sha256, build_version_identity, discover_repo_root, generated_at_unix_seconds,
    is_executable_file, option_value, trustd_version_output_is_bound,
};
use super::product_proof::PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS;
use super::types::CANDIDATE_COMMAND_VERSION;

const COMMAND: &str = "targo trust release collect-trustd-evidence";
const EVIDENCE_SCHEMA: &str = "trust.product-proof.v1";
const EVIDENCE_KIND: &str = "Trust daemon protocol smoke";
const SMOKE_LABEL: &str = "product-proof-live-smoke";
const DEFAULT_OUTPUT_ROOT: &str = "build/product-proof";
const MAX_GIT_OUTPUT_BYTES: usize = 1024 * 1024;
const MAX_GIT_INDEX_OUTPUT_BYTES: usize = 64 * 1024 * 1024;

#[derive(Default)]
struct Options {
    repo_root: Option<PathBuf>,
    candidate_commit: Option<String>,
    out: Option<String>,
    json: bool,
}

struct CandidateDaemon {
    path: PathBuf,
    repo_relative_path: String,
    sha256: String,
    version: String,
    release: String,
    commit_hash: String,
    rust_compat_version: Option<String>,
}

struct Collection {
    evidence: Value,
    evidence_path: String,
    evidence_sha256: String,
    transcript_path: String,
    transcript_sha256: String,
}

pub(super) fn run_collect_trustd_evidence_subcommand(args: &[String]) -> ExitCode {
    if args.first().is_some_and(|arg| matches!(arg.as_str(), "--help" | "-h" | "help")) {
        print!("{}", usage_text());
        return ExitCode::SUCCESS;
    }

    let options = match parse_options(args) {
        Ok(options) => options,
        Err(error) => return argument_error(error),
    };
    let candidate_commit = match options.candidate_commit.as_deref() {
        Some(commit) if canonical_commit(commit) => commit,
        Some(_) => return argument_error("--candidate-commit must be canonical lowercase 40-hex"),
        None => return argument_error("--candidate-commit is required"),
    };
    let root = match discover_repo_root(options.repo_root.as_deref()) {
        Ok(root) => root,
        Err(error) => {
            return collection_error(format!("could not resolve repository root: {error}"));
        }
    };
    // The candidate was validated above, so it cannot introduce path syntax.
    // This ignored build-tree default preserves the exact clean worktree.
    let default_output =
        format!("{DEFAULT_OUTPUT_ROOT}/trustd-protocol-smoke-{candidate_commit}.json");
    let output_text = options.out.as_deref().unwrap_or(&default_output);
    let (output_relative, output_path) = match repo_relative_json_output(&root, output_text) {
        Ok(output) => output,
        Err(error) => return argument_error(error),
    };
    if let Err(error) = require_ignored_untracked_output(&root, &output_relative, "--out") {
        return argument_error(error);
    }

    let collection = match collect(&root, candidate_commit, &output_relative, &output_path) {
        Ok(collection) => collection,
        Err(error) => return collection_error(error),
    };
    if options.json {
        match serde_json::to_string_pretty(&collection.evidence) {
            Ok(rendered) => println!("{rendered}"),
            Err(error) => {
                return collection_error(format!("could not render collected evidence: {error}"));
            }
        }
    } else {
        println!("collected candidate-bound trustd protocol evidence");
        println!("candidate: {candidate_commit}");
        println!("evidence: {} (sha256:{})", collection.evidence_path, collection.evidence_sha256);
        println!(
            "transcript: {} (sha256:{})",
            collection.transcript_path, collection.transcript_sha256
        );
    }
    ExitCode::SUCCESS
}

fn parse_options(args: &[String]) -> Result<Options, String> {
    let mut options = Options::default();
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--json" => options.json = true,
            "--format" => match iter.next().map(String::as_str) {
                Some("json") => options.json = true,
                Some("terminal" | "text") => options.json = false,
                Some(format) => return Err(format!("unsupported format `{format}`")),
                None => return Err("--format requires a value".to_string()),
            },
            "--repo-root" => match iter.next() {
                Some(path) => options.repo_root = Some(PathBuf::from(path)),
                None => return Err("--repo-root requires a path".to_string()),
            },
            "--candidate-commit" => match iter.next() {
                Some(commit) => options.candidate_commit = Some(commit.clone()),
                None => return Err("--candidate-commit requires a 40-hex commit".to_string()),
            },
            "--out" | "--output" => match iter.next() {
                Some(path) => options.out = Some(path.clone()),
                None => return Err("--out requires a repo-relative JSON path".to_string()),
            },
            "--help" | "-h" | "help" => {
                return Err("--help must be the first argument".to_string());
            }
            other => {
                if let Some(format) = option_value(other, "--format") {
                    match format {
                        "json" => options.json = true,
                        "terminal" | "text" => options.json = false,
                        _ => return Err(format!("unsupported format `{format}`")),
                    }
                    continue;
                }
                if let Some(path) = option_value(other, "--repo-root") {
                    options.repo_root = Some(PathBuf::from(path));
                    continue;
                }
                if let Some(commit) = option_value(other, "--candidate-commit") {
                    options.candidate_commit = Some(commit.to_string());
                    continue;
                }
                if let Some(path) =
                    option_value(other, "--out").or_else(|| option_value(other, "--output"))
                {
                    options.out = Some(path.to_string());
                    continue;
                }
                return Err(format!("unknown option `{other}`"));
            }
        }
    }
    Ok(options)
}

fn collect(
    root: &Path,
    candidate_commit: &str,
    output_relative: &str,
    output_path: &Path,
) -> Result<Collection, String> {
    require_exact_clean_candidate(root, candidate_commit)?;
    require_ignored_untracked_output(root, output_relative, "--out")?;

    let version_identity = build_version_identity(Some(root))
        .map_err(|error| format!("could not build candidate toolchain identity: {error}"))?;
    require_version_candidate(&version_identity, candidate_commit)?;
    let candidate = bind_candidate_daemon(root, candidate_commit, &version_identity.tools.daemon)?;
    let runtime_closure = inspect_trustd_runtime_closure(&candidate.path)?;
    runtime_closure.validate_for_candidate(&candidate.path)?;
    verify_cleared_version_probe(&candidate, &runtime_closure)?;
    runtime_closure.validate_for_candidate(&candidate.path)?;

    let smoke = capture_live_smoke(&candidate, &runtime_closure)?;
    runtime_closure.validate_for_candidate(&candidate.path)?;
    require_exact_clean_candidate(root, candidate_commit)?;
    require_candidate_unchanged(&candidate)?;

    let transcript = render_transcript(&smoke)?;
    let transcript_sha256 = trust_types::digest::stable_sha256_hex(transcript.as_bytes());
    let transcript_relative = format!(
        "{DEFAULT_OUTPUT_ROOT}/transcripts/trustd-protocol-smoke-sha256-{transcript_sha256}.txt"
    );
    if output_relative == transcript_relative {
        return Err("--out must be distinct from the content-addressed transcript".to_string());
    }
    require_ignored_untracked_output(root, &transcript_relative, "transcript output")?;
    let transcript_path = root.join(&transcript_relative);
    atomic_write_private(&transcript_path, transcript.as_bytes()).map_err(|error| {
        format!(
            "could not publish content-addressed transcript {} atomically: {error}",
            transcript_path.display()
        )
    })?;
    if bound_file_sha256(&transcript_path).as_deref() != Some(transcript_sha256.as_str()) {
        return Err("content-addressed transcript did not read back with its SHA-256".to_string());
    }

    require_exact_clean_candidate(root, candidate_commit)?;
    require_candidate_unchanged(&candidate)?;
    let clean_metadata = clean_repo_metadata(root)?;
    let git_identity = controlled_git_identity(root)?;
    let generated_at = generated_at_unix_seconds();
    if generated_at < PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS {
        return Err("system clock cannot produce an admissible evidence timestamp".to_string());
    }
    let evidence = build_evidence(
        candidate_commit,
        &candidate,
        &runtime_closure,
        &smoke,
        generated_at,
        clean_metadata,
        git_identity.clone(),
        &transcript_relative,
        &transcript_sha256,
    );
    let rendered = serde_json::to_string_pretty(&evidence)
        .map_err(|error| format!("could not render trustd evidence JSON: {error}"))?;
    let evidence_bytes = format!("{rendered}\n");
    let evidence_sha256 = trust_types::digest::stable_sha256_hex(evidence_bytes.as_bytes());
    atomic_write_private(output_path, evidence_bytes.as_bytes()).map_err(|error| {
        format!("could not publish {} atomically: {error}", output_path.display())
    })?;
    if bound_file_sha256(output_path).as_deref() != Some(evidence_sha256.as_str()) {
        return Err("evidence JSON did not read back with its publication SHA-256".to_string());
    }
    require_exact_clean_candidate(root, candidate_commit)?;
    require_candidate_unchanged(&candidate)?;
    if controlled_git_identity(root)? != git_identity {
        return Err("controlled Git executable changed during evidence publication".to_string());
    }

    Ok(Collection {
        evidence,
        evidence_path: output_relative.to_string(),
        evidence_sha256,
        transcript_path: transcript_relative,
        transcript_sha256,
    })
}

fn bind_candidate_daemon(
    root: &Path,
    candidate_commit: &str,
    identity: &BoundToolIdentity,
) -> Result<CandidateDaemon, String> {
    if identity.name != "trustd"
        || identity.executable != Some(true)
        || identity.resolution.as_deref() != Some("bound-executable")
    {
        return Err("release identity does not bind an exact executable trustd sibling".to_string());
    }
    let path_text = identity
        .path
        .as_deref()
        .ok_or_else(|| "release identity trustd has no canonical path".to_string())?;
    let path = fs::canonicalize(path_text)
        .map_err(|error| format!("could not canonicalize release identity trustd: {error}"))?;
    if !is_executable_file(&path) {
        return Err("release identity trustd is not an exact regular executable".to_string());
    }
    let relative = path.strip_prefix(root).map_err(|_| {
        format!(
            "canonical candidate trustd is outside the candidate repository: {}",
            path.display()
        )
    })?;
    if relative.as_os_str().is_empty()
        || relative.components().any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err("canonical candidate trustd has no normal repo-relative path".to_string());
    }
    let repo_relative_path = relative
        .to_str()
        .ok_or_else(|| "canonical candidate trustd path is not UTF-8".to_string())?
        .to_string();
    let sha256 = identity
        .sha256
        .as_deref()
        .filter(|sha256| trust_types::digest::is_stable_sha256_hex(sha256))
        .ok_or_else(|| "release identity trustd has no canonical SHA-256".to_string())?
        .to_string();
    if bound_file_sha256(&path).as_deref() != Some(sha256.as_str()) {
        return Err("release identity trustd SHA-256 does not match its current bytes".to_string());
    }
    let version = identity
        .version
        .as_deref()
        .ok_or_else(|| "release identity trustd has no version".to_string())?
        .to_string();
    let release = version
        .strip_prefix("trustd ")
        .filter(|release| !release.is_empty() && !release.starts_with("trustd "))
        .ok_or_else(|| "release identity trustd version is not `trustd <release>`".to_string())?
        .to_string();
    let commit_hash = identity
        .commit_hash
        .as_deref()
        .filter(|commit| *commit == candidate_commit)
        .ok_or_else(|| "release identity trustd commit does not match candidate HEAD".to_string())?
        .to_string();
    if identity.rust_compat_version.as_deref() != Some(release.as_str()) {
        return Err("release identity trustd version differs from its Rust-compatibility binding"
            .to_string());
    }

    Ok(CandidateDaemon {
        path,
        repo_relative_path,
        sha256,
        version,
        release,
        commit_hash,
        rust_compat_version: identity.rust_compat_version.clone(),
    })
}

fn verify_cleared_version_probe(
    candidate: &CandidateDaemon,
    runtime_closure: &TrustdRuntimeClosure,
) -> Result<(), String> {
    require_candidate_unchanged(candidate)?;
    let probe_root = tempfile::Builder::new()
        .prefix("trustd-version-probe-")
        .tempdir()
        .map_err(|error| format!("could not create private trustd probe directory: {error}"))?;
    let mut command = Command::new(&candidate.path);
    command.arg("--version").current_dir(probe_root.path());
    apply_trustd_runtime_closure(&mut command, &candidate.path, runtime_closure)?;
    let probe_result = (|| -> Result<(), String> {
        let output = bounded_process::output(
            &mut command,
            "canonical trustd evidence identity probe",
            64 * 1024,
            Duration::from_secs(10),
        )?;
        if !output.status.success() {
            return Err(format!("canonical trustd --version exited {}", output.status));
        }
        if !output.stderr.is_empty() {
            return Err("canonical trustd --version wrote to stderr".to_string());
        }
        let stdout = String::from_utf8(output.stdout)
            .map_err(|_| "canonical trustd --version output was not UTF-8".to_string())?;
        if !trustd_version_output_is_bound(&stdout, &candidate.release) {
            return Err("canonical trustd --version did not bind identity, protocol, and release"
                .to_string());
        }
        if stdout.lines().next().map(str::trim) != Some(candidate.version.as_str()) {
            return Err(
                "canonical trustd live version differs from the release identity".to_string()
            );
        }
        let commits = stdout
            .lines()
            .filter_map(|line| line.trim().strip_prefix("commit-hash:").map(str::trim))
            .collect::<Vec<_>>();
        if commits != [candidate.commit_hash.as_str()] {
            return Err("canonical trustd live commit differs from candidate HEAD".to_string());
        }
        Ok(())
    })();
    require_candidate_unchanged(candidate)?;
    runtime_closure.validate_for_candidate(&candidate.path)?;
    probe_result
}

#[cfg(unix)]
struct TrustdChild {
    child: std::process::Child,
    pid: u32,
}

#[cfg(unix)]
impl Drop for TrustdChild {
    fn drop(&mut self) {
        let _ = bounded_process::terminate_process_group(self.pid);
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

#[cfg(unix)]
fn capture_live_smoke(
    candidate: &CandidateDaemon,
    runtime_closure: &TrustdRuntimeClosure,
) -> Result<trust_router::coordinator::DaemonSmoke, String> {
    use std::os::unix::fs::{FileTypeExt as _, MetadataExt as _, PermissionsExt as _};

    require_candidate_unchanged(candidate)?;
    let socket_root =
        tempfile::Builder::new().prefix("trust-product-proof-collector-").tempdir().map_err(
            |error| format!("could not create private trustd socket directory: {error}"),
        )?;
    fs::set_permissions(socket_root.path(), fs::Permissions::from_mode(0o700)).map_err(
        |error| format!("could not make trustd socket directory owner-private: {error}"),
    )?;
    let socket_root_metadata = fs::symlink_metadata(socket_root.path())
        .map_err(|error| format!("could not inspect private socket directory: {error}"))?;
    if socket_root_metadata.file_type().is_symlink() || !socket_root_metadata.file_type().is_dir() {
        return Err("private trustd socket root is not an exact directory".to_string());
    }
    // SAFETY: geteuid has no preconditions and only observes process identity.
    let effective_uid = unsafe { libc::geteuid() };
    if socket_root_metadata.uid() != effective_uid {
        return Err(format!(
            "trustd socket directory is owned by uid {}, expected effective uid {effective_uid}",
            socket_root_metadata.uid()
        ));
    }
    let socket_root_mode = socket_root_metadata.permissions().mode() & 0o777;
    if socket_root_mode != 0o700 {
        return Err(format!(
            "trustd socket directory permissions are {socket_root_mode:o}, expected 700"
        ));
    }
    let socket = socket_root.path().join("trustd.sock");
    let mut command = Command::new(&candidate.path);
    command
        .arg("--socket")
        .arg(&socket)
        .current_dir(socket_root.path())
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    apply_trustd_runtime_closure(&mut command, &candidate.path, runtime_closure)?;
    bounded_process::configure_process_group(&mut command);
    let child = match command.spawn() {
        Ok(child) => child,
        Err(error) => {
            require_candidate_unchanged(candidate)?;
            runtime_closure.validate_for_candidate(&candidate.path)?;
            return Err(format!("could not launch canonical candidate trustd: {error}"));
        }
    };
    let pid = child.id();
    let mut child = TrustdChild { child, pid };

    let smoke_result = (|| -> Result<trust_router::coordinator::DaemonSmoke, String> {
        let ready_deadline = Instant::now()
            .checked_add(Duration::from_secs(5))
            .ok_or_else(|| "trustd readiness deadline overflowed".to_string())?;
        loop {
            if bounded_process::exited_without_reaping(&mut child.child)
                .map_err(|error| format!("could not poll candidate trustd: {error}"))?
            {
                return Err("canonical candidate trustd exited before readiness".to_string());
            }
            if trust_router::coordinator::daemon_matches_executable(&socket, &candidate.path) {
                break;
            }
            if Instant::now() >= ready_deadline {
                return Err("canonical candidate trustd was not identity/status ready within 5s"
                    .to_string());
            }
            std::thread::sleep(Duration::from_millis(20));
        }
        let socket_metadata = fs::symlink_metadata(&socket)
            .map_err(|error| format!("could not inspect candidate trustd socket: {error}"))?;
        if !socket_metadata.file_type().is_socket() {
            return Err("candidate trustd endpoint is not a Unix-domain socket".to_string());
        }
        if bounded_process::exited_without_reaping(&mut child.child)
            .map_err(|error| format!("could not poll candidate trustd: {error}"))?
        {
            return Err(
                "canonical candidate trustd exited before the protocol exchange".to_string()
            );
        }

        let smoke =
            trust_router::coordinator::exercise_daemon_at(&socket, &candidate.path, SMOKE_LABEL)?;
        if bounded_process::exited_without_reaping(&mut child.child)
            .map_err(|error| format!("could not poll candidate trustd: {error}"))?
        {
            return Err(
                "canonical candidate trustd exited before the final observation".to_string()
            );
        }
        if smoke.identity.version != trust_router::coordinator::IDENTITY_VERSION
            || smoke.identity.protocol != trust_router::coordinator::STATUS_VERSION
            || smoke.identity.release != candidate.release
            || smoke.identity.commit != candidate.commit_hash
            || smoke.identity.executable_sha256 != candidate.sha256
            || smoke.reservation_bytes != 1
            || smoke.reservation_label != SMOKE_LABEL
            || smoke.reservation_pid == 0
            || smoke.reservation_token == 0
        {
            return Err(
                "live trustd transition did not bind the exact candidate identity and reservation"
                    .to_string(),
            );
        }
        Ok(smoke)
    })();
    require_candidate_unchanged(candidate)?;
    runtime_closure.validate_for_candidate(&candidate.path)?;
    smoke_result
}

#[cfg(not(unix))]
fn capture_live_smoke(
    _candidate: &CandidateDaemon,
    _runtime_closure: &TrustdRuntimeClosure,
) -> Result<(), String> {
    Err("trustd product-proof evidence collection requires a Unix-domain socket host".to_string())
}

#[cfg(unix)]
fn render_transcript(smoke: &trust_router::coordinator::DaemonSmoke) -> Result<String, String> {
    // Serialize through Value, exactly as the evidence document does. This
    // keeps object-key ordering byte-for-byte identical to the validator's
    // transcript reconstruction rather than depending on struct field order.
    let identity_value = serde_json::to_value(&smoke.identity)
        .map_err(|error| format!("could not materialize trustd identity: {error}"))?;
    let before_value = serde_json::to_value(&smoke.status_before)
        .map_err(|error| format!("could not materialize initial trustd status: {error}"))?;
    let reserved_value = serde_json::to_value(&smoke.status_reserved)
        .map_err(|error| format!("could not materialize reserved trustd status: {error}"))?;
    let released_value = serde_json::to_value(&smoke.status_released)
        .map_err(|error| format!("could not materialize released trustd status: {error}"))?;
    let identity = serde_json::to_string(&identity_value)
        .map_err(|error| format!("could not serialize trustd identity: {error}"))?;
    let before = serde_json::to_string(&before_value)
        .map_err(|error| format!("could not serialize initial trustd status: {error}"))?;
    let reserved = serde_json::to_string(&reserved_value)
        .map_err(|error| format!("could not serialize reserved trustd status: {error}"))?;
    let released = serde_json::to_string(&released_value)
        .map_err(|error| format!("could not serialize released trustd status: {error}"))?;
    Ok(format!(
        "> PING\n< PONG\n> IDENTITY\n< {identity}\n> STATUS\n< {before}\n> RESERVE 1 {pid} {label}\n< GRANTED {token}\n> STATUS\n< {reserved}\n> RELEASE {token}\n< OK\n> STATUS\n< {released}\n",
        pid = smoke.reservation_pid,
        label = SMOKE_LABEL,
        token = smoke.reservation_token,
    ))
}

#[cfg(not(unix))]
fn render_transcript(_smoke: &()) -> Result<String, String> {
    Err("trustd product-proof evidence collection requires a Unix-domain socket host".to_string())
}

#[cfg(unix)]
fn build_evidence(
    candidate_commit: &str,
    candidate: &CandidateDaemon,
    runtime_closure: &TrustdRuntimeClosure,
    smoke: &trust_router::coordinator::DaemonSmoke,
    generated_at: u64,
    clean_metadata: Value,
    git_identity: Value,
    transcript_path: &str,
    transcript_sha256: &str,
) -> Value {
    json!({
        "schema_version": EVIDENCE_SCHEMA,
        "evidence_kind": EVIDENCE_KIND,
        "candidate_commit": candidate_commit,
        "generated_at": generated_at,
        "status": "passed",
        "runner": {
            "implementation": "rust",
            "tool": "targo-trust",
            "entrypoint": COMMAND,
            "command_version": CANDIDATE_COMMAND_VERSION,
            "python_used": false,
            "repo_dirty": false,
            "repo_dirty_metadata": clean_metadata,
            "git": git_identity,
        },
        "operational_checks": {
            "ping": true,
            "identity": true,
            "status": true,
            "reserve": true,
            "release": true,
        },
        "tool_identity": {
            "name": "trustd",
            "path": candidate.repo_relative_path,
            "sha256": candidate.sha256,
            "executable": true,
            "version": candidate.version,
            "commit_hash": candidate.commit_hash,
            "rust_compat_version": candidate.rust_compat_version,
            "resolution": "bound-executable",
        },
        "runtime_closure": runtime_closure,
        "trustd_protocol_smoke": {
            "requests": ["PING", "IDENTITY", "STATUS", "RESERVE", "STATUS", "RELEASE", "STATUS"],
            "ping_response": "PONG",
            "reservation_bytes": smoke.reservation_bytes,
            "reservation_label": smoke.reservation_label,
            "reservation_pid": smoke.reservation_pid,
            "reservation_token": smoke.reservation_token,
            "identity_response": smoke.identity,
            "status_before": smoke.status_before,
            "status_reserved": smoke.status_reserved,
            "status_released": smoke.status_released,
            "transcript_path": transcript_path,
            "transcript_sha256": transcript_sha256,
        },
    })
}

#[cfg(not(unix))]
fn build_evidence(
    _candidate_commit: &str,
    _candidate: &CandidateDaemon,
    _runtime_closure: &TrustdRuntimeClosure,
    _smoke: &(),
    _generated_at: u64,
    _clean_metadata: Value,
    _git_identity: Value,
    _transcript_path: &str,
    _transcript_sha256: &str,
) -> Value {
    Value::Null
}

fn require_version_candidate(
    identity: &TrustVersionIdentity,
    candidate_commit: &str,
) -> Result<(), String> {
    match identity.candidate_commit.as_deref() {
        Some(actual) if actual == candidate_commit => Ok(()),
        Some(actual) => Err(format!(
            "release identity candidate {actual} differs from requested HEAD {candidate_commit}"
        )),
        None => Err("release identity did not bind a candidate commit".to_string()),
    }
}

fn require_candidate_unchanged(candidate: &CandidateDaemon) -> Result<(), String> {
    if bound_file_sha256(&candidate.path).as_deref() == Some(candidate.sha256.as_str()) {
        Ok(())
    } else {
        Err("canonical candidate trustd changed during evidence collection".to_string())
    }
}

fn require_exact_clean_candidate(root: &Path, candidate_commit: &str) -> Result<(), String> {
    let top_level = controlled_git::resolve_repo_root(root)?;
    if top_level != root {
        return Err(format!(
            "--repo-root must be the exact Git top level {}; got {}",
            top_level.display(),
            root.display()
        ));
    }
    let head = controlled_git::canonical_head(
        root,
        "trustd evidence candidate HEAD probe",
        MAX_GIT_OUTPUT_BYTES,
        Duration::from_secs(30),
    )?;
    if head != candidate_commit {
        return Err(format!("candidate HEAD is {head}, expected {candidate_commit}"));
    }
    if !git_status_porcelain_lines(root)?.is_empty() {
        return Err(
            "candidate repository is dirty or its complete Git status is unavailable; commit or remove every tracked, untracked, and submodule change before collecting evidence"
                .to_string(),
        );
    }
    Ok(())
}

fn clean_repo_metadata(root: &Path) -> Result<Value, String> {
    let lines = git_status_porcelain_lines(root)?;
    if !lines.is_empty() {
        return Err("candidate repository became dirty before evidence publication".to_string());
    }
    Ok(json!({
        "available": true,
        "dirty": false,
        "porcelain_v1": lines,
        "untracked_files": "all",
        "ignore_submodules": "none",
    }))
}

fn git_status_porcelain_lines(root: &Path) -> Result<Vec<String>, String> {
    controlled_git::exact_status_porcelain_v1(
        root,
        "trustd evidence repository cleanliness probe",
        MAX_GIT_OUTPUT_BYTES,
        Duration::from_secs(30),
    )
}

fn repo_relative_json_output(root: &Path, path_text: &str) -> Result<(String, PathBuf), String> {
    let path_text = path_text.trim();
    let path = Path::new(path_text);
    if path_text.is_empty()
        || path_text.contains('\0')
        || path.is_absolute()
        || path.extension().and_then(OsStr::to_str) != Some("json")
        || path.components().any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err(
            "--out must be a non-empty repo-relative .json path with only normal components"
                .to_string(),
        );
    }
    Ok((path_text.to_string(), root.join(path)))
}

fn require_ignored_untracked_output(
    root: &Path,
    relative: &str,
    label: &str,
) -> Result<(), String> {
    controlled_git::validate_status_authority(
        root,
        "trustd evidence output-policy probe",
        MAX_GIT_INDEX_OUTPUT_BYTES,
        Duration::from_secs(30),
    )?;
    if git_path_is_tracked(root, Path::new(relative), "Git tracked-output check")? {
        return Err(format!(
            "{label} `{relative}` is tracked and would mutate the exact candidate"
        ));
    }

    require_tracked_ignore_rule(root, relative).map_err(|detail| {
        format!(
            "{label} `{relative}` is not ignored by a tracked .gitignore and would dirty the exact candidate; use the default `{DEFAULT_OUTPUT_ROOT}` location or another committed ignore rule: {detail}"
        )
    })
}

fn require_tracked_ignore_rule(root: &Path, relative: &str) -> Result<(), String> {
    let mut command = controlled_git::command(root)?;
    command.args(["check-ignore", "--no-index", "--verbose", "--"]).arg(relative);
    let output = bounded_process::output(
        &mut command,
        "Git ignored-output provenance check",
        64 * 1024,
        Duration::from_secs(30),
    )?;
    if !output.stderr.is_empty() {
        return Err("Git check-ignore wrote to stderr".to_string());
    }
    match output.status.code() {
        Some(1) => return Err("Git reports the path as unignored".to_string()),
        Some(0) => {}
        status => return Err(format!("Git check-ignore returned unexpected status {status:?}")),
    }
    let text = String::from_utf8(output.stdout)
        .map_err(|_| "Git check-ignore provenance was not UTF-8".to_string())?;
    let line = text
        .strip_suffix('\n')
        .ok_or_else(|| "Git check-ignore provenance lacked one complete line".to_string())?;
    if line.contains('\n') || line.contains('\r') {
        return Err("Git check-ignore returned multiple or malformed records".to_string());
    }
    let (rule, reported_path) = line
        .split_once('\t')
        .ok_or_else(|| "Git check-ignore did not report rule provenance".to_string())?;
    if reported_path != relative {
        return Err("Git check-ignore reported a different output path".to_string());
    }
    let mut fields = rule.splitn(3, ':');
    let source = fields.next().unwrap_or_default();
    let line_number = fields.next().unwrap_or_default();
    let pattern = fields.next().unwrap_or_default();
    if source.is_empty()
        || line_number.parse::<u64>().ok().is_none_or(|line| line == 0)
        || pattern.is_empty()
    {
        return Err("Git check-ignore returned malformed rule provenance".to_string());
    }
    let source_path = Path::new(source);
    if source_path.is_absolute()
        || source_path.file_name() != Some(OsStr::new(".gitignore"))
        || source_path.components().any(|component| !matches!(component, Component::Normal(_)))
        || !repo_relative_exact_regular_file(root, source_path)
    {
        return Err(format!(
            "ignore rule source `{source}` is not an exact repo-relative .gitignore"
        ));
    }
    if !git_path_is_tracked(root, source_path, "Git ignore-rule index check")? {
        return Err(format!("ignore rule source `{source}` is not tracked"));
    }
    Ok(())
}

fn repo_relative_exact_regular_file(root: &Path, relative: &Path) -> bool {
    let components = relative.components().collect::<Vec<_>>();
    if components.is_empty() {
        return false;
    }
    let mut current = root.to_path_buf();
    for (index, component) in components.iter().enumerate() {
        let Component::Normal(name) = component else {
            return false;
        };
        current.push(name);
        let Ok(metadata) = fs::symlink_metadata(&current) else {
            return false;
        };
        if metadata.file_type().is_symlink() {
            return false;
        }
        let leaf = index + 1 == components.len();
        if (leaf && !metadata.file_type().is_file()) || (!leaf && !metadata.file_type().is_dir()) {
            return false;
        }
    }
    true
}

fn git_text(root: &Path, args: &[&str]) -> Result<String, String> {
    git_text_with_limit(root, args, "trustd evidence Git identity probe", MAX_GIT_OUTPUT_BYTES)
}

fn git_text_with_limit(
    root: &Path,
    args: &[&str],
    context: &str,
    max_output_bytes: usize,
) -> Result<String, String> {
    controlled_git::text(root, args, context, max_output_bytes, Duration::from_secs(30))
}

fn git_path_is_tracked(root: &Path, path: &Path, context: &str) -> Result<bool, String> {
    let mut command = controlled_git::command(root)?;
    command.args(["ls-files", "--stage", "--"]).arg(path);
    let output =
        bounded_process::output(&mut command, context, 64 * 1024, Duration::from_secs(30))?;
    if !output.status.success() {
        return Err(format!("{context} exited {}", output.status));
    }
    if !output.stderr.is_empty() {
        return Err(format!("{context} wrote to stderr"));
    }
    Ok(!output.stdout.is_empty())
}

fn controlled_git_identity(root: &Path) -> Result<Value, String> {
    let path = controlled_git::executable()?;
    let sha256 = bound_file_sha256(&path)
        .ok_or_else(|| format!("could not hash controlled Git {}", path.display()))?;
    let config_path_text = git_text(root, &["rev-parse", "--git-path", "config"])?;
    let config_path_text = config_path_text.trim();
    let config_path = if Path::new(config_path_text).is_absolute() {
        PathBuf::from(config_path_text)
    } else {
        root.join(config_path_text)
    };
    let config_sha256 = bound_file_sha256(&config_path).ok_or_else(|| {
        format!("could not bind residual repository config {}", config_path.display())
    })?;
    let effective_config = controlled_git::output(
        root,
        &["config", "--show-origin", "--null", "--list"],
        "trustd evidence effective Git configuration probe",
        MAX_GIT_OUTPUT_BYTES,
        Duration::from_secs(30),
    )?;
    if !effective_config.status.success() || !effective_config.stderr.is_empty() {
        return Err("could not bind controlled Git effective configuration".to_string());
    }
    let effective_config_sha256 = trust_types::digest::stable_sha256_hex(&effective_config.stdout);
    Ok(json!({
        "path": path,
        "sha256": sha256,
        "environment": "cleared",
        "system_config": false,
        "global_config": false,
        "local_config": "recorded-residual-repository-tcb",
        "local_config_path": config_path,
        "local_config_sha256": config_sha256,
        "effective_config_sha256": effective_config_sha256,
        "local_authority_overrides": [
            "core.bare=false",
            "core.worktree=<exact-repo-root>",
            "core.fsmonitor=false",
            "core.untrackedCache=false",
            "core.trustctime=true",
            "core.checkStat=default",
            "core.ignoreStat=false",
            "core.autocrlf=false",
            "core.eol=lf",
            "core.safecrlf=true",
            "core.ignoreCase=false",
            "core.hooksPath=/dev/null",
            "core.filemode=true",
            "core.symlinks=true",
            "core.excludesFile=/dev/null",
            "core.attributesFile=/dev/null",
            "core.sparseCheckout=false",
            "status.showUntrackedFiles=all",
        ],
        "replace_objects": false,
        "lazy_fetch": false,
        "system_attributes": false,
        "hooks_invoked": false,
        "clean": true,
        "dirty": false,
    }))
}


fn canonical_commit(value: &str) -> bool {
    value.len() == 40
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}


fn argument_error(error: impl AsRef<str>) -> ExitCode {
    eprintln!("{COMMAND}: {}", error.as_ref());
    eprint!("{}", usage_text());
    ExitCode::from(2)
}

fn collection_error(error: impl AsRef<str>) -> ExitCode {
    eprintln!("{COMMAND}: {}", error.as_ref());
    ExitCode::from(1)
}

fn usage_text() -> &'static str {
    "Usage: targo trust release collect-trustd-evidence --candidate-commit <40-hex> [--repo-root <path>] [--out <ignored-repo-relative-json>] [--json]\n\nRuns the canonical candidate trustd sibling through a live PING/IDENTITY/STATUS/RESERVE/STATUS/RELEASE/STATUS transition. The checkout must be the exact clean candidate HEAD. The default evidence and content-addressed transcript are written owner-private beneath ignored build/product-proof/. A custom output must be untracked and ignored by a tracked .gitignore.\n"
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_digests_are_lowercase_and_exact_width() {
        assert!(canonical_commit(&"a".repeat(40)));
        assert!(!canonical_commit(&"A".repeat(40)));
        assert!(!canonical_commit(&"a".repeat(39)));
        assert!(trust_types::digest::is_stable_sha256_hex(&"9".repeat(64)));
        assert!(!trust_types::digest::is_stable_sha256_hex(&"g".repeat(64)));
    }

    #[test]
    fn output_path_cannot_escape_or_target_non_json() {
        let root = Path::new("/candidate");
        assert!(repo_relative_json_output(root, "build/product-proof/evidence.json").is_ok());
        assert!(repo_relative_json_output(root, "../evidence.json").is_err());
        assert!(repo_relative_json_output(root, "/tmp/evidence.json").is_err());
        assert!(repo_relative_json_output(root, "build/product-proof/evidence.txt").is_err());
        assert!(repo_relative_json_output(root, "./build/evidence.json").is_err());
    }

    #[test]
    fn parser_accepts_only_explicit_collector_options() {
        let parsed = parse_options(&[
            "--candidate-commit".to_string(),
            "a".repeat(40),
            "--out=build/product-proof/evidence.json".to_string(),
            "--format=json".to_string(),
        ])
        .expect("parse collector options");
        let expected_commit = "a".repeat(40);
        assert_eq!(parsed.candidate_commit.as_deref(), Some(expected_commit.as_str()));
        assert_eq!(parsed.out.as_deref(), Some("build/product-proof/evidence.json"));
        assert!(parsed.json);
        assert!(parse_options(&["--socket".to_string()]).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn output_policy_accepts_only_ignored_untracked_paths() {
        let repository = tempfile::tempdir().expect("temporary Git repository");
        let mut init = Command::new(controlled_git::executable().expect("controlled Git"));
        init.env_clear()
            .env("LC_ALL", "C")
            .args(["init", "--quiet"])
            .arg(repository.path())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        assert!(init.status().expect("initialize Git repository").success());
        fs::write(repository.path().join(".gitignore"), "/build/\n")
            .expect("write ignored output policy");
        fs::write(repository.path().join("tracked.json"), "{}\n").expect("write tracked fixture");
        assert!(
            require_ignored_untracked_output(
                repository.path(),
                "build/product-proof/evidence.json",
                "test output",
            )
            .unwrap_err()
            .contains("ignore rule source `.gitignore` is not tracked")
        );
        let mut add = controlled_git::command(repository.path()).expect("controlled Git");
        add.args(["add", "--", ".gitignore", "tracked.json"])
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        assert!(add.status().expect("index tracked fixture").success());

        assert!(
            require_ignored_untracked_output(
                repository.path(),
                "build/product-proof/evidence.json",
                "test output",
            )
            .is_ok()
        );
        assert!(
            require_ignored_untracked_output(repository.path(), "tracked.json", "test output",)
                .unwrap_err()
                .contains("tracked")
        );
        assert!(
            require_ignored_untracked_output(
                repository.path(),
                "evidence/output.json",
                "test output",
            )
            .unwrap_err()
            .contains("not ignored")
        );
        fs::write(repository.path().join(".git/info/exclude"), "/private-output/\n")
            .expect("write local exclude fixture");
        assert!(
            require_ignored_untracked_output(
                repository.path(),
                "build/product-proof/evidence.json",
                "test output",
            )
            .unwrap_err()
            .contains("info/exclude contains material rules")
        );
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn transcript_uses_the_same_canonical_json_as_the_evidence_values() {
        use trust_router::coordinator::{
            ActiveReservation, DaemonIdentity, DaemonSmoke, DaemonStatus, IDENTITY_VERSION,
            STATUS_VERSION,
        };

        let before = DaemonStatus {
            version: STATUS_VERSION.to_string(),
            budget_bytes: 10,
            reserved_bytes: 0,
            free_bytes: 10,
            queue_depth: 0,
            granted_total: 0,
            released_total: 0,
            started_at: 1,
            active: Vec::new(),
        };
        let reserved = DaemonStatus {
            version: STATUS_VERSION.to_string(),
            budget_bytes: 10,
            reserved_bytes: 1,
            free_bytes: 9,
            queue_depth: 0,
            granted_total: 1,
            released_total: 0,
            started_at: 1,
            active: vec![ActiveReservation {
                pid: 123,
                bytes: 1,
                label: SMOKE_LABEL.to_string(),
                since_secs: 0,
                token: 7,
            }],
        };
        let released = DaemonStatus {
            version: STATUS_VERSION.to_string(),
            budget_bytes: 10,
            reserved_bytes: 0,
            free_bytes: 10,
            queue_depth: 0,
            granted_total: 1,
            released_total: 1,
            started_at: 1,
            active: Vec::new(),
        };
        let smoke = DaemonSmoke {
            identity: DaemonIdentity {
                version: IDENTITY_VERSION.to_string(),
                protocol: STATUS_VERSION.to_string(),
                release: "1.0.0".to_string(),
                commit: "a".repeat(40),
                executable_sha256: "b".repeat(64),
            },
            status_before: before,
            status_reserved: reserved,
            status_released: released,
            reservation_pid: 123,
            reservation_token: 7,
            reservation_bytes: 1,
            reservation_label: SMOKE_LABEL.to_string(),
        };
        let candidate = CandidateDaemon {
            path: PathBuf::from("/candidate/build/host/stage2/bin/trustd"),
            repo_relative_path: "build/host/stage2/bin/trustd".to_string(),
            sha256: "b".repeat(64),
            version: "trustd 1.0.0".to_string(),
            release: "1.0.0".to_string(),
            commit_hash: "a".repeat(40),
            rust_compat_version: Some("1.0.0".to_string()),
        };
        let runtime_closure = inspect_trustd_runtime_closure(
            &std::env::current_exe().expect("current test executable"),
        )
        .expect("inspect test executable runtime closure");
        let transcript = render_transcript(&smoke).expect("render canonical transcript");
        let evidence = build_evidence(
            &"a".repeat(40),
            &candidate,
            &runtime_closure,
            &smoke,
            PRODUCT_PROOF_TIMESTAMP_MIN_UNIX_SECONDS,
            json!({"available": true, "dirty": false, "porcelain_v1": []}),
            json!({"path": "/usr/bin/git", "clean": true, "dirty": false}),
            "build/product-proof/transcript.txt",
            &trust_types::digest::stable_sha256_hex(transcript.as_bytes()),
        );
        assert_eq!(
            evidence["runtime_closure"],
            serde_json::to_value(&runtime_closure).expect("serialize runtime closure")
        );
        assert_eq!(evidence["runtime_closure"]["loader_environment"], "none");
        assert_eq!(evidence["runtime_closure"]["search_paths"], json!([]));
        let material = &evidence["trustd_protocol_smoke"];
        let expected = format!(
            "> PING\n< PONG\n> IDENTITY\n< {}\n> STATUS\n< {}\n> RESERVE 1 123 {SMOKE_LABEL}\n< GRANTED 7\n> STATUS\n< {}\n> RELEASE 7\n< OK\n> STATUS\n< {}\n",
            serde_json::to_string(&material["identity_response"]).unwrap(),
            serde_json::to_string(&material["status_before"]).unwrap(),
            serde_json::to_string(&material["status_reserved"]).unwrap(),
            serde_json::to_string(&material["status_released"]).unwrap(),
        );
        assert_eq!(transcript, expected);
    }
}
