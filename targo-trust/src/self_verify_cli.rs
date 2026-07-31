use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsString;
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufRead, BufReader, Read, Write};
use std::path::{Component, Path, PathBuf};
#[cfg(unix)]
use std::process::Stdio;
use std::process::{Command, ExitCode, ExitStatus};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use std::{env, thread};

use serde_json::{Map, Value, json};
use sha2::{Digest, Sha256};
use trust_types::is_trust_vc_digest_bound_proof_certificate_artifact;

use crate::config::DEFAULT_CODEGEN_BACKEND;
use crate::input_limits::{MAX_CARGO_JSON_LINE_BYTES, read_bounded_utf8_line};
use crate::pipeline::backend::{
    canonical_rustc_option_name, find_forbidden_in_process_codegen_arg,
};
use crate::pipeline::probe::native_runtime_environment;
use crate::pipeline::transport::{
    CargoTargetIdentity, cargo_proof_inventory_report, cargo_unit_semantics_sha256,
    parse_cargo_json_stdout_with_authenticated_messages, validate_cargo_unit_semantics,
};
use crate::report::{
    is_replay_or_check_artifact, is_solver_transcript_artifact,
    transport_obligation_has_publishable_native_proof,
};

const SCHEMA: &str = "trust.self-verify-harness.report.v1";
const SOLVER_SUITE_SCHEMA: &str = "trust.self-verify-harness.solver-suite.v1";
const COVERAGE_BLOCKER_SCHEMA: &str = "trust.self-verify-harness.coverage-blocker.v1";
const ALL_UNKNOWN_ROUTING_SCHEMA: &str = "trust.self-verify-harness.all-unknown-routing.v1";
const VERIFICATION_ROW_SCHEMA: &str = "trust.self-verify-harness.compiler-self-verification-row.v1";
const VERIFICATION_ROW_SUMMARY_SCHEMA: &str =
    "trust.self-verify-harness.compiler-self-verification-row-summary.v1";
const COMPILER_SELF_VERIFICATION_SCHEMA: &str =
    "trust.self-verify-harness.compiler-self-verification.v1";
const CARGO_TARGET_IDENTITY_SCHEMA: &str = "trust.self-verify-harness.cargo-target-identity.v2";
const REPORT_NAME: &str = "self-verify-harness.report.json";
const DEFAULT_TARGET: &str = "compiler/rustc_middle";
const DEFAULT_EVIDENCE_MANIFEST: &str = "compiler/rustc_middle/Cargo.toml";
const DEFAULT_STAGE_LABEL: &str = "compiler-crate-verification-on";
const DEFAULT_STAGE_DESCRIPTION: &str = "Direct verification-on Cargo JSON evidence build for one compiler crate; any bootstrap rebuild/provenance phase is separate and its stdout is not proof input.";
const DEFAULT_TIMEOUT_SEC: f64 = 900.0;
const UNIT_SEPARATOR: char = '\x1f';
const MAX_RUN_ID_BYTES: usize = 128;
const MAX_STAGE2_EXECUTABLE_BYTES: usize = 1024 * 1024 * 1024;
const MAX_IDENTITY_PROBE_STREAM_BYTES: usize = 64 * 1024;
const IDENTITY_PROBE_TIMEOUT: Duration = Duration::from_secs(10);
#[cfg(unix)]
const TRUSTD_READY_TIMEOUT: Duration = Duration::from_secs(5);
#[cfg(unix)]
const TRUSTD_READY_POLL_INTERVAL: Duration = Duration::from_millis(20);
#[cfg(unix)]
const TRUSTD_SMOKE_RESERVATION_BYTES: u64 = 1;
#[cfg(unix)]
const TRUSTD_SMOKE_RESERVATION_LABEL: &str = "product-proof-live-smoke";
const MAX_STAGE_LOG_STREAM_BYTES: usize = 128 * 1024 * 1024;

const ENV_KEYS_TO_RECORD: &[&str] = &[
    "TRUST_TARGO_VERIFY",
    "RUSTFLAGS",
    "CARGO_ENCODED_RUSTFLAGS",
    "RUSTDOCFLAGS",
    "CARGO_ENCODED_RUSTDOCFLAGS",
    "RUSTFLAGS_BOOTSTRAP",
    "RUSTFLAGS_NOT_BOOTSTRAP",
    "RUSTDOCFLAGS_BOOTSTRAP",
    "RUSTDOCFLAGS_NOT_BOOTSTRAP",
    "MAGIC_EXTRA_RUSTFLAGS",
    "RUSTC",
    "CARGO_BUILD_RUSTC",
    "RUSTDOC",
    "CARGO_BUILD_RUSTDOC",
    "CARGO_CACHE_RUSTC_INFO",
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "CARGO_BUILD_RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
    "CARGO_INCREMENTAL",
    "CARGO_NET_OFFLINE",
    "CARGO_TERM_COLOR",
    "TRUST_TARGO_BIN",
    "TRUST_TRUSTC_BIN",
    "TRUST_SELF_VERIFY_TARGO_SHA256",
    "TRUST_SELF_VERIFY_TRUSTC_SHA256",
    "TRUST_SELF_VERIFY_TRUSTDOC_SHA256",
    "TRUST_SELF_VERIFY_TRUSTD_SHA256",
    "TRUST_TARGO_TRUST_BIN",
    "TRUST_TRUSTDOC_BIN",
    "TRUST_TRUSTD_BIN",
    "TRUSTC",
    "TRUSTDOC",
];

const PROVED_OUTCOME: &str = "proved";
const INCOMPLETE_OUTCOMES: &[&str] = &[
    "unknown",
    "timed_out",
    "runtime_checked",
    "skipped",
    "unsupported",
    "missing",
    "canceled",
    "no_verification",
    "unverified",
];

const FAILED_OUTCOMES: &[&str] = &["failed"];
const USAGE: &str = "\
Usage: targo trust verify self [options]

Options:
  --repo-root PATH
  --run-id ID
  --report-dir PATH
  --target TEXT
      Logical release/composition label; never interpreted as a filesystem path.
  --evidence-manifest PATH
      Cargo manifest selecting the authenticated evidence package.
  --timeout SEC (> 0; default: 900)
  --stage-label TEXT
  --stage-description TEXT
  --jobs N
  --level 0|1|2
  --full-verifier
  --offline
  --dry-run
      Plans the stage without running it; full-verifier mode still executes
      bounded Targo/trustc/trustdoc version probes plus an exact-sibling trustd
      --version and live PING/IDENTITY/STATUS/RESERVE/RELEASE protocol smoke on Unix.
  --perf-budget-mode report|enforce
  --max-verification-wall-time-sec SEC
  --max-reported-solver-time-ms MS
  --max-obligation-rows N
  --max-cache-miss-obligations N
  --compare-report PATH
  --stage-command <command...>
      Diagnostic custom stage command (not permitted with --full-verifier).

Examples:
  targo trust verify self --full-verifier
  targo trust verify self --report-dir reports/self-verify --target compiler/rustc_middle --evidence-manifest compiler/rustc_middle/Cargo.toml --dry-run
";

#[derive(Debug, Clone)]
struct Options {
    repo_root: PathBuf,
    run_id: String,
    report_dir: Option<PathBuf>,
    /// Logical release/composition label. It is never interpreted as a path.
    target: String,
    /// Cargo manifest whose package is the authenticated evidence subject.
    evidence_manifest: PathBuf,
    timeout_sec: f64,
    stage_label: String,
    stage_description: String,
    jobs: Option<String>,
    level: u8,
    full_verifier: bool,
    offline: bool,
    dry_run: bool,
    perf_budget_mode: PerfBudgetMode,
    max_verification_wall_time_sec: Option<f64>,
    max_reported_solver_time_ms: Option<u64>,
    max_obligation_rows: Option<u64>,
    max_cache_miss_obligations: Option<u64>,
    compare_report: Option<PathBuf>,
    stage_command: Option<Vec<String>>,
    raw_argv: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PerfBudgetMode {
    Report,
    Enforce,
}

impl PerfBudgetMode {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "report" => Ok(Self::Report),
            "enforce" => Ok(Self::Enforce),
            other => Err(format!("unsupported --perf-budget-mode `{other}`")),
        }
    }

    fn as_str(self) -> &'static str {
        match self {
            Self::Report => "report",
            Self::Enforce => "enforce",
        }
    }
}

#[derive(Debug)]
struct StagePlan {
    label: String,
    description: String,
    target: String,
    evidence_manifest: PathBuf,
    argv: Vec<String>,
    timeout_sec: f64,
    env: BTreeMap<String, String>,
    env_policy: Value,
    verification_session: String,
    stage2_toolchain: Option<Stage2ToolchainIdentity>,
    // Keeps the compiler's path-backed proof authority alive through the
    // subprocess, transport parsing, report validation, and report write.
    _proof_artifact_root: SelfVerifyProofArtifactRoot,
}

#[derive(Debug)]
struct SelfVerifyProofArtifactRoot {
    _guard: tempfile::TempDir,
    canonical_path: PathBuf,
}

impl SelfVerifyProofArtifactRoot {
    fn create() -> Result<Self, String> {
        let guard = tempfile::Builder::new()
            .prefix("trust-self-verify-proof-root-")
            .tempdir()
            .map_err(|error| format!("could not create self-verification proof root: {error}"))?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;

            fs::set_permissions(guard.path(), fs::Permissions::from_mode(0o700)).map_err(
                |error| format!("could not make self-verification proof root private: {error}"),
            )?;
        }
        let canonical_path = guard.path().canonicalize().map_err(|error| {
            format!("could not canonicalize self-verification proof root: {error}")
        })?;
        let metadata = fs::symlink_metadata(&canonical_path)
            .map_err(|error| format!("could not inspect self-verification proof root: {error}"))?;
        if metadata.file_type().is_symlink() || !metadata.is_dir() {
            return Err("self-verification proof root is not a non-symlink directory".to_string());
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;

            if metadata.permissions().mode() & 0o777 != 0o700 {
                return Err(
                    "self-verification proof root is not owner-private (mode 0700)".to_string()
                );
            }
        }
        let path = canonical_path.to_str().ok_or_else(|| {
            "self-verification proof root is not valid UTF-8 for rustflags".to_string()
        })?;
        if path.chars().any(char::is_whitespace) || path.contains(UNIT_SEPARATOR) {
            return Err(
                "self-verification proof root cannot contain whitespace or Cargo's encoded-rustflags delimiter"
                    .to_string(),
            );
        }
        Ok(Self { _guard: guard, canonical_path })
    }

    fn path(&self) -> &Path {
        &self.canonical_path
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExecutableIdentity {
    canonical_path: PathBuf,
    file_identity: FileObjectIdentity,
    sha256: String,
    size_bytes: u64,
}

#[derive(Debug, Clone)]
struct Stage2ToolchainIdentity {
    targo: ExecutableIdentity,
    trustc: ExecutableIdentity,
    trustdoc: ExecutableIdentity,
    trustd: ExecutableIdentity,
    targo_version: TargoVersionIdentity,
    trustc_version: CompilerVersionIdentity,
    trustdoc_version: CompilerVersionIdentity,
    trustd_version: TrustdVersionIdentity,
    trustd_protocol_smoke: Option<TrustdProtocolSmoke>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TargoVersionIdentity {
    binary: String,
    host: String,
    release: String,
    commit: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CompilerVersionIdentity {
    binary: String,
    host: String,
    release: String,
    commit: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TrustdVersionIdentity {
    binary: String,
    release: String,
    commit: String,
    protocol: String,
}

#[derive(Debug, Clone)]
struct TrustdProtocolSmoke {
    ping_response: String,
    reservation_bytes: u64,
    reservation_label: String,
    reservation_pid: u32,
    reservation_token: u64,
    identity_response: trust_router::coordinator::DaemonIdentity,
    status_before: trust_router::coordinator::DaemonStatus,
    status_reserved: trust_router::coordinator::DaemonStatus,
    status_released: trust_router::coordinator::DaemonStatus,
    transcript: String,
    transcript_sha256: String,
}

impl TrustdProtocolSmoke {
    fn same_bound_identity(&self, other: &Self) -> bool {
        self.ping_response == other.ping_response
            && self.reservation_bytes == other.reservation_bytes
            && self.reservation_label == other.reservation_label
            && self.identity_response == other.identity_response
            && self.status_before.version == other.status_before.version
            && self.status_reserved.version == other.status_reserved.version
            && self.status_released.version == other.status_released.version
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Stage2EndpointSnapshot {
    targo: ExecutableIdentity,
    trustc: ExecutableIdentity,
    trustdoc: ExecutableIdentity,
    trustd: ExecutableIdentity,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct FileObjectIdentity {
    size_bytes: u64,
    #[cfg(unix)]
    device: u64,
    #[cfg(unix)]
    inode: u64,
    #[cfg(windows)]
    volume_serial_number: u64,
    #[cfg(windows)]
    file_id: [u8; 16],
    #[cfg(windows)]
    change_time: i64,
    #[cfg(windows)]
    links: u32,
    #[cfg(all(not(unix), not(windows)))]
    modified_nanos: u128,
}

#[derive(Debug, Default)]
struct TransportSummary {
    stage2_toolchain_identity_verified: bool,
    stage2_execution_identity_bound: bool,
    source_provenance_bound: bool,
    authenticated_cargo_transport: bool,
    completed_targets: Vec<String>,
    coverage_targets: Vec<String>,
    completed_target_identities: BTreeMap<String, Value>,
    coverage_target_identities: BTreeMap<String, Value>,
    /// Canonical observational projections of each Cargo invocation's exact
    /// declared/completed/covered proof-unit frontier. A vector is used because
    /// the top-level report aggregates independently executed stages.
    cargo_proof_inventories: Vec<Value>,
    coverage_eligible: u64,
    coverage_processed: u64,
    coverage_complete: bool,
    messages: usize,
    function_results: usize,
    functions: Vec<String>,
    crate_summaries: Vec<Value>,
    obligation_rows: u64,
    reported_obligations: u64,
    outcomes: BTreeMap<String, u64>,
    solvers: BTreeMap<String, SolverTotals>,
    kinds: BTreeMap<String, SolverTotals>,
    total_solver_time_ms: u64,
    cache_hit_obligations: u64,
    cache_miss_obligations: u64,
    cache_miss_available: bool,
    cache_hit_functions: u64,
    cache_miss_functions: u64,
    cache_function_status_available: bool,
    obligation_evidence: Vec<Value>,
    coverage_blockers: Vec<Value>,
    verification_rows: Vec<Value>,
    parse_errors: Vec<String>,
    inconsistencies: Vec<String>,
}

#[derive(Debug, Default)]
struct SolverTotals {
    obligations: u64,
    time_ms: u64,
    outcomes: BTreeMap<String, u64>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OutcomeClass {
    Proved,
    Failed,
    Incomplete,
    Unrecognized,
}

impl OutcomeClass {
    fn as_str(self) -> &'static str {
        match self {
            Self::Proved => "proved",
            Self::Failed => "failed",
            Self::Incomplete => "incomplete",
            Self::Unrecognized => "unrecognized",
        }
    }
}

pub(crate) fn run(args: &[String]) -> ExitCode {
    match run_inner(args) {
        Ok(code) => ExitCode::from(code),
        Err(error) => {
            eprintln!("self-verify-harness: {error}");
            ExitCode::from(2)
        }
    }
}

fn run_inner(args: &[String]) -> Result<u8, String> {
    if args.first().is_some_and(|arg| is_help_arg(arg)) {
        print!("{USAGE}");
        return Ok(0);
    }

    let mut options = Options::parse(args)?;
    options.repo_root =
        options.repo_root.canonicalize().unwrap_or_else(|_| options.repo_root.clone());
    let report_dir = resolve_report_dir(&options)?;
    if let Some(path) = options.compare_report.as_mut() {
        if !path.is_absolute() {
            *path = options.repo_root.join(&path);
        }
    }

    let plan = build_stage_plan(&options)?;
    let report_dir = create_private_report_directory(&report_dir)?;
    let stages = if options.dry_run {
        vec![planned_stage(&plan)]
    } else {
        vec![run_stage(&plan, &options.repo_root, &report_dir)]
    };
    let status = report_status_from_stages(&stages);
    let mut report = build_report(&options, &report_dir, &plan, stages, &status);
    let effective_exit = exit_code(&report);
    report["exit"] = json!({
        "exit_code": effective_exit,
    });

    validate_report_payload(&report)?;
    let report_path = report_dir.join(REPORT_NAME);
    write_report(&report_path, &report)?;
    println!("self-verify-harness report: {}", report_path.display());
    println!(
        "self-verify-harness status: {} proof={}",
        report.get("status").and_then(Value::as_str).unwrap_or("unknown"),
        report
            .get("proof")
            .and_then(|proof| proof.get("status"))
            .and_then(Value::as_str)
            .unwrap_or("unknown")
    );
    Ok(effective_exit)
}

impl Options {
    fn parse(args: &[String]) -> Result<Self, String> {
        let default_repo_root = env::var_os("TRUST_REPO_ROOT")
            .map(PathBuf::from)
            .unwrap_or_else(|| env::current_dir().unwrap_or_else(|_| PathBuf::from(".")));
        let mut options = Self {
            repo_root: default_repo_root,
            // Trust: removed env TRUST_SELF_VERIFY_RUN_ID; sole surface is --run-id (overrides options.run_id post-init).
            run_id: run_id()?,
            report_dir: None,
            // Trust: removed env TRUST_SELF_VERIFY_TARGET; sole surface is --target.
            target: DEFAULT_TARGET.to_string(),
            evidence_manifest: PathBuf::from(DEFAULT_EVIDENCE_MANIFEST),
            // Trust: removed env TRUST_SELF_VERIFY_TIMEOUT_SEC; sole surface is --timeout.
            timeout_sec: DEFAULT_TIMEOUT_SEC,
            stage_label: DEFAULT_STAGE_LABEL.to_string(),
            stage_description: DEFAULT_STAGE_DESCRIPTION.to_string(),
            jobs: env::var("TRUST_JOBS").ok().filter(|value| !value.is_empty()),
            level: 1,
            full_verifier: false,
            offline: env::var("CARGO_NET_OFFLINE")
                .is_ok_and(|value| value == "true" || value == "1"),
            dry_run: false,
            // Trust: removed env TRUST_SELF_VERIFY_PERF_BUDGET_MODE; sole surface is --perf-budget-mode report|enforce.
            perf_budget_mode: PerfBudgetMode::Report,
            max_verification_wall_time_sec: None,
            max_reported_solver_time_ms: None,
            max_obligation_rows: None,
            max_cache_miss_obligations: None,
            compare_report: None,
            stage_command: None,
            raw_argv: args.to_vec(),
        };

        let mut index = 0;
        while index < args.len() {
            let arg = &args[index];
            if arg == "--stage-command" {
                let command = args[index + 1..].to_vec();
                if command.is_empty() {
                    return Err("--stage-command requires at least one command token".to_string());
                }
                options.stage_command = Some(strip_command_separator(command));
                break;
            }
            if let Some(value) = arg.strip_prefix("--stage-command=") {
                let mut command = vec![value.to_string()];
                command.extend_from_slice(&args[index + 1..]);
                options.stage_command = Some(strip_command_separator(command));
                break;
            }

            match arg.as_str() {
                "--repo-root" => {
                    options.repo_root = PathBuf::from(required_value(args, &mut index, arg)?)
                }
                "--run-id" => options.run_id = required_value(args, &mut index, arg)?,
                "--report-dir" => {
                    options.report_dir = Some(PathBuf::from(required_value(args, &mut index, arg)?))
                }
                "--target" => options.target = required_value(args, &mut index, arg)?,
                "--evidence-manifest" => {
                    options.evidence_manifest =
                        PathBuf::from(required_value(args, &mut index, arg)?)
                }
                "--timeout" => {
                    options.timeout_sec =
                        parse_timeout_sec(&required_value(args, &mut index, arg)?, arg)?
                }
                "--stage-label" => options.stage_label = required_value(args, &mut index, arg)?,
                "--stage-description" => {
                    options.stage_description = required_value(args, &mut index, arg)?
                }
                "--jobs" => options.jobs = Some(required_value(args, &mut index, arg)?),
                "--level" => {
                    let level = parse_u64(&required_value(args, &mut index, arg)?, arg)?;
                    if level > 2 {
                        return Err("--level must be 0, 1, or 2".to_string());
                    }
                    options.level = level as u8;
                }
                "--full-verifier" => options.full_verifier = true,
                "--offline" => options.offline = true,
                "--dry-run" => options.dry_run = true,
                "--allow-incomplete" => {
                    return Err(
                        "--allow-incomplete was removed because self-verification evidence is fail-closed; incomplete proof cannot be converted into a successful exit"
                            .to_string(),
                    );
                }
                "--perf-budget-mode" => {
                    options.perf_budget_mode =
                        PerfBudgetMode::parse(&required_value(args, &mut index, arg)?)?
                }
                "--max-verification-wall-time-sec" => {
                    options.max_verification_wall_time_sec =
                        Some(parse_f64(&required_value(args, &mut index, arg)?, arg)?)
                }
                "--max-reported-solver-time-ms" => {
                    options.max_reported_solver_time_ms =
                        Some(parse_u64(&required_value(args, &mut index, arg)?, arg)?)
                }
                "--max-obligation-rows" => {
                    options.max_obligation_rows =
                        Some(parse_u64(&required_value(args, &mut index, arg)?, arg)?)
                }
                "--max-cache-miss-obligations" => {
                    options.max_cache_miss_obligations =
                        Some(parse_u64(&required_value(args, &mut index, arg)?, arg)?)
                }
                "--compare-report" => {
                    options.compare_report =
                        Some(PathBuf::from(required_value(args, &mut index, arg)?))
                }
                "--help" | "-h" => {
                    print!("{USAGE}");
                    std::process::exit(0);
                }
                _ => {
                    if let Some((name, value)) = arg.split_once('=') {
                        parse_equals_option(&mut options, name, value)?;
                    } else {
                        return Err(format!("unknown argument `{arg}`"));
                    }
                }
            }
            index += 1;
        }

        Ok(options)
    }
}

fn parse_equals_option(options: &mut Options, name: &str, value: &str) -> Result<(), String> {
    match name {
        "--repo-root" => options.repo_root = PathBuf::from(value),
        "--run-id" => options.run_id = value.to_string(),
        "--report-dir" => options.report_dir = Some(PathBuf::from(value)),
        "--target" => options.target = value.to_string(),
        "--evidence-manifest" => options.evidence_manifest = PathBuf::from(value),
        "--timeout" => options.timeout_sec = parse_timeout_sec(value, name)?,
        "--stage-label" => options.stage_label = value.to_string(),
        "--stage-description" => options.stage_description = value.to_string(),
        "--jobs" => options.jobs = Some(value.to_string()),
        "--level" => {
            let level = parse_u64(value, name)?;
            if level > 2 {
                return Err("--level must be 0, 1, or 2".to_string());
            }
            options.level = level as u8;
        }
        "--perf-budget-mode" => options.perf_budget_mode = PerfBudgetMode::parse(value)?,
        "--max-verification-wall-time-sec" => {
            options.max_verification_wall_time_sec = Some(parse_f64(value, name)?)
        }
        "--max-reported-solver-time-ms" => {
            options.max_reported_solver_time_ms = Some(parse_u64(value, name)?)
        }
        "--max-obligation-rows" => options.max_obligation_rows = Some(parse_u64(value, name)?),
        "--max-cache-miss-obligations" => {
            options.max_cache_miss_obligations = Some(parse_u64(value, name)?)
        }
        "--compare-report" => options.compare_report = Some(PathBuf::from(value)),
        other => return Err(format!("unknown argument `{other}`")),
    }
    Ok(())
}

fn required_value(args: &[String], index: &mut usize, flag: &str) -> Result<String, String> {
    let Some(value) = args.get(*index + 1) else {
        return Err(format!("{flag} requires a value"));
    };
    if value.starts_with('-') {
        return Err(format!("{flag} requires a value, got option-like token `{value}`"));
    }
    *index += 1;
    Ok(value.clone())
}

fn parse_f64(value: &str, flag: &str) -> Result<f64, String> {
    let parsed = value.parse::<f64>().map_err(|_| format!("{flag} requires a numeric value"))?;
    if !parsed.is_finite() || parsed < 0.0 {
        return Err(format!("{flag} requires a finite non-negative value"));
    }
    Ok(parsed)
}

fn parse_timeout_sec(value: &str, flag: &str) -> Result<f64, String> {
    let parsed = parse_f64(value, flag)?;
    validate_timeout_sec(parsed, flag)?;
    Ok(parsed)
}

fn validate_timeout_sec(timeout_sec: f64, flag: &str) -> Result<(), String> {
    if !timeout_sec.is_finite() || timeout_sec <= 0.0 {
        return Err(format!("{flag} requires a finite value greater than zero"));
    }
    let duration = Duration::try_from_secs_f64(timeout_sec)
        .map_err(|_| format!("{flag} requires a representable finite value greater than zero"))?;
    if duration.is_zero() {
        return Err(format!("{flag} requires a finite value greater than zero"));
    }
    Ok(())
}

fn parse_u64(value: &str, flag: &str) -> Result<u64, String> {
    value.parse::<u64>().map_err(|_| format!("{flag} requires a non-negative integer"))
}

fn strip_command_separator(mut command: Vec<String>) -> Vec<String> {
    if command.first().is_some_and(|value| value == "--") {
        command.remove(0);
    }
    command
}

fn build_stage_plan(options: &Options) -> Result<StagePlan, String> {
    validate_timeout_sec(options.timeout_sec, "--timeout")?;
    let label = options.stage_label.trim().to_string();
    if label.is_empty() {
        return Err("--stage-label must not be empty".to_string());
    }
    let description = options.stage_description.trim().to_string();
    if description.is_empty() {
        return Err("--stage-description must not be empty".to_string());
    }
    if options.evidence_manifest.as_os_str().is_empty() {
        return Err("--evidence-manifest must not be empty".to_string());
    }
    let argv = if options.full_verifier {
        if options.stage_command.is_some() {
            return Err(
                "--full-verifier does not permit --stage-command; full-verifier mode exclusively executes the fixed repository stage2 Targo build command"
                    .to_string(),
            );
        }
        default_native_stage_argv(
            &options.repo_root,
            &options.evidence_manifest,
            options.jobs.as_deref(),
        )?
    } else {
        match &options.stage_command {
            Some(command) if command.is_empty() => {
                return Err("--stage-command requires at least one command token".to_string());
            }
            Some(command) => command.clone(),
            None => default_bootstrap_stage_argv(&options.target, options.jobs.as_deref()),
        }
    };
    // Resolve and bound the evidence authority before starting any stage
    // command. Otherwise a default command could execute an out-of-repository
    // manifest and only discover that it was ineligible while parsing output.
    expected_self_verify_package(&options.repo_root, &options.evidence_manifest)?;
    let stage2_toolchain = if options.full_verifier {
        Some(validate_stage2_toolchain(&options.repo_root)?)
    } else {
        None
    };
    let proof_artifact_root = SelfVerifyProofArtifactRoot::create()?;
    let (mut env, mut env_policy) = verification_env(
        options.level,
        options.full_verifier,
        options.offline,
        proof_artifact_root.path(),
    )?;
    let verification_session = verification_session_from_policy(&env_policy)?;
    if options.full_verifier {
        let identity = stage2_toolchain.as_ref().expect("full verifier identity validated");
        let stage2_trustc = identity
            .trustc
            .canonical_path
            .to_str()
            .ok_or_else(|| {
                "validated canonical stage2 trustc path is not valid UTF-8 for Cargo's compiler environment"
                    .to_string()
            })?
            .to_string();
        let stage2_trustdoc = identity
            .trustdoc
            .canonical_path
            .to_str()
            .ok_or_else(|| {
                "validated canonical stage2 trustdoc path is not valid UTF-8 for Cargo's rustdoc environment"
                    .to_string()
            })?
            .to_string();
        env.insert(
            "TRUST_TARGO_BIN".to_string(),
            identity.targo.canonical_path.display().to_string(),
        );
        env.insert("TRUST_TRUSTC_BIN".to_string(), stage2_trustc.clone());
        env.insert("TRUST_TRUSTDOC_BIN".to_string(), stage2_trustdoc.clone());
        env.insert(
            "TRUST_TRUSTD_BIN".to_string(),
            identity.trustd.canonical_path.display().to_string(),
        );
        env.insert("TRUST_SELF_VERIFY_TARGO_SHA256".to_string(), identity.targo.sha256.clone());
        env.insert("TRUST_SELF_VERIFY_TRUSTC_SHA256".to_string(), identity.trustc.sha256.clone());
        env.insert(
            "TRUST_SELF_VERIFY_TRUSTDOC_SHA256".to_string(),
            identity.trustdoc.sha256.clone(),
        );
        env.insert("TRUST_SELF_VERIFY_TRUSTD_SHA256".to_string(), identity.trustd.sha256.clone());
        // Cargo has two compiler-selection environment spellings, and its
        // rustc-info cache can otherwise reuse metadata from a different
        // compiler selected before this identity check. Bind all three to the
        // exact canonical stage2 trustc decision made above.
        env.insert("RUSTC".to_string(), stage2_trustc.clone());
        env.insert("CARGO_BUILD_RUSTC".to_string(), stage2_trustc.clone());
        env.insert("RUSTDOC".to_string(), stage2_trustdoc.clone());
        env.insert("CARGO_BUILD_RUSTDOC".to_string(), stage2_trustdoc.clone());
        env.insert("CARGO_CACHE_RUSTC_INFO".to_string(), "0".to_string());
        let native_runtime_environment =
            native_runtime_environment(&identity.trustc.canonical_path)
                .map(|(variable, value)| {
                    value
                        .into_string()
                        .map(|value| (variable.to_string(), value))
                        .map_err(|_| {
                            "validated stage2 native runtime search path is not valid UTF-8 for the self-verification environment"
                                .to_string()
                        })
                })
                .transpose()?;
        if let Some((variable, value)) = &native_runtime_environment {
            env.insert(variable.clone(), value.clone());
        }
        let policy = env_policy
            .as_object_mut()
            .ok_or_else(|| "verification environment policy is not an object".to_string())?;
        policy.insert(
            "pinned_compiler_environment".to_string(),
            json!({
                "authority": "validated canonical stage2 trustc",
                "RUSTC": stage2_trustc,
                "CARGO_BUILD_RUSTC": stage2_trustc,
                "CARGO_CACHE_RUSTC_INFO": "0",
                "cargo_rustc_info_cache_disabled": true,
                "RUSTC_WRAPPER": "",
                "RUSTC_WORKSPACE_WRAPPER": "",
                "CARGO_BUILD_RUSTC_WRAPPER": "",
                "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER": "",
                "compiler_wrappers_disabled": true,
            }),
        );
        policy.insert(
            "pinned_rustdoc_environment".to_string(),
            json!({
                "authority": "validated canonical stage2 trustdoc",
                "RUSTDOC": stage2_trustdoc,
                "CARGO_BUILD_RUSTDOC": stage2_trustdoc,
            }),
        );
        policy.insert(
            "pinned_trustd_environment".to_string(),
            json!({
                "authority": "validated canonical same-stage2-bin trustd",
                "TRUST_TRUSTD_BIN": identity.trustd.canonical_path,
                "TRUST_SELF_VERIFY_TRUSTD_SHA256": identity.trustd.sha256,
                "protocol": identity.trustd_version.protocol,
                "live_protocol_smoke_required": cfg!(unix),
                "live_protocol_smoke_completed": identity.trustd_protocol_smoke.is_some(),
                "ambient_lookup_permitted": false,
            }),
        );
        policy.insert(
            "pinned_native_runtime_environment".to_string(),
            match native_runtime_environment {
                Some((variable, value)) => json!({
                    "authority": "reconstructed exclusively from validated canonical stage2 toolchain directories",
                    "variable": variable,
                    "value": value,
                }),
                None => json!({
                    "authority": "no native runtime search path required by this stage2 layout or platform",
                    "variable": Value::Null,
                    "value": Value::Null,
                }),
            },
        );
    }
    Ok(StagePlan {
        label,
        description,
        target: options.target.clone(),
        evidence_manifest: options.evidence_manifest.clone(),
        argv,
        timeout_sec: options.timeout_sec,
        env,
        env_policy,
        verification_session,
        stage2_toolchain,
        _proof_artifact_root: proof_artifact_root,
    })
}

fn verification_session_from_policy(policy: &Value) -> Result<String, String> {
    let flags = policy
        .get("verification_flags")
        .and_then(Value::as_array)
        .ok_or_else(|| "self-verify environment policy omitted verification_flags".to_string())?;
    let sessions = flags
        .iter()
        .filter_map(Value::as_str)
        .flat_map(split_env_words)
        .filter_map(|word| {
            word.strip_prefix("trust-verify-session=")
                .or_else(|| word.strip_prefix("-Ztrust-verify-session="))
                .map(str::to_string)
        })
        .collect::<BTreeSet<_>>();
    if sessions.len() != 1 {
        return Err(format!(
            "self-verify environment policy requires exactly one verification session, found {}",
            sessions.len()
        ));
    }
    Ok(sessions.into_iter().next().expect("length checked"))
}

fn default_native_stage_argv(
    repo_root: &Path,
    evidence_manifest: &Path,
    jobs: Option<&str>,
) -> Result<Vec<String>, String> {
    let targo = stage2_targo_path(repo_root);
    if !targo.is_file() {
        return Err(format!(
            "default --full-verifier requires a repo-local stage2 Targo endpoint at {}; rebuild the repository stage2 toolchain before retrying",
            targo.display()
        ));
    }
    let mut argv = vec![
        targo.display().to_string(),
        "build".to_string(),
        // Trust transport is carried inside Cargo compiler-message envelopes.
        // `json-render-diagnostics` diverts diagnostics to stderr and strips
        // the Cargo-owned target identity required by proof authentication.
        "--message-format=json".to_string(),
        "--manifest-path".to_string(),
        evidence_manifest.display().to_string(),
    ];
    if let Some(jobs) = jobs.filter(|value| !value.is_empty()) {
        argv.extend(["-j".to_string(), jobs.to_string()]);
    }
    Ok(argv)
}

fn stage2_targo_path(repo_root: &Path) -> PathBuf {
    repo_root.join("build/host/stage2/bin").join(stage2_tool_file_name("targo"))
}

fn default_bootstrap_stage_argv(target: &str, jobs: Option<&str>) -> Vec<String> {
    let mut argv = vec![
        "./x.py".to_string(),
        "check".to_string(),
        "--stage".to_string(),
        "1".to_string(),
        "--set".to_string(),
        "build.locked-deps=true".to_string(),
    ];
    if let Some(jobs) = jobs.filter(|value| !value.is_empty()) {
        argv.extend(["-j".to_string(), jobs.to_string()]);
    }
    argv.push(target.to_string());
    argv
}

fn validate_stage2_toolchain(repo_root: &Path) -> Result<Stage2ToolchainIdentity, String> {
    let before = capture_stage2_endpoints(repo_root)?;
    let (targo_version, trustc_version, trustdoc_version, trustd_version) =
        stage2_version_identities(&before)?;

    // The version probe executes by pathname, so bracket it with fresh,
    // independently opened endpoint snapshots. This detects every persistent
    // replacement and any path/object/length change visible at the boundaries.
    // It does not claim to defeat a same-user replace/execute/restore race;
    // `stage2_execution_identity_bound` remains false and proof completion is
    // gated on that honest limitation below.
    let after = capture_stage2_endpoints(repo_root)?;
    if after != before {
        return Err(
            "stage2 Targo/trustc/trustdoc/trustd path, bytes, file identity, or length changed during version-label validation"
                .to_string(),
        );
    }
    validate_cross_tool_version_identity(
        &targo_version,
        &trustc_version,
        &trustdoc_version,
        &trustd_version,
    )?;
    let trustd_protocol_smoke = live_stage2_trustd_protocol_smoke(&before.trustd, &trustd_version)?;
    let after_smoke = capture_stage2_endpoints(repo_root)?;
    if after_smoke != before {
        return Err(
            "stage2 Targo/trustc/trustdoc/trustd path, bytes, file identity, or length changed during the live trustd protocol smoke"
                .to_string(),
        );
    }
    Ok(Stage2ToolchainIdentity {
        targo: before.targo,
        trustc: before.trustc,
        trustdoc: before.trustdoc,
        trustd: before.trustd,
        targo_version,
        trustc_version,
        trustdoc_version,
        trustd_version,
        trustd_protocol_smoke,
    })
}

fn capture_stage2_endpoints(repo_root: &Path) -> Result<Stage2EndpointSnapshot, String> {
    let canonical_root = repo_root.canonicalize().map_err(|error| {
        format!("could not canonicalize self-verification repository root: {error}")
    })?;
    let stage2_bin = validate_plain_stage2_bin(&canonical_root)?;
    Ok(Stage2EndpointSnapshot {
        targo: validate_stage2_executable(&stage2_bin, "targo")?,
        trustc: validate_stage2_executable(&stage2_bin, "trustc")?,
        trustdoc: validate_stage2_executable(&stage2_bin, "trustdoc")?,
        trustd: validate_stage2_executable(&stage2_bin, "trustd")?,
    })
}

fn stage2_version_identities(
    snapshot: &Stage2EndpointSnapshot,
) -> Result<
    (TargoVersionIdentity, CompilerVersionIdentity, CompilerVersionIdentity, TrustdVersionIdentity),
    String,
> {
    Ok((
        stage2_targo_version_identity(&snapshot.targo.canonical_path)?,
        stage2_compiler_version_identity("trustc", &snapshot.trustc.canonical_path)?,
        stage2_compiler_version_identity("trustdoc", &snapshot.trustdoc.canonical_path)?,
        stage2_trustd_version_identity(&snapshot.trustd.canonical_path)?,
    ))
}

fn validate_cross_tool_version_identity(
    targo: &TargoVersionIdentity,
    trustc: &CompilerVersionIdentity,
    trustdoc: &CompilerVersionIdentity,
    trustd: &TrustdVersionIdentity,
) -> Result<(), String> {
    for (tool, observed, expected) in [
        ("Targo", targo.binary.as_str(), "targo"),
        ("trustc", trustc.binary.as_str(), "trustc"),
        ("trustdoc", trustdoc.binary.as_str(), "trustdoc"),
        ("trustd", trustd.binary.as_str(), "trustd"),
    ] {
        if observed != expected {
            return Err(format!(
                "full self-verification requires exact stage2 {tool} binary identity `{expected}`, observed `{observed}`"
            ));
        }
    }
    if trustc.host != trustdoc.host {
        return Err(format!(
            "full self-verification requires stage2 trustc/trustdoc host-label consistency: trustc reports host {}, trustdoc reports host {}",
            trustc.host, trustdoc.host,
        ));
    }
    if trustc.release != trustdoc.release {
        return Err(format!(
            "full self-verification requires stage2 trustc/trustdoc release-label consistency: trustc reports release {}, trustdoc reports release {}",
            trustc.release, trustdoc.release,
        ));
    }
    if trustc.commit != trustdoc.commit {
        return Err(format!(
            "full self-verification requires stage2 trustc/trustdoc commit-label consistency: trustc reports commit-hash {}, trustdoc reports commit-hash {}; these labels are not source provenance and are not compared with Git",
            trustc.commit, trustdoc.commit,
        ));
    }
    if targo.host != trustc.host {
        return Err(format!(
            "full self-verification requires stage2 Targo/trustc host-label consistency: Targo reports host {}, trustc reports host {}",
            targo.host, trustc.host,
        ));
    }
    if targo.release != trustc.release {
        return Err(format!(
            "full self-verification requires stage2 Targo/trustc release-label consistency: Targo reports release {}, trustc reports release {}",
            targo.release, trustc.release,
        ));
    }
    if targo.commit != trustc.commit {
        return Err(format!(
            "full self-verification requires stage2 Targo/trustc commit-label consistency: Targo reports commit-hash {}, trustc reports commit-hash {}; these labels are not source provenance and are not compared with Git",
            targo.commit, trustc.commit,
        ));
    }
    if trustd.protocol != trust_router::coordinator::STATUS_VERSION {
        return Err(format!(
            "full self-verification requires stage2 trustd protocol `{}`, observed `{}`",
            trust_router::coordinator::STATUS_VERSION,
            trustd.protocol,
        ));
    }
    if trustd.release != trustc.release {
        return Err(format!(
            "full self-verification requires stage2 trustd/trustc release-label consistency: trustd reports release {}, trustc reports release {}",
            trustd.release, trustc.release,
        ));
    }
    if trustd.commit != trustc.commit {
        return Err(format!(
            "full self-verification requires stage2 trustd/trustc commit-label consistency: trustd reports commit-hash {}, trustc reports commit-hash {}; these labels are not source provenance and are not compared with Git",
            trustd.commit, trustc.commit,
        ));
    }
    Ok(())
}

fn recheck_stage2_toolchain(
    repo_root: &Path,
    expected: &Stage2ToolchainIdentity,
) -> Result<(), String> {
    let expected_endpoints = Stage2EndpointSnapshot {
        targo: expected.targo.clone(),
        trustc: expected.trustc.clone(),
        trustdoc: expected.trustdoc.clone(),
        trustd: expected.trustd.clone(),
    };
    let before_probe = capture_stage2_endpoints(repo_root)?;
    if before_probe != expected_endpoints {
        return Err(
            "stage2 Targo/trustc/trustdoc/trustd endpoint identity changed during self-verification; refusing to execute any replacement version or protocol identity probe"
                .to_string(),
        );
    }

    let (targo_version, trustc_version, trustdoc_version, trustd_version) =
        stage2_version_identities(&before_probe)?;
    let after_probe = capture_stage2_endpoints(repo_root)?;
    if after_probe != before_probe || after_probe != expected_endpoints {
        return Err(
            "stage2 Targo/trustc/trustdoc/trustd endpoint identity changed while rechecking version labels"
                .to_string(),
        );
    }
    validate_cross_tool_version_identity(
        &targo_version,
        &trustc_version,
        &trustdoc_version,
        &trustd_version,
    )?;
    if targo_version != expected.targo_version
        || trustc_version != expected.trustc_version
        || trustdoc_version != expected.trustdoc_version
        || trustd_version != expected.trustd_version
    {
        return Err(format!(
            "stage2 Targo/trustc/trustdoc/trustd version identities changed during self-verification (expected Targo={:?} trustc={:?} trustdoc={:?} trustd={:?}; observed Targo={:?} trustc={:?} trustdoc={:?} trustd={:?})",
            expected.targo_version,
            expected.trustc_version,
            expected.trustdoc_version,
            expected.trustd_version,
            targo_version,
            trustc_version,
            trustdoc_version,
            trustd_version,
        ));
    }
    let trustd_protocol_smoke =
        live_stage2_trustd_protocol_smoke(&before_probe.trustd, &trustd_version)?;
    let smoke_identity_matches =
        match (expected.trustd_protocol_smoke.as_ref(), trustd_protocol_smoke.as_ref()) {
            (Some(expected), Some(observed)) => expected.same_bound_identity(observed),
            (None, None) => true,
            _ => false,
        };
    if !smoke_identity_matches {
        return Err(
            "stage2 trustd live protocol identity changed during self-verification".to_string()
        );
    }
    if capture_stage2_endpoints(repo_root)? != expected_endpoints {
        return Err(
            "stage2 Targo/trustc/trustdoc/trustd endpoint identity changed during the post-stage trustd protocol smoke"
                .to_string(),
        );
    }
    Ok(())
}

fn validate_plain_stage2_bin(canonical_root: &Path) -> Result<PathBuf, String> {
    let mut path = canonical_root.to_path_buf();
    for component in ["build", "host", "stage2", "bin"] {
        path.push(component);
        let metadata = fs::symlink_metadata(&path).map_err(|error| {
            format!(
                "full self-verification requires plain stage2 directory `{}`: {error}",
                path.display()
            )
        })?;
        if metadata.file_type().is_symlink() {
            return Err(format!(
                "full self-verification rejects symlinked stage2 directory `{}`",
                path.display()
            ));
        }
        if metadata_is_windows_reparse_point(&metadata) {
            return Err(format!(
                "full self-verification rejects reparse-point stage2 directory `{}`",
                path.display()
            ));
        }
        if !metadata.file_type().is_dir() {
            return Err(format!(
                "full self-verification requires stage2 directory `{}` to be a directory",
                path.display()
            ));
        }
        let canonical = path.canonicalize().map_err(|error| {
            format!("could not canonicalize stage2 directory `{}`: {error}", path.display())
        })?;
        if canonical != path {
            return Err(format!(
                "stage2 directory resolves outside the exact repository path: `{}`",
                canonical.display()
            ));
        }
    }
    Ok(path)
}

fn validate_stage2_executable(
    canonical_stage2_bin: &Path,
    tool: &str,
) -> Result<ExecutableIdentity, String> {
    let expected = canonical_stage2_bin.join(stage2_tool_file_name(tool));
    let before_metadata = fs::symlink_metadata(&expected).map_err(|error| {
        format!(
            "full self-verification requires stage2 `{tool}` at `{}`: {error}",
            expected.display()
        )
    })?;
    if before_metadata.file_type().is_symlink() {
        return Err(format!(
            "full self-verification rejects symlinked stage2 `{tool}` at `{}`",
            expected.display()
        ));
    }
    if metadata_is_windows_reparse_point(&before_metadata) {
        return Err(format!(
            "full self-verification rejects reparse-point stage2 `{tool}` at `{}`",
            expected.display()
        ));
    }
    if !before_metadata.file_type().is_file() {
        return Err(format!(
            "full self-verification requires stage2 `{tool}` to be a regular file at `{}`",
            expected.display()
        ));
    }
    if !metadata_is_executable(&before_metadata) {
        return Err(format!(
            "full self-verification requires executable stage2 `{tool}` at `{}`",
            expected.display()
        ));
    }
    validate_stage2_executable_size(tool, before_metadata.len())?;
    let canonical_path = expected.canonicalize().map_err(|error| {
        format!("could not canonicalize stage2 `{tool}` at `{}`: {error}", expected.display())
    })?;
    if canonical_path != expected || canonical_path.parent() != Some(canonical_stage2_bin) {
        return Err(format!(
            "stage2 `{tool}` resolves outside the exact repository stage2 bin directory: `{}`",
            canonical_path.display()
        ));
    }
    let file = File::open(&canonical_path).map_err(|error| {
        format!("could not open stage2 `{tool}` at `{}`: {error}", canonical_path.display())
    })?;
    let opened_metadata = file.metadata().map_err(|error| {
        format!(
            "could not inspect opened stage2 `{tool}` at `{}`: {error}",
            canonical_path.display()
        )
    })?;
    if !opened_metadata.is_file() {
        return Err(format!(
            "opened stage2 `{tool}` is not a regular file at `{}`",
            canonical_path.display()
        ));
    }
    if !metadata_is_executable(&opened_metadata) {
        return Err(format!(
            "opened stage2 `{tool}` is not executable at `{}`",
            canonical_path.display()
        ));
    }
    let opened_identity = file_object_identity(&file)?;
    validate_stage2_executable_size(tool, opened_identity.size_bytes)?;
    let sha256 = sha256_reader_bounded(file, MAX_STAGE2_EXECUTABLE_BYTES).map_err(|error| {
        format!("could not hash stage2 `{tool}` at `{}`: {error}", canonical_path.display())
    })?;
    let after_metadata = fs::symlink_metadata(&expected).map_err(|error| {
        format!("could not re-inspect stage2 `{tool}` at `{}`: {error}", expected.display())
    })?;
    if after_metadata.file_type().is_symlink()
        || metadata_is_windows_reparse_point(&after_metadata)
        || !after_metadata.file_type().is_file()
        || !metadata_is_executable(&after_metadata)
    {
        return Err(format!(
            "stage2 `{tool}` path ceased to be an exact regular executable while hashing"
        ));
    }
    let after_file = File::open(&expected).map_err(|error| {
        format!("could not reopen stage2 `{tool}` at `{}`: {error}", expected.display())
    })?;
    let after_identity = file_object_identity(&after_file)?;
    let canonical_after = expected.canonicalize().map_err(|error| {
        format!("could not re-canonicalize stage2 `{tool}` at `{}`: {error}", expected.display())
    })?;
    if after_identity != opened_identity || canonical_after != canonical_path {
        return Err(format!(
            "stage2 `{tool}` path changed file identity, length, or canonical target while hashing"
        ));
    }
    Ok(ExecutableIdentity {
        canonical_path,
        file_identity: opened_identity,
        sha256,
        size_bytes: opened_identity.size_bytes,
    })
}

fn stage2_tool_file_name(tool: &str) -> String {
    format!("{tool}{}", env::consts::EXE_SUFFIX)
}

#[cfg(windows)]
fn metadata_is_windows_reparse_point(metadata: &fs::Metadata) -> bool {
    use std::os::windows::fs::MetadataExt as _;

    const FILE_ATTRIBUTE_REPARSE_POINT: u32 = 0x0000_0400;
    metadata.file_attributes() & FILE_ATTRIBUTE_REPARSE_POINT != 0
}

#[cfg(not(windows))]
fn metadata_is_windows_reparse_point(_metadata: &fs::Metadata) -> bool {
    false
}

fn validate_stage2_executable_size(tool: &str, size_bytes: u64) -> Result<(), String> {
    if size_bytes == 0 || size_bytes > MAX_STAGE2_EXECUTABLE_BYTES as u64 {
        return Err(format!(
            "stage2 `{tool}` size {size_bytes} is outside the required 1..={MAX_STAGE2_EXECUTABLE_BYTES} byte bound"
        ));
    }
    Ok(())
}

fn file_object_identity(file: &File) -> Result<FileObjectIdentity, String> {
    let metadata = file
        .metadata()
        .map_err(|error| format!("could not inspect opened file identity metadata: {error}"))?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;

        Ok(FileObjectIdentity {
            size_bytes: metadata.len(),
            device: metadata.dev(),
            inode: metadata.ino(),
        })
    }
    #[cfg(windows)]
    {
        use std::mem::{MaybeUninit, size_of};
        use std::os::windows::io::AsRawHandle as _;

        use windows_sys::Win32::Storage::FileSystem::{
            FILE_BASIC_INFO, FILE_ID_INFO, FILE_STANDARD_INFO, FileBasicInfo, FileIdInfo,
            FileStandardInfo, GetFileInformationByHandleEx,
        };

        let handle = file.as_raw_handle();
        let mut id = MaybeUninit::<FILE_ID_INFO>::uninit();
        // SAFETY: `id` is correctly sized/aligned output storage and `file`
        // keeps the OS handle live for the complete call.
        if unsafe {
            GetFileInformationByHandleEx(
                handle,
                FileIdInfo,
                id.as_mut_ptr().cast(),
                size_of::<FILE_ID_INFO>() as u32,
            )
        } == 0
        {
            return Err(format!(
                "Windows FileIdInfo identity query failed: {}",
                io::Error::last_os_error()
            ));
        }
        // SAFETY: success initializes the complete FILE_ID_INFO structure.
        let id = unsafe { id.assume_init() };

        let mut basic = MaybeUninit::<FILE_BASIC_INFO>::uninit();
        // SAFETY: `basic` is valid output storage and the handle is live.
        if unsafe {
            GetFileInformationByHandleEx(
                handle,
                FileBasicInfo,
                basic.as_mut_ptr().cast(),
                size_of::<FILE_BASIC_INFO>() as u32,
            )
        } == 0
        {
            return Err(format!(
                "Windows FileBasicInfo continuity query failed: {}",
                io::Error::last_os_error()
            ));
        }
        // SAFETY: success initializes the complete FILE_BASIC_INFO structure.
        let basic = unsafe { basic.assume_init() };

        let mut standard = MaybeUninit::<FILE_STANDARD_INFO>::uninit();
        // SAFETY: `standard` is valid output storage and the handle is live.
        if unsafe {
            GetFileInformationByHandleEx(
                handle,
                FileStandardInfo,
                standard.as_mut_ptr().cast(),
                size_of::<FILE_STANDARD_INFO>() as u32,
            )
        } == 0
        {
            return Err(format!(
                "Windows FileStandardInfo continuity query failed: {}",
                io::Error::last_os_error()
            ));
        }
        // SAFETY: success initializes the complete FILE_STANDARD_INFO structure.
        let standard = unsafe { standard.assume_init() };

        Ok(FileObjectIdentity {
            size_bytes: metadata.len(),
            volume_serial_number: id.VolumeSerialNumber,
            file_id: id.FileId.Identifier,
            change_time: basic.ChangeTime,
            links: standard.NumberOfLinks,
        })
    }
    #[cfg(all(not(unix), not(windows)))]
    {
        let modified_nanos = metadata
            .modified()
            .map_err(|error| format!("could not inspect executable modification time: {error}"))?
            .duration_since(UNIX_EPOCH)
            .map_err(|error| format!("executable modification time predates the epoch: {error}"))?
            .as_nanos();
        Ok(FileObjectIdentity { size_bytes: metadata.len(), modified_nanos })
    }
}

#[cfg(unix)]
fn file_object_identity_json(identity: FileObjectIdentity) -> Value {
    json!({
        "model": "unix-device-inode",
        "device": identity.device,
        "inode": identity.inode,
        "size_bytes": identity.size_bytes,
    })
}

#[cfg(windows)]
fn file_object_identity_json(identity: FileObjectIdentity) -> Value {
    json!({
        "model": "windows-file-id-info-128",
        "volume_serial_number": identity.volume_serial_number,
        "file_id_hex": identity.file_id.iter().map(|byte| format!("{byte:02x}")).collect::<String>(),
        "change_time": identity.change_time,
        "links": identity.links,
        "size_bytes": identity.size_bytes,
    })
}

#[cfg(all(not(unix), not(windows)))]
fn file_object_identity_json(identity: FileObjectIdentity) -> Value {
    json!({
        "model": "size-modified-time-fallback",
        "modified_nanos": identity.modified_nanos.to_string(),
        "size_bytes": identity.size_bytes,
    })
}

fn stage2_verbose_version_output(tool: &str, executable: &Path) -> Result<String, String> {
    let mut command = Command::new(executable);
    command.arg("-Vv").env_clear();
    let output = crate::bounded_process::output(
        &mut command,
        &format!("stage2 {tool} verbose-version identity probe"),
        MAX_IDENTITY_PROBE_STREAM_BYTES,
        IDENTITY_PROBE_TIMEOUT,
    )?;
    if !output.status.success() {
        return Err(format!(
            "stage2 {tool} -Vv failed with {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    String::from_utf8(output.stdout)
        .map_err(|_| format!("stage2 {tool} -Vv output was not valid UTF-8"))
}

fn stage2_targo_version_identity(executable: &Path) -> Result<TargoVersionIdentity, String> {
    let stdout = stage2_verbose_version_output("Targo", executable)?;
    parse_targo_version_identity(&stdout)
}

fn parse_targo_version_identity(stdout: &str) -> Result<TargoVersionIdentity, String> {
    require_leading_version_brand(stdout, "targo", "Targo")?;
    let commit = unique_version_field(stdout, "commit-hash", "Targo").map_err(|error| {
        format!(
            "{error}; repository stage2 Targo requires bootstrap CARGO_COMMIT_HASH wiring and a rebuilt stage2 Targo"
        )
    })?;
    if !is_full_version_commit_label(&commit) {
        return Err(format!(
            "stage2 Targo reported malformed canonical 40- or 64-hex commit-hash version label `{commit}`"
        ));
    }
    Ok(TargoVersionIdentity {
        binary: "targo".to_string(),
        host: unique_version_field(stdout, "host", "Targo")?,
        release: unique_version_field(stdout, "release", "Targo")?,
        commit,
    })
}

fn stage2_compiler_version_identity(
    tool: &str,
    executable: &Path,
) -> Result<CompilerVersionIdentity, String> {
    let stdout = stage2_verbose_version_output(tool, executable)?;
    parse_compiler_version_identity(tool, &stdout)
}

fn parse_compiler_version_identity(
    tool: &str,
    stdout: &str,
) -> Result<CompilerVersionIdentity, String> {
    require_leading_version_brand(stdout, "rustc", tool)?;
    let binary = unique_version_field(stdout, "binary", tool)?;
    if binary != tool {
        return Err(format!(
            "stage2 {tool} reported exact binary identity `{binary}` instead of required `{tool}`"
        ));
    }
    let commit = unique_version_field(stdout, "commit-hash", tool)?;
    if !is_full_version_commit_label(&commit) {
        return Err(format!(
            "stage2 {tool} reported malformed canonical 40- or 64-hex commit-hash version label `{commit}`"
        ));
    }
    Ok(CompilerVersionIdentity {
        binary,
        host: unique_version_field(stdout, "host", tool)?,
        release: unique_version_field(stdout, "release", tool)?,
        commit,
    })
}

fn stage2_trustd_version_identity(executable: &Path) -> Result<TrustdVersionIdentity, String> {
    let mut command = Command::new(executable);
    command.arg("--version").env_clear();
    if let Some((variable, value)) = native_runtime_environment(executable) {
        command.env(variable, value);
    }
    let output = crate::bounded_process::output(
        &mut command,
        "stage2 trustd version identity probe",
        MAX_IDENTITY_PROBE_STREAM_BYTES,
        IDENTITY_PROBE_TIMEOUT,
    )?;
    if !output.status.success() {
        return Err(format!(
            "stage2 trustd --version failed with {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let stdout = String::from_utf8(output.stdout)
        .map_err(|_| "stage2 trustd --version output was not valid UTF-8".to_string())?;
    parse_trustd_version_identity(&stdout)
}

fn parse_trustd_version_identity(stdout: &str) -> Result<TrustdVersionIdentity, String> {
    require_leading_version_brand(stdout, "trustd", "trustd")?;
    let first = stdout.lines().next().expect("leading brand validated");
    let release = first.strip_prefix("trustd ").expect("leading brand validated").to_string();
    let binary = unique_equals_version_field(stdout, "trust.identity", "trustd")?;
    if binary != "trustd" {
        return Err(format!(
            "stage2 trustd reported exact binary identity `{binary}` instead of required `trustd`"
        ));
    }
    let protocol = unique_equals_version_field(stdout, "trust.protocol", "trustd")?;
    if protocol != trust_router::coordinator::STATUS_VERSION {
        return Err(format!(
            "stage2 trustd reported protocol `{protocol}` instead of required `{}`",
            trust_router::coordinator::STATUS_VERSION,
        ));
    }
    let commit = unique_version_field(stdout, "commit-hash", "trustd")?;
    if !is_full_version_commit_label(&commit) {
        return Err(format!(
            "stage2 trustd reported malformed canonical 40- or 64-hex commit-hash version label `{commit}`"
        ));
    }
    let legacy_lines = stdout
        .lines()
        .filter(|line| line.starts_with("trust-repo-commit-hash:"))
        .collect::<Vec<_>>();
    let legacy_valid = match legacy_lines.as_slice() {
        [] => true,
        [line] => line
            .strip_prefix("trust-repo-commit-hash: ")
            .is_some_and(|legacy| legacy == commit.as_str()),
        _ => false,
    };
    if !legacy_valid {
        return Err(
            "stage2 trustd optional trust-repo-commit-hash must be unique and exactly match commit-hash"
                .to_string(),
        );
    }
    Ok(TrustdVersionIdentity { binary, release, commit, protocol })
}

fn unique_equals_version_field(output: &str, field: &str, tool: &str) -> Result<String, String> {
    let label = format!("{field}=");
    let matching = output.lines().filter(|line| line.starts_with(field)).collect::<Vec<_>>();
    if matching.len() != 1 {
        return Err(format!(
            "stage2 {tool} identity output requires exactly one `{label}` field, found {}",
            matching.len()
        ));
    }
    let line = matching[0];
    let Some(value) = line.strip_prefix(&label) else {
        return Err(format!(
            "stage2 {tool} identity field `{field}` must use exact `{label}<value>` syntax"
        ));
    };
    if value.is_empty() || value.trim() != value || value.chars().any(char::is_control) {
        return Err(format!("stage2 {tool} identity field `{field}` was malformed"));
    }
    Ok(value.to_string())
}

#[cfg(unix)]
struct TrustdSmokeChild {
    child: std::process::Child,
    pid: u32,
}

#[cfg(unix)]
impl Drop for TrustdSmokeChild {
    fn drop(&mut self) {
        let _ = crate::bounded_process::terminate_process_group(self.pid);
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

#[cfg(unix)]
fn live_stage2_trustd_protocol_smoke(
    executable: &ExecutableIdentity,
    version: &TrustdVersionIdentity,
) -> Result<Option<TrustdProtocolSmoke>, String> {
    use std::os::unix::fs::{MetadataExt as _, PermissionsExt as _};

    // Each proof owns a fresh endpoint. Never adopt a pre-existing daemon:
    // even a byte-identical process would escape this invocation's lifecycle.
    let socket_root = tempfile::Builder::new()
        .prefix("trust-self-verify-trustd-")
        .tempdir()
        .map_err(|error| format!("could not create private trustd smoke directory: {error}"))?;
    fs::set_permissions(socket_root.path(), fs::Permissions::from_mode(0o700))
        .map_err(|error| format!("could not make trustd smoke directory owner-private: {error}"))?;
    let metadata = fs::symlink_metadata(socket_root.path())
        .map_err(|error| format!("could not inspect private trustd smoke directory: {error}"))?;
    if metadata.file_type().is_symlink()
        || !metadata.is_dir()
        || metadata.uid() != unsafe { libc::geteuid() }
        || metadata.permissions().mode() & 0o777 != 0o700
    {
        return Err(
            "trustd smoke directory must be owner-owned, non-symlink, and mode 0700".to_string()
        );
    }
    let socket = socket_root.path().join("trustd.sock");

    let mut command = Command::new(&executable.canonical_path);
    command
        .arg("--socket")
        .arg(&socket)
        .env_clear()
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    if let Some((variable, value)) = native_runtime_environment(&executable.canonical_path) {
        command.env(variable, value);
    }
    crate::bounded_process::configure_process_group(&mut command);
    let child = command.spawn().map_err(|error| {
        format!(
            "could not start exact stage2 trustd `{}` for the live protocol smoke: {error}",
            executable.canonical_path.display()
        )
    })?;
    let pid = child.id();
    let mut child = TrustdSmokeChild { child, pid };
    let expected_identity = trust_router::coordinator::DaemonIdentity {
        version: trust_router::coordinator::IDENTITY_VERSION.to_string(),
        protocol: version.protocol.clone(),
        release: version.release.clone(),
        commit: version.commit.clone(),
        executable_sha256: executable.sha256.clone(),
    };
    let deadline = Instant::now()
        .checked_add(TRUSTD_READY_TIMEOUT)
        .ok_or_else(|| "trustd live-smoke readiness deadline overflowed".to_string())?;
    loop {
        match crate::bounded_process::exited_without_reaping(&mut child.child) {
            Ok(true) => {
                return Err("exact stage2 trustd exited before becoming ready".to_string());
            }
            Ok(false) => {}
            Err(error) => {
                return Err(format!("could not poll exact stage2 trustd during smoke: {error}"));
            }
        }

        if trust_router::coordinator::daemon_matches_bound_identity(
            &socket,
            &executable.canonical_path,
            &expected_identity,
        ) {
            break;
        }
        if Instant::now() >= deadline {
            return Err(format!(
                "exact stage2 trustd did not become closed IDENTITY/STATUS ready within {TRUSTD_READY_TIMEOUT:?}"
            ));
        }
        thread::sleep(TRUSTD_READY_POLL_INTERVAL);
    }

    if crate::bounded_process::exited_without_reaping(&mut child.child)
        .map_err(|error| format!("could not poll exact stage2 trustd during smoke: {error}"))?
    {
        return Err("exact stage2 trustd exited before the live exchange".to_string());
    }

    let observed = trust_router::coordinator::exercise_daemon_at_with_identity(
        &socket,
        &executable.canonical_path,
        &expected_identity,
        TRUSTD_SMOKE_RESERVATION_LABEL,
    )?;
    let smoke = materialize_stage2_trustd_protocol_smoke(observed, executable, version)?;

    if crate::bounded_process::exited_without_reaping(&mut child.child)
        .map_err(|error| format!("could not poll exact stage2 trustd during smoke: {error}"))?
    {
        return Err("exact stage2 trustd exited before the final smoke observation".to_string());
    }
    Ok(Some(smoke))
}

#[cfg(not(unix))]
fn live_stage2_trustd_protocol_smoke(
    _executable: &ExecutableIdentity,
    _version: &TrustdVersionIdentity,
) -> Result<Option<TrustdProtocolSmoke>, String> {
    // trustd's transport is a Unix-domain socket. The exact same-sysroot binary,
    // hash, release, commit, and advertised protocol remain mandatory on other
    // hosts; a live socket exchange is inapplicable there and is recorded absent.
    Ok(None)
}

#[cfg(unix)]
fn materialize_stage2_trustd_protocol_smoke(
    observed: trust_router::coordinator::DaemonSmoke,
    executable: &ExecutableIdentity,
    version: &TrustdVersionIdentity,
) -> Result<TrustdProtocolSmoke, String> {
    let trust_router::coordinator::DaemonSmoke {
        identity,
        status_before,
        status_reserved,
        status_released,
        reservation_pid,
        reservation_token,
        reservation_bytes,
        reservation_label,
    } = observed;
    if identity.version != trust_router::coordinator::IDENTITY_VERSION
        || identity.protocol != version.protocol
        || identity.release != version.release
        || identity.commit != version.commit
        || identity.executable_sha256 != executable.sha256
    {
        return Err(format!(
            "stage2 trustd live IDENTITY did not bind the exact captured daemon bytes and --version identity (expected version={} protocol={} release={} commit={} sha256={}; observed version={} protocol={} release={} commit={} sha256={})",
            trust_router::coordinator::IDENTITY_VERSION,
            version.protocol,
            version.release,
            version.commit,
            executable.sha256,
            identity.version,
            identity.protocol,
            identity.release,
            identity.commit,
            identity.executable_sha256,
        ));
    }
    if reservation_bytes != TRUSTD_SMOKE_RESERVATION_BYTES
        || reservation_label != TRUSTD_SMOKE_RESERVATION_LABEL
        || reservation_pid == 0
        || reservation_token == 0
        || status_before.version != version.protocol
        || status_reserved.version != version.protocol
        || status_released.version != version.protocol
    {
        return Err(format!(
            "stage2 trustd live exchange did not bind the required one-byte `{TRUSTD_SMOKE_RESERVATION_LABEL}` transition and `{}` STATUS protocol",
            version.protocol,
        ));
    }

    // Serialize through serde_json::Value, matching the exact key ordering a
    // collector observes after reading the enclosing self-verify report.
    let identity_value = serde_json::to_value(&identity).map_err(|error| {
        format!("could not materialize trustd IDENTITY smoke response: {error}")
    })?;
    let status_before_value = serde_json::to_value(&status_before).map_err(|error| {
        format!("could not materialize trustd initial STATUS smoke response: {error}")
    })?;
    let status_reserved_value = serde_json::to_value(&status_reserved).map_err(|error| {
        format!("could not materialize trustd reserved STATUS smoke response: {error}")
    })?;
    let status_released_value = serde_json::to_value(&status_released).map_err(|error| {
        format!("could not materialize trustd released STATUS smoke response: {error}")
    })?;
    let identity_line = serde_json::to_string(&identity_value)
        .map_err(|error| format!("could not serialize trustd IDENTITY smoke response: {error}"))?;
    let status_before_line = serde_json::to_string(&status_before_value).map_err(|error| {
        format!("could not serialize trustd initial STATUS smoke response: {error}")
    })?;
    let status_reserved_line = serde_json::to_string(&status_reserved_value).map_err(|error| {
        format!("could not serialize trustd reserved STATUS smoke response: {error}")
    })?;
    let status_released_line = serde_json::to_string(&status_released_value).map_err(|error| {
        format!("could not serialize trustd released STATUS smoke response: {error}")
    })?;
    let transcript = format!(
        "> PING\n< PONG\n> IDENTITY\n< {identity_line}\n> STATUS\n< {status_before_line}\n> RESERVE {reservation_bytes} {reservation_pid} {reservation_label}\n< GRANTED {reservation_token}\n> STATUS\n< {status_reserved_line}\n> RELEASE {reservation_token}\n< OK\n> STATUS\n< {status_released_line}\n"
    );
    let transcript_sha256 = format!("{:x}", Sha256::digest(transcript.as_bytes()));
    Ok(TrustdProtocolSmoke {
        ping_response: "PONG".to_string(),
        reservation_bytes,
        reservation_label,
        reservation_pid,
        reservation_token,
        identity_response: identity,
        status_before,
        status_reserved,
        status_released,
        transcript,
        transcript_sha256,
    })
}

fn require_leading_version_brand(
    output: &str,
    expected_binary: &str,
    tool: &str,
) -> Result<(), String> {
    let first =
        output.lines().next().ok_or_else(|| format!("stage2 {tool} -Vv output was empty"))?;
    let Some(version) = first.strip_prefix(&format!("{expected_binary} ")) else {
        return Err(format!(
            "stage2 {tool} -Vv leading line must use exact `{expected_binary}` branding, got `{first}`"
        ));
    };
    if version.is_empty() || version.trim() != version || version.chars().any(char::is_control) {
        return Err(format!("stage2 {tool} -Vv leading version line was malformed"));
    }
    Ok(())
}

fn unique_version_field(output: &str, field: &str, tool: &str) -> Result<String, String> {
    let label = format!("{field}:");
    let prefix = format!("{label} ");
    let matching = output.lines().filter(|line| line.starts_with(&label)).collect::<Vec<_>>();
    let value = match matching.as_slice() {
        [line] => line.strip_prefix(&prefix).ok_or_else(|| {
            format!(
                "stage2 {tool} identity field `{field}` must use exact `{prefix}<value>` syntax"
            )
        })?,
        [] => return Err(format!("stage2 {tool} identity output omitted `{field}:`")),
        _ => return Err(format!("stage2 {tool} identity output repeated `{field}:`")),
    };
    if value.is_empty()
        || value.trim() != value
        || value.bytes().any(|byte| byte.is_ascii_whitespace() || byte.is_ascii_control())
    {
        return Err(format!(
            "stage2 {tool} identity output reported malformed atomic `{field}` value `{value}`"
        ));
    }
    Ok(value.to_string())
}

fn is_full_version_commit_label(value: &str) -> bool {
    matches!(value.len(), 40 | 64) && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

#[cfg(unix)]
fn metadata_is_executable(metadata: &fs::Metadata) -> bool {
    use std::os::unix::fs::PermissionsExt;
    metadata.permissions().mode() & 0o111 != 0
}

#[cfg(not(unix))]
fn metadata_is_executable(_metadata: &fs::Metadata) -> bool {
    true
}

fn is_loader_authority_env_key(key: &str) -> bool {
    let upper = key.to_ascii_uppercase();
    upper.starts_with("LD_")
        || upper.starts_with("DYLD_")
        || upper == "LIBPATH"
        || upper == "SHLIB_PATH"
        || upper.starts_with("LDR_")
        || upper.starts_with("_RLD")
}

fn verification_env(
    level: u8,
    full_verifier: bool,
    offline: bool,
    proof_artifact_root: &Path,
) -> Result<(BTreeMap<String, String>, Value), String> {
    let mut env_map = unicode_environment(env::vars_os())?;
    let mut removed_toolchain_overrides = BTreeSet::new();
    let loader_overrides =
        env_map.keys().filter(|key| is_loader_authority_env_key(key)).cloned().collect::<Vec<_>>();
    for key in loader_overrides {
        env_map.remove(&key);
        removed_toolchain_overrides.insert(key);
    }
    for key in [
        "RUSTC",
        "RUSTDOC",
        "TRUSTC",
        "TRUSTDOC",
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "CARGO_BUILD_RUSTC",
        "CARGO_CACHE_RUSTC_INFO",
        "CARGO_BUILD_RUSTDOC",
        "CARGO_BUILD_RUSTC_WRAPPER",
        "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
        "CARGO_BUILD_RUSTFLAGS",
        "CARGO_BUILD_RUSTDOCFLAGS",
        "CARGO_BUILD_TARGET",
        "CARGO_TARGET_DIR",
        "TRUST_TARGO_BIN",
        "TRUST_TRUSTC_BIN",
        "TRUST_TARGO_TRUST_BIN",
        "TRUST_TRUSTDOC_BIN",
        "TRUST_TRUSTD_BIN",
        "TRUST_SELF_VERIFY_TARGO_SHA256",
        "TRUST_SELF_VERIFY_TRUSTC_SHA256",
        "TRUST_SELF_VERIFY_TRUSTDOC_SHA256",
        "TRUST_SELF_VERIFY_TRUSTD_SHA256",
        "TRUST_TARGO_TEST_EXECUTE_FRESH_SESSION",
        "TRUST_TARGO_TEST_EXECUTION_MANIFEST",
        "TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256",
        "TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION",
        "TRUST_TARGO_TEST_MONITOR_SESSION",
    ] {
        if env_map.remove(key).is_some() {
            removed_toolchain_overrides.insert(key.to_string());
        }
    }
    // Empty wrapper variables override repository/user Cargo configuration;
    // merely removing inherited environment values lets `.cargo/config.toml`
    // reintroduce a post-validation process that can rewrite rustc argv/output.
    for key in [
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "CARGO_BUILD_RUSTC_WRAPPER",
        "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
    ] {
        env_map.insert(key.to_string(), String::new());
    }
    let target_flag_overrides = env_map
        .keys()
        .filter(|key| {
            key.starts_with("CARGO_TARGET_")
                && (key.ends_with("_RUSTFLAGS") || key.ends_with("_RUSTDOCFLAGS"))
        })
        .cloned()
        .collect::<Vec<_>>();
    for key in target_flag_overrides {
        env_map.remove(&key);
        removed_toolchain_overrides.insert(key);
    }
    env_map.insert("TRUST_TARGO_VERIFY".to_string(), "1".to_string());
    // Dependency scope remains a tracked compiler option. The former generated-
    // MIR switch was never wired and is now retired: generated MIR is always in
    // batteries-on scope, so remove its stale environment spelling rather than
    // pretending to translate it into policy.
    env_map.remove("TRUST_VERIFY_INCLUDE_GENERATED");
    let include_dependencies = normalize_scope_bool(
        "TRUST_VERIFY_INCLUDE_DEPENDENCIES",
        env_map.remove("TRUST_VERIFY_INCLUDE_DEPENDENCIES").as_deref().unwrap_or("yes"),
    )?;
    let worker_threads =
        normalize_worker_threads(env_map.remove("TRUST_VERIFY_WORKER_THREADS").as_deref())?;
    // The retired policy label used to participate in compiler-side scope
    // heuristics. Targo now supplies an explicit tracked crate role for every
    // Cargo unit, so forwarding the label would be both inert and misleading.
    env_map.remove("TRUST_VERIFY");
    env_map.remove("TRUST_VERIFY_POLICY");
    env_map.remove("TRUST_DUMP_ONLY");
    env_map.insert("CARGO_INCREMENTAL".to_string(), "0".to_string());
    env_map.insert("CARGO_TERM_COLOR".to_string(), "never".to_string());
    if offline {
        env_map.insert("CARGO_NET_OFFLINE".to_string(), "true".to_string());
    }

    let flags = verification_flags_with_scope(
        level,
        full_verifier,
        &include_dependencies,
        worker_threads.as_deref(),
        proof_artifact_root,
    )?;
    let mut stripped = Map::new();
    let mut stripped_disable_flags = Map::new();
    for key in [
        "RUSTFLAGS",
        "RUSTDOCFLAGS",
        "RUSTFLAGS_BOOTSTRAP",
        "RUSTFLAGS_NOT_BOOTSTRAP",
        "RUSTDOCFLAGS_BOOTSTRAP",
        "RUSTDOCFLAGS_NOT_BOOTSTRAP",
        "MAGIC_EXTRA_RUSTFLAGS",
    ] {
        let current = env_map.get(key).cloned().unwrap_or_default();
        let words = if matches!(key, "RUSTFLAGS" | "RUSTDOCFLAGS") {
            split_plain_rustflags(&current)
        } else {
            // Bootstrap's private flag variables use its historical
            // whitespace protocol rather than Cargo's RUSTFLAGS protocol.
            split_env_words(&current)
        };
        reject_uninspectable_inherited_flags(key, &words)?;
        let (kept, removed) = strip_inherited_verifier_words(words);
        let merged = append_flag_words(kept, &flags);
        env_map.insert(key.to_string(), merged.join(" "));
        stripped.insert(key.to_string(), Value::Bool(!removed.is_empty()));
        stripped_disable_flags.insert(key.to_string(), json!(removed));
    }
    for key in ["CARGO_ENCODED_RUSTFLAGS", "CARGO_ENCODED_RUSTDOCFLAGS"] {
        let Some(current) = env_map.get(key).cloned() else {
            continue;
        };
        let words = split_encoded_rustflags(&current);
        reject_uninspectable_inherited_flags(key, &words)?;
        let (kept, removed) = strip_inherited_verifier_words(words);
        let merged = append_flag_words(kept, &flags);
        env_map.insert(key.to_string(), merged.join(&UNIT_SEPARATOR.to_string()));
        stripped.insert(key.to_string(), Value::Bool(!removed.is_empty()));
        stripped_disable_flags.insert(key.to_string(), json!(removed));
    }

    Ok((
        env_map,
        json!({
            "verification_flags": flags,
            "stripped_verifier_policy": Value::Object(stripped.clone()),
            "stripped_verifier_policy_flags": Value::Object(stripped_disable_flags.clone()),
            // Retained as schema-compatible aliases for existing report
            // consumers. The fields describe every inherited Trust policy
            // option, not only the verification switch their names came from.
            "stripped_no_trust_verify": Value::Object(stripped),
            "stripped_trust_verify_disable_flags": Value::Object(stripped_disable_flags),
            "transport_source": "Cargo-authenticated compiler-message TRUST_JSON transport only",
            "stage2_identity_model": "plain repository stage2 bin plus before/open/after endpoint file-object identity, length, canonical path, bounded SHA-256, exact Targo/trustc/trustdoc/trustd binary branding, matching release/commit labels, exact trustd protocol, and on Unix a bounded exact-sibling PING/closed-IDENTITY/semantic-STATUS/one-byte-RESERVE/RELEASE live smoke; version labels are diagnostics, not Git/source provenance; persistent changes only",
            "stage2_execution_identity_bound": false,
            "source_provenance_bound": false,
            "source_cleanliness_bound": false,
            "planning_executes_tool_identity_probes": full_verifier,
            "transient_same_user_swap_restore_detected": false,
            "external_execution_isolation_required": true,
            "worker_threads": if full_verifier {
                worker_threads.clone().map(Value::String).unwrap_or(Value::Null)
            } else {
                Value::Null
            },
            "tracked_scope_options": {
                "include_dependencies": include_dependencies,
                "worker_threads": worker_threads,
                "proof_artifact_root": proof_artifact_root,
            },
            "removed_toolchain_override_environment": removed_toolchain_overrides,
            "legacy_environment_translated": true,
        }),
    ))
}

fn unicode_environment(
    variables: impl IntoIterator<Item = (OsString, OsString)>,
) -> Result<BTreeMap<String, String>, String> {
    variables
        .into_iter()
        .map(|(name, value)| {
            let name = name.into_string().map_err(|name| {
                format!("environment variable name is not valid Unicode: {name:?}")
            })?;
            let value = value.into_string().map_err(|value| {
                format!("environment variable `{name}` is not valid Unicode: {value:?}")
            })?;
            Ok((name, value))
        })
        .collect()
}

fn normalize_worker_threads(value: Option<&str>) -> Result<Option<String>, String> {
    let Some(value) = value else {
        return Ok(None);
    };
    if value.is_empty() {
        return Ok(None);
    }
    let parsed = value.parse::<usize>().ok().filter(|value| (1..=256).contains(value));
    parsed.map(|value| Some(value.to_string())).ok_or_else(|| {
        "TRUST_VERIFY_WORKER_THREADS requires one integer from 1 through 256 with no whitespace or additional compiler arguments"
            .to_string()
    })
}

fn normalize_scope_bool(variable: &str, value: &str) -> Result<String, String> {
    match value.trim().to_ascii_lowercase().as_str() {
        "1" | "y" | "yes" | "on" | "true" => Ok("yes".to_string()),
        "0" | "n" | "no" | "off" | "false" => Ok("no".to_string()),
        _ => {
            Err(format!("{variable} requires a boolean value (0/1, yes/no, on/off, or true/false)"))
        }
    }
}

#[cfg(test)]
fn verification_flags(level: u8, full_verifier: bool) -> Vec<String> {
    verification_flags_with_scope(
        level,
        full_verifier,
        "yes",
        None,
        Path::new("/tmp/trust-self-verify-test-proof-root"),
    )
    .expect("test proof root flag")
}

fn verification_flags_with_scope(
    level: u8,
    full_verifier: bool,
    include_dependencies: &str,
    worker_threads: Option<&str>,
    proof_artifact_root: &Path,
) -> Result<Vec<String>, String> {
    let proof_artifact_root = proof_artifact_root.to_str().ok_or_else(|| {
        "self-verification proof root is not valid UTF-8 for rustflags".to_string()
    })?;
    if proof_artifact_root.chars().any(char::is_whitespace)
        || proof_artifact_root.contains(UNIT_SEPARATOR)
    {
        return Err(
            "self-verification proof root cannot contain whitespace or Cargo's encoded-rustflags delimiter"
                .to_string(),
        );
    }
    let mut flags = vec![
        format!("-Z codegen-backend={DEFAULT_CODEGEN_BACKEND}"),
        "-Z trust-verify-output=json".to_string(),
        format!("-Z trust-verify-level={level}"),
        format!("-Z trust-verify-session={}", verification_session_nonce()),
        format!("-Ztrust-proof-artifact-root={proof_artifact_root}"),
    ];
    // Verification is batteries-on. The session nonce asks Targo to attach
    // authenticated per-unit role/package metadata; this harness supplies only
    // that nonce and tracked policy.
    let _ = full_verifier;
    flags.push(format!("-Z trust-verify-include-dependencies={include_dependencies}"));
    if let Some(worker_threads) = worker_threads {
        flags.push(format!("-Z trust-verify-worker-threads={worker_threads}"));
    }
    Ok(flags)
}

fn split_env_words(value: &str) -> Vec<String> {
    value.split_whitespace().filter(|word| !word.is_empty()).map(str::to_string).collect()
}

fn split_plain_rustflags(value: &str) -> Vec<String> {
    value.split(' ').map(str::trim).filter(|word| !word.is_empty()).map(str::to_string).collect()
}

fn split_encoded_rustflags(value: &str) -> Vec<String> {
    if value.is_empty() {
        Vec::new()
    } else {
        value.split(UNIT_SEPARATOR).map(str::to_string).collect()
    }
}

fn reject_uninspectable_inherited_flags(variable: &str, words: &[String]) -> Result<(), String> {
    if let Some(argfile) = words.iter().find(|word| word.starts_with('@')) {
        return Err(format!(
            "{variable} contains response or shell argfile `{argfile}`; self-verification requires an explicit inspectable compiler argument vector"
        ));
    }
    if words.iter().any(|word| word == "--") {
        return Err(format!(
            "{variable} contains a semantic `--` separator; self-verification cannot prove that canonical verifier policy remains in rustc's option stream"
        ));
    }
    let mut index = 0;
    while index < words.len() {
        let word = &words[index];
        let option = if word == "-Z" {
            index += 1;
            words.get(index).map(String::as_str)
        } else {
            word.strip_prefix("-Z").filter(|option| !option.is_empty())
        };
        if option.is_some_and(|option| canonical_rustc_option_name(option) == "llvm-plugins") {
            return Err(format!(
                "{variable} contains forbidden in-process LLVM plugin option `{word}`"
            ));
        }
        index += 1;
    }
    if let Some(option) = find_forbidden_in_process_codegen_arg(words) {
        return Err(format!(
            "{variable} contains forbidden in-process LLVM argument channel `{option}`"
        ));
    }
    Ok(())
}

fn strip_inherited_verifier_words(words: Vec<String>) -> (Vec<String>, Vec<String>) {
    let mut kept = Vec::new();
    let mut removed = Vec::new();
    let mut index = 0;
    while index < words.len() {
        let word = &words[index];
        let next = words.get(index + 1);
        if word == "-Z" && next.is_some_and(|next| inherited_verifier_policy_option(next)) {
            removed.push(format!("-Z {}", next.expect("checked next")));
            index += 2;
            continue;
        }
        if let Some(option) = word.strip_prefix("-Z") {
            if !option.is_empty() && inherited_verifier_policy_option(option) {
                removed.push(word.clone());
                index += 1;
                continue;
            }
        }
        kept.push(word.clone());
        index += 1;
    }
    (kept, removed)
}

fn inherited_verifier_policy_option(option: &str) -> bool {
    let name = canonical_rustc_option_name(option);
    name == "trust-verify=off" || name == "codegen-backend" || name.starts_with("trust-")
}

static VERIFICATION_SESSION_SEQUENCE: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

fn verification_session_nonce() -> String {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_nanos())
        .unwrap_or(0);
    let sequence = VERIFICATION_SESSION_SEQUENCE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    format!("self-verify-{}-{nanos}-{sequence}", std::process::id())
}

fn append_flag_words(mut words: Vec<String>, flags: &[String]) -> Vec<String> {
    for flag in flags {
        let flag_words = split_env_words(flag);
        if flag_words.is_empty() || contains_subsequence(&words, &flag_words) {
            continue;
        }
        words.extend(flag_words);
    }
    words
}

fn contains_subsequence(words: &[String], needle: &[String]) -> bool {
    if needle.is_empty() {
        return true;
    }
    words.windows(needle.len()).any(|window| window == needle)
}

fn run_stage(plan: &StagePlan, root: &Path, report_dir: &Path) -> Value {
    let logs_dir = report_dir.join("logs");
    let log_stem = stage_log_stem(&plan.label);
    let stdout_path = logs_dir.join(format!("{log_stem}.stdout.log"));
    let stderr_path = logs_dir.join(format!("{log_stem}.stderr.log"));

    let started_at = now_string();
    let monotonic_start = Instant::now();
    let mut process_timed_out = false;
    let mut missing_command = false;
    let mut returncode: Option<i32>;
    let mut error: Option<String> = None;
    let mut stage2_toolchain_identity_verified = false;
    let mut descendants_terminated = false;
    // Parse evidence from the exact bytes returned by the bounded child
    // capture. Reopening the published log path would let a same-user build
    // script replace it between capture and proof parsing.
    let mut captured_stdout = Vec::new();

    if let Err(log_error) = create_private_subdirectory(&logs_dir) {
        returncode = Some(1);
        error = Some(log_error);
    } else {
        let stdout_file = open_private_new_file(&stdout_path);
        let stderr_file = open_private_new_file(&stderr_path);
        match (stdout_file, stderr_file) {
            (Ok(mut stdout_file), Ok(mut stderr_file)) => {
                let mut command = Command::new(&plan.argv[0]);
                command.args(&plan.argv[1..]).current_dir(root).env_clear().envs(&plan.env);
                // Stage plans validate this duration before any output path or child is created.
                // Retain a zero fallback here so a future internal caller cannot turn an invalid
                // value into an unbounded subprocess or a conversion panic.
                let timeout =
                    Duration::try_from_secs_f64(plan.timeout_sec).unwrap_or(Duration::ZERO);
                match crate::bounded_process::output(
                    &mut command,
                    "self-verification stage command",
                    MAX_STAGE_LOG_STREAM_BYTES,
                    timeout,
                ) {
                    Ok(output) => {
                        returncode = Some(process_returncode(&output.status));
                        captured_stdout = output.stdout;
                        if let Err(write_error) = stdout_file.write_all(&captured_stdout) {
                            returncode = Some(1);
                            append_stage_error(
                                &mut error,
                                format!("failed to write bounded stdout log: {write_error}"),
                            );
                        }
                        if let Err(write_error) = stderr_file.write_all(&output.stderr) {
                            returncode = Some(1);
                            append_stage_error(
                                &mut error,
                                format!("failed to write bounded stderr log: {write_error}"),
                            );
                        }
                    }
                    Err(process_error) => {
                        process_timed_out = process_error.contains("timeout");
                        descendants_terminated = process_error.contains("background descendant");
                        missing_command = process_error.contains("could not start");
                        returncode = Some(if missing_command { 127 } else { 1 });
                        let _ = writeln!(stderr_file, "self-verify-harness: {process_error}");
                        error = Some(process_error);
                    }
                }
                if let Err(sync_error) = stdout_file.sync_all() {
                    returncode = Some(1);
                    append_stage_error(
                        &mut error,
                        format!("failed to fsync stdout log: {sync_error}"),
                    );
                }
                if let Err(sync_error) = stderr_file.sync_all() {
                    returncode = Some(1);
                    append_stage_error(
                        &mut error,
                        format!("failed to fsync stderr log: {sync_error}"),
                    );
                }
            }
            (stdout_result, stderr_result) => {
                returncode = Some(1);
                error = Some(format!(
                    "failed to create private log files: stdout={:?} stderr={:?}",
                    stdout_result.err(),
                    stderr_result.err()
                ));
            }
        }
    }

    if let Some(expected) = &plan.stage2_toolchain {
        match recheck_stage2_toolchain(root, expected) {
            Ok(()) => {
                stage2_toolchain_identity_verified = true;
            }
            Err(identity_error) => {
                returncode = Some(1);
                append_stage_error(
                    &mut error,
                    format!(
                        "stage2 Targo/trustc/trustdoc/trustd identity and protocol recheck failed: {identity_error}"
                    ),
                );
            }
        }
    }

    let duration_sec = round3(monotonic_start.elapsed().as_secs_f64());
    let mut summary =
        parse_authenticated_cargo_transport(&captured_stdout, &stdout_path, root, plan);
    summary.stage2_toolchain_identity_verified = stage2_toolchain_identity_verified;
    let solver_suite = solver_suite_json(&summary);

    let status = if process_timed_out {
        "timed_out"
    } else if missing_command || returncode != Some(0) {
        "failed"
    } else {
        let preliminary = evaluate_proof("passed", returncode, false, &solver_suite);
        if preliminary.get("complete").and_then(Value::as_bool).unwrap_or(false) {
            "passed"
        } else if preliminary
            .get("status")
            .and_then(Value::as_str)
            .is_some_and(|status| status == "failed")
        {
            "failed"
        } else {
            "incomplete"
        }
    };
    let proof = evaluate_proof(status, returncode, process_timed_out, &solver_suite);
    let mut stage = json!({
        "label": plan.label,
        "description": plan.description,
        "status": status,
        "started_at": started_at,
        "finished_at": now_string(),
        "duration_sec": duration_sec,
        "timeout_sec": plan.timeout_sec,
        "process_timed_out": process_timed_out,
        "process_group_isolated": cfg!(unix),
        "descendants_terminated": descendants_terminated,
        "returncode": returncode,
        "command": {
            "argv": plan.argv,
            "command_line": command_line(&plan.argv),
        },
        "environment": recorded_environment(&plan.env),
        "env_policy": plan.env_policy,
        "stage2_toolchain_identity": stage2_toolchain_identity_json(plan.stage2_toolchain.as_ref()),
        "identity_probes": {
            "executed_during_planning": plan.stage2_toolchain.is_some(),
            "rechecked_after_stage": stage2_toolchain_identity_verified,
            "scope": if plan.stage2_toolchain.is_some() {
                "bounded planning-time Targo/trustc/trustdoc version probes plus exact-sibling trustd --version and live PING/closed-IDENTITY/semantic-STATUS/one-byte-RESERVE/RELEASE protocol smoke on Unix; after the stage, endpoint/version checks and the complete trustd smoke were repeated"
            } else {
                "none"
            },
        },
        "verification_scope": verification_scope(plan),
        "logs": {
            "stdout": relative_path(&stdout_path, root),
            "stderr": relative_path(&stderr_path, root),
        },
        "solver_suite": solver_suite,
        "compiler_self_verification": solver_suite_json(&summary).get("compiler_self_verification").cloned().unwrap_or(Value::Null),
        "proof": proof,
    });
    let performance = performance_summary(
        std::slice::from_ref(&stage),
        stage["solver_suite"].clone(),
        status,
        &stage["proof"],
    );
    stage["performance"] = performance;
    if let Some(error) = error {
        stage["error"] = Value::String(error);
    }
    stage
}

fn append_stage_error(error: &mut Option<String>, message: String) {
    if let Some(existing) = error {
        existing.push_str("; ");
        existing.push_str(&message);
    } else {
        *error = Some(message);
    }
}

fn process_returncode(status: &ExitStatus) -> i32 {
    if let Some(code) = status.code() {
        return code;
    }
    #[cfg(unix)]
    if let Some(signal) = std::os::unix::process::ExitStatusExt::signal(status) {
        return 128_i32.saturating_add(signal);
    }
    1
}

fn planned_stage(plan: &StagePlan) -> Value {
    let solver_suite = solver_suite_json(&TransportSummary::default());
    let proof = json!({
        "status": "not_run",
        "complete": false,
        "timeout_is_incomplete_proof": true,
        "obligation_summary": obligation_outcome_summary(&solver_suite),
        "reasons": ["dry run only; no compiler or solver evidence was collected"],
    });
    let mut stage = json!({
        "label": plan.label,
        "description": plan.description,
        "status": "planned",
        "timeout_sec": plan.timeout_sec,
        "command": {
            "argv": plan.argv,
            "command_line": command_line(&plan.argv),
        },
        "environment": recorded_environment(&plan.env),
        "env_policy": plan.env_policy,
        "stage2_toolchain_identity": stage2_toolchain_identity_json(plan.stage2_toolchain.as_ref()),
        "identity_probes": {
            "executed_during_planning": plan.stage2_toolchain.is_some(),
            "rechecked_after_stage": false,
            "scope": if plan.stage2_toolchain.is_some() {
                "bounded Targo/trustc/trustdoc version probes plus exact-sibling trustd --version and live PING/closed-IDENTITY/semantic-STATUS/one-byte-RESERVE/RELEASE protocol smoke on Unix; the planned stage command was not executed"
            } else {
                "none"
            },
        },
        "verification_scope": verification_scope(plan),
        "solver_suite": solver_suite,
        "compiler_self_verification": solver_suite.get("compiler_self_verification").cloned().unwrap_or(Value::Null),
        "proof": proof,
    });
    stage["performance"] =
        performance_summary(std::slice::from_ref(&stage), solver_suite, "planned", &stage["proof"]);
    stage
}

fn parse_authenticated_cargo_transport(
    captured_stdout: &[u8],
    stdout_path: &Path,
    root: &Path,
    plan: &StagePlan,
) -> TransportSummary {
    let mut summary = TransportSummary::default();
    let source = relative_path(stdout_path, root);
    let package_scan = BufReader::new(io::Cursor::new(captured_stdout));

    let expected = match expected_self_verify_package(root, &plan.evidence_manifest) {
        Ok(expected) => expected,
        Err(error) => {
            summary.parse_errors.push(error);
            return summary;
        }
    };
    let selected_packages = match selected_package_from_cargo_json(package_scan, &expected) {
        Ok(selected) => selected,
        Err(error) => {
            summary.parse_errors.push(format!("{source}: {error}"));
            return summary;
        }
    };

    let evidence_input = BufReader::new(io::Cursor::new(captured_stdout));

    let evidence = match parse_cargo_json_stdout_with_authenticated_messages(
        evidence_input,
        &selected_packages,
        &plan.verification_session,
        true,
    ) {
        Ok(evidence) => evidence,
        Err(error) => {
            summary
                .parse_errors
                .push(format!("{source}: unauthenticated Cargo compiler evidence: {error}"));
            return summary;
        }
    };
    if let Err(error) = evidence.require_successful_selected_roots(&selected_packages, true) {
        summary
            .parse_errors
            .push(format!("{source}: incomplete successful Cargo proof inventory: {error}"));
        return summary;
    }

    let inventory_report = match cargo_proof_inventory_report(
        evidence.declared_inventory.as_ref(),
        &evidence.parsed.completed_proof_targets,
        &evidence.parsed.coverage_proof_targets,
    ) {
        Ok(Some(report)) => match serde_json::to_value(report) {
            Ok(report) => report,
            Err(error) => {
                summary.parse_errors.push(format!(
                    "{source}: could not serialize canonical Cargo proof inventory: {error}"
                ));
                return summary;
            }
        },
        Ok(None) => {
            summary.parse_errors.push(format!(
                "{source}: successful Cargo proof stream had no canonical proof inventory"
            ));
            return summary;
        }
        Err(error) => {
            summary.parse_errors.push(format!(
                "{source}: could not project canonical Cargo proof inventory: {error}"
            ));
            return summary;
        }
    };
    summary.cargo_proof_inventories.push(inventory_report);

    let parsed = evidence.parsed.require_structured_json_transport(true);
    for defect in
        parsed.verification_results.iter().filter(|result| result.kind.starts_with("transport:"))
    {
        summary.inconsistencies.push(format!(
            "{source}: authenticated compiler transport defect [{}]: {}",
            defect.kind, defect.message
        ));
    }

    let completed = &parsed.completed_proof_targets;
    let observed = &parsed.observed_proof_targets;
    let covered = &parsed.coverage_proof_targets;
    if completed.is_empty() {
        summary
            .inconsistencies
            .push(format!("{source}: no authenticated primary terminal crate summary"));
    }
    if evidence.compiled_targets != *completed {
        summary.inconsistencies.push(target_inventory_mismatch(
            "compiler-artifact/terminal",
            &evidence.compiled_targets,
            completed,
        ));
    }
    if observed != completed {
        summary.inconsistencies.push(target_inventory_mismatch(
            "observed/terminal",
            observed,
            completed,
        ));
    }
    if covered != completed {
        summary.inconsistencies.push(target_inventory_mismatch(
            "coverage/terminal",
            covered,
            completed,
        ));
    }
    if parsed.coverage_rows.len() != completed.len() {
        summary.inconsistencies.push(format!(
            "{source}: authenticated coverage row count {} did not match completed target count {}",
            parsed.coverage_rows.len(),
            completed.len()
        ));
    }
    for coverage in &parsed.coverage_rows {
        summary.coverage_eligible = summary
            .coverage_eligible
            .saturating_add(u64::try_from(coverage.eligible).unwrap_or(u64::MAX));
        summary.coverage_processed = summary
            .coverage_processed
            .saturating_add(u64::try_from(coverage.processed).unwrap_or(u64::MAX));
        if !coverage.is_complete() {
            summary.inconsistencies.push(format!(
                "{source}: incomplete authenticated coverage for crate {:?}: processed {} of {} eligible bodies",
                coverage.crate_name, coverage.processed, coverage.eligible
            ));
        }
    }
    for target in parsed
        .zero_eligible_coverage_targets
        .iter()
        .filter(|target| target.proof_unit_role == "primary")
    {
        summary.inconsistencies.push(format!(
            "{source}: authenticated coverage for selected proof root `{}` declared zero eligible bodies",
            target.report_label()
        ));
    }

    summary.completed_targets = completed.iter().map(CargoTargetIdentity::report_label).collect();
    summary.coverage_targets = covered.iter().map(CargoTargetIdentity::report_label).collect();
    summary.completed_target_identities = completed
        .iter()
        .map(|target| (target.report_label(), cargo_target_identity_json(target)))
        .collect();
    summary.coverage_target_identities = covered
        .iter()
        .map(|target| (target.report_label(), cargo_target_identity_json(target)))
        .collect();
    summary.coverage_complete = !completed.is_empty()
        && completed == covered
        && parsed.coverage_rows.len() == completed.len()
        && parsed.coverage_rows.iter().all(|coverage| coverage.is_complete())
        && !parsed
            .zero_eligible_coverage_targets
            .iter()
            .any(|target| target.proof_unit_role == "primary");
    summary.authenticated_cargo_transport = !evidence.authenticated_transport_messages.is_empty();

    for (index, (target, message)) in
        evidence.authenticated_transport_messages.into_iter().enumerate()
    {
        let decoded = match serde_json::to_value(message) {
            Ok(Value::Object(map)) => Value::Object(map),
            Ok(_) => {
                summary.inconsistencies.push(format!(
                    "{source}:{}: authenticated transport message was not an object",
                    index + 1
                ));
                continue;
            }
            Err(error) => {
                summary.inconsistencies.push(format!(
                    "{source}:{}: could not serialize authenticated transport: {error}",
                    index + 1
                ));
                continue;
            }
        };
        if decoded.get("type").and_then(Value::as_str) == Some("coverage_summary") {
            continue;
        }
        summary.messages += 1;
        ingest_transport_message(
            &mut summary,
            &target,
            &decoded,
            plan._proof_artifact_root.path(),
            &source,
            index + 1,
        );
    }

    summary
}

struct ExpectedSelfVerifyPackage {
    name: String,
    root: PathBuf,
}

fn expected_self_verify_package(
    repo_root: &Path,
    evidence_manifest: &Path,
) -> Result<ExpectedSelfVerifyPackage, String> {
    let manifest = if evidence_manifest.is_absolute() {
        evidence_manifest.to_path_buf()
    } else {
        repo_root.join(evidence_manifest)
    };
    let canonical_manifest = manifest.canonicalize().map_err(|error| {
        format!("could not resolve self-verify evidence manifest `{}`: {error}", manifest.display())
    })?;
    let canonical_repo = repo_root
        .canonicalize()
        .map_err(|error| format!("could not resolve self-verify repository root: {error}"))?;
    if !canonical_manifest.starts_with(&canonical_repo) {
        return Err(format!(
            "self-verify evidence manifest `{}` escapes repository root `{}`",
            canonical_manifest.display(),
            canonical_repo.display()
        ));
    }
    let contents = crate::input_limits::read_bounded_utf8_file(
        &canonical_manifest,
        crate::input_limits::MAX_RELEASE_METADATA_BYTES,
    )
    .map_err(|error| {
        format!(
            "could not read self-verify evidence manifest `{}`: {error}",
            canonical_manifest.display()
        )
    })?;
    let manifest_value = contents.parse::<toml::Value>().map_err(|error| {
        format!(
            "could not parse self-verify evidence manifest `{}`: {error}",
            canonical_manifest.display()
        )
    })?;
    let name = manifest_value
        .get("package")
        .and_then(|package| package.get("name"))
        .and_then(toml::Value::as_str)
        .filter(|name| !name.is_empty())
        .ok_or_else(|| {
            format!(
                "self-verify evidence manifest `{}` omitted package.name",
                canonical_manifest.display()
            )
        })?
        .to_string();
    let root = canonical_manifest
        .parent()
        .ok_or_else(|| "self-verify evidence manifest has no parent directory".to_string())?
        .to_path_buf();
    Ok(ExpectedSelfVerifyPackage { name, root })
}

fn selected_package_from_cargo_json<R: BufRead>(
    mut reader: R,
    expected: &ExpectedSelfVerifyPackage,
) -> Result<BTreeMap<String, String>, String> {
    let mut package_ids = BTreeSet::new();
    let mut line_index = 0usize;
    while let Some(line) =
        read_bounded_utf8_line(&mut reader, MAX_CARGO_JSON_LINE_BYTES).map_err(|error| {
            format!("could not safely read canonical Targo stdout line {}: {error}", line_index + 1)
        })?
    {
        line_index += 1;
        let envelope: Value = serde_json::from_str(&line).map_err(|error| {
            format!(
                "canonical Targo stdout line {line_index} was not a Cargo JSON envelope: {error}"
            )
        })?;
        let reason = envelope.get("reason").and_then(Value::as_str);
        if !matches!(reason, Some("compiler-artifact" | "compiler-message")) {
            continue;
        }
        let Some(package_id) = envelope.get("package_id").and_then(Value::as_str) else {
            continue;
        };
        if !cargo_package_id_matches_name(package_id, &expected.name) {
            continue;
        }
        let Some(src_path) = envelope
            .get("target")
            .and_then(|target| target.get("src_path"))
            .and_then(Value::as_str)
        else {
            continue;
        };
        let Ok(canonical_source) = Path::new(src_path).canonicalize() else {
            continue;
        };
        if canonical_source.starts_with(&expected.root) {
            package_ids.insert(package_id.to_string());
        }
    }
    if package_ids.len() != 1 {
        return Err(format!(
            "expected exactly one Cargo package id for self-verify package {:?}, found [{}]",
            expected.name,
            package_ids.iter().map(|id| format!("{id:?}")).collect::<Vec<_>>().join(", ")
        ));
    }
    Ok(package_ids.into_iter().map(|package_id| (package_id, expected.name.clone())).collect())
}

fn cargo_package_id_matches_name(package_id: &str, expected_name: &str) -> bool {
    package_id
        .rsplit_once('#')
        .map(|(_, fragment)| {
            fragment == expected_name
                || fragment.strip_prefix(expected_name).is_some_and(|rest| rest.starts_with('@'))
        })
        .unwrap_or(false)
        || package_id.strip_prefix(expected_name).is_some_and(|rest| rest.starts_with(' '))
}

fn target_inventory_mismatch(
    label: &str,
    actual: &BTreeSet<CargoTargetIdentity>,
    expected: &BTreeSet<CargoTargetIdentity>,
) -> String {
    let missing =
        expected.difference(actual).map(CargoTargetIdentity::report_label).collect::<Vec<_>>();
    let unexpected =
        actual.difference(expected).map(CargoTargetIdentity::report_label).collect::<Vec<_>>();
    format!(
        "authenticated {label} target inventory mismatch (missing: [{}]; unexpected: [{}])",
        missing.join(", "),
        unexpected.join(", ")
    )
}

fn cargo_target_identity_json(target: &CargoTargetIdentity) -> Value {
    json!({
        "schema": CARGO_TARGET_IDENTITY_SCHEMA,
        "package_id": target.package_id,
        "package_name": target.package_name,
        "target_name": target.target_name,
        "target_kinds": target.target_kinds,
        "compile_target": target.compile_target,
        "compile_mode": target.compile_mode,
        "compile_kind": target.compile_kind,
        "unit_identity_sha256": target.unit_identity_sha256,
        "compile_target_spec_sha256": target.compile_target_spec_sha256,
        "proof_unit_index": target.proof_unit_index,
        "proof_unit_mode": target.proof_unit_mode,
        "proof_unit_role": target.proof_unit_role,
        "semantics_sha256": target.semantics_sha256,
        "report_label": target.report_label(),
    })
}

fn cargo_target_identity_from_json(value: &Value) -> Result<CargoTargetIdentity, String> {
    let object =
        value.as_object().ok_or_else(|| "Cargo target identity was not an object".to_string())?;
    if object.get("schema").and_then(Value::as_str) != Some(CARGO_TARGET_IDENTITY_SCHEMA) {
        return Err("Cargo target identity schema mismatch".to_string());
    }
    let required_string = |field: &str| -> Result<String, String> {
        object
            .get(field)
            .and_then(Value::as_str)
            .filter(|value| !value.is_empty())
            .map(str::to_string)
            .ok_or_else(|| format!("Cargo target identity omitted nonempty `{field}`"))
    };
    let target_kinds = object
        .get("target_kinds")
        .and_then(Value::as_array)
        .ok_or_else(|| "Cargo target identity omitted `target_kinds` array".to_string())?
        .iter()
        .map(|kind| {
            kind.as_str()
                .filter(|kind| !kind.is_empty())
                .map(str::to_string)
                .ok_or_else(|| "Cargo target identity contained an invalid target kind".to_string())
        })
        .collect::<Result<Vec<_>, _>>()?;
    if target_kinds.is_empty() {
        return Err("Cargo target identity contained no target kinds".to_string());
    }
    let unique_target_kinds = target_kinds.iter().collect::<BTreeSet<_>>();
    if unique_target_kinds.len() != target_kinds.len() {
        return Err("Cargo target identity repeated a target kind".to_string());
    }
    let compile_target_spec_sha256 =
        match object.get("compile_target_spec_sha256") {
            Some(Value::Null) => None,
            Some(Value::String(digest)) if trust_types::digest::is_stable_sha256_hex(digest) => Some(digest.clone()),
            None => {
                return Err("Cargo target identity omitted explicit `compile_target_spec_sha256`"
                    .to_string());
            }
            _ => {
                return Err("Cargo target identity contained a non-canonical target-spec SHA-256"
                    .to_string());
            }
        };
    let proof_unit_role = required_string("proof_unit_role")?;
    if !matches!(proof_unit_role.as_str(), "primary" | "test-execution" | "dependency") {
        return Err(format!(
            "Cargo target identity contained unsupported proof-unit role `{proof_unit_role}`"
        ));
    }
    let compile_mode = required_string("compile_mode")?;
    if !matches!(
        compile_mode.as_str(),
        "build"
            | "test"
            | "check"
            | "check-test"
            | "doc"
            | "doctest"
            | "docscrape"
            | "run-custom-build"
    ) {
        return Err(format!(
            "Cargo target identity contained unsupported compile mode `{compile_mode}`"
        ));
    }
    let compile_kind = required_string("compile_kind")?;
    if !matches!(compile_kind.as_str(), "host" | "target") {
        return Err(format!(
            "Cargo target identity contained unsupported compile kind `{compile_kind}`"
        ));
    }
    let unit_identity_sha256 = required_string("unit_identity_sha256")?;
    if !trust_types::digest::is_stable_sha256_hex(&unit_identity_sha256) {
        return Err(
            "Cargo target identity contained a non-canonical unit-identity SHA-256".to_string()
        );
    }
    let proof_unit_mode = required_string("proof_unit_mode")?;
    if proof_unit_mode != compile_mode {
        return Err(format!(
            "Cargo target identity disagreed about its compile mode: compile_mode={compile_mode:?}, proof_unit_mode={proof_unit_mode:?}"
        ));
    }
    let identity = CargoTargetIdentity {
        package_id: required_string("package_id")?,
        package_name: required_string("package_name")?,
        target_name: required_string("target_name")?,
        target_kinds,
        compile_target: required_string("compile_target")?,
        compile_mode,
        compile_kind,
        unit_identity_sha256,
        compile_target_spec_sha256,
        proof_unit_index: object
            .get("proof_unit_index")
            .and_then(Value::as_u64)
            .ok_or_else(|| "Cargo target identity omitted `proof_unit_index`".to_string())?,
        proof_unit_mode,
        proof_unit_role,
        semantics_sha256: required_string("semantics_sha256")?,
    };
    if !trust_types::digest::is_stable_sha256_hex(&identity.semantics_sha256) {
        return Err("Cargo target identity contained a non-canonical semantic descriptor SHA-256"
            .to_string());
    }
    let label = object
        .get("report_label")
        .and_then(Value::as_str)
        .ok_or_else(|| "Cargo target identity omitted `report_label`".to_string())?;
    if label != identity.report_label() {
        return Err("Cargo target identity report label did not match its exact fields".to_string());
    }
    Ok(identity)
}

fn cargo_scoped_function(target: &CargoTargetIdentity, function: &str) -> String {
    format!("{}::{function}", target.report_label())
}

fn ingest_transport_message(
    summary: &mut TransportSummary,
    cargo_target: &CargoTargetIdentity,
    message: &Value,
    proof_artifact_root: &Path,
    source: &str,
    line: usize,
) {
    let message_type = message.get("type").and_then(Value::as_str);
    match message_type {
        Some("crate_summary") => {
            let mut crate_summary = message.clone();
            if let Some(crate_summary) = crate_summary.as_object_mut() {
                crate_summary
                    .insert("cargo_target".to_string(), cargo_target_identity_json(cargo_target));
            }
            summary.crate_summaries.push(crate_summary);
        }
        Some("function_result") => {
            summary.function_results += 1;
            if let Some(function) = message.get("function").and_then(Value::as_str) {
                summary.functions.push(cargo_scoped_function(cargo_target, function));
            }
            match normalized_cache_status(
                message.get("cache_status").or_else(|| message.get("cache")),
            ) {
                Some("hit") => {
                    summary.cache_hit_functions += 1;
                    summary.cache_function_status_available = true;
                }
                Some("miss") => {
                    summary.cache_miss_functions += 1;
                    summary.cache_function_status_available = true;
                }
                _ => {}
            }
            ingest_result_rows(
                summary,
                cargo_target,
                message,
                proof_artifact_root,
                source,
                line,
                message.get("function").and_then(Value::as_str),
            );
        }
        Some("verification_result") => {
            summary.function_results += 1;
            if let Some(function) = message.get("function").and_then(Value::as_str) {
                summary.functions.push(cargo_scoped_function(cargo_target, function));
            }
            ingest_result_rows(
                summary,
                cargo_target,
                message,
                proof_artifact_root,
                source,
                line,
                message.get("function").and_then(Value::as_str),
            );
        }
        other => {
            summary.inconsistencies.push(format!(
                "{source}:{line}: unsupported TRUST_JSON type {:?}",
                other.unwrap_or("<missing>")
            ));
        }
    }
}

fn ingest_result_rows(
    summary: &mut TransportSummary,
    cargo_target: &CargoTargetIdentity,
    message: &Value,
    proof_artifact_root: &Path,
    source: &str,
    line: usize,
    function: Option<&str>,
) {
    let scoped_function = function.map(|function| cargo_scoped_function(cargo_target, function));
    let cargo_target_json = cargo_target_identity_json(cargo_target);
    let results = message.get("results").or_else(|| message.get("rows")).and_then(Value::as_array);
    let Some(results) = results else {
        summary
            .inconsistencies
            .push(format!("{source}:{line}: function_result missing results list"));
        return;
    };
    if let Some(total) = message.get("total").and_then(Value::as_u64) {
        summary.reported_obligations += total;
        if total != results.len() as u64 {
            summary.inconsistencies.push(format!(
                "{source}:{line}: total={total} but results has {} row(s)",
                results.len()
            ));
        }
    }
    for (row_index, result) in results.iter().enumerate() {
        let Some(row) = result.as_object() else {
            summary
                .inconsistencies
                .push(format!("{source}:{line}: obligation row is not an object"));
            continue;
        };
        summary.obligation_rows += 1;
        let raw_outcome = raw_outcome_status(row);
        let outcome = normalize_outcome(raw_outcome);
        let outcome_class = classify_outcome(&outcome);
        *summary.outcomes.entry(outcome.clone()).or_default() += 1;
        let solver = row
            .get("solver")
            .and_then(Value::as_str)
            .filter(|value| !value.is_empty())
            .unwrap_or("unknown")
            .to_string();
        let time_ms = row.get("time_ms").and_then(Value::as_u64).unwrap_or_else(|| {
            summary
                .inconsistencies
                .push(format!("{source}:{line}: invalid time_ms for solver {solver:?}"));
            0
        });
        summary.total_solver_time_ms += time_ms;
        add_totals(&mut summary.solvers, &solver, &outcome, time_ms);
        let kind = row
            .get("kind")
            .and_then(Value::as_str)
            .filter(|value| !value.is_empty())
            .unwrap_or("unknown")
            .to_string();
        add_totals(&mut summary.kinds, &kind, &outcome, time_ms);
        match row_cache_status(result) {
            Some("hit") => summary.cache_hit_obligations += 1,
            Some("miss") => {
                summary.cache_miss_available = true;
                summary.cache_miss_obligations += 1;
            }
            _ => {}
        }
        let proof_binding = match serde_json::from_value::<trust_types::TransportObligationResult>(
            result.clone(),
        ) {
            Ok(transport) => proof_binding_summary(&transport, proof_artifact_root),
            Err(error) => {
                summary.inconsistencies.push(format!(
                    "{source}:{line}: authenticated obligation row could not be restored to its typed transport form: {error}"
                ));
                rejected_proof_binding_summary(&error.to_string())
            }
        };
        if row.get("native_trust_ir").is_some() || row.get("proof_evidence").is_some() {
            summary.obligation_evidence.push(json!({
                "source": source,
                "line": line,
                "cargo_target": cargo_target_json,
                "function": scoped_function,
                "raw_function": function,
                "row_index": row_index,
                "obligation_id": row.get("obligation_id").cloned().unwrap_or(Value::Null),
                "kind": row.get("kind").cloned().unwrap_or(Value::Null),
                "raw_outcome": raw_outcome.map(|value| Value::String(value.to_string())).unwrap_or(Value::Null),
                "outcome": outcome.clone(),
                "outcome_class": outcome_class.as_str(),
                "solver": solver.clone(),
                "time_ms": time_ms,
                "native_trust_ir": row.get("native_trust_ir").cloned().unwrap_or(Value::Null),
                "proof_evidence": row.get("proof_evidence").cloned().unwrap_or(Value::Null),
                "proof_binding": proof_binding.clone(),
            }));
        }
        let blockers = coverage_blockers_for_row(
            source,
            line,
            cargo_target,
            scoped_function.as_deref(),
            function,
            row_index,
            result,
            &outcome,
            &proof_binding,
        );
        summary.coverage_blockers.extend(blockers.iter().cloned());
        summary.verification_rows.push(json!({
            "schema": VERIFICATION_ROW_SCHEMA,
            "source": source,
            "line": line,
            "cargo_target": cargo_target_json,
            "function": scoped_function,
            "raw_function": function,
            "row_index": row_index,
            "obligation_id": row.get("obligation_id").cloned().unwrap_or(Value::Null),
            "kind": row.get("kind").cloned().unwrap_or(Value::Null),
            "raw_outcome": raw_outcome.map(|value| Value::String(value.to_string())).unwrap_or(Value::Null),
            "outcome": outcome.clone(),
            "outcome_class": outcome_class.as_str(),
            "solver": solver,
            "time_ms": time_ms,
            "native_trust_ir": row.get("native_trust_ir").cloned().unwrap_or(Value::Null),
            "proof_evidence": row.get("proof_evidence").cloned().unwrap_or(Value::Null),
            "proof_binding": proof_binding.clone(),
            "coverage_blockers": blockers,
            "supported": !matches!(
                outcome.as_str(),
                "unsupported" | "missing" | "skipped" | "no_verification" | "unverified"
            ),
            "failed": outcome_class == OutcomeClass::Failed,
            "complete": outcome_class == OutcomeClass::Proved
                && proof_binding.get("accepted").and_then(Value::as_bool) == Some(true),
        }));
    }
}

fn raw_outcome_status(row: &Map<String, Value>) -> Option<&str> {
    for key in ["outcome", "status"] {
        let Some(value) = row.get(key) else {
            continue;
        };
        match value {
            Value::String(text) if !text.trim().is_empty() => return Some(text),
            Value::Object(map) => {
                if let Some(status) = map
                    .get("status")
                    .and_then(Value::as_str)
                    .filter(|status| !status.trim().is_empty())
                {
                    return Some(status);
                }
            }
            _ => {}
        }
    }
    None
}

fn normalize_outcome(raw: Option<&str>) -> String {
    let Some(raw) = raw else {
        return "unknown".to_string();
    };
    let token = normalize_outcome_token(raw);
    if token.is_empty() {
        return "unknown".to_string();
    }
    match token.as_str() {
        "timeout" | "timedout" | "timed_out" => "timed_out".to_string(),
        "runtimechecked" | "runtime_checked" => "runtime_checked".to_string(),
        "skip" | "skipped" => "skipped".to_string(),
        "cancelled" => "canceled".to_string(),
        "noverification" | "no_verification" | "notverified" | "not_verified" => {
            "no_verification".to_string()
        }
        other => other.to_string(),
    }
}

fn normalize_outcome_token(raw: &str) -> String {
    let mut normalized = String::new();
    let mut last_was_separator = false;
    for ch in raw.trim().chars() {
        let ch = ch.to_ascii_lowercase();
        if ch.is_ascii_alphanumeric() {
            normalized.push(ch);
            last_was_separator = false;
        } else if ch == '_' || ch == '-' || ch.is_ascii_whitespace() {
            if !normalized.is_empty() && !last_was_separator {
                normalized.push('_');
                last_was_separator = true;
            }
        } else {
            normalized.push(ch);
            last_was_separator = false;
        }
    }
    while normalized.ends_with('_') {
        normalized.pop();
    }
    normalized
}

fn classify_outcome(outcome: &str) -> OutcomeClass {
    if outcome == PROVED_OUTCOME {
        OutcomeClass::Proved
    } else if FAILED_OUTCOMES.contains(&outcome) {
        OutcomeClass::Failed
    } else if INCOMPLETE_OUTCOMES.contains(&outcome) {
        OutcomeClass::Incomplete
    } else {
        OutcomeClass::Unrecognized
    }
}

#[derive(Debug, Default)]
struct ProofBindingEvidence {
    canonical_sha256_digest_binding: bool,
    repo_local_readable_path_binding: bool,
    digest_matches_materialized_path: bool,
    digest_matches_inline_materialization: bool,
    materialized_artifact_or_transcript_binding: bool,
    digest_evidence: Vec<Value>,
    path_evidence: Vec<Value>,
    artifact_evidence: Vec<Value>,
}

fn proof_binding_summary(row: &trust_types::TransportObligationResult, root: &Path) -> Value {
    let proof = row.proof_evidence.as_ref();
    let proof_evidence_present = proof.is_some();
    let proof_evidence_object = proof.is_some();
    let proof_evidence_status = proof
        .and_then(|proof| serde_json::to_value(proof.status).ok())
        .and_then(|status| status.as_str().map(str::to_string))
        .map(|status| normalize_outcome(Some(&status)));
    let proof_evidence_status_proved = proof_evidence_status.as_deref() == Some(PROVED_OUTCOME);
    let canonical_root = fs::canonicalize(root).ok();
    let publication_grade_native_proof = canonical_root
        .as_deref()
        .is_some_and(|root| transport_obligation_has_publishable_native_proof(row, root));
    let (binding_evidence, required_artifact_materialization) =
        typed_proof_artifact_bindings(row, canonical_root.as_deref().unwrap_or(root));
    let artifact_or_transcript_binding =
        binding_evidence.materialized_artifact_or_transcript_binding;
    let accepted = proof_evidence_object
        && proof_evidence_status_proved
        && publication_grade_native_proof
        && artifact_or_transcript_binding;
    json!({
        "schema": "trust.self-verify-harness.proof-binding.v1",
        "proof_evidence_present": proof_evidence_present,
        "proof_evidence_object": proof_evidence_object,
        "proof_evidence_status": proof_evidence_status.map(Value::String).unwrap_or(Value::Null),
        "proof_evidence_status_proved": proof_evidence_status_proved,
        "publication_grade_native_proof": publication_grade_native_proof,
        "canonical_sha256_digest_binding": binding_evidence.canonical_sha256_digest_binding,
        "repo_local_readable_path_binding": binding_evidence.repo_local_readable_path_binding,
        "digest_matches_materialized_path": binding_evidence.digest_matches_materialized_path,
        "digest_matches_inline_materialization": binding_evidence.digest_matches_inline_materialization,
        "materialized_artifact_or_transcript_binding": binding_evidence.materialized_artifact_or_transcript_binding,
        "artifact_or_transcript_binding": artifact_or_transcript_binding,
        "required_artifact_materialization": required_artifact_materialization,
        "digest_evidence": binding_evidence.digest_evidence,
        "path_evidence": binding_evidence.path_evidence,
        "artifact_evidence": binding_evidence.artifact_evidence,
        "accepted": accepted,
    })
}

fn rejected_proof_binding_summary(error: &str) -> Value {
    json!({
        "schema": "trust.self-verify-harness.proof-binding.v1",
        "proof_evidence_present": false,
        "proof_evidence_object": false,
        "proof_evidence_status": Value::Null,
        "proof_evidence_status_proved": false,
        "publication_grade_native_proof": false,
        "canonical_sha256_digest_binding": false,
        "repo_local_readable_path_binding": false,
        "digest_matches_materialized_path": false,
        "materialized_artifact_or_transcript_binding": false,
        "artifact_or_transcript_binding": false,
        "required_artifact_materialization": {
            "mode": "unavailable",
            "complete": false,
            "error": error,
        },
        "digest_evidence": [],
        "path_evidence": [],
        "artifact_evidence": [],
        "accepted": false,
    })
}

fn typed_proof_artifact_bindings(
    row: &trust_types::TransportObligationResult,
    root: &Path,
) -> (ProofBindingEvidence, Value) {
    let proof = row.proof_evidence.as_ref();
    let Some(proof) = proof else {
        return (
            ProofBindingEvidence::default(),
            json!({
                "mode": "missing_proof_evidence",
                "solver_transcript_bound": false,
                "replay_or_check_bound": false,
                "trust_vc_certificate_bound": false,
                "complete": false,
            }),
        );
    };

    let trust_vc_certificate_backed = proof.suite.eq_ignore_ascii_case("trust-vc")
        && proof.artifacts.iter().any(is_trust_vc_digest_bound_proof_certificate_artifact);
    let mut evidence = ProofBindingEvidence::default();
    let mut solver_transcript_bound = false;
    let mut replay_or_check_bound = false;
    let mut trust_vc_certificate_bound = false;

    for (index, artifact) in proof.artifacts.iter().enumerate() {
        let solver_transcript = is_solver_transcript_artifact(artifact);
        let replay_or_check = is_replay_or_check_artifact(artifact);
        let trust_vc_certificate = is_trust_vc_digest_bound_proof_certificate_artifact(artifact);
        let binding = typed_artifact_binding(index, artifact, root);
        let bound = binding.get("accepted").and_then(Value::as_bool) == Some(true);
        solver_transcript_bound |= solver_transcript && bound;
        replay_or_check_bound |= replay_or_check && bound;
        trust_vc_certificate_bound |= trust_vc_certificate && bound;
        evidence.canonical_sha256_digest_binding |=
            binding.get("canonical_sha256_digest").and_then(Value::as_bool).unwrap_or(false);
        evidence.repo_local_readable_path_binding |=
            binding.get("repo_local_readable_path").and_then(Value::as_bool).unwrap_or(false);
        evidence.digest_matches_materialized_path |= binding
            .get("digest_matches_materialized_path")
            .and_then(Value::as_bool)
            .unwrap_or(false);
        evidence.digest_matches_inline_materialization |= binding
            .get("digest_matches_inline_materialization")
            .and_then(Value::as_bool)
            .unwrap_or(false);
        if let Some(digest) = binding.get("declared_digest") {
            evidence.digest_evidence.push(json!({
                "artifact_index": index,
                "kind": artifact.kind,
                "digest": digest,
            }));
        }
        if let Some(path) = binding.get("path_evidence").filter(|value| !value.is_null()) {
            evidence.path_evidence.push(path.clone());
        }
        evidence.artifact_evidence.push(binding);
    }

    let topology_defect = trust_types::transport_proof_artifact_topology_defect_at_root(
        &proof.suite,
        &proof.artifacts,
        row.obligation_id.as_deref(),
        root,
    );
    let proof_paths_secure = evidence.artifact_evidence.iter().all(|binding| {
        binding.get("materialization_present").and_then(Value::as_bool) != Some(true)
            || binding.get("accepted").and_then(Value::as_bool) == Some(true)
    });
    let native_paths_secure = row.native_trust_ir.as_ref().is_none_or(|native| {
        native.artifacts.iter().enumerate().all(|(index, artifact)| {
            artifact.materialization.is_none()
                || typed_artifact_binding(index, artifact, root)
                    .get("accepted")
                    .and_then(Value::as_bool)
                    == Some(true)
        })
    });
    let complete = topology_defect.is_none() && proof_paths_secure && native_paths_secure;
    evidence.materialized_artifact_or_transcript_binding = complete;
    let requirement = json!({
        "mode": if trust_vc_certificate_backed {
            "trust_vc_digest_bound_certificate"
        } else {
            "solver_transcript_and_replay_or_check"
        },
        "solver_transcript_bound": solver_transcript_bound,
        "replay_or_check_bound": replay_or_check_bound,
        "trust_vc_certificate_bound": trust_vc_certificate_bound,
        "complete": complete,
        "topology_defect": topology_defect.map(Value::String).unwrap_or(Value::Null),
        "proof_materialization_paths_secure": proof_paths_secure,
        "native_materialization_paths_secure": native_paths_secure,
        "uri_only_artifacts_receive_no_credit": true,
        "metadata_only_artifacts_receive_no_credit": true,
        "accepts_bounded_inline_materialization": true,
        "requires_repo_local_non_symlink_regular_file_for_path_materialization": true,
        "producer_gap": if complete {
            Value::Null
        } else {
            Value::String("proof producers must carry an exclusive owner-bound materialized certificate or an exact typed transcript/replay/check DAG; inline frames are bounded and path-backed frames must be repo-local non-symlink regular files".to_string())
        },
    });
    (evidence, requirement)
}

fn typed_artifact_binding(
    index: usize,
    artifact: &trust_types::TransportEvidenceArtifact,
    root: &Path,
) -> Value {
    let declared_digest = artifact
        .digest
        .as_ref()
        .filter(|digest| digest.algorithm == "sha256" && trust_types::digest::is_stable_sha256_hex(&digest.value))
        .map(|digest| digest.value.as_str());
    let canonical_sha256_digest = declared_digest.is_some();

    let materialization = artifact.materialization.as_ref();
    let path_evidence = materialization
        .and_then(|materialization| materialization.materialized_path.as_deref())
        .map(|path| proof_path_evidence("materialized_path", path, root));
    let repo_local_readable_path = path_evidence
        .as_ref()
        .is_some_and(|path| path.get("accepted").and_then(Value::as_bool) == Some(true));
    let digest_matches_materialized_path = declared_digest.is_some_and(|declared| {
        path_evidence.as_ref().and_then(|path| path.get("actual_sha256")).and_then(Value::as_str)
            == Some(declared)
            && materialization.is_some_and(|materialization| {
                artifact.digest.as_ref().is_some_and(|digest| {
                    materialization.matches_sha256_digest_at_root(digest, root)
                })
            })
    });
    let digest_matches_inline_materialization = declared_digest.is_some()
        && materialization.is_some_and(|materialization| {
            materialization.materialized_path.is_none()
                && artifact
                    .digest
                    .as_ref()
                    .is_some_and(|digest| materialization.matches_sha256_digest(digest))
        });

    // `metadata` is deliberately not artifact content.  It carries small
    // backend-specific facts and is producer-controlled, so hashing it would
    // let a producer self-declare a digest over arbitrary JSON instead of
    // materializing the transcript/check/certificate bytes themselves.
    let accepted = canonical_sha256_digest
        && (digest_matches_inline_materialization
            || (repo_local_readable_path && digest_matches_materialized_path));

    json!({
        "artifact_index": index,
        "kind": artifact.kind,
        "uri": artifact.uri,
        "declared_digest": declared_digest.map(|digest| format!("sha256:{digest}")),
        "canonical_sha256_digest": canonical_sha256_digest,
        "solver_transcript": is_solver_transcript_artifact(artifact),
        "replay_or_check": is_replay_or_check_artifact(artifact),
        "trust_vc_digest_bound_certificate": is_trust_vc_digest_bound_proof_certificate_artifact(artifact),
        "repo_local_readable_path": repo_local_readable_path,
        "digest_matches_materialized_path": digest_matches_materialized_path,
        "digest_matches_inline_materialization": digest_matches_inline_materialization,
        "materialization_present": materialization.is_some(),
        "materialization_byte_len": materialization.map(|materialization| materialization.byte_len),
        "proof_binding_id": materialization.map(|materialization| materialization.proof_binding_id.as_str()),
        "referenced_artifacts": materialization.map(|materialization| &materialization.referenced_artifacts),
        "metadata_present": artifact.metadata.is_some(),
        "metadata_materialization_credit": false,
        "path_evidence": path_evidence,
        "accepted": accepted,
    })
}

fn proof_path_evidence(field: &str, path: &str, root: &Path) -> Value {
    let candidate = Path::new(path);
    let absolute_candidate =
        if candidate.is_absolute() { candidate.to_path_buf() } else { root.join(candidate) };
    let canonical_root = fs::canonicalize(root).unwrap_or_else(|_| root.to_path_buf());
    let entry_metadata = match fs::symlink_metadata(&absolute_candidate) {
        Ok(metadata) => metadata,
        Err(error) => {
            return json!({
                "field": field,
                "path": path,
                "repo_local": false,
                "readable": false,
                "is_file": false,
                "is_symlink": false,
                "accepted": false,
                "error": error.to_string(),
            });
        }
    };
    if entry_metadata.file_type().is_symlink() || !entry_metadata.file_type().is_file() {
        return json!({
            "field": field,
            "path": path,
            "repo_local": false,
            "readable": false,
            "is_file": entry_metadata.file_type().is_file(),
            "is_symlink": entry_metadata.file_type().is_symlink(),
            "accepted": false,
            "error": "proof artifact path must name a non-symlink regular file",
        });
    }
    match fs::canonicalize(&absolute_candidate) {
        Ok(canonical_path) => {
            let repo_local = canonical_path.starts_with(&canonical_root);
            let opened = File::open(&canonical_path);
            let readable = opened.is_ok();
            let metadata = opened.as_ref().ok().and_then(|file| file.metadata().ok());
            let is_file = metadata.as_ref().is_some_and(|metadata| metadata.is_file());
            let size_within_limit = metadata.as_ref().is_some_and(|metadata| {
                metadata.len() <= trust_types::MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES as u64
            });
            let actual_sha256 = opened
                .ok()
                .filter(|_| repo_local && is_file && size_within_limit)
                .and_then(|file| {
                    sha256_reader_bounded(
                        file,
                        trust_types::MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES,
                    )
                    .ok()
                });
            let accepted =
                repo_local && readable && is_file && size_within_limit && actual_sha256.is_some();
            json!({
                "field": field,
                "path": path,
                "resolved": relative_path(&canonical_path, &canonical_root),
                "repo_local": repo_local,
                "readable": readable,
                "is_file": is_file,
                "is_symlink": false,
                "size_within_limit": size_within_limit,
                "max_bytes": trust_types::MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES,
                "actual_sha256": actual_sha256,
                "accepted": accepted,
            })
        }
        Err(error) => json!({
            "field": field,
            "path": path,
            "repo_local": false,
            "readable": false,
            "is_file": false,
            "is_symlink": false,
            "accepted": false,
            "error": error.to_string(),
        }),
    }
}

fn sha256_reader_bounded(reader: impl Read, max_bytes: usize) -> io::Result<String> {
    let mut reader = BufReader::new(reader);
    let mut hasher = Sha256::new();
    let mut buffer = [0_u8; 64 * 1024];
    let mut total = 0_usize;
    loop {
        let read = reader.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        total = total.checked_add(read).ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidData, "artifact byte count overflow")
        })?;
        if total > max_bytes {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("artifact exceeds the {max_bytes}-byte safety limit while hashing"),
            ));
        }
        hasher.update(&buffer[..read]);
    }
    Ok(format!("{:x}", hasher.finalize()))
}


fn add_totals(totals: &mut BTreeMap<String, SolverTotals>, key: &str, outcome: &str, time_ms: u64) {
    let entry = totals.entry(key.to_string()).or_default();
    entry.obligations += 1;
    entry.time_ms += time_ms;
    *entry.outcomes.entry(outcome.to_string()).or_default() += 1;
}

fn coverage_blockers_for_row(
    source: &str,
    line: usize,
    cargo_target: &CargoTargetIdentity,
    function: Option<&str>,
    raw_function: Option<&str>,
    row_index: usize,
    result: &Value,
    outcome: &str,
    proof_binding: &Value,
) -> Vec<Value> {
    let mut blockers = Vec::new();
    for field in ["coverage_blocker", "coverage_blockers", "unsupported_reason"] {
        if let Some(value) = result.get(field) {
            match value {
                Value::Array(items) => {
                    for item in items {
                        blockers.push(coverage_blocker(
                            source,
                            line,
                            cargo_target,
                            function,
                            raw_function,
                            row_index,
                            field,
                            item,
                        ));
                    }
                }
                Value::Null => {}
                other => blockers.push(coverage_blocker(
                    source,
                    line,
                    cargo_target,
                    function,
                    raw_function,
                    row_index,
                    field,
                    other,
                )),
            }
        }
    }
    match classify_outcome(outcome) {
        OutcomeClass::Incomplete => {
            blockers.push(json!({
                "schema": COVERAGE_BLOCKER_SCHEMA,
                "source": source,
                "line": line,
                "cargo_target": cargo_target_identity_json(cargo_target),
                "function": function,
                "raw_function": raw_function,
                "row_index": row_index,
                "kind": "incomplete_outcome",
                "reason": format!("solver obligation ended as {outcome}"),
                "detail": outcome,
            }));
        }
        OutcomeClass::Unrecognized => {
            blockers.push(json!({
                "schema": COVERAGE_BLOCKER_SCHEMA,
                "source": source,
                "line": line,
                "cargo_target": cargo_target_identity_json(cargo_target),
                "function": function,
                "raw_function": raw_function,
                "row_index": row_index,
                "kind": "unrecognized_outcome",
                "reason": format!("solver obligation reported unrecognized outcome `{outcome}`"),
                "detail": outcome,
            }));
        }
        OutcomeClass::Proved => {
            if proof_binding.get("accepted").and_then(Value::as_bool) != Some(true) {
                blockers.push(json!({
                    "schema": COVERAGE_BLOCKER_SCHEMA,
                    "source": source,
                    "line": line,
                    "cargo_target": cargo_target_identity_json(cargo_target),
                    "function": function,
                    "raw_function": raw_function,
                    "row_index": row_index,
                    "kind": "missing_proof_binding",
                    "reason": "proved solver obligation lacks row-level proof evidence with artifact/transcript binding",
                    "detail": proof_binding,
                }));
            }
        }
        OutcomeClass::Failed => {}
    }
    blockers
}

fn coverage_blocker(
    source: &str,
    line: usize,
    cargo_target: &CargoTargetIdentity,
    function: Option<&str>,
    raw_function: Option<&str>,
    row_index: usize,
    kind: &str,
    detail: &Value,
) -> Value {
    json!({
        "schema": COVERAGE_BLOCKER_SCHEMA,
        "source": source,
        "line": line,
        "cargo_target": cargo_target_identity_json(cargo_target),
        "function": function,
        "raw_function": raw_function,
        "row_index": row_index,
        "kind": kind,
        "reason": compact_json(detail),
        "detail": detail,
    })
}

fn normalized_cache_status(value: Option<&Value>) -> Option<&'static str> {
    match value {
        Some(Value::Bool(true)) => Some("hit"),
        Some(Value::Bool(false)) => Some("miss"),
        Some(Value::String(text)) => {
            match text.trim().to_ascii_lowercase().replace('-', "_").as_str() {
                "hit" | "cache_hit" | "cached" => Some("hit"),
                "miss" | "cache_miss" | "uncached" => Some("miss"),
                _ => None,
            }
        }
        Some(Value::Object(map)) => {
            for key in ["status", "state", "result", "cache_status"] {
                if let Some(status) = normalized_cache_status(map.get(key)) {
                    return Some(status);
                }
            }
            if let Some(Value::Bool(hit)) = map.get("hit") {
                return Some(if *hit { "hit" } else { "miss" });
            }
            None
        }
        _ => None,
    }
}

fn row_cache_status(result: &Value) -> Option<&'static str> {
    for key in ["cache", "cache_status", "cached"] {
        if let Some(status) = normalized_cache_status(result.get(key)) {
            return Some(status);
        }
    }
    if result.get("solver").and_then(Value::as_str) == Some("trust-cache")
        || result.get("kind").and_then(Value::as_str) == Some("cached")
    {
        return Some("hit");
    }
    if result
        .get("reason")
        .and_then(Value::as_str)
        .is_some_and(|reason| reason.to_ascii_lowercase().contains("verification cache"))
    {
        return Some("hit");
    }
    None
}

fn solver_suite_json(summary: &TransportSummary) -> Value {
    let solvers = summary
        .solvers
        .iter()
        .map(|(solver, totals)| {
            json!({
                "solver": solver,
                "obligations": totals.obligations,
                "time_ms": totals.time_ms,
                "outcomes": totals.outcomes,
            })
        })
        .collect::<Vec<_>>();
    let kinds = summary
        .kinds
        .iter()
        .map(|(kind, totals)| {
            json!({
                "kind": kind,
                "obligations": totals.obligations,
                "time_ms": totals.time_ms,
                "outcomes": totals.outcomes,
            })
        })
        .collect::<Vec<_>>();
    let outcome_summary = outcome_summary_from_counts(&summary.outcomes, summary.obligation_rows);
    let coverage_blocker_summary = coverage_blocker_summary(&summary.coverage_blockers);
    let all_unknown_routing =
        all_unknown_routing_report(&summary.outcomes, summary.obligation_rows);
    let compiler_self_verification = compiler_self_verification_report(
        &summary.verification_rows,
        &summary.coverage_blockers,
        &coverage_blocker_summary,
        &all_unknown_routing,
        &outcome_summary,
    );
    json!({
        "schema": SOLVER_SUITE_SCHEMA,
        "transport_authority": "Cargo compiler-message envelopes with Trust diagnostic tag",
        "stage2_toolchain_identity_verified": summary.stage2_toolchain_identity_verified,
        "stage2_endpoint_snapshot_identity_verified": summary.stage2_toolchain_identity_verified,
        "stage2_execution_identity_bound": summary.stage2_execution_identity_bound,
        "source_provenance_bound": summary.source_provenance_bound,
        "authenticated_cargo_transport": summary.authenticated_cargo_transport,
        "completed_targets": summary.completed_targets,
        "coverage_targets": summary.coverage_targets,
        "completed_target_identities": summary.completed_target_identities.values().cloned().collect::<Vec<_>>(),
        "coverage_target_identities": summary.coverage_target_identities.values().cloned().collect::<Vec<_>>(),
        "cargo_proof_inventories": summary.cargo_proof_inventories,
        "coverage": {
            "eligible": summary.coverage_eligible,
            "processed": summary.coverage_processed,
            "complete": summary.coverage_complete,
        },
        "transport_message_count": summary.messages,
        "function_result_count": summary.function_results,
        "functions": summary.functions,
        "crate_summaries": summary.crate_summaries,
        "obligation_rows": summary.obligation_rows,
        "reported_obligations": summary.reported_obligations,
        "outcomes": summary.outcomes,
        "outcome_summary": outcome_summary,
        "solvers": solvers,
        "obligation_kinds": kinds,
        "total_solver_time_ms": summary.total_solver_time_ms,
        "bundle_counts": {
            "function_result_bundles": summary.function_results,
            "crate_summary_bundles": summary.crate_summaries.len(),
            "obligation_rows": summary.obligation_rows,
            "reported_obligations": summary.reported_obligations,
        },
        "cache": {
            "source": "Cargo-authenticated compiler-message TRUST_JSON transport rows",
            "hit_obligations": summary.cache_hit_obligations,
            "hit_obligations_available": summary.obligation_rows > 0,
            "miss_obligations": if summary.cache_miss_available {
                Value::from(summary.cache_miss_obligations)
            } else {
                Value::Null
            },
            "miss_obligations_available": summary.cache_miss_available,
            "hit_functions": if summary.cache_function_status_available {
                Value::from(summary.cache_hit_functions)
            } else {
                Value::Null
            },
            "miss_functions": if summary.cache_function_status_available {
                Value::from(summary.cache_miss_functions)
            } else {
                Value::Null
            },
            "function_status_available": summary.cache_function_status_available,
        },
        "obligation_evidence": summary.obligation_evidence,
        "evidence_summary": {
            "rows_with_native_trust_ir": summary.obligation_evidence.iter().filter(|entry| entry.get("native_trust_ir").is_some_and(|value| !value.is_null())).count(),
            "rows_with_proof_evidence": summary.obligation_evidence.iter().filter(|entry| entry.get("proof_evidence").is_some_and(|value| !value.is_null())).count(),
            "rows_with_accepted_proof_binding": summary.verification_rows.iter().filter(|entry| entry.get("proof_binding").and_then(|binding| binding.get("accepted")).and_then(Value::as_bool) == Some(true)).count(),
            "proved_rows_missing_proof_binding": summary.verification_rows.iter().filter(|entry| entry.get("outcome_class").and_then(Value::as_str) == Some("proved") && entry.get("proof_binding").and_then(|binding| binding.get("accepted")).and_then(Value::as_bool) != Some(true)).count(),
        },
        "coverage_blockers": summary.coverage_blockers,
        "coverage_blocker_summary": coverage_blocker_summary,
        "all_unknown_routing": all_unknown_routing,
        "verification_rows": summary.verification_rows,
        "verification_row_summary": compiler_self_verification["summary"].clone(),
        "compiler_self_verification": compiler_self_verification,
        "per_suite_timing": solvers.iter().map(|solver| {
            json!({
                "suite": solver.get("solver").cloned().unwrap_or(Value::Null),
                "time_ms": solver.get("time_ms").cloned().unwrap_or(Value::Null),
                "obligations": solver.get("obligations").cloned().unwrap_or(Value::Null),
                "outcomes": solver.get("outcomes").cloned().unwrap_or(Value::Null),
                "source": "authenticated TRUST_JSON result.time_ms",
            })
        }).collect::<Vec<_>>(),
        "parse_errors": summary.parse_errors,
        "transport_inconsistencies": summary.inconsistencies,
    })
}

fn outcome_summary_from_counts(outcomes: &BTreeMap<String, u64>, obligation_rows: u64) -> Value {
    let failed = count_outcomes_by_class(outcomes, OutcomeClass::Failed);
    let incomplete_known = count_outcomes_by_class(outcomes, OutcomeClass::Incomplete);
    let unrecognized = count_outcomes_by_class(outcomes, OutcomeClass::Unrecognized);
    let incomplete = incomplete_known + unrecognized;
    json!({
        "total_rows": obligation_rows,
        "proved_rows": outcomes.get("proved").copied().unwrap_or(0),
        "failed_rows": failed,
        "incomplete_rows": incomplete,
        "known_incomplete_rows": incomplete_known,
        "unrecognized_rows": unrecognized,
        "complete": obligation_rows > 0 && failed == 0 && incomplete == 0,
        "outcomes": outcomes,
    })
}

fn count_outcomes_by_class(outcomes: &BTreeMap<String, u64>, class: OutcomeClass) -> u64 {
    outcomes
        .iter()
        .filter(|(outcome, _)| classify_outcome(outcome) == class)
        .map(|(_, count)| *count)
        .sum()
}

fn coverage_blocker_summary(blockers: &[Value]) -> Value {
    let mut by_kind: BTreeMap<String, u64> = BTreeMap::new();
    for blocker in blockers {
        let kind = blocker.get("kind").and_then(Value::as_str).unwrap_or("unknown").to_string();
        *by_kind.entry(kind).or_default() += 1;
    }
    json!({
        "schema": "trust.self-verify-harness.coverage-blocker-summary.v1",
        "blocker_count": blockers.len(),
        "by_kind": by_kind,
    })
}

fn all_unknown_routing_report(outcomes: &BTreeMap<String, u64>, obligation_rows: u64) -> Value {
    let unknown = outcomes.get("unknown").copied().unwrap_or(0);
    json!({
        "schema": ALL_UNKNOWN_ROUTING_SCHEMA,
        "detected": obligation_rows > 0 && unknown == obligation_rows,
        "obligation_rows": obligation_rows,
        "unknown_rows": unknown,
        "reason": if obligation_rows > 0 && unknown == obligation_rows {
            Value::String("all solver obligation rows ended as unknown".to_string())
        } else {
            Value::Null
        },
    })
}

fn compiler_self_verification_report(
    rows: &[Value],
    blockers: &[Value],
    blocker_summary: &Value,
    all_unknown_routing: &Value,
    outcome_summary: &Value,
) -> Value {
    let unsupported_rows = rows
        .iter()
        .filter(|row| row.get("supported").and_then(Value::as_bool) == Some(false))
        .count();
    let failure_rows =
        rows.iter().filter(|row| row.get("failed").and_then(Value::as_bool) == Some(true)).count();
    let proved_rows = rows
        .iter()
        .filter(|row| row.get("outcome_class").and_then(Value::as_str) == Some("proved"))
        .count();
    let rows_with_accepted_proof_binding = rows
        .iter()
        .filter(|row| {
            row.get("proof_binding")
                .and_then(|binding| binding.get("accepted"))
                .and_then(Value::as_bool)
                == Some(true)
        })
        .count();
    let proved_rows_missing_proof_binding = rows
        .iter()
        .filter(|row| {
            row.get("outcome_class").and_then(Value::as_str) == Some("proved")
                && row
                    .get("proof_binding")
                    .and_then(|binding| binding.get("accepted"))
                    .and_then(Value::as_bool)
                    != Some(true)
        })
        .count();
    json!({
        "schema": COMPILER_SELF_VERIFICATION_SCHEMA,
        "rows": rows,
        "summary": {
            "schema": VERIFICATION_ROW_SUMMARY_SCHEMA,
            "row_count": rows.len(),
            "proved_rows": proved_rows,
            "unsupported_rows": unsupported_rows,
            "failure_rows": failure_rows,
            "coverage_blocker_rows": blockers.len(),
            "rows_with_accepted_proof_binding": rows_with_accepted_proof_binding,
            "proved_rows_missing_proof_binding": proved_rows_missing_proof_binding,
            "complete_rows": outcome_summary.get("complete").and_then(Value::as_bool).unwrap_or(false)
                && blockers.is_empty()
                && rows.len() == proved_rows
                && proved_rows_missing_proof_binding == 0,
        },
        "coverage_blocker_summary": blocker_summary,
        "all_unknown_routing": all_unknown_routing,
    })
}

/// Public proof-inventory identity. The persisted Cargo inventory is an
/// observational projection and deliberately cannot recreate Targo's private
/// live execution identity (`compile_kind` and `unit_identity_sha256`). Keep
/// this projection distinct so report completeness is checked against exactly
/// the fields the report is authorized to carry, while live target envelopes
/// retain and validate the stronger execution identity separately.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct CargoProofUnitIdentity {
    package_id: String,
    package_name: String,
    target_name: String,
    target_kinds: Vec<String>,
    compile_target: String,
    compile_target_spec_sha256: Option<String>,
    proof_unit_index: u64,
    proof_unit_mode: String,
    proof_unit_role: String,
    semantics_sha256: String,
}

impl CargoProofUnitIdentity {
    fn from_live_target(target: &CargoTargetIdentity) -> Self {
        Self {
            package_id: target.package_id.clone(),
            package_name: target.package_name.clone(),
            target_name: target.target_name.clone(),
            target_kinds: target.target_kinds.clone(),
            compile_target: target.compile_target.clone(),
            compile_target_spec_sha256: target.compile_target_spec_sha256.clone(),
            proof_unit_index: target.proof_unit_index,
            proof_unit_mode: target.proof_unit_mode.clone(),
            proof_unit_role: target.proof_unit_role.clone(),
            semantics_sha256: target.semantics_sha256.clone(),
        }
    }

    fn from_report(
        unit: &trust_types::CargoProofUnitReport,
        semantics_sha256: &str,
    ) -> Result<Self, String> {
        let identity = Self {
            package_id: unit.package_id.clone(),
            package_name: unit.package_name.clone(),
            target_name: unit.target_name.clone(),
            target_kinds: unit.target_kinds.clone(),
            compile_target: unit.compile_target.clone(),
            compile_target_spec_sha256: unit.compile_target_spec_sha256.clone(),
            proof_unit_index: unit.proof_unit_index,
            proof_unit_mode: unit.proof_unit_mode.clone(),
            proof_unit_role: unit.proof_unit_role.clone(),
            semantics_sha256: semantics_sha256.to_string(),
        };
        for (field, value) in [
            ("package_id", identity.package_id.as_str()),
            ("package_name", identity.package_name.as_str()),
            ("target_name", identity.target_name.as_str()),
            ("compile_target", identity.compile_target.as_str()),
        ] {
            if value.is_empty() {
                return Err(format!("Cargo proof-unit identity omitted nonempty `{field}`"));
            }
        }
        if identity.target_kinds.is_empty()
            || identity.target_kinds.iter().any(|kind| kind.is_empty())
        {
            return Err("Cargo proof-unit identity contained no valid target kinds".to_string());
        }
        if identity.target_kinds.iter().collect::<BTreeSet<_>>().len()
            != identity.target_kinds.len()
        {
            return Err("Cargo proof-unit identity repeated a target kind".to_string());
        }
        if identity
            .compile_target_spec_sha256
            .as_deref()
            .is_some_and(|digest| !trust_types::digest::is_stable_sha256_hex(digest))
        {
            return Err("Cargo proof-unit identity contained a non-canonical target-spec SHA-256"
                .to_string());
        }
        if !matches!(
            identity.proof_unit_mode.as_str(),
            "build"
                | "test"
                | "check"
                | "check-test"
                | "doc"
                | "doctest"
                | "docscrape"
                | "run-custom-build"
        ) {
            return Err(format!(
                "Cargo proof-unit identity contained unsupported compile mode {:?}",
                identity.proof_unit_mode
            ));
        }
        if !matches!(identity.proof_unit_role.as_str(), "primary" | "test-execution" | "dependency")
        {
            return Err(format!(
                "Cargo proof-unit identity contained unsupported role {:?}",
                identity.proof_unit_role
            ));
        }
        if !trust_types::digest::is_stable_sha256_hex(&identity.semantics_sha256) {
            return Err(
                "Cargo proof-unit identity contained a non-canonical semantic descriptor SHA-256"
                    .to_string(),
            );
        }
        Ok(identity)
    }

    fn report_label(&self) -> String {
        format!(
            "cargo-proof-unit(package_id={:?},package={:?},kind={:?},target={:?},compile_target={:?},compile_target_spec_sha256={:?},proof_unit_index={},proof_unit_mode={:?},proof_unit_role={:?},semantics_sha256={:?})",
            self.package_id,
            self.package_name,
            self.target_kinds,
            self.target_name,
            self.compile_target,
            self.compile_target_spec_sha256,
            self.proof_unit_index,
            self.proof_unit_mode,
            self.proof_unit_role,
            self.semantics_sha256,
        )
    }
}

fn cargo_proof_partition_identities(
    partitions: &trust_types::CargoProofUnitPartitions,
    context: &str,
    errors: &mut Vec<String>,
) -> BTreeMap<String, CargoProofUnitIdentity> {
    let mut identities = BTreeMap::new();
    let mut unit_indices = BTreeMap::new();
    let roles = [
        ("primary_roots", "primary", &partitions.primary_roots),
        ("test_execution_units", "test-execution", &partitions.test_execution_units),
        ("dependency_units", "dependency", &partitions.dependency_units),
    ];

    for (field, expected_role, units) in roles {
        if units.windows(2).any(|pair| {
            pair[0]
                .proof_unit_index
                .cmp(&pair[1].proof_unit_index)
                .then_with(|| pair[0].cmp(&pair[1]))
                .is_gt()
        }) {
            errors.push(format!("{context} `{field}` was not in canonical Cargo Unit-index order"));
        }
        for (position, unit) in units.iter().enumerate() {
            if unit.proof_unit_role != expected_role {
                errors.push(format!(
                    "{context} `{field}` entry {position} carried role {:?} instead of {expected_role:?}",
                    unit.proof_unit_role
                ));
            }
            if unit.exclusion_reason.is_some() {
                errors.push(format!(
                    "{context} `{field}` entry {position} attached an exclusion reason to a proof-frontier Unit"
                ));
            }
            let semantics_sha256 = match unit.semantics_sha256.as_deref() {
                Some(digest) if trust_types::digest::is_stable_sha256_hex(digest) => digest,
                _ => {
                    errors.push(format!(
                        "{context} `{field}` entry {position} omitted its canonical semantic descriptor digest"
                    ));
                    ""
                }
            };
            match unit.semantics.as_ref() {
                Some(semantics) => {
                    if let Err(error) = validate_cargo_unit_semantics(semantics, context) {
                        errors.push(format!(
                            "{context} `{field}` entry {position} had invalid Unit semantics: {error}"
                        ));
                    }
                    match cargo_unit_semantics_sha256(semantics) {
                        Ok(actual) if actual == semantics_sha256 => {}
                        Ok(_) => errors.push(format!(
                            "{context} `{field}` entry {position} semantic descriptor did not match its digest"
                        )),
                        Err(error) => errors.push(format!(
                            "{context} `{field}` entry {position} semantic descriptor could not be hashed: {error}"
                        )),
                    }
                }
                None => errors.push(format!(
                    "{context} `{field}` entry {position} omitted its closed Unit semantic descriptor"
                )),
            }
            let target = match CargoProofUnitIdentity::from_report(unit, semantics_sha256) {
                Ok(target) => target,
                Err(error) => {
                    errors.push(format!(
                        "{context} `{field}` entry {position} had an invalid Cargo proof-unit identity: {error}"
                    ));
                    continue;
                }
            };
            let label = target.report_label();
            if let Some(previous) = unit_indices.insert(target.proof_unit_index, label.clone()) {
                errors.push(format!(
                    "{context} reused Cargo Unit index {} for `{previous}` and `{label}`",
                    target.proof_unit_index
                ));
            }
            if identities.insert(label.clone(), target).is_some() {
                errors.push(format!("{context} repeated Cargo proof unit `{label}`"));
            }
        }
    }
    identities
}

/// Validate the serialized observational inventory independently of the live
/// parser. This second check is intentional: aggregate and persisted reports
/// must not become complete merely because they retain some successful rows
/// while dropping a declared Cargo Unit, dependency scope, or exclusion.
fn cargo_proof_inventory_completeness_errors(solver_suite: &Value) -> Vec<String> {
    let mut errors = Vec::new();
    let Some(values) = solver_suite.get("cargo_proof_inventories").and_then(Value::as_array) else {
        return vec![
            "complete proof requires canonical Cargo proof inventory evidence".to_string(),
        ];
    };
    if values.is_empty() {
        return vec![
            "complete proof requires at least one canonical Cargo proof inventory".to_string(),
        ];
    }

    let mut inventory_completed = BTreeMap::new();
    let mut inventory_covered = BTreeMap::new();
    for (index, value) in values.iter().enumerate() {
        let context = format!("Cargo proof inventory {index}");
        let inventory =
            match serde_json::from_value::<trust_types::CargoProofInventoryReport>(value.clone()) {
                Ok(inventory) => inventory,
                Err(error) => {
                    errors.push(format!("{context} was invalid: {error}"));
                    continue;
                }
            };
        match serde_json::to_value(&inventory) {
            Ok(canonical) if canonical == *value => {}
            Ok(_) => errors
                .push(format!("{context} was not the canonical serialized inventory projection")),
            Err(error) => errors.push(format!("{context} could not be canonicalized: {error}")),
        }
        if inventory.schema != trust_types::CARGO_PROOF_INVENTORY_REPORT_SCHEMA_V2 {
            errors.push(format!("{context} schema {:?} was unsupported", inventory.schema));
        }
        if !inventory.include_dependencies {
            errors.push(format!(
                "{context} excluded dependency Units; complete self-verification requires include_dependencies=true"
            ));
        }
        if !inventory.excluded_active_units.is_empty() {
            errors.push(format!(
                "{context} contained {} excluded active Cargo Unit(s)",
                inventory.excluded_active_units.len()
            ));
        }

        let declared = cargo_proof_partition_identities(
            &inventory.declared,
            &format!("{context} declared frontier"),
            &mut errors,
        );
        let completed = cargo_proof_partition_identities(
            &inventory.completed,
            &format!("{context} completed frontier"),
            &mut errors,
        );
        let covered = cargo_proof_partition_identities(
            &inventory.covered,
            &format!("{context} covered frontier"),
            &mut errors,
        );
        if declared.is_empty() {
            errors.push(format!("{context} declared an empty proof frontier"));
        }
        if inventory.declared != inventory.completed {
            errors.push(format!(
                "{context} declared and completed Cargo Unit frontiers were not exact matches"
            ));
        }
        if inventory.declared != inventory.covered {
            errors.push(format!(
                "{context} declared and covered Cargo Unit frontiers were not exact matches"
            ));
        }
        inventory_completed.extend(completed);
        inventory_covered.extend(covered);
    }

    let mut target_errors = Vec::new();
    let completed_targets =
        report_target_inventory(solver_suite, "completed_target_identities", &mut target_errors);
    let covered_targets =
        report_target_inventory(solver_suite, "coverage_target_identities", &mut target_errors);
    errors.extend(target_errors);
    let completed_proof_units = completed_targets
        .values()
        .map(CargoProofUnitIdentity::from_live_target)
        .map(|identity| (identity.report_label(), identity))
        .collect::<BTreeMap<_, _>>();
    let covered_proof_units = covered_targets
        .values()
        .map(CargoProofUnitIdentity::from_live_target)
        .map(|identity| (identity.report_label(), identity))
        .collect::<BTreeMap<_, _>>();
    if inventory_completed != completed_proof_units {
        errors.push(
            "canonical Cargo proof inventories did not exactly match completed target identities"
                .to_string(),
        );
    }
    if inventory_covered != covered_proof_units {
        errors.push(
            "canonical Cargo proof inventories did not exactly match covered target identities"
                .to_string(),
        );
    }
    errors
}

fn evaluate_proof(
    stage_status: &str,
    returncode: Option<i32>,
    process_timed_out: bool,
    solver_suite: &Value,
) -> Value {
    let mut reasons = Vec::new();
    let outcomes = solver_suite.get("outcomes").and_then(Value::as_object);
    let outcome_count = |name: &str| -> u64 {
        outcomes.and_then(|outcomes| outcomes.get(name)).and_then(Value::as_u64).unwrap_or(0)
    };
    let transport_message_count =
        solver_suite.get("transport_message_count").and_then(Value::as_u64).unwrap_or(0);
    let obligation_rows = solver_suite.get("obligation_rows").and_then(Value::as_u64).unwrap_or(0);

    if solver_suite.get("stage2_toolchain_identity_verified").and_then(Value::as_bool) != Some(true)
    {
        reasons.push(
            "the stage runner lacked a captured and rechecked repository stage2 Targo/trustc/trustdoc/trustd identity and live daemon protocol smoke"
                .to_string(),
        );
    }
    if solver_suite.get("stage2_execution_identity_bound").and_then(Value::as_bool) != Some(true) {
        reasons.push(
            "stage2 endpoint snapshots do not bind the exact executable bytes used by every compiler or rustdoc launch; external execution isolation or a platform execution-handle design is required"
                .to_string(),
        );
    }
    if solver_suite.get("source_provenance_bound").and_then(Value::as_bool) != Some(true) {
        reasons.push(
            "the source tree, index, submodules, and dependency closure are not bound to the executed toolchain; Targo/trustc/trustdoc/trustd version agreement is diagnostic consistency, not source provenance"
                .to_string(),
        );
    }
    if solver_suite.get("authenticated_cargo_transport").and_then(Value::as_bool) != Some(true) {
        reasons.push(
            "no authenticated Cargo compiler-message transport was established; raw stdout/stderr is never proof authority"
                .to_string(),
        );
    }
    if solver_suite.get("completed_targets").and_then(Value::as_array).is_none_or(Vec::is_empty) {
        reasons.push("no authenticated terminal summary for the selected Cargo target".to_string());
    }
    reasons.extend(cargo_proof_inventory_completeness_errors(solver_suite));
    if solver_suite
        .get("coverage")
        .and_then(|coverage| coverage.get("complete"))
        .and_then(Value::as_bool)
        != Some(true)
    {
        reasons.push(
            "authenticated whole-target coverage was absent or incomplete (processed != eligible)"
                .to_string(),
        );
    }

    if process_timed_out {
        reasons.push("process timed out before verification evidence was complete".to_string());
    }
    if !matches!(returncode, None | Some(0)) {
        reasons.push(format!(
            "verification command returned nonzero status {}",
            returncode.unwrap_or(1)
        ));
    }
    if transport_message_count == 0 {
        reasons.push("no authenticated compiler TRUST_JSON transport was observed".to_string());
    }
    if obligation_rows == 0 {
        reasons.push("no per-obligation solver evidence rows were observed".to_string());
    }
    let failed_count = count_outcomes_value(solver_suite, FAILED_OUTCOMES);
    if failed_count > 0 {
        reasons.push(format!("{failed_count} solver obligation(s) failed"));
    }
    for outcome in INCOMPLETE_OUTCOMES {
        let count = outcome_count(outcome);
        if count > 0 {
            if *outcome == "timed_out" {
                reasons.push(format!("{count} solver obligation(s) timed out"));
            } else {
                reasons.push(format!("{count} solver obligation(s) ended as {outcome}"));
            }
        }
    }
    for (outcome, count) in unrecognized_outcomes_value(solver_suite) {
        reasons.push(format!(
            "{count} solver obligation(s) reported unrecognized outcome `{outcome}`"
        ));
    }
    let all_unknown_routing =
        solver_suite.get("all_unknown_routing").cloned().unwrap_or(Value::Null);
    if all_unknown_routing.get("detected").and_then(Value::as_bool).unwrap_or(false) {
        reasons
            .push("all_unknown_routing: all solver obligation rows ended as unknown".to_string());
    }
    let coverage_blockers = solver_suite
        .get("coverage_blockers")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default();
    if !coverage_blockers.is_empty() {
        reasons.push(format!(
            "{} structured coverage blocker(s) prevent proof completeness",
            coverage_blockers.len()
        ));
    }
    if let Some(summary) = solver_suite.get("verification_row_summary") {
        if summary.get("unsupported_rows").and_then(Value::as_u64).unwrap_or(0) > 0 {
            reasons.push(format!(
                "{} compiler self-verification row(s) unsupported",
                summary.get("unsupported_rows").and_then(Value::as_u64).unwrap_or(0)
            ));
        }
        if summary.get("failure_rows").and_then(Value::as_u64).unwrap_or(0) > 0 && failed_count == 0
        {
            reasons.push(format!(
                "{} compiler self-verification row(s) failed",
                summary.get("failure_rows").and_then(Value::as_u64).unwrap_or(0)
            ));
        }
        if summary.get("proved_rows_missing_proof_binding").and_then(Value::as_u64).unwrap_or(0) > 0
        {
            reasons.push(format!(
                "{} proved compiler self-verification row(s) lacked proof artifact/transcript binding",
                summary
                    .get("proved_rows_missing_proof_binding")
                    .and_then(Value::as_u64)
                    .unwrap_or(0)
            ));
        }
    }
    if solver_suite
        .get("parse_errors")
        .and_then(Value::as_array)
        .is_some_and(|items| !items.is_empty())
    {
        reasons.push(
            "canonical Cargo compiler evidence could not be parsed or authenticated".to_string(),
        );
    }
    if solver_suite
        .get("transport_inconsistencies")
        .and_then(Value::as_array)
        .is_some_and(|items| !items.is_empty())
    {
        reasons.push("compiler transport contained inconsistent obligation accounting".to_string());
    }

    let status = if process_timed_out || reasons.iter().any(|reason| reason.contains("timed out")) {
        "incomplete"
    } else if failed_count > 0 || !matches!(returncode, None | Some(0)) {
        "failed"
    } else if !reasons.is_empty() {
        "incomplete"
    } else if stage_status == "passed" {
        "complete"
    } else {
        "incomplete"
    };
    json!({
        "status": status,
        "complete": status == "complete",
        "timeout_is_incomplete_proof": true,
        "obligation_summary": obligation_outcome_summary(solver_suite),
        "coverage_blocker_summary": solver_suite.get("coverage_blocker_summary").cloned().unwrap_or(Value::Null),
        "coverage_blockers": coverage_blockers,
        "all_unknown_routing": all_unknown_routing,
        "reasons": reasons,
    })
}

fn count_outcomes_value(solver_suite: &Value, names: &[&str]) -> u64 {
    names
        .iter()
        .map(|name| {
            solver_suite
                .get("outcomes")
                .and_then(|outcomes| outcomes.get(*name))
                .and_then(Value::as_u64)
                .unwrap_or(0)
        })
        .sum()
}

fn unrecognized_outcomes_value(solver_suite: &Value) -> BTreeMap<String, u64> {
    let mut unrecognized = BTreeMap::new();
    let Some(outcomes) = solver_suite.get("outcomes").and_then(Value::as_object) else {
        return unrecognized;
    };
    for (outcome, count) in outcomes {
        if classify_outcome(outcome) == OutcomeClass::Unrecognized {
            unrecognized.insert(outcome.clone(), count.as_u64().unwrap_or(0));
        }
    }
    unrecognized
}

fn obligation_outcome_summary(solver_suite: &Value) -> Value {
    let obligation_rows = solver_suite.get("obligation_rows").and_then(Value::as_u64).unwrap_or(0);
    let mut outcomes = BTreeMap::new();
    if let Some(map) = solver_suite.get("outcomes").and_then(Value::as_object) {
        for (key, value) in map {
            if let Some(count) = value.as_u64() {
                outcomes.insert(key.clone(), count);
            }
        }
    }
    outcome_summary_from_counts(&outcomes, obligation_rows)
}

fn report_status_from_stages(stages: &[Value]) -> String {
    if stages.iter().any(|stage| stage["status"] == "timed_out") {
        "timed_out".to_string()
    } else if stages.iter().any(|stage| stage["status"] == "failed") {
        "failed".to_string()
    } else if stages.iter().any(|stage| stage["status"] == "incomplete") {
        "incomplete".to_string()
    } else if stages.iter().all(|stage| stage["status"] == "passed") {
        "passed".to_string()
    } else if stages.iter().all(|stage| stage["status"] == "planned") {
        "planned".to_string()
    } else {
        "incomplete".to_string()
    }
}

fn build_report(
    options: &Options,
    report_dir: &Path,
    plan: &StagePlan,
    stages: Vec<Value>,
    status: &str,
) -> Value {
    let aggregate_solver_suite = aggregate_report_solver_suite(&stages);
    let proof = if status == "planned" {
        let empty_suite = solver_suite_json(&TransportSummary::default());
        json!({
            "status": "not_run",
            "complete": false,
            "timeout_is_incomplete_proof": true,
            "obligation_summary": obligation_outcome_summary(&empty_suite),
            "reasons": ["dry run only; no compiler or solver evidence was collected"],
        })
    } else {
        let returncode = stages
            .iter()
            .find_map(|stage| stage.get("returncode").and_then(Value::as_i64))
            .map(|code| code as i32)
            .or_else(|| if status == "passed" { Some(0) } else { None });
        let timed_out = stages
            .iter()
            .any(|stage| stage.get("process_timed_out").and_then(Value::as_bool) == Some(true));
        evaluate_proof(status, returncode, timed_out, &aggregate_solver_suite)
    };
    let mut performance =
        performance_summary(&stages, aggregate_solver_suite.clone(), status, &proof);
    let perf_budget = evaluate_perf_budget(options, &performance);
    performance["budget"] = perf_budget.clone();
    if let Some(compare_report) = &options.compare_report {
        performance["comparison"] = json!({
            "previous_report": relative_path(compare_report, &options.repo_root),
            "mode": "report",
            "available": compare_report.is_file(),
        });
    }
    let effective_status = if perf_budget["failed"].as_bool().unwrap_or(false)
        || proof.get("status").and_then(Value::as_str) == Some("failed")
    {
        "failed"
    } else {
        status
    };
    json!({
        "schema": SCHEMA,
        "issue": "#1149",
        "run_id": options.run_id,
        "created_at": now_string(),
        "status": effective_status,
        "repo_root": options.repo_root.display().to_string(),
        "report_dir": relative_path(report_dir, &options.repo_root),
        "git": git_info(),
        "host": {
            "platform": env::consts::OS,
            "machine": env::consts::ARCH,
            "rust_cli": "targo-trust",
        },
        "invocation": {
            "argv": options.raw_argv,
            "command_line": command_line(&["targo", "trust", "verify", "self"].iter().map(|arg| arg.to_string()).chain(options.raw_argv.iter().cloned()).collect::<Vec<_>>()),
        },
        "configuration": {
            "target": options.target,
            "evidence_manifest": options.evidence_manifest.display().to_string(),
            "timeout_sec": options.timeout_sec,
            "stage_label": plan.label,
            "level": options.level,
            "full_verifier": options.full_verifier,
            "worker_threads": if options.full_verifier {
                plan.env_policy.get("worker_threads").cloned().unwrap_or(Value::Null)
            } else {
                Value::Null
            },
            "offline": options.offline,
            "dry_run": options.dry_run,
            "dry_run_identity_probes_executed": options.dry_run && plan.stage2_toolchain.is_some(),
            "perf_budget_mode": options.perf_budget_mode.as_str(),
            "perf_budget_thresholds": perf_budget.get("thresholds").cloned().unwrap_or(Value::Null),
            "compare_report": options.compare_report.as_ref().map(|path| Value::String(relative_path(path, &options.repo_root))).unwrap_or(Value::Null),
        },
        "evidence_controls": {
            "stage2_endpoint_snapshot_identity_required": true,
            "stage2_before_open_after_file_identity_required": true,
            "stage2_tool_verbose_identities_agree_required": true,
            "version_labels_are_source_provenance": false,
            "source_provenance_bound": false,
            "source_cleanliness_bound": false,
            "stage2_plain_bin_directory_required": true,
            "stage2_execution_identity_bound": false,
            "external_execution_isolation_required": true,
            "compiler_trust_json_required": true,
            "exact_cargo_target_identity_required": true,
            "exact_cargo_proof_inventory_required": true,
            "cargo_proof_inventory_include_dependencies_required": true,
            "excluded_active_cargo_units_complete_proof": false,
            "per_obligation_rows_required": true,
            "unknown_outcomes_complete_proof": false,
            "timeout_outcomes_complete_proof": false,
            "unrecognized_outcomes_complete_proof": false,
            "no_verification_outcomes_complete_proof": false,
            "bounded_timeout_sec": if plan.timeout_sec > 0.0 { Value::from(plan.timeout_sec) } else { Value::Null },
            "performance_budget_mode": options.perf_budget_mode.as_str(),
            "performance_budget_gate_status": perf_budget.get("gate_status").cloned().unwrap_or(Value::Null),
            "fail_closed_on_unsupported_perf_counters": perf_budget.get("fail_closed_on_unsupported_counters").cloned().unwrap_or(Value::Null),
            "coverage_blockers_complete_proof": false,
            "row_level_proof_artifact_or_transcript_binding_required": true,
            "all_unknown_routing_complete_proof": false,
            "fail_closed_on_all_unknown_routing": true,
        },
        "toolchain": recorded_toolchains(
            &options.repo_root,
            &plan.env,
            plan.stage2_toolchain.as_ref(),
        ),
        "verification_scope": verification_scope(plan),
        "composition": composition_metadata(
            &options.target,
            &options.evidence_manifest,
            &plan.label,
        ),
        "stage2_bootstrap_semantics": stage2_bootstrap_semantics(plan),
        "stages": stages,
        "solver_suite": aggregate_solver_suite,
        "compiler_self_verification": aggregate_solver_suite.get("compiler_self_verification").cloned().unwrap_or(Value::Null),
        "proof": proof,
        "performance": performance,
    })
}

fn aggregate_report_solver_suite(stages: &[Value]) -> Value {
    let mut summary = TransportSummary::default();
    let mut suite_count = 0_usize;
    let mut every_suite_toolchain_verified = true;
    let mut every_suite_execution_identity_bound = true;
    let mut every_suite_source_provenance_bound = true;
    let mut every_suite_authenticated = true;
    let mut every_suite_coverage_complete = true;
    for (stage_index, stage) in stages.iter().enumerate() {
        let Some(suite) = stage.get("solver_suite") else {
            continue;
        };
        suite_count += 1;
        every_suite_toolchain_verified &=
            suite.get("stage2_toolchain_identity_verified").and_then(Value::as_bool) == Some(true);
        every_suite_execution_identity_bound &=
            suite.get("stage2_execution_identity_bound").and_then(Value::as_bool) == Some(true);
        every_suite_source_provenance_bound &=
            suite.get("source_provenance_bound").and_then(Value::as_bool) == Some(true);
        every_suite_authenticated &=
            suite.get("authenticated_cargo_transport").and_then(Value::as_bool) == Some(true);
        every_suite_coverage_complete &= suite
            .get("coverage")
            .and_then(|coverage| coverage.get("complete"))
            .and_then(Value::as_bool)
            == Some(true);
        summary.coverage_eligible = summary.coverage_eligible.saturating_add(
            suite
                .get("coverage")
                .and_then(|coverage| coverage.get("eligible"))
                .and_then(Value::as_u64)
                .unwrap_or(0),
        );
        summary.coverage_processed = summary.coverage_processed.saturating_add(
            suite
                .get("coverage")
                .and_then(|coverage| coverage.get("processed"))
                .and_then(Value::as_u64)
                .unwrap_or(0),
        );
        extend_strings(&mut summary.completed_targets, suite.get("completed_targets"));
        extend_strings(&mut summary.coverage_targets, suite.get("coverage_targets"));
        extend_target_identities(
            &mut summary.completed_target_identities,
            suite.get("completed_target_identities"),
            &mut summary.inconsistencies,
            "completed",
        );
        extend_target_identities(
            &mut summary.coverage_target_identities,
            suite.get("coverage_target_identities"),
            &mut summary.inconsistencies,
            "coverage",
        );
        match suite.get("cargo_proof_inventories").and_then(Value::as_array) {
            Some(inventories) => {
                summary.cargo_proof_inventories.extend(inventories.iter().cloned());
                if stage.get("status").and_then(Value::as_str) != Some("planned")
                    && inventories.len() != 1
                {
                    summary.inconsistencies.push(format!(
                        "stage {stage_index} carried {} canonical Cargo proof inventories; exactly one is required per executed stage",
                        inventories.len()
                    ));
                }
            }
            None if stage.get("status").and_then(Value::as_str) != Some("planned") => summary
                .inconsistencies
                .push(format!("stage {stage_index} omitted its canonical Cargo proof inventory")),
            None => {}
        }
        summary.messages +=
            suite.get("transport_message_count").and_then(Value::as_u64).unwrap_or(0) as usize;
        summary.function_results +=
            suite.get("function_result_count").and_then(Value::as_u64).unwrap_or(0) as usize;
        summary.obligation_rows +=
            suite.get("obligation_rows").and_then(Value::as_u64).unwrap_or(0);
        summary.reported_obligations +=
            suite.get("reported_obligations").and_then(Value::as_u64).unwrap_or(0);
        summary.total_solver_time_ms +=
            suite.get("total_solver_time_ms").and_then(Value::as_u64).unwrap_or(0);
        if let Some(functions) = suite.get("functions").and_then(Value::as_array) {
            summary
                .functions
                .extend(functions.iter().filter_map(Value::as_str).map(str::to_string));
        }
        if let Some(crate_summaries) = suite.get("crate_summaries").and_then(Value::as_array) {
            summary.crate_summaries.extend(crate_summaries.iter().cloned());
        }
        merge_count_map(&mut summary.outcomes, suite.get("outcomes"));
        merge_totals(&mut summary.solvers, suite.get("solvers"), "solver");
        merge_totals(&mut summary.kinds, suite.get("obligation_kinds"), "kind");
        if let Some(cache) = suite.get("cache") {
            summary.cache_hit_obligations +=
                cache.get("hit_obligations").and_then(Value::as_u64).unwrap_or(0);
            if let Some(miss) = cache.get("miss_obligations").and_then(Value::as_u64) {
                summary.cache_miss_available = true;
                summary.cache_miss_obligations += miss;
            }
            if cache.get("function_status_available").and_then(Value::as_bool).unwrap_or(false) {
                summary.cache_function_status_available = true;
                summary.cache_hit_functions +=
                    cache.get("hit_functions").and_then(Value::as_u64).unwrap_or(0);
                summary.cache_miss_functions +=
                    cache.get("miss_functions").and_then(Value::as_u64).unwrap_or(0);
            }
        }
        extend_array(&mut summary.obligation_evidence, suite.get("obligation_evidence"));
        extend_array(&mut summary.coverage_blockers, suite.get("coverage_blockers"));
        extend_array(&mut summary.verification_rows, suite.get("verification_rows"));
        extend_strings(&mut summary.parse_errors, suite.get("parse_errors"));
        extend_strings(&mut summary.inconsistencies, suite.get("transport_inconsistencies"));
    }
    summary.stage2_toolchain_identity_verified = suite_count > 0 && every_suite_toolchain_verified;
    summary.stage2_execution_identity_bound =
        suite_count > 0 && every_suite_execution_identity_bound;
    summary.source_provenance_bound = suite_count > 0 && every_suite_source_provenance_bound;
    summary.authenticated_cargo_transport = suite_count > 0 && every_suite_authenticated;
    summary.coverage_complete = suite_count > 0 && every_suite_coverage_complete;
    summary.completed_targets.sort();
    summary.completed_targets.dedup();
    summary.coverage_targets.sort();
    summary.coverage_targets.dedup();
    solver_suite_json(&summary)
}

fn merge_count_map(target: &mut BTreeMap<String, u64>, source: Option<&Value>) {
    if let Some(map) = source.and_then(Value::as_object) {
        for (key, value) in map {
            *target.entry(key.clone()).or_default() += value.as_u64().unwrap_or(0);
        }
    }
}

fn merge_totals(
    target: &mut BTreeMap<String, SolverTotals>,
    source: Option<&Value>,
    key_name: &str,
) {
    let Some(items) = source.and_then(Value::as_array) else {
        return;
    };
    for item in items {
        let Some(name) = item.get(key_name).and_then(Value::as_str) else {
            continue;
        };
        let entry = target.entry(name.to_string()).or_default();
        entry.obligations += item.get("obligations").and_then(Value::as_u64).unwrap_or(0);
        entry.time_ms += item.get("time_ms").and_then(Value::as_u64).unwrap_or(0);
        if let Some(outcomes) = item.get("outcomes").and_then(Value::as_object) {
            for (outcome, count) in outcomes {
                *entry.outcomes.entry(outcome.clone()).or_default() += count.as_u64().unwrap_or(0);
            }
        }
    }
}

fn extend_array(target: &mut Vec<Value>, source: Option<&Value>) {
    if let Some(items) = source.and_then(Value::as_array) {
        target.extend(items.iter().cloned());
    }
}

fn extend_strings(target: &mut Vec<String>, source: Option<&Value>) {
    if let Some(items) = source.and_then(Value::as_array) {
        target.extend(items.iter().filter_map(Value::as_str).map(str::to_string));
    }
}

fn extend_target_identities(
    target: &mut BTreeMap<String, Value>,
    source: Option<&Value>,
    inconsistencies: &mut Vec<String>,
    inventory: &str,
) {
    let Some(items) = source.and_then(Value::as_array) else {
        if source.is_some() {
            inconsistencies.push(format!(
                "authenticated {inventory} target identity inventory was not an array"
            ));
        }
        return;
    };
    for item in items {
        match cargo_target_identity_from_json(item) {
            Ok(identity) => {
                let label = identity.report_label();
                target.entry(label).or_insert_with(|| item.clone());
            }
            Err(error) => inconsistencies
                .push(format!("authenticated {inventory} target identity was invalid: {error}")),
        }
    }
}

fn performance_summary(
    stages: &[Value],
    solver_suite: Value,
    status: &str,
    proof: &Value,
) -> Value {
    let wall_time_sec = stages
        .iter()
        .filter_map(|stage| stage.get("duration_sec").and_then(Value::as_f64))
        .sum::<f64>();
    let measurement_state = match status {
        "planned" => "planned",
        "passed" => "complete",
        "timed_out" => "partial_timed_out",
        "failed" => "failed",
        _ => "partial",
    };
    json!({
        "schema": "trust.self-verify-harness.performance.v1",
        "measurement_state": measurement_state,
        "wall_time_sec": round3(wall_time_sec),
        "reported_solver_time_ms": solver_suite.get("total_solver_time_ms").cloned().unwrap_or(Value::from(0)),
        "obligation_rows": solver_suite.get("obligation_rows").cloned().unwrap_or(Value::from(0)),
        "cache_miss_obligations": solver_suite
            .get("cache")
            .and_then(|cache| cache.get("miss_obligations"))
            .cloned()
            .unwrap_or(Value::Null),
        "proof_complete": proof.get("complete").and_then(Value::as_bool).unwrap_or(false),
    })
}

fn evaluate_perf_budget(options: &Options, performance: &Value) -> Value {
    let thresholds = json!({
        "max_verification_wall_time_sec": options.max_verification_wall_time_sec,
        "max_reported_solver_time_ms": options.max_reported_solver_time_ms,
        "max_obligation_rows": options.max_obligation_rows,
        "max_cache_miss_obligations": options.max_cache_miss_obligations,
    });
    let mut violations = Vec::new();
    push_budget_violation(
        &mut violations,
        "max_verification_wall_time_sec",
        performance.get("wall_time_sec").and_then(Value::as_f64),
        options.max_verification_wall_time_sec,
    );
    push_budget_violation_u64(
        &mut violations,
        "max_reported_solver_time_ms",
        performance.get("reported_solver_time_ms").and_then(Value::as_u64),
        options.max_reported_solver_time_ms,
    );
    push_budget_violation_u64(
        &mut violations,
        "max_obligation_rows",
        performance.get("obligation_rows").and_then(Value::as_u64),
        options.max_obligation_rows,
    );
    push_budget_violation_u64(
        &mut violations,
        "max_cache_miss_obligations",
        performance.get("cache_miss_obligations").and_then(Value::as_u64),
        options.max_cache_miss_obligations,
    );
    if options.perf_budget_mode == PerfBudgetMode::Enforce {
        push_missing_budget_counter(
            &mut violations,
            "max_cache_miss_obligations",
            performance.get("cache_miss_obligations").and_then(Value::as_u64).is_some(),
            options.max_cache_miss_obligations.is_some(),
        );
    }
    let failed = options.perf_budget_mode == PerfBudgetMode::Enforce && !violations.is_empty();
    json!({
        "schema": "trust.self-verify-harness.perf-budget.v1",
        "mode": options.perf_budget_mode.as_str(),
        "thresholds": thresholds,
        "violations": violations,
        "failed": failed,
        "gate_status": if failed { "failed" } else if violations.is_empty() { "passed" } else { "reported" },
        "fail_closed_on_unsupported_counters": options.perf_budget_mode == PerfBudgetMode::Enforce,
    })
}

fn push_budget_violation(
    violations: &mut Vec<Value>,
    name: &str,
    actual: Option<f64>,
    max_allowed: Option<f64>,
) {
    if let (Some(actual), Some(max_allowed)) = (actual, max_allowed) {
        if actual > max_allowed {
            violations.push(json!({
                "metric": name,
                "actual": actual,
                "max_allowed": max_allowed,
            }));
        }
    }
}

fn push_budget_violation_u64(
    violations: &mut Vec<Value>,
    name: &str,
    actual: Option<u64>,
    max_allowed: Option<u64>,
) {
    if let (Some(actual), Some(max_allowed)) = (actual, max_allowed) {
        if actual > max_allowed {
            violations.push(json!({
                "metric": name,
                "actual": actual,
                "max_allowed": max_allowed,
            }));
        }
    }
}

fn push_missing_budget_counter(
    violations: &mut Vec<Value>,
    name: &str,
    actual_available: bool,
    threshold_requested: bool,
) {
    if threshold_requested && !actual_available {
        violations.push(json!({
            "metric": name,
            "reason": "counter unavailable",
        }));
    }
}

fn exit_code(report: &Value) -> u8 {
    match report.get("status").and_then(Value::as_str) {
        Some("planned") => 0,
        Some("passed") if report["proof"]["complete"].as_bool() == Some(true) => 0,
        Some("timed_out") => 124,
        Some("failed") => report
            .get("stages")
            .and_then(Value::as_array)
            .and_then(|stages| {
                stages.iter().find_map(|stage| stage.get("returncode").and_then(Value::as_i64))
            })
            .map(|code| if code == 0 { 1 } else { code.clamp(1, 255) as u8 })
            .unwrap_or(1),
        _ => 1,
    }
}

type ReportRowIdentity = (String, String, u64, Option<String>, u64);

fn report_target_inventory(
    suite: &Value,
    field: &str,
    errors: &mut Vec<String>,
) -> BTreeMap<String, CargoTargetIdentity> {
    let Some(values) = suite.get(field).and_then(Value::as_array) else {
        errors.push(format!("complete proof requires `{field}` as an exact identity array"));
        return BTreeMap::new();
    };
    let mut identities = BTreeMap::new();
    let mut unit_indices = BTreeMap::new();
    for (index, value) in values.iter().enumerate() {
        match cargo_target_identity_from_json(value) {
            Ok(identity) => {
                let label = identity.report_label();
                if identities.insert(label.clone(), identity.clone()).is_some() {
                    errors.push(format!(
                        "complete proof `{field}` repeated Cargo target identity `{label}`"
                    ));
                }
                if let Some(previous) =
                    unit_indices.insert(identity.proof_unit_index, label.clone())
                {
                    if previous != label {
                        errors.push(format!(
                            "complete proof `{field}` assigned Cargo proof-unit index {} to both `{previous}` and `{label}`",
                            identity.proof_unit_index
                        ));
                    }
                }
            }
            Err(error) => {
                errors.push(format!("complete proof `{field}` entry {index} was invalid: {error}"))
            }
        }
    }
    identities
}

fn report_label_inventory(
    suite: &Value,
    field: &str,
    errors: &mut Vec<String>,
) -> BTreeSet<String> {
    let Some(values) = suite.get(field).and_then(Value::as_array) else {
        errors.push(format!("complete proof requires `{field}` as a target-label array"));
        return BTreeSet::new();
    };
    let mut labels = BTreeSet::new();
    for (index, value) in values.iter().enumerate() {
        let Some(label) = value.as_str().filter(|label| !label.is_empty()) else {
            errors.push(format!(
                "complete proof `{field}` entry {index} was not a nonempty target label"
            ));
            continue;
        };
        if !labels.insert(label.to_string()) {
            errors.push(format!("complete proof `{field}` repeated target label `{label}`"));
        }
    }
    labels
}

fn report_row_identity(
    row: &Value,
    context: &str,
    completed: &BTreeMap<String, CargoTargetIdentity>,
    errors: &mut Vec<String>,
) -> Option<ReportRowIdentity> {
    let object = match row.as_object() {
        Some(object) => object,
        None => {
            errors.push(format!("complete proof {context} was not an object"));
            return None;
        }
    };
    let identity = match object
        .get("cargo_target")
        .ok_or_else(|| "missing `cargo_target`".to_string())
        .and_then(cargo_target_identity_from_json)
    {
        Ok(identity) => identity,
        Err(error) => {
            errors.push(format!("complete proof {context} had invalid Cargo target: {error}"));
            return None;
        }
    };
    let label = identity.report_label();
    match completed.get(&label) {
        Some(completed_identity) if completed_identity == &identity => {}
        Some(_) => errors.push(format!(
            "complete proof {context} Cargo target fields disagreed with completed identity `{label}`"
        )),
        None => errors.push(format!(
            "complete proof {context} named uncompleted Cargo target `{label}`"
        )),
    }

    let raw_function = match object.get("raw_function") {
        Some(Value::String(function)) if !function.is_empty() => Some(function.clone()),
        Some(Value::Null) => None,
        _ => {
            errors
                .push(format!("complete proof {context} omitted a string-or-null `raw_function`"));
            None
        }
    };
    match (&raw_function, object.get("function")) {
        (Some(raw), Some(Value::String(scoped)))
            if scoped == &cargo_scoped_function(&identity, raw) => {}
        (None, Some(Value::Null)) => {}
        (Some(_), _) => errors.push(format!(
            "complete proof {context} function was not scoped by its exact Cargo target identity"
        )),
        (None, _) => errors.push(format!(
            "complete proof {context} null raw function had a non-null scoped function"
        )),
    }

    let source =
        match object.get("source").and_then(Value::as_str).filter(|value| !value.is_empty()) {
            Some(source) => source.to_string(),
            None => {
                errors.push(format!("complete proof {context} omitted nonempty `source`"));
                String::new()
            }
        };
    let line = match object.get("line").and_then(Value::as_u64) {
        Some(line) => line,
        None => {
            errors.push(format!("complete proof {context} omitted numeric `line`"));
            u64::MAX
        }
    };
    let row_index = match object.get("row_index").and_then(Value::as_u64) {
        Some(row_index) => row_index,
        None => {
            errors.push(format!("complete proof {context} omitted numeric `row_index`"));
            u64::MAX
        }
    };
    Some((label, source, line, raw_function, row_index))
}

fn report_target_scoped_rows(
    suite: &Value,
    field: &str,
    completed: &BTreeMap<String, CargoTargetIdentity>,
    errors: &mut Vec<String>,
) -> BTreeSet<ReportRowIdentity> {
    let Some(rows) = suite.get(field).and_then(Value::as_array) else {
        errors.push(format!("complete proof requires `{field}` as an array"));
        return BTreeSet::new();
    };
    let mut identities = BTreeSet::new();
    for (index, row) in rows.iter().enumerate() {
        if let Some(identity) =
            report_row_identity(row, &format!("`{field}` row {index}"), completed, errors)
        {
            if !identities.insert(identity) {
                errors.push(format!(
                    "complete proof `{field}` repeated one target-scoped transport row"
                ));
            }
        }
    }
    identities
}

fn validate_complete_proof_cargo_identity(suite: &Value, errors: &mut Vec<String>) {
    if suite.get("authenticated_cargo_transport").and_then(Value::as_bool) != Some(true) {
        errors.push("complete proof requires authenticated Cargo compiler transport".to_string());
    }
    let completed = report_target_inventory(suite, "completed_target_identities", errors);
    let covered = report_target_inventory(suite, "coverage_target_identities", errors);
    let completed_keys = completed.keys().cloned().collect::<BTreeSet<_>>();
    let covered_keys = covered.keys().cloned().collect::<BTreeSet<_>>();
    if completed_keys.is_empty() {
        errors.push(
            "complete proof requires at least one completed Cargo target identity".to_string(),
        );
    }
    if completed_keys != covered_keys {
        errors.push(
            "complete proof completed and covered Cargo target identities were not exact matches"
                .to_string(),
        );
    }
    if !completed.values().any(|target| target.proof_unit_role == "primary") {
        errors.push("complete proof requires a completed primary Cargo proof unit".to_string());
    }
    let completed_labels = report_label_inventory(suite, "completed_targets", errors);
    let coverage_labels = report_label_inventory(suite, "coverage_targets", errors);
    if completed_labels != completed_keys {
        errors.push(
            "complete proof legacy completed-target labels disagreed with exact identities"
                .to_string(),
        );
    }
    if coverage_labels != covered_keys {
        errors.push(
            "complete proof legacy coverage-target labels disagreed with exact identities"
                .to_string(),
        );
    }
    if suite.get("coverage").and_then(|coverage| coverage.get("complete")).and_then(Value::as_bool)
        != Some(true)
    {
        errors.push("complete proof requires exact whole-target coverage".to_string());
    }

    let mut crate_summary_targets = BTreeSet::new();
    match suite.get("crate_summaries").and_then(Value::as_array) {
        Some(summaries) => {
            for (index, summary) in summaries.iter().enumerate() {
                match summary
                    .get("cargo_target")
                    .ok_or_else(|| "missing `cargo_target`".to_string())
                    .and_then(cargo_target_identity_from_json)
                {
                    Ok(identity) => {
                        let label = identity.report_label();
                        if completed.get(&label) != Some(&identity) {
                            errors.push(format!(
                                "complete proof crate summary {index} named a non-completed Cargo target `{label}`"
                            ));
                        }
                        if !crate_summary_targets.insert(label.clone()) {
                            errors.push(format!(
                                "complete proof repeated terminal crate summary for Cargo target `{label}`"
                            ));
                        }
                    }
                    Err(error) => errors.push(format!(
                        "complete proof crate summary {index} had invalid Cargo target: {error}"
                    )),
                }
            }
        }
        None => errors.push("complete proof requires target-bound `crate_summaries`".to_string()),
    }
    if crate_summary_targets != completed_keys {
        errors.push(
            "complete proof terminal crate summaries did not exactly cover completed Cargo targets"
                .to_string(),
        );
    }

    let verification_rows =
        report_target_scoped_rows(suite, "verification_rows", &completed, errors);
    let obligation_rows = suite.get("obligation_rows").and_then(Value::as_u64).unwrap_or(0);
    if u64::try_from(verification_rows.len()).unwrap_or(u64::MAX) != obligation_rows {
        errors.push(
            "complete proof target-scoped verification-row count disagreed with obligation_rows"
                .to_string(),
        );
    }
    let obligation_evidence =
        report_target_scoped_rows(suite, "obligation_evidence", &completed, errors);
    if obligation_evidence != verification_rows {
        errors.push(
            "complete proof obligation evidence did not exactly match target-scoped verification rows"
                .to_string(),
        );
    }

    let mut functions = BTreeSet::new();
    match suite.get("functions").and_then(Value::as_array) {
        Some(values) => {
            for (index, value) in values.iter().enumerate() {
                let Some(function) = value.as_str().filter(|function| !function.is_empty()) else {
                    errors.push(format!(
                        "complete proof function entry {index} was not a nonempty string"
                    ));
                    continue;
                };
                if !completed_keys.iter().any(|target| {
                    function
                        .strip_prefix(target)
                        .is_some_and(|suffix| suffix.starts_with("::") && suffix.len() > 2)
                }) {
                    errors.push(format!(
                        "complete proof function `{function}` was not scoped by a completed Cargo target"
                    ));
                }
                if !functions.insert(function.to_string()) {
                    errors.push(format!(
                        "complete proof repeated target-scoped function `{function}`"
                    ));
                }
            }
        }
        None => errors.push("complete proof requires target-scoped `functions`".to_string()),
    }
    for (target, _, _, raw_function, _) in &verification_rows {
        if let Some(raw_function) = raw_function {
            let scoped = format!("{target}::{raw_function}");
            if !functions.contains(&scoped) {
                errors.push(format!(
                    "complete proof verification row function `{scoped}` was absent from the target-scoped function inventory"
                ));
            }
        }
    }
}

fn validate_report_payload(report: &Value) -> Result<(), String> {
    let mut errors = Vec::new();
    if report.get("schema").and_then(Value::as_str) != Some(SCHEMA) {
        errors.push("report schema mismatch".to_string());
    }
    if !matches!(
        report.get("status").and_then(Value::as_str),
        Some("planned" | "passed" | "failed" | "incomplete" | "timed_out")
    ) {
        errors.push(format!(
            "invalid report status: {:?}",
            report.get("status").unwrap_or(&Value::Null)
        ));
    }
    let stages = report.get("stages").and_then(Value::as_array);
    if stages.is_none_or(|stages| stages.is_empty()) {
        errors.push("report must contain at least one stage".to_string());
    }
    if !matches!(
        report.get("proof").and_then(|proof| proof.get("status")).and_then(Value::as_str),
        Some("not_run" | "complete" | "failed" | "incomplete")
    ) {
        errors.push("report proof must contain a valid status".to_string());
    }
    if report
        .get("proof")
        .and_then(|proof| proof.get("timeout_is_incomplete_proof"))
        .and_then(Value::as_bool)
        != Some(true)
    {
        errors.push("timeout-is-incomplete-proof semantics must be explicit".to_string());
    }
    if report.get("proof").and_then(|proof| proof.get("status")).and_then(Value::as_str)
        == Some("complete")
    {
        let suite = report.get("solver_suite").unwrap_or(&Value::Null);
        if report
            .get("evidence_controls")
            .and_then(|controls| controls.get("exact_cargo_target_identity_required"))
            .and_then(Value::as_bool)
            != Some(true)
        {
            errors.push(
                "complete proof must declare exact Cargo target identity as an evidence control"
                    .to_string(),
            );
        }
        if report
            .get("evidence_controls")
            .and_then(|controls| controls.get("exact_cargo_proof_inventory_required"))
            .and_then(Value::as_bool)
            != Some(true)
        {
            errors.push(
                "complete proof must declare exact Cargo proof inventory as an evidence control"
                    .to_string(),
            );
        }
        validate_complete_proof_cargo_identity(suite, &mut errors);
        errors.extend(cargo_proof_inventory_completeness_errors(suite));
        if suite.get("stage2_toolchain_identity_verified").and_then(Value::as_bool) != Some(true) {
            errors.push(
                "complete proof requires captured and rechecked stage2 Targo/trustc/trustdoc/trustd identities and the platform-required live daemon protocol smoke"
                    .to_string(),
            );
        }
        if suite.get("stage2_execution_identity_bound").and_then(Value::as_bool) != Some(true) {
            errors.push(
                "complete proof requires the exact stage2 executable bytes used by every compiler and rustdoc launch to be execution-bound"
                    .to_string(),
            );
        }
        if suite.get("source_provenance_bound").and_then(Value::as_bool) != Some(true) {
            errors.push(
                "complete proof requires the source tree, index, submodules, and dependency closure to be bound to the executed toolchain; verbose-version identity agreement alone is insufficient"
                    .to_string(),
            );
        }
        if suite.get("obligation_rows").and_then(Value::as_u64).unwrap_or(0) == 0 {
            errors.push("complete proof requires at least one solver obligation row".to_string());
        }
        for outcome in INCOMPLETE_OUTCOMES.iter().chain(FAILED_OUTCOMES) {
            if suite
                .get("outcomes")
                .and_then(|outcomes| outcomes.get(*outcome))
                .and_then(Value::as_u64)
                .unwrap_or(0)
                > 0
            {
                errors.push(format!("complete proof cannot include {outcome} outcomes"));
            }
        }
        for (outcome, count) in unrecognized_outcomes_value(suite) {
            if count > 0 {
                errors.push(format!(
                    "complete proof cannot include unrecognized outcome `{outcome}`"
                ));
            }
        }
        if suite
            .get("coverage_blockers")
            .and_then(Value::as_array)
            .is_some_and(|items| !items.is_empty())
        {
            errors.push("complete proof cannot include coverage_blockers".to_string());
        }
        let proved_rows_missing_proof_binding = suite
            .get("verification_rows")
            .and_then(Value::as_array)
            .map(|rows| {
                rows.iter()
                    .filter(|row| {
                        row.get("outcome_class").and_then(Value::as_str) == Some("proved")
                            && row
                                .get("proof_binding")
                                .and_then(|binding| binding.get("accepted"))
                                .and_then(Value::as_bool)
                                != Some(true)
                    })
                    .count()
            })
            .unwrap_or(0);
        if proved_rows_missing_proof_binding > 0 {
            errors.push(
                "complete proof requires every proved row to carry proof artifact/transcript binding"
                    .to_string(),
            );
        }
        if suite
            .get("all_unknown_routing")
            .and_then(|routing| routing.get("detected"))
            .and_then(Value::as_bool)
            == Some(true)
        {
            errors.push("complete proof cannot include all_unknown_routing".to_string());
        }
    }
    if errors.is_empty() { Ok(()) } else { Err(errors.join("; ")) }
}

fn write_report(report_path: &Path, report: &Value) -> Result<(), String> {
    let parent = report_path
        .parent()
        .ok_or_else(|| format!("report path has no parent: {}", report_path.display()))?;
    match fs::symlink_metadata(report_path) {
        Ok(_) => {
            return Err(format!(
                "refusing to replace an existing report path: {}",
                report_path.display()
            ));
        }
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => {
            return Err(format!(
                "failed to inspect report destination {}: {error}",
                report_path.display()
            ));
        }
    }
    let tmp_path = report_path.with_file_name(format!(
        ".{}.{}.tmp",
        report_path.file_name().and_then(|name| name.to_str()).unwrap_or(REPORT_NAME),
        random_hex(16)?
    ));
    let text = serde_json::to_string_pretty(report)
        .map_err(|error| format!("failed to serialize report: {error}"))?
        + "\n";
    let publish = (|| -> Result<(), String> {
        let mut tmp = open_private_new_file(&tmp_path).map_err(|error| {
            format!("failed to create private report {}: {error}", tmp_path.display())
        })?;
        tmp.write_all(text.as_bytes())
            .map_err(|error| format!("failed to write report {}: {error}", tmp_path.display()))?;
        tmp.sync_all()
            .map_err(|error| format!("failed to fsync report {}: {error}", tmp_path.display()))?;
        drop(tmp);
        fs::rename(&tmp_path, report_path).map_err(|error| {
            format!(
                "failed to publish report {} -> {}: {error}",
                tmp_path.display(),
                report_path.display()
            )
        })?;
        sync_directory(parent).map_err(|error| {
            format!("failed to fsync report directory {}: {error}", parent.display())
        })
    })();
    if publish.is_err() {
        let _ = fs::remove_file(&tmp_path);
    }
    publish
}

fn recorded_environment(env_map: &BTreeMap<String, String>) -> Value {
    let mut recorded = Map::new();
    for key in ENV_KEYS_TO_RECORD {
        recorded.insert(
            (*key).to_string(),
            env_map.get(*key).cloned().map(Value::String).unwrap_or(Value::Null),
        );
    }
    Value::Object(recorded)
}

fn stage2_toolchain_identity_json(identity: Option<&Stage2ToolchainIdentity>) -> Value {
    let Some(identity) = identity else {
        return Value::Null;
    };
    json!({
        "targo_commit": identity.targo_version.commit,
        "trustc_commit": identity.trustc_version.commit,
        "trustdoc_commit": identity.trustdoc_version.commit,
        "trustd_commit": identity.trustd_version.commit,
        "version_labels_match": identity.targo_version.binary == "targo"
            && identity.trustc_version.binary == "trustc"
            && identity.trustdoc_version.binary == "trustdoc"
            && identity.trustd_version.binary == "trustd"
            && identity.targo_version.host == identity.trustc_version.host
            && identity.targo_version.release == identity.trustc_version.release
            && identity.targo_version.commit == identity.trustc_version.commit
            && identity.trustc_version.host == identity.trustdoc_version.host
            && identity.trustc_version.release == identity.trustdoc_version.release
            && identity.trustc_version.commit == identity.trustdoc_version.commit
            && identity.trustc_version.release == identity.trustd_version.release
            && identity.trustc_version.commit == identity.trustd_version.commit
            && identity.trustd_version.protocol == trust_router::coordinator::STATUS_VERSION,
        "verbose_version_identities_validated": true,
        "version_label_scope": "diagnostic Targo/trustc/trustdoc/trustd binary, release, and commit consistency plus trustd protocol compatibility; labels are not compared with Git and do not establish source provenance",
        "targo_verbose_version_identity": {
            "binary": identity.targo_version.binary,
            "binary_authority": "exact leading -Vv token",
            "host": identity.targo_version.host,
            "release": identity.targo_version.release,
            "commit_hash": identity.targo_version.commit,
        },
        "trustc_verbose_version_identity": {
            "binary": identity.trustc_version.binary,
            "binary_authority": "exact unique binary: field",
            "host": identity.trustc_version.host,
            "release": identity.trustc_version.release,
            "commit_hash": identity.trustc_version.commit,
        },
        "trustdoc_verbose_version_identity": {
            "binary": identity.trustdoc_version.binary,
            "binary_authority": "exact unique binary: field",
            "host": identity.trustdoc_version.host,
            "release": identity.trustdoc_version.release,
            "commit_hash": identity.trustdoc_version.commit,
        },
        "trustd_version_identity": {
            "binary": identity.trustd_version.binary,
            "binary_authority": "exact leading --version token plus exact unique trust.identity field",
            "release": identity.trustd_version.release,
            "commit_hash": identity.trustd_version.commit,
            "protocol": identity.trustd_version.protocol,
        },
        "trustd_protocol_smoke": identity.trustd_protocol_smoke.as_ref().map(|smoke| json!({
            "schema": "trust.self-verify.trustd-protocol-smoke.v1",
            "required_on_this_platform": cfg!(unix),
            "ambient_lookup_permitted": false,
            "exact_captured_executable_required": true,
            "fresh_owner_private_endpoint_required": true,
            "existing_endpoint_reuse_permitted": false,
            "canonical_child_spawn_required": true,
            "bounded": true,
            "same_stage2_bin_required": true,
            "daemon_tool_identity": {
                "name": "trustd",
                "path": identity.trustd.canonical_path,
                "repo_relative_path": format!("build/host/stage2/bin/{}", stage2_tool_file_name("trustd")),
                "sha256": identity.trustd.sha256,
                "size_bytes": identity.trustd.size_bytes,
                "release": identity.trustd_version.release,
                "commit_hash": identity.trustd_version.commit,
                "protocol": identity.trustd_version.protocol,
            },
            "requests": ["PING", "IDENTITY", "STATUS", "RESERVE", "STATUS", "RELEASE", "STATUS"],
            "ping_response": smoke.ping_response,
            "reservation_bytes": smoke.reservation_bytes,
            "reservation_label": smoke.reservation_label,
            "reservation_pid": smoke.reservation_pid,
            "reservation_token": smoke.reservation_token,
            "identity_response": smoke.identity_response,
            "status_before": smoke.status_before,
            "status_reserved": smoke.status_reserved,
            "status_released": smoke.status_released,
            "status_semantically_valid": smoke.status_before.is_semantically_valid()
                && smoke.status_reserved.is_semantically_valid()
                && smoke.status_released.is_semantically_valid(),
            "reserve_release_transition_valid": true,
            "transcript_kind": "canonical typed observation; raw wire bytes are not retained",
            "transcript": smoke.transcript,
            "transcript_sha256": smoke.transcript_sha256,
            "transcript_path": Value::Null,
        })),
        "trustd_protocol_smoke_required_on_this_platform": cfg!(unix),
        "trustd_protocol_smoke_completed": identity.trustd_protocol_smoke.is_some(),
        "source_provenance_bound": false,
        "source_cleanliness_bound": false,
        "stage2_bin_plain_directory_required": true,
        "endpoint_snapshot_model": "before/open/after file-object identity, length, canonical path, and bounded SHA-256 for Targo, trustc, trustdoc, and trustd",
        "snapshot_source": "captured and validated before stage execution; report generation does not reopen the executable paths",
        "execution_identity_bound": false,
        "targo": {
            "path": identity.targo.canonical_path,
            "file_identity": file_object_identity_json(identity.targo.file_identity),
            "sha256": identity.targo.sha256,
            "size_bytes": identity.targo.size_bytes,
        },
        "trustc": {
            "path": identity.trustc.canonical_path,
            "file_identity": file_object_identity_json(identity.trustc.file_identity),
            "sha256": identity.trustc.sha256,
            "size_bytes": identity.trustc.size_bytes,
        },
        "trustdoc": {
            "path": identity.trustdoc.canonical_path,
            "file_identity": file_object_identity_json(identity.trustdoc.file_identity),
            "sha256": identity.trustdoc.sha256,
            "size_bytes": identity.trustdoc.size_bytes,
        },
        "trustd": {
            "path": identity.trustd.canonical_path,
            "file_identity": file_object_identity_json(identity.trustd.file_identity),
            "sha256": identity.trustd.sha256,
            "size_bytes": identity.trustd.size_bytes,
        },
    })
}

fn recorded_toolchains(
    root: &Path,
    env_map: &BTreeMap<String, String>,
    stage2: Option<&Stage2ToolchainIdentity>,
) -> Value {
    let tools = [
        ("targo", "TRUST_TARGO_BIN"),
        ("trustc", "TRUST_TRUSTC_BIN"),
        ("targo-trust", "TRUST_TARGO_TRUST_BIN"),
        ("trustdoc", "TRUST_TRUSTDOC_BIN"),
        ("trustd", "TRUST_TRUSTD_BIN"),
    ];
    let entries = tools
        .iter()
        .map(|(tool, env_key)| {
            let captured = match (*tool, stage2) {
                ("targo", Some(identity)) => Some(&identity.targo),
                ("trustc", Some(identity)) => Some(&identity.trustc),
                ("trustdoc", Some(identity)) => Some(&identity.trustdoc),
                ("trustd", Some(identity)) => Some(&identity.trustd),
                _ => None,
            };
            let path = captured
                .map(|identity| identity.canonical_path.clone())
                .or_else(|| env_map.get(*env_key).map(PathBuf::from))
                .or_else(|| {
                    env_map.get("TRUSTC").map(|trustc| {
                        PathBuf::from(trustc).with_file_name(stage2_tool_file_name(tool))
                    })
                })
                .unwrap_or_else(|| {
                    root.join("build/host/stage2/bin").join(stage2_tool_file_name(tool))
                });
            let expected_sha256 = match *tool {
                "targo" => env_map.get("TRUST_SELF_VERIFY_TARGO_SHA256"),
                "trustc" => env_map.get("TRUST_SELF_VERIFY_TRUSTC_SHA256"),
                "trustdoc" => env_map.get("TRUST_SELF_VERIFY_TRUSTDOC_SHA256"),
                "trustd" => env_map.get("TRUST_SELF_VERIFY_TRUSTD_SHA256"),
                _ => None,
            };
            let identity_matches_expected = match (
                captured.map(|identity| identity.sha256.as_str()),
                expected_sha256.map(String::as_str),
            ) {
                (Some(actual), Some(expected)) => Value::Bool(actual == expected),
                _ => Value::Null,
            };
            json!({
                "tool": tool,
                "env": env_key,
                "path": relative_path(&path, root),
                "available": captured.map(|_| true),
                "regular_file": captured.map(|_| true),
                "executable": captured.map(|_| true),
                "symlink": captured.map(|_| false),
                "file_identity": captured.map(|identity| file_object_identity_json(identity.file_identity)),
                "size_bytes": captured.map(|identity| identity.size_bytes),
                "sha256": captured.map(|identity| identity.sha256.clone()),
                "expected_sha256": expected_sha256,
                "identity_matches_expected": identity_matches_expected,
                "snapshot_source": if captured.is_some() {
                    "captured validated bounded endpoint snapshot; no report-time reopen"
                } else {
                    "not captured; report generation intentionally performs no path inspection or hashing"
                },
            })
        })
        .collect::<Vec<_>>();
    json!({
        "source": "Rust self-verification CLI",
        "identity_model": "captured plain repository stage2 endpoints with non-symlink/non-reparse validation, file-object continuity, and bounded SHA-256; report generation does not reopen paths",
        "report_time_path_reopen": false,
        "report_time_hashing": false,
        "external_trust_anchor_present": false,
        "execution_identity_bound": false,
        "source_provenance_bound": false,
        "source_cleanliness_bound": false,
        "version_labels_are_source_provenance": false,
        "transient_swap_restore_detected": false,
        "endpoint_snapshot_equality_detects_persistent_change_only": true,
        "external_execution_isolation_required": true,
        "residual_assumption": "the initially captured stage2 Targo/trustc/trustdoc/trustd binaries are trusted; endpoint path and SHA-256 equality plus the exact-sibling trustd live identity smoke detect persistent changes present at either snapshot, but neither binds the source/dependency closure nor the bytes actually executed and cannot detect a same-user replace/execute/restore race during Cargo build scripts, proc macros, rustdoc, or daemon launch; closing those boundaries requires authenticated source/dependency provenance plus an external signed/reproducible trust anchor and execution isolation or a platform execution-handle design plumbed through every launch",
        "tools": entries,
    })
}

fn git_info() -> Value {
    json!({
        "head": "",
        "branch": "",
        "head_available": false,
        "branch_available": false,
        "authority": "not consulted by self-verification",
        "ambient_git_executed": false,
        "source_provenance_bound": false,
        "source_cleanliness_bound": false,
        "reason": "tool version labels are diagnostic consistency only; this report does not parse Git metadata or claim that the source/dependency closure matches a commit",
    })
}

fn verification_scope(plan: &StagePlan) -> Value {
    let kind = if plan.label.contains("stage2") || plan.target.contains("stage2") {
        "stage2-self-build"
    } else if plan.target.starts_with("compiler/") {
        "compiler-crate"
    } else {
        "custom"
    };
    json!({
        "kind": kind,
        "target": plan.target,
        "evidence_manifest": plan.evidence_manifest.display().to_string(),
        "stage_label": plan.label,
        "command": {
            "argv": plan.argv,
            "command_line": command_line(&plan.argv),
        },
        "evidence_requirements": {
            "stage2_endpoint_snapshot_identity_required": true,
            "stage2_tool_verbose_identities_agree_required": true,
            "version_labels_are_source_provenance": false,
            "source_provenance_bound": false,
            "source_cleanliness_bound": false,
            "stage2_plain_bin_directory_required": true,
            "stage2_execution_identity_bound": false,
            "external_execution_isolation_required": true,
            "compiler_trust_json_required": true,
            "per_obligation_rows_required": true,
            "unknown_outcomes_complete_proof": false,
            "timeout_outcomes_complete_proof": false,
            "unrecognized_outcomes_complete_proof": false,
            "no_verification_outcomes_complete_proof": false,
            "row_level_proof_artifact_or_transcript_binding_required": true,
        },
    })
}

fn composition_metadata(target: &str, evidence_manifest: &Path, stage_label: &str) -> Value {
    json!({
        "target": target,
        "evidence_manifest": evidence_manifest.display().to_string(),
        "stage_label": stage_label,
        "self_verification_stage": true,
        "rust_cli_owned": true,
        "python_policy_engine": false,
    })
}

fn stage2_bootstrap_semantics(plan: &StagePlan) -> Value {
    json!({
        "stage2_source": "direct Cargo JSON evidence command under verification harness",
        "evidence_command_only": true,
        "evidence_manifest": plan.evidence_manifest.display().to_string(),
        "bootstrap_stdout_parsed_as_evidence": false,
        "bootstrap_rebuild_is_separate_phase": true,
        "delegated_build_command_detected": false,
        "native_bootstrap_runner_detected": false,
        "full_bootstrap_requested": false,
        "rebuild_claimed": false,
        "independent_std_rebuild_claimed": false,
        "independent_std_rebuild_claim_requires_log_evidence": true,
    })
}

fn resolve_report_dir(options: &Options) -> Result<PathBuf, String> {
    validate_run_id(&options.run_id)?;
    let path = options.report_dir.clone().unwrap_or_else(|| {
        options.repo_root.join("reports").join("self-verify-harness").join(&options.run_id)
    });
    let path = if path.is_absolute() { path } else { options.repo_root.join(path) };
    if path.components().any(|component| component == Component::ParentDir) {
        return Err(format!(
            "report directory must not contain parent traversal: {}",
            path.display()
        ));
    }
    Ok(path)
}

fn validate_run_id(run_id: &str) -> Result<(), String> {
    if run_id.is_empty() || run_id.len() > MAX_RUN_ID_BYTES {
        return Err(format!("--run-id must contain 1..={MAX_RUN_ID_BYTES} bytes"));
    }
    if matches!(run_id, "." | "..")
        || !run_id
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'))
    {
        return Err(
            "--run-id must be one safe ASCII path component using only letters, digits, '.', '-', or '_'"
                .to_string(),
        );
    }
    Ok(())
}

fn create_private_report_directory(path: &Path) -> Result<PathBuf, String> {
    let parent = path
        .parent()
        .ok_or_else(|| format!("report directory has no parent: {}", path.display()))?;
    create_directory_tree_without_symlinks(parent)?;
    fs::create_dir(path).map_err(|error| {
        format!(
            "refusing non-fresh report directory {} (each run must own a new directory): {error}",
            path.display()
        )
    })?;
    make_directory_private(path)?;
    let canonical = path
        .canonicalize()
        .map_err(|error| format!("could not canonicalize report directory: {error}"))?;
    validate_private_directory(&canonical, "report directory")?;
    sync_directory(parent)
        .map_err(|error| format!("could not fsync report parent {}: {error}", parent.display()))?;
    Ok(canonical)
}

fn create_private_subdirectory(path: &Path) -> Result<(), String> {
    fs::create_dir(path).map_err(|error| {
        format!("could not create fresh private directory {}: {error}", path.display())
    })?;
    make_directory_private(path)?;
    validate_private_directory(path, "private output directory")?;
    if let Some(parent) = path.parent() {
        sync_directory(parent).map_err(|error| {
            format!("could not fsync private directory parent {}: {error}", parent.display())
        })?;
    }
    Ok(())
}

fn create_directory_tree_without_symlinks(path: &Path) -> Result<(), String> {
    let mut current = PathBuf::new();
    for component in path.components() {
        match component {
            Component::Prefix(_) | Component::RootDir => current.push(component.as_os_str()),
            Component::CurDir => continue,
            Component::ParentDir => {
                return Err(format!(
                    "output directory contains parent traversal: {}",
                    path.display()
                ));
            }
            Component::Normal(name) => {
                current.push(name);
                match fs::symlink_metadata(&current) {
                    Ok(metadata) => {
                        if metadata.file_type().is_symlink()
                            && trusted_platform_ancestor_symlink(&current, &metadata)
                        {
                            continue;
                        }
                        if metadata.file_type().is_symlink() || !metadata.is_dir() {
                            return Err(format!(
                                "output directory component is not a non-symlink directory: {}",
                                current.display()
                            ));
                        }
                    }
                    Err(error) if error.kind() == io::ErrorKind::NotFound => {
                        fs::create_dir(&current).map_err(|error| {
                            format!(
                                "could not create output directory {}: {error}",
                                current.display()
                            )
                        })?;
                        make_directory_private(&current)?;
                    }
                    Err(error) => {
                        return Err(format!(
                            "could not inspect output directory {}: {error}",
                            current.display()
                        ));
                    }
                }
            }
        }
    }
    Ok(())
}

/// Some platforms expose stable, administrator-owned top-level aliases (macOS
/// `/var` -> `/private/var` is the common example). Following an arbitrary
/// caller-controlled symlink would reopen the report-path race this walk is
/// intended to close, but rejecting an immutable system alias makes ordinary
/// temporary directories unusable. Permit a symlink only when both it and its
/// containing directory are root-owned, the containing directory is not
/// group/world writable, and the resolved object is a directory. Every path
/// component below the alias is still checked independently.
#[cfg(unix)]
fn trusted_platform_ancestor_symlink(path: &Path, metadata: &fs::Metadata) -> bool {
    use std::os::unix::fs::{MetadataExt as _, PermissionsExt as _};

    if metadata.uid() != 0 {
        return false;
    }
    let Some(parent) = path.parent() else {
        return false;
    };
    let Ok(parent_metadata) = fs::symlink_metadata(parent) else {
        return false;
    };
    if parent_metadata.file_type().is_symlink()
        || !parent_metadata.is_dir()
        || parent_metadata.uid() != 0
        || parent_metadata.permissions().mode() & 0o022 != 0
    {
        return false;
    }
    path.canonicalize().ok().and_then(|target| fs::symlink_metadata(target).ok()).is_some_and(
        |target_metadata| !target_metadata.file_type().is_symlink() && target_metadata.is_dir(),
    )
}

#[cfg(not(unix))]
fn trusted_platform_ancestor_symlink(_path: &Path, _metadata: &fs::Metadata) -> bool {
    false
}

fn make_directory_private(path: &Path) -> Result<(), String> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        fs::set_permissions(path, fs::Permissions::from_mode(0o700)).map_err(|error| {
            format!("could not set owner-private permissions on {}: {error}", path.display())
        })?;
    }
    Ok(())
}

fn validate_private_directory(path: &Path, description: &str) -> Result<(), String> {
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| format!("could not inspect {description} {}: {error}", path.display()))?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(format!("{description} is not a non-symlink directory: {}", path.display()));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        if metadata.permissions().mode() & 0o777 != 0o700 {
            return Err(format!(
                "{description} is not owner-private mode 0700: {}",
                path.display()
            ));
        }
    }
    Ok(())
}

fn open_private_new_file(path: &Path) -> io::Result<File> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;

        options.mode(0o600).custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC);
    }
    let file = options.open(path)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        file.set_permissions(fs::Permissions::from_mode(0o600))?;
    }
    Ok(file)
}

#[cfg(unix)]
fn sync_directory(path: &Path) -> io::Result<()> {
    File::open(path)?.sync_all()
}

#[cfg(not(unix))]
fn sync_directory(_path: &Path) -> io::Result<()> {
    // Opening directories as `File` is not supported by all platforms. Every
    // evidence file is still individually flushed before publication.
    Ok(())
}

fn stage_log_stem(label: &str) -> String {
    let digest = format!("{:x}", Sha256::digest(label.as_bytes()));
    format!("stage-{}", &digest[..24])
}

fn relative_path(path: &Path, root: &Path) -> String {
    path.strip_prefix(root)
        .map(|path| path.display().to_string())
        .unwrap_or_else(|_| path.display().to_string())
}

fn command_line(argv: &[String]) -> String {
    argv.iter()
        .map(|arg| {
            if arg.chars().all(|ch| {
                ch.is_ascii_alphanumeric() || matches!(ch, '/' | '.' | '_' | '-' | '=' | ':')
            }) {
                arg.clone()
            } else {
                format!("'{}'", arg.replace('\'', "'\\''"))
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

fn compact_json(value: &Value) -> String {
    let mut text =
        if let Some(text) = value.as_str() { text.to_string() } else { value.to_string() };
    text = text.split_whitespace().collect::<Vec<_>>().join(" ");
    if text.len() > 240 {
        text.truncate(237);
        text.push_str("...");
    }
    text
}

fn round3(value: f64) -> f64 {
    (value * 1000.0).round() / 1000.0
}

fn now_string() -> String {
    let seconds = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_secs())
        .unwrap_or(0);
    format!("unix:{seconds}")
}

fn random_hex(bytes: usize) -> Result<String, String> {
    let mut random = vec![0_u8; bytes];
    getrandom::fill(&mut random)
        .map_err(|error| format!("operating-system randomness unavailable: {error}"))?;
    Ok(random.iter().map(|byte| format!("{byte:02x}")).collect())
}

fn run_id() -> Result<String, String> {
    Ok(format!("self-verify-{}", random_hex(16)?))
}

fn is_help_arg(arg: &str) -> bool {
    matches!(arg, "-h" | "--help" | "help")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bound_transport_artifact(
        kind: &str,
        payload: &[u8],
        binding: &str,
        owner: &str,
        mut references: Vec<trust_types::TransportArtifactReference>,
        external_root: Option<&Path>,
    ) -> trust_types::TransportEvidenceArtifact {
        const MAGIC: &[u8] = b"trust.evidence-artifact-binding-envelope.v1\0";
        references.sort();
        let mut bytes = MAGIC.to_vec();
        let push = |bytes: &mut Vec<u8>, value: &[u8]| {
            bytes.extend_from_slice(&(value.len() as u32).to_be_bytes());
            bytes.extend_from_slice(value);
        };
        push(&mut bytes, kind.as_bytes());
        push(&mut bytes, owner.as_bytes());
        push(&mut bytes, binding.as_bytes());
        bytes.extend_from_slice(&(references.len() as u32).to_be_bytes());
        for reference in &references {
            push(&mut bytes, reference.kind.as_bytes());
            push(&mut bytes, reference.digest.algorithm.as_bytes());
            push(&mut bytes, reference.digest.value.as_bytes());
        }
        bytes.extend_from_slice(&(payload.len() as u64).to_be_bytes());
        bytes.extend_from_slice(payload);
        let digest = format!("{:x}", Sha256::digest(&bytes));
        let mut materialization = trust_types::TransportArtifactMaterialization::from_exact_bytes(
            &bytes, binding, references,
        )
        .expect("bound transport materialization");
        if let Some(root) = external_root {
            let store = root.join(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY).join("sha256");
            fs::create_dir_all(&store).expect("create proof artifact store");
            fs::write(store.join(&digest), &bytes).expect("write proof artifact");
            materialization = materialization
                .with_materialized_path(format!(
                    "{}/sha256/{digest}",
                    trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY
                ))
                .expect("path materialization");
        }
        trust_types::TransportEvidenceArtifact {
            kind: kind.into(),
            format: Some("binary".into()),
            artifact_id: Some(kind.into()),
            digest: Some(trust_types::TransportArtifactDigest {
                algorithm: "sha256".into(),
                value: digest.clone(),
            }),
            uri: Some(format!("artifact://self-verify/{kind}/{digest}")),
            materialization: Some(materialization),
            metadata: None,
        }
    }

    fn native_shape_artifacts(
        suite: &str,
        request_id: &str,
        proof_id: &str,
    ) -> Vec<trust_types::TransportEvidenceArtifact> {
        let native_id = format!("trust_ir-native-{suite}-request-{request_id}-proof-{proof_id}");
        let bundle = native_materialization(
            "bundle",
            None,
            None,
            None,
            serde_json::json!({"bundle": "exact"}),
            &native_id,
            vec![],
        );
        let bundle_digest = bundle.1.value.clone();
        let bundle_uri = format!("trust_ir-native://verification-bundle/{bundle_digest}");
        let request = native_materialization(
            "request",
            Some(suite),
            Some(request_id),
            None,
            serde_json::json!({"request": "exact"}),
            &native_id,
            vec![trust_types::TransportArtifactReference {
                kind: "EngineInput".into(),
                digest: bundle.1.clone(),
            }],
        );
        let request_digest = request.1.value.clone();
        let normalized = native_materialization(
            "normalized_obligation",
            Some(suite),
            Some(request_id),
            Some(proof_id),
            serde_json::json!({"obligation": "exact"}),
            &native_id,
            vec![trust_types::TransportArtifactReference {
                kind: "EngineInput".into(),
                digest: request.1.clone(),
            }],
        );
        vec![
            native_artifact("EngineInput", bundle, bundle_uri.clone()),
            native_artifact(
                "EngineInput",
                request,
                format!("{bundle_uri}/{suite}/request/{request_id}/{request_digest}"),
            ),
            native_artifact(
                "NormalizedObligation",
                normalized.clone(),
                format!(
                    "{bundle_uri}/{suite}/request/{request_id}/{request_digest}/proof/{proof_id}/{}",
                    normalized.1.value
                ),
            ),
        ]
    }

    fn native_materialization(
        role: &str,
        suite: Option<&str>,
        request_id: Option<&str>,
        proof_id: Option<&str>,
        payload: Value,
        native_id: &str,
        references: Vec<trust_types::TransportArtifactReference>,
    ) -> (trust_types::TransportArtifactMaterialization, trust_types::TransportArtifactDigest) {
        let mut value = json!({
            "schema": trust_types::NATIVE_TRUST_IR_MATERIALIZATION_SCHEMA,
            "role": role,
            "suite": suite,
            "request_id": request_id,
            "proof_id": proof_id,
            "payload": payload,
        });
        canonicalize_test_json(&mut value);
        let bytes = serde_json::to_vec(&value).expect("serialize native materialization");
        let digest = trust_types::TransportArtifactDigest {
            algorithm: "sha256".into(),
            value: format!("{:x}", Sha256::digest(&bytes)),
        };
        (
            trust_types::TransportArtifactMaterialization::from_exact_bytes(
                &bytes, native_id, references,
            )
            .expect("native materialization"),
            digest,
        )
    }

    fn native_artifact(
        kind: &str,
        materialized: (
            trust_types::TransportArtifactMaterialization,
            trust_types::TransportArtifactDigest,
        ),
        uri: String,
    ) -> trust_types::TransportEvidenceArtifact {
        trust_types::TransportEvidenceArtifact {
            kind: kind.into(),
            format: Some("trust_ir-json".into()),
            artifact_id: None,
            digest: Some(materialized.1),
            uri: Some(uri),
            materialization: Some(materialized.0),
            metadata: None,
        }
    }

    fn canonicalize_test_json(value: &mut Value) {
        match value {
            Value::Array(values) => {
                for value in values {
                    canonicalize_test_json(value);
                }
            }
            Value::Object(object) => {
                let old = std::mem::take(object);
                let mut entries = old.into_iter().collect::<Vec<_>>();
                entries.sort_by(|left, right| left.0.cmp(&right.0));
                for (key, mut value) in entries {
                    canonicalize_test_json(&mut value);
                    object.insert(key, value);
                }
            }
            _ => {}
        }
    }

    #[test]
    fn verification_flags_use_tracked_policy_without_retired_activation_modes() {
        let advisory = verification_flags(1, false);
        assert!(!advisory.iter().any(|flag| flag == "-Z trust-verify"));
        assert!(!advisory.iter().any(|flag| flag == "-Z trust-verify-full"));
        assert!(advisory.iter().any(|flag| flag == "-Z codegen-backend=llvm"));
        assert!(advisory.iter().any(|flag| flag == "-Z trust-verify-include-dependencies=yes"));
        assert!(
            advisory.iter().any(|flag| flag.starts_with("-Z trust-verify-session=self-verify-"))
        );

        let full = verification_flags(2, true);
        assert!(!full.iter().any(|flag| flag == "-Z trust-verify-full"));
        assert!(!full.iter().any(|flag| flag == "-Z trust-verify"));

        let configured = verification_flags_with_scope(
            2,
            true,
            "yes",
            Some("3"),
            Path::new("/tmp/trust-self-verify-test-proof-root"),
        )
        .expect("configured proof root flag");
        assert!(configured.iter().any(|flag| flag == "-Z trust-verify-include-dependencies=yes"));
        assert!(configured.iter().any(|flag| flag == "-Z trust-verify-worker-threads=3"));
        assert!(configured.iter().any(|flag| {
            flag == "-Ztrust-proof-artifact-root=/tmp/trust-self-verify-test-proof-root"
        }));
    }

    #[test]
    fn self_verify_proof_root_is_private_and_run_scoped() {
        let path = {
            let root = SelfVerifyProofArtifactRoot::create().expect("create proof root");
            let path = root.path().to_path_buf();
            assert!(path.is_absolute());
            assert_eq!(path.canonicalize().expect("canonical proof root"), path);
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt as _;

                assert_eq!(
                    fs::metadata(&path).expect("proof root metadata").permissions().mode() & 0o777,
                    0o700
                );
            }
            path
        };
        assert!(!path.exists(), "self-verification proof root survived its owner plan");
    }

    #[test]
    fn self_verify_proof_root_flag_rejects_ambiguous_argument_paths() {
        let error = verification_flags_with_scope(
            1,
            false,
            "no",
            None,
            Path::new("/tmp/proof roots/ambiguous"),
        )
        .expect_err("whitespace would split a bootstrap rustflags argument");
        assert!(error.contains("whitespace"), "unexpected error: {error}");
    }

    #[test]
    fn dependency_scope_environment_booleans_are_canonical_rustc_booleans() {
        for (raw, expected) in [
            ("0", "no"),
            ("false", "no"),
            ("off", "no"),
            ("1", "yes"),
            ("true", "yes"),
            ("on", "yes"),
        ] {
            assert_eq!(normalize_scope_bool("SCOPE", raw).as_deref(), Ok(expected));
        }
        assert!(normalize_scope_bool("SCOPE", "maybe").is_err());
    }

    #[test]
    fn self_verify_preserves_cargo_rustflags_argument_boundaries() {
        assert_eq!(
            split_plain_rustflags("--cfg\tjoined  -C opt-level=2"),
            ["--cfg\tjoined", "-C", "opt-level=2"]
        );
        assert_eq!(split_encoded_rustflags("--cfg\x1f\x1fvalue\x1f"), ["--cfg", "", "value", ""]);
        assert!(split_encoded_rustflags("").is_empty());
    }

    #[test]
    fn inherited_verifier_policy_is_removed_from_rustc_and_rustdoc_vectors() {
        let (kept, removed) = strip_inherited_verifier_words(vec![
            "-Copt-level=2".to_string(),
            "-Ztrust-policy=advisory".to_string(),
            "-Z".to_string(),
            "trust-verify-level=0".to_string(),
            "-Zunrelated=yes".to_string(),
        ]);
        assert_eq!(kept, ["-Copt-level=2", "-Zunrelated=yes"]);
        assert_eq!(removed, ["-Ztrust-policy=advisory", "-Z trust-verify-level=0"]);
    }

    #[test]
    fn inherited_rustc_equivalent_policy_spellings_are_removed_from_every_flag_protocol() {
        let fixtures = [
            (
                "plain rustflags/rustdocflags",
                split_plain_rustflags(
                    "-Copt-level=2 -Ztrust_verify=off -Z trust_verify-level=0 -Zcodegen_backend=/tmp/forged.dylib",
                ),
            ),
            (
                "encoded rustflags/rustdocflags",
                split_encoded_rustflags(
                    "-Copt-level=2\x1f-Ztrust_verify_output=human\x1f-Z\x1ftrust-verify_session=forged",
                ),
            ),
            (
                "bootstrap rustflags/rustdocflags",
                split_env_words("-Copt-level=2 -Ztrust_verify_full=false -Z trust-verify=off"),
            ),
        ];

        for (channel, words) in fixtures {
            let (kept, removed) = strip_inherited_verifier_words(words);
            assert_eq!(kept, ["-Copt-level=2"], "{channel}");
            let expected_removed = if channel == "plain rustflags/rustdocflags" { 3 } else { 2 };
            assert_eq!(removed.len(), expected_removed, "{channel}: {removed:?}");
        }
    }

    #[test]
    fn inherited_in_process_extension_channels_fail_closed_in_every_flag_protocol() {
        for (variable, words) in [
            ("RUSTFLAGS", split_plain_rustflags("-Zllvm_plugins=/tmp/forged.dylib")),
            (
                "CARGO_ENCODED_RUSTFLAGS",
                split_encoded_rustflags("--codegen\x1fllvm_args=-load=/tmp/forged.dylib"),
            ),
            ("RUSTFLAGS_BOOTSTRAP", split_env_words("-Cllvm-args=-load=/tmp/forged.dylib")),
        ] {
            let error = reject_uninspectable_inherited_flags(variable, &words)
                .expect_err("in-process extension channel must fail closed");
            assert!(error.contains(variable), "{error}");
            assert!(error.contains("in-process LLVM"), "{error}");
        }
    }

    #[test]
    fn inherited_argfiles_and_semantic_separator_fail_closed() {
        for (variable, words) in [
            ("RUSTFLAGS", vec!["@policy.args".to_string()]),
            ("RUSTDOCFLAGS", vec!["@shell:policy.args".to_string()]),
            ("CARGO_ENCODED_RUSTFLAGS", vec!["-Copt-level=2".to_string(), "--".to_string()]),
            ("CARGO_ENCODED_RUSTDOCFLAGS", vec!["--".to_string(), "-Ztrust-verify=off".to_string()]),
        ] {
            let error = reject_uninspectable_inherited_flags(variable, &words)
                .expect_err("uninspectable inherited compiler vector must reject");
            assert!(error.contains(variable), "{error}");
        }
    }

    #[test]
    fn worker_thread_scope_is_one_bounded_integer_not_an_argument_channel() {
        for accepted in ["1", "2", "256"] {
            assert_eq!(
                normalize_worker_threads(Some(accepted)).unwrap().as_deref(),
                Some(accepted)
            );
        }
        for rejected in ["0", "257", "", " 3", "3 ", "3 -Z trust-verify=off", "abc"] {
            if rejected.is_empty() {
                assert_eq!(normalize_worker_threads(Some(rejected)).unwrap(), None);
            } else {
                assert!(normalize_worker_threads(Some(rejected)).is_err(), "accepted {rejected:?}");
            }
        }
    }

    #[test]
    fn outcome_classifier_fails_closed_for_aliases_and_unrecognized_statuses() {
        assert_eq!(normalize_outcome(Some("timed-out")), "timed_out");
        assert_eq!(normalize_outcome(Some("TimedOut")), "timed_out");
        assert_eq!(normalize_outcome(Some("runtime checked")), "runtime_checked");
        assert_eq!(normalize_outcome(Some("no verification")), "no_verification");
        assert_eq!(normalize_outcome(Some("Unverified")), "unverified");

        assert_eq!(classify_outcome("proved"), OutcomeClass::Proved);
        assert_eq!(classify_outcome("timed_out"), OutcomeClass::Incomplete);
        assert_eq!(classify_outcome("no_verification"), OutcomeClass::Incomplete);
        assert_eq!(classify_outcome("unverified"), OutcomeClass::Incomplete);
        assert_eq!(classify_outcome("solver_gave_up"), OutcomeClass::Unrecognized);
    }

    #[test]
    fn proof_binding_requires_publishable_same_artifact_materialization() {
        let root =
            env::temp_dir().join(format!("targo-trust-proof-binding-{}", std::process::id()));
        fs::create_dir_all(&root).expect("create proof root");
        let root = root.canonicalize().expect("canonical proof root");
        let owner = "obligation:test:0";
        let native_id = "trust_ir-native-trust-wp-request-1-proof-1";
        let input = bound_transport_artifact(
            "NormalizedObligation",
            b"normalized obligation\n",
            native_id,
            owner,
            vec![],
            Some(&root),
        );
        let transcript = bound_transport_artifact(
            "SolverTranscript",
            b"solver transcript\n",
            native_id,
            owner,
            vec![trust_types::TransportArtifactReference {
                kind: input.kind.clone(),
                digest: input.digest.clone().expect("input digest"),
            }],
            Some(&root),
        );
        let solver_digest = transcript.digest.as_ref().expect("solver digest").value.clone();
        let check = bound_transport_artifact(
            "ProofCheckReport",
            b"proof check\n",
            native_id,
            owner,
            vec![trust_types::TransportArtifactReference {
                kind: transcript.kind.clone(),
                digest: transcript.digest.clone().expect("solver digest"),
            }],
            Some(&root),
        );
        let check_digest = check.digest.as_ref().expect("check digest").value.clone();
        let strength = trust_types::ProofStrength::deductive();
        let mut row = trust_types::TransportObligationResult {
            obligation_id: Some(owner.to_string()),
            claim_digest_sha256: None,
            kind: "self-build".to_string(),
            typed_kind: None,
            description: "native proof".to_string(),
            location: None,
            outcome: trust_types::Outcome::Proved,
            solver: "trust-wp".to_string(),
            time_ms: 1,
            counterexample: None,
            counterexample_model: None,
            reason: None,
            design_mandate: false,
            native_trust_ir: Some(trust_types::TransportNativeTrustIrEvidence {
                suite: "trust-wp".to_string(),
                backend: "trust-wp".to_string(),
                request_id: Some("1".to_string()),
                native_id: Some(native_id.to_string()),
                present: true,
                artifacts: native_shape_artifacts("trust-wp", "1", "1"),
                diagnostics: Vec::new(),
            }),
            proof_evidence: Some(trust_types::TransportProofEvidence {
                suite: "trust-wp".to_string(),
                backend: "trust-wp".to_string(),
                request_id: Some("1".to_string()),
                proof_id: Some("1".to_string()),
                native_id: Some(native_id.to_string()),
                status: trust_types::TransportProofStatus::Proved,
                strength: Some(strength.clone()),
                evidence: Some(trust_types::ProofEvidence::from(strength)),
                // Keep the transcript/check positions stable for the digest-
                // swap adversary below; DAG validation follows exact refs, not
                // vector order.
                artifacts: vec![transcript, check, input],
                diagnostics: Vec::new(),
            }),
            monitor: None,
        };

        let bound = proof_binding_summary(&row, &root);
        assert_eq!(bound["accepted"], true);
        assert_eq!(bound["publication_grade_native_proof"], true);
        assert_eq!(bound["digest_matches_materialized_path"], true);
        assert_eq!(bound["required_artifact_materialization"]["solver_transcript_bound"], true);
        assert_eq!(bound["required_artifact_materialization"]["replay_or_check_bound"], true);

        row.proof_evidence.as_mut().expect("proof").artifacts[0]
            .digest
            .as_mut()
            .expect("digest")
            .value = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".to_string();
        let mismatched_digest = proof_binding_summary(&row, &root);
        assert_eq!(mismatched_digest["repo_local_readable_path_binding"], true);
        assert_eq!(
            mismatched_digest["required_artifact_materialization"]["solver_transcript_bound"],
            false
        );
        assert_eq!(mismatched_digest["accepted"], false);

        // Cross-artifact digest/path swapping must not receive global-set
        // matching credit: neither typed artifact matches its own bytes.
        let proof = row.proof_evidence.as_mut().expect("proof");
        proof.artifacts[0].digest.as_mut().expect("solver digest").value = check_digest;
        proof.artifacts[1].digest.as_mut().expect("check digest").value = solver_digest;
        let confused_deputy = proof_binding_summary(&row, &root);
        // The aggregate remains true because the independent normalized-input
        // artifact still matches its own path. The two proof-bearing artifacts
        // must each fail their typed binding, so they cannot borrow that credit.
        assert_eq!(confused_deputy["digest_matches_materialized_path"], true);
        let artifact_evidence =
            confused_deputy["artifact_evidence"].as_array().expect("artifact evidence");
        assert_eq!(artifact_evidence[0]["digest_matches_materialized_path"], false);
        assert_eq!(artifact_evidence[1]["digest_matches_materialized_path"], false);
        assert_eq!(confused_deputy["accepted"], false);

        // Metadata is descriptive producer-controlled data, not the artifact
        // bytes. Even an artifact whose declared digest exactly matches its own
        // canonical metadata JSON must receive no materialization credit.
        let proof = row.proof_evidence.as_mut().expect("proof");
        proof.artifacts = [
            ("SolverTranscript", serde_json::json!("solver metadata")),
            ("ProofCheckReport", serde_json::json!("check metadata")),
        ]
        .into_iter()
        .map(|(kind, metadata)| trust_types::TransportEvidenceArtifact {
            kind: kind.to_string(),
            format: None,
            artifact_id: None,
            digest: Some(trust_types::TransportArtifactDigest {
                algorithm: "sha256".to_string(),
                value: format!(
                    "{:x}",
                    Sha256::digest(serde_json::to_vec(&metadata).expect("serialize metadata"))
                ),
            }),
            uri: Some(format!("artifact://trust-wp/{kind}")),
            materialization: None,
            metadata: Some(metadata),
        })
        .collect();
        let metadata_only = proof_binding_summary(&row, &root);
        assert_eq!(metadata_only["publication_grade_native_proof"], false);
        assert_eq!(metadata_only["required_artifact_materialization"]["complete"], false);
        assert_eq!(metadata_only["accepted"], false);
        assert!(
            metadata_only["artifact_evidence"]
                .as_array()
                .expect("artifact evidence")
                .iter()
                .all(|artifact| artifact["metadata_materialization_credit"] == false)
        );
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_path_evidence_rejects_oversized_artifact_before_hash_credit() {
        let root = tempfile::tempdir().expect("proof root");
        let artifact_path = root.path().join("oversized-proof-artifact");
        let artifact = File::create(&artifact_path).expect("create sparse proof artifact");
        artifact
            .set_len(trust_types::MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES as u64 + 1)
            .expect("extend sparse proof artifact");

        let evidence =
            proof_path_evidence("materialized_path", "oversized-proof-artifact", root.path());

        assert_eq!(evidence["repo_local"], true);
        assert_eq!(evidence["size_within_limit"], false);
        assert_eq!(evidence["accepted"], false);
        assert!(evidence["actual_sha256"].is_null());
    }

    #[test]
    fn logical_target_and_evidence_manifest_are_independent_authorities() {
        let root = test_repo_root("targo-trust-self-verify-manifest-authority");
        let manifest = root.join("evidence-subject/Cargo.toml");
        fs::create_dir_all(manifest.parent().expect("manifest parent"))
            .expect("create manifest parent");
        fs::write(
            &manifest,
            "[package]\nname = \"evidence-subject\"\nversion = \"0.0.0\"\nedition = \"2021\"\n",
        )
        .expect("write evidence manifest");

        let options = Options::parse(&[
            "--target".to_string(),
            "stage2 full-bootstrap compiler/rustc library/std".to_string(),
            "--evidence-manifest".to_string(),
            "evidence-subject/Cargo.toml".to_string(),
        ])
        .expect("parse separate logical and evidence subjects");
        assert_eq!(options.target, "stage2 full-bootstrap compiler/rustc library/std");
        assert_eq!(options.evidence_manifest, PathBuf::from("evidence-subject/Cargo.toml"));

        let expected = expected_self_verify_package(&root, &options.evidence_manifest)
            .expect("resolve evidence package from the explicit manifest");
        assert_eq!(expected.name, "evidence-subject");
        assert_eq!(
            expected.root,
            manifest.parent().expect("manifest parent").canonicalize().expect("canonical parent")
        );
        let composition =
            composition_metadata(&options.target, &options.evidence_manifest, "release-stage");
        assert_eq!(composition["target"], options.target);
        assert_eq!(composition["evidence_manifest"], "evidence-subject/Cargo.toml");
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn default_full_verifier_non_dry_command_is_direct_manifest_scoped_targo_build() {
        let root = test_repo_root("targo-trust-self-verify-default-command");
        let targo = install_stage2_tool(&root, "targo");
        let mut options = full_verifier_options(&root);
        options.dry_run = false;
        options.target = "logical release composition label".to_string();
        options.evidence_manifest = PathBuf::from("evidence/Cargo.toml");
        options.jobs = Some("7".to_string());

        let argv = default_native_stage_argv(
            &options.repo_root,
            &options.evidence_manifest,
            options.jobs.as_deref(),
        )
        .expect("default full-verifier command");
        assert_eq!(
            argv,
            [
                targo.display().to_string(),
                "build".to_string(),
                "--message-format=json".to_string(),
                "--manifest-path".to_string(),
                "evidence/Cargo.toml".to_string(),
                "-j".to_string(),
                "7".to_string(),
            ]
        );
        assert!(!argv.iter().any(|word| word == &options.target));
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn stage2_semantics_never_treats_evidence_stdout_as_bootstrap_provenance() {
        let root = test_repo_root("targo-trust-self-verify-stage2-semantics");
        let targo = install_stage2_tool(&root, "targo");
        install_stage2_tool(&root, "trustc");
        let plan = StagePlan {
            label: "stage2-full-bootstrap".to_string(),
            description: "test stage2 full bootstrap".to_string(),
            target: "stage2 full-bootstrap compiler/rustc library/std".to_string(),
            evidence_manifest: PathBuf::from("targo-trust/Cargo.toml"),
            argv: targo_bootstrap_command(&root, &targo),
            timeout_sec: DEFAULT_TIMEOUT_SEC,
            env: BTreeMap::new(),
            env_policy: Value::Null,
            verification_session: "test-session".to_string(),
            stage2_toolchain: None,
            _proof_artifact_root: SelfVerifyProofArtifactRoot::create()
                .expect("create proof artifact root"),
        };

        let semantics = stage2_bootstrap_semantics(&plan);
        assert_eq!(semantics["evidence_command_only"], true);
        assert_eq!(semantics["bootstrap_stdout_parsed_as_evidence"], false);
        assert_eq!(semantics["bootstrap_rebuild_is_separate_phase"], true);
        assert_eq!(semantics["delegated_build_command_detected"], false);
        assert_eq!(semantics["native_bootstrap_runner_detected"], false);
        assert_eq!(semantics["full_bootstrap_requested"], false);
        assert_eq!(semantics["rebuild_claimed"], false);
        let _ = fs::remove_dir_all(root);
    }

    fn cargo_semantics_fixture(mode: &str) -> trust_types::CargoUnitSemanticsReport {
        trust_types::CargoUnitSemanticsReport {
            schema: "targo.trust-unit-semantics.v1".to_string(),
            features: Vec::new(),
            target_cfg: vec!["target_arch = \"x86_64\"".to_string(), "unix".to_string()],
            cfg_test: matches!(mode, "test" | "check-test" | "doctest"),
            target_edition: "2024".to_string(),
            target_crate_types: vec!["rlib".to_string()],
            target_harness: true,
            target_proc_macro: false,
            profile: trust_types::CargoUnitProfileSemanticsReport {
                opt_level: "0".to_string(),
                requested_lto: "false".to_string(),
                effective_lto: "only-object".to_string(),
                codegen_backend: None,
                codegen_units: None,
                debuginfo: "0".to_string(),
                split_debuginfo: None,
                debug_assertions: false,
                overflow_checks: false,
                rpath: false,
                incremental: false,
                panic: "unwind".to_string(),
                strip: "none".to_string(),
                rustflags: Vec::new(),
                trim_paths: None,
                hint_mostly_unused: None,
            },
            compiler: trust_types::CargoUnitCompilerSemanticsReport {
                frontend: "rustc".to_string(),
                codegen_backend: "trust-cg".to_string(),
                rustc_release: "1.99.0-nightly".to_string(),
                rustc_commit_hash: Some("a".repeat(40)),
                rustc_host: "x86_64-unknown-linux-gnu".to_string(),
                rustc_verbose_version_sha256: "b".repeat(64),
            },
            unit_rustflags: vec!["-Zcodegen-backend=trust-cg".to_string()],
            manifest_lint_rustflags: Vec::new(),
            extra_compiler_args: Vec::new(),
        }
    }

    fn cargo_identity_fixture(proof_unit_index: u64, proof_unit_role: &str) -> CargoTargetIdentity {
        let semantics = cargo_semantics_fixture("build");
        CargoTargetIdentity {
            package_id: format!("path+file:///workspace/shared-{proof_unit_role}#shared@0.1.0"),
            package_name: "shared".to_string(),
            target_name: "shared".to_string(),
            target_kinds: vec!["lib".to_string()],
            compile_target: "x86_64-unknown-linux-gnu".to_string(),
            compile_mode: "build".to_string(),
            compile_kind: "target".to_string(),
            unit_identity_sha256: "c".repeat(64),
            compile_target_spec_sha256: None,
            proof_unit_index,
            proof_unit_mode: "build".to_string(),
            proof_unit_role: proof_unit_role.to_string(),
            semantics_sha256: cargo_unit_semantics_sha256(&semantics).unwrap(),
        }
    }

    fn canonical_inventory_fixture(
        targets: &[CargoTargetIdentity],
        include_dependencies: bool,
        excluded: &[CargoTargetIdentity],
    ) -> Value {
        let unit = |target: &CargoTargetIdentity| {
            let semantics = cargo_semantics_fixture(&target.proof_unit_mode);
            assert_eq!(target.semantics_sha256, cargo_unit_semantics_sha256(&semantics).unwrap());
            json!({
                "package_id": target.package_id,
                "package_name": target.package_name,
                "target_name": target.target_name,
                "target_kinds": target.target_kinds,
                "compile_target": target.compile_target,
                "compile_target_spec_sha256": target.compile_target_spec_sha256,
                "proof_unit_index": target.proof_unit_index,
                "proof_unit_mode": target.proof_unit_mode,
                "proof_unit_role": target.proof_unit_role,
                "graph_role": target.proof_unit_role,
                "semantics_sha256": target.semantics_sha256,
                "semantics": semantics,
            })
        };
        let excluded_unit = |target: &CargoTargetIdentity| {
            let semantics = cargo_semantics_fixture(&target.proof_unit_mode);
            json!({
                "package_id": target.package_id,
                "package_name": target.package_name,
                "target_name": target.target_name,
                "target_kinds": target.target_kinds,
                "compile_target": target.compile_target,
                "compile_target_spec_sha256": target.compile_target_spec_sha256,
                "proof_unit_index": target.proof_unit_index,
                "proof_unit_mode": target.proof_unit_mode,
                "proof_unit_role": "excluded",
                "graph_role": "dependency",
                "exclusion_reason": "dependency-policy-excluded",
                "semantics_sha256": target.semantics_sha256,
                "semantics": semantics,
            })
        };
        let mut primary_roots = Vec::new();
        let mut test_execution_units = Vec::new();
        let mut dependency_units = Vec::new();
        for target in targets {
            match target.proof_unit_role.as_str() {
                "primary" => primary_roots.push(unit(target)),
                "test-execution" => test_execution_units.push(unit(target)),
                "dependency" => dependency_units.push(unit(target)),
                role => panic!("unsupported proof fixture role {role:?}"),
            }
        }
        let partitions = json!({
            "primary_roots": primary_roots,
            "test_execution_units": test_execution_units,
            "dependency_units": dependency_units,
        });
        let raw = json!({
            "schema": trust_types::CARGO_PROOF_INVENTORY_REPORT_SCHEMA_V2,
            "include_dependencies": include_dependencies,
            "declared": partitions,
            "completed": partitions,
            "covered": partitions,
            "excluded_active_units": excluded.iter().map(excluded_unit).collect::<Vec<_>>(),
        });
        let typed: trust_types::CargoProofInventoryReport =
            serde_json::from_value(raw).expect("typed Cargo proof inventory fixture");
        serde_json::to_value(typed).expect("canonical Cargo proof inventory fixture")
    }

    fn complete_target_identity_report(targets: &[CargoTargetIdentity]) -> Value {
        let raw_function = "shared::identical_path";
        let completed_targets =
            targets.iter().map(CargoTargetIdentity::report_label).collect::<Vec<_>>();
        let target_identities = targets.iter().map(cargo_target_identity_json).collect::<Vec<_>>();
        let functions = targets
            .iter()
            .map(|target| cargo_scoped_function(target, raw_function))
            .collect::<Vec<_>>();
        let verification_rows = targets
            .iter()
            .enumerate()
            .map(|(index, target)| {
                json!({
                    "schema": VERIFICATION_ROW_SCHEMA,
                    "source": "stage.stdout.log",
                    "line": index + 1,
                    "cargo_target": cargo_target_identity_json(target),
                    "function": cargo_scoped_function(target, raw_function),
                    "raw_function": raw_function,
                    "row_index": 0,
                    "outcome": "proved",
                    "outcome_class": "proved",
                    "proof_binding": {"accepted": true},
                })
            })
            .collect::<Vec<_>>();
        let obligation_evidence = verification_rows
            .iter()
            .map(|row| {
                json!({
                    "source": row["source"],
                    "line": row["line"],
                    "cargo_target": row["cargo_target"],
                    "function": row["function"],
                    "raw_function": row["raw_function"],
                    "row_index": row["row_index"],
                })
            })
            .collect::<Vec<_>>();
        let crate_summaries = targets
            .iter()
            .map(|target| {
                json!({
                    "type": "crate_summary",
                    "cargo_target": cargo_target_identity_json(target),
                })
            })
            .collect::<Vec<_>>();
        json!({
            "schema": SCHEMA,
            "status": "passed",
            "stages": [{}],
            "evidence_controls": {
                "exact_cargo_target_identity_required": true,
                "exact_cargo_proof_inventory_required": true,
            },
            "proof": {
                "status": "complete",
                "complete": true,
                "timeout_is_incomplete_proof": true,
            },
            "solver_suite": {
                "stage2_toolchain_identity_verified": true,
                "stage2_execution_identity_bound": true,
                "source_provenance_bound": true,
                "authenticated_cargo_transport": true,
                "transport_message_count": targets.len(),
                "completed_targets": completed_targets,
                "coverage_targets": completed_targets,
                "completed_target_identities": target_identities,
                "coverage_target_identities": target_identities,
                "cargo_proof_inventories": [canonical_inventory_fixture(targets, true, &[])],
                "coverage": {"complete": true},
                "functions": functions,
                "crate_summaries": crate_summaries,
                "obligation_rows": targets.len(),
                "outcomes": {"proved": targets.len()},
                "coverage_blockers": [],
                "verification_rows": verification_rows,
                "obligation_evidence": obligation_evidence,
                "all_unknown_routing": {"detected": false},
            },
        })
    }

    #[test]
    fn authenticated_cargo_units_scope_identical_raw_function_paths() {
        let primary = cargo_identity_fixture(0, "primary");
        let dependency = cargo_identity_fixture(1, "dependency");
        let message = json!({
            "type": "function_result",
            "function": "shared::identical_path",
            "total": 1,
            "results": [{
                "kind": "assertion",
                "description": "identity regression fixture",
                "outcome": "unknown",
                "solver": "fixture",
                "time_ms": 1,
            }],
        });
        let proof_root = tempfile::tempdir().expect("proof root");
        let mut summary = TransportSummary::default();
        ingest_transport_message(
            &mut summary,
            &primary,
            &message,
            proof_root.path(),
            "stage.stdout.log",
            1,
        );
        ingest_transport_message(
            &mut summary,
            &dependency,
            &message,
            proof_root.path(),
            "stage.stdout.log",
            2,
        );

        assert_eq!(summary.functions.len(), 2);
        assert_ne!(summary.functions[0], summary.functions[1]);
        assert!(summary.functions[0].starts_with(&primary.report_label()));
        assert!(summary.functions[1].starts_with(&dependency.report_label()));
        let rows = &summary.verification_rows;
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0]["raw_function"], rows[1]["raw_function"]);
        assert_ne!(rows[0]["function"], rows[1]["function"]);
        assert_eq!(rows[0]["cargo_target"]["proof_unit_role"], "primary");
        assert_eq!(rows[1]["cargo_target"]["proof_unit_role"], "dependency");
    }

    #[test]
    fn complete_report_validation_rejects_dropped_or_aliased_cargo_identity() {
        let targets =
            [cargo_identity_fixture(0, "primary"), cargo_identity_fixture(1, "dependency")];
        let report = complete_target_identity_report(&targets);
        validate_report_payload(&report).expect("exact target-scoped complete report");

        let mut inventory_dropped = report.clone();
        inventory_dropped["solver_suite"]
            .as_object_mut()
            .expect("solver suite")
            .remove("cargo_proof_inventories");
        let error = validate_report_payload(&inventory_dropped)
            .expect_err("serialized complete report requires the exact Cargo proof frontier");
        assert!(error.contains("Cargo proof inventory"), "{error}");

        let mut aliased = report.clone();
        aliased["solver_suite"]["verification_rows"][1]["function"] =
            aliased["solver_suite"]["verification_rows"][0]["function"].clone();
        let error = validate_report_payload(&aliased)
            .expect_err("one Cargo unit must not borrow another unit's function scope");
        assert!(error.contains("exact Cargo target identity"), "{error}");

        let mut dropped = report;
        dropped["solver_suite"]["verification_rows"][1]
            .as_object_mut()
            .expect("verification row")
            .remove("cargo_target");
        let error = validate_report_payload(&dropped)
            .expect_err("complete report rows require their authenticated Cargo target");
        assert!(error.contains("missing `cargo_target`"), "{error}");
    }

    #[test]
    fn complete_proof_requires_closed_dependency_inclusive_cargo_inventory() {
        let target = cargo_identity_fixture(0, "primary");
        let report = complete_target_identity_report(std::slice::from_ref(&target));
        let suite = report["solver_suite"].clone();
        let baseline = evaluate_proof("passed", Some(0), false, &suite);
        assert_eq!(baseline["status"], "complete", "{baseline}");

        let mut missing = suite.clone();
        missing.as_object_mut().expect("solver suite").remove("cargo_proof_inventories");
        let proof = evaluate_proof("passed", Some(0), false, &missing);
        assert_eq!(proof["complete"], false);
        assert!(
            proof["reasons"]
                .as_array()
                .expect("proof reasons")
                .iter()
                .filter_map(Value::as_str)
                .any(|reason| reason.contains("canonical Cargo proof inventory")),
            "{proof}"
        );

        let mut dependency_excluded = suite.clone();
        dependency_excluded["cargo_proof_inventories"][0]["include_dependencies"] =
            Value::Bool(false);
        let proof = evaluate_proof("passed", Some(0), false, &dependency_excluded);
        assert_eq!(proof["complete"], false);
        assert!(
            proof["reasons"]
                .as_array()
                .expect("proof reasons")
                .iter()
                .filter_map(Value::as_str)
                .any(|reason| reason.contains("include_dependencies=true")),
            "{proof}"
        );

        let mut dropped_completion = suite.clone();
        dropped_completion["cargo_proof_inventories"][0]["completed"]["primary_roots"] = json!([]);
        let proof = evaluate_proof("passed", Some(0), false, &dropped_completion);
        assert_eq!(proof["complete"], false);
        assert!(
            proof["reasons"]
                .as_array()
                .expect("proof reasons")
                .iter()
                .filter_map(Value::as_str)
                .any(|reason| reason.contains("declared and completed")),
            "{proof}"
        );

        let mut excluded = target.clone();
        excluded.proof_unit_index = 1;
        excluded.proof_unit_role = "excluded".to_string();
        let mut active_exclusion = suite;
        active_exclusion["cargo_proof_inventories"][0] = canonical_inventory_fixture(
            std::slice::from_ref(&target),
            true,
            std::slice::from_ref(&excluded),
        );
        let proof = evaluate_proof("passed", Some(0), false, &active_exclusion);
        assert_eq!(proof["complete"], false);
        assert!(
            proof["reasons"]
                .as_array()
                .expect("proof reasons")
                .iter()
                .filter_map(Value::as_str)
                .any(|reason| reason.contains("excluded active Cargo Unit")),
            "{proof}"
        );
    }

    #[test]
    fn aggregate_solver_suite_preserves_each_stage_cargo_inventory() {
        let first = cargo_identity_fixture(0, "primary");
        let mut second = cargo_identity_fixture(1, "primary");
        second.package_id = "path+file:///workspace/second#second@0.1.0".to_string();
        second.package_name = "second".to_string();
        second.target_name = "second".to_string();
        let first_suite =
            complete_target_identity_report(std::slice::from_ref(&first))["solver_suite"].clone();
        let second_suite =
            complete_target_identity_report(std::slice::from_ref(&second))["solver_suite"].clone();
        let aggregate = aggregate_report_solver_suite(&[
            json!({"status": "passed", "solver_suite": first_suite}),
            json!({"status": "passed", "solver_suite": second_suite}),
        ]);
        assert_eq!(
            aggregate["cargo_proof_inventories"].as_array().expect("aggregate inventories").len(),
            2
        );
        assert!(
            aggregate["transport_inconsistencies"]
                .as_array()
                .expect("aggregate inconsistencies")
                .is_empty(),
            "{aggregate}"
        );
    }

    #[test]
    fn incomplete_legacy_report_does_not_claim_new_target_identity_authority() {
        let legacy = json!({
            "schema": SCHEMA,
            "status": "incomplete",
            "stages": [{}],
            "proof": {
                "status": "incomplete",
                "complete": false,
                "timeout_is_incomplete_proof": true,
            },
        });
        validate_report_payload(&legacy).expect("incomplete legacy report remains readable");
    }

    #[test]
    fn execution_identity_gap_prevents_complete_proof() {
        let target = cargo_identity_fixture(0, "primary");
        let target_label = target.report_label();
        let target_identity = cargo_target_identity_json(&target);
        let mut summary = TransportSummary {
            stage2_toolchain_identity_verified: true,
            stage2_execution_identity_bound: false,
            source_provenance_bound: true,
            authenticated_cargo_transport: true,
            completed_targets: vec![target_label.clone()],
            coverage_targets: vec![target_label.clone()],
            completed_target_identities: BTreeMap::from([(
                target_label.clone(),
                target_identity.clone(),
            )]),
            coverage_target_identities: BTreeMap::from([(target_label, target_identity)]),
            cargo_proof_inventories: vec![canonical_inventory_fixture(
                std::slice::from_ref(&target),
                true,
                &[],
            )],
            coverage_eligible: 1,
            coverage_processed: 1,
            coverage_complete: true,
            messages: 1,
            obligation_rows: 1,
            reported_obligations: 1,
            ..TransportSummary::default()
        };
        summary.outcomes.insert("proved".to_string(), 1);
        let mut suite = solver_suite_json(&summary);
        let proof = evaluate_proof("passed", Some(0), false, &suite);
        assert_eq!(proof["status"], "incomplete");
        assert_eq!(proof["complete"], false);
        assert!(
            proof["reasons"]
                .as_array()
                .expect("proof reasons")
                .iter()
                .filter_map(Value::as_str)
                .any(|reason| reason.contains("exact executable bytes")),
            "missing execution binding was not surfaced: {proof}"
        );

        suite["stage2_execution_identity_bound"] = Value::Bool(true);
        let hypothetically_bound = evaluate_proof("passed", Some(0), false, &suite);
        assert_eq!(hypothetically_bound["status"], "complete");
        assert_eq!(hypothetically_bound["complete"], true);
    }

    #[test]
    fn source_provenance_gap_prevents_complete_proof() {
        let target = cargo_identity_fixture(0, "primary");
        let mut report = complete_target_identity_report(std::slice::from_ref(&target));
        report["solver_suite"]["source_provenance_bound"] = Value::Bool(false);

        let proof = evaluate_proof("passed", Some(0), false, &report["solver_suite"]);
        assert_eq!(proof["status"], "incomplete");
        assert_eq!(proof["complete"], false);
        assert!(
            proof["reasons"]
                .as_array()
                .expect("proof reasons")
                .iter()
                .filter_map(Value::as_str)
                .any(|reason| reason.contains("not source provenance")),
            "{proof}"
        );

        let error = validate_report_payload(&report)
            .expect_err("a serialized complete claim must bind source provenance");
        assert!(error.contains("source tree, index, submodules"), "{error}");
    }

    #[test]
    fn loader_authority_environment_names_are_scrubbed_portably_and_case_insensitively() {
        for key in [
            "LD_PRELOAD",
            "ld_library_path",
            "DYLD_INSERT_LIBRARIES",
            "DyLd_Framework_Path",
            "LIBPATH",
            "libpath",
            "SHLIB_PATH",
            "shlib_path",
            "LDR_PRELOAD",
            "ldr_config",
            "_RLD_LIST",
            "_rld_root",
        ] {
            assert!(is_loader_authority_env_key(key), "loader authority {key} was accepted");
        }
        for key in ["LD", "DYLD", "LIBPATH_EXTRA", "SHLIB_PATH_EXTRA", "RLD_PRELOAD"] {
            assert!(!is_loader_authority_env_key(key), "unrelated key {key} was overmatched");
        }
    }

    #[test]
    fn stage2_tool_paths_use_the_platform_executable_suffix() {
        for tool in ["targo", "trustc", "trustdoc", "trustd"] {
            assert_eq!(stage2_tool_file_name(tool), format!("{tool}{}", env::consts::EXE_SUFFIX));
        }
    }

    #[test]
    fn run_id_and_report_path_reject_traversal() {
        for run_id in ["", ".", "..", "../escape", "nested/run", "back\\slash"] {
            assert!(validate_run_id(run_id).is_err(), "accepted unsafe run id {run_id:?}");
        }
        assert!(validate_run_id("safe-run_2026.07").is_ok());

        let root = test_repo_root("targo-trust-self-verify-run-id-traversal");
        let mut options = full_verifier_options(&root);
        options.full_verifier = false;
        options.run_id = "../escape".to_string();
        assert!(resolve_report_dir(&options).is_err());
        options.run_id = "safe".to_string();
        options.report_dir = Some(PathBuf::from("reports/../escape"));
        assert!(resolve_report_dir(&options).is_err());
        let _ = fs::remove_dir_all(root);
    }

    #[cfg(unix)]
    #[test]
    fn report_persistence_is_private_exclusive_and_rejects_symlink_ancestors() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path().canonicalize().expect("canonical tempdir");
        let report_dir = create_private_report_directory(&root.join("reports/run"))
            .expect("create private report directory");
        assert_eq!(
            fs::metadata(&report_dir).expect("report metadata").permissions().mode() & 0o777,
            0o700
        );
        let report_path = report_dir.join(REPORT_NAME);
        write_report(&report_path, &json!({"status": "test"})).expect("publish report");
        assert_eq!(
            fs::metadata(&report_path).expect("report metadata").permissions().mode() & 0o777,
            0o600
        );
        assert!(
            write_report(&report_path, &json!({"status": "replacement"})).is_err(),
            "report publication replaced an existing path"
        );
        assert!(
            fs::read_dir(&report_dir).expect("list report directory").all(|entry| !entry
                .expect("directory entry")
                .file_name()
                .to_string_lossy()
                .ends_with(".tmp")),
            "transactional report left a temporary file behind"
        );

        let external = root.join("external");
        fs::create_dir(&external).expect("external directory");
        symlink(&external, root.join("redirect")).expect("symlink ancestor");
        let error = create_private_report_directory(&root.join("redirect/run"))
            .expect_err("symlinked output ancestor must reject");
        assert!(error.contains("non-symlink directory"), "{error}");
    }

    #[test]
    fn stage2_identity_binds_file_objects_lengths_hashes_and_version_labels() {
        let root = test_repo_root("targo-trust-self-verify-stage2-identity");
        let label = "0123456789abcdef0123456789abcdef01234567";
        install_stage2_tool_with_contents(
            &root,
            "targo",
            &unit_targo_version_script(label, "test-host", "1.99.0-test"),
        );
        install_stage2_tool_with_contents(
            &root,
            "trustc",
            &unit_compiler_version_script("trustc", label, "test-host", "1.99.0-test"),
        );
        install_stage2_tool_with_contents(
            &root,
            "trustdoc",
            &unit_compiler_version_script("trustdoc", label, "test-host", "1.99.0-test"),
        );
        install_stage2_tool_with_contents(
            &root,
            "trustd",
            &unit_trustd_version_and_server_script(label, "1.99.0-test"),
        );
        let identity = validate_stage2_toolchain(&root).expect("valid stage2 identity");
        assert_eq!(identity.targo_version.commit, label);
        assert_eq!(identity.trustc_version.commit, label);
        assert_eq!(identity.trustdoc_version.commit, label);
        assert_eq!(identity.trustd_version.commit, label);
        assert_eq!(identity.targo_version.binary, "targo");
        assert_eq!(identity.trustc_version.binary, "trustc");
        assert_eq!(identity.trustdoc_version.binary, "trustdoc");
        assert_eq!(identity.trustd_version.binary, "trustd");
        assert_eq!(identity.trustd_version.protocol, trust_router::coordinator::STATUS_VERSION);
        assert!(identity.targo.size_bytes > 0);
        assert!(identity.trustc.size_bytes > 0);
        assert!(identity.trustdoc.size_bytes > 0);
        assert!(identity.trustd.size_bytes > 0);
        assert_eq!(identity.trustd_protocol_smoke.is_some(), cfg!(unix));
        #[cfg(unix)]
        {
            let smoke = identity.trustd_protocol_smoke.as_ref().expect("Unix trustd smoke");
            assert_eq!(smoke.ping_response, "PONG");
            assert_eq!(smoke.reservation_bytes, 1);
            assert_eq!(smoke.reservation_label, TRUSTD_SMOKE_RESERVATION_LABEL);
            assert!(smoke.reservation_pid > 0);
            assert!(smoke.reservation_token > 0);
            assert_eq!(smoke.status_before.reserved_bytes, 0);
            assert_eq!(smoke.status_reserved.reserved_bytes, 1);
            assert_eq!(smoke.status_released.reserved_bytes, 0);
            assert_eq!(
                smoke.transcript_sha256,
                format!("{:x}", Sha256::digest(smoke.transcript.as_bytes()))
            );
        }

        let stale = "1111111111111111111111111111111111111111";
        install_stage2_tool_with_contents(
            &root,
            "trustc",
            &unit_compiler_version_script("trustc", stale, "test-host", "1.99.0-test"),
        );
        let error = validate_stage2_toolchain(&root).expect_err("mismatched labels must reject");
        assert!(error.contains("commit-label consistency"), "{error}");
        assert!(error.contains("not source provenance"), "{error}");
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn full_verifier_reconstructs_nonempty_stage2_native_runtime_environment() {
        let root = test_repo_root("targo-trust-self-verify-stage2-runtime");
        let label = "0123456789abcdef0123456789abcdef01234567";
        for (tool, script) in [
            ("targo", unit_targo_version_script(label, "test-host", "1.99.0-test")),
            ("trustc", unit_compiler_version_script("trustc", label, "test-host", "1.99.0-test")),
            (
                "trustdoc",
                unit_compiler_version_script("trustdoc", label, "test-host", "1.99.0-test"),
            ),
            ("trustd", unit_trustd_version_and_server_script(label, "1.99.0-test")),
        ] {
            install_stage2_tool_with_contents(&root, tool, &script);
        }
        let lib = root.join("build/host/stage2/lib");
        let rustlib = lib.join("rustlib/test-host/lib");
        fs::create_dir_all(&rustlib).expect("stage2 runtime directories");
        let manifest = root.join(DEFAULT_EVIDENCE_MANIFEST);
        fs::create_dir_all(manifest.parent().expect("manifest parent"))
            .expect("evidence package directory");
        fs::write(
            &manifest,
            "[package]\nname = \"rustc_middle\"\nversion = \"0.0.0\"\nedition = \"2021\"\n",
        )
        .expect("evidence manifest");

        let plan = build_stage_plan(&full_verifier_options(&root))
            .expect("full verifier plan with runtime closure");
        let (variable, expected) = native_runtime_environment(
            &plan.stage2_toolchain.as_ref().unwrap().trustc.canonical_path,
        )
        .expect("nonempty native runtime environment");
        assert_eq!(plan.env.get(variable).map(String::as_str), expected.to_str());
        assert_eq!(plan.env_policy["pinned_native_runtime_environment"]["variable"], variable);
        assert_eq!(
            plan.env_policy["pinned_native_runtime_environment"]["value"],
            expected.to_str().expect("test paths are UTF-8")
        );
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn verbose_version_identity_requires_exact_branding_unique_atomic_fields_and_cross_tool_agreement()
     {
        let commit = "0123456789abcdef0123456789abcdef01234567";
        let targo = parse_targo_version_identity(&format!(
            "targo 1.99.0-test\nrelease: 1.99.0-test\ncommit-hash: {commit}\nhost: test-host\n"
        ))
        .expect("valid Targo identity");
        let trustc = parse_compiler_version_identity(
            "trustc",
            &format!(
                "rustc 1.99.0-test (trustc)\nbinary: trustc\ncommit-hash: {commit}\nhost: test-host\nrelease: 1.99.0-test\n"
            ),
        )
        .expect("valid trustc identity");
        let trustdoc = parse_compiler_version_identity(
            "trustdoc",
            &format!(
                "rustc 1.99.0-test (trustdoc)\nbinary: trustdoc\ncommit-hash: {commit}\nhost: test-host\nrelease: 1.99.0-test\n"
            ),
        )
        .expect("valid trustdoc identity");
        let trustd = parse_trustd_version_identity(&format!(
            "trustd 1.99.0-test\ntrust.identity=trustd\ntrust.protocol={}\ncommit-hash: {commit}\n",
            trust_router::coordinator::STATUS_VERSION,
        ))
        .expect("valid trustd identity");
        validate_cross_tool_version_identity(&targo, &trustc, &trustdoc, &trustd)
            .expect("matching cross-tool identity");
        let valid_trustdoc = trustdoc.clone();
        let valid_trustd = trustd.clone();

        for invalid in [
            format!(
                "rustc 1.99.0-test\nbinary: rustc\ncommit-hash: {commit}\nhost: test-host\nrelease: 1.99.0-test\n"
            ),
            format!(
                "trustc 1.99.0-test\nbinary: trustc\ncommit-hash: {commit}\nhost: test-host\nrelease: 1.99.0-test\n"
            ),
            format!(
                "rustc 1.99.0-test\nbinary: trustc\nbinary: trustc\ncommit-hash: {commit}\nhost: test-host\nrelease: 1.99.0-test\n"
            ),
            format!(
                "rustc 1.99.0-test\nbinary: trustc\ncommit-hash: {commit}\nhost: test-host\nhost: test-host\nrelease: 1.99.0-test\n"
            ),
            format!(
                "rustc 1.99.0-test\nbinary: trustc\ncommit-hash: {commit}\ncommit-hash: {commit}\nhost: test-host\nrelease: 1.99.0-test\n"
            ),
            format!(
                "rustc 1.99.0-test\nbinary: trustc\ncommit-hash: {commit}\nhost: test-host\nrelease: 1.99.0-test\nrelease: 1.99.0-test\n"
            ),
            format!(
                "rustc 1.99.0-test\nbinary:trustc\ncommit-hash: {commit}\nhost: test-host\nrelease: 1.99.0-test\n"
            ),
            "rustc 1.99.0-test\nbinary: trustc\ncommit-hash: short\nhost: test-host\nrelease: 1.99.0-test\n"
                .to_string(),
        ] {
            assert!(
                parse_compiler_version_identity("trustc", &invalid).is_err(),
                "accepted invalid trustc identity: {invalid:?}"
            );
        }

        let missing_targo_commit = "targo 1.99.0-test\nrelease: 1.99.0-test\nhost: test-host\n";
        let error = parse_targo_version_identity(missing_targo_commit)
            .expect_err("stage2 Targo commit identity is mandatory");
        assert!(error.contains("CARGO_COMMIT_HASH wiring"), "{error}");
        assert!(
            parse_targo_version_identity(&format!(
                "cargo 1.99.0-test\nrelease: 1.99.0-test\ncommit-hash: {commit}\nhost: test-host\n"
            ))
            .is_err()
        );
        for invalid in [
            format!(
                "daemon 1.99.0-test\ntrust.identity=trustd\ntrust.protocol={}\ncommit-hash: {commit}\n",
                trust_router::coordinator::STATUS_VERSION,
            ),
            format!(
                "trustd 1.99.0-test\ntrust.identity=other\ntrust.protocol={}\ncommit-hash: {commit}\n",
                trust_router::coordinator::STATUS_VERSION,
            ),
            format!(
                "trustd 1.99.0-test\ntrust.identity=trustd\ntrust.identity=trustd\ntrust.protocol={}\ncommit-hash: {commit}\n",
                trust_router::coordinator::STATUS_VERSION,
            ),
            format!(
                "trustd 1.99.0-test\ntrust.identity=trustd\ntrust.protocol=wrong.v1\ncommit-hash: {commit}\n"
            ),
            format!(
                "trustd 1.99.0-test\ntrust.identity=trustd\ntrust.protocol={}\ncommit-hash: {commit}\ntrust-repo-commit-hash: 1111111111111111111111111111111111111111\n",
                trust_router::coordinator::STATUS_VERSION,
            ),
            "trustd 1.99.0-test\ntrust.identity=trustd\ntrust.protocol=trustd.status.v1\ncommit-hash: unbound\n"
                .to_string(),
        ] {
            assert!(
                parse_trustd_version_identity(&invalid).is_err(),
                "accepted invalid trustd identity: {invalid:?}"
            );
        }

        let mut mismatch = trustdoc.clone();
        mismatch.host = "other-host".to_string();
        assert!(
            validate_cross_tool_version_identity(&targo, &trustc, &mismatch, &valid_trustd)
                .is_err()
        );
        mismatch = trustdoc.clone();
        mismatch.release = "other-release".to_string();
        assert!(
            validate_cross_tool_version_identity(&targo, &trustc, &mismatch, &valid_trustd)
                .is_err()
        );
        mismatch = trustdoc;
        mismatch.commit = "1111111111111111111111111111111111111111".to_string();
        assert!(
            validate_cross_tool_version_identity(&targo, &trustc, &mismatch, &valid_trustd)
                .is_err()
        );

        let mut targo_mismatch = targo.clone();
        targo_mismatch.host = "other-host".to_string();
        assert!(
            validate_cross_tool_version_identity(
                &targo_mismatch,
                &trustc,
                &valid_trustdoc,
                &valid_trustd,
            )
            .is_err()
        );
        targo_mismatch = targo.clone();
        targo_mismatch.release = "other-release".to_string();
        assert!(
            validate_cross_tool_version_identity(
                &targo_mismatch,
                &trustc,
                &valid_trustdoc,
                &valid_trustd,
            )
            .is_err()
        );
        targo_mismatch = targo.clone();
        targo_mismatch.commit = "2222222222222222222222222222222222222222".to_string();
        assert!(
            validate_cross_tool_version_identity(
                &targo_mismatch,
                &trustc,
                &valid_trustdoc,
                &valid_trustd,
            )
            .is_err()
        );

        let mut trustd_mismatch = valid_trustd;
        trustd_mismatch.commit = "3333333333333333333333333333333333333333".to_string();
        assert!(
            validate_cross_tool_version_identity(
                &targo,
                &trustc,
                &valid_trustdoc,
                &trustd_mismatch,
            )
            .is_err()
        );
    }

    #[test]
    fn verbose_version_identity_accepts_sha1_and_sha256_object_ids_only() {
        assert!(is_full_version_commit_label(&"a".repeat(40)));
        assert!(is_full_version_commit_label(&"b".repeat(64)));
        assert!(!is_full_version_commit_label(&"c".repeat(39)));
        assert!(!is_full_version_commit_label(&"d".repeat(63)));
        assert!(!is_full_version_commit_label(&format!("{}g", "e".repeat(39))));
    }

    #[cfg(windows)]
    #[test]
    fn windows_file_object_identity_uses_full_file_id_info() {
        let root = test_repo_root("targo-trust-self-verify-windows-file-identity");
        fs::create_dir_all(&root).expect("identity fixture root");
        let first = root.join("first");
        let second = root.join("second");
        fs::write(&first, b"same").expect("first identity file");
        fs::write(&second, b"same").expect("second identity file");
        let first_identity = file_object_identity(&File::open(&first).expect("open first"))
            .expect("first Windows identity");
        let second_identity = file_object_identity(&File::open(&second).expect("open second"))
            .expect("second Windows identity");
        assert_ne!(
            first_identity, second_identity,
            "distinct live files must not collapse to size/mtime identity"
        );
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn stage2_identity_rejects_oversized_executable_before_hashing() {
        let root = test_repo_root("targo-trust-self-verify-stage2-size");
        let bin = root.join("build/host/stage2/bin");
        fs::create_dir_all(&bin).expect("stage2 bin");
        let path = bin.join(stage2_tool_file_name("trustc"));
        let file = File::create(&path).expect("create sparse executable");
        file.set_len(MAX_STAGE2_EXECUTABLE_BYTES as u64 + 1).expect("extend sparse executable");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;

            fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).expect("mark executable");
        }
        let error = validate_stage2_executable(&bin, "trustc")
            .expect_err("oversized stage2 executable must reject");
        assert!(error.contains("outside the required"), "{error}");
        let _ = fs::remove_dir_all(root);
    }

    #[cfg(unix)]
    #[test]
    fn stage_timeout_terminates_background_descendants() {
        let root = test_repo_root("targo-trust-self-verify-process-tree");
        let report_dir = create_private_report_directory(&root.join("report"))
            .expect("private report directory");
        let child_pid_path = root.join("background.pid");
        let script = format!(
            "sleep 30 & child=$!; printf '%s' \"$child\" > '{}'; wait",
            child_pid_path.display()
        );
        let plan = StagePlan {
            label: "../../untrusted-stage-label".to_string(),
            description: "process-tree timeout test".to_string(),
            target: DEFAULT_TARGET.to_string(),
            evidence_manifest: PathBuf::from(DEFAULT_EVIDENCE_MANIFEST),
            argv: vec!["/bin/sh".to_string(), "-c".to_string(), script],
            timeout_sec: 0.2,
            env: BTreeMap::new(),
            env_policy: Value::Null,
            verification_session: "test-session".to_string(),
            stage2_toolchain: None,
            _proof_artifact_root: SelfVerifyProofArtifactRoot::create()
                .expect("proof artifact root"),
        };
        let stage = run_stage(&plan, &root, &report_dir);
        assert_eq!(stage["process_timed_out"], true);
        assert_eq!(stage["process_group_isolated"], true);
        assert!(
            report_dir.join("logs").read_dir().expect("logs directory").all(|entry| !entry
                .expect("log entry")
                .file_name()
                .to_string_lossy()
                .contains("..")),
            "untrusted stage label escaped into a log filename"
        );
        let child_pid: i32 = fs::read_to_string(&child_pid_path)
            .expect("background pid")
            .parse()
            .expect("numeric pid");
        let deadline = Instant::now() + Duration::from_secs(2);
        while unsafe { libc::kill(child_pid, 0) } == 0 && Instant::now() < deadline {
            thread::sleep(Duration::from_millis(10));
        }
        assert_ne!(unsafe { libc::kill(child_pid, 0) }, 0, "timed-out descendant remained alive");
        let _ = fs::remove_dir_all(root);
    }

    fn full_verifier_options(repo_root: &Path) -> Options {
        Options {
            repo_root: repo_root.to_path_buf(),
            run_id: "test-run".to_string(),
            report_dir: None,
            target: DEFAULT_TARGET.to_string(),
            evidence_manifest: PathBuf::from(DEFAULT_EVIDENCE_MANIFEST),
            timeout_sec: DEFAULT_TIMEOUT_SEC,
            stage_label: DEFAULT_STAGE_LABEL.to_string(),
            stage_description: DEFAULT_STAGE_DESCRIPTION.to_string(),
            jobs: None,
            level: 1,
            full_verifier: true,
            offline: false,
            dry_run: true,
            perf_budget_mode: PerfBudgetMode::Report,
            max_verification_wall_time_sec: None,
            max_reported_solver_time_ms: None,
            max_obligation_rows: None,
            max_cache_miss_obligations: None,
            compare_report: None,
            stage_command: None,
            raw_argv: Vec::new(),
        }
    }

    fn test_repo_root(name: &str) -> PathBuf {
        let root = env::temp_dir().join(format!("{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).expect("create test repo root");
        root.canonicalize().expect("canonical test repo root")
    }

    fn install_stage2_tool(repo_root: &Path, tool: &str) -> PathBuf {
        install_stage2_tool_with_contents(repo_root, tool, "#!/bin/sh\nexit 0\n")
    }

    fn unit_targo_version_script(commit: &str, host: &str, release: &str) -> String {
        format!(
            "#!/bin/sh\n[ \"${{1:-}}\" = \"-Vv\" ] || exit 2\nprintf 'targo {release}\\nrelease: {release}\\ncommit-hash: {commit}\\nhost: {host}\\n'\n"
        )
    }

    fn unit_compiler_version_script(tool: &str, commit: &str, host: &str, release: &str) -> String {
        format!(
            "#!/bin/sh\n[ \"${{1:-}}\" = \"-Vv\" ] || exit 2\nprintf 'rustc {release} ({tool})\\nbinary: {tool}\\ncommit-hash: {commit}\\nhost: {host}\\nrelease: {release}\\n'\n"
        )
    }

    fn unit_trustd_version_and_server_script(commit: &str, release: &str) -> String {
        let python = unit_python_interpreter();
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

    fn unit_python_interpreter() -> String {
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

    fn install_stage2_tool_with_contents(repo_root: &Path, tool: &str, contents: &str) -> PathBuf {
        let path = repo_root.join("build/host/stage2/bin").join(stage2_tool_file_name(tool));
        fs::create_dir_all(path.parent().expect("stage2 tool parent"))
            .expect("create stage2 tool parent");
        fs::write(&path, contents).expect("write stage2 tool");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mut permissions = fs::metadata(&path).expect("stage2 tool metadata").permissions();
            permissions.set_mode(0o755);
            fs::set_permissions(&path, permissions).expect("mark stage2 tool executable");
        }
        path
    }

    fn targo_bootstrap_command(repo_root: &Path, targo: &Path) -> Vec<String> {
        vec![
            targo.display().to_string(),
            "run".to_string(),
            "--locked".to_string(),
            "--offline".to_string(),
            "--manifest-path".to_string(),
            repo_root.join("src/bootstrap/Cargo.toml").display().to_string(),
            "--".to_string(),
            "build".to_string(),
            "--set".to_string(),
            "build.full-bootstrap=true".to_string(),
            "--stage".to_string(),
            "2".to_string(),
            "compiler/rustc".to_string(),
            "library/std".to_string(),
        ]
    }
}
