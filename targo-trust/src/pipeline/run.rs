// Compiler invocation and rewrite loop entry points.
//
// Builds the native trustc command line for single-file vs. targo-driven crate
// invocations, spawns the compiler, streams stderr through the transport parser, and
// renders a VerificationReport. Also hosts the rewrite loop fallback that drives
// prove -> strengthen -> backprop convergence against the in-tree trustc.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::fs::{File, OpenOptions};
use std::io::{BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, ExitStatus, Stdio};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use std::{env, thread};

use sha2::{Digest as _, Sha256};

use super::backend::{
    CargoRustflags, append_codegen_backend_args, append_strict_safety_check_args,
    append_trust_cg_codegen_args, append_verification_mode_args, canonical_rustc_option_name,
    canonicalize_strict_safety_codegen_args, canonicalize_trust_cg_codegen_args,
    find_codegen_help_arg, find_forbidden_in_process_codegen_arg,
    inherited_trust_rustflags_warning, level_to_num, merged_cargo_rustflags_with_options,
    targo_owned_z_option, validate_direct_trust_cg_rlib_target,
};
use super::cargo_selection::{
    CargoSelectionArgs, ResolvedCargoSelection, effective_cargo_target_with_targo,
    preflight_trust_cg_cargo_targets_with_targo, resolve_cargo_selection_with_targo,
    validate_trust_cg_effective_target,
};
use super::discovery::{is_cargo_program, native_trust_cargo_path};
use super::hardened::{
    GateDecision, GateLane, OutcomeCounts, aggregate_coverage, evaluate_run_gate,
    hardened_profile_name, hardened_proof_gate_failure_for_results, memory_safe_gate_counts,
    partition_outcome_counts,
};
use super::probe::apply_native_runtime_env;
use super::process_environment::scrub_proof_compiler_authority_env;
use super::provenance::{
    print_runtime_binary_source_backpropagation_blocker,
    runtime_binary_source_provenance_for_rewrite_loop,
};
use super::transport::{
    CargoCompilerEvidence, CargoTargetIdentity, CargoTestExecutable, ParsedCompilerOutput,
    cargo_proof_inventory_report, cargo_report_subject, parse_cargo_json_stdout,
    parse_cargo_json_stdout_for_test, parse_compiler_stderr, parse_untrusted_cargo_stderr,
};
use super::trustflags::{TrustFlags, trustflags_from_env};
use crate::cli::SubcommandArgs;
use crate::config::TrustConfig;
use crate::report::{
    CertifiedTestExecutableReport, CertifiedTestExecutionCompletionScope,
    CertifiedTestExecutionPhaseState, CertifiedTestExecutionReport, CompilerDiagnostic,
    LiveCanonicalReport, LiveTransportAuthority, ReportConfig, UnsafeMemoryReportRequest,
    VerificationReport, cargo_active_exclusion_labels, cargo_gate_failing_exclusion_labels,
};
use crate::rewrite_loop::ProofFrontier;
use crate::types::{OutputFormat, Subcommand, VerificationResult};

const COMPILER_PROCESS_TIMEOUT: Duration = Duration::from_secs(2 * 60 * 60);
const COMPILER_OUTPUT_CLOSE_TIMEOUT: Duration = Duration::from_secs(30);

fn certified_test_execution_platform_blocker() -> Option<&'static str> {
    #[cfg(all(target_os = "linux", any(target_arch = "x86_64", target_arch = "aarch64")))]
    {
        None
    }
    #[cfg(not(all(target_os = "linux", any(target_arch = "x86_64", target_arch = "aarch64"))))]
    {
        Some(
            "evidence-grade Cargo test execution requires Linux x86-64/aarch64 sealed-memfd execveat; this platform has no implemented immutable execution handle",
        )
    }
}

fn record_certified_test_execution_error(
    execution: Option<&mut CertifiedTestExecutionReport>,
    phase_b_started: bool,
    error: &str,
) {
    if let Some(execution) = execution {
        execution.phase_b_state = if phase_b_started {
            CertifiedTestExecutionPhaseState::Started
        } else {
            CertifiedTestExecutionPhaseState::Blocked
        };
        execution.phase_b_exit = None;
        execution.blocker = Some(error.to_string());
    }
}

struct CompilerProcessGuard {
    #[cfg(unix)]
    pid: u32,
    #[cfg(unix)]
    cancel: Option<mpsc::Sender<()>>,
    #[cfg(unix)]
    watcher: Option<thread::JoinHandle<()>>,
    timed_out: Arc<AtomicBool>,
    timeout: Duration,
    #[cfg(not(unix))]
    deadline: Option<Instant>,
}

impl CompilerProcessGuard {
    fn configure(command: &mut Command) {
        crate::bounded_process::configure_process_group(command);
    }

    fn start(pid: u32, timeout: Duration) -> Self {
        let timed_out = Arc::new(AtomicBool::new(false));
        #[cfg(unix)]
        {
            let (sender, receiver) = mpsc::channel();
            let timed_out_for_thread = Arc::clone(&timed_out);
            let watcher = thread::spawn(move || {
                if matches!(receiver.recv_timeout(timeout), Err(RecvTimeoutError::Timeout)) {
                    timed_out_for_thread.store(true, Ordering::Release);
                    let _ = crate::bounded_process::terminate_process_group(pid);
                }
            });
            Self { pid, cancel: Some(sender), watcher: Some(watcher), timed_out, timeout }
        }
        #[cfg(not(unix))]
        {
            let _ = pid;
            Self { timed_out, timeout, deadline: Instant::now().checked_add(timeout) }
        }
    }

    fn finish(mut self) -> Result<(), String> {
        self.cancel_watcher();
        let timed_out = self.timed_out.load(Ordering::Acquire);
        if timed_out {
            Err(format!("compiler process exceeded the {:?} timeout", self.timeout))
        } else {
            Ok(())
        }
    }

    fn cancel_watcher(&mut self) {
        #[cfg(unix)]
        {
            if let Some(cancel) = self.cancel.take() {
                let _ = cancel.send(());
            }
            if let Some(watcher) = self.watcher.take() {
                let _ = watcher.join();
            }
        }
    }

    fn abort_before_reap(&mut self) {
        self.cancel_watcher();
        #[cfg(unix)]
        let _ = crate::bounded_process::terminate_process_group(self.pid);
    }
}

impl Drop for CompilerProcessGuard {
    fn drop(&mut self) {
        self.cancel_watcher();
    }
}

fn wait_for_compiler_process(
    child: &mut std::process::Child,
    guard: &mut CompilerProcessGuard,
) -> std::io::Result<ExitStatus> {
    #[cfg(unix)]
    {
        let pid = child.id();
        loop {
            let exited = match crate::bounded_process::exited_without_reaping(child) {
                Ok(exited) => exited,
                Err(error) => {
                    guard.abort_before_reap();
                    return Err(error);
                }
            };
            if exited {
                // The unreaped leader reserves this PID as the group's PGID,
                // so terminating the group here cannot race PID reuse.
                guard.cancel_watcher();
                let _ = crate::bounded_process::terminate_process_group(pid);
                return child.wait();
            }
            thread::sleep(Duration::from_millis(10));
        }
    }
    #[cfg(not(unix))]
    {
        // `std::process` can bound and reap the leader portably, but it cannot
        // contain arbitrary descendants. Windows job-object integration (or
        // the corresponding facility on another non-Unix target) is required
        // before this branch can make the Unix process-group guarantee.
        wait_for_compiler_leader_until(child, guard.deadline, &guard.timed_out)
    }
}

#[cfg(any(not(unix), test))]
fn wait_for_compiler_leader_until(
    child: &mut std::process::Child,
    deadline: Option<Instant>,
    timed_out: &AtomicBool,
) -> std::io::Result<ExitStatus> {
    loop {
        match child.try_wait() {
            Ok(Some(status)) => return Ok(status),
            Ok(None) if deadline.map_or(true, |deadline| Instant::now() >= deadline) => {
                timed_out.store(true, Ordering::Release);
                // The leader may exit between `try_wait` and `kill`; waiting
                // unconditionally both resolves that race and guarantees reap.
                let _ = child.kill();
                return child.wait();
            }
            Ok(None) => {
                let remaining = deadline
                    .expect("non-expired compiler deadline")
                    .saturating_duration_since(Instant::now());
                thread::sleep(remaining.min(Duration::from_millis(10)));
            }
            Err(error) => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(error);
            }
        }
    }
}

fn spawn_compiler_stderr_parser(
    stderr: std::process::ChildStderr,
    crate_mode: bool,
    echo: bool,
    supports_json_transport: bool,
    expected_session: String,
    strict_artifact_policy: bool,
) -> mpsc::Receiver<Result<ParsedCompilerOutput, String>> {
    let (sender, receiver) = mpsc::sync_channel(1);
    thread::spawn(move || {
        let parsed = if crate_mode {
            let mut parsed = ParsedCompilerOutput::default();
            parsed.compiler_diagnostics =
                parse_untrusted_cargo_stderr(BufReader::new(stderr), echo);
            Ok(parsed)
        } else {
            parse_compiler_stderr(BufReader::new(stderr), echo)
                .require_structured_json_transport(supports_json_transport)
                .require_raw_coverage_authentication(&expected_session, strict_artifact_policy)
        };
        let _ = sender.send(parsed);
    });
    receiver
}

fn spawn_cargo_stdout_parser(
    stdout: std::process::ChildStdout,
    selected: BTreeMap<String, String>,
    expected_session: String,
    require_authenticated_coverage: bool,
    cargo_execution_mode: bool,
) -> mpsc::Receiver<Result<CargoCompilerEvidence, String>> {
    let (sender, receiver) = mpsc::sync_channel(1);
    thread::spawn(move || {
        // `targo trust test` and `targo trust bench` compile execution
        // harnesses, then multiplex their untrusted stdout after Cargo's
        // authenticated build-finished boundary. The execution-mode parser
        // accepts that suffix without ever feeding it back into proof parsing.
        // Ordinary check/build keeps the strict all-JSON parser.
        let parsed = if cargo_execution_mode {
            parse_cargo_json_stdout_for_test(
                BufReader::new(stdout),
                &selected,
                &expected_session,
                require_authenticated_coverage,
            )
        } else {
            parse_cargo_json_stdout(
                BufReader::new(stdout),
                &selected,
                &expected_session,
                require_authenticated_coverage,
            )
        };
        let _ = sender.send(parsed);
    });
    receiver
}

fn receive_compiler_output<T>(
    receiver: mpsc::Receiver<Result<T, String>>,
    channel: &str,
) -> Result<T, String> {
    match receiver.recv_timeout(COMPILER_OUTPUT_CLOSE_TIMEOUT) {
        Ok(result) => result,
        Err(RecvTimeoutError::Timeout) => Err(format!(
            "{channel} remained open more than {COMPILER_OUTPUT_CLOSE_TIMEOUT:?} after the compiler leader exited; an uncontained descendant may still own the pipe"
        )),
        Err(RecvTimeoutError::Disconnected) => {
            Err(format!("{channel} parser terminated without returning a result"))
        }
    }
}

// ---------------------------------------------------------------------------
// Utility functions (used by pipeline and main)
// ---------------------------------------------------------------------------

pub(crate) fn has_output_path_flag(args: &[String]) -> bool {
    args.iter().any(|arg| {
        arg == "-o"
            || (arg.starts_with("-o") && arg.len() > 2)
            || arg == "--out-dir"
            || arg.starts_with("--out-dir=")
    })
}

/// Proof transport requires Cargo's plain `json` format. Trust evidence rides
/// rustc NOTE diagnostics (`TRUST_JSON:...`), and only plain JSON preserves
/// those diagnostics inside authenticated Cargo `compiler-message` envelopes.
/// `json-render-diagnostics` renders them directly to stderr, losing the
/// `trust_compile_target` identity that the parser intentionally requires.
/// Human-readable diagnostics are retained because the parser re-emits every
/// non-transport message's rendered text.
fn cargo_args_without_message_format(args: &[String]) -> Result<Vec<String>, String> {
    let mut output = Vec::with_capacity(args.len());
    let mut index = 0;
    while index < args.len() {
        let arg = &args[index];
        if arg == "--" {
            output.extend(args[index..].iter().cloned());
            return Ok(output);
        }
        if arg == "--message-format" {
            index += 1;
            if args.get(index).is_none_or(|value| value.is_empty() || value.starts_with('-')) {
                return Err("--message-format requires a value".to_string());
            }
        } else if arg.starts_with("--message-format=") {
            if arg == "--message-format=" {
                return Err("--message-format requires a value".to_string());
            }
        } else {
            output.push(arg.clone());
        }
        index += 1;
    }
    Ok(output)
}

fn insert_cargo_arg_before_passthrough(args: &mut Vec<String>, arg: impl Into<String>) {
    let index = args.iter().position(|candidate| candidate == "--").unwrap_or(args.len());
    args.insert(index, arg.into());
}

fn cargo_args_with_proof_message_format(args: &[String]) -> Result<Vec<String>, String> {
    let mut output = cargo_args_without_message_format(args)?;
    insert_cargo_arg_before_passthrough(&mut output, "--message-format=json");
    Ok(output)
}

fn cargo_arg_before_passthrough(args: &[String], predicate: impl Fn(&str) -> bool) -> bool {
    args.iter().take_while(|arg| arg.as_str() != "--").any(|arg| predicate(arg))
}

fn cargo_test_has_explicit_target_selector(args: &[String]) -> bool {
    cargo_arg_before_passthrough(args.get(1..).unwrap_or_default(), |arg| {
        matches!(arg, "--lib" | "--bins" | "--examples" | "--tests" | "--benches" | "--all-targets")
            || ["--bin=", "--example=", "--test=", "--bench="]
                .iter()
                .any(|prefix| arg.starts_with(prefix))
            || matches!(arg, "--bin" | "--example" | "--test" | "--bench")
    })
}

/// Validate the currently supported evidence-grade Cargo test surface and
/// remove caller-selected message formats. Cargo does not precompile doctests
/// under `--no-run`; until rustdoc exposes an authenticated reusable
/// executable lane, explicit doctest-only requests fail closed.
fn cargo_test_non_doc_args(args: &[String]) -> Result<Vec<String>, String> {
    if !args.first().is_some_and(|arg| arg == "test") {
        return Err("internal error: Cargo test argument normalization received another command"
            .to_string());
    }
    if cargo_arg_before_passthrough(args, |arg| arg == "--doc") {
        return Err(
            "evidence-grade `targo trust test --doc` is unavailable: Cargo/rustdoc cannot precompile and authenticate reusable doctest executables"
                .to_string(),
        );
    }
    cargo_args_without_message_format(args)
}

fn cargo_test_compile_only_args(args: &[String]) -> Result<Vec<String>, String> {
    // Preserve Cargo's default non-doc compile filter, including examples it
    // compiles but does not execute. `--no-run` already prevents rustdoc's
    // separate doctest compile/execute lane.
    let mut output = cargo_test_non_doc_args(args)?;
    if !cargo_arg_before_passthrough(&output, |arg| arg == "--no-run") {
        insert_cargo_arg_before_passthrough(&mut output, "--no-run");
    }
    insert_cargo_arg_before_passthrough(&mut output, "--message-format=json");
    Ok(output)
}

fn cargo_test_execution_args(args: &[String]) -> Result<Vec<String>, String> {
    let had_selector = cargo_test_has_explicit_target_selector(args);
    let mut output = cargo_test_non_doc_args(args)?;
    if cargo_arg_before_passthrough(&output, |arg| arg == "--no-run") {
        return Err(
            "internal error: a compile-only Cargo test request has no execution phase".to_string()
        );
    }
    // Default `cargo test` would proceed to doctests after unit/integration
    // tests. Select all ordinary test targets only in phase B; phase A above
    // already retained Cargo's broader default compile coverage.
    if !had_selector {
        insert_cargo_arg_before_passthrough(&mut output, "--tests");
    }
    Ok(output)
}

/// Authenticate the child Targo path against the selected compiler and use
/// that exact executable for Cargo metadata/package selection. Re-discovering
/// a frontend after command construction could bind coverage to one Targo and
/// execute another.
pub(super) fn resolve_cargo_selection_for_compiler(
    args: &[String],
    rustc_path: &Path,
    program: &str,
) -> Result<ResolvedCargoSelection, String> {
    let expected_targo = native_trust_cargo_path(rustc_path)?;
    let actual_targo = Path::new(program);
    let expected_identity = expected_targo.canonicalize().map_err(|error| {
        format!(
            "could not resolve selected compiler's sibling Targo `{}`: {error}",
            expected_targo.display()
        )
    })?;
    let actual_identity = actual_targo.canonicalize().map_err(|error| {
        format!("could not resolve invoked Targo `{}`: {error}", actual_targo.display())
    })?;
    if actual_identity != expected_identity {
        return Err(format!(
            "invoked Targo `{}` is not the authenticated sibling `{}` of selected compiler `{}`",
            actual_targo.display(),
            expected_targo.display(),
            rustc_path.display()
        ));
    }
    resolve_cargo_selection_with_targo(args, &expected_targo)
}

pub(super) fn single_file_report_subject(args: &[String]) -> Result<String, String> {
    let source = args
        .iter()
        .find(|argument| argument.ends_with(".rs") && !argument.starts_with('-'))
        .ok_or_else(|| {
            "single-file verification command omitted its Rust source path".to_string()
        })?;
    let canonical = Path::new(source).canonicalize().map_err(|error| {
        format!("could not canonicalize single-file report subject `{source}`: {error}")
    })?;
    canonical_single_file_report_subject(&canonical)
}

pub(super) fn canonical_single_file_report_subject(canonical: &Path) -> Result<String, String> {
    let canonical = canonical.to_str().ok_or_else(|| {
        format!("canonical single-file report subject is not valid UTF-8: {}", canonical.display())
    })?;
    Ok(format!("single-file(source={canonical:?})"))
}

fn temp_single_file_output_path(args: &[String]) -> PathBuf {
    let stem = args
        .iter()
        .find(|arg| arg.ends_with(".rs"))
        .and_then(|arg| Path::new(arg).file_stem())
        .and_then(|stem| stem.to_str())
        .filter(|stem| !stem.is_empty())
        .unwrap_or("trust-check");
    let nanos = SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0);
    let suffix = if cfg!(windows) { ".exe" } else { "" };
    let sequence = SINGLE_FILE_OUTPUT_SEQUENCE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    env::temp_dir()
        .join(format!("targo-trust-single-{}-{nanos}-{sequence}", std::process::id()))
        .join(format!("{stem}{suffix}"))
}

static SINGLE_FILE_OUTPUT_SEQUENCE: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

struct EphemeralSingleFileOutput {
    directory: PathBuf,
}

impl Drop for EphemeralSingleFileOutput {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.directory);
    }
}

fn prepare_ephemeral_single_file_output(
    args: &[String],
    enabled: bool,
) -> std::io::Result<Option<EphemeralSingleFileOutput>> {
    if !enabled {
        return Ok(None);
    }
    let output = args
        .windows(2)
        .rev()
        .find_map(|pair| (pair[0] == "-o").then(|| PathBuf::from(&pair[1])))
        .ok_or_else(|| std::io::Error::other("missing internal single-file output path"))?;
    let directory = output
        .parent()
        .ok_or_else(|| std::io::Error::other("internal single-file output has no parent"))?
        .to_path_buf();
    std::fs::create_dir(&directory)?;
    Ok(Some(EphemeralSingleFileOutput { directory }))
}

#[cfg(test)]
pub(crate) fn compiler_help_supports_option(help: &str, option: &str) -> bool {
    help.lines().any(|line| line.contains(option))
}

fn trust_verify_disable_option(z_value: &str) -> Option<&'static str> {
    let (_name, value) =
        z_value.split_once('=').map_or((z_value, None), |(name, value)| (name, Some(value)));

    match canonical_rustc_option_name(z_value).as_ref() {
        // Unlike the Boolean opt-outs below, either value (or even a malformed
        // value) is forbidden: the retired projection is not a Targo mode.
        "contract-checks" => Some("-Z contract-checks"),
        "trust-verify=off" if rustc_bool_value(value).unwrap_or(true) => Some("-Z trust-verify=off"),
        "trust-verify" if rustc_bool_value(value) == Some(false) => Some("-Z trust-verify=false"),
        "trust-verify-full" if rustc_bool_value(value) == Some(false) => {
            Some("-Z trust-verify-full=false")
        }
        _ => None,
    }
}

fn rustc_bool_value(value: Option<&str>) -> Option<bool> {
    match value {
        None | Some("y") | Some("yes") | Some("on") | Some("true") => Some(true),
        Some("n") | Some("no") | Some("off") | Some("false") => Some(false),
        _ => None,
    }
}

pub(crate) fn find_trust_verify_disable_arg(args: &[String]) -> Option<String> {
    for (idx, arg) in args.iter().enumerate() {
        if arg == "-Z" {
            if let Some(next) = args.get(idx + 1).and_then(|next| trust_verify_disable_option(next))
            {
                return Some(next.to_string());
            }
            continue;
        }

        if let Some(option) = arg.strip_prefix("-Z").filter(|option| !option.is_empty()) {
            if let Some(disabled) = trust_verify_disable_option(option) {
                return Some(disabled.to_string());
            }
        }
    }

    None
}

fn find_retired_contract_checks_arg(args: &[String]) -> Option<String> {
    for (idx, arg) in args.iter().enumerate() {
        let option = if arg == "-Z" {
            args.get(idx + 1).map(String::as_str)
        } else {
            arg.strip_prefix("-Z").filter(|option| !option.is_empty())
        };
        if option.is_some_and(|option| canonical_rustc_option_name(option) == "contract-checks") {
            return Some("-Z contract-checks".to_string());
        }
    }
    None
}

fn find_targo_policy_override_arg(args: &[String]) -> Option<String> {
    let mut index = 0;
    while index < args.len() {
        let argument = &args[index];
        if argument == "-Z" {
            if let Some(option) = args.get(index + 1) {
                if targo_owned_z_option(option, true) {
                    return Some(format!("-Z {option}"));
                }
            }
            index += 2;
            continue;
        }
        if let Some(option) = argument.strip_prefix("-Z").filter(|option| !option.is_empty()) {
            if targo_owned_z_option(option, true) {
                return Some(format!("-Z {option}"));
            }
        }
        index += 1;
    }
    None
}

fn find_forbidden_in_process_z_arg(args: &[String]) -> Option<String> {
    let mut index = 0;
    while index < args.len() {
        let argument = &args[index];
        let option = if argument == "-Z" {
            args.get(index + 1).map(String::as_str)
        } else {
            argument.strip_prefix("-Z").filter(|option| !option.is_empty())
        };
        if option.is_some_and(|option| canonical_rustc_option_name(option) == "llvm-plugins") {
            return Some(if argument == "-Z" {
                format!("-Z {}", option.expect("matched split option"))
            } else {
                argument.clone()
            });
        }
        index += if argument == "-Z" { 2 } else { 1 };
    }
    None
}

fn dep_info_only_emit_spec(spec: &str) -> bool {
    let mut kinds = spec.split(',').filter(|kind| !kind.is_empty()).peekable();
    kinds.peek().is_some()
        && kinds.all(|kind| kind.split_once('=').map_or(kind, |(name, _)| name) == "dep-info")
}

fn find_direct_compiler_early_exit_arg(args: &[String]) -> Option<String> {
    if let Some(help) = find_codegen_help_arg(args) {
        return Some(help);
    }
    let mut index = 0;
    while index < args.len() {
        let argument = &args[index];
        if matches!(argument.as_str(), "-h" | "--help" | "-V" | "-vV" | "--version")
            || argument == "--explain"
            || argument.starts_with("--explain=")
            || argument == "--print"
            || argument.starts_with("--print=")
            || argument == "--pretty"
            || argument.starts_with("--pretty=")
        {
            return Some(argument.clone());
        }
        if argument == "--emit" {
            if let Some(spec) = args.get(index + 1) {
                if dep_info_only_emit_spec(spec) {
                    return Some(format!("--emit {spec}"));
                }
            }
            index += 2;
            continue;
        }
        if let Some(spec) = argument.strip_prefix("--emit=") {
            if dep_info_only_emit_spec(spec) {
                return Some(argument.clone());
            }
        }

        let z_option = if argument == "-Z" {
            args.get(index + 1).map(String::as_str)
        } else {
            argument.strip_prefix("-Z").filter(|option| !option.is_empty())
        };
        if let Some(option) = z_option {
            let name = canonical_rustc_option_name(option);
            // Only the `mir-only` sink truncates the compile before evidence; the
            // other `-Ztrust-dump` sinks publish alongside a normal run.
            let dump_stops_the_compile = name == "trust-dump"
                && option.split_once('=').is_some_and(|(_, value)| value.starts_with("mir-only:"));
            if dump_stops_the_compile
                || matches!(
                    name.as_ref(),
                    "help"
                        | "link-only"
                        | "ls"
                        | "no-analysis"
                        | "parse-crate-root-only"
                        | "unpretty"
                )
            {
                return Some(format!("-Z {option}"));
            }
        }
        let lint_option = if matches!(argument.as_str(), "-W" | "-A" | "-D" | "-F") {
            args.get(index + 1).map(String::as_str)
        } else {
            argument
                .get(..2)
                .filter(|prefix| matches!(*prefix, "-W" | "-A" | "-D" | "-F"))
                .and_then(|_| argument.get(2..))
                .filter(|option| !option.is_empty())
        };
        if lint_option == Some("help") {
            return Some(argument.clone());
        }
        index += if matches!(argument.as_str(), "-Z" | "-W" | "-A" | "-D" | "-F") { 2 } else { 1 };
    }
    None
}

/// Reject compiler argument constructs whose effective token stream is not the
/// one inspected by targo-trust. rustc expands every `@path` argument before
/// parsing options (including `@shell:path` when shell argfiles are enabled),
/// while `--` changes the meaning of every argument that follows it. A direct
/// evidence-grade invocation must therefore use an explicit, inspectable argv;
/// otherwise an argfile can hide a policy override or a separator can strand
/// canonical safety flags outside the option parser.
fn validate_direct_rustc_passthrough(args: &[String]) -> Result<(), String> {
    if let Some(argfile) = args.iter().find(|argument| argument.starts_with('@')) {
        return Err(format!(
            "direct evidence-grade compiler arguments cannot contain response or shell argfiles (`{argfile}`); pass each rustc argument explicitly"
        ));
    }
    if args.iter().any(|argument| argument == "--") {
        return Err(
            "direct evidence-grade compiler arguments cannot contain a semantic `--` separator; pass the Rust source and each rustc option explicitly"
                .to_string(),
        );
    }
    if let Some(flag) = find_forbidden_in_process_z_arg(args) {
        return Err(format!(
            "direct evidence-grade compiler argument `{flag}` loads plugin code inside trustc; in-process extension channels are forbidden"
        ));
    }
    if direct_rustc_uses_retired_valtree_node_limit(args) {
        return Err(
            "direct evidence-grade compiler arguments use retired `-Zvaltree-node-limit`; verified compilations enforce rustc's fixed valtree resource limit"
                .to_string(),
        );
    }
    if let Some(flag) = find_forbidden_in_process_codegen_arg(args) {
        return Err(format!(
            "direct evidence-grade compiler argument `{flag}` can load LLVM plugin code inside trustc; in-process extension channels are forbidden"
        ));
    }
    if let Some(flag) = find_direct_compiler_early_exit_arg(args) {
        return Err(format!(
            "direct evidence-grade compiler argument `{flag}` exits before authenticated Trust coverage is closed"
        ));
    }
    if let Some(flag) = find_targo_policy_override_arg(args) {
        return Err(format!(
            "passthrough argument `{flag}` conflicts with targo-trust's verifier policy; use the corresponding public targo trust option"
        ));
    }
    if let Some(external) = args.iter().enumerate().find_map(|(index, argument)| {
        (argument == "--extern")
            .then(|| args.get(index + 1).cloned().unwrap_or_else(|| "<missing>".to_string()))
            .or_else(|| argument.strip_prefix("--extern=").map(str::to_string))
    }) {
        return Err(format!(
            "direct evidence-grade compiler arguments cannot authenticate whether --extern={external} loads an in-process proc macro capable of forging raw TRUSTJSON transport; use verified Cargo mode, which enforces the no-proc-macro TCB boundary"
        ));
    }
    Ok(())
}

fn direct_rustc_uses_retired_valtree_node_limit(args: &[String]) -> bool {
    args.iter().enumerate().any(|(index, argument)| {
        let z_option = if argument == "-Z" {
            args.get(index + 1).map(String::as_str)
        } else {
            argument.strip_prefix("-Z").filter(|option| !option.is_empty())
        };
        z_option.is_some_and(|option| canonical_rustc_option_name(option) == "valtree-node-limit")
    })
}

fn direct_rustc_target(args: &[String]) -> Result<Option<&str>, String> {
    let mut target = None;
    let mut target_count = 0usize;
    let mut index = 0usize;
    while index < args.len() {
        let candidate = if args[index] == "--target" {
            index += 1;
            Some(
                args.get(index)
                    .filter(|value| !value.is_empty())
                    .ok_or_else(|| "direct rustc --target requires a non-empty value".to_string())?
                    .as_str(),
            )
        } else {
            args[index]
                .strip_prefix("--target=")
                .map(|value| {
                    if value.is_empty() {
                        Err("direct rustc --target requires a non-empty value".to_string())
                    } else {
                        Ok(value)
                    }
                })
                .transpose()?
        };
        if let Some(candidate) = candidate {
            target_count += 1;
            if let Some(previous) = target {
                return Err(if previous == candidate {
                    format!(
                        "direct evidence-grade rustc received duplicate --target value `{candidate}`"
                    )
                } else {
                    format!(
                        "direct evidence-grade rustc received conflicting --target values `{previous}` and `{candidate}`"
                    )
                });
            }
            target = Some(candidate);
        }
        index += 1;
    }
    debug_assert_eq!(target_count, usize::from(target.is_some()));
    Ok(target)
}

fn validate_direct_custom_target_extension_tcb(target: &str) -> Result<(), String> {
    let target_path = Path::new(target);
    let mut candidates = Vec::new();
    if target.ends_with(".json") || target_path.components().count() > 1 {
        candidates.push(target_path.to_path_buf());
    } else if let Some(search_path) = env::var_os("RUST_TARGET_PATH") {
        candidates.extend(
            env::split_paths(&search_path)
                .map(|directory| directory.join(format!("{target}.json")))
                .filter(|path| path.exists()),
        );
    }

    for path in candidates {
        let bytes = crate::input_limits::read_bounded_file(
            &path,
            crate::input_limits::MAX_RELEASE_METADATA_BYTES,
        )
        .map_err(|error| {
            format!(
                "cannot inspect custom target `{}` before verification: {error}",
                path.display()
            )
        })?;
        let spec: serde_json::Value = serde_json::from_slice(&bytes).map_err(|error| {
            format!("cannot parse custom target `{}` before verification: {error}", path.display())
        })?;
        for key in ["llvm-args", "llvm_args"] {
            let Some(value) = spec.get(key) else { continue };
            let empty = value.as_array().is_some_and(Vec::is_empty) || value.is_null();
            if !empty {
                return Err(format!(
                    "direct evidence-grade compilation rejects non-empty custom-target `{key}` in `{}`: LLVM extension arguments execute inside trustc's proof-transport TCB",
                    path.display()
                ));
            }
        }
    }
    Ok(())
}

pub(crate) fn find_trust_verify_disable_in_rustflags(flags: &str) -> Option<String> {
    let args = flags
        .split(' ')
        .map(str::trim)
        .filter(|flag| !flag.is_empty())
        .map(str::to_string)
        .collect::<Vec<_>>();
    find_trust_verify_disable_arg(&args)
}

fn find_trust_verify_disable_in_encoded_rustflags(flags: &str) -> Option<String> {
    let args = flags.split('\x1f').map(str::to_string).collect::<Vec<_>>();
    find_trust_verify_disable_arg(&args)
}

pub(crate) fn trust_verify_disable_diagnostic(
    passthrough: &[String],
    rustc_passthrough: bool,
) -> Option<String> {
    if env::var_os("TRUST_VERIFY_FN_BUDGET_MS").is_some() {
        return Some(
            "TRUST_VERIFY_FN_BUDGET_MS is retired; set positive `function_budget_ms` in the project manifest's [trust] table"
                .to_string(),
        );
    }
    if rustc_passthrough {
        if let Some(flag) = find_trust_verify_disable_arg(passthrough) {
            return Some(format!("passthrough argument `{flag}` is not allowed"));
        }
        if let Some(flag) = find_targo_policy_override_arg(passthrough) {
            return Some(format!(
                "passthrough argument `{flag}` conflicts with targo-trust's verifier policy; \
                 use the corresponding public targo trust option"
            ));
        }
    }

    if let Ok(flags) = env::var("RUSTFLAGS") {
        if let Some(flag) = find_trust_verify_disable_in_rustflags(&flags) {
            return Some(format!("RUSTFLAGS contains `{flag}`"));
        }
    }

    if let Ok(flags) = env::var("CARGO_ENCODED_RUSTFLAGS") {
        if let Some(flag) = find_trust_verify_disable_in_encoded_rustflags(&flags) {
            return Some(format!("CARGO_ENCODED_RUSTFLAGS contains `{flag}`"));
        }
    }

    // `cargo test --doc` and future documentation-bearing verified commands
    // use Cargo's parallel rustdoc flag channels. rustdoc accepts rustc's
    // unstable session options, so the retired exec projection must be denied
    // there just as it is in the ordinary compiler flag stream.
    if let Ok(flags) = env::var("RUSTDOCFLAGS") {
        let args = flags
            .split(' ')
            .map(str::trim)
            .filter(|flag| !flag.is_empty())
            .map(str::to_string)
            .collect::<Vec<_>>();
        if let Some(flag) = find_retired_contract_checks_arg(&args) {
            return Some(format!("RUSTDOCFLAGS contains `{flag}`"));
        }
    }

    if let Ok(flags) = env::var("CARGO_ENCODED_RUSTDOCFLAGS") {
        let args = flags.split('\x1f').map(str::to_string).collect::<Vec<_>>();
        if let Some(flag) = find_retired_contract_checks_arg(&args) {
            return Some(format!("CARGO_ENCODED_RUSTDOCFLAGS contains `{flag}`"));
        }
    }

    None
}

fn apply_cargo_rustflags_env(
    cmd: &mut Command,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
    strict_artifact_policy: bool,
    allow_l0_gaps: bool,
    controls: &VerificationControls<'_>,
    trustflags: &TrustFlags,
) -> Result<(), String> {
    // The merge below strips inherited `-Ztrust-*` policy. That filter used to
    // be silent; point at TRUSTFLAGS, the sanctioned override channel, so an
    // ignored ambient flag is visible instead of a mystery.
    if let Some(warning) = inherited_trust_rustflags_warning(
        env::var("CARGO_ENCODED_RUSTFLAGS").ok().as_deref(),
        env::var("RUSTFLAGS").ok().as_deref(),
    ) {
        eprintln!("targo trust: {warning}");
    }
    // TRUSTFLAGS overrides are merged LAST, after config-derived policy and
    // the per-run verification controls, into the same rustflags value Cargo
    // fingerprints — so a TRUSTFLAGS change re-verifies affected units exactly
    // like a policy change would.
    let merged = trustflags.apply_to_cargo_rustflags(cargo_rustflags_with_controls(
        merged_cargo_rustflags_with_options(
            &config.level,
            selected_codegen_backend,
            supports_json_transport,
            strict_artifact_policy,
            allow_l0_gaps,
        ),
        controls,
    )?);
    match merged {
        CargoRustflags::Plain(flags) => {
            cmd.env("RUSTFLAGS", flags);
            cmd.env_remove("CARGO_ENCODED_RUSTFLAGS");
        }
        CargoRustflags::Encoded(flags) => {
            cmd.env("CARGO_ENCODED_RUSTFLAGS", flags);
            cmd.env_remove("RUSTFLAGS");
        }
    }
    if selected_codegen_backend == Some("trust-cg") {
        // Cargo's profile-level incremental switch is independent of
        // RUSTFLAGS. Disable it before Unit construction so no incremental
        // directory or reuse fingerprint is created for a backend that does
        // not implement incremental object reuse.
        cmd.env("CARGO_INCREMENTAL", "0");
    }
    Ok(())
}

/// The compiler's `-Ztrust-policy` domain, as selected by this run's lane.
///
/// Held as one value rather than a pair of booleans because the compiler
/// rejects the pair: emitting both `memory-safe` and `advisory` was a
/// representable state here that no compilation could accept.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TrustPolicySelection {
    Strict,
    /// Release gate: `-Ztrust-policy=certify`, full static discharge.
    Certify,
    Advisory,
    MemorySafe,
}

impl TrustPolicySelection {
    /// Resolve the lane flags the CLI carries. Memory-safe is the narrow
    /// policy and advisory the broad one, so a run that somehow asked for both
    /// gets the narrower guarantee.
    pub(crate) fn from_lane_flags(memory_safe: bool, survey: bool, certify: bool) -> Self {
        // `certify` is the tightening lane and wins over nothing — the CLI
        // rejects combining it with a loosener — but it is checked first so the
        // resolution order reads tightest-to-loosest.
        if certify {
            Self::Certify
        } else if memory_safe {
            Self::MemorySafe
        } else if survey {
            Self::Advisory
        } else {
            Self::Strict
        }
    }

    /// `None` for the compiler's own default, so a strict run's command line
    /// stays free of a redundant tracked option.
    fn option_value(self) -> Option<&'static str> {
        match self {
            Self::Strict => None,
            Self::Certify => Some("certify"),
            Self::Advisory => Some("advisory"),
            Self::MemorySafe => Some("memory-safe"),
        }
    }
}

#[derive(Clone, Copy)]
struct VerificationControls<'a> {
    policy: TrustPolicySelection,
    timeout_ms: u64,
    function_budget_ms: u64,
    hardened_profile: Option<&'a str>,
    ay_path: Option<&'a Path>,
    verification_session: &'a str,
    proof_artifact_root: &'a Path,
}

fn verification_control_options(
    controls: &VerificationControls<'_>,
) -> Result<Vec<String>, String> {
    let mut options = vec![
        format!("trust-verify-timeout-ms={}", controls.timeout_ms),
        format!("trust-verify-function-budget-ms={}", controls.function_budget_ms),
        format!("trust-verify-session={}", controls.verification_session),
    ];
    let proof_artifact_root = controls.proof_artifact_root.to_str().ok_or_else(|| {
        format!(
            "proof artifact root is not valid UTF-8: {}",
            controls.proof_artifact_root.display()
        )
    })?;
    options.push(format!("trust-proof-artifact-root={proof_artifact_root}"));
    if let Some(policy) = controls.policy.option_value() {
        options.push(format!("trust-policy={policy}"));
    }
    // The profile is the sole carrier of hardened boundary obligations, so a
    // hardened run and a raw `trustc` run with the same profile now request
    // the same obligation set.
    if let Some(profile) = controls.hardened_profile {
        options.push(format!("trust-verify-profile={profile}"));
    }
    if let Some(path) = controls.ay_path {
        let path = path
            .to_str()
            .ok_or_else(|| format!("AY executable path is not valid UTF-8: {}", path.display()))?;
        options.push(format!("trust-verify-ay-path={path}"));
    }
    if options.iter().any(|option| option.contains('\x1f')) {
        return Err(
            "verifier control values cannot contain Cargo's U+001F encoded-rustflags delimiter"
                .to_string(),
        );
    }
    Ok(options)
}

fn append_verification_control_args(
    args: &mut Vec<String>,
    controls: &VerificationControls<'_>,
) -> Result<(), String> {
    for option in verification_control_options(controls)? {
        args.push("-Z".to_string());
        args.push(option);
    }
    Ok(())
}

fn cargo_rustflags_with_controls(
    merged: CargoRustflags,
    controls: &VerificationControls<'_>,
) -> Result<CargoRustflags, String> {
    let options = verification_control_options(controls)?;
    match merged {
        CargoRustflags::Plain(mut flags) => {
            // Plain RUSTFLAGS cannot preserve whitespace inside a single
            // argument. Switch to Cargo's encoded representation when an
            // explicit path requires it.
            if options.iter().any(|option| option.chars().any(char::is_whitespace)) {
                let mut args = flags
                    .split(' ')
                    .map(str::trim)
                    .filter(|flag| !flag.is_empty())
                    .map(str::to_string)
                    .collect::<Vec<_>>();
                for option in options {
                    args.push("-Z".to_string());
                    args.push(option);
                }
                return Ok(CargoRustflags::Encoded(args.join("\x1f")));
            }
            for option in options {
                flags.push_str(" -Z ");
                flags.push_str(&option);
            }
            Ok(CargoRustflags::Plain(flags))
        }
        CargoRustflags::Encoded(mut flags) => {
            for option in options {
                flags.push_str("\x1f-Z\x1f");
                flags.push_str(&option);
            }
            Ok(CargoRustflags::Encoded(flags))
        }
    }
}

/// Remove retired ambient compiler controls from the proof subprocess. Every
/// supported proof-affecting choice is carried by a tracked `-Z` option above;
/// allowing an inherited legacy variable as a second control plane would make
/// the report, Cargo fingerprint, and verifier semantics disagree.
fn scrub_legacy_verifier_env(cmd: &mut Command) {
    for name in [
        "TRUST_VERIFY",
        "AY_DIRECT_SOLVE_TIMEOUT_MS",
        "AY_PATH",
        "TY_PATH",
        "TRUST_AY_PATH",
        "TRUST_AGGREGATE_PERTURB",
        "TRUST_BACKING_INVARIANTS",
        "TRUST_BRIDGE_GATE",
        "TRUST_CACHE_DIR",
        "TRUST_CALLEE_PERTURB",
        "TRUST_COMPILER_CACHE",
        "TRUST_DUMP_ONLY",
        "TRUST_HARDENED",
        "TRUST_INTERIOR_PERTURB",
        "TRUST_IR_FLIP",
        "TRUST_NATIVE_UNIVERSAL",
        "TRUST_NO_COMPILER_CACHE",
        "TRUST_PROFILE",
        "TRUST_PROP_UNSAT_WORK_BUDGET",
        "TRUST_PROVE_BUDGET_SECS",
        "TRUST_SOLVER",
        "TRUST_SPINE_CONTRACT_FLIP",
        "TRUST_SPINE_NATIVE_GEN",
        "TRUST_SPINE_VERDICT_FLIP",
        "TRUST_STRUCTFIELD_PERTURB",
        "TRUST_TEMPORAL_SINGLE_WRITER",
        "TRUST_TARGO_TEST_EXECUTE_FRESH_SESSION",
        "TRUST_TARGO_TEST_EXECUTION_MANIFEST",
        "TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256",
        "TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION",
        "TRUST_TARGO_TEST_MONITOR_SESSION",
        "TRUST_TYPE_LOWERING_PRODUCED_NODE_BUDGET",
        "TRUST_TY_PATH",
        "TRUST_VCGEN_BUNDLE_ADT_BUDGET",
        "TRUST_VCGEN_GENERATION_WORK_BUDGET",
        "TRUST_VCGEN_WORK_BUDGET",
        "TRUST_VERIFY_FN_BUDGET_MS",
        "TRUST_VERIFY_HARDENED",
        "TRUST_VERIFY_INCLUDE_DEPENDENCIES",
        "TRUST_VERIFY_INCLUDE_GENERATED",
        "TRUST_VERIFY_MEMORY_SAFE",
        "TRUST_VERIFY_OUTPUT",
        "TRUST_VERIFY_POLICY",
        "TRUST_VERIFY_PRIMARY_ONLY",
        "TRUST_VERIFY_SURVEY",
        "TRUST_VERIFY_TIMEOUT_MS",
        "TRUST_VERIFY_WORKER_THREADS",
        "TRUST_WP_PATH",
        "TRUST_WAVE24_PERTURB",
        "LIBPATH",
        "SHLIB_PATH",
        "LDR_PRELOAD",
    ] {
        cmd.env_remove(name);
    }
    // A verified test process must not inherit dynamic-loader injection from
    // the outer shell. Native Targo reconstructs the platform's ordinary
    // library search path for each test executable after the build; ambient
    // LD_*/DYLD_* values are not part of the authorized artifact identity.
    for (name, _) in env::vars_os() {
        if name.to_str().is_some_and(|name| name.starts_with("LD_") || name.starts_with("DYLD_")) {
            cmd.env_remove(name);
        }
    }
}

/// Establish the internal Targo→trustc monitor-mode channel. The value is the
/// same random session nonce carried by tracked `-Ztrust-verify-session`, so
/// an inherited ambient variable cannot independently select different MIR.
fn apply_targo_test_monitor_session(
    cmd: &mut Command,
    cargo_test_mode: bool,
    verification_session: &str,
) {
    // The outer process grants Targo authority to route a monitor marker; it
    // never exposes the compiler-consumed marker globally. Native Targo
    // authenticates the nonce and re-adds TRUST_TARGO_TEST_MONITOR_SESSION
    // only to selected-package runtime compilation units.
    cmd.env_remove("TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION");
    if cargo_test_mode {
        cmd.env("TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION", verification_session);
    }
}

#[allow(clippy::too_many_arguments)]
fn configured_verified_cargo_child(
    program: &str,
    effective_args: &[String],
    original_args: &[String],
    rustc_path: &Path,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
    strict_artifact_policy: bool,
    allow_l0_gaps: bool,
    controls: &VerificationControls<'_>,
    trustflags: &TrustFlags,
    cargo_selection: &ResolvedCargoSelection,
    cargo_test_mode: bool,
    execution_authority: Option<(&Path, &str)>,
) -> Result<Command, String> {
    configured_verified_cargo_child_with_memory(
        program,
        effective_args,
        original_args,
        rustc_path,
        config,
        selected_codegen_backend,
        supports_json_transport,
        strict_artifact_policy,
        allow_l0_gaps,
        controls,
        trustflags,
        cargo_selection,
        cargo_test_mode,
        execution_authority,
        apply_crate_memory_coordination,
    )
}

#[allow(clippy::too_many_arguments)]
fn configured_verified_cargo_child_with_memory<F>(
    program: &str,
    effective_args: &[String],
    original_args: &[String],
    rustc_path: &Path,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
    strict_artifact_policy: bool,
    allow_l0_gaps: bool,
    controls: &VerificationControls<'_>,
    trustflags: &TrustFlags,
    cargo_selection: &ResolvedCargoSelection,
    cargo_test_mode: bool,
    execution_authority: Option<(&Path, &str)>,
    configure_memory: F,
) -> Result<Command, String>
where
    F: FnOnce(&mut Command, &[String], Option<&Path>) -> Result<(), String>,
{
    let mut cmd = Command::new(program);
    cmd.args(effective_args);
    scrub_proof_compiler_authority_env(&mut cmd);
    scrub_legacy_verifier_env(&mut cmd);
    apply_targo_test_monitor_session(&mut cmd, cargo_test_mode, controls.verification_session);
    apply_native_runtime_env(&mut cmd, rustc_path);
    cmd.env("TRUST_TARGO_VERIFY", "1");
    apply_cargo_child_rustc_env(&mut cmd, rustc_path);
    apply_cargo_rustflags_env(
        &mut cmd,
        config,
        selected_codegen_backend,
        supports_json_transport,
        strict_artifact_policy,
        allow_l0_gaps,
        controls,
        trustflags,
    )?;
    configure_memory(&mut cmd, original_args, Some(cargo_selection.target_directory.as_path()))?;
    cmd.env_remove("TRUST_TARGO_TEST_EXECUTE_FRESH_SESSION");
    cmd.env_remove("TRUST_TARGO_TEST_EXECUTION_MANIFEST");
    cmd.env_remove("TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256");
    if let Some((authority, authority_sha256)) = execution_authority {
        cmd.env("TRUST_TARGO_TEST_EXECUTE_FRESH_SESSION", controls.verification_session);
        cmd.env("TRUST_TARGO_TEST_EXECUTION_MANIFEST", authority);
        cmd.env("TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256", authority_sha256);
    }
    Ok(cmd)
}
/// A cryptographically random 256-bit nonce injected into rustflags for one
/// Cargo proof run.
/// Cargo fingerprints the complete rustflags vector, so this forces every
/// selected target through trustc without deleting the user's build artifacts.
/// The terminal target inventory and `fresh=false` artifact events remain the
/// evidence that the invalidation actually took effect.
struct VerificationSession {
    _artifact_root: tempfile::TempDir,
    artifact_root: PathBuf,
    id: String,
}

impl VerificationSession {
    fn create() -> std::io::Result<Self> {
        let mut nonce = [0u8; 32];
        getrandom::fill(&mut nonce).map_err(|error| {
            std::io::Error::other(format!(
                "operating-system randomness failed while creating verification session: {error}"
            ))
        })?;
        let id = nonce.iter().map(|byte| format!("{byte:02x}")).collect();
        let artifact_root =
            tempfile::Builder::new().prefix("trust-proof-artifact-root-").tempdir()?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;

            let mut permissions = std::fs::symlink_metadata(artifact_root.path())?.permissions();
            permissions.set_mode(0o700);
            std::fs::set_permissions(artifact_root.path(), permissions)?;
        }
        let canonical_artifact_root = artifact_root.path().canonicalize()?;
        let metadata = std::fs::symlink_metadata(&canonical_artifact_root)?;
        if metadata.file_type().is_symlink() || !metadata.is_dir() {
            return Err(std::io::Error::other(
                "verification proof artifact root is not a non-symlink directory",
            ));
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;

            if metadata.permissions().mode() & 0o777 != 0o700 {
                return Err(std::io::Error::other(
                    "verification proof artifact root is not private (mode 0700)",
                ));
            }
        }
        Ok(Self { _artifact_root: artifact_root, artifact_root: canonical_artifact_root, id })
    }

    fn artifact_root(&self) -> &Path {
        &self.artifact_root
    }
}

const TEST_EXECUTION_AUTHORITY_SCHEMA: &str = "trust.targo-test-execution-authority.v1";

#[derive(serde::Serialize)]
struct TestExecutionAuthorityManifest<'a> {
    schema: &'static str,
    verification_session: &'a str,
    target_directory: String,
    executables: Vec<TestExecutionAuthorityEntry>,
}

#[derive(serde::Serialize)]
struct TestExecutionAuthorityEntry {
    target: String,
    path: String,
    sha256: String,
    size: u64,
}

#[derive(Debug)]
struct TestExecutionAuthority {
    path: PathBuf,
    target_directory: String,
    executables: Vec<CertifiedTestExecutableReport>,
    inventory_sha256: String,
}

fn exact_test_executable_identity(path: &Path) -> Result<(PathBuf, String, u64), String> {
    let before = std::fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect test executable `{}`: {error}", path.display()))?;
    if before.file_type().is_symlink() || !before.file_type().is_file() {
        return Err(format!(
            "test executable `{}` is not a regular non-symlink file",
            path.display()
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        if before.permissions().mode() & 0o111 == 0 {
            return Err(format!("test artifact `{}` is not executable", path.display()));
        }
    }
    let canonical = path.canonicalize().map_err(|error| {
        format!("cannot canonicalize test executable `{}`: {error}", path.display())
    })?;
    let mut file = File::open(&canonical).map_err(|error| {
        format!("cannot open test executable `{}`: {error}", canonical.display())
    })?;
    let opened = file.metadata().map_err(|error| {
        format!("cannot inspect open test executable `{}`: {error}", canonical.display())
    })?;
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let read = file.read(&mut buffer).map_err(|error| {
            format!("cannot hash test executable `{}`: {error}", canonical.display())
        })?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    let after = std::fs::symlink_metadata(&canonical).map_err(|error| {
        format!("cannot re-inspect test executable `{}`: {error}", canonical.display())
    })?;
    let stable = !after.file_type().is_symlink()
        && after.file_type().is_file()
        && before.len() == opened.len()
        && opened.len() == after.len()
        && before.modified().ok() == opened.modified().ok()
        && opened.modified().ok() == after.modified().ok();
    #[cfg(unix)]
    let stable = {
        use std::os::unix::fs::MetadataExt as _;

        stable
            && before.dev() == opened.dev()
            && opened.dev() == after.dev()
            && before.ino() == opened.ino()
            && opened.ino() == after.ino()
    };
    if !stable {
        return Err(format!(
            "test executable `{}` changed while its phase-A identity was captured",
            canonical.display()
        ));
    }
    Ok((canonical, format!("{:x}", hasher.finalize()), opened.len()))
}

fn write_test_execution_authority(
    verification_session: &VerificationSession,
    target_directory: &Path,
    toolchain_root: &Path,
    executables: &BTreeSet<CargoTestExecutable>,
) -> Result<TestExecutionAuthority, String> {
    if executables.is_empty() {
        return Err(
            "Cargo test compile phase emitted no selected-package test executables".to_string()
        );
    }
    let target_directory = target_directory.canonicalize().map_err(|error| {
        format!(
            "cannot canonicalize Cargo target directory `{}`: {error}",
            target_directory.display()
        )
    })?;
    let toolchain_root = toolchain_root.canonicalize().map_err(|error| {
        format!(
            "cannot canonicalize authenticated Trust toolchain root `{}`: {error}",
            toolchain_root.display()
        )
    })?;
    if target_directory.starts_with(&toolchain_root)
        || toolchain_root.starts_with(&target_directory)
    {
        return Err(format!(
            "Cargo target directory `{}` overlaps authenticated Trust toolchain root `{}`; project artifacts must not be able to masquerade as or mutate sysroot TCB artifacts",
            target_directory.display(),
            toolchain_root.display(),
        ));
    }
    let mut entries = Vec::with_capacity(executables.len());
    let mut paths = BTreeSet::new();
    let mut target_paths = BTreeMap::new();
    for executable in executables {
        if !executable.path.is_absolute() {
            return Err(format!(
                "selected test target `{}` emitted a non-absolute executable path `{}`",
                executable.target.report_label(),
                executable.path.display()
            ));
        }
        let (path, sha256, size) = exact_test_executable_identity(&executable.path)?;
        if sha256 != executable.phase_a_sha256 {
            return Err(format!(
                "selected test executable `{}` changed after native Targo published its phase-A byte identity (published sha256={}, observed sha256={})",
                path.display(),
                executable.phase_a_sha256,
                sha256,
            ));
        }
        if !path.starts_with(&target_directory) {
            return Err(format!(
                "selected test executable `{}` escapes Cargo target directory `{}`",
                path.display(),
                target_directory.display()
            ));
        }
        if !paths.insert(path.clone()) {
            return Err(format!(
                "Cargo emitted duplicate selected test executable `{}`",
                path.display()
            ));
        }
        if let Some(previous) = target_paths.insert(executable.target.clone(), path.clone()) {
            if previous != path {
                return Err(format!(
                    "selected Cargo target `{}` emitted ambiguous executable paths `{}` and `{}`",
                    executable.target.report_label(),
                    previous.display(),
                    path.display()
                ));
            }
        }
        let path = path.to_str().ok_or_else(|| {
            format!("test executable path `{}` is not valid UTF-8", path.display())
        })?;
        entries.push(TestExecutionAuthorityEntry {
            target: executable.target.report_label(),
            path: path.to_string(),
            sha256,
            size,
        });
    }
    entries.sort_by(|left, right| left.path.cmp(&right.path));
    let target_directory = target_directory.to_str().ok_or_else(|| {
        format!("Cargo target directory `{}` is not valid UTF-8", target_directory.display())
    })?;
    let manifest = TestExecutionAuthorityManifest {
        schema: TEST_EXECUTION_AUTHORITY_SCHEMA,
        verification_session: &verification_session.id,
        target_directory: target_directory.to_string(),
        executables: entries,
    };
    let path = verification_session.artifact_root().join("test-execution-authority.json");
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;

        options.mode(0o600);
    }
    let mut file = options
        .open(&path)
        .map_err(|error| format!("cannot create private test execution authority: {error}"))?;
    let serialized = serde_json::to_vec(&manifest)
        .map_err(|error| format!("cannot serialize test execution authority: {error}"))?;
    let inventory_sha256 = format!("{:x}", Sha256::digest(&serialized));
    file.write_all(&serialized)
        .map_err(|error| format!("cannot write private test execution authority: {error}"))?;
    file.sync_all().map_err(|error| format!("cannot persist test execution authority: {error}"))?;
    let executables = manifest
        .executables
        .into_iter()
        .map(|entry| CertifiedTestExecutableReport {
            target: entry.target,
            path: entry.path,
            sha256: entry.sha256,
            size: entry.size,
        })
        .collect();
    Ok(TestExecutionAuthority {
        path,
        target_directory: manifest.target_directory,
        executables,
        inventory_sha256,
    })
}

/// Resolve the `RUSTC` value pinned onto child cargo invocations.
///
/// Ambient overrides and compatibility aliases are never proof authority.
/// `trustc` now reports a rustc-compatible version identity directly, so Cargo
/// and build scripts no longer need a `rustc`-spelled copy, hard link, or
/// symlink. Pinning the already selected path also avoids rereading and
/// byte-comparing a mutable alias before each Cargo invocation.
pub(super) fn cargo_child_rustc_path(rustc_path: &Path) -> PathBuf {
    rustc_path.to_path_buf()
}

/// Pin `RUSTC` for a child cargo so dependency and build-script compiles use
/// the discovered Trust toolchain instead of whatever PATH resolution finds
/// (rustup shims have attempted component management against linked Trust
/// toolchains, destroying the link). Wrappers are explicitly disabled so they
/// cannot strip flags or forge compiler output.
fn apply_cargo_child_rustc_env(cmd: &mut Command, rustc_path: &Path) {
    let rustc = cargo_child_rustc_path(rustc_path);
    // Cargo exposes the same build.rustc setting through both variables;
    // CARGO_BUILD_RUSTC is the config-key spelling and can otherwise win over
    // a pinned RUSTC. Pin both to one authenticated compiler.
    cmd.env("RUSTC", &rustc);
    cmd.env("CARGO_BUILD_RUSTC", rustc);
    cmd.env("RUSTC_WRAPPER", "");
    cmd.env("RUSTC_WORKSPACE_WRAPPER", "");
    cmd.env("CARGO_BUILD_RUSTC_WRAPPER", "");
    cmd.env("CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "");
}

fn cargo_compiler_override_diagnostic(args: &[String]) -> Option<String> {
    for variable in ["RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS"] {
        if env::var_os(variable).as_deref().is_some_and(|value| value.to_str().is_none()) {
            return Some(format!(
                "{variable} is not valid Unicode; evidence-grade Targo cannot preserve its compiler-argument boundaries"
            ));
        }
    }
    for variable in [
        "RUSTC",
        "CARGO_BUILD_RUSTC",
        "RUSTC_WRAPPER",
        "CARGO_BUILD_RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
    ] {
        if env::var_os(variable).is_some_and(|value| !value.is_empty()) {
            return Some(format!(
                "{variable} is set; evidence-grade Targo invocations require the selected sibling trustc with no compiler wrapper (unset {variable})"
            ));
        }
    }
    let mut index = 0;
    while index < args.len() {
        let arg = &args[index];
        if arg == "--" {
            break;
        }
        let value = if arg == "--config" {
            index += 1;
            args.get(index).map(String::as_str)
        } else {
            arg.strip_prefix("--config=")
        };
        if let Some(value) = value {
            let key = value.split('=').next().unwrap_or_default().trim().to_ascii_lowercase();
            if key == "build.rustc"
                || key == "build.rustc-wrapper"
                || key == "build.rustc-workspace-wrapper"
                || (key.starts_with("target.")
                    && (key.ends_with(".rustc")
                        || key.ends_with(".rustc-wrapper")
                        || key.ends_with(".rustc-workspace-wrapper")))
            {
                return Some(format!(
                    "Cargo config override `{key}` is not permitted in an evidence-grade compiler invocation"
                ));
            }
        }
        index += 1;
    }
    None
}

/// A per-function verification row parsed from the compiler's TRUST_JSON
/// transport. Synthetic transport bookkeeping rows (`transport:*` kinds, e.g.
/// the `<transport>` missing-json placeholder) do not count as evidence that
/// verification ran.
fn is_per_function_verification_row(result: &VerificationResult) -> bool {
    !result.kind.starts_with("transport:")
}

/// Hard-error diagnostic for a run that collected no authenticated evidence
/// that verification actually executed. A real per-function row or coverage
/// summary proves that trustc ran; Cargo crate mode may additionally rely on
/// its authenticated terminal primary-target inventory for a valid empty
/// crate. Raw single-file mode has no Cargo inventory and therefore requires a
/// row or coverage summary even in an advisory lane. This prevents a replaced,
/// stale, or early-exiting compiler from turning an empty transport into a
/// successful zero-obligation report.
pub(super) fn missing_trust_json_diagnostic(
    crate_mode: bool,
    results: &[VerificationResult],
    completed_proof_targets: &BTreeSet<CargoTargetIdentity>,
    has_authenticated_coverage_summary: bool,
) -> Option<String> {
    if results.iter().any(is_per_function_verification_row)
        || has_authenticated_coverage_summary
        || (crate_mode && !completed_proof_targets.is_empty())
    {
        return None;
    }
    Some(
        "verification did not run: no per-function TRUST_JSON transport row, authenticated \
         coverage summary, or terminal Cargo target inventory was collected\n\
         Likely causes:\n\
         - the unique `-Z trust-verify-session` compiler-session rustflag did not reach the compiler or an authenticated primary target\n\
         - the linked Trust Cargo frontend (sibling `targo` next to trustc) is missing or was bypassed\n\
         - the selected source or Cargo targets did not invoke trustc\n\
         Note: targo-trust injects a unique compiler-session rustflag and rejects selected `fresh=true` artifacts; a warm Cargo cache is not accepted as proof evidence."
            .to_string(),
    )
}

// ---------------------------------------------------------------------------
// Build command
// ---------------------------------------------------------------------------

/// Build the command for a built local Trust compiler.
#[cfg(test)]
pub(crate) fn build_native_command(
    rustc: &Path,
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
) -> Vec<String> {
    build_native_command_with_json_transport(rustc, subcommand, sub_args, config, None, true)
        .expect("test command fixtures should include sibling targo for crate mode")
}

pub(crate) fn build_native_command_with_json_transport(
    rustc: &Path,
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
) -> Result<Vec<String>, String> {
    if sub_args.is_single_file {
        // Direct rustc invocation for a single .rs file. Verification is
        // batteries-on and the compiler's default `unscoped` role is in scope;
        // raw invocations never forge Cargo-owned role/package metadata.
        validate_direct_rustc_passthrough(&sub_args.passthrough)?;
        let strict_artifact_policy = sub_args.strict_artifact_policy();
        let passthrough = if strict_artifact_policy {
            canonicalize_strict_safety_codegen_args(&sub_args.passthrough).map_err(
                |override_arg| {
                    format!(
                        "passthrough argument `{override_arg}` conflicts with strict verification's required overflow checks and debug assertions"
                    )
                },
            )?
        } else {
            sub_args.passthrough.clone()
        };
        let direct_target = direct_rustc_target(&passthrough)?;
        if selected_codegen_backend == Some("trust-cg") {
            if let Some(target) = direct_target {
                // Trust-CG rejects every custom target (and every unaudited
                // built-in target) outright. Apply that stronger policy before
                // trying to inspect a target file so an absent custom target
                // cannot obscure the authoritative matrix diagnostic.
                validate_trust_cg_effective_target(target)?;
            }
        }
        if let Some(target) = direct_target {
            validate_direct_custom_target_extension_tcb(target)?;
        }
        let passthrough = if selected_codegen_backend == Some("trust-cg") {
            validate_direct_trust_cg_rlib_target(&passthrough).map_err(|detail| {
                format!("trust-cg can currently link only an explicit rlib target: {detail}")
            })?;
            canonicalize_trust_cg_codegen_args(&passthrough).map_err(|override_arg| {
                format!(
                    "passthrough argument `{override_arg}` conflicts with trust-cg's required -Cpanic=abort, -Cdebuginfo=0, -Ccodegen-units=1, non-incremental contract"
                )
            })?
        } else {
            passthrough
        };
        let mut cmd_args = vec![
            rustc.to_string_lossy().to_string(),
            "-Z".to_string(),
            format!("trust-verify-level={}", level_to_num(&config.level)),
        ];
        if supports_json_transport {
            cmd_args.push("-Z".to_string());
            cmd_args.push("trust-verify-output=json".to_string());
        }
        append_verification_mode_args(&mut cmd_args, sub_args.allow_l0_gaps_lane());
        append_codegen_backend_args(&mut cmd_args, selected_codegen_backend, sub_args.allow_l0_gaps_lane());
        cmd_args.extend(passthrough);
        if selected_codegen_backend == Some("trust-cg") {
            append_trust_cg_codegen_args(&mut cmd_args);
        }
        if strict_artifact_policy {
            // Append last so the effective direct-rustc policy is obvious in
            // captured argv. Explicit user attempts to own either option were
            // rejected above rather than silently reordered.
            append_strict_safety_check_args(&mut cmd_args);
        }
        if !matches!(subcommand, Subcommand::Build | Subcommand::Test)
            && !has_output_path_flag(&sub_args.passthrough)
        {
            cmd_args.push("-o".to_string());
            cmd_args
                .push(temp_single_file_output_path(&sub_args.passthrough).display().to_string());
        }
        Ok(cmd_args)
    } else {
        // targo-based invocation for a crate.
        let cargo_cmd = match subcommand {
            Subcommand::Check | Subcommand::Report | Subcommand::Loop => {
                // TrustVerify runs over optimized MIR; `cargo check` can stop
                // before that pipeline, so check/report use build-mode targo.
                "build"
            }
            Subcommand::Diff | Subcommand::Solvers | Subcommand::Init => "check",
            Subcommand::Build => "build",
            Subcommand::Test => "test",
        };
        let targo = native_trust_cargo_path(rustc)?;
        let mut cargo_args = sub_args.crate_mode_cargo_args();
        if let Some(error) = cargo_compiler_override_diagnostic(&cargo_args) {
            return Err(error);
        }
        if selected_codegen_backend == Some("trust-cg") {
            let effective_target =
                if let Some(target) = effective_cargo_target_with_targo(&cargo_args, &targo)? {
                    target
                } else {
                    let host = exact_rustc_host_triple(rustc)?;
                    insert_cargo_option_before_separator(&mut cargo_args, "--target", host.clone());
                    host
                };
            validate_trust_cg_effective_target(&effective_target)?;
            let cargo_rustc = cargo_child_rustc_path(rustc);
            preflight_trust_cg_cargo_targets_with_targo(&cargo_args, &targo, &cargo_rustc)?;
        }
        let mut cmd_args = vec![targo.to_string_lossy().to_string(), cargo_cmd.to_string()];
        cmd_args.extend(cargo_args);
        // RUSTC and RUSTFLAGS are set via env in run_compiler /
        // run_compiler_capture (apply_cargo_child_rustc_env +
        // apply_cargo_rustflags_env).
        Ok(cmd_args)
    }
}

pub(super) fn exact_rustc_host_triple(rustc: &Path) -> Result<String, String> {
    let mut command = Command::new(rustc);
    command.arg("-vV").env_clear();
    let output = crate::bounded_process::output(
        &mut command,
        &format!("selected compiler {} -vV host probe", rustc.display()),
        64 * 1024,
        Duration::from_secs(10),
    )?;
    if !output.status.success() {
        return Err(format!("{} -vV failed with {}", rustc.display(), output.status));
    }
    let stdout = String::from_utf8(output.stdout)
        .map_err(|_| format!("{} -vV output was not valid UTF-8", rustc.display()))?;
    let hosts = stdout.lines().filter_map(|line| line.strip_prefix("host: ")).collect::<Vec<_>>();
    let [host] = hosts.as_slice() else {
        return Err(format!(
            "{} -vV must report exactly one host triple, observed {}",
            rustc.display(),
            hosts.len()
        ));
    };
    if host.is_empty()
        || host.len() > 255
        || host.trim() != *host
        || !host
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'))
    {
        return Err(format!("{} -vV reported invalid host triple `{host}`", rustc.display()));
    }
    Ok((*host).to_string())
}

fn insert_cargo_option_before_separator(args: &mut Vec<String>, option: &str, value: String) {
    let index = args.iter().position(|arg| arg == "--").unwrap_or(args.len());
    args.splice(index..index, [option.to_string(), value]);
}

// ---------------------------------------------------------------------------
// Compiler execution
// ---------------------------------------------------------------------------

pub(crate) struct CompilerRun<'a> {
    pub(crate) cmd_args: &'a [String],
    pub(crate) rustc_path: &'a Path,
    pub(crate) config: &'a TrustConfig,
    pub(crate) selected_codegen_backend: Option<&'a str>,
    pub(crate) supports_json_transport: bool,
    pub(crate) strict_artifact_policy: bool,
    pub(crate) strict_result_gate: bool,
    /// `--certify`: the release gate. Selects `GateLane::Certify` (every
    /// non-proved bucket fatal) and `-Ztrust-policy=certify` (full static
    /// discharge in the compiler).
    pub(crate) certify_gate: bool,
    pub(crate) allow_l0_gaps: bool,
    pub(crate) memory_safe_policy: bool,
    pub(crate) survey: bool,
    pub(crate) hardened: bool,
    pub(crate) trust_profile: Option<&'a str>,
    pub(crate) ay_path: Option<&'a Path>,
    pub(crate) format: OutputFormat,
    pub(crate) report_dir: Option<&'a str>,
    pub(crate) unsafe_memory_report: Option<&'a UnsafeMemoryReportRequest>,
    /// Optional proof-consuming same-process workflow. The callback receives an
    /// opaque capability only after both final publication receipts validate.
    pub(crate) live_report_consumer:
        Option<&'a mut dyn FnMut(&LiveCanonicalReport) -> Result<(), String>>,
    /// Whether ordinary terminal/JSON/HTML output should be rendered. Internal
    /// reducers may suppress it only when no report artifacts were requested.
    pub(crate) render_output: bool,
    /// The command builder injected a disposable `-o` for a non-build
    /// single-file invocation. The runner owns and removes its directory.
    pub(crate) ephemeral_single_file_output: bool,
}

/// Trust: extract a `--manifest-path <path>` (or `=`-joined) value from cargo args.
fn cargo_manifest_path_arg(args: &[String]) -> Option<PathBuf> {
    CargoSelectionArgs::parse(args)
        .ok()
        .and_then(|selection| selection.manifest_path().map(Path::to_path_buf))
}

/// Return Cargo's explicit target-directory override, without interpreting
/// arguments after `--` (those belong to the compiled target). Cargo accepts
/// both spellings and gives this CLI value precedence over environment/config
/// values.
fn cargo_target_dir_arg(args: &[String]) -> Option<PathBuf> {
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        if arg == "--" {
            break;
        } else if arg == "--target-dir" {
            if let Some(path) = iter.next().filter(|path| !path.is_empty()) {
                return Some(PathBuf::from(path));
            }
        } else if let Some(path) = arg.strip_prefix("--target-dir=").filter(|path| !path.is_empty())
        {
            return Some(PathBuf::from(path));
        }
    }
    None
}

/// Trust: env var naming the optional cross-process memory-jobserver token file.
/// Normal verified crate mode never exports it: Unix requires the authenticated
/// host daemon, while platforms that cannot establish the file authority's Unix
/// ownership/locking invariants fail before Cargo fan-out.
const TRUST_MEMORY_JOBSERVER_ENV: &str = "TRUST_MEMORY_JOBSERVER";

/// Trust: env var naming the `trustd` memory-coordination daemon's Unix socket.
/// Unix crate mode exports this only after the exact packaged daemon passes its
/// identity and readiness checks. It deliberately does not export the token-file
/// transport at the same time. A selected daemon failure stops solver dispatch
/// inside a worker; launcher failure prevents the Cargo fan-out from starting.
const TRUST_MEMORY_JOBSERVER_SOCK_ENV: &str = "TRUST_MEMORY_JOBSERVER_SOCK";

/// Historical daemon opt-out. Unix verified crate mode rejects a truthy opt-out
/// and strips every spelling before workers: without a lifetime exclusion lease,
/// a file-only run could race another run's live daemon and create two
/// aggregate-budget authorities.
#[cfg(unix)]
const TRUSTD_DISABLE_ENV: &str = "TRUSTD_DISABLE";

/// Trust: is the `trustd` daemon auto-start opted out via [`TRUSTD_DISABLE_ENV`]?
/// Truthy = set to anything other than empty / `0` / `false` / `no` / `off`.
#[cfg(unix)]
fn trustd_disabled() -> bool {
    match env::var(TRUSTD_DISABLE_ENV) {
        Ok(v) => {
            let v = v.trim();
            !(v.is_empty()
                || v.eq_ignore_ascii_case("0")
                || v.eq_ignore_ascii_case("false")
                || v.eq_ignore_ascii_case("no")
                || v.eq_ignore_ascii_case("off"))
        }
        Err(_) => false,
    }
}

/// Resolve the Cargo target directory for artifacts, snapshots, and execution
/// manifests. Memory admission deliberately no longer derives authority from
/// this path. Honors Cargo's explicit `--target-dir` override first, then the
/// authoritative `target_directory` returned by the already-required
/// authenticated sibling `targo metadata` invocation. That value incorporates
/// Cargo's effective environment/config precedence. Direct environment and
/// manifest/cwd fallbacks exist only for unit-level callers without metadata.
fn cargo_target_dir(args: &[String], resolved_target_dir: Option<&Path>) -> PathBuf {
    if let Some(dir) = cargo_target_dir_arg(args) {
        return dir;
    }
    if let Some(dir) = resolved_target_dir.filter(|dir| !dir.as_os_str().is_empty()) {
        return dir.to_path_buf();
    }
    if let Some(dir) = env::var_os("CARGO_TARGET_DIR").filter(|v| !v.is_empty()) {
        return PathBuf::from(dir);
    }
    if let Some(dir) = env::var_os("CARGO_BUILD_TARGET_DIR").filter(|v| !v.is_empty()) {
        return PathBuf::from(dir);
    }
    let manifest_dir = cargo_manifest_path_arg(args)
        .and_then(|m| m.parent().map(Path::to_path_buf))
        .or_else(nearest_manifest_dir_from_cwd)
        .unwrap_or_else(|| PathBuf::from("."));
    manifest_dir.join("target")
}

/// Resolve the observational last-results snapshot root. Cargo metadata is the
/// authority for the effective target directory, except for its default
/// workspace collapse: when exactly one non-root member is selected it reports
/// `<workspace>/target`, while this per-unit snapshot belongs under the
/// selected member's source root. Explicit/custom target directories retain
/// Cargo's resolution.
fn verification_cache_target_dir(
    args: &[String],
    cargo_selection: Option<&ResolvedCargoSelection>,
) -> Option<PathBuf> {
    if let Some(selection) = cargo_selection {
        if cargo_target_dir_arg(args).is_some() {
            return Some(cargo_target_dir(args, Some(&selection.target_directory)));
        }
        if let [package] = selection.packages.as_slice() {
            let metadata_parent = selection.target_directory.parent();
            let is_default_workspace_target = selection.target_directory.file_name()
                == Some(OsStr::new("target"))
                && metadata_parent.is_some_and(|parent| {
                    parent != package.root && package.root.starts_with(parent)
                });
            if is_default_workspace_target {
                return Some(package.root.join("target"));
            }
        }
        return Some(selection.target_directory.clone());
    }

    args.iter()
        .find(|arg| arg.ends_with(".rs") && !arg.starts_with('-'))
        .and_then(|source| std::fs::canonicalize(source).ok())
        .and_then(|source| source.parent().map(|parent| parent.join("target")))
}

fn persist_verification_snapshot(
    args: &[String],
    cargo_selection: Option<&ResolvedCargoSelection>,
    results: &[VerificationResult],
) {
    let Some(target_dir) = verification_cache_target_dir(args, cargo_selection) else {
        return;
    };
    let Ok(json) = serde_json::to_vec(results) else { return };
    let path = target_dir.join("trust-cache/verification.json");
    // Observational only: publication is atomic and symlink-safe, but failure
    // to write this convenience snapshot never changes the proof verdict.
    let _ = crate::durable_io::atomic_write_private(&path, &json);
}

/// Walk up from the cwd to the nearest directory containing `Cargo.toml` —
/// cargo's own manifest resolution. Without this, a subdirectory invocation
/// computed a cwd-relative `./target`, leaking an empty target dir (and the
/// jobserver artifacts) into the caller's subdir instead of the crate root.
/// Caught by the native trust-added trustc-native root-resolution gate.
fn nearest_manifest_dir_from_cwd() -> Option<PathBuf> {
    let mut dir = env::current_dir().ok()?;
    loop {
        if dir.join("Cargo.toml").is_file() {
            return Some(dir);
        }
        if !dir.pop() {
            return None;
        }
    }
}

/// Trust: `trustd` daemon Unix-socket path for the crate-mode fan-out. The
/// endpoint is fixed inside one euid-owned 0700 runtime directory, independent
/// of Cargo target directories. Thus concurrent verified builds share one host
/// allowance instead of each admitting 70% of RAM. The coordinator helper alone
/// creates and validates that directory; callers must not `create_dir_all` it.
#[cfg(unix)]
fn memory_jobserver_socket_path() -> Result<PathBuf, String> {
    trust_router::coordinator::host_socket_path().map_err(|error| {
        format!("could not establish the private per-user trustd runtime directory: {error}")
    })
}

/// Derive crash-recovery tooling from the already selected Targo program. The
/// caller validates that Targo against the selected Trust compiler before this
/// coordinator path runs. Keep the derivation lexical so a `targo` compatibility
/// symlink still names the `trustd` in its selected sysroot, and require an
/// absolute path so the diagnostic can never recommend ambient PATH lookup.
#[cfg(unix)]
fn recovery_trustd_for_selected_targo(program: &OsStr) -> Result<PathBuf, String> {
    let targo = Path::new(program);
    if !targo.is_absolute() {
        return Err(format!(
            "selected Targo path `{}` is not absolute; refusing to suggest an ambient-PATH crash-recovery command",
            targo.display()
        ));
    }
    let bin = targo.parent().ok_or_else(|| {
        format!(
            "selected Targo path `{}` has no same-sysroot bin directory",
            targo.display()
        )
    })?;
    Ok(bin.join(format!("trustd{}", std::env::consts::EXE_SUFFIX)))
}

/// Configure the shared crate-mode memory coordinator for every compiler
/// execution path, including rewrite-loop capture iterations. Unix clears both
/// inherited transports and exports only an exact authenticated daemon socket.
/// Non-Unix currently has no authority satisfying the required filesystem
/// invariants, so it fails after non-compiling metadata selection but before
/// compilation, Cargo fan-out, or solver dispatch.
fn apply_crate_memory_coordination(
    cmd: &mut Command,
    args: &[String],
    resolved_target_dir: Option<&Path>,
) -> Result<(), String> {
    let inherited_token = env::var_os(TRUST_MEMORY_JOBSERVER_ENV);
    #[cfg(unix)]
    {
        if trustd_disabled() {
            cmd.env_remove(TRUST_MEMORY_JOBSERVER_SOCK_ENV);
            cmd.env_remove(TRUST_MEMORY_JOBSERVER_ENV);
            return Err(format!(
                "{TRUSTD_DISABLE_ENV} is unsafe for verified crate mode on Unix; unset it so the authenticated trustd authority can be established"
            ));
        }
        apply_crate_memory_coordination_with(
            cmd,
            args,
            resolved_target_dir,
            inherited_token.as_deref(),
            true,
            trust_router::coordinator::ensure_daemon,
        )
    }
    #[cfg(not(unix))]
    {
        apply_crate_memory_coordination_with(
            cmd,
            args,
            resolved_target_dir,
            inherited_token.as_deref(),
            false,
            |_| false,
        )
    }
}

fn apply_crate_memory_coordination_with<F>(
    cmd: &mut Command,
    _args: &[String],
    _resolved_target_dir: Option<&Path>,
    inherited_token: Option<&OsStr>,
    start_daemon: bool,
    ensure_daemon: F,
) -> Result<(), String>
where
    F: FnOnce(&Path) -> bool,
{
    cmd.env_remove(TRUST_MEMORY_JOBSERVER_SOCK_ENV);
    cmd.env_remove(TRUST_MEMORY_JOBSERVER_ENV);

    #[cfg(unix)]
    {
        let _ = inherited_token;
        // Targo has already interpreted the opt-out before selecting this exact
        // daemon domain. Do not propagate even a false-looking spelling into
        // workers, whose lower-level compatibility shim recognizes only `1`.
        cmd.env_remove(TRUSTD_DISABLE_ENV);
        if !start_daemon {
            return Err(format!(
                "{TRUSTD_DISABLE_ENV} cannot select a file-only authority on Unix verified crate mode"
            ));
        }
        let socket_path = memory_jobserver_socket_path()?;
        if !ensure_daemon(&socket_path) {
            let recovery_trustd = recovery_trustd_for_selected_targo(cmd.get_program())?;
            return Err(format!(
                "could not establish the selected same-sysroot trustd memory authority at {}; refusing to launch a split-authority Cargo fan-out. Confirm the sibling trustd at `{}` is installed/executable and stop any incompatible live daemon. If the prior trustd exited uncleanly, first establish that every solver it admitted is gone, then invoke the absolute executable `{}` with arguments `--recover-after-crash --confirm-no-solvers --socket {}` and retry. This absolute sibling path avoids ambient PATH selection; path derivation alone does not prove distribution provenance, packaged byte identity, or execution identity",
                socket_path.display(),
                recovery_trustd.display(),
                recovery_trustd.display(),
                socket_path.display(),
            ));
        }
        cmd.env(TRUST_MEMORY_JOBSERVER_SOCK_ENV, socket_path);
        return Ok(());
    }

    #[cfg(not(unix))]
    {
        let _ = (inherited_token, start_daemon, ensure_daemon);
        Err(format!(
            "verified crate mode is unsupported on {}: no memory-admission authority satisfies the required Unix ownership and locking invariants; refusing to launch uncoordinated workers",
            std::env::consts::OS
        ))
    }
}

/// Convert Cargo's canonical selected packages into the names used by report
/// subject and dependency-TCB accounting. Targo derives proof scope from this
/// resolved unit graph and carries role/package strings only as reporting
/// metadata; excluded units receive the explicit compiler off-switch.
/// Canonical selection handles package globs, workspace defaults/excludes,
/// partial versions, and source-qualified package IDs.
#[cfg(test)]
fn selected_package_names_from_selection(selection: &ResolvedCargoSelection) -> Option<String> {
    let mut names = selection
        .packages
        .iter()
        .map(|package| package.name.as_str())
        .filter(|name| !name.is_empty())
        .collect::<Vec<_>>();
    names.sort_unstable();
    names.dedup();
    (!names.is_empty()).then(|| names.join(","))
}

/// Preserve Cargo's source-qualified package IDs alongside display names for
/// proof-inventory authentication. Names alone are never an authority boundary:
/// one graph can contain several versions or sources with the same name.
fn selected_package_map_from_selection(
    selection: &ResolvedCargoSelection,
) -> BTreeMap<String, String> {
    selection.packages.iter().map(|package| (package.id.clone(), package.name.clone())).collect()
}

fn child_status_code(status: &ExitStatus) -> i32 {
    status.code().unwrap_or_else(|| child_signal_exit_code(status).map(i32::from).unwrap_or(1))
}

fn child_signal_exit_code(status: &ExitStatus) -> Option<u8> {
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt as _;

        return status
            .signal()
            .map(|signal| 128_i32.saturating_add(signal).min(u8::MAX.into()) as u8);
    }

    #[cfg(not(unix))]
    {
        let _ = status;
        None
    }
}

pub(super) fn live_report_consumer_rejection(
    crate_mode: bool,
    compiler_exit: i32,
    compiler_signal_exit: Option<u8>,
    cargo_proof_inventory: Option<&trust_types::CargoProofInventoryReport>,
    coverage: Option<&trust_types::VerificationCoverage>,
    missing_target_coverage: &[CargoTargetIdentity],
    raw_terminal_inventory_complete: bool,
    compiled_targets: &BTreeSet<CargoTargetIdentity>,
    observed_proof_targets: &BTreeSet<CargoTargetIdentity>,
    completed_proof_targets: &BTreeSet<CargoTargetIdentity>,
    coverage_proof_targets: &BTreeSet<CargoTargetIdentity>,
) -> Option<String> {
    if let Some(signal_exit) = compiler_signal_exit {
        return Some(format!("compiler terminated by signal (shell status {signal_exit})"));
    }
    if !matches!(compiler_exit, 0 | 1) {
        return Some(format!("compiler terminated abnormally with status {compiler_exit}"));
    }

    let active_exclusions = cargo_active_exclusion_labels(cargo_proof_inventory);
    if !active_exclusions.is_empty() {
        return Some(format!(
            "Cargo proof frontier excluded {} active Unit(s): {}",
            active_exclusions.len(),
            active_exclusions.join("; "),
        ));
    }

    let Some(coverage) = coverage else {
        return Some("authenticated coverage inventory was absent".to_string());
    };
    if !coverage.coverage_complete || coverage.processed != coverage.eligible {
        return Some(format!(
            "authenticated coverage inventory was incomplete ({} of {} functions processed)",
            coverage.processed, coverage.eligible
        ));
    }
    if !missing_target_coverage.is_empty() {
        return Some(
            "one or more completed compiler targets lacked coverage inventory".to_string(),
        );
    }

    if !crate_mode {
        return (!raw_terminal_inventory_complete).then(|| {
            "direct compiler stream lacked one complete authenticated terminal inventory"
                .to_string()
        });
    }

    if completed_proof_targets.is_empty() {
        return Some("Cargo stream lacked a completed proof-target inventory".to_string());
    }
    if observed_proof_targets != completed_proof_targets {
        return Some(
            "observed Cargo proof targets did not exactly equal completed compiler targets"
                .to_string(),
        );
    }
    if coverage_proof_targets != completed_proof_targets {
        return Some(
            "Cargo coverage targets did not exactly equal completed compiler targets".to_string(),
        );
    }
    if !compiled_targets.is_subset(completed_proof_targets) {
        return Some(
            "Cargo artifact targets were not all covered by terminal compiler inventories"
                .to_string(),
        );
    }
    None
}

pub(crate) fn run_compiler(run: CompilerRun<'_>) -> ExitCode {
    let CompilerRun {
        cmd_args,
        rustc_path,
        config,
        selected_codegen_backend,
        supports_json_transport,
        strict_artifact_policy,
        strict_result_gate,
        certify_gate,
        allow_l0_gaps,
        memory_safe_policy,
        survey,
        hardened,
        trust_profile,
        ay_path,
        format,
        report_dir,
        unsafe_memory_report,
        mut live_report_consumer,
        render_output,
        ephemeral_single_file_output,
    } = run;

    if cmd_args.is_empty() {
        eprintln!("targo trust: internal error: empty command");
        return ExitCode::from(2);
    }

    let program = &cmd_args[0];
    let args = &cmd_args[1..];
    // Read the TRUSTFLAGS override channel at invocation start, fail-closed:
    // an invalid value is a setup error before any compiler runs.
    let trustflags = match trustflags_from_env() {
        Ok(trustflags) => trustflags,
        Err(error) => {
            eprintln!("targo trust: {error}");
            return ExitCode::from(2);
        }
    };
    let crate_mode = is_cargo_program(program);
    let cargo_test_mode = crate_mode && args.first().is_some_and(|arg| arg == "test");
    let cargo_test_compile_only =
        cargo_test_mode && cargo_arg_before_passthrough(args, |arg| arg == "--no-run");
    if cargo_test_mode {
        if let Some(report_dir) = report_dir {
            if let Err(error) = crate::report::invalidate_report_bundle(Path::new(report_dir)) {
                eprintln!(
                    "targo trust: could not invalidate the previous certified-test report bundle: {error}"
                );
                return ExitCode::from(2);
            }
        }
    }
    let cargo_execution_mode =
        crate_mode && args.first().is_some_and(|arg| matches!(arg.as_str(), "test" | "bench"));
    if crate_mode {
        if let Some(error) = cargo_compiler_override_diagnostic(args) {
            eprintln!("targo trust: {error}");
            return ExitCode::from(2);
        }
    }
    if crate_mode && !supports_json_transport {
        eprintln!(
            "targo trust: selected compiler lacks the structured Trust transport required for evidence-grade Cargo verification"
        );
        return ExitCode::from(2);
    }
    if cargo_test_mode && !cargo_test_has_explicit_target_selector(args) {
        eprintln!(
            "targo trust: note: phase A preserves Cargo's default non-doc compile coverage; phase B executes ordinary test targets (`--tests`) but excludes doctests, which require a separate authenticated rustdoc lane"
        );
    }
    let verification_session = match VerificationSession::create() {
        Ok(session) => session,
        Err(error) => {
            eprintln!("targo trust: could not create verification freshness token: {error}");
            return ExitCode::from(2);
        }
    };
    let hardened_profile = hardened_profile_name(hardened, trust_profile).map(str::to_string);
    let controls = VerificationControls {
        policy: TrustPolicySelection::from_lane_flags(memory_safe_policy, survey, certify_gate),
        timeout_ms: config.timeout_ms,
        function_budget_ms: config.function_budget_ms,
        hardened_profile: hardened_profile.as_deref(),
        ay_path,
        verification_session: &verification_session.id,
        proof_artifact_root: verification_session.artifact_root(),
    };
    let mut effective_args = if crate_mode {
        let normalized = if cargo_test_mode {
            cargo_test_compile_only_args(args)
        } else {
            cargo_args_with_proof_message_format(args)
        };
        match normalized {
            Ok(args) => args,
            Err(error) => {
                eprintln!("targo trust: could not establish Cargo proof execution plan: {error}");
                return ExitCode::from(2);
            }
        }
    } else {
        args.to_vec()
    };
    if !crate_mode {
        if let Err(error) = append_verification_control_args(&mut effective_args, &controls) {
            eprintln!("targo trust: could not configure verifier options: {error}");
            return ExitCode::from(2);
        }
        // TRUSTFLAGS overrides are merged last so they win over the
        // config-derived policy above, mirroring the crate-mode rustflags
        // merge in apply_cargo_rustflags_env.
        trustflags.apply_to_args(&mut effective_args);
    }
    let _ephemeral_output =
        match prepare_ephemeral_single_file_output(args, ephemeral_single_file_output) {
            Ok(output) => output,
            Err(error) => {
                eprintln!("targo trust: could not prepare temporary single-file output: {error}");
                return ExitCode::from(2);
            }
        };
    let start = Instant::now();

    // For targo-based invocations, pin RUSTC to the discovered Trust
    // toolchain; verifier policy (config-derived plus TRUSTFLAGS overrides)
    // rides in the rustflags environment assembled below.
    let cargo_selection = if crate_mode {
        match resolve_cargo_selection_for_compiler(args, rustc_path, program) {
            Ok(selection) => Some(selection),
            Err(error) => {
                eprintln!(
                    "targo trust: could not resolve canonical Cargo package selection: {error}"
                );
                return ExitCode::from(2);
            }
        }
    } else {
        None
    };
    let selected_cargo_packages = cargo_selection.as_ref().map(selected_package_map_from_selection);
    let mut cmd = if let Some(selection) = cargo_selection.as_ref() {
        match configured_verified_cargo_child(
            program,
            &effective_args,
            args,
            rustc_path,
            config,
            selected_codegen_backend,
            supports_json_transport,
            strict_artifact_policy,
            allow_l0_gaps,
            &controls,
            &trustflags,
            selection,
            cargo_test_mode,
            None,
        ) {
            Ok(command) => command,
            Err(error) => {
                eprintln!("targo trust: could not configure Cargo verifier options: {error}");
                return ExitCode::from(2);
            }
        }
    } else {
        let mut command = Command::new(program);
        command.args(&effective_args);
        scrub_proof_compiler_authority_env(&mut command);
        scrub_legacy_verifier_env(&mut command);
        apply_targo_test_monitor_session(&mut command, false, &verification_session.id);
        apply_native_runtime_env(&mut command, rustc_path);
        command
    };
    cmd.stderr(Stdio::piped());
    if crate_mode {
        cmd.stdout(Stdio::piped());
    }

    CompilerProcessGuard::configure(&mut cmd);
    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            eprintln!("targo trust: failed to spawn `{program}`: {e}");
            return ExitCode::from(2);
        }
    };
    let mut process_guard = CompilerProcessGuard::start(child.id(), COMPILER_PROCESS_TIMEOUT);

    let cargo_stdout = if crate_mode {
        let Some(stdout) = child.stdout.take() else {
            eprintln!("targo trust: canonical Targo stdout pipe was not available");
            process_guard.abort_before_reap();
            let _ = child.kill();
            let _ = child.wait();
            return ExitCode::from(2);
        };
        let selected = selected_cargo_packages
            .as_ref()
            .expect("crate mode has canonical package selection")
            .clone();
        Some(spawn_cargo_stdout_parser(
            stdout,
            selected,
            verification_session.id.clone(),
            strict_artifact_policy,
            cargo_execution_mode,
        ))
    } else {
        None
    };

    let Some(stderr) = child.stderr.take() else {
        eprintln!("targo trust: compiler stderr pipe was not available");
        process_guard.abort_before_reap();
        let _ = child.kill();
        let _ = child.wait();
        return ExitCode::from(2);
    };
    // Drain both compiler pipes concurrently with the lifecycle wait. Besides
    // preventing pipe-buffer deadlock, this is what makes the portable
    // try_wait deadline reachable on platforms without the Unix watchdog.
    let stderr_output = spawn_compiler_stderr_parser(
        stderr,
        crate_mode,
        render_output,
        supports_json_transport,
        verification_session.id.clone(),
        strict_artifact_policy,
    );

    let mut status = match wait_for_compiler_process(&mut child, &mut process_guard) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("targo trust: failed to wait for process: {e}");
            return ExitCode::from(2);
        }
    };
    if let Err(error) = process_guard.finish() {
        eprintln!("targo trust: {error}");
        return ExitCode::from(2);
    }

    let mut verification_results = Vec::new();
    let mut compiler_diagnostics;
    let mut cached_obligations = 0usize;
    let mut coverage_rows = Vec::new();
    let mut coverage_proof_targets = BTreeSet::new();
    let mut observed_proof_targets = BTreeSet::new();
    let mut completed_proof_targets = BTreeSet::new();
    let mut compiled_targets = BTreeSet::new();
    let mut test_executables = BTreeSet::new();
    let mut cargo_proof_inventory = None;
    // Successful-child transport defects are setup/evidence failures, but
    // they must still flow through the canonical failed-report path. Returning
    // here would suppress the very diagnostic artifact callers requested and
    // make an unauthenticated empty stream observationally indistinguishable
    // from a report-rendering failure.
    let mut cargo_evidence_integrity_errors = Vec::new();

    let parsed_stderr = match receive_compiler_output(stderr_output, "compiler stderr") {
        Ok(parsed) => parsed,
        Err(error) => {
            eprintln!("targo trust: invalid compiler stderr channel: {error}");
            return ExitCode::from(2);
        }
    };
    let raw_terminal_inventory_complete =
        !crate_mode && parsed_stderr.raw_terminal_inventory_complete();
    if crate_mode {
        compiler_diagnostics = parsed_stderr.compiler_diagnostics;
    } else {
        let ParsedCompilerOutput {
            verification_results: parsed_results,
            compiler_diagnostics: parsed_diagnostics,
            cached_obligations: parsed_cached,
            coverage_rows: parsed_coverage,
            ..
        } = parsed_stderr;
        verification_results = parsed_results;
        compiler_diagnostics = parsed_diagnostics;
        cached_obligations = parsed_cached;
        coverage_rows = parsed_coverage;
    }

    if let Some(receiver) = cargo_stdout {
        let evidence = match receive_compiler_output(receiver, "canonical Cargo stdout") {
            Ok(evidence) => evidence,
            Err(error) => {
                eprintln!("targo trust: invalid canonical Cargo evidence channel: {error}");
                return ExitCode::from(2);
            }
        };
        if status.success() {
            let selected = selected_cargo_packages
                .as_ref()
                .expect("crate mode has canonical package selection");
            if let Err(error) =
                evidence.require_successful_selected_roots(selected, strict_artifact_policy)
            {
                eprintln!("targo trust: invalid successful Cargo proof inventory: {error}");
                cargo_evidence_integrity_errors
                    .push(format!("invalid successful Cargo proof inventory: {error}"));
            }
        }
        cargo_proof_inventory = evidence.declared_inventory;
        let parsed = evidence.parsed.require_structured_json_transport(true);
        verification_results = parsed.verification_results;
        compiler_diagnostics.extend(parsed.compiler_diagnostics);
        cached_obligations = parsed.cached_obligations;
        coverage_rows = parsed.coverage_rows;
        coverage_proof_targets = parsed.coverage_proof_targets;
        observed_proof_targets = parsed.observed_proof_targets;
        completed_proof_targets = parsed.completed_proof_targets;
        compiled_targets = evidence.compiled_targets;
        test_executables = evidence.test_executables;
    }

    // Preserve the exact authenticated compiler vector before applying the one
    // publication normalization.  The normalized vector can only downgrade a
    // proof label or elide a redundant diagnostic alias; it never manufactures
    // a Targo-owned Proved row.  Live publication authority later recomputes
    // this projection from the compiler vector before it mints any receipts.
    let authenticated_compiler_results = verification_results.clone();
    let zero_obligation_functions =
        crate::types::authenticated_zero_obligation_inventory(&authenticated_compiler_results);
    crate::types::normalize_authenticated_results_for_publication(
        &mut verification_results,
        Some(verification_session.artifact_root()),
    );

    persist_verification_snapshot(args, cargo_selection.as_ref(), &authenticated_compiler_results);

    let phase_a_status = child_status_code(&status);
    let phase_a_success = status.success();
    let mut post_phase_a_orchestration_error = None;
    let mut test_execution = cargo_test_mode.then(|| CertifiedTestExecutionReport {
        schema: trust_types::CERTIFIED_TEST_EXECUTION_SCHEMA_VERSION.to_string(),
        completion_scope: CertifiedTestExecutionCompletionScope::TopLevelCargoChildExitOnlyV1,
        requested: true,
        scope: trust_types::CERTIFIED_TEST_EXECUTION_SCOPE.to_string(),
        compile_only: cargo_test_compile_only,
        phase_a_status,
        phase_a_success,
        phase_b_state: if cargo_test_compile_only {
            CertifiedTestExecutionPhaseState::NotRequested
        } else {
            CertifiedTestExecutionPhaseState::Blocked
        },
        blocker: None,
        phase_b_exit: None,
        authorized_executables: Vec::new(),
        authorized_inventory_sha256: None,
        target_directory: None,
    });

    if cargo_test_mode {
        for executable in &test_executables {
            compiler_diagnostics.push(CompilerDiagnostic {
                level: "note".to_string(),
                message: format!(
                    "targo trust: certified test execution inventory target={} path={} phase_a_sha256={}",
                    executable.target.report_label(),
                    executable.path.display(),
                    executable.phase_a_sha256,
                ),
            });
        }
        if cargo_test_compile_only {
            compiler_diagnostics.push(CompilerDiagnostic {
                level: "note".to_string(),
                message: "targo trust: certified test execution state=compile-only (`--no-run`); no test process ran, so no installed runtime monitor could be reached"
                    .to_string(),
            });
        }
    }

    // `targo trust test` is evidence-gated before user code executes. Phase A
    // compiled all non-doc test targets under the unique proof session and the
    // parser authenticated their transport. Only then may phase B ask the same
    // Targo/RUSTC/session configuration to replay Fresh jobs. The Cargo fork
    // copies each byte-identical authorized test artifact into a sealed
    // anonymous image and executes that handle. Unsupported platforms fail
    // closed before the phase-B Cargo child is spawned; Cargo repeats that gate
    // as defense in depth. There is no pathname fallback.
    if cargo_test_mode && !cargo_test_compile_only && post_phase_a_orchestration_error.is_none() {
        let phase_a_coverage_overflowed = coverage_accounting_overflowed(&coverage_rows);
        let phase_a_coverage = aggregate_coverage(&coverage_rows);
        let phase_a_missing_target_coverage = completed_proof_targets
            .difference(&coverage_proof_targets)
            .cloned()
            .collect::<Vec<_>>();
        let phase_a_missing_transport = missing_trust_json_diagnostic(
            true,
            &verification_results,
            &completed_proof_targets,
            !coverage_rows.is_empty(),
        );
        if let Some(blocker) = cargo_test_execution_evidence_blocker(
            status.success(),
            phase_a_missing_transport.as_deref(),
            strict_artifact_policy,
            phase_a_coverage.as_ref(),
            phase_a_coverage_overflowed,
            &phase_a_missing_target_coverage,
        ) {
            eprintln!(
                "targo trust: refusing to execute Cargo tests before authenticated build evidence is complete: {blocker}"
            );
            compiler_diagnostics.push(CompilerDiagnostic {
                level: "error".to_string(),
                message: format!(
                    "targo trust: certified test execution state=blocked-before-execution: {blocker}"
                ),
            });
            if let Some(execution) = test_execution.as_mut() {
                execution.phase_b_state = CertifiedTestExecutionPhaseState::Blocked;
                execution.blocker = Some(blocker);
            }
        } else {
            let selection =
                cargo_selection.as_ref().expect("Cargo test mode has canonical package selection");
            // `targo metadata` reports its own effective target directory but
            // does not consume the build command's `--target-dir`. Preserve
            // Cargo's CLI precedence when binding the actual phase-A
            // executables instead of authenticating the metadata default.
            let execution_target_directory =
                cargo_target_dir(args, Some(&selection.target_directory));
            if let Some(execution) = test_execution.as_mut() {
                execution.target_directory = Some(execution_target_directory.display().to_string());
            }
            let mut phase_b_started = false;
            let phase_b = (|| -> Result<ExitStatus, String> {
                if let Some(blocker) = certified_test_execution_platform_blocker() {
                    return Err(blocker.to_string());
                }
                let execution_authority = write_test_execution_authority(
                    &verification_session,
                    &execution_target_directory,
                    rustc_path.parent().and_then(Path::parent).ok_or_else(|| {
                        format!(
                            "authenticated compiler path `{}` has no toolchain root",
                            rustc_path.display()
                        )
                    })?,
                    &test_executables,
                )
                .map_err(|error| {
                    format!("could not bind Cargo test executables before execution: {error}")
                })?;
                if let Some(execution) = test_execution.as_mut() {
                    execution.authorized_executables = execution_authority.executables.clone();
                    execution.authorized_inventory_sha256 =
                        Some(execution_authority.inventory_sha256.clone());
                    execution.target_directory = Some(execution_authority.target_directory.clone());
                }
                let execution_args = cargo_test_execution_args(args).map_err(|error| {
                    format!("could not construct Cargo test execution phase: {error}")
                })?;
                let mut execution = configured_verified_cargo_child(
                    program,
                    &execution_args,
                    args,
                    rustc_path,
                    config,
                    selected_codegen_backend,
                    supports_json_transport,
                    strict_artifact_policy,
                    allow_l0_gaps,
                    &controls,
                    &trustflags,
                    selection,
                    true,
                    Some((&execution_authority.path, &execution_authority.inventory_sha256)),
                )
                .map_err(|error| format!("could not configure Cargo test execution: {error}"))?;
                CompilerProcessGuard::configure(&mut execution);
                let mut execution_child = execution.spawn().map_err(|error| {
                    format!("failed to spawn Cargo test execution phase: {error}")
                })?;
                phase_b_started = true;
                if let Some(execution) = test_execution.as_mut() {
                    execution.phase_b_state = CertifiedTestExecutionPhaseState::Started;
                }
                let mut execution_guard =
                    CompilerProcessGuard::start(execution_child.id(), COMPILER_PROCESS_TIMEOUT);
                let execution_status =
                    wait_for_compiler_process(&mut execution_child, &mut execution_guard).map_err(
                        |error| format!("failed to wait for Cargo test execution: {error}"),
                    )?;
                execution_guard.finish()?;
                Ok(execution_status)
            })();
            match phase_b {
                Ok(execution_status) => {
                    status = execution_status;
                    let phase_b_exit = child_status_code(&status);
                    if let Some(execution) = test_execution.as_mut() {
                        execution.phase_b_state =
                            CertifiedTestExecutionPhaseState::CargoInvocationExited;
                        execution.phase_b_exit = Some(phase_b_exit);
                    }
                    compiler_diagnostics.push(CompilerDiagnostic {
                        level: if status.success() { "note" } else { "error" }.to_string(),
                        message: format!(
                            "targo trust: certified test execution state=phase-b-cargo-invocation-exited authorized_executables={} cargo_exit_code={phase_b_exit}",
                            test_executables.len(),
                        ),
                    });
                }
                Err(error) => {
                    eprintln!("targo trust: {error}");
                    compiler_diagnostics.push(CompilerDiagnostic {
                        level: "error".to_string(),
                        message: format!(
                            "targo trust: certified test execution state={} error={error}",
                            if phase_b_started {
                                "phase-b-started"
                            } else {
                                "blocked-before-execution"
                            },
                        ),
                    });
                    record_certified_test_execution_error(
                        test_execution.as_mut(),
                        phase_b_started,
                        &error,
                    );
                    post_phase_a_orchestration_error = Some(error);
                }
            }
        }
    }
    let compiler_exit =
        if post_phase_a_orchestration_error.is_some() { 2 } else { child_status_code(&status) };
    let compiler_signal_exit = post_phase_a_orchestration_error
        .is_none()
        .then(|| child_signal_exit_code(&status))
        .flatten();
    let duration_ms = start.elapsed().as_millis() as u64;
    if let Some(profile) = hardened_profile.as_deref() {
        let message = format!("targo trust: hardened profile `{profile}` enabled");
        if !compiler_diagnostics.iter().any(|diagnostic| diagnostic.message == message) {
            compiler_diagnostics.push(CompilerDiagnostic { level: "note".into(), message });
        }
    }

    // Count verification outcomes into the disjoint Stage-2 partition:
    // proved / failed / runtime_checked, plus a three-way split of the
    // inconclusive rows into assumed (`assumption:*`), mandated (the compiler's
    // design_mandate bit), and genuine unknown. Defective assumption rows
    // (claiming proof) are fail-closed to unknown and surfaced as transport
    // defects on stderr.
    let (counts, transport_defects) = partition_outcome_counts(&verification_results);
    for defect in &transport_defects {
        eprintln!("targo trust: {defect}");
    }
    let OutcomeCounts {
        total,
        proved,
        failed,
        unknown,
        runtime_checked,
        assumed,
        mandated,
        contract_panics,
    } = counts;

    // The exit-code gate. The advisory lane exits 0 on a conditional pass (no
    // refutation, no genuine unknown, every non-proved row an EXPLICIT ledger
    // entry). The canonical strict lane uses the historical
    // `compiler_verification_success` predicate.
    let lane = if certify_gate {
        GateLane::Certify
    } else if memory_safe_policy {
        GateLane::MemorySafe
    } else if strict_result_gate {
        GateLane::Strict
    } else {
        GateLane::Advisory
    };
    let gate_counts = if lane == GateLane::MemorySafe {
        let (gate_counts, defects) = memory_safe_gate_counts(&verification_results, counts);
        for defect in defects {
            eprintln!("targo trust: {defect}");
        }
        gate_counts
    } else {
        counts
    };
    // Trust (assertion-grade coverage, roadmap §4.1): the compiler's
    // `coverage_summary` row(s). Any accounting mismatch (`processed != eligible`)
    // means whole-crate coverage was not established — a FAIL-CLOSED condition like an unknown,
    // not a warning: the gate is capped at Inconclusive (never a passing gate).
    // `None` is coverage-UNKNOWN. Current strict compiler policy promises the
    // row, so absence is inconclusive there; explicit advisory/survey lanes
    // retain compatibility with older compilers and report the unknown.
    let coverage_overflowed = coverage_accounting_overflowed(&coverage_rows);
    let coverage = aggregate_coverage(&coverage_rows);
    let missing_target_coverage =
        completed_proof_targets.difference(&coverage_proof_targets).cloned().collect::<Vec<_>>();
    if let Some(cov) = coverage.filter(|cov| !cov.coverage_complete) {
        if !coverage_overflowed && cov.processed < cov.eligible {
            eprintln!(
                "targo trust: coverage shortfall: {} function(s) were never verified \
                 ({} of {} eligible function bodies processed) — the verification report \
                 does NOT cover the whole crate; fail-closed: this run cannot pass",
                cov.eligible - cov.processed,
                cov.processed,
                cov.eligible,
            );
        } else {
            eprintln!(
                "targo trust: malformed coverage accounting: {} processed function bodies \
                 were reported for {} eligible bodies — proof completeness cannot be \
                 established; fail-closed: this run cannot pass",
                cov.processed, cov.eligible,
            );
        }
    }
    let require_coverage = strict_artifact_policy;
    if require_coverage && (coverage.is_none() || !missing_target_coverage.is_empty()) {
        if missing_target_coverage.is_empty() {
            eprintln!(
                "targo trust: missing coverage_summary transport — strict proof completeness cannot be established; fail-closed"
            );
        } else {
            let targets = missing_target_coverage
                .iter()
                .map(CargoTargetIdentity::report_label)
                .collect::<Vec<_>>()
                .join(", ");
            eprintln!(
                "targo trust: missing coverage_summary transport for completed target(s): {targets} — strict proof completeness cannot be established; fail-closed"
            );
        }
    }
    let gate_decision = evaluate_run_gate(
        lane,
        compiler_exit,
        gate_counts,
        coverage.as_ref(),
        !missing_target_coverage.is_empty(),
        require_coverage,
        zero_obligation_functions.len(),
    );
    // A run with no authenticated evidence that verification executed is a
    // hard setup error, never a plausible zero-obligation report. Coverage
    // rows reaching this point have already passed raw/Cargo authentication.
    let missing_trust_json = missing_trust_json_diagnostic(
        crate_mode,
        &verification_results,
        &completed_proof_targets,
        !coverage_rows.is_empty(),
    );

    // Trust (assumption ledger): compute the dep-TCB entries BEFORE the report
    // literal so the crate-scope assumptions land in report.json (the stderr
    // ledger rendering below derives from the same set's line renderer).
    let dep_assumptions = if crate_mode {
        crate::dep_tcb::dep_tcb_assumption_entries(cargo_proof_inventory.as_ref())
    } else {
        Vec::new()
    };
    let canonical_cargo_proof_inventory = if crate_mode {
        match cargo_proof_inventory_report(
            cargo_proof_inventory.as_ref(),
            &completed_proof_targets,
            &coverage_proof_targets,
        ) {
            Ok(report) => report,
            Err(error) => {
                eprintln!("targo trust: invalid Cargo proof report inventory: {error}");
                cargo_evidence_integrity_errors
                    .push(format!("invalid Cargo proof report inventory: {error}"));
                None
            }
        }
    } else {
        None
    };
    // Only exclusions NOT admitted to the dependency-TCB ledger fail the gate.
    // A ledger-admitted third-party dep (dependency-policy / build-script) is a
    // recorded trust assumption (see `dep_assumptions` above), not a proof gap;
    // an unresolved exclusion still fails closed. This keeps the gate and the
    // dep-TCB admission ledger in agreement.
    let active_cargo_exclusions =
        cargo_gate_failing_exclusion_labels(canonical_cargo_proof_inventory.as_ref());
    let cargo_exclusion_gate_failure = !active_cargo_exclusions.is_empty();
    if cargo_exclusion_gate_failure {
        eprintln!(
            "targo trust: Cargo proof frontier excluded {} active Unit(s) outside the dependency-TCB ledger; whole-crate proof is incomplete and the verification gate cannot pass: {}",
            active_cargo_exclusions.len(),
            active_cargo_exclusions.join("; "),
        );
    }
    for error in &cargo_evidence_integrity_errors {
        compiler_diagnostics
            .push(CompilerDiagnostic { level: "error".into(), message: error.clone() });
    }
    let evidence_setup_failed =
        missing_trust_json.is_some() || !cargo_evidence_integrity_errors.is_empty();
    let base_success = gate_decision.is_success()
        && !cargo_exclusion_gate_failure
        && post_phase_a_orchestration_error.is_none();
    let report_subject = if crate_mode {
        cargo_report_subject(&compiled_targets, &observed_proof_targets, &completed_proof_targets)
    } else {
        match single_file_report_subject(cmd_args) {
            Ok(subject) => subject,
            Err(error) => {
                eprintln!("targo trust: {error}");
                return ExitCode::from(2);
            }
        }
    };
    // Mint same-process row authority only after the protected compiler/Cargo
    // channels and target-inventory checks.  The constructor independently
    // recomputes the fail-closed publication projection from the exact compiler
    // vector, so an arbitrary post-parse rewrite cannot acquire proof credit.
    let live_transport_authority = LiveTransportAuthority::capture_authenticated_projection(
        &report_subject,
        &verification_session.id,
        &authenticated_compiler_results,
        &verification_results,
        Some(verification_session.artifact_root()),
    );
    let mut report = VerificationReport {
        report_subject,
        success: base_success,
        exit_code: compiler_exit,
        proved,
        failed,
        unknown,
        runtime_checked,
        assumed,
        mandated,
        contract_panics,
        cached: cached_obligations,
        total,
        results: verification_results,
        zero_obligation_functions,
        compiler_diagnostics,
        duration_ms,
        config: ReportConfig {
            level: config.level.clone(),
            timeout_ms: config.timeout_ms,
            function_budget_ms: config.function_budget_ms,
            enabled: config.enabled,
            hardened,
            trust_profile: hardened_profile.clone(),
        },
        dep_assumptions,
        gate: None,
        coverage,
        test_execution,
        cargo_proof_inventory: canonical_cargo_proof_inventory,
        proof_artifact_root: Some(verification_session.artifact_root().to_path_buf()),
        live_transport_authority,
    };
    let hardened_gate_failure = report.hardened_proof_gate_failure();
    if let Some(gap) = hardened_gate_failure {
        eprintln!(
            "targo trust: hardened proof evidence gate failed: {}/{} hardened obligations have publishable native proof evidence",
            gap.proof_evidence_entries, gap.hardened_obligations
        );
        report.success = false;
    }
    if evidence_setup_failed {
        report.success = false;
    }

    // Decide the actual process status once, before serializing any evidence.
    // A missing compiler transport is a setup/evidence failure (2), not an
    // ordinary verification-gate failure (1), even when Cargo itself exited 0.
    //
    // Verification-in-compilation era: a fail-closed verification outcome makes
    // trustc emit hard errors, so Cargo exits 101 even though the run is an
    // ORDINARY verification-gate failure with a full sealed report. The CLI
    // contract (and the e2e corpora that pin it) reserves exit 1 for exactly
    // that case, and passes the compiler's own code through otherwise (genuine
    // compile/setup errors, ICEs). Two conjuncts, both required:
    //  * the verification session CONCLUDED — the authenticated coverage
    //    inventory is present, complete, and covers every completed target. A
    //    compiler that died mid-run (ICE, signal wrapper, genuine compile
    //    error aborting before verification) never completes coverage, so its
    //    own status passes through
    //    (`live_report_consumer_cannot_override_early_proof_followed_by_ice`:
    //    a claimed-proved prefix followed by death must keep the ICE status —
    //    row counting alone cannot see this, because the transport synthesizes
    //    a defect row for the abnormal end and claimed rows are downgraded);
    //  * the outcome partition actually contains a non-proved row (a concluded
    //    run that failed for NON-verification reasons keeps its own status).
    let verification_concluded = missing_target_coverage.is_empty()
        && coverage.as_ref().is_some_and(|coverage| {
            coverage.coverage_complete && coverage.processed == coverage.eligible
        });
    let fail_closed_rows_observed =
        verification_concluded && gate_counts.total > gate_counts.proved;
    let process_exit_code = if post_phase_a_orchestration_error.is_some() {
        2
    } else if let Some(signal_exit) = compiler_signal_exit {
        signal_exit
    } else if evidence_setup_failed {
        2
    } else {
        targo_exit_code_value_for_report(report.success, compiler_exit, fail_closed_rows_observed)
    };
    let process_exit = ExitCode::from(process_exit_code);

    // Trust (green front door, Stage 2): record the exit-code gate decision into
    // the report (and thus report.json) AFTER the hardened / missing-json
    // success flips above. The gate object is SEPARATE from the verdict lattice
    // (report_builder computes `summary.verdict` unchanged); it answers why the
    // shell exited as it did. Curated dependency/sysroot assumptions remain
    // metadata-only; exact active Cargo Unit exclusions are different: they
    // establish an incomplete proof frontier and therefore cap the gate.
    let published_gate_decision = if hardened_gate_failure.is_some() || evidence_setup_failed {
        GateDecision::Fail
    } else if report.failed > 0 || compiler_exit != 0 {
        GateDecision::Fail
    } else if cargo_exclusion_gate_failure {
        GateDecision::Inconclusive
    } else if report.success {
        gate_decision
    } else {
        GateDecision::Inconclusive
    };
    let mut verification_gate = build_verification_gate_report(
        lane,
        &config.level,
        published_gate_decision,
        gate_counts,
        process_exit_code,
        &report.dep_assumptions,
        coverage,
    );
    verification_gate.test_execution = report.test_execution.clone();
    report.gate = Some(verification_gate);

    if !report.seal_for_publication() {
        eprintln!(
            "targo trust: could not seal the final compiler rows, coverage, policy, gate, and exit state for canonical publication"
        );
        return ExitCode::from(2);
    }

    if evidence_setup_failed && live_report_consumer.is_some() {
        eprintln!(
            "targo trust: live report consumer withheld: compiler/Cargo evidence setup failed"
        );
    } else if let Some(consumer) = live_report_consumer.as_mut() {
        if let Some(reason) = live_report_consumer_rejection(
            crate_mode,
            compiler_exit,
            compiler_signal_exit,
            report.cargo_proof_inventory.as_ref(),
            coverage.as_ref(),
            &missing_target_coverage,
            raw_terminal_inventory_complete,
            &compiled_targets,
            &observed_proof_targets,
            &completed_proof_targets,
            &coverage_proof_targets,
        ) {
            eprintln!("targo trust: live report consumer withheld: {reason}");
        } else {
            let live_report = match report.sealed_canonical_report() {
                Ok(report) => report,
                Err(error) => {
                    eprintln!("targo trust: live report authority gate failed: {error}");
                    return ExitCode::from(2);
                }
            };
            if let Err(error) = consumer(&live_report) {
                eprintln!("targo trust: live report consumer failed: {error}");
                return ExitCode::from(2);
            }
        }
    }

    if !render_output && (report_dir.is_some() || unsafe_memory_report.is_some()) {
        eprintln!(
            "targo trust: internal error: suppressed rendering cannot satisfy requested report artifacts"
        );
        return ExitCode::from(2);
    }

    let render_result = if !render_output {
        Ok(())
    } else if let Some(unsafe_memory_report) = unsafe_memory_report {
        report.render_with_unsafe_memory_report(format, report_dir, Some(unsafe_memory_report))
    } else {
        report.render(format, report_dir)
    };
    if let Err(error) = render_result {
        eprintln!("targo trust: report artifact evidence gate failed: {error}");
        return ExitCode::from(2);
    }

    // Trust (dep-TCB ledger, Stage 0): surface the crate's dependency trust base
    // — every crate scoped out of verification (transitive deps + the
    // core/alloc/std hard-skip) that the proof is conditional on. Only in crate
    // mode (single-file builds have no resolved dep graph), and never gated on
    // success: the trust base is reported whether or not the obligations passed.
    if crate_mode && render_output {
        let ledger = crate::dep_tcb::dep_tcb_ledger_lines(cargo_proof_inventory.as_ref());
        if !ledger.is_empty() {
            let mut rendered = String::new();
            trust_report::append_dep_tcb_ledger(&mut rendered, &ledger);
            eprintln!("{rendered}");
        }
    }

    if let Some(diagnostic) = missing_trust_json {
        eprintln!("targo trust: error: {diagnostic}");
        return process_exit;
    }
    if !cargo_evidence_integrity_errors.is_empty() {
        return process_exit;
    }

    process_exit
}

fn targo_exit_code_value_for_report(
    report_success: bool,
    compiler_exit: i32,
    fail_closed_rows_observed: bool,
) -> u8 {
    if report_success {
        return 0;
    }
    // Ordinary verification-gate failure: verification CONCLUDED (complete
    // authenticated coverage) and at least one obligation is not proved. Exit 1
    // per the CLI contract, even though trustc's fail-closed errors made Cargo
    // exit 101. Otherwise (ICE, signal wrapper, compile error before
    // verification, fake/broken toolchain), preserve the compiler's own code.
    if fail_closed_rows_observed {
        return 1;
    }

    match u8::try_from(compiler_exit) {
        Ok(code) if code != 0 => code,
        _ => 1,
    }
}

/// Trust (green front door, Stage 2): build the serializable gate object from
/// the gate decision, the outcome partition, and the crate-scope ledger. The
/// `exit_code` is the already-finalized REAL process exit, so it can never claim
/// 0 or an ordinary gate failure while another gate (hardened evidence,
/// missing-json, or compiler setup) chooses a different status. `decision`
/// has already incorporated exact active-Unit exclusions from the canonical
/// Cargo proof inventory. Ledger entries only populate
/// `conditional_on_dependency_entries`; curated sysroot assumptions do not
/// independently drive the decision or terminal label.
fn build_verification_gate_report(
    lane: GateLane,
    verification_level: &str,
    decision: GateDecision,
    counts: OutcomeCounts,
    process_exit_code: u8,
    dep_assumptions: &[trust_types::AssumptionEntry],
    coverage: Option<trust_types::VerificationCoverage>,
) -> trust_types::VerificationGateReport {
    trust_types::VerificationGateReport {
        lane: lane.as_str().to_string(),
        verification_level: Some(verification_level.to_string()),
        decision: decision.as_str().to_string(),
        exit_code: process_exit_code,
        counts: trust_types::VerificationGateCounts {
            total: counts.total,
            proved: counts.proved,
            failed: counts.failed,
            unknown: counts.unknown,
            runtime_checked: counts.runtime_checked,
            assumed: counts.assumed,
            mandated: counts.mandated,
            contract_panics: counts.contract_panics,
        },
        conditional_on_assumption_rows: counts.assumed > 0,
        conditional_on_dependency_entries: !dep_assumptions.is_empty(),
        conditional_on_runtime_checks: counts.runtime_checked > 0,
        conditional_on_visitation_entries: false,
        // Trust (assertion-grade coverage): the counts + `coverage_complete`
        // recorded into report.json; `None` = coverage unknown (older compiler).
        coverage,
        test_execution: None,
    }
}

// ---------------------------------------------------------------------------
// Compiler capture (for rewrite loop)
// ---------------------------------------------------------------------------

/// Outcome of a single compiler invocation, for use in the rewrite loop.
pub(crate) struct CompilerRunResult {
    pub(crate) exit_code: i32,
    pub(crate) signal_exit: Option<u8>,
    pub(crate) report_subject: String,
    pub(crate) verification_results: Vec<VerificationResult>,
    pub(crate) zero_obligation_functions: Vec<String>,
    pub(crate) compiler_diagnostics: Vec<CompilerDiagnostic>,
    pub(crate) coverage: Option<trust_types::VerificationCoverage>,
    pub(crate) missing_target_coverage: Vec<CargoTargetIdentity>,
    pub(crate) live_transport_authority: LiveTransportAuthority,
}

/// Run a compiler command and capture verification results without rendering.
///
/// Unlike `run_compiler`, this returns the results for loop processing rather
/// than rendering a report and exiting.
pub(super) fn run_compiler_capture(
    cmd_args: &[String],
    rustc_path: &Path,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
    strict_artifact_policy: bool,
    allow_l0_gaps: bool,
    memory_safe_policy: bool,
    survey: bool,
    certify_gate: bool,
    hardened: bool,
    trust_profile: Option<&str>,
    ay_path: Option<&Path>,
    quiet: bool,
    ephemeral_single_file_output: bool,
) -> Result<CompilerRunResult, ExitCode> {
    if cmd_args.is_empty() {
        eprintln!("targo trust: internal error: empty command");
        return Err(ExitCode::from(2));
    }

    let program = &cmd_args[0];
    let args = &cmd_args[1..];
    // Same TRUSTFLAGS protocol as run_compiler: read the override channel at
    // invocation start, fail-closed before any compiler runs.
    let trustflags = match trustflags_from_env() {
        Ok(trustflags) => trustflags,
        Err(error) => {
            eprintln!("targo trust: {error}");
            return Err(ExitCode::from(2));
        }
    };
    let crate_mode = is_cargo_program(program);
    let cargo_execution_mode =
        crate_mode && args.first().is_some_and(|arg| matches!(arg.as_str(), "test" | "bench"));
    // This capture path feeds the source-rewrite loop and has no
    // evidence-gated second execution phase. Keep this defense in depth even
    // though the CLI rejects `test --rewrite`: an internal caller must not
    // revive compile-and-execute-before-admission behavior.
    if cargo_execution_mode {
        eprintln!(
            "targo trust: test/bench execution is unavailable in rewrite capture mode; run without `--rewrite`"
        );
        return Err(ExitCode::from(2));
    }
    if crate_mode {
        if let Some(error) = cargo_compiler_override_diagnostic(args) {
            eprintln!("targo trust: {error}");
            return Err(ExitCode::from(2));
        }
        if !supports_json_transport {
            eprintln!(
                "targo trust: selected compiler lacks the structured Trust transport required for evidence-grade Cargo verification"
            );
            return Err(ExitCode::from(2));
        }
    }
    let verification_session = match VerificationSession::create() {
        Ok(session) => session,
        Err(error) => {
            eprintln!("targo trust: could not create verification freshness token: {error}");
            return Err(ExitCode::from(2));
        }
    };
    let hardened_profile = hardened_profile_name(hardened, trust_profile).map(str::to_string);
    let controls = VerificationControls {
        policy: TrustPolicySelection::from_lane_flags(memory_safe_policy, survey, certify_gate),
        timeout_ms: config.timeout_ms,
        function_budget_ms: config.function_budget_ms,
        hardened_profile: hardened_profile.as_deref(),
        ay_path,
        verification_session: &verification_session.id,
        proof_artifact_root: verification_session.artifact_root(),
    };
    let mut effective_args = if crate_mode {
        cargo_args_with_proof_message_format(args).map_err(|error| {
            eprintln!("targo trust: could not establish Cargo proof message format: {error}");
            ExitCode::from(2)
        })?
    } else {
        args.to_vec()
    };
    if !crate_mode {
        if let Err(error) = append_verification_control_args(&mut effective_args, &controls) {
            eprintln!("targo trust: could not configure verifier options: {error}");
            return Err(ExitCode::from(2));
        }
        trustflags.apply_to_args(&mut effective_args);
    }
    let _ephemeral_output =
        match prepare_ephemeral_single_file_output(args, ephemeral_single_file_output) {
            Ok(output) => output,
            Err(error) => {
                eprintln!("targo trust: could not prepare temporary single-file output: {error}");
                return Err(ExitCode::from(2));
            }
        };
    let mut cmd = Command::new(program);
    cmd.args(&effective_args);
    scrub_proof_compiler_authority_env(&mut cmd);
    cmd.stderr(Stdio::piped());
    if crate_mode {
        cmd.stdout(Stdio::piped());
    }
    apply_native_runtime_env(&mut cmd, rustc_path);

    let cargo_selection = if crate_mode {
        match resolve_cargo_selection_for_compiler(args, rustc_path, program) {
            Ok(selection) => Some(selection),
            Err(error) => {
                eprintln!(
                    "targo trust: could not resolve canonical Cargo package selection: {error}"
                );
                return Err(ExitCode::from(2));
            }
        }
    } else {
        None
    };
    let selected_cargo_packages = cargo_selection.as_ref().map(selected_package_map_from_selection);
    if crate_mode {
        cmd.env("TRUST_TARGO_VERIFY", "1");
        apply_cargo_child_rustc_env(&mut cmd, rustc_path);
        if let Err(error) = apply_cargo_rustflags_env(
            &mut cmd,
            config,
            selected_codegen_backend,
            supports_json_transport,
            strict_artifact_policy,
            allow_l0_gaps,
            &controls,
            &trustflags,
        ) {
            eprintln!("targo trust: could not configure Cargo verifier options: {error}");
            return Err(ExitCode::from(2));
        }
        if let Err(error) = apply_crate_memory_coordination(
            &mut cmd,
            args,
            cargo_selection.as_ref().map(|selection| selection.target_directory.as_path()),
        ) {
            eprintln!("targo trust: could not establish memory coordination: {error}");
            return Err(ExitCode::from(2));
        }
    }

    CompilerProcessGuard::configure(&mut cmd);
    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            eprintln!("targo trust: failed to spawn `{program}`: {e}");
            return Err(ExitCode::from(2));
        }
    };
    let mut process_guard = CompilerProcessGuard::start(child.id(), COMPILER_PROCESS_TIMEOUT);

    let cargo_stdout = if crate_mode {
        let Some(stdout) = child.stdout.take() else {
            process_guard.abort_before_reap();
            let _ = child.kill();
            let _ = child.wait();
            return Err(ExitCode::from(2));
        };
        let selected = selected_cargo_packages
            .as_ref()
            .expect("crate mode has canonical package selection")
            .clone();
        Some(spawn_cargo_stdout_parser(
            stdout,
            selected,
            verification_session.id.clone(),
            strict_artifact_policy,
            cargo_execution_mode,
        ))
    } else {
        None
    };

    let Some(stderr) = child.stderr.take() else {
        eprintln!("targo trust: compiler stderr pipe was not available");
        process_guard.abort_before_reap();
        let _ = child.kill();
        let _ = child.wait();
        return Err(ExitCode::from(2));
    };
    let stderr_output = spawn_compiler_stderr_parser(
        stderr,
        crate_mode,
        !quiet,
        supports_json_transport,
        verification_session.id.clone(),
        strict_artifact_policy,
    );

    let status = match wait_for_compiler_process(&mut child, &mut process_guard) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("targo trust: failed to wait for process: {e}");
            return Err(ExitCode::from(2));
        }
    };
    if let Err(error) = process_guard.finish() {
        eprintln!("targo trust: {error}");
        return Err(ExitCode::from(2));
    }

    let mut verification_results = Vec::new();
    let mut compiler_diagnostics;
    let mut coverage_rows = Vec::new();
    let mut coverage_proof_targets = BTreeSet::new();
    let mut observed_proof_targets = BTreeSet::new();
    let mut completed_proof_targets = BTreeSet::new();
    let mut compiled_targets = BTreeSet::new();

    let parsed_stderr = match receive_compiler_output(stderr_output, "compiler stderr") {
        Ok(parsed) => parsed,
        Err(error) => {
            eprintln!("targo trust: invalid compiler stderr channel: {error}");
            return Err(ExitCode::from(2));
        }
    };
    if crate_mode {
        compiler_diagnostics = parsed_stderr.compiler_diagnostics;
    } else {
        verification_results = parsed_stderr.verification_results;
        compiler_diagnostics = parsed_stderr.compiler_diagnostics;
        coverage_rows = parsed_stderr.coverage_rows;
    }
    if let Some(receiver) = cargo_stdout {
        let evidence = match receive_compiler_output(receiver, "canonical Cargo stdout") {
            Ok(evidence) => evidence,
            Err(error) => {
                eprintln!("targo trust: invalid canonical Cargo evidence channel: {error}");
                return Err(ExitCode::from(2));
            }
        };
        if status.success() {
            let selected = selected_cargo_packages
                .as_ref()
                .expect("crate mode has canonical package selection");
            if let Err(error) =
                evidence.require_successful_selected_roots(selected, strict_artifact_policy)
            {
                eprintln!("targo trust: invalid successful Cargo proof inventory: {error}");
                return Err(ExitCode::from(2));
            }
        }
        let parsed = evidence.parsed.require_structured_json_transport(true);
        verification_results = parsed.verification_results;
        compiler_diagnostics.extend(parsed.compiler_diagnostics);
        coverage_rows = parsed.coverage_rows;
        coverage_proof_targets = parsed.coverage_proof_targets;
        observed_proof_targets = parsed.observed_proof_targets;
        completed_proof_targets = parsed.completed_proof_targets;
        compiled_targets = evidence.compiled_targets;
    }

    let coverage = aggregate_coverage(&coverage_rows);
    let missing_target_coverage =
        completed_proof_targets.difference(&coverage_proof_targets).cloned().collect();
    let report_subject = if crate_mode {
        cargo_report_subject(&compiled_targets, &observed_proof_targets, &completed_proof_targets)
    } else {
        match single_file_report_subject(cmd_args) {
            Ok(subject) => subject,
            Err(error) => {
                eprintln!("targo trust: {error}");
                return Err(ExitCode::from(2));
            }
        }
    };

    // Retain the exact authenticated vector before projecting it for rewrite
    // publication.  Inlining first makes the authority self-contained after
    // the private per-run store is deleted; normalization then validates those
    // same bytes without reopening a path-backed artifact.
    let mut authenticated_compiler_results = verification_results;
    if let Err(error) = crate::report::inline_verification_result_artifacts(
        &mut authenticated_compiler_results,
        verification_session.artifact_root(),
    ) {
        eprintln!(
            "targo trust: could not retain captured proof artifacts before deleting the private run store: {error}"
        );
        return Err(ExitCode::from(2));
    }
    let zero_obligation_functions =
        crate::types::authenticated_zero_obligation_inventory(&authenticated_compiler_results);
    let mut verification_results = authenticated_compiler_results.clone();
    crate::types::normalize_authenticated_results_for_publication(&mut verification_results, None);
    let Some(live_transport_authority) = LiveTransportAuthority::capture_authenticated_projection(
        &report_subject,
        &verification_session.id,
        &authenticated_compiler_results,
        &verification_results,
        None,
    ) else {
        eprintln!(
            "targo trust: captured compiler rows did not match their authenticated publication projection; fail-closed"
        );
        return Err(ExitCode::from(2));
    };

    Ok(CompilerRunResult {
        exit_code: child_status_code(&status),
        signal_exit: child_signal_exit_code(&status),
        report_subject,
        verification_results,
        zero_obligation_functions,
        compiler_diagnostics,
        coverage,
        missing_target_coverage,
        live_transport_authority,
    })
}

// ---------------------------------------------------------------------------
// Rewrite loop
// ---------------------------------------------------------------------------

/// Run the prove-strengthen-backprop convergence loop.
///
/// Uses the ad-hoc CLI rewrite loop implementation.
pub(crate) fn run_rewrite_loop(
    rustc: &Path,
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
    ay_path: Option<&Path>,
) -> ExitCode {
    run_rewrite_loop_fallback(
        rustc,
        subcommand,
        sub_args,
        config,
        selected_codegen_backend,
        supports_json_transport,
        ay_path,
    )
}

/// The prove step of one rewrite-loop iteration: build the command for the
/// source as it stands on disk right now and capture the compiler's verdict on
/// it. That verdict is what grades the previous iteration's edits.
fn rewrite_loop_prove_once(
    rustc: &Path,
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
    ay_path: Option<&Path>,
    quiet: bool,
) -> Result<(Vec<String>, CompilerRunResult), ExitCode> {
    let cmd_args = build_native_command_with_json_transport(
        rustc,
        subcommand,
        sub_args,
        config,
        selected_codegen_backend,
        supports_json_transport,
    )
    .map_err(|error| {
        eprintln!("targo trust: error: {error}");
        ExitCode::from(2)
    })?;
    let run_result = run_compiler_capture(
        &cmd_args,
        rustc,
        config,
        selected_codegen_backend,
        supports_json_transport,
        sub_args.strict_artifact_policy(),
        sub_args.allow_l0_gaps_lane(),
        sub_args.memory_safe && !sub_args.survey,
        sub_args.survey,
        sub_args.certify_lane(),
        sub_args.hardened,
        sub_args.trust_profile.as_deref(),
        ay_path,
        quiet,
        sub_args.is_single_file
            && !matches!(subcommand, Subcommand::Build | Subcommand::Test)
            && !has_output_path_flag(&sub_args.passthrough),
    )?;
    if let Some(signal_exit) = run_result.signal_exit {
        // A killed compiler is an execution failure, not a proof frontier
        // that the rewrite loop can strengthen. Preserve its conventional
        // shell status instead of collapsing every signal to exit 1.
        return Err(ExitCode::from(signal_exit));
    }
    Ok((cmd_args, run_result))
}

/// Ad-hoc CLI rewrite loop.
fn run_rewrite_loop_fallback(
    rustc: &Path,
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
    ay_path: Option<&Path>,
) -> ExitCode {
    use crate::rewrite_loop::{
        BackpropEngine, BackpropResult, ConvergenceTracker, LoopDecision, RepairArtifact,
        RepairIteration, RepairRunSummary, UnverifiedRewrites, append_audit_entries,
        binary_source_backpropagation_blockers, build_rewrite_records, decision_label,
        describe_restore, print_ai_repair_prompts_for_results, print_iteration_header,
        print_iteration_summary, print_loop_summary, rewrite_rejection,
        strengthen_failures_with_binary_source_provenance, write_repair_artifact,
        write_repair_markdown,
    };
    let mut audit_trail = trust_backprop::AuditTrail::new();

    let max_iterations = sub_args.max_iterations;

    // Intent is a first-class repair input: a design doc / chat that guides what
    // the AI repair should aim for. Resolved once for the whole loop.
    let repair_intent = match crate::intent::resolve_intent(
        sub_args.intent.as_deref(),
        config.intent.as_ref(),
        sub_args.manifest_path.as_deref().map(Path::new),
    ) {
        Ok(intent) => intent,
        Err(message) => {
            eprintln!("targo trust: error: {message}");
            return ExitCode::from(2);
        }
    };
    if let Some(intent) = &repair_intent {
        eprintln!(
            "  Intent input: {} ({} bytes) — guiding AI repair prompts",
            intent.source.label(),
            intent.text.len()
        );
    }
    let repair_intent_excerpt = repair_intent.as_ref().map(|intent| intent.excerpt(2000));

    let mut tracker = ConvergenceTracker::new(max_iterations);
    let mut backprop = BackpropEngine::with_protected(&config.skip_functions);
    let binary_source_provenance = match runtime_binary_source_provenance_for_rewrite_loop(sub_args)
    {
        Ok(source_provenance) => source_provenance,
        Err(message) => {
            eprintln!("targo trust: error: {message}");
            return ExitCode::from(2);
        }
    };

    let mut default_source_file: Option<String> = None;
    if sub_args.is_single_file {
        let file_path = std::fs::canonicalize(
            sub_args.single_file_path().expect("single-file mode should have a file path"),
        )
        .unwrap_or_else(|_| {
            PathBuf::from(
                sub_args.single_file_path().expect("single-file mode should have a file path"),
            )
        });
        let path_str = file_path.display().to_string();
        backprop.set_default_source_file(path_str.clone());
        default_source_file = Some(path_str);
    }

    let loop_start = Instant::now();
    let mut last_frontier = ProofFrontier { proved: 0, failed: 0, unknown: 0 };
    let mut last_success = false;
    let mut last_decision = LoopDecision::Continue { verdict: "starting" };
    let mut repair_iterations = Vec::new();
    // Edits that are on disk and still owe the compiler a verdict. At most one
    // generation is ever outstanding: the loop judges it before writing more.
    let mut unverified: Option<UnverifiedRewrites> = None;
    // Set when an undo could not be completed, which is the one state where the
    // tree holds content neither the user nor a judged rewrite produced.
    let mut restore_failed = false;

    eprintln!();
    eprintln!("targo trust: starting rewrite loop (max {} iterations)", max_iterations);

    for iteration in 0..max_iterations {
        let iter_start = Instant::now();
        let mut halted_by_rejection = None;
        print_iteration_header(iteration, max_iterations);

        // Step 1: Prove -- run the compiler and capture results.
        let (cmd_args, run_result) = match rewrite_loop_prove_once(
            rustc,
            subcommand,
            sub_args,
            config,
            selected_codegen_backend,
            supports_json_transport,
            ay_path,
            iteration > 0,
        ) {
            Ok(captured) => captured,
            Err(exit_code) => return exit_code,
        };

        // Step 2b: Backprop AI prompt -- for every Failed/Unknown obligation,
        // print an explicit AI prompt asking the assistant to add the strongest
        // `#[requires]`/`#[ensures]` to repair the failing function. The prompt
        // is paired with a `claude --dangerously-skip-permissions` invocation
        // so the operator can pipe it straight in.
        print_ai_repair_prompts_for_results(
            &run_result.verification_results,
            default_source_file.as_deref(),
            repair_intent_excerpt.as_deref(),
        );

        if let Some(gap) = hardened_proof_gate_failure_for_results(
            &run_result.verification_results,
            &run_result.compiler_diagnostics,
            &run_result.report_subject,
            &run_result.zero_obligation_functions,
            Some(&run_result.live_transport_authority),
            config,
            sub_args.hardened,
            sub_args.trust_profile.as_deref(),
        ) {
            eprintln!(
                "targo trust: hardened proof evidence gate failed in rewrite loop: {}/{} hardened obligations have publishable native proof evidence",
                gap.proof_evidence_entries, gap.hardened_obligations
            );
            return ExitCode::FAILURE;
        }

        let binary_source_blockers = binary_source_backpropagation_blockers(
            &run_result.verification_results,
            binary_source_provenance.as_ref(),
        );
        if !binary_source_blockers.is_empty() {
            print_runtime_binary_source_backpropagation_blocker(&binary_source_blockers);
            return ExitCode::FAILURE;
        }

        // Step 2: Strengthen -- analyze failures and propose rewrites.
        let obligations = run_result.verification_results.len();
        let frontier = ProofFrontier::from_results(&run_result.verification_results);
        let iteration_success = rewrite_iteration_success(
            run_result.exit_code,
            &run_result.verification_results,
            &run_result.zero_obligation_functions,
            run_result.coverage.as_ref(),
            &run_result.missing_target_coverage,
            sub_args.strict_artifact_policy(),
        );
        let strengthen = strengthen_failures_with_binary_source_provenance(
            &run_result.verification_results,
            binary_source_provenance.as_ref(),
        );
        let proposal_summaries = strengthen.summaries();

        // Step 3: Converge -- judge what this run measured. The verdict comes
        // before the next edit is written, because this same run is the first
        // and only judgement on the edits the previous iteration made: deciding
        // after applying would stack an unjudged generation on top of a
        // generation already known to be bad.
        let decision = tracker.observe(frontier.clone());
        print_iteration_summary(&frontier, &proposal_summaries, &decision, &iter_start.elapsed());

        // Step 4: Adjudicate the outstanding edits against that verdict, and
        // take them back if they did not earn their place.
        if let Some(pending) = unverified.take() {
            // Taking the generation out is the accept: without a rejection its
            // checkpoint has done its job and the edits stand.
            if let Some(rejection) =
                rewrite_rejection(run_result.exit_code, obligations, &decision)
            {
                eprintln!("{}", describe_restore(&pending, rejection));
                match pending.restore() {
                    Ok(files) => {
                        eprintln!("  Restored {files} file(s) to their pre-rewrite content.");
                    }
                    Err(error) => {
                        // The tree now holds content neither we nor the user
                        // authored. Say so loudly and stop touching it.
                        eprintln!(
                            "targo trust: error: could not restore the pre-rewrite source: {error}"
                        );
                        eprintln!(
                            "targo trust: the working tree holds ungraded rewrites -- inspect it before rebuilding."
                        );
                        restore_failed = true;
                    }
                }
                halted_by_rejection = Some(rejection);
            }
        }

        // Step 5: Backprop -- apply rewrites to source via trust-backprop, but
        // only while the loop is still moving forward.
        let mut bp_result = BackpropResult::nothing_applied(0, 0);
        let keep_rewriting = halted_by_rejection.is_none()
            && !restore_failed
            && !iteration_success
            && matches!(decision, LoopDecision::Continue { .. });
        if keep_rewriting && !strengthen.proposals.is_empty() {
            bp_result = backprop.apply_strengthen_proposals(&strengthen.proposals, 0, 0);
            eprintln!(
                "  Backprop: {} rewrites applied to {} files ({} governance skips, {} limit skips, {} queued for review)",
                bp_result.rewrites_applied,
                bp_result.files_modified,
                bp_result.governance_skips,
                bp_result.limit_skips,
                bp_result.pending_rewrites.len(),
            );
            if let Some(checkpoint) = bp_result.pre_apply_checkpoint.take() {
                unverified =
                    UnverifiedRewrites::new(iteration + 1, checkpoint, bp_result.rewrites_applied);
            }
        }
        let iter_elapsed = iter_start.elapsed();

        let proposal_records = strengthen.proposal_records();
        let rewrite_records = build_rewrite_records(
            &bp_result.applied_rewrites,
            &bp_result.pending_rewrites,
            &bp_result.file_results,
        );
        append_audit_entries(&mut audit_trail, iteration + 1, &rewrite_records);
        repair_iterations.push(RepairIteration {
            iteration: iteration + 1,
            command: cmd_args,
            exit_code: run_result.exit_code,
            frontier: frontier.clone(),
            results: run_result.verification_results.clone(),
            compiler_diagnostics: run_result.compiler_diagnostics,
            failures: strengthen.failures,
            proposals: proposal_records,
            applied_rewrites: bp_result.applied_rewrites.clone(),
            pending_rewrites: bp_result.pending_rewrites.clone(),
            rewrite_records,
            governance_skips: bp_result.governance_skips,
            limit_skips: bp_result.limit_skips,
            duration_ms: iter_elapsed.as_millis() as u64,
        });

        if let Some(rejection) = halted_by_rejection {
            // This run measured source that has just been reverted, so the
            // frontier the user is left with is the one before it.
            last_decision = LoopDecision::Regressed { reason: rejection.reason() };
            last_success = false;
            break;
        }
        last_frontier = frontier;
        last_success = iteration_success;
        last_decision = decision.clone();

        match &decision {
            LoopDecision::Continue { .. } => {
                if iteration_success {
                    eprintln!("  All obligations proved -- stopping early.");
                    last_decision = LoopDecision::Converged { stable_rounds: 1 };
                    break;
                }
                if strengthen.proposals.is_empty() {
                    if last_frontier.failed > 0 {
                        eprintln!(
                            "  No proposals generated for {} failures -- stopping.",
                            last_frontier.failed
                        );
                    } else {
                        eprintln!(
                            "  No proposals generated for incomplete proof frontier -- stopping."
                        );
                    }
                    break;
                }
            }
            LoopDecision::Converged { .. }
            | LoopDecision::Regressed { .. }
            | LoopDecision::IterationLimitReached => break,
        }
    }

    // Nothing may outlive the loop unjudged. The loop only writes a generation
    // when a later prove pass will grade it, which is why the last iteration
    // measures instead of editing; this is the fail-closed backstop for a future
    // change to that ordering, not a second verdict path. An edit nobody graded
    // goes back, and the run does not claim success either way.
    if let Some(pending) = unverified.take() {
        eprintln!();
        eprintln!(
            "targo trust: reverting {} rewrite(s) from iteration {} that no prove pass graded",
            pending.rewrites(),
            pending.iteration()
        );
        match pending.restore() {
            Ok(files) => eprintln!("  Restored {files} file(s) to their pre-rewrite content."),
            Err(error) => {
                eprintln!("targo trust: error: could not restore the pre-rewrite source: {error}");
                eprintln!(
                    "targo trust: the working tree holds ungraded rewrites -- inspect it before rebuilding."
                );
                restore_failed = true;
            }
        }
        last_success = false;
    }

    let total_elapsed = loop_start.elapsed();
    print_loop_summary(&tracker, &last_frontier, &total_elapsed, &last_decision);

    if let Some(dir) = sub_args.report_dir.as_deref() {
        let artifact = RepairArtifact {
            schema_version: "0.2.0",
            summary: RepairRunSummary {
                iterations: tracker.iteration_count(),
                succeeded: last_success,
                final_frontier: last_frontier.clone(),
                final_decision: decision_label(&last_decision),
                total_duration_ms: total_elapsed.as_millis() as u64,
                exact_source_type_ownership_artifact_digest: binary_source_provenance
                    .as_ref()
                    .and_then(|provenance| provenance.exact_source_type_ownership_artifact_digest())
                    .map(str::to_string),
            },
            iterations: repair_iterations,
            audit_trail,
        };
        let output_dir = Path::new(dir);
        match write_repair_artifact(output_dir, &artifact) {
            Ok(()) => eprintln!("targo trust: wrote {dir}/repair.json"),
            Err(e) => eprintln!("targo trust: failed to write repair artifact: {e}"),
        }
        match write_repair_markdown(output_dir, &artifact) {
            Ok(()) => eprintln!("targo trust: wrote {dir}/repair.md"),
            Err(e) => eprintln!("targo trust: failed to write repair markdown: {e}"),
        }
    }

    // A tree left holding rewrites that could neither be judged nor undone is a
    // failed run whatever the last frontier said.
    if last_success && !restore_failed { ExitCode::SUCCESS } else { ExitCode::FAILURE }
}

pub(super) fn rewrite_iteration_success(
    compiler_exit: i32,
    results: &[VerificationResult],
    zero_obligation_functions: &[String],
    coverage: Option<&trust_types::VerificationCoverage>,
    missing_target_coverage: &[CargoTargetIdentity],
    require_coverage: bool,
) -> bool {
    let (counts, _transport_defects) = partition_outcome_counts(results);
    // Trust (completeness-gap ruling, 2026-07-25): the rewrite loop is a
    // CONVERGENCE criterion, not a build gate, so it keeps the full-discharge
    // predicate (`GateLane::Certify`) rather than following the relaxed default.
    // The loop exists to drive code to a statically proved state; accepting a
    // `runtime_checked` row would declare success on exactly the gap it is trying
    // to close, and it would stop iterating one step early. Its original
    // assertions — runtime-checked is NOT success — are preserved verbatim by
    // this lane.
    evaluate_run_gate(
        GateLane::Certify,
        compiler_exit,
        counts,
        coverage,
        !missing_target_coverage.is_empty(),
        require_coverage,
        zero_obligation_functions.len(),
    )
    .is_success()
}

fn coverage_accounting_overflowed(rows: &[trust_types::CoverageTransportSummary]) -> bool {
    fn overflows(mut values: impl Iterator<Item = usize>) -> bool {
        values.try_fold(0usize, |total, value| total.checked_add(value)).is_none()
    }

    overflows(rows.iter().map(|row| row.eligible))
        || overflows(rows.iter().map(|row| row.processed))
}

fn cargo_test_execution_evidence_blocker(
    compile_succeeded: bool,
    missing_transport: Option<&str>,
    strict_artifact_policy: bool,
    coverage: Option<&trust_types::VerificationCoverage>,
    coverage_overflowed: bool,
    missing_target_coverage: &[CargoTargetIdentity],
) -> Option<String> {
    if !compile_succeeded {
        return Some("Cargo test compile-only phase failed".to_string());
    }
    if let Some(reason) = missing_transport {
        return Some(reason.to_string());
    }
    if strict_artifact_policy
        && (coverage_overflowed
            || coverage.is_none_or(|coverage| !coverage.coverage_complete)
            || !missing_target_coverage.is_empty())
    {
        return Some(
            "strict authenticated coverage was incomplete after the Cargo test compile-only phase"
                .to_string(),
        );
    }
    None
}

#[cfg(test)]
mod selection_and_control_tests {
    use std::path::PathBuf;

    use sha2::Digest as _;

    #[cfg(unix)]
    use super::TRUSTD_DISABLE_ENV;
    use super::TrustFlags;
    use super::{
        CertifiedTestExecutionCompletionScope, CertifiedTestExecutionPhaseState,
        CertifiedTestExecutionReport, TRUST_MEMORY_JOBSERVER_ENV, TRUST_MEMORY_JOBSERVER_SOCK_ENV,
        TrustPolicySelection, VerificationControls, VerificationSession,
        append_verification_control_args,
        apply_cargo_child_rustc_env, apply_cargo_rustflags_env,
        apply_crate_memory_coordination_with, apply_targo_test_monitor_session,
        cargo_args_with_proof_message_format, cargo_manifest_path_arg,
        cargo_rustflags_with_controls, cargo_target_dir, cargo_target_dir_arg,
        cargo_test_compile_only_args, cargo_test_execution_args,
        cargo_test_execution_evidence_blocker, certified_test_execution_platform_blocker,
        child_signal_exit_code, child_status_code, configured_verified_cargo_child_with_memory,
        prepare_ephemeral_single_file_output, record_certified_test_execution_error,
        scrub_proof_compiler_authority_env, selected_package_names_from_selection,
        temp_single_file_output_path, validate_direct_custom_target_extension_tcb,
        verification_cache_target_dir, write_test_execution_authority,
    };
    use crate::config::TrustConfig;
    use crate::pipeline::transport::{CargoTargetIdentity, CargoTestExecutable};
    use crate::pipeline::{CargoRustflags, ResolvedCargoPackage, ResolvedCargoSelection};

    fn s(args: &[&str]) -> Vec<String> {
        args.iter().map(|a| a.to_string()).collect()
    }

    #[test]
    fn certified_test_execution_platform_gate_matches_the_handle_backend() {
        let blocker = certified_test_execution_platform_blocker();
        if cfg!(all(target_os = "linux", any(target_arch = "x86_64", target_arch = "aarch64"))) {
            assert!(blocker.is_none(), "supported host was blocked: {blocker:?}");
        } else {
            assert!(
                blocker.is_some_and(|message| {
                    message.contains("requires Linux x86-64/aarch64 sealed-memfd execveat")
                }),
                "unsupported host did not fail closed: {blocker:?}"
            );
        }
    }

    #[test]
    fn certified_test_pre_spawn_error_remains_blocked_in_the_typed_report() {
        let mut report = CertifiedTestExecutionReport {
            schema: trust_types::CERTIFIED_TEST_EXECUTION_SCHEMA_VERSION.to_string(),
            completion_scope: CertifiedTestExecutionCompletionScope::TopLevelCargoChildExitOnlyV1,
            requested: true,
            scope: trust_types::CERTIFIED_TEST_EXECUTION_SCOPE.to_string(),
            compile_only: false,
            phase_a_status: 0,
            phase_a_success: true,
            phase_b_state: CertifiedTestExecutionPhaseState::Blocked,
            blocker: None,
            phase_b_exit: None,
            authorized_executables: Vec::new(),
            authorized_inventory_sha256: None,
            target_directory: None,
        };
        record_certified_test_execution_error(
            Some(&mut report),
            false,
            "unsupported immutable execution handle",
        );
        assert_eq!(report.phase_b_state, CertifiedTestExecutionPhaseState::Blocked);
        assert_eq!(report.blocker.as_deref(), Some("unsupported immutable execution handle"));
        assert_eq!(report.phase_b_exit, None, "no phase-B Cargo child was started");
    }

    #[test]
    fn certified_test_cargo_child_installs_or_removes_the_complete_authority_tuple() {
        let session = VerificationSession::create().expect("create verification session");
        let controls = VerificationControls {
            policy: TrustPolicySelection::Strict,
            timeout_ms: 5_000,
            function_budget_ms: 120_000,
            hardened_profile: None,
            ay_path: None,
            verification_session: &session.id,
            proof_artifact_root: session.artifact_root(),
        };
        let selection = ResolvedCargoSelection {
            packages: Vec::new(),
            target_directory: session.artifact_root().join("target"),
        };
        let authority_path = session.artifact_root().join("execution-authority.json");
        let authority_sha256 = "0123456789abcdef".repeat(4);
        let args = s(&["test", "--tests"]);
        let rustc = std::path::Path::new("/authenticated/toolchain/bin/trustc");

        let bound = configured_verified_cargo_child_with_memory(
            "unused",
            &args,
            &args,
            rustc,
            &TrustConfig::default(),
            None,
            true,
            true,
            false,
            &controls,
            &TrustFlags::default(),
            &selection,
            true,
            Some((&authority_path, &authority_sha256)),
            |command, _, _| {
                command.env_remove(TRUST_MEMORY_JOBSERVER_ENV);
                command.env(TRUST_MEMORY_JOBSERVER_SOCK_ENV, "/test/trustd.sock");
                Ok(())
            },
        )
        .expect("configure authenticated phase-B Cargo child");
        for (name, expected) in [
            ("TRUST_TARGO_TEST_EXECUTE_FRESH_SESSION", std::ffi::OsStr::new(&session.id)),
            ("TRUST_TARGO_TEST_EXECUTION_MANIFEST", authority_path.as_os_str()),
            ("TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256", std::ffi::OsStr::new(&authority_sha256)),
        ] {
            assert_eq!(
                bound
                    .get_envs()
                    .find(|(key, _)| *key == std::ffi::OsStr::new(name))
                    .map(|(_, value)| value),
                Some(Some(expected)),
                "phase-B Cargo child did not receive exact `{name}` authority"
            );
        }

        let unbound = configured_verified_cargo_child_with_memory(
            "unused",
            &args,
            &args,
            rustc,
            &TrustConfig::default(),
            None,
            true,
            true,
            false,
            &controls,
            &TrustFlags::default(),
            &selection,
            true,
            None,
            |command, _, _| {
                command.env_remove(TRUST_MEMORY_JOBSERVER_ENV);
                command.env(TRUST_MEMORY_JOBSERVER_SOCK_ENV, "/test/trustd.sock");
                Ok(())
            },
        )
        .expect("configure Cargo child without execution authority");
        for name in [
            "TRUST_TARGO_TEST_EXECUTE_FRESH_SESSION",
            "TRUST_TARGO_TEST_EXECUTION_MANIFEST",
            "TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256",
        ] {
            assert_eq!(
                unbound
                    .get_envs()
                    .find(|(key, _)| *key == std::ffi::OsStr::new(name))
                    .map(|(_, value)| value),
                Some(None),
                "unbound Cargo child did not explicitly remove `{name}`"
            );
        }
    }

    #[test]
    fn proof_message_format_is_one_authenticated_json_stream_before_passthrough() {
        assert_eq!(
            cargo_args_with_proof_message_format(&s(&[
                "test",
                "--message-format=json-render-diagnostics",
                "--message-format",
                "short",
                "--",
                "--nocapture",
            ]))
            .expect("canonical proof format"),
            s(&["test", "--message-format=json", "--", "--nocapture"]),
        );
        assert_eq!(
            cargo_args_with_proof_message_format(&s(&["build"])).expect("insert proof format"),
            s(&["build", "--message-format=json"]),
        );
        assert_eq!(
            cargo_args_with_proof_message_format(&s(&["build", "--message-format", "--release",]))
                .expect_err("an option cannot be consumed as the format value"),
            "--message-format requires a value",
        );
    }

    #[test]
    fn cargo_test_two_phase_args_preserve_harness_args_and_exclude_doctests() {
        let original =
            s(&["test", "--release", "name_filter", "--message-format=short", "--", "--nocapture"]);
        assert_eq!(
            cargo_test_compile_only_args(&original).expect("compile phase"),
            s(&[
                "test",
                "--release",
                "name_filter",
                "--no-run",
                "--message-format=json",
                "--",
                "--nocapture",
            ])
        );
        assert_eq!(
            cargo_test_execution_args(&original).expect("execution phase"),
            s(&["test", "--release", "name_filter", "--tests", "--", "--nocapture",])
        );

        let selected = s(&["test", "--test", "integration", "--", "--exact"]);
        assert_eq!(
            cargo_test_compile_only_args(&selected).expect("selected compile phase"),
            s(&[
                "test",
                "--test",
                "integration",
                "--no-run",
                "--message-format=json",
                "--",
                "--exact",
            ])
        );
        assert!(
            cargo_test_compile_only_args(&s(&["test", "--doc"]))
                .expect_err("doctest must fail closed")
                .contains("cannot precompile")
        );
    }

    #[test]
    fn cargo_test_execution_requires_complete_structural_evidence() {
        let complete = trust_types::VerificationCoverage::from_counts(2, 2);
        let incomplete = trust_types::VerificationCoverage::from_counts(2, 1);
        assert!(
            cargo_test_execution_evidence_blocker(false, None, false, None, false, &[]).is_some()
        );
        assert!(
            cargo_test_execution_evidence_blocker(
                true,
                Some("missing authenticated transport"),
                false,
                None,
                false,
                &[],
            )
            .is_some()
        );
        assert!(
            cargo_test_execution_evidence_blocker(true, None, true, None, false, &[]).is_some()
        );
        assert!(
            cargo_test_execution_evidence_blocker(true, None, true, Some(&incomplete), false, &[],)
                .is_some()
        );
        assert!(
            cargo_test_execution_evidence_blocker(true, None, true, Some(&complete), true, &[],)
                .is_some()
        );
        assert_eq!(
            cargo_test_execution_evidence_blocker(true, None, true, Some(&complete), false, &[],),
            None
        );
        assert_eq!(
            cargo_test_execution_evidence_blocker(true, None, false, None, false, &[]),
            None,
            "advisory policy still requires transport but does not claim strict coverage"
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_execution_authority_binds_exact_private_executable_inventory() {
        use std::os::unix::fs::PermissionsExt as _;

        let target_root = tempfile::tempdir().expect("target directory");
        let toolchain_root = tempfile::tempdir().expect("toolchain directory");
        let executable = target_root.path().join("fixture-test");
        std::fs::write(&executable, b"authenticated test bytes").expect("write executable");
        std::fs::set_permissions(&executable, std::fs::Permissions::from_mode(0o755))
            .expect("mark executable");
        let target = CargoTargetIdentity {
            package_id: "path+file:///fixture#demo@0.1.0".to_string(),
            package_name: "demo".to_string(),
            target_name: "fixture".to_string(),
            target_kinds: vec!["test".to_string()],
            compile_target: "host".to_string(),
            compile_mode: "test".to_string(),
            compile_kind: "target".to_string(),
            unit_identity_sha256: "c".repeat(64),
            compile_target_spec_sha256: None,
            proof_unit_index: 0,
            proof_unit_mode: "test".to_string(),
            proof_unit_role: "primary".to_string(),
            semantics_sha256: "a".repeat(64),
        };
        let inventory = [CargoTestExecutable {
            target: target.clone(),
            path: executable.canonicalize().expect("canonical executable"),
            phase_a_sha256: format!("{:x}", sha2::Sha256::digest(b"authenticated test bytes")),
        }]
        .into_iter()
        .collect();
        let session = VerificationSession::create().expect("verification session");
        let manifest = write_test_execution_authority(
            &session,
            target_root.path(),
            toolchain_root.path(),
            &inventory,
        )
        .expect("write execution authority");
        let metadata = std::fs::symlink_metadata(&manifest.path).expect("manifest metadata");
        assert_eq!(metadata.permissions().mode() & 0o777, 0o600);
        let value: serde_json::Value = serde_json::from_slice(
            &std::fs::read(&manifest.path).expect("read execution authority"),
        )
        .expect("parse execution authority");
        assert_eq!(value["schema"], "trust.targo-test-execution-authority.v1");
        assert_eq!(value["verification_session"], session.id);
        assert_eq!(value["executables"].as_array().map(Vec::len), Some(1));
        assert_eq!(value["executables"][0]["size"], 24);
        assert_eq!(value["executables"][0]["sha256"].as_str().map(str::len), Some(64));
        assert_eq!(
            manifest.inventory_sha256,
            format!(
                "{:x}",
                sha2::Sha256::digest(
                    std::fs::read(&manifest.path).expect("read bound execution authority")
                )
            ),
            "the digest passed to phase-B Cargo must bind the exact manifest bytes"
        );
        assert_eq!(manifest.executables.len(), 1);
        assert_eq!(
            manifest.target_directory,
            target_root.path().canonicalize().unwrap().to_str().unwrap()
        );

        let second = target_root.path().join("fixture-test-second");
        std::fs::write(&second, b"second authenticated test").expect("write second executable");
        std::fs::set_permissions(&second, std::fs::Permissions::from_mode(0o755))
            .expect("mark second executable");
        let ambiguous = [
            CargoTestExecutable {
                target: target.clone(),
                path: executable.canonicalize().expect("canonical executable"),
                phase_a_sha256: format!("{:x}", sha2::Sha256::digest(b"authenticated test bytes")),
            },
            CargoTestExecutable {
                target,
                path: second.canonicalize().expect("canonical second executable"),
                phase_a_sha256: format!("{:x}", sha2::Sha256::digest(b"second authenticated test")),
            },
        ]
        .into_iter()
        .collect();
        let second_session = VerificationSession::create().expect("second verification session");
        assert!(
            write_test_execution_authority(
                &second_session,
                target_root.path(),
                toolchain_root.path(),
                &ambiguous,
            )
            .expect_err("one Cargo target cannot authorize two executable identities")
            .contains("ambiguous executable paths")
        );

        let overlapping_session =
            VerificationSession::create().expect("overlap verification session");
        assert!(
            write_test_execution_authority(
                &overlapping_session,
                target_root.path(),
                target_root.path(),
                &inventory,
            )
            .expect_err("project artifacts must never live inside the toolchain TCB")
            .contains("overlaps authenticated Trust toolchain root")
        );
    }

    #[cfg(unix)]
    #[test]
    fn compiler_process_guard_times_out_the_process_group() {
        let mut command = std::process::Command::new("/bin/sh");
        command.args(["-c", "sleep 30 & wait"]);
        super::CompilerProcessGuard::configure(&mut command);
        let mut child = command.spawn().expect("spawn hanging compiler fixture");
        let mut guard =
            super::CompilerProcessGuard::start(child.id(), std::time::Duration::from_millis(100));
        let _ = super::wait_for_compiler_process(&mut child, &mut guard);
        assert!(guard.finish().expect_err("timeout must fail").contains("timeout"));
    }

    #[cfg(unix)]
    #[test]
    fn compiler_process_guard_reaps_background_descendants_before_leader() {
        let mut command = std::process::Command::new("/bin/sh");
        command.args(["-c", "sleep 30 & printf '%s' \"$!\" >&2; exit 0"]);
        command.stderr(std::process::Stdio::piped());
        super::CompilerProcessGuard::configure(&mut command);
        let mut child = command.spawn().expect("spawn background compiler fixture");
        let stderr = child.stderr.take().expect("stderr pipe");
        let mut guard =
            super::CompilerProcessGuard::start(child.id(), std::time::Duration::from_secs(2));
        let _ = super::wait_for_compiler_process(&mut child, &mut guard).expect("wait compiler");
        guard.finish().expect("natural exit");
        let mut pid_text = String::new();
        std::io::Read::read_to_string(&mut std::io::BufReader::new(stderr), &mut pid_text)
            .expect("read pid");
        let pid: i32 = pid_text.parse().expect("numeric pid");
        // The process-group kill is synchronous, but the kernel may expose a
        // just-killed descendant briefly while its exit is being reaped.
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(2);
        while unsafe { libc::kill(pid, 0) } == 0 && std::time::Instant::now() < deadline {
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        assert_ne!(unsafe { libc::kill(pid, 0) }, 0, "background descendant survived");
    }

    #[cfg(any(unix, windows))]
    #[test]
    fn portable_compiler_process_leader_wait_enforces_deadline_and_reaps() {
        #[cfg(unix)]
        let mut command = {
            let mut command = std::process::Command::new("/bin/sh");
            command.args(["-c", "sleep 30"]);
            command
        };
        #[cfg(windows)]
        let mut command = {
            let mut command = std::process::Command::new("cmd.exe");
            command.args(["/C", "ping -n 30 127.0.0.1 >NUL"]);
            command
        };
        let mut child = command.spawn().expect("spawn hanging compiler leader fixture");
        let timed_out = std::sync::atomic::AtomicBool::new(false);
        let deadline = std::time::Instant::now().checked_add(std::time::Duration::from_millis(100));
        let status = super::wait_for_compiler_leader_until(&mut child, deadline, &timed_out)
            .expect("kill and reap compiler leader");
        assert!(timed_out.load(std::sync::atomic::Ordering::Acquire));
        assert!(!status.success());
        assert!(child.try_wait().expect("query reaped child").is_some());
    }

    #[cfg(any(unix, windows))]
    #[test]
    fn compiler_process_pipe_drain_does_not_hide_timeout() {
        #[cfg(unix)]
        let mut command = {
            let mut command = std::process::Command::new("/bin/sh");
            command.args(["-c", "sleep 30"]);
            command
        };
        #[cfg(windows)]
        let mut command = {
            let mut command = std::process::Command::new("cmd.exe");
            command.args(["/C", "ping -n 30 127.0.0.1 >NUL"]);
            command
        };
        command.stderr(std::process::Stdio::piped());
        super::CompilerProcessGuard::configure(&mut command);
        let started = std::time::Instant::now();
        let mut child = command.spawn().expect("spawn hanging compiler pipe fixture");
        let stderr = child.stderr.take().expect("compiler stderr pipe");
        let output =
            super::spawn_compiler_stderr_parser(stderr, false, false, false, String::new(), false);
        let mut guard =
            super::CompilerProcessGuard::start(child.id(), std::time::Duration::from_millis(100));

        let _ = super::wait_for_compiler_process(&mut child, &mut guard).expect("wait compiler");
        assert!(guard.finish().expect_err("timeout must fail").contains("timeout"));
        super::receive_compiler_output(output, "test compiler stderr")
            .expect("killed compiler must close stderr");
        assert!(started.elapsed() < std::time::Duration::from_secs(5));
    }

    fn package(name: &str, id: &str) -> ResolvedCargoPackage {
        ResolvedCargoPackage {
            id: id.to_string(),
            name: name.to_string(),
            root: PathBuf::from(format!("/workspace/{name}")),
        }
    }

    fn selection(packages: Vec<ResolvedCargoPackage>) -> ResolvedCargoSelection {
        ResolvedCargoSelection { packages, target_directory: PathBuf::from("/workspace/target") }
    }

    #[test]
    fn manifest_path_arg_handles_both_spellings() {
        assert_eq!(
            cargo_manifest_path_arg(&s(&["build", "--manifest-path", "crates/x/Cargo.toml"])),
            Some(std::path::PathBuf::from("crates/x/Cargo.toml"))
        );
        assert_eq!(
            cargo_manifest_path_arg(&s(&["build", "--manifest-path=a/Cargo.toml"])),
            Some(std::path::PathBuf::from("a/Cargo.toml"))
        );
        assert_eq!(cargo_manifest_path_arg(&s(&["build"])), None);
    }

    #[test]
    fn custom_target_tcb_rejects_oversized_input_before_json_parsing() {
        let root = tempfile::tempdir().expect("custom target fixture");
        let target = root.path().join("oversized.json");
        let file = std::fs::File::create(&target).expect("create target");
        file.set_len(crate::input_limits::MAX_RELEASE_METADATA_BYTES as u64 + 1)
            .expect("oversize target");
        let error = validate_direct_custom_target_extension_tcb(
            target.to_str().expect("UTF-8 target path"),
        )
        .expect_err("oversized custom target must fail closed");
        assert!(error.contains("safety limit"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn custom_target_tcb_rejects_leaf_symlink() {
        use std::os::unix::fs::symlink;

        let root = tempfile::tempdir().expect("custom target fixture");
        let target = root.path().join("target.json");
        let linked = root.path().join("linked.json");
        std::fs::write(&target, "{}").expect("write target");
        symlink(&target, &linked).expect("link target");
        let error = validate_direct_custom_target_extension_tcb(
            linked.to_str().expect("UTF-8 target path"),
        )
        .expect_err("symlinked custom target must fail closed");
        assert!(error.contains("not a regular file"), "{error}");
    }

    #[test]
    fn raw_ambient_verifier_controls_are_removed_from_child_processes() {
        let mut command = std::process::Command::new("unused");
        command.env("TRUST_VERIFY", "1");
        command.env("TRUST_DUMP_ONLY", "1");
        command.env("TRUST_NO_VERIFY", "1");
        scrub_proof_compiler_authority_env(&mut command);
        for removed in ["TRUST_VERIFY", "TRUST_DUMP_ONLY", "TRUST_NO_VERIFY"] {
            assert!(
                command.get_envs().any(|(name, value)| {
                    name == std::ffi::OsStr::new(removed) && value.is_none()
                })
            );
        }
    }

    #[test]
    fn test_monitor_marker_is_session_bound_and_test_only() {
        let mut test_command = std::process::Command::new("unused");
        apply_targo_test_monitor_session(&mut test_command, true, "fresh-test-session");
        assert!(test_command.get_envs().any(|(name, value)| {
            name == std::ffi::OsStr::new("TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION")
                && value == Some(std::ffi::OsStr::new("fresh-test-session"))
        }));

        let mut build_command = std::process::Command::new("unused");
        build_command.env("TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION", "ambient");
        apply_targo_test_monitor_session(&mut build_command, false, "fresh-build-session");
        assert!(build_command.get_envs().any(|(name, value)| {
            name == std::ffi::OsStr::new("TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION")
                && value.is_none()
        }));
    }

    #[test]
    fn cargo_child_pins_both_compiler_configuration_spellings() {
        let mut command = std::process::Command::new("unused");
        let compiler = std::path::Path::new("/authenticated/toolchain/trustc");
        apply_cargo_child_rustc_env(&mut command, compiler);
        let envs = command.get_envs().collect::<Vec<_>>();
        for name in ["RUSTC", "CARGO_BUILD_RUSTC"] {
            assert!(envs.iter().any(|(key, value)| {
                *key == std::ffi::OsStr::new(name)
                    && value.is_some_and(|value| value == compiler.as_os_str())
            }));
        }
    }

    #[test]
    fn trust_cg_cargo_policy_disables_incremental_before_unit_construction() {
        let mut command = std::process::Command::new("unused");
        let session = VerificationSession::create().expect("create session");
        let controls = VerificationControls {
            policy: TrustPolicySelection::Strict,
            timeout_ms: 5000,
            function_budget_ms: 120_000,
            hardened_profile: None,
            ay_path: None,
            verification_session: "trust-cg-incremental-test",
            proof_artifact_root: session.artifact_root(),
        };
        apply_cargo_rustflags_env(
            &mut command,
            &TrustConfig::default(),
            Some("trust-cg"),
            true,
            true,
            false,
            &controls,
            &TrustFlags::default(),
        )
        .expect("configure trust-cg Cargo environment");
        assert!(command.get_envs().any(|(name, value)| {
            name == std::ffi::OsStr::new("CARGO_INCREMENTAL")
                && value == Some(std::ffi::OsStr::new("0"))
        }));
    }

    #[cfg(unix)]
    #[test]
    fn unix_file_only_override_is_rejected_without_exporting_an_authority() {
        let root = std::env::temp_dir().join(format!(
            "targo-trust-memory-env-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let args = s(&["build", "--target-dir", root.to_str().expect("UTF-8 temp path")]);
        let mut command = std::process::Command::new("unused");
        command.env(TRUST_MEMORY_JOBSERVER_SOCK_ENV, "/tmp/attacker.sock");
        command.env(TRUST_MEMORY_JOBSERVER_ENV, "/tmp/attacker.tokens");
        let error =
            apply_crate_memory_coordination_with(&mut command, &args, None, None, false, |_| {
                panic!("disabled lane must not probe or start a daemon")
            })
            .expect_err("Unix file-only mode must fail closed");

        let envs = command.get_envs().collect::<Vec<_>>();
        assert!(envs.iter().any(|(name, value)| {
            *name == std::ffi::OsStr::new(TRUST_MEMORY_JOBSERVER_ENV) && value.is_none()
        }));
        assert!(envs.iter().any(|(name, value)| {
            *name == std::ffi::OsStr::new(TRUST_MEMORY_JOBSERVER_SOCK_ENV) && value.is_none()
        }));
        assert!(error.contains("file-only authority"));
        let _ = std::fs::remove_dir_all(root);
    }

    #[cfg(unix)]
    #[test]
    fn healthy_unix_memory_domain_is_shared_across_target_directories() {
        let root = std::env::temp_dir().join(format!(
            "targo-trust-memory-healthy-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let member = root.join("member");
        let target = root.join("metadata-target");
        let manifest = member.join("Cargo.toml");
        let args = s(&["check", "--manifest-path", manifest.to_str().expect("UTF-8 temp path")]);
        let mut command = std::process::Command::new("unused");
        command.env(TRUSTD_DISABLE_ENV, "false");
        let expected = trust_router::coordinator::host_socket_path()
            .expect("private per-user trustd endpoint");
        apply_crate_memory_coordination_with(
            &mut command,
            &args,
            Some(&target),
            Some(std::ffi::OsStr::new("/tmp/inherited.tokens")),
            true,
            |socket| socket == expected,
        )
        .expect("exact daemon is ready");
        assert!(command.get_envs().any(|(name, value)| {
            name == std::ffi::OsStr::new(TRUST_MEMORY_JOBSERVER_SOCK_ENV)
                && value == Some(expected.as_os_str())
        }));
        assert!(command.get_envs().any(|(name, value)| {
            name == std::ffi::OsStr::new(TRUST_MEMORY_JOBSERVER_ENV) && value.is_none()
        }));
        assert!(command.get_envs().any(|(name, value)| {
            name == std::ffi::OsStr::new(TRUSTD_DISABLE_ENV) && value.is_none()
        }));
        assert_ne!(expected, target.join("trust-memory-jobserver.sock"));
        assert_ne!(expected, member.join("target/trust-memory-jobserver.sock"));

        let other_target = root.join("independent-target");
        let other_args =
            s(&["check", "--target-dir", other_target.to_str().expect("UTF-8 temp path")]);
        let mut other_command = std::process::Command::new("unused");
        apply_crate_memory_coordination_with(
            &mut other_command,
            &other_args,
            Some(&other_target),
            None,
            true,
            |socket| socket == expected,
        )
        .expect("independent target reuses exact host daemon");
        assert!(other_command.get_envs().any(|(name, value)| {
            name == std::ffi::OsStr::new(TRUST_MEMORY_JOBSERVER_SOCK_ENV)
                && value == Some(expected.as_os_str())
        }));
        let _ = std::fs::remove_dir_all(root);
    }

    #[cfg(unix)]
    #[test]
    fn failed_unix_daemon_provisioning_exports_no_fallback_ledger() {
        let root = std::env::temp_dir().join(format!(
            "targo-trust-memory-failure-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let args = s(&["build", "--target-dir", root.to_str().expect("UTF-8 temp path")]);
        let mut command = std::process::Command::new("/validated/toolchain/bin/targo");
        command.env(TRUST_MEMORY_JOBSERVER_ENV, "/tmp/inherited.tokens");
        command.env(TRUST_MEMORY_JOBSERVER_SOCK_ENV, "/tmp/inherited.sock");
        let error = apply_crate_memory_coordination_with(
            &mut command,
            &args,
            None,
            Some(std::ffi::OsStr::new("/tmp/inherited.tokens")),
            true,
            |_| false,
        )
        .expect_err("identity/start failure must block Cargo launch");

        assert!(error.contains("refusing to launch a split-authority Cargo fan-out"));
        assert!(
            error.contains(
                "executable `/validated/toolchain/bin/trustd` with arguments `--recover-after-crash --confirm-no-solvers"
            ),
            "recovery guidance must use the absolute same-sysroot trustd: {error}"
        );
        assert!(!error.contains("run `trustd --recover-after-crash"), "{error}");
        for authority in [TRUST_MEMORY_JOBSERVER_ENV, TRUST_MEMORY_JOBSERVER_SOCK_ENV] {
            assert!(command.get_envs().any(|(name, value)| {
                name == std::ffi::OsStr::new(authority) && value.is_none()
            }));
        }
        let _ = std::fs::remove_dir_all(root);
    }

    #[cfg(not(unix))]
    #[test]
    fn non_unix_verified_crate_mode_fails_without_exporting_an_authority() {
        let root = std::env::temp_dir().join(format!(
            "targo-trust-memory-file-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let args = s(&["check", "--target-dir", root.to_str().expect("UTF-8 temp path")]);
        let mut command = std::process::Command::new("unused");
        command.env(TRUST_MEMORY_JOBSERVER_ENV, "inherited.tokens");
        command.env(TRUST_MEMORY_JOBSERVER_SOCK_ENV, "inherited.sock");
        let error =
            apply_crate_memory_coordination_with(&mut command, &args, None, None, false, |_| {
                panic!("non-Unix has no daemon transport")
            })
            .expect_err("non-Unix must fail before uncoordinated worker fan-out");
        assert!(error.contains("unsupported"));
        for authority in [TRUST_MEMORY_JOBSERVER_ENV, TRUST_MEMORY_JOBSERVER_SOCK_ENV] {
            assert!(command.get_envs().any(|(name, value)| {
                name == std::ffi::OsStr::new(authority) && value.is_none()
            }));
        }
        let _ = std::fs::remove_dir_all(root);
    }

    #[cfg(unix)]
    #[test]
    fn child_signal_status_is_not_collapsed_to_generic_failure() {
        let status = std::process::Command::new("sh")
            .args(["-c", "kill -TERM $$"])
            .status()
            .expect("launch signal fixture");
        assert_eq!(child_signal_exit_code(&status), Some(128 + 15));
        assert_eq!(child_status_code(&status), 128 + 15);
    }

    #[test]
    fn target_dir_arg_handles_both_spellings_and_separator() {
        assert_eq!(
            cargo_target_dir_arg(&s(&["build", "--target-dir", "out/one"])),
            Some(std::path::PathBuf::from("out/one"))
        );
        assert_eq!(
            cargo_target_dir_arg(&s(&["build", "--target-dir=out/two"])),
            Some(std::path::PathBuf::from("out/two"))
        );
        assert_eq!(cargo_target_dir_arg(&s(&["build", "--", "--target-dir=target-code"])), None);
        assert_eq!(cargo_target_dir_arg(&s(&["build", "--target-dir="])), None);
        assert_eq!(
            cargo_target_dir(
                &s(&["test", "--target-dir", "out/phase-a"]),
                Some(std::path::Path::new("/metadata/default-target")),
            ),
            std::path::PathBuf::from("out/phase-a"),
            "the test execution manifest must bind Cargo's CLI target directory"
        );
    }

    #[test]
    fn verification_cache_root_tracks_the_selected_unit_not_the_calling_cwd() {
        let member =
            selection(vec![package("member", "path+file:///workspace/member#member@1.0.0")]);
        assert_eq!(
            verification_cache_target_dir(&s(&["check"]), Some(&member)),
            Some(PathBuf::from("/workspace/member/target")),
            "Cargo metadata's default workspace target must not absorb a lone member snapshot"
        );

        let workspace = selection(vec![
            package("member", "path+file:///workspace/member#member@1.0.0"),
            package("other", "path+file:///workspace/other#other@1.0.0"),
        ]);
        assert_eq!(
            verification_cache_target_dir(&s(&["check", "--workspace"]), Some(&workspace)),
            Some(PathBuf::from("/workspace/target")),
            "an aggregate selection retains Cargo's authenticated target directory"
        );

        assert_eq!(
            verification_cache_target_dir(
                &s(&["check", "--target-dir", "/explicit/target"]),
                Some(&member),
            ),
            Some(PathBuf::from("/explicit/target")),
            "an explicit Cargo target directory keeps CLI precedence"
        );

        let source_root = tempfile::tempdir().expect("single-file cache fixture");
        let source = source_root.path().join("demo.rs");
        std::fs::write(&source, "fn main() {}\n").expect("write single-file source");
        let canonical_source_root =
            std::fs::canonicalize(source_root.path()).expect("canonical single-file root");
        assert_eq!(
            verification_cache_target_dir(&[source.display().to_string()], None),
            Some(canonical_source_root.join("target")),
        );
        assert_eq!(verification_cache_target_dir(&s(&["check"]), None), None);
    }

    #[test]
    fn canonical_selection_names_primary_packages_for_globs_workspaces_and_defaults() {
        let resolved = selection(vec![
            package("z-last", "path+file:///workspace/z#z-last@1.0.0"),
            package("a-first", "path+file:///workspace/a#a-first@1.0.0"),
            package("a-first", "registry+https://example.invalid#a-first@2.0.0"),
        ]);
        assert_eq!(
            selected_package_names_from_selection(&resolved),
            Some("a-first,z-last".to_string())
        );
    }

    #[test]
    fn verification_sessions_are_unique_and_injected_in_both_rustflags_encodings() {
        let first = VerificationSession::create().expect("create first session");
        let second = VerificationSession::create().expect("create second session");
        assert_ne!(first.id, second.id);
        for id in [&first.id, &second.id] {
            assert_eq!(id.len(), 64, "session ID must carry 256 random bits");
            assert!(
                id.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
                "session ID must use canonical lowercase hexadecimal: {id}"
            );
            assert!(
                !id.contains("trust-verify-session") && !id.contains(std::path::MAIN_SEPARATOR),
                "session ID must be an in-memory nonce, not a tempfile-derived path/name"
            );
        }
        assert_ne!(first.artifact_root(), second.artifact_root());
        assert!(first.artifact_root().is_dir());
        assert!(second.artifact_root().is_dir());
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;

            assert_eq!(
                std::fs::metadata(first.artifact_root())
                    .expect("artifact root metadata")
                    .permissions()
                    .mode()
                    & 0o777,
                0o700
            );
        }

        let first_controls = VerificationControls {
            policy: TrustPolicySelection::Strict,
            timeout_ms: 5000,
            function_budget_ms: 120_000,
            hardened_profile: None,
            ay_path: None,
            verification_session: &first.id,
            proof_artifact_root: first.artifact_root(),
        };
        let CargoRustflags::Plain(plain) = cargo_rustflags_with_controls(
            CargoRustflags::Plain("-C opt-level=2".to_string()),
            &first_controls,
        )
        .expect("plain controls") else {
            panic!("plain flags changed representation");
        };
        assert!(plain.contains(&format!("-Z trust-verify-session={}", first.id)));
        assert!(plain.contains(&format!(
            "-Z trust-proof-artifact-root={}",
            first.artifact_root().display()
        )));
        assert!(!plain.contains("trust-compiler-cache"));
        assert!(plain.contains("-Z trust-verify-timeout-ms=5000"));
        assert!(plain.contains("-Z trust-verify-function-budget-ms=120000"));
        assert!(!plain.contains("trust-policy="));
        let mut raw_args = Vec::new();
        append_verification_control_args(&mut raw_args, &first_controls)
            .expect("raw rustc controls");
        assert!(raw_args.windows(2).any(|pair| {
            pair[0] == "-Z"
                && pair[1]
                    == format!("trust-proof-artifact-root={}", first.artifact_root().display())
        }));

        let second_controls = VerificationControls {
            policy: TrustPolicySelection::MemorySafe,
            timeout_ms: 7000,
            function_budget_ms: 45_000,
            hardened_profile: Some("unix_hardened"),
            ay_path: None,
            verification_session: &second.id,
            proof_artifact_root: second.artifact_root(),
        };
        let CargoRustflags::Encoded(encoded) = cargo_rustflags_with_controls(
            CargoRustflags::Encoded("-C\x1fopt-level=2".to_string()),
            &second_controls,
        )
        .expect("encoded controls") else {
            panic!("encoded flags changed representation");
        };
        assert!(encoded.contains(&format!("\x1f-Z\x1ftrust-verify-session={}", second.id)));
        assert!(encoded.contains(&format!(
            "\x1f-Z\x1ftrust-proof-artifact-root={}",
            second.artifact_root().display()
        )));
        assert!(encoded.contains("\x1f-Z\x1ftrust-policy=memory-safe"));
        assert!(!encoded.contains("\x1f-Z\x1ftrust-policy=advisory"));
        assert!(encoded.contains("\x1f-Z\x1ftrust-verify-profile=unix_hardened"));
        assert!(encoded.contains("\x1f-Z\x1ftrust-verify-function-budget-ms=45000"));
    }

    #[test]
    fn trustflags_budget_override_wins_over_the_config_derived_default() {
        let session = VerificationSession::create().expect("create session");
        let config_default_budget = crate::config::default_function_budget_ms();
        let override_budget = config_default_budget / 2;
        let controls = VerificationControls {
            policy: TrustPolicySelection::Strict,
            timeout_ms: 5000,
            function_budget_ms: config_default_budget,
            hardened_profile: None,
            ay_path: None,
            verification_session: &session.id,
            proof_artifact_root: session.artifact_root(),
        };
        let merged = cargo_rustflags_with_controls(
            CargoRustflags::Plain("-C opt-level=2".to_string()),
            &controls,
        )
        .expect("render config-derived controls");
        let trustflags = TrustFlags::parse_plain(&format!(
            "-Ztrust-verify-function-budget-ms={override_budget}"
        ))
        .expect("budget override parses");
        let CargoRustflags::Plain(plain) = trustflags.apply_to_cargo_rustflags(merged) else {
            panic!("space-free override keeps the plain representation");
        };
        assert!(
            plain.contains(&format!("-Z trust-verify-function-budget-ms={override_budget}")),
            "{plain}"
        );
        assert!(
            !plain.contains(&format!("trust-verify-function-budget-ms={config_default_budget}")),
            "{plain}"
        );
        assert_eq!(
            plain.matches("trust-verify-function-budget-ms=").count(),
            1,
            "the merged vector must stay duplicate-free for targo's host-boundary parser: {plain}"
        );
        // The rest of the config-derived policy — including the per-run
        // authentication nonce and artifact root — is untouched.
        assert!(plain.contains(&format!("-Z trust-verify-session={}", session.id)), "{plain}");
        assert!(plain.contains("-Z trust-verify-timeout-ms=5000"), "{plain}");
        assert!(plain.contains("-C opt-level=2"), "{plain}");
    }

    #[test]
    fn verification_session_deletes_its_private_artifact_root_on_drop() {
        let artifact_root = {
            let session = VerificationSession::create().expect("create session");
            let artifact_root = session.artifact_root().to_path_buf();
            std::fs::write(artifact_root.join("sentinel"), b"private proof bytes")
                .expect("write private artifact fixture");
            artifact_root
        };
        assert!(
            !artifact_root.exists(),
            "private proof artifact root survived its verification session: {}",
            artifact_root.display()
        );
    }

    #[test]
    fn solver_paths_with_whitespace_force_lossless_encoded_rustflags() {
        let session = VerificationSession::create().expect("create session");
        let controls = VerificationControls {
            policy: TrustPolicySelection::Strict,
            timeout_ms: 5000,
            function_budget_ms: 120_000,
            hardened_profile: None,
            ay_path: Some(std::path::Path::new("/tmp/solver tools/ay")),
            verification_session: &session.id,
            proof_artifact_root: session.artifact_root(),
        };
        let CargoRustflags::Encoded(encoded) = cargo_rustflags_with_controls(
            CargoRustflags::Plain("-C opt-level=2".to_string()),
            &controls,
        )
        .expect("encode path-bearing flags") else {
            panic!("path-bearing rustflags must use Cargo's encoded representation");
        };
        assert!(encoded.contains("\x1ftrust-verify-ay-path=/tmp/solver tools/ay"));
    }

    #[test]
    fn proof_artifact_roots_with_whitespace_force_lossless_encoded_rustflags() {
        let session = VerificationSession::create().expect("create session");
        let controls = VerificationControls {
            policy: TrustPolicySelection::Strict,
            timeout_ms: 5000,
            function_budget_ms: 120_000,
            hardened_profile: None,
            ay_path: None,
            verification_session: &session.id,
            proof_artifact_root: std::path::Path::new("/tmp/proof artifacts/run"),
        };
        let CargoRustflags::Encoded(encoded) = cargo_rustflags_with_controls(
            CargoRustflags::Plain("-C opt-level=2".to_string()),
            &controls,
        )
        .expect("encode root-bearing flags") else {
            panic!("a spaced proof artifact root must use Cargo's encoded representation");
        };
        assert!(encoded.contains("\x1ftrust-proof-artifact-root=/tmp/proof artifacts/run"));
    }

    #[test]
    fn proof_artifact_root_rejects_the_encoded_rustflags_delimiter() {
        let session = VerificationSession::create().expect("create session");
        let controls = VerificationControls {
            policy: TrustPolicySelection::Strict,
            timeout_ms: 5000,
            function_budget_ms: 120_000,
            hardened_profile: None,
            ay_path: None,
            verification_session: &session.id,
            proof_artifact_root: std::path::Path::new("/tmp/proof\u{1f}artifacts"),
        };
        let error = match cargo_rustflags_with_controls(
            CargoRustflags::Plain("-C opt-level=2".to_string()),
            &controls,
        ) {
            Err(error) => error,
            Ok(_) => panic!("the encoded-rustflags delimiter cannot be represented in one flag"),
        };
        assert!(error.contains("U+001F"), "{error}");
    }

    #[test]
    fn ephemeral_single_file_output_is_removed_with_its_guard() {
        let output = temp_single_file_output_path(&["example.rs".to_string()]);
        let directory = output.parent().expect("generated output parent").to_path_buf();
        let args = ["-o".to_string(), output.display().to_string()];

        let guard = prepare_ephemeral_single_file_output(&args, true)
            .expect("prepare output")
            .expect("enabled output guard");
        std::fs::write(&output, b"artifact").expect("write fake compiler artifact");
        assert!(directory.is_dir());
        drop(guard);
        assert!(!directory.exists());
    }
}
