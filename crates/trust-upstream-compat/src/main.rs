// trust-upstream-compat: CLI entry point for upstream compatibility accounting.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// This is a CLI binary, not a reusable library: callers immediately drop the
// Err on print-and-exit. Boxing the error to satisfy `result_large_err`
// across 30+ call sites would be churn for no runtime benefit (the CLI
// returns at most a single Err per invocation).
#![allow(clippy::result_large_err)]

use std::env;
use std::ffi::{OsStr, OsString};
use std::fs::{self, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::{Command as ProcessCommand, ExitCode, ExitStatus, Stdio};

use serde::Serialize;
use trust_upstream_compat::porting::{self, ProofMode};
use trust_upstream_compat::{
    AccountingBundle, CompatibilityBaseline, CompatibilityResultSummary, ExceptionLedger,
    ParseError, TestExceptionLedger, TestInventory, TestInventoryEntry, TestKind, TestOutcome,
    TestProofBundle, TestProofTotals, TestResult, TestResultReport, TestSource,
    TrustAddedTestManifest, UpstreamFixLedger, ValidationFinding, parse_baseline_json,
    parse_baseline_toml, parse_exceptions_json, parse_exceptions_toml, parse_result_summary_json,
    parse_result_summary_toml, parse_test_exceptions_json_for_date,
    parse_test_exceptions_toml_for_date, parse_test_inventory_json, parse_test_inventory_toml,
    parse_test_result_report_json, parse_test_result_report_toml, parse_trust_added_tests_json,
    parse_trust_added_tests_toml, parse_upstream_fixes_json, parse_upstream_fixes_toml,
    validate_accounting_bundle, validate_test_proof_bundle,
};

const HELP: &str = "\
trust-upstream-compat

Usage:
  trust-upstream-compat validate --baseline <path> --exceptions <path> --upstream-fixes <path> [--summary <path>] [--current-upstream-revision <rev>]
  trust-upstream-compat port [--baseline <path>] [--upstream-fixes <path>] [--test-exceptions <path>] [--patch-manifest <path>] [--llm-directives <path>] [--summary-out <path>] [--run-id <id>] [--target-arch <arch>] [--target <target>] [--target-triple <triple>] [--host <host>] [--host-triple <triple>] [--upstream-revision <rev>] [--upstream-remote <url>] [--out-dir <path>] [--execute|--no-execute] [--apply|--no-apply] [--no-fetch] [--scorecard-log <path>] [--bootstrap-args <args>] [--max-files <n>] [--release] [--proof-mode auto|smoke|full]
  trust-upstream-compat --help

Canonical release-facing entry point:
  targo trust domination upstream-tests [port options]

Formats are selected by extension: .json parses as JSON; all other paths parse as TOML.
This binary is an internal compatibility/accounting engine. The run, prove, and
upstream-port aliases remain accepted for compatibility but are intentionally
not part of the release-facing help. The port command defaults to the reviewed
upstream ledger revision with no network fetch, execute+apply, writes porting
scorecards, and uses --proof-mode auto as smoke for --max-files runs and full
otherwise. Pass --upstream-revision rust-lang/rust:HEAD explicitly to refetch
current upstream and open a drift review. It also reapplies the default
deterministic patch manifest and writes an AI-actionable directives artifact
beside the scorecard.
";

const DEFAULT_PORT_BASELINE: &str = "tests/upstream-rust/baseline.toml";
const DEFAULT_PORT_UPSTREAM_FIXES: &str = "tests/upstream-rust/upstream-fixes.toml";
const DEFAULT_PORT_TEST_EXCEPTIONS: &str = "tests/upstream-rust/test-exceptions.toml";
const DEFAULT_PORT_PATCH_MANIFEST: &str = "tests/upstream-rust/patches.toml";
const DEFAULT_PORT_UPSTREAM_REVISION: &str =
    "rust-lang/rust:5e91de65d75d3c849c643f5079509b9e5985a5c0";
const DEFAULT_PORT_UPSTREAM_REMOTE: &str = "https://github.com/rust-lang/rust.git";
const DEFAULT_PORT_OUT_DIR: &str = "reports/upstream-rust/porting/current";
const PORT_BOOTSTRAP_ARGS_ENV: &str = "TRUST_UPSTREAM_RUST_BOOTSTRAP_ARGS";
const TEST_EXCEPTION_VALIDATION_DATE_ENV: &str = "TRUST_UPSTREAM_COMPAT_VALIDATION_DATE";

fn main() -> ExitCode {
    let mut stdout = io::stdout();
    let mut stderr = io::stderr();

    match run(env::args_os(), &mut stdout, &mut stderr) {
        Ok(()) => ExitCode::SUCCESS,
        Err(code) => ExitCode::from(code),
    }
}

fn run<I>(args: I, stdout: &mut dyn Write, stderr: &mut dyn Write) -> Result<(), u8>
where
    I: IntoIterator<Item = OsString>,
{
    let args = args.into_iter().skip(1);
    match parse_args(args).and_then(execute) {
        Ok(CommandOutcome::Success) => Ok(()),
        Ok(CommandOutcome::Help) => write_all(stdout, HELP.as_bytes(), stderr),
        Err(err) => {
            let code = err.exit_code();
            print_error(stderr, &err);
            Err(code)
        }
    }
}

fn execute(command: Command) -> Result<CommandOutcome, CliError> {
    match command {
        Command::Help => Ok(CommandOutcome::Help),
        Command::Validate(options) => {
            let baseline = parse_baseline_file(&options.baseline)?;
            let exceptions = parse_exceptions_file(&options.exceptions)?;
            let upstream_fixes = parse_upstream_fixes_file(&options.upstream_fixes)?;
            let result_summary =
                options.summary.as_deref().map(parse_result_summary_file).transpose()?;

            validate_accounting_bundle(AccountingBundle {
                baseline: &baseline,
                exceptions: Some(&exceptions),
                upstream_fixes: Some(&upstream_fixes),
                result_summary: result_summary.as_ref(),
                current_upstream_revision: options.current_upstream_revision.as_deref(),
            })
            .map_err(CliError::BundleValidation)?;

            Ok(CommandOutcome::Success)
        }
        Command::Run(options) => execute_run(options),
        Command::Prove(options) => {
            let baseline = parse_baseline_file(&options.baseline)?;
            let exceptions = parse_exceptions_file(&options.exceptions)?;
            let upstream_fixes = parse_upstream_fixes_file(&options.upstream_fixes)?;
            let result_summary =
                options.summary.as_deref().map(parse_result_summary_file).transpose()?;
            let test_exception_validation_date = test_exception_validation_date();

            validate_accounting_bundle(AccountingBundle {
                baseline: &baseline,
                exceptions: Some(&exceptions),
                upstream_fixes: Some(&upstream_fixes),
                result_summary: result_summary.as_ref(),
                current_upstream_revision: options.current_upstream_revision.as_deref(),
            })
            .map_err(CliError::BundleValidation)?;

            let inventory = parse_test_inventory_file(&options.inventory)?;
            let results = parse_test_result_report_file(&options.results)?;
            let test_exceptions = parse_test_exceptions_file_for_date(
                &options.test_exceptions,
                &test_exception_validation_date,
            )?;
            let trust_tests = parse_trust_added_tests_file(&options.trust_tests)?;
            let totals = validate_test_proof_bundle(TestProofBundle {
                inventory: &inventory,
                results: &results,
                exceptions: &test_exceptions,
                trust_added_tests: Some(&trust_tests),
                validation_date: &test_exception_validation_date,
                release: options.release,
            })
            .map_err(CliError::BundleValidation)?;

            if let Some(path) = options.proof_summary_out.as_deref() {
                write_proof_summary(path, totals)?;
            }

            Ok(CommandOutcome::Success)
        }
        Command::Port(options) => execute_port(options),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Command {
    Help,
    Validate(ValidateOptions),
    Run(RunOptions),
    Prove(ProveOptions),
    Port(PortOptions),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ValidateOptions {
    baseline: PathBuf,
    exceptions: PathBuf,
    upstream_fixes: PathBuf,
    summary: Option<PathBuf>,
    current_upstream_revision: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RunOptions {
    baseline: PathBuf,
    exceptions: PathBuf,
    upstream_fixes: PathBuf,
    test_exceptions: PathBuf,
    trust_tests: PathBuf,
    out_dir: PathBuf,
    current_upstream_revision: String,
    release: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ProveOptions {
    baseline: PathBuf,
    exceptions: PathBuf,
    upstream_fixes: PathBuf,
    summary: Option<PathBuf>,
    current_upstream_revision: Option<String>,
    inventory: PathBuf,
    results: PathBuf,
    test_exceptions: PathBuf,
    trust_tests: PathBuf,
    release: bool,
    proof_summary_out: Option<PathBuf>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PortOptions {
    baseline: PathBuf,
    upstream_fixes: PathBuf,
    test_exceptions: Option<PathBuf>,
    patch_manifest: Option<PathBuf>,
    llm_directives: Option<PathBuf>,
    summary_out: Option<PathBuf>,
    run_id: Option<String>,
    target_arch: Option<String>,
    target: Option<String>,
    target_triple: Option<String>,
    host: Option<String>,
    host_triple: Option<String>,
    upstream_revision: String,
    upstream_remote: String,
    out_dir: PathBuf,
    execute: bool,
    apply: bool,
    fetch: bool,
    scorecard_log: Option<PathBuf>,
    bootstrap_args: String,
    max_files: Option<usize>,
    release: bool,
    proof_mode: ProofMode,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CommandOutcome {
    Success,
    Help,
}

#[derive(Debug)]
enum CliError {
    Usage(String),
    Read { kind: &'static str, path: PathBuf, source: io::Error },
    Parse { kind: &'static str, path: PathBuf, source: ParseError },
    BundleValidation(Vec<ValidationFinding>),
    Output(io::Error),
    Porting(porting::PortError),
    PortingFailure(u8),
}

impl CliError {
    fn exit_code(&self) -> u8 {
        match self {
            Self::Usage(_) => 2,
            Self::Porting(source) => source.exit_code(),
            Self::PortingFailure(code) => *code,
            Self::Read { .. }
            | Self::Parse { .. }
            | Self::BundleValidation(_)
            | Self::Output(_) => 1,
        }
    }
}

fn parse_args(args: impl IntoIterator<Item = OsString>) -> Result<Command, CliError> {
    let mut args = args.into_iter();
    let Some(command) = args.next() else {
        return Ok(Command::Help);
    };

    if command == OsStr::new("--help") || command == OsStr::new("-h") {
        return Ok(Command::Help);
    }

    if command == OsStr::new("validate") {
        return parse_validate_args(args);
    }

    if command == OsStr::new("run") {
        return parse_run_args(args);
    }

    if command == OsStr::new("prove") {
        return parse_prove_args(args);
    }

    if command == OsStr::new("port") || command == OsStr::new("upstream-port") {
        return parse_port_args(args);
    }

    if command == OsStr::new("trust") {
        return parse_release_facing_port_args(args);
    }

    Err(CliError::Usage(format!("unknown command '{}'", command.to_string_lossy())))
}

fn parse_release_facing_port_args(
    mut args: impl Iterator<Item = OsString>,
) -> Result<Command, CliError> {
    let Some(surface) = args.next() else {
        return Err(CliError::Usage(
            "expected `domination upstream-tests` after `trust`".to_string(),
        ));
    };
    if surface != OsStr::new("domination") && surface != OsStr::new("rust-vs-trust") {
        return Err(CliError::Usage(format!(
            "unknown trust surface '{}'",
            surface.to_string_lossy()
        )));
    }

    let Some(subcommand) = args.next() else {
        return Err(CliError::Usage(format!(
            "expected `upstream-tests` after `trust {}`",
            surface.to_string_lossy()
        )));
    };
    if subcommand != OsStr::new("upstream-tests") && subcommand != OsStr::new("upstream-rust-tests")
    {
        return Err(CliError::Usage(format!(
            "unknown trust {} subcommand '{}'",
            surface.to_string_lossy(),
            subcommand.to_string_lossy()
        )));
    }

    parse_port_args(args)
}

fn parse_validate_args(mut args: impl Iterator<Item = OsString>) -> Result<Command, CliError> {
    let mut baseline = None;
    let mut exceptions = None;
    let mut upstream_fixes = None;
    let mut summary = None;
    let mut current_upstream_revision = None;

    while let Some(arg) = args.next() {
        if arg == OsStr::new("--help") || arg == OsStr::new("-h") {
            return Ok(Command::Help);
        }

        if arg == OsStr::new("--baseline") {
            set_path("--baseline", &mut baseline, args.next())?;
        } else if arg == OsStr::new("--exceptions") {
            set_path("--exceptions", &mut exceptions, args.next())?;
        } else if arg == OsStr::new("--upstream-fixes") {
            set_path("--upstream-fixes", &mut upstream_fixes, args.next())?;
        } else if arg == OsStr::new("--summary") {
            set_path("--summary", &mut summary, args.next())?;
        } else if arg == OsStr::new("--current-upstream-revision") {
            set_string("--current-upstream-revision", &mut current_upstream_revision, args.next())?;
        } else {
            return Err(CliError::Usage(format!(
                "unexpected argument '{}'",
                arg.to_string_lossy()
            )));
        }
    }

    let baseline = baseline
        .ok_or_else(|| CliError::Usage("missing required --baseline <path>".to_string()))?;
    let exceptions = exceptions
        .ok_or_else(|| CliError::Usage("missing required --exceptions <path>".to_string()))?;
    let upstream_fixes = upstream_fixes
        .ok_or_else(|| CliError::Usage("missing required --upstream-fixes <path>".to_string()))?;

    Ok(Command::Validate(ValidateOptions {
        baseline,
        exceptions,
        upstream_fixes,
        summary,
        current_upstream_revision,
    }))
}

fn parse_run_args(mut args: impl Iterator<Item = OsString>) -> Result<Command, CliError> {
    let mut baseline = None;
    let mut exceptions = None;
    let mut upstream_fixes = None;
    let mut test_exceptions = None;
    let mut trust_tests = None;
    let mut out_dir = None;
    let mut current_upstream_revision = None;
    let mut release = false;

    while let Some(arg) = args.next() {
        if arg == OsStr::new("--help") || arg == OsStr::new("-h") {
            return Ok(Command::Help);
        }

        if arg == OsStr::new("--baseline") {
            set_path("--baseline", &mut baseline, args.next())?;
        } else if arg == OsStr::new("--exceptions") {
            set_path("--exceptions", &mut exceptions, args.next())?;
        } else if arg == OsStr::new("--upstream-fixes") {
            set_path("--upstream-fixes", &mut upstream_fixes, args.next())?;
        } else if arg == OsStr::new("--test-exceptions") {
            set_path("--test-exceptions", &mut test_exceptions, args.next())?;
        } else if arg == OsStr::new("--trust-tests") {
            set_path("--trust-tests", &mut trust_tests, args.next())?;
        } else if arg == OsStr::new("--out-dir") {
            set_path("--out-dir", &mut out_dir, args.next())?;
        } else if arg == OsStr::new("--current-upstream-revision") {
            set_string("--current-upstream-revision", &mut current_upstream_revision, args.next())?;
        } else if arg == OsStr::new("--release") {
            if release {
                return Err(CliError::Usage("duplicate --release".to_string()));
            }
            release = true;
        } else {
            return Err(CliError::Usage(format!(
                "unexpected argument '{}'",
                arg.to_string_lossy()
            )));
        }
    }

    let baseline = baseline
        .ok_or_else(|| CliError::Usage("missing required --baseline <path>".to_string()))?;
    let exceptions = exceptions
        .ok_or_else(|| CliError::Usage("missing required --exceptions <path>".to_string()))?;
    let upstream_fixes = upstream_fixes
        .ok_or_else(|| CliError::Usage("missing required --upstream-fixes <path>".to_string()))?;
    let test_exceptions = test_exceptions
        .ok_or_else(|| CliError::Usage("missing required --test-exceptions <path>".to_string()))?;
    let trust_tests = trust_tests
        .ok_or_else(|| CliError::Usage("missing required --trust-tests <path>".to_string()))?;
    let out_dir =
        out_dir.ok_or_else(|| CliError::Usage("missing required --out-dir <path>".to_string()))?;
    let current_upstream_revision = current_upstream_revision.ok_or_else(|| {
        CliError::Usage("missing required --current-upstream-revision <rev>".to_string())
    })?;

    Ok(Command::Run(RunOptions {
        baseline,
        exceptions,
        upstream_fixes,
        test_exceptions,
        trust_tests,
        out_dir,
        current_upstream_revision,
        release,
    }))
}

fn parse_prove_args(mut args: impl Iterator<Item = OsString>) -> Result<Command, CliError> {
    let mut baseline = None;
    let mut exceptions = None;
    let mut upstream_fixes = None;
    let mut summary = None;
    let mut current_upstream_revision = None;
    let mut inventory = None;
    let mut results = None;
    let mut test_exceptions = None;
    let mut trust_tests = None;
    let mut proof_summary_out = None;
    let mut release = false;

    while let Some(arg) = args.next() {
        if arg == OsStr::new("--help") || arg == OsStr::new("-h") {
            return Ok(Command::Help);
        }

        if arg == OsStr::new("--baseline") {
            set_path("--baseline", &mut baseline, args.next())?;
        } else if arg == OsStr::new("--exceptions") {
            set_path("--exceptions", &mut exceptions, args.next())?;
        } else if arg == OsStr::new("--upstream-fixes") {
            set_path("--upstream-fixes", &mut upstream_fixes, args.next())?;
        } else if arg == OsStr::new("--summary") {
            set_path("--summary", &mut summary, args.next())?;
        } else if arg == OsStr::new("--current-upstream-revision") {
            set_string("--current-upstream-revision", &mut current_upstream_revision, args.next())?;
        } else if arg == OsStr::new("--inventory") {
            set_path("--inventory", &mut inventory, args.next())?;
        } else if arg == OsStr::new("--results") {
            set_path("--results", &mut results, args.next())?;
        } else if arg == OsStr::new("--test-exceptions") {
            set_path("--test-exceptions", &mut test_exceptions, args.next())?;
        } else if arg == OsStr::new("--trust-tests") {
            set_path("--trust-tests", &mut trust_tests, args.next())?;
        } else if arg == OsStr::new("--proof-summary-out") {
            set_path("--proof-summary-out", &mut proof_summary_out, args.next())?;
        } else if arg == OsStr::new("--release") {
            if release {
                return Err(CliError::Usage("duplicate --release".to_string()));
            }
            release = true;
        } else {
            return Err(CliError::Usage(format!(
                "unexpected argument '{}'",
                arg.to_string_lossy()
            )));
        }
    }

    let baseline = baseline
        .ok_or_else(|| CliError::Usage("missing required --baseline <path>".to_string()))?;
    let exceptions = exceptions
        .ok_or_else(|| CliError::Usage("missing required --exceptions <path>".to_string()))?;
    let upstream_fixes = upstream_fixes
        .ok_or_else(|| CliError::Usage("missing required --upstream-fixes <path>".to_string()))?;
    let inventory = inventory
        .ok_or_else(|| CliError::Usage("missing required --inventory <path>".to_string()))?;
    let results =
        results.ok_or_else(|| CliError::Usage("missing required --results <path>".to_string()))?;
    let test_exceptions = test_exceptions
        .ok_or_else(|| CliError::Usage("missing required --test-exceptions <path>".to_string()))?;
    let trust_tests = trust_tests
        .ok_or_else(|| CliError::Usage("missing required --trust-tests <path>".to_string()))?;

    Ok(Command::Prove(ProveOptions {
        baseline,
        exceptions,
        upstream_fixes,
        summary,
        current_upstream_revision,
        inventory,
        results,
        test_exceptions,
        trust_tests,
        release,
        proof_summary_out,
    }))
}

fn parse_port_args(mut args: impl Iterator<Item = OsString>) -> Result<Command, CliError> {
    let mut baseline = None;
    let mut upstream_fixes = None;
    let mut test_exceptions = None;
    let mut patch_manifest = None;
    let mut llm_directives = None;
    let mut summary_out = None;
    let mut run_id = None;
    let mut target_arch = None;
    let mut target = None;
    let mut target_triple = None;
    let mut host = None;
    let mut host_triple = None;
    let mut upstream_revision = None;
    let mut upstream_remote = None;
    let mut out_dir = None;
    let mut scorecard_log = None;
    let mut bootstrap_args = None;
    let mut max_files = None;
    let mut proof_mode = None;
    let mut execute = None;
    let mut apply = None;
    let mut fetch = true;
    let mut no_fetch_seen = false;
    let mut release = false;

    while let Some(arg) = args.next() {
        if arg == OsStr::new("--help") || arg == OsStr::new("-h") {
            return Ok(Command::Help);
        }

        if let Some((flag, value)) = split_port_value_arg(&arg) {
            match flag {
                "--baseline" => set_path(flag, &mut baseline, Some(value))?,
                "--upstream-fixes" => set_path(flag, &mut upstream_fixes, Some(value))?,
                "--test-exceptions" => set_path(flag, &mut test_exceptions, Some(value))?,
                "--patch-manifest" => set_path(flag, &mut patch_manifest, Some(value))?,
                "--llm-directives" => set_path(flag, &mut llm_directives, Some(value))?,
                "--summary-out" => set_path(flag, &mut summary_out, Some(value))?,
                "--run-id" => set_string(flag, &mut run_id, Some(value))?,
                "--target-arch" => set_string(flag, &mut target_arch, Some(value))?,
                "--target" => set_string(flag, &mut target, Some(value))?,
                "--target-triple" => set_string(flag, &mut target_triple, Some(value))?,
                "--host" => set_string(flag, &mut host, Some(value))?,
                "--host-triple" => set_string(flag, &mut host_triple, Some(value))?,
                "--upstream-revision" => set_string(flag, &mut upstream_revision, Some(value))?,
                "--upstream-remote" => set_string(flag, &mut upstream_remote, Some(value))?,
                "--out-dir" => set_path(flag, &mut out_dir, Some(value))?,
                "--scorecard-log" => set_path(flag, &mut scorecard_log, Some(value))?,
                "--bootstrap-args" => set_string(flag, &mut bootstrap_args, Some(value))?,
                "--max-files" => set_usize(flag, &mut max_files, Some(value))?,
                "--proof-mode" => set_proof_mode(flag, &mut proof_mode, Some(value))?,
                _ => unreachable!("split_port_value_arg returned an unsupported flag"),
            }
        } else if arg == OsStr::new("--baseline") {
            set_path("--baseline", &mut baseline, args.next())?;
        } else if arg == OsStr::new("--upstream-fixes") {
            set_path("--upstream-fixes", &mut upstream_fixes, args.next())?;
        } else if arg == OsStr::new("--test-exceptions") {
            set_path("--test-exceptions", &mut test_exceptions, args.next())?;
        } else if arg == OsStr::new("--patch-manifest") {
            set_path("--patch-manifest", &mut patch_manifest, args.next())?;
        } else if arg == OsStr::new("--llm-directives") {
            set_path("--llm-directives", &mut llm_directives, args.next())?;
        } else if arg == OsStr::new("--summary-out") {
            set_path("--summary-out", &mut summary_out, args.next())?;
        } else if arg == OsStr::new("--run-id") {
            set_string("--run-id", &mut run_id, args.next())?;
        } else if arg == OsStr::new("--target-arch") {
            set_string("--target-arch", &mut target_arch, args.next())?;
        } else if arg == OsStr::new("--target") {
            set_string("--target", &mut target, args.next())?;
        } else if arg == OsStr::new("--target-triple") {
            set_string("--target-triple", &mut target_triple, args.next())?;
        } else if arg == OsStr::new("--host") {
            set_string("--host", &mut host, args.next())?;
        } else if arg == OsStr::new("--host-triple") {
            set_string("--host-triple", &mut host_triple, args.next())?;
        } else if arg == OsStr::new("--upstream-revision") {
            set_string("--upstream-revision", &mut upstream_revision, args.next())?;
        } else if arg == OsStr::new("--upstream-remote") {
            set_string("--upstream-remote", &mut upstream_remote, args.next())?;
        } else if arg == OsStr::new("--out-dir") {
            set_path("--out-dir", &mut out_dir, args.next())?;
        } else if arg == OsStr::new("--execute") {
            set_bool_option_flag("--execute", &mut execute, true)?;
        } else if arg == OsStr::new("--no-execute") {
            set_bool_option_flag("--no-execute", &mut execute, false)?;
        } else if arg == OsStr::new("--apply") {
            set_bool_option_flag("--apply", &mut apply, true)?;
        } else if arg == OsStr::new("--no-apply") {
            set_bool_option_flag("--no-apply", &mut apply, false)?;
        } else if arg == OsStr::new("--no-fetch") {
            set_flag("--no-fetch", &mut no_fetch_seen)?;
            fetch = false;
        } else if arg == OsStr::new("--scorecard-log") {
            set_path("--scorecard-log", &mut scorecard_log, args.next())?;
        } else if arg == OsStr::new("--bootstrap-args") {
            set_string("--bootstrap-args", &mut bootstrap_args, args.next())?;
        } else if arg == OsStr::new("--max-files") {
            set_usize("--max-files", &mut max_files, args.next())?;
        } else if arg == OsStr::new("--release") {
            set_flag("--release", &mut release)?;
        } else if arg == OsStr::new("--proof-mode") {
            set_proof_mode("--proof-mode", &mut proof_mode, args.next())?;
        } else {
            return Err(CliError::Usage(format!(
                "unexpected argument '{}'",
                arg.to_string_lossy()
            )));
        }
    }

    let upstream_revision_was_explicit = upstream_revision.is_some();
    let upstream_revision =
        upstream_revision.unwrap_or_else(|| DEFAULT_PORT_UPSTREAM_REVISION.to_string());
    let fetch = if no_fetch_seen { false } else { upstream_revision_was_explicit && fetch };

    let options = PortOptions {
        baseline: baseline.unwrap_or_else(|| PathBuf::from(DEFAULT_PORT_BASELINE)),
        upstream_fixes: upstream_fixes
            .unwrap_or_else(|| PathBuf::from(DEFAULT_PORT_UPSTREAM_FIXES)),
        test_exceptions: Some(
            test_exceptions.unwrap_or_else(|| PathBuf::from(DEFAULT_PORT_TEST_EXCEPTIONS)),
        ),
        patch_manifest: Some(
            patch_manifest.unwrap_or_else(|| PathBuf::from(DEFAULT_PORT_PATCH_MANIFEST)),
        ),
        llm_directives,
        summary_out,
        run_id,
        target_arch,
        target,
        target_triple,
        host,
        host_triple,
        upstream_revision,
        upstream_remote: upstream_remote
            .unwrap_or_else(|| DEFAULT_PORT_UPSTREAM_REMOTE.to_string()),
        out_dir: out_dir.unwrap_or_else(|| PathBuf::from(DEFAULT_PORT_OUT_DIR)),
        execute: execute.unwrap_or(scorecard_log.is_none()),
        apply: apply.unwrap_or(scorecard_log.is_none() && max_files.is_none()),
        fetch,
        scorecard_log,
        bootstrap_args: bootstrap_args
            .or_else(|| env::var(PORT_BOOTSTRAP_ARGS_ENV).ok())
            .unwrap_or_default(),
        max_files,
        release,
        proof_mode: proof_mode.unwrap_or(ProofMode::Auto),
    };
    validate_port_options(&options)?;

    Ok(Command::Port(options))
}

fn split_port_value_arg(arg: &OsStr) -> Option<(&'static str, OsString)> {
    let arg = arg.to_str()?;
    let (flag, value) = arg.split_once('=')?;
    let flag = match flag {
        "--baseline" => "--baseline",
        "--upstream-fixes" => "--upstream-fixes",
        "--test-exceptions" => "--test-exceptions",
        "--patch-manifest" => "--patch-manifest",
        "--llm-directives" => "--llm-directives",
        "--summary-out" => "--summary-out",
        "--run-id" => "--run-id",
        "--target-arch" => "--target-arch",
        "--target" => "--target",
        "--target-triple" => "--target-triple",
        "--host" => "--host",
        "--host-triple" => "--host-triple",
        "--upstream-revision" => "--upstream-revision",
        "--upstream-remote" => "--upstream-remote",
        "--out-dir" => "--out-dir",
        "--scorecard-log" => "--scorecard-log",
        "--bootstrap-args" => "--bootstrap-args",
        "--max-files" => "--max-files",
        "--proof-mode" => "--proof-mode",
        _ => return None,
    };

    Some((flag, OsString::from(value)))
}

fn set_path(
    flag: &'static str,
    target: &mut Option<PathBuf>,
    value: Option<OsString>,
) -> Result<(), CliError> {
    if target.is_some() {
        return Err(CliError::Usage(format!("duplicate {flag}")));
    }

    let value = value.ok_or_else(|| CliError::Usage(format!("missing value for {flag}")))?;
    *target = Some(PathBuf::from(value));
    Ok(())
}

fn set_string(
    flag: &'static str,
    target: &mut Option<String>,
    value: Option<OsString>,
) -> Result<(), CliError> {
    if target.is_some() {
        return Err(CliError::Usage(format!("duplicate {flag}")));
    }

    let value = value.ok_or_else(|| CliError::Usage(format!("missing value for {flag}")))?;
    *target = Some(value.to_string_lossy().into_owned());
    Ok(())
}

fn set_usize(
    flag: &'static str,
    target: &mut Option<usize>,
    value: Option<OsString>,
) -> Result<(), CliError> {
    if target.is_some() {
        return Err(CliError::Usage(format!("duplicate {flag}")));
    }

    let value = value.ok_or_else(|| CliError::Usage(format!("missing value for {flag}")))?;
    let display_value = value.to_string_lossy();
    let parsed = display_value.parse::<usize>().map_err(|_| {
        CliError::Usage(format!("invalid value for {flag}: '{display_value}' is not a count"))
    })?;
    *target = Some(parsed);
    Ok(())
}

fn set_flag(flag: &'static str, target: &mut bool) -> Result<(), CliError> {
    if *target {
        return Err(CliError::Usage(format!("duplicate {flag}")));
    }

    *target = true;
    Ok(())
}

fn set_bool_option_flag(
    flag: &'static str,
    target: &mut Option<bool>,
    value: bool,
) -> Result<(), CliError> {
    if target.is_some() {
        return Err(CliError::Usage(format!("duplicate workflow mode flag near {flag}")));
    }

    *target = Some(value);
    Ok(())
}

fn set_proof_mode(
    flag: &'static str,
    target: &mut Option<ProofMode>,
    value: Option<OsString>,
) -> Result<(), CliError> {
    if target.is_some() {
        return Err(CliError::Usage(format!("duplicate {flag}")));
    }

    let value = value.ok_or_else(|| CliError::Usage(format!("missing value for {flag}")))?;
    let display_value = value.to_string_lossy();
    let proof_mode = ProofMode::parse(&display_value).ok_or_else(|| {
        CliError::Usage(format!(
            "invalid value for {flag}: '{display_value}' (expected auto, smoke, or full)"
        ))
    })?;
    *target = Some(proof_mode);
    Ok(())
}

fn validate_port_options(options: &PortOptions) -> Result<(), CliError> {
    if options.execute && options.scorecard_log.is_some() {
        return Err(CliError::Usage(
            "--scorecard-log is log-parse mode; pass it without --execute so scorecard evidence cannot be mistaken for a fresh suite run".to_string(),
        ));
    }

    if options.max_files.is_some() && options.apply {
        return Err(CliError::Usage(
            "--max-files is a bounded smoke import and cannot be combined with --apply; rerun without --max-files for an applying import".to_string(),
        ));
    }

    if options.max_files.is_some() && options.proof_mode == ProofMode::Full {
        return Err(CliError::Usage(
            "--max-files is a bounded smoke import and cannot be combined with --proof-mode full; rerun without --max-files for full proof".to_string(),
        ));
    }

    Ok(())
}

#[cfg(test)]
fn resolved_proof_mode(requested: ProofMode, max_files: Option<usize>) -> ProofMode {
    requested.resolved(max_files)
}

fn execute_port(options: PortOptions) -> Result<CommandOutcome, CliError> {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let test_exception_validation_date = test_exception_validation_date();
    let test_exceptions = options
        .test_exceptions
        .as_deref()
        .map(|path| {
            parse_test_exceptions_file_for_date(
                &repo_relative_path(&repo_root, path),
                &test_exception_validation_date,
            )
        })
        .transpose()?;
    let report = porting::run_porting(porting::PortOptions {
        repo_root: repo_root.clone(),
        baseline: options.baseline,
        upstream_fixes: options.upstream_fixes,
        test_exceptions,
        patch_manifest: options.patch_manifest,
        llm_directives: options.llm_directives,
        summary_out: options.summary_out,
        run_id: options.run_id,
        target_arch: options.target_arch,
        target: options.target,
        target_triple: options.target_triple,
        host: options.host,
        host_triple: options.host_triple,
        test_exception_validation_date: Some(test_exception_validation_date),
        upstream_revision: options.upstream_revision,
        upstream_remote: options.upstream_remote,
        out_dir: options.out_dir,
        execute: options.execute,
        apply: options.apply,
        fetch: options.fetch,
        scorecard_log: options.scorecard_log,
        bootstrap_args: options.bootstrap_args,
        max_files: options.max_files,
        release: options.release,
        proof_mode: options.proof_mode,
    })
    .map_err(CliError::Porting)?;
    print!("{}", report.render_terminal(&repo_root));
    if report.exit_code == 0 {
        Ok(CommandOutcome::Success)
    } else {
        Err(CliError::PortingFailure(report.exit_code))
    }
}

fn repo_relative_path(root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() { path.to_path_buf() } else { root.join(path) }
}

fn execute_run(options: RunOptions) -> Result<CommandOutcome, CliError> {
    let baseline = parse_baseline_file(&options.baseline)?;
    let exceptions = parse_exceptions_file(&options.exceptions)?;
    let upstream_fixes = parse_upstream_fixes_file(&options.upstream_fixes)?;
    let test_exception_validation_date = test_exception_validation_date();
    let test_exceptions = parse_test_exceptions_file_for_date(
        &options.test_exceptions,
        &test_exception_validation_date,
    )?;
    let trust_tests = parse_trust_added_tests_file(&options.trust_tests)?;

    validate_accounting_bundle(AccountingBundle {
        baseline: &baseline,
        exceptions: Some(&exceptions),
        upstream_fixes: Some(&upstream_fixes),
        result_summary: None,
        current_upstream_revision: Some(&options.current_upstream_revision),
    })
    .map_err(CliError::BundleValidation)?;

    fs::create_dir_all(&options.out_dir).map_err(CliError::Output)?;
    let upstream_log = options.out_dir.join("upstream-rust-compat.log");
    let trust_log = options.out_dir.join("trust-added.log");

    let upstream_command = upstream_suite_command(options.release);
    run_shell_command(
        &upstream_command,
        &[
            ("TRUST_RUN_FULL_UPSTREAM_RUST_TESTS", "1"),
            ("TRUST_UPSTREAM_RUST_CURRENT_REVISION", &options.current_upstream_revision),
            ("TRUST_UPSTREAM_RUST_PORT_REVISION", &options.current_upstream_revision),
            ("TRUST_STRICT", "1"),
            ("TRUST_RELEASE_GATE", if options.release { "1" } else { "0" }),
        ],
        &upstream_log,
    )?;

    let mut inventory_tests = upstream_inventory_from_git(&baseline)?;
    let mut results = inventory_tests
        .iter()
        .map(|test| TestResult {
            test_id: test.id.clone(),
            outcome: TestOutcome::Passed,
            exception_id: None,
            observed: Some("full upstream Rust compatibility command passed".to_string()),
            artifact: Some(path_display(&upstream_log)),
        })
        .collect::<Vec<_>>();

    fs::write(&trust_log, "").map_err(CliError::Output)?;
    for command in &trust_tests.commands {
        for test_id in &command.covers {
            inventory_tests.push(TestInventoryEntry {
                id: test_id.clone(),
                suite: command.id.clone(),
                path: command.command.clone(),
                revision: None,
                source_git_blob: None,
                source: TestSource::TrustAdded,
                kind: TestKind::Shell,
                applicable: true,
                inapplicable_reason: None,
                source_sha256: None,
            });
        }

        let status = run_shell_command_logged(&command.command, &[], &trust_log, LogMode::Append)?;
        let outcome = if status.success() { TestOutcome::Passed } else { TestOutcome::Failed };
        for test_id in &command.covers {
            results.push(TestResult {
                test_id: test_id.clone(),
                outcome,
                exception_id: None,
                observed: Some(format!("Trust-added command exited with {status}")),
                artifact: Some(path_display(&trust_log)),
            });
        }

        if !status.success() {
            return Err(CliError::BundleValidation(vec![ValidationFinding {
                field: "trust_added_tests.commands.command".to_string(),
                message: format!(
                    "Trust-added command '{}' failed with {}; see {}",
                    command.id,
                    status,
                    trust_log.display()
                ),
            }]));
        }
    }

    let inventory = TestInventory {
        schema_version: trust_upstream_compat::SCHEMA_VERSION.to_string(),
        upstream_revision: baseline.upstream.revision.clone(),
        local_revision: baseline.local.revision.clone(),
        host: current_host(),
        tests: inventory_tests,
    };
    let result_report = TestResultReport {
        schema_version: trust_upstream_compat::SCHEMA_VERSION.to_string(),
        inventory_id: "generated-by-trust-upstream-compat-run".to_string(),
        generated_on: current_date_string(),
        command: format!("{} && <Trust-added manifest commands>", upstream_command),
        results,
    };

    let inventory_path = options.out_dir.join("inventory.json");
    let results_path = options.out_dir.join("results.json");
    write_json(&inventory_path, &inventory)?;
    write_json(&results_path, &result_report)?;

    let totals = validate_test_proof_bundle(TestProofBundle {
        inventory: &inventory,
        results: &result_report,
        exceptions: &test_exceptions,
        trust_added_tests: Some(&trust_tests),
        validation_date: &test_exception_validation_date,
        release: options.release,
    })
    .map_err(CliError::BundleValidation)?;
    write_proof_summary(&options.out_dir.join("proof-summary.json"), totals)?;

    Ok(CommandOutcome::Success)
}

fn parse_baseline_file(path: &Path) -> Result<CompatibilityBaseline, CliError> {
    let input = read_document("baseline", path)?;
    match document_format(path) {
        DocumentFormat::Json => parse_baseline_json(&input),
        DocumentFormat::Toml => parse_baseline_toml(&input),
    }
    .map_err(|source| CliError::Parse { kind: "baseline", path: path.to_path_buf(), source })
}

fn parse_exceptions_file(path: &Path) -> Result<ExceptionLedger, CliError> {
    let input = read_document("exceptions", path)?;
    match document_format(path) {
        DocumentFormat::Json => parse_exceptions_json(&input),
        DocumentFormat::Toml => parse_exceptions_toml(&input),
    }
    .map_err(|source| CliError::Parse { kind: "exceptions", path: path.to_path_buf(), source })
}

fn parse_upstream_fixes_file(path: &Path) -> Result<UpstreamFixLedger, CliError> {
    let input = read_document("upstream fixes", path)?;
    match document_format(path) {
        DocumentFormat::Json => parse_upstream_fixes_json(&input),
        DocumentFormat::Toml => parse_upstream_fixes_toml(&input),
    }
    .map_err(|source| CliError::Parse {
        kind: "upstream fixes",
        path: path.to_path_buf(),
        source,
    })
}

fn parse_result_summary_file(path: &Path) -> Result<CompatibilityResultSummary, CliError> {
    let input = read_document("summary", path)?;
    match document_format(path) {
        DocumentFormat::Json => parse_result_summary_json(&input),
        DocumentFormat::Toml => parse_result_summary_toml(&input),
    }
    .map_err(|source| CliError::Parse { kind: "summary", path: path.to_path_buf(), source })
}

fn parse_test_inventory_file(path: &Path) -> Result<TestInventory, CliError> {
    let input = read_document("test inventory", path)?;
    match document_format(path) {
        DocumentFormat::Json => parse_test_inventory_json(&input),
        DocumentFormat::Toml => parse_test_inventory_toml(&input),
    }
    .map_err(|source| CliError::Parse {
        kind: "test inventory",
        path: path.to_path_buf(),
        source,
    })
}

fn parse_test_result_report_file(path: &Path) -> Result<TestResultReport, CliError> {
    let input = read_document("test results", path)?;
    match document_format(path) {
        DocumentFormat::Json => parse_test_result_report_json(&input),
        DocumentFormat::Toml => parse_test_result_report_toml(&input),
    }
    .map_err(|source| CliError::Parse {
        kind: "test results",
        path: path.to_path_buf(),
        source,
    })
}

fn parse_test_exceptions_file_for_date(
    path: &Path,
    validation_date: &str,
) -> Result<TestExceptionLedger, CliError> {
    let input = read_document("test exceptions", path)?;
    match document_format(path) {
        DocumentFormat::Json => parse_test_exceptions_json_for_date(&input, validation_date),
        DocumentFormat::Toml => parse_test_exceptions_toml_for_date(&input, validation_date),
    }
    .map_err(|source| CliError::Parse {
        kind: "test exceptions",
        path: path.to_path_buf(),
        source,
    })
}

fn test_exception_validation_date() -> String {
    env::var(TEST_EXCEPTION_VALIDATION_DATE_ENV)
        .ok()
        .filter(|date| !date.trim().is_empty())
        .unwrap_or_else(current_date_string)
}

fn parse_trust_added_tests_file(path: &Path) -> Result<TrustAddedTestManifest, CliError> {
    let input = read_document("Trust-added tests", path)?;
    match document_format(path) {
        DocumentFormat::Json => parse_trust_added_tests_json(&input),
        DocumentFormat::Toml => parse_trust_added_tests_toml(&input),
    }
    .map_err(|source| CliError::Parse {
        kind: "Trust-added tests",
        path: path.to_path_buf(),
        source,
    })
}

fn write_proof_summary(path: &Path, totals: TestProofTotals) -> Result<(), CliError> {
    if let Some(parent) = path.parent().filter(|parent| !parent.as_os_str().is_empty()) {
        fs::create_dir_all(parent).map_err(CliError::Output)?;
    }
    let mut output = serde_json::to_string_pretty(&totals).map_err(|err| {
        CliError::Output(io::Error::other(format!("failed to serialize proof summary: {err}")))
    })?;
    output.push('\n');
    fs::write(path, output).map_err(CliError::Output)
}

fn write_json<T: Serialize>(path: &Path, value: &T) -> Result<(), CliError> {
    if let Some(parent) = path.parent().filter(|parent| !parent.as_os_str().is_empty()) {
        fs::create_dir_all(parent).map_err(CliError::Output)?;
    }
    let mut output = serde_json::to_string_pretty(value).map_err(|err| {
        CliError::Output(io::Error::other(format!("failed to serialize JSON: {err}")))
    })?;
    output.push('\n');
    fs::write(path, output).map_err(CliError::Output)
}

fn upstream_suite_command(release: bool) -> String {
    if release {
        "targo trust domination upstream-tests --release".to_string()
    } else {
        "targo trust domination upstream-tests".to_string()
    }
}

fn run_shell_command(
    command: &str,
    envs: &[(&str, &str)],
    log_path: &Path,
) -> Result<(), CliError> {
    let status = run_shell_command_logged(command, envs, log_path, LogMode::Truncate)?;

    if status.success() {
        Ok(())
    } else {
        Err(CliError::BundleValidation(vec![ValidationFinding {
            field: "upstream_command".to_string(),
            message: format!(
                "full upstream Rust compatibility command failed with {}; see {}",
                status,
                log_path.display()
            ),
        }]))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LogMode {
    Truncate,
    Append,
}

fn run_shell_command_logged(
    command: &str,
    envs: &[(&str, &str)],
    log_path: &Path,
    mode: LogMode,
) -> Result<ExitStatus, CliError> {
    if let Some(parent) = log_path.parent().filter(|parent| !parent.as_os_str().is_empty()) {
        fs::create_dir_all(parent).map_err(CliError::Output)?;
    }

    let mut options = OpenOptions::new();
    options.create(true).write(true);
    match mode {
        LogMode::Truncate => {
            options.truncate(true);
        }
        LogMode::Append => {
            options.append(true);
        }
    }

    let mut log = options.open(log_path).map_err(CliError::Output)?;
    writeln!(log, "$ {command}").map_err(CliError::Output)?;
    log.flush().map_err(CliError::Output)?;

    let stdout = log.try_clone().map_err(CliError::Output)?;
    let stderr = log.try_clone().map_err(CliError::Output)?;
    let mut process = if cfg!(windows) {
        let mut process = ProcessCommand::new("cmd");
        process.arg("/C").arg(command);
        process
    } else {
        let mut process = ProcessCommand::new("sh");
        process.arg("-c").arg(command);
        process
    };
    for (key, value) in envs {
        process.env(key, value);
    }

    process
        .stdout(Stdio::from(stdout))
        .stderr(Stdio::from(stderr))
        .status()
        .map_err(CliError::Output)
}

fn upstream_inventory_from_git(
    baseline: &CompatibilityBaseline,
) -> Result<Vec<TestInventoryEntry>, CliError> {
    let revision = revision_suffix(&baseline.upstream.revision);
    let output = ProcessCommand::new("git")
        .args([
            "ls-tree",
            "-r",
            "-l",
            revision,
            "--",
            "tests",
            "src/tools/targo/tests",
            "src/tools/trustfmt/tests",
            "src/tools/tippy/tests",
            "src/tools/miri/tests",
            "src/tools/rust-analyzer/crates",
            "library",
        ])
        .output()
        .map_err(CliError::Output)?;

    if !output.status.success() {
        return Err(CliError::BundleValidation(vec![ValidationFinding {
            field: "inventory.upstream_revision".to_string(),
            message: format!(
                "could not list upstream test inventory for revision '{}': {}",
                baseline.upstream.revision,
                String::from_utf8_lossy(&output.stderr)
            ),
        }]));
    }

    let mut tests = String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(parse_git_tree_entry)
        .filter(|entry| is_probable_test_input(&entry.path))
        .enumerate()
        .map(|(idx, entry)| {
            let path = entry.path;
            TestInventoryEntry {
                id: format!("upstream.{idx:08}.{}", sanitize_id(&path)),
                suite: suite_for_path(&path).to_string(),
                kind: kind_for_path(&path),
                path,
                revision: Some(baseline.upstream.revision.clone()),
                source_git_blob: Some(entry.object_id),
                source: TestSource::UpstreamRust,
                applicable: true,
                inapplicable_reason: None,
                source_sha256: None,
            }
        })
        .collect::<Vec<_>>();

    if tests.is_empty() {
        tests = baseline
            .entries
            .iter()
            .map(|entry| TestInventoryEntry {
                id: format!("upstream.{}", entry.id),
                suite: entry.title.clone(),
                path: entry.upstream_artifact.clone(),
                revision: None,
                source_git_blob: None,
                source: TestSource::UpstreamRust,
                kind: TestKind::Other,
                applicable: true,
                inapplicable_reason: None,
                source_sha256: None,
            })
            .collect();
    }

    Ok(tests)
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct GitTreeEntry {
    object_id: String,
    path: String,
}

fn parse_git_tree_entry(line: &str) -> Option<GitTreeEntry> {
    let (metadata, path) = line.split_once('\t')?;
    let mut parts = metadata.split_whitespace();
    let _mode = parts.next()?;
    let object_type = parts.next()?;
    let object_id = parts.next()?;
    if object_type != "blob" {
        return None;
    }

    Some(GitTreeEntry { object_id: object_id.to_string(), path: path.to_string() })
}

fn is_probable_test_input(path: &str) -> bool {
    let name = Path::new(path).file_name().and_then(OsStr::to_str).unwrap_or("");
    if matches!(name, "Makefile" | "rmake.rs" | "Cargo.toml" | "Cargo.lock") {
        return true;
    }
    matches!(
        Path::new(path).extension().and_then(OsStr::to_str),
        Some(
            "rs" | "stderr"
                | "stdout"
                | "fixed"
                | "mir"
                | "ll"
                | "asm"
                | "s"
                | "c"
                | "cc"
                | "cpp"
                | "h"
                | "hpp"
                | "json"
                | "js"
                | "css"
                | "html"
                | "md"
                | "txt"
                | "py"
                | "sh"
                | "toml"
        )
    )
}

fn suite_for_path(path: &str) -> &str {
    let mut parts = path.split('/');
    match (parts.next(), parts.next()) {
        (Some("tests"), Some(suite)) => suite,
        (Some("src"), Some("tools")) => "tool",
        (Some("library"), _) => "library",
        _ => "other",
    }
}

fn kind_for_path(path: &str) -> TestKind {
    if path.starts_with("tests/") {
        TestKind::Compiletest
    } else if path.starts_with("library/") {
        TestKind::Rustbuild
    } else if path.contains("/cargo/tests/") {
        TestKind::Cargo
    } else if path.starts_with("src/tools/") {
        TestKind::Tool
    } else {
        TestKind::Other
    }
}

fn sanitize_id(path: &str) -> String {
    path.bytes()
        .map(|byte| match byte {
            b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' => char::from(byte),
            _ => '.',
        })
        .collect()
}

fn revision_suffix(value: &str) -> &str {
    value.rsplit_once(':').map_or(value, |(_, suffix)| suffix).trim()
}

fn current_date_string() -> String {
    ProcessCommand::new("date")
        .arg("+%F")
        .output()
        .ok()
        .and_then(|output| {
            output
                .status
                .success()
                .then(|| String::from_utf8_lossy(&output.stdout).trim().to_string())
        })
        .filter(|date| !date.is_empty())
        .unwrap_or_else(|| "1970-01-01".to_string())
}

fn current_host() -> Option<String> {
    let output = ProcessCommand::new("rustc").arg("-vV").output().ok()?;
    if !output.status.success() {
        return None;
    }
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .find_map(|line| line.strip_prefix("host: ").map(str::to_string))
}

fn path_display(path: &Path) -> String {
    path.to_string_lossy().into_owned()
}

fn read_document(kind: &'static str, path: &Path) -> Result<String, CliError> {
    fs::read_to_string(path).map_err(|source| CliError::Read {
        kind,
        path: path.to_path_buf(),
        source,
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DocumentFormat {
    Toml,
    Json,
}

fn document_format(path: &Path) -> DocumentFormat {
    match path.extension().and_then(OsStr::to_str) {
        Some(extension) if extension.eq_ignore_ascii_case("json") => DocumentFormat::Json,
        _ => DocumentFormat::Toml,
    }
}

fn write_all(stdout: &mut dyn Write, bytes: &[u8], stderr: &mut dyn Write) -> Result<(), u8> {
    stdout.write_all(bytes).map_err(|err| {
        print_error(stderr, &CliError::Output(err));
        1
    })
}

fn print_error(stderr: &mut dyn Write, err: &CliError) {
    let _ = match err {
        CliError::Usage(message) => {
            writeln!(stderr, "error: {message}\nTry 'trust-upstream-compat --help' for usage.")
        }
        CliError::Read { kind, path, source } => {
            writeln!(stderr, "error: failed to read {kind} '{}': {source}", path.display())
        }
        CliError::Parse { kind, path, source } => write_parse_error(stderr, kind, path, source),
        CliError::BundleValidation(findings) => {
            writeln!(stderr, "error: accounting bundle failed validation")
                .and_then(|()| write_findings(stderr, findings))
        }
        CliError::Output(source) => writeln!(stderr, "error: failed to write output: {source}"),
        CliError::Porting(source) => writeln!(stderr, "error: upstream porting failed: {source}"),
        CliError::PortingFailure(code) => writeln!(
            stderr,
            "error: upstream porting scorecard did not meet success criteria (exit {code})"
        ),
    };
}

fn write_parse_error(
    stderr: &mut dyn Write,
    kind: &str,
    path: &Path,
    source: &ParseError,
) -> io::Result<()> {
    match source {
        ParseError::Validation { findings } => {
            writeln!(stderr, "error: {kind} '{}' failed validation", path.display())?;
            write_findings(stderr, findings)
        }
        _ => writeln!(stderr, "error: failed to parse {kind} '{}': {source}", path.display()),
    }
}

fn write_findings(stderr: &mut dyn Write, findings: &[ValidationFinding]) -> io::Result<()> {
    for finding in findings {
        writeln!(stderr, "  {}: {}", finding.field, finding.message)?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::*;

    #[test]
    fn help_prints_usage() {
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let result =
            run(["trust-upstream-compat", "--help"].map(OsString::from), &mut stdout, &mut stderr);

        assert_eq!(result, Ok(()));
        assert!(String::from_utf8(stdout).expect("stdout should be utf-8").contains("Usage:"));
        assert!(stderr.is_empty());
    }

    #[test]
    fn parse_validate_args_requires_all_input_paths() {
        let err = parse_args(["validate", "--baseline", "baseline.toml"].map(OsString::from))
            .expect_err("missing flags should fail");

        match err {
            CliError::Usage(message) => assert!(message.contains("--exceptions")),
            other => panic!("expected usage error, got {other:?}"),
        }
    }

    #[test]
    fn parse_port_args_uses_workflow_defaults() {
        let command = parse_args(["port"].map(OsString::from)).expect("port defaults should parse");

        match command {
            Command::Port(options) => {
                assert_eq!(options.baseline, PathBuf::from(DEFAULT_PORT_BASELINE));
                assert_eq!(options.upstream_fixes, PathBuf::from(DEFAULT_PORT_UPSTREAM_FIXES));
                assert_eq!(
                    options.test_exceptions,
                    Some(PathBuf::from(DEFAULT_PORT_TEST_EXCEPTIONS))
                );
                assert_eq!(
                    options.patch_manifest,
                    Some(PathBuf::from(DEFAULT_PORT_PATCH_MANIFEST))
                );
                assert_eq!(options.llm_directives, None);
                assert_eq!(options.summary_out, None);
                assert_eq!(options.run_id, None);
                assert_eq!(options.target_arch, None);
                assert_eq!(options.target, None);
                assert_eq!(options.target_triple, None);
                assert_eq!(options.host, None);
                assert_eq!(options.host_triple, None);
                assert_eq!(options.upstream_revision, DEFAULT_PORT_UPSTREAM_REVISION);
                assert_eq!(options.upstream_remote, DEFAULT_PORT_UPSTREAM_REMOTE);
                assert_eq!(options.out_dir, PathBuf::from(DEFAULT_PORT_OUT_DIR));
                assert!(options.execute);
                assert!(options.apply);
                assert!(!options.fetch);
                assert_eq!(options.scorecard_log, None);
                assert_eq!(
                    options.bootstrap_args,
                    env::var(PORT_BOOTSTRAP_ARGS_ENV).unwrap_or_default()
                );
                assert_eq!(options.max_files, None);
                assert!(!options.release);
                assert_eq!(options.proof_mode, ProofMode::Auto);
                assert_eq!(
                    resolved_proof_mode(options.proof_mode, options.max_files),
                    ProofMode::Full
                );
            }
            other => panic!("expected port command, got {other:?}"),
        }
    }

    #[test]
    fn parse_upstream_port_args_accepts_full_workflow_surface() {
        let command = parse_args(
            [
                "upstream-port",
                "--baseline",
                "baseline.toml",
                "--upstream-fixes",
                "fixes.toml",
                "--test-exceptions",
                "test-exceptions.toml",
                "--patch-manifest",
                "patches.toml",
                "--llm-directives",
                "llm.md",
                "--summary-out",
                "reports/ported/aarch64/summary.json",
                "--run-id",
                "compat-aarch64",
                "--target-arch",
                "aarch64",
                "--target",
                "aarch64-unknown-linux-gnu",
                "--target-triple",
                "aarch64-unknown-linux-gnu",
                "--host",
                "aarch64-unknown-linux-gnu",
                "--host-triple",
                "aarch64-unknown-linux-gnu",
                "--upstream-revision",
                "rust-lang/rust:feedface",
                "--upstream-remote",
                "https://example.invalid/rust.git",
                "--out-dir",
                "reports/ported",
                "--execute",
                "--no-apply",
                "--no-fetch",
                "--bootstrap-args",
                "--set llvm.ninja=false",
                "--max-files",
                "12",
                "--release",
                "--proof-mode",
                "smoke",
            ]
            .map(OsString::from),
        )
        .expect("explicit upstream-port options should parse");

        match command {
            Command::Port(options) => {
                assert_eq!(options.baseline, PathBuf::from("baseline.toml"));
                assert_eq!(options.upstream_fixes, PathBuf::from("fixes.toml"));
                assert_eq!(options.test_exceptions, Some(PathBuf::from("test-exceptions.toml")));
                assert_eq!(options.patch_manifest, Some(PathBuf::from("patches.toml")));
                assert_eq!(options.llm_directives, Some(PathBuf::from("llm.md")));
                assert_eq!(
                    options.summary_out,
                    Some(PathBuf::from("reports/ported/aarch64/summary.json"))
                );
                assert_eq!(options.run_id.as_deref(), Some("compat-aarch64"));
                assert_eq!(options.target_arch.as_deref(), Some("aarch64"));
                assert_eq!(options.target.as_deref(), Some("aarch64-unknown-linux-gnu"));
                assert_eq!(options.target_triple.as_deref(), Some("aarch64-unknown-linux-gnu"));
                assert_eq!(options.host.as_deref(), Some("aarch64-unknown-linux-gnu"));
                assert_eq!(options.host_triple.as_deref(), Some("aarch64-unknown-linux-gnu"));
                assert_eq!(options.upstream_revision, "rust-lang/rust:feedface");
                assert_eq!(options.upstream_remote, "https://example.invalid/rust.git");
                assert_eq!(options.out_dir, PathBuf::from("reports/ported"));
                assert!(options.execute);
                assert!(!options.apply);
                assert!(!options.fetch);
                assert_eq!(options.scorecard_log, None);
                assert_eq!(options.bootstrap_args, "--set llvm.ninja=false");
                assert_eq!(options.max_files, Some(12));
                assert!(options.release);
                assert_eq!(options.proof_mode, ProofMode::Smoke);
                assert_eq!(
                    resolved_proof_mode(options.proof_mode, options.max_files),
                    ProofMode::Smoke
                );
            }
            other => panic!("expected port command, got {other:?}"),
        }
    }

    #[test]
    fn parse_release_facing_upstream_tests_surface_uses_port_engine() {
        for surface in ["domination", "rust-vs-trust"] {
            let command = parse_args(
                [
                    "trust",
                    surface,
                    "upstream-tests",
                    "--no-execute",
                    "--no-apply",
                    "--no-fetch",
                    "--max-files",
                    "1",
                    "--proof-mode",
                    "smoke",
                ]
                .map(OsString::from),
            )
            .expect("release-facing upstream-tests spelling should parse through port engine");

            match command {
                Command::Port(options) => {
                    assert!(!options.execute);
                    assert!(!options.apply);
                    assert!(!options.fetch);
                    assert_eq!(options.max_files, Some(1));
                    assert_eq!(options.proof_mode, ProofMode::Smoke);
                }
                other => panic!("expected port command for {surface}, got {other:?}"),
            }
        }
    }

    #[test]
    fn parse_port_args_accepts_equals_value_forms() {
        let command = parse_args(
            [
                "port",
                "--baseline=baseline.toml",
                "--upstream-fixes=fixes.toml",
                "--test-exceptions=test-exceptions.toml",
                "--patch-manifest=patches.toml",
                "--llm-directives=llm.md",
                "--summary-out=reports/ported/x86_64/summary.json",
                "--run-id=compat-x86_64",
                "--target-arch=x86_64",
                "--target=x86_64-unknown-linux-gnu",
                "--target-triple=x86_64-unknown-linux-gnu",
                "--host=x86_64-unknown-linux-gnu",
                "--host-triple=x86_64-unknown-linux-gnu",
                "--upstream-revision=rust-lang/rust:feedface",
                "--upstream-remote=https://example.invalid/rust.git",
                "--out-dir=reports/ported",
                "--scorecard-log=previous.log",
                "--bootstrap-args=--set llvm.ninja=false",
                "--max-files=12",
                "--proof-mode=smoke",
            ]
            .map(OsString::from),
        )
        .expect("equals-form port options should parse");

        match command {
            Command::Port(options) => {
                assert_eq!(options.baseline, PathBuf::from("baseline.toml"));
                assert_eq!(options.upstream_fixes, PathBuf::from("fixes.toml"));
                assert_eq!(options.test_exceptions, Some(PathBuf::from("test-exceptions.toml")));
                assert_eq!(options.patch_manifest, Some(PathBuf::from("patches.toml")));
                assert_eq!(options.llm_directives, Some(PathBuf::from("llm.md")));
                assert_eq!(
                    options.summary_out,
                    Some(PathBuf::from("reports/ported/x86_64/summary.json"))
                );
                assert_eq!(options.run_id.as_deref(), Some("compat-x86_64"));
                assert_eq!(options.target_arch.as_deref(), Some("x86_64"));
                assert_eq!(options.target.as_deref(), Some("x86_64-unknown-linux-gnu"));
                assert_eq!(options.target_triple.as_deref(), Some("x86_64-unknown-linux-gnu"));
                assert_eq!(options.host.as_deref(), Some("x86_64-unknown-linux-gnu"));
                assert_eq!(options.host_triple.as_deref(), Some("x86_64-unknown-linux-gnu"));
                assert_eq!(options.upstream_revision, "rust-lang/rust:feedface");
                assert_eq!(options.upstream_remote, "https://example.invalid/rust.git");
                assert_eq!(options.out_dir, PathBuf::from("reports/ported"));
                assert!(!options.execute);
                assert!(!options.apply);
                assert_eq!(options.scorecard_log, Some(PathBuf::from("previous.log")));
                assert_eq!(options.bootstrap_args, "--set llvm.ninja=false");
                assert_eq!(options.max_files, Some(12));
                assert_eq!(options.proof_mode, ProofMode::Smoke);
            }
            other => panic!("expected port command, got {other:?}"),
        }
    }

    #[test]
    fn parse_port_args_max_files_defaults_to_no_apply() {
        let command = parse_args(["port", "--max-files", "1"].map(OsString::from))
            .expect("bounded smoke port options should parse");

        match command {
            Command::Port(options) => {
                assert_eq!(options.max_files, Some(1));
                assert!(!options.apply);
            }
            other => panic!("expected port command, got {other:?}"),
        }
    }

    #[test]
    fn parse_port_args_max_files_accepts_explicit_no_apply() {
        let command = parse_args(["port", "--max-files", "1", "--no-apply"].map(OsString::from))
            .expect("explicit bounded no-apply should parse");

        match command {
            Command::Port(options) => {
                assert_eq!(options.max_files, Some(1));
                assert!(!options.apply);
            }
            other => panic!("expected port command, got {other:?}"),
        }
    }

    #[test]
    fn parse_port_args_rejects_max_files_with_apply() {
        let err = parse_args(["port", "--max-files", "1", "--apply"].map(OsString::from))
            .expect_err("bounded apply should fail closed");

        match err {
            CliError::Usage(message) => {
                assert!(message.contains("--max-files"));
                assert!(message.contains("--apply"));
            }
            other => panic!("expected usage error, got {other:?}"),
        }
    }

    #[test]
    fn parse_port_args_rejects_max_files_with_full_proof_mode() {
        let err =
            parse_args(["port", "--max-files", "1", "--proof-mode", "full"].map(OsString::from))
                .expect_err("bounded full proof should fail closed");

        match err {
            CliError::Usage(message) => {
                assert!(message.contains("--max-files"));
                assert!(message.contains("--proof-mode full"));
            }
            other => panic!("expected usage error, got {other:?}"),
        }
    }

    #[test]
    fn parse_port_args_rejects_duplicate_mixed_value_forms() {
        for (flag, first, second) in [
            ("--baseline", "baseline.toml", "other-baseline.toml"),
            ("--upstream-fixes", "fixes.toml", "other-fixes.toml"),
            ("--test-exceptions", "test-exceptions.toml", "other-test-exceptions.toml"),
            ("--patch-manifest", "patches.toml", "other-patches.toml"),
            ("--llm-directives", "llm.md", "other-llm.md"),
            ("--upstream-revision", "rust-lang/rust:feedface", "rust-lang/rust:cafebabe"),
            (
                "--upstream-remote",
                "https://example.invalid/rust.git",
                "https://example.invalid/other.git",
            ),
            ("--out-dir", "reports/ported", "reports/other"),
            ("--scorecard-log", "previous.log", "other.log"),
            ("--bootstrap-args", "--set llvm.ninja=false", "--set llvm.ninja=true"),
            ("--max-files", "12", "13"),
            ("--proof-mode", "smoke", "full"),
        ] {
            let split_then_equals = parse_args([
                OsString::from("port"),
                OsString::from(flag),
                OsString::from(first),
                OsString::from(format!("{flag}={second}")),
            ])
            .expect_err("split then equals duplicate should fail");
            assert_duplicate_flag(split_then_equals, flag);

            let equals_then_split = parse_args([
                OsString::from("port"),
                OsString::from(format!("{flag}={first}")),
                OsString::from(flag),
                OsString::from(second),
            ])
            .expect_err("equals then split duplicate should fail");
            assert_duplicate_flag(equals_then_split, flag);
        }
    }

    #[test]
    fn parse_port_args_rejects_scorecard_log_with_execute() {
        let err = parse_args(
            ["port", "--execute", "--scorecard-log", "previous.log"].map(OsString::from),
        )
        .expect_err("scorecard-log with execute should fail closed");

        match err {
            CliError::Usage(message) => {
                assert!(message.contains("--scorecard-log is log-parse mode"))
            }
            other => panic!("expected usage error, got {other:?}"),
        }
    }

    fn assert_duplicate_flag(err: CliError, flag: &str) {
        match err {
            CliError::Usage(message) => assert!(
                message.contains(&format!("duplicate {flag}")),
                "expected duplicate error for {flag}, got {message}"
            ),
            other => panic!("expected usage error, got {other:?}"),
        }
    }

    #[test]
    fn parse_port_args_scorecard_log_defaults_to_log_parse_mode() {
        let command = parse_args(["port", "--scorecard-log", "previous.log"].map(OsString::from))
            .expect("scorecard-log should imply non-executing log-parse mode");

        match command {
            Command::Port(options) => {
                assert!(!options.execute);
                assert!(!options.apply);
                assert_eq!(options.scorecard_log, Some(PathBuf::from("previous.log")));
            }
            other => panic!("expected port command, got {other:?}"),
        }
    }

    #[test]
    fn parse_port_args_rejects_invalid_proof_mode() {
        let err = parse_args(["port", "--proof-mode", "release"].map(OsString::from))
            .expect_err("invalid proof mode should fail");

        match err {
            CliError::Usage(message) => {
                assert!(message.contains("--proof-mode"));
                assert!(message.contains("auto, smoke, or full"));
            }
            other => panic!("expected usage error, got {other:?}"),
        }
    }

    #[test]
    fn port_auto_proof_mode_treats_bounded_runs_as_smoke() {
        assert_eq!(resolved_proof_mode(ProofMode::Auto, Some(1)), ProofMode::Smoke);
        assert_eq!(resolved_proof_mode(ProofMode::Auto, None), ProofMode::Full);
        assert_eq!(resolved_proof_mode(ProofMode::Full, Some(1)), ProofMode::Full);
    }

    #[test]
    fn validate_command_accepts_consistent_documents() {
        let fixture = Fixture::new("accepts-consistent-documents");
        let baseline = fixture.write("baseline.toml", BASELINE_TOML);
        let exceptions = fixture.write("exceptions.toml", EXCEPTIONS_TOML);
        let fixes = fixture.write("upstream-fixes.toml", UPSTREAM_FIXES_TOML);
        let summary = fixture.write("summary.toml", SUMMARY_TOML);
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let result = run(
            [
                OsString::from("trust-upstream-compat"),
                OsString::from("validate"),
                OsString::from("--baseline"),
                baseline.into_os_string(),
                OsString::from("--exceptions"),
                exceptions.into_os_string(),
                OsString::from("--upstream-fixes"),
                fixes.into_os_string(),
                OsString::from("--summary"),
                summary.into_os_string(),
            ],
            &mut stdout,
            &mut stderr,
        );

        assert_eq!(result, Ok(()));
        assert!(stdout.is_empty());
        assert!(stderr.is_empty());
    }

    #[test]
    fn validate_command_reports_bundle_findings() {
        let fixture = Fixture::new("reports-bundle-findings");
        let baseline = fixture.write("baseline.toml", BASELINE_TOML);
        let exceptions = fixture.write("exceptions.toml", DANGLING_EXCEPTIONS_TOML);
        let fixes = fixture.write("upstream-fixes.toml", UPSTREAM_FIXES_TOML);
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let result = run(
            [
                OsString::from("trust-upstream-compat"),
                OsString::from("validate"),
                OsString::from("--baseline"),
                baseline.into_os_string(),
                OsString::from("--exceptions"),
                exceptions.into_os_string(),
                OsString::from("--upstream-fixes"),
                fixes.into_os_string(),
            ],
            &mut stdout,
            &mut stderr,
        );

        assert_eq!(result, Err(1));
        assert!(stdout.is_empty());
        let stderr = String::from_utf8(stderr).expect("stderr should be utf-8");
        assert!(stderr.contains("accounting bundle failed validation"));
        assert!(stderr.contains("unknown baseline entry"));
    }

    #[test]
    fn validate_command_rejects_unaccounted_upstream_revision_drift() {
        let fixture = Fixture::new("rejects-unaccounted-upstream-drift");
        let baseline = fixture.write("baseline.toml", BASELINE_TOML);
        let exceptions = fixture.write("exceptions.toml", EXCEPTIONS_TOML);
        let fixes = fixture.write("upstream-fixes.toml", EMPTY_UPSTREAM_FIXES_TOML);
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let result = run(
            [
                OsString::from("trust-upstream-compat"),
                OsString::from("validate"),
                OsString::from("--baseline"),
                baseline.into_os_string(),
                OsString::from("--exceptions"),
                exceptions.into_os_string(),
                OsString::from("--upstream-fixes"),
                fixes.into_os_string(),
                OsString::from("--current-upstream-revision"),
                OsString::from("rust-lang-rust:feedface"),
            ],
            &mut stdout,
            &mut stderr,
        );

        assert_eq!(result, Err(1));
        assert!(stdout.is_empty());
        let stderr = String::from_utf8(stderr).expect("stderr should be utf-8");
        assert!(stderr.contains("upstream_fixes.fixes"));
        assert!(stderr.contains("differs from current upstream revision"));
    }

    #[test]
    fn validate_command_rejects_non_empty_unreviewed_upstream_fix_ledger_after_drift() {
        let fixture = Fixture::new("rejects-non-empty-unreviewed-upstream-drift");
        let baseline = fixture.write("baseline.toml", BASELINE_TOML);
        let exceptions = fixture.write("exceptions.toml", EXCEPTIONS_TOML);
        let fixes = fixture.write("upstream-fixes.toml", UPSTREAM_FIXES_TOML);
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let result = run(
            [
                OsString::from("trust-upstream-compat"),
                OsString::from("validate"),
                OsString::from("--baseline"),
                baseline.into_os_string(),
                OsString::from("--exceptions"),
                exceptions.into_os_string(),
                OsString::from("--upstream-fixes"),
                fixes.into_os_string(),
                OsString::from("--current-upstream-revision"),
                OsString::from("rust-lang-rust:feedface"),
            ],
            &mut stdout,
            &mut stderr,
        );

        assert_eq!(result, Err(1));
        assert!(stdout.is_empty());
        let stderr = String::from_utf8(stderr).expect("stderr should be utf-8");
        assert!(stderr.contains("upstream_fixes.tracked_until_revision"));
        assert!(stderr.contains("no reviewed-through revision"));
    }

    #[test]
    fn validate_command_rejects_incomplete_result_summary() {
        let fixture = Fixture::new("rejects-incomplete-result-summary");
        let baseline = fixture.write("baseline.toml", BASELINE_TOML);
        let exceptions = fixture.write("exceptions.toml", EXCEPTIONS_TOML);
        let fixes = fixture.write("upstream-fixes.toml", UPSTREAM_FIXES_TOML);
        let summary = fixture.write("summary.toml", INCOMPLETE_SUMMARY_TOML);
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let result = run(
            [
                OsString::from("trust-upstream-compat"),
                OsString::from("validate"),
                OsString::from("--baseline"),
                baseline.into_os_string(),
                OsString::from("--exceptions"),
                exceptions.into_os_string(),
                OsString::from("--upstream-fixes"),
                fixes.into_os_string(),
                OsString::from("--summary"),
                summary.into_os_string(),
            ],
            &mut stdout,
            &mut stderr,
        );

        assert_eq!(result, Err(1));
        assert!(stdout.is_empty());
        let stderr = String::from_utf8(stderr).expect("stderr should be utf-8");
        assert!(stderr.contains("result_summary.results"));
        assert!(stderr.contains("entry.two"));
        assert!(stderr.contains("missing result"));
    }

    #[test]
    fn prove_command_accepts_per_test_evidence() {
        let fixture = Fixture::new("accepts-per-test-evidence");
        let baseline = fixture.write("baseline.toml", BASELINE_TOML);
        let exceptions = fixture.write("exceptions.toml", EXCEPTIONS_TOML);
        let fixes = fixture.write("upstream-fixes.toml", UPSTREAM_FIXES_TOML);
        let inventory = fixture.write("inventory.toml", TEST_INVENTORY_TOML);
        let results = fixture.write("results.toml", TEST_RESULTS_TOML);
        let test_exceptions = fixture.write("test-exceptions.toml", TEST_EXCEPTIONS_TOML);
        let trust_tests = fixture.write("trust-tests.toml", TRUST_TESTS_TOML);
        let proof_summary = fixture.root.join("proof-summary.json");
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let result = run(
            [
                OsString::from("trust-upstream-compat"),
                OsString::from("prove"),
                OsString::from("--baseline"),
                baseline.into_os_string(),
                OsString::from("--exceptions"),
                exceptions.into_os_string(),
                OsString::from("--upstream-fixes"),
                fixes.into_os_string(),
                OsString::from("--inventory"),
                inventory.into_os_string(),
                OsString::from("--results"),
                results.into_os_string(),
                OsString::from("--test-exceptions"),
                test_exceptions.into_os_string(),
                OsString::from("--trust-tests"),
                trust_tests.into_os_string(),
                OsString::from("--release"),
                OsString::from("--proof-summary-out"),
                proof_summary.clone().into_os_string(),
            ],
            &mut stdout,
            &mut stderr,
        );

        assert_eq!(result, Ok(()));
        assert!(stdout.is_empty());
        assert!(stderr.is_empty());
        let summary = fs::read_to_string(proof_summary).expect("proof summary should be written");
        assert!(summary.contains("\"unaccounted\": 0"));
        assert!(summary.contains("\"trust_added\": 1"));
    }

    #[test]
    fn prove_command_rejects_unaccounted_non_pass() {
        let fixture = Fixture::new("rejects-unaccounted-non-pass");
        let baseline = fixture.write("baseline.toml", BASELINE_TOML);
        let exceptions = fixture.write("exceptions.toml", EXCEPTIONS_TOML);
        let fixes = fixture.write("upstream-fixes.toml", UPSTREAM_FIXES_TOML);
        let inventory = fixture.write("inventory.toml", TEST_INVENTORY_TOML);
        let results = fixture.write("results.toml", UNACCOUNTED_TEST_RESULTS_TOML);
        let test_exceptions = fixture.write("test-exceptions.toml", TEST_EXCEPTIONS_TOML);
        let trust_tests = fixture.write("trust-tests.toml", TRUST_TESTS_TOML);
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let result = run(
            [
                OsString::from("trust-upstream-compat"),
                OsString::from("prove"),
                OsString::from("--baseline"),
                baseline.into_os_string(),
                OsString::from("--exceptions"),
                exceptions.into_os_string(),
                OsString::from("--upstream-fixes"),
                fixes.into_os_string(),
                OsString::from("--inventory"),
                inventory.into_os_string(),
                OsString::from("--results"),
                results.into_os_string(),
                OsString::from("--test-exceptions"),
                test_exceptions.into_os_string(),
                OsString::from("--trust-tests"),
                trust_tests.into_os_string(),
                OsString::from("--release"),
            ],
            &mut stdout,
            &mut stderr,
        );

        assert_eq!(result, Err(1));
        assert!(stdout.is_empty());
        let stderr = String::from_utf8(stderr).expect("stderr should be utf-8");
        assert!(stderr.contains("non-pass result"));
        assert!(stderr.contains("totals.unaccounted"));
    }

    #[test]
    fn prove_command_rejects_python_trust_added_manifest_command() {
        let fixture = Fixture::new("rejects-python-trust-added-command");
        let baseline = fixture.write("baseline.toml", BASELINE_TOML);
        let exceptions = fixture.write("exceptions.toml", EXCEPTIONS_TOML);
        let fixes = fixture.write("upstream-fixes.toml", UPSTREAM_FIXES_TOML);
        let inventory = fixture.write("inventory.toml", TEST_INVENTORY_TOML);
        let results = fixture.write("results.toml", TEST_RESULTS_TOML);
        let test_exceptions = fixture.write("test-exceptions.toml", TEST_EXCEPTIONS_TOML);
        let trust_tests = fixture.write("trust-tests.toml", PYTHON_TRUST_TESTS_TOML);
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let result = run(
            [
                OsString::from("trust-upstream-compat"),
                OsString::from("prove"),
                OsString::from("--baseline"),
                baseline.into_os_string(),
                OsString::from("--exceptions"),
                exceptions.into_os_string(),
                OsString::from("--upstream-fixes"),
                fixes.into_os_string(),
                OsString::from("--inventory"),
                inventory.into_os_string(),
                OsString::from("--results"),
                results.into_os_string(),
                OsString::from("--test-exceptions"),
                test_exceptions.into_os_string(),
                OsString::from("--trust-tests"),
                trust_tests.into_os_string(),
            ],
            &mut stdout,
            &mut stderr,
        );

        assert_eq!(result, Err(1));
        assert!(stdout.is_empty());
        let stderr = String::from_utf8(stderr).expect("stderr should be utf-8");
        assert!(stderr.contains("commands[0].command"));
        assert!(stderr.contains("python3"));
    }

    #[test]
    fn prove_command_rejects_non_release_trust_added_manifest_command() {
        let fixture = Fixture::new("rejects-non-release-trust-added-command");
        let baseline = fixture.write("baseline.toml", BASELINE_TOML);
        let exceptions = fixture.write("exceptions.toml", EXCEPTIONS_TOML);
        let fixes = fixture.write("upstream-fixes.toml", UPSTREAM_FIXES_TOML);
        let inventory = fixture.write("inventory.toml", TEST_INVENTORY_TOML);
        let results = fixture.write("results.toml", TEST_RESULTS_TOML);
        let test_exceptions = fixture.write("test-exceptions.toml", TEST_EXCEPTIONS_TOML);
        let trust_tests = fixture.write("trust-tests.toml", NON_RELEASE_TRUST_TESTS_TOML);
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let result = run(
            [
                OsString::from("trust-upstream-compat"),
                OsString::from("prove"),
                OsString::from("--baseline"),
                baseline.into_os_string(),
                OsString::from("--exceptions"),
                exceptions.into_os_string(),
                OsString::from("--upstream-fixes"),
                fixes.into_os_string(),
                OsString::from("--inventory"),
                inventory.into_os_string(),
                OsString::from("--results"),
                results.into_os_string(),
                OsString::from("--test-exceptions"),
                test_exceptions.into_os_string(),
                OsString::from("--trust-tests"),
                trust_tests.into_os_string(),
                OsString::from("--release"),
            ],
            &mut stdout,
            &mut stderr,
        );

        assert_eq!(result, Err(1));
        assert!(stdout.is_empty());
        let stderr = String::from_utf8(stderr).expect("stderr should be utf-8");
        assert!(stderr.contains("commands[0].command"));
        assert!(stderr.contains("exactly one pre-mode `--release`"));
    }

    #[test]
    fn upstream_inventory_includes_compiletest_oracles() {
        assert!(is_probable_test_input("tests/ui/borrowck/issue.stderr"));
        assert!(is_probable_test_input("tests/ui/borrowck/issue.stdout"));
        assert!(is_probable_test_input("tests/ui/fmt/issue.fixed"));
        assert!(is_probable_test_input("tests/mir-opt/example.mir"));
        assert!(is_probable_test_input("tests/codegen/example.ll"));
        assert!(is_probable_test_input("src/tools/targo/tests/testsuite/Cargo.lock"));
    }

    struct Fixture {
        root: PathBuf,
    }

    impl Fixture {
        fn new(name: &str) -> Self {
            let mut root = env::temp_dir();
            let nanos = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system clock should be after unix epoch")
                .as_nanos();
            root.push(format!("trust-upstream-compat-{name}-{}-{nanos}", std::process::id()));
            fs::create_dir_all(&root).expect("fixture directory should be created");
            Self { root }
        }

        fn write(&self, name: &str, contents: &str) -> PathBuf {
            let path = self.root.join(name);
            fs::write(&path, contents).expect("fixture file should be written");
            path
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.root);
        }
    }

    const BASELINE_TOML: &str = r#"
schema_version = "0.1.0"
id = "baseline.cli"

[upstream]
channel = "nightly"
revision = "rust-lang-rust:abc123"
snapshot_date = "2026-04-26"

[local]
revision = "trust:def456"

[[entries]]
id = "entry.one"
title = "entry one"
surface = "cli"
upstream_artifact = "tests/ui/entry-one.rs"
status = "diverged"

[entries.expectation]
upstream_behavior = "upstream behavior one"
local_behavior = "local behavior one"
compatibility_rule = "rule one"

[[entries]]
id = "entry.two"
title = "entry two"
surface = "mir"
upstream_artifact = "compiler/rustc_mir_transform/src/elaborate_drops.rs"
status = "compatible"

[entries.expectation]
upstream_behavior = "upstream behavior two"
local_behavior = "local behavior two"
compatibility_rule = "rule two"
"#;

    const EXCEPTIONS_TOML: &str = r#"
schema_version = "0.1.0"

[[exceptions]]
id = "exc.entry.one"
baseline_entry_id = "entry.one"
title = "entry one exception"
class = "intentional_divergence"
status = "active"
owner = "compat"
reason = "local behavior intentionally diverges"
expires_on = "2026-12-31"
"#;

    const DANGLING_EXCEPTIONS_TOML: &str = r#"
schema_version = "0.1.0"

[[exceptions]]
id = "exc.entry.missing"
baseline_entry_id = "entry.missing"
title = "missing entry exception"
class = "intentional_divergence"
status = "active"
owner = "compat"
reason = "local behavior intentionally diverges"
expires_on = "2026-12-31"
"#;

    const UPSTREAM_FIXES_TOML: &str = r#"
schema_version = "0.1.0"

[[fixes]]
id = "fix.entry.two"
baseline_entry_id = "entry.two"
title = "entry two upstream fix"
upstream_reference = "rust-lang/rust#123457"
status = "landed"
local_action = "rebase_baseline"
landed_on = "2026-04-20"
"#;

    const EMPTY_UPSTREAM_FIXES_TOML: &str = r#"
schema_version = "0.1.0"
fixes = []
"#;

    const SUMMARY_TOML: &str = r#"
schema_version = "0.1.0"
baseline_id = "baseline.cli"
generated_on = "2026-04-26"

[totals]
total = 2
compatible = 0
divergent = 0
excepted = 1
fixed_upstream = 1
unknown = 0

[[results]]
baseline_entry_id = "entry.one"
outcome = "excepted"
observed = "local behavior is waived"
exception_id = "exc.entry.one"

[[results]]
baseline_entry_id = "entry.two"
outcome = "fixed_upstream"
observed = "upstream fix accounts for the result"
upstream_fix_id = "fix.entry.two"
"#;

    const INCOMPLETE_SUMMARY_TOML: &str = r#"
schema_version = "0.1.0"
baseline_id = "baseline.cli"
generated_on = "2026-04-26"

[totals]
total = 1
compatible = 0
divergent = 0
excepted = 1
fixed_upstream = 0
unknown = 0

[[results]]
baseline_entry_id = "entry.one"
outcome = "excepted"
observed = "local behavior is waived"
exception_id = "exc.entry.one"
"#;

    const TEST_INVENTORY_TOML: &str = r#"
schema_version = "0.1.0"
upstream_revision = "rust-lang-rust:abc123"
local_revision = "trust:def456"
host = "aarch64-apple-darwin"

[[tests]]
id = "upstream.ui.entry-one"
suite = "ui"
path = "tests/ui/entry-one.rs"
revision = "rust-lang-rust:abc123"
source_git_blob = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
source = "upstream_rust"
kind = "compiletest"
applicable = true
source_sha256 = "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"

[[tests]]
id = "trust.cargo-cli.midpoint"
suite = "targo-trust"
path = "tests/e2e_midpoint.sh"
source = "trust_added"
kind = "shell"
applicable = true
"#;

    const TEST_RESULTS_TOML: &str = r#"
schema_version = "0.1.0"
inventory_id = "inventory.fixture"
generated_on = "2026-04-27"
command = "trust-upstream-compat fixture command"

[[results]]
test_id = "upstream.ui.entry-one"
outcome = "diffed"
exception_id = "test-exc.entry-one"
observed = "diagnostic URL changed intentionally"
artifact = "diffs/test-exc.entry-one.diff"

[[results]]
test_id = "trust.cargo-cli.midpoint"
outcome = "passed"
"#;

    const UNACCOUNTED_TEST_RESULTS_TOML: &str = r#"
schema_version = "0.1.0"
inventory_id = "inventory.fixture"
generated_on = "2026-04-27"
command = "trust-upstream-compat fixture command"

[[results]]
test_id = "upstream.ui.entry-one"
outcome = "failed"
observed = "unaccounted failure"

[[results]]
test_id = "trust.cargo-cli.midpoint"
outcome = "passed"
"#;

    const TEST_EXCEPTIONS_TOML: &str = r#"
schema_version = "0.1.0"

[[exceptions]]
id = "test-exc.entry-one"
test_id = "upstream.ui.entry-one"
suite = "ui"
path = "tests/ui/entry-one.rs"
revision = "rust-lang-rust:abc123"
kind = "changed_diagnostic"
status = "active"
owner = "compat"
reason = "intentional Trust diagnostic URL"
issue = "https://github.com/alabsystems/Trust/issues/1"
introduced_by = "def456"
reviewed_on = "2026-04-27"
expires_on = "2026-12-31"
allowed_patterns = ["diagnostic URL changed intentionally"]
"#;

    const TRUST_TESTS_TOML: &str = r#"
schema_version = "0.1.0"

[[commands]]
id = "trust.added.midpoint"
command = "targo trust domination trust-added --release quick"
covers = ["trust.cargo-cli.midpoint"]
required = true
"#;

    const NON_RELEASE_TRUST_TESTS_TOML: &str = r#"
schema_version = "0.1.0"

[[commands]]
id = "trust.added.non-release"
command = "targo trust domination trust-added quick"
covers = ["trust.cargo-cli.midpoint"]
required = true
"#;

    const PYTHON_TRUST_TESTS_TOML: &str = r#"
schema_version = "0.1.0"

[[commands]]
id = "trust.added.python"
command = "python3 tests/e2e_midpoint.py"
covers = ["trust.cargo-cli.midpoint"]
required = true
"#;
}
