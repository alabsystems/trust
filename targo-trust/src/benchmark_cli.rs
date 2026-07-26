// Rust-owned benchmark runners for Trust evidence surfaces.
//
// The program-index runner intentionally mirrors the existing declarative
// corpus while keeping the public entry point inside `targo trust`.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::fs::{self, File, OpenOptions};
use std::io::{BufRead, BufReader, Read, Seek, SeekFrom};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use std::{env, thread};

use serde::Serialize;
use serde_json::{Map, Value, json};
use sha2::{Digest, Sha256};

const INDEX_SCHEMA: &str = "trust.compile-verify-program-index.v1";
const REPORT_SCHEMA: &str = "trust.compile-verify-program-index.report.v1";
const PROGRAM_INDEX_EVIDENCE_SCHEMA: &str =
    "trust.compile-verify-program-index.evidence-admissibility.v1";
const PROOF_DESIGN_VERIFIER_EVIDENCE_SCHEMA: &str =
    "trust.compile-verify-program-index.proof-design-verifier-evidence.v1";
const RUNTIME_PARITY_SCHEMA: &str = "trust.program-index.runtime-output-parity.v1";
const STAGE2_SNAPSHOT_SCHEMA: &str = "trust.stage2-toolchain-snapshot.v1";
const STAGE2_SNAPSHOT_DIGEST_SCHEMA: &str = "trust.stage2-toolchain-snapshot.digest.v2";
const UNSUPPORTED_MIR_GATE_SCHEMA: &str = "trust.program-index.unsupported-mir-gate.v1";
const UNSUPPORTED_FRONTEND_LOWERING_GATE_SCHEMA: &str =
    "trust.program-index.unsupported-frontend-lowering-gate.v1";
const STAGE2_PREFLIGHT_SCHEMA: &str = "trust.program-index.stage2-preflight.v1";
const UNLOCK_PATH_SCHEMA: &str = "trust.program-index.unlock-path.v1";
const TRANSPORT_PREFIX: &str = "TRUST_JSON:";
const MAX_CAPTURE_BYTES: usize = 2_000_000;
const MAX_COMMAND_LOG_BYTES: u64 = 64 * 1024 * 1024;
const MAX_BENCHMARK_TIMEOUT_SECONDS: u64 = 24 * 60 * 60;
const IDENTITY_PROBE_MAX_STREAM_BYTES: usize = 64 * 1024;
const IDENTITY_PROBE_TIMEOUT: Duration = Duration::from_secs(5);
const GIT_PROBE_MAX_STREAM_BYTES: usize = 64 * 1024 * 1024;
const GIT_PROBE_TIMEOUT: Duration = Duration::from_secs(30);
const EXCERPT_BYTES: usize = 4_000;
const UNSUPPORTED_MIR_GATE_ROW_LIMIT: usize = 50;
const TOOLCHAIN_MUTATED: &str = "toolchain_mutated";
const RUNTIME_BASELINE_SLOT: &str = "upstream-rustc";
const SLOT_ORDER: &[&str] =
    &["upstream-rustc", "trust-noverify", "trust-verify", "llvm", "trust-cg"];
const COMPILE_MEASUREMENT_PROFILE_SCHEMA: &str =
    "trust.program-index.compile-measurement-profile.v1";
const STRICT_SUPERIORITY_PERFORMANCE_SCHEMA: &str =
    "trust.strict-superiority.performance-evidence.v1";
const STRICT_SUPERIORITY_PLATFORM_IDENTITY_SCHEMA: &str =
    "trust.strict-superiority.platform-identity.v1";
const PROOF_DESIGN_SUITE: &str = "proof-design";
const PROOF_DESIGN_CANDIDATE_SUITE: &str = "proof-design-candidates";

const BENCHMARK_USAGE: &str = "\
Usage: targo trust benchmark <command> [args...]

Commands:
  program-index   Run the compile/verify program-index matrix in Rust

Examples:
  targo trust benchmark program-index --list
  targo trust benchmark program-index --suite proof-design --limit 2 --slots trust-verify
  targo trust benchmark program-index --runtime-parity --slots upstream-rustc trust-noverify llvm

Python is not used by this benchmark command.
";

const PROGRAM_INDEX_USAGE: &str = "\
Usage: targo trust benchmark program-index [options]

Options:
  --repo-root PATH          Trust checkout root (default: discovered checkout)
  --index PATH              Program index JSON (default: examples/bench/program_index/index.json)
  --run-id ID               Report run id
  --report-dir PATH         Report directory (default: reports/bench/program-index/<run-id>)
  --slots SLOT...           Slots to run: upstream-rustc trust-noverify trust-verify llvm trust-cg
  --slot-bin SLOT=PATH      Override a slot binary; Trust slots require absolute executable paths
  --program ID              Program id or pair id filter; repeatable
  --variant good|flawed     Variant filter
  --suite NAME              Suite filter
  --limit N                 Limit selected programs after filtering
  --timeout SECONDS         Per-command timeout (default: 20)
  --repetitions N           Repeated samples per program/slot row (default: 1)
  --trust-cg-mode report|enforce
  --build-profile debug|release
                           rustc codegen profile for compile/runtime evidence (default: debug)
  --compile-measurement cold-artifact|warm-incremental
                           Compile timing mode (default: cold-artifact)
  --runtime-parity          Link/run compile slots and compare runtime output
  --require-slots           Fail if any selected slot binary is missing
  --dry-run                 Write planned commands without running compilers
  --list                    List selected programs without running compilers
  -h, --help                Show this help

Python is not used by this benchmark command.
";

#[derive(Debug)]
struct ProgramIndexError(String);

impl ProgramIndexError {
    fn new(message: impl Into<String>) -> Self {
        Self(message.into())
    }
}

impl std::fmt::Display for ProgramIndexError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.0)
    }
}

#[derive(Debug, Clone)]
struct Program {
    id: String,
    pair_id: String,
    variant: String,
    path: PathBuf,
    relative_path: String,
    source_sha256: String,
    obligations: Vec<String>,
    suite: String,
    metadata: Value,
}

#[derive(Debug, Clone, Copy)]
struct SlotProfile {
    id: &'static str,
    mode: &'static str,
    fallback_binary: &'static str,
    extra_args: &'static [&'static str],
}

#[derive(Debug, Clone)]
struct SlotBinding {
    id: String,
    profile: SlotProfile,
    binary: Option<String>,
    source: String,
}

#[derive(Debug, Clone)]
struct ProgramIndexArgs {
    repo_root: PathBuf,
    index: PathBuf,
    run_id: String,
    report_dir: Option<PathBuf>,
    slots: Vec<String>,
    slot_bins: Vec<String>,
    programs: Vec<String>,
    variant: Option<String>,
    suite: Option<String>,
    limit: Option<usize>,
    timeout_seconds: u64,
    repetitions: usize,
    trust_cg_mode: String,
    build_profile: BuildProfile,
    compile_measurement_mode: CompileMeasurementMode,
    runtime_parity: bool,
    require_slots: bool,
    dry_run: bool,
    list: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompileMeasurementMode {
    ColdArtifact,
    WarmIncremental,
}

impl CompileMeasurementMode {
    fn as_str(self) -> &'static str {
        match self {
            Self::ColdArtifact => "cold-artifact",
            Self::WarmIncremental => "warm-incremental",
        }
    }

    fn requested_incremental(self) -> bool {
        matches!(self, Self::WarmIncremental)
    }

    fn uses_warmup(self) -> bool {
        matches!(self, Self::WarmIncremental)
    }

    fn cargo_incremental_env(self) -> &'static str {
        match self {
            Self::ColdArtifact => "0",
            Self::WarmIncremental => "1",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BuildProfile {
    Debug,
    Release,
}

impl BuildProfile {
    fn as_str(self) -> &'static str {
        match self {
            Self::Debug => "debug",
            Self::Release => "release",
        }
    }

    fn rustc_args(self) -> &'static [&'static str] {
        match self {
            Self::Debug => &[],
            Self::Release => &["-C", "opt-level=3", "-C", "debuginfo=0"],
        }
    }
}

#[derive(Debug, Clone)]
struct CommandRun {
    exit_code: Option<i32>,
    timed_out: bool,
    elapsed_seconds: f64,
    resource_usage: Value,
}

#[derive(Debug, Clone)]
struct ExecutionResult {
    status: String,
    exit_code: Option<i32>,
    duration_seconds: f64,
    timed_out: bool,
    stdout_path: PathBuf,
    stderr_path: PathBuf,
    stdout_bytes: u64,
    stderr_bytes: u64,
    output_path: PathBuf,
    output_exists: bool,
    resource_usage: Value,
    transport: Value,
    stderr_excerpt: String,
    stderr_tail_excerpt: String,
}

#[derive(Debug, Clone)]
struct WarmupMeasurement {
    command: Vec<String>,
    result: ExecutionResult,
    expected: String,
    valid: bool,
}

#[derive(Debug, Clone)]
struct SlotRunSample {
    sample_index: usize,
    command: Vec<String>,
    result: ExecutionResult,
    observed: String,
    outcome: String,
    exception_class: String,
    warmup: Option<WarmupMeasurement>,
    incremental_dir: Option<PathBuf>,
}

pub(crate) fn run_benchmark_subcommand(args: &[String]) -> ExitCode {
    let Some(command) = args.first().map(String::as_str) else {
        print!("{BENCHMARK_USAGE}");
        return ExitCode::from(2);
    };
    if is_help_arg(command) {
        print!("{BENCHMARK_USAGE}");
        return ExitCode::SUCCESS;
    }

    match command {
        "program-index" => run_program_index_subcommand(&args[1..]),
        other => {
            eprintln!("targo trust benchmark: unknown command `{other}`");
            eprint!("{BENCHMARK_USAGE}");
            ExitCode::from(2)
        }
    }
}

fn run_program_index_subcommand(args: &[String]) -> ExitCode {
    if args.first().is_some_and(|arg| is_help_arg(arg)) {
        print!("{PROGRAM_INDEX_USAGE}");
        return ExitCode::SUCCESS;
    }

    let args = match parse_program_index_args(args) {
        Ok(args) => args,
        Err(error) => {
            eprintln!("program-index benchmark: {error}");
            eprint!("{PROGRAM_INDEX_USAGE}");
            return ExitCode::from(2);
        }
    };

    match run_program_index(args) {
        Ok((status, report_path)) => {
            if let Some(report_path) = report_path {
                print_terminal_summary(&report_path);
            }
            ExitCode::from(status)
        }
        Err(error) => {
            eprintln!("program-index benchmark: {error}");
            ExitCode::from(2)
        }
    }
}

fn parse_program_index_args(args: &[String]) -> Result<ProgramIndexArgs, ProgramIndexError> {
    let discovered_root = discover_repo_root().map_err(|error| {
        ProgramIndexError::new(format!("failed to discover repo root: {error}"))
    })?;
    let mut parsed = ProgramIndexArgs {
        repo_root: discovered_root,
        index: PathBuf::from("examples/bench/program_index/index.json"),
        run_id: default_run_id(),
        report_dir: None,
        slots: SLOT_ORDER.iter().map(|slot| (*slot).to_string()).collect(),
        slot_bins: Vec::new(),
        programs: Vec::new(),
        variant: None,
        suite: None,
        limit: None,
        timeout_seconds: 20,
        repetitions: 1,
        trust_cg_mode: "report".to_string(),
        build_profile: BuildProfile::Debug,
        compile_measurement_mode: CompileMeasurementMode::ColdArtifact,
        runtime_parity: false,
        require_slots: false,
        dry_run: false,
        list: false,
    };

    let mut index = 0;
    while index < args.len() {
        match args[index].as_str() {
            "-h" | "--help" => unreachable!("handled before parsing"),
            "--repo-root" => {
                let value = value_after(args, index, "--repo-root")?;
                parsed.repo_root = PathBuf::from(value);
                index += 2;
            }
            option if option.starts_with("--repo-root=") => {
                parsed.repo_root = PathBuf::from(value_in(option, "--repo-root="));
                index += 1;
            }
            "--index" => {
                let value = value_after(args, index, "--index")?;
                parsed.index = PathBuf::from(value);
                index += 2;
            }
            option if option.starts_with("--index=") => {
                parsed.index = PathBuf::from(value_in(option, "--index="));
                index += 1;
            }
            "--run-id" => {
                parsed.run_id = value_after(args, index, "--run-id")?.to_string();
                index += 2;
            }
            option if option.starts_with("--run-id=") => {
                parsed.run_id = value_in(option, "--run-id=").to_string();
                index += 1;
            }
            "--report-dir" => {
                parsed.report_dir = Some(PathBuf::from(value_after(args, index, "--report-dir")?));
                index += 2;
            }
            option if option.starts_with("--report-dir=") => {
                parsed.report_dir = Some(PathBuf::from(value_in(option, "--report-dir=")));
                index += 1;
            }
            "--slots" => {
                let (slots, consumed) = parse_slot_values(args, index + 1)?;
                parsed.slots = slots;
                index = consumed;
            }
            option if option.starts_with("--slots=") => {
                parsed.slots = split_slot_list(value_in(option, "--slots="))?;
                index += 1;
            }
            "--slot-bin" => {
                let value = value_after(args, index, "--slot-bin")?;
                reject_deprecated_slot_bin_value(value)?;
                parsed.slot_bins.push(value.to_string());
                index += 2;
            }
            option if option.starts_with("--slot-bin=") => {
                let value = value_in(option, "--slot-bin=");
                reject_deprecated_slot_bin_value(value)?;
                parsed.slot_bins.push(value.to_string());
                index += 1;
            }
            "--program" => {
                parsed.programs.push(value_after(args, index, "--program")?.to_string());
                index += 2;
            }
            option if option.starts_with("--program=") => {
                parsed.programs.push(value_in(option, "--program=").to_string());
                index += 1;
            }
            "--variant" => {
                parsed.variant = Some(parse_variant(value_after(args, index, "--variant")?)?);
                index += 2;
            }
            option if option.starts_with("--variant=") => {
                parsed.variant = Some(parse_variant(value_in(option, "--variant="))?);
                index += 1;
            }
            "--suite" => {
                parsed.suite = Some(value_after(args, index, "--suite")?.to_string());
                index += 2;
            }
            option if option.starts_with("--suite=") => {
                parsed.suite = Some(value_in(option, "--suite=").to_string());
                index += 1;
            }
            "--limit" => {
                parsed.limit = Some(parse_usize(value_after(args, index, "--limit")?, "--limit")?);
                index += 2;
            }
            option if option.starts_with("--limit=") => {
                parsed.limit = Some(parse_usize(value_in(option, "--limit="), "--limit")?);
                index += 1;
            }
            "--timeout" => {
                parsed.timeout_seconds =
                    parse_u64(value_after(args, index, "--timeout")?, "--timeout")?;
                index += 2;
            }
            option if option.starts_with("--timeout=") => {
                parsed.timeout_seconds = parse_u64(value_in(option, "--timeout="), "--timeout")?;
                index += 1;
            }
            "--repetitions" => {
                parsed.repetitions =
                    parse_usize(value_after(args, index, "--repetitions")?, "--repetitions")?;
                index += 2;
            }
            option if option.starts_with("--repetitions=") => {
                parsed.repetitions =
                    parse_usize(value_in(option, "--repetitions="), "--repetitions")?;
                index += 1;
            }
            "--trust_cg-mode" => {
                return Err(deprecated_trust_cg_cli_spelling("--trust_cg-mode", "--trust-cg-mode"));
            }
            "--trust-cg-mode" => {
                parsed.trust_cg_mode =
                    parse_trust_cg_mode(value_after(args, index, args[index].as_str())?)?;
                index += 2;
            }
            option if option.starts_with("--trust_cg-mode=") => {
                return Err(deprecated_trust_cg_cli_spelling("--trust_cg-mode", "--trust-cg-mode"));
            }
            option if option.starts_with("--trust-cg-mode=") => {
                parsed.trust_cg_mode = parse_trust_cg_mode(value_in(option, "--trust-cg-mode="))?;
                index += 1;
            }
            "--build-profile" => {
                parsed.build_profile =
                    parse_build_profile(value_after(args, index, "--build-profile")?)?;
                index += 2;
            }
            option if option.starts_with("--build-profile=") => {
                parsed.build_profile = parse_build_profile(value_in(option, "--build-profile="))?;
                index += 1;
            }
            "--compile-measurement" => {
                parsed.compile_measurement_mode = parse_compile_measurement_mode(value_after(
                    args,
                    index,
                    "--compile-measurement",
                )?)?;
                index += 2;
            }
            option if option.starts_with("--compile-measurement=") => {
                parsed.compile_measurement_mode =
                    parse_compile_measurement_mode(value_in(option, "--compile-measurement="))?;
                index += 1;
            }
            "--runtime-parity" => {
                parsed.runtime_parity = true;
                index += 1;
            }
            "--require-slots" => {
                parsed.require_slots = true;
                index += 1;
            }
            "--dry-run" => {
                parsed.dry_run = true;
                index += 1;
            }
            "--list" => {
                parsed.list = true;
                index += 1;
            }
            other => {
                return Err(ProgramIndexError::new(format!("unknown option `{other}`")));
            }
        }
    }

    parsed.repo_root = absolutize(&parsed.repo_root, &env::current_dir().unwrap_or_default());
    parsed.index = absolutize(&parsed.index, &parsed.repo_root);
    if let Some(report_dir) = parsed.report_dir.take() {
        parsed.report_dir = Some(absolutize(&report_dir, &parsed.repo_root));
    }
    if parsed.timeout_seconds == 0 {
        return Err(ProgramIndexError::new("--timeout must be at least 1"));
    }
    if parsed.timeout_seconds > MAX_BENCHMARK_TIMEOUT_SECONDS {
        return Err(ProgramIndexError::new(format!(
            "--timeout must not exceed {MAX_BENCHMARK_TIMEOUT_SECONDS} seconds"
        )));
    }
    if parsed.repetitions == 0 {
        return Err(ProgramIndexError::new("--repetitions must be at least 1"));
    }
    Ok(parsed)
}

fn run_program_index(args: ProgramIndexArgs) -> Result<(u8, Option<PathBuf>), ProgramIndexError> {
    let (raw_index, all_programs) = load_index(&args.index, &args.repo_root)?;
    let programs = filter_programs(
        &all_programs,
        &args.programs,
        args.variant.as_deref(),
        args.suite.as_deref(),
        args.limit,
    )?;
    if args.list {
        print_programs(&programs);
        return Ok((0, None));
    }

    let overrides = parse_slot_overrides(&args.slot_bins)?;
    let bindings = resolve_slots(&args.slots, &overrides, &args.repo_root);
    let missing_required: Vec<String> = bindings
        .iter()
        .filter(|binding| binding.binary.is_none())
        .map(|binding| binding.id.clone())
        .collect();
    let report_dir = args
        .report_dir
        .clone()
        .unwrap_or_else(|| args.repo_root.join("reports/bench/program-index").join(&args.run_id));
    fs::create_dir_all(&report_dir)
        .map_err(|error| ProgramIndexError::new(format!("create report dir: {error}")))?;
    let report_path = report_dir.join("report.json");

    if args.require_slots && !missing_required.is_empty() {
        let report_path = write_missing_required_slots_report(
            &args,
            &raw_index,
            &programs,
            &bindings,
            &missing_required,
            &report_path,
        )?;
        eprintln!(
            "program-index benchmark: required slot binary not found for: {}",
            missing_required.join(", ")
        );
        return Ok((2, Some(report_path)));
    }

    let started_at = timestamp_string();
    let start = Instant::now();
    let stage2_roots = stage2_roots_for_bindings(&bindings, &args.repo_root);
    let monitored_slots = monitored_stage2_slots(&bindings, &args.repo_root);
    let (stage2_before, stage2_before_path, mut toolchain_integrity) = if args.dry_run {
        (None, None, toolchain_integrity_not_applicable("dry-run does not execute compilers"))
    } else if stage2_roots.is_empty() {
        (
            None,
            None,
            toolchain_integrity_not_applicable(
                "no selected compiler binary was resolved from repo build/*/stage2",
            ),
        )
    } else {
        let snapshot = capture_stage2_snapshot(&args.repo_root, &stage2_roots)?;
        let path = write_named_report(&snapshot, &report_dir.join("toolchain/stage2-before.json"))?;
        (
            Some(snapshot),
            Some(path),
            toolchain_integrity_not_applicable("post-run snapshot has not been captured"),
        )
    };

    let mut runtime_parity = runtime_parity_not_requested();
    let mut rows = Vec::new();
    if args.dry_run {
        for program in &programs {
            for binding in &bindings {
                rows.push(planned_row(
                    binding,
                    program,
                    &report_dir,
                    &raw_index,
                    args.build_profile,
                    args.compile_measurement_mode,
                    args.repetitions,
                ));
            }
        }
        if args.runtime_parity {
            runtime_parity = runtime_parity_not_applicable(
                "dry-run does not compile, link, or run runtime parity artifacts",
                true,
            );
        }
        preserve_pre_exception_outcomes(&mut rows);
    } else {
        for program in &programs {
            for binding in &bindings {
                rows.push(run_slot(
                    binding,
                    program,
                    &args.repo_root,
                    &report_dir,
                    args.timeout_seconds,
                    &raw_index,
                    args.build_profile,
                    args.compile_measurement_mode,
                    args.repetitions,
                )?);
            }
        }
        preserve_pre_exception_outcomes(&mut rows);
        apply_trust_cg_mode(&mut rows, &args.trust_cg_mode);
        let gaps = expected_known_gaps(&raw_index)?;
        let gap_hooks = expected_gap_hooks(&raw_index, &gaps)?;
        apply_expected_known_gaps(&mut rows, &gaps, &gap_hooks);
        apply_unsupported_mir_gate(&mut rows, &gaps, &gap_hooks);
        apply_unsupported_frontend_lowering_gate(&mut rows, &gaps, &gap_hooks);
        if args.runtime_parity {
            runtime_parity = run_runtime_parity(
                &programs,
                &bindings,
                &args.repo_root,
                &report_dir,
                args.timeout_seconds,
                args.build_profile,
            )?;
        }
        if let Some(before) = stage2_before.as_ref() {
            let after = capture_stage2_snapshot(&args.repo_root, &stage2_roots)?;
            let after_path =
                write_named_report(&after, &report_dir.join("toolchain/stage2-after.json"))?;
            toolchain_integrity = compare_stage2_snapshots(
                before,
                &after,
                stage2_before_path.as_deref(),
                Some(after_path.as_path()),
                &report_dir,
            );
        }
    }
    apply_result_classification(&mut rows);
    annotate_toolchain_integrity(&mut rows, &toolchain_integrity, &monitored_slots);
    let upstream_baseline = upstream_baseline_integrity(&bindings, &args.repo_root);

    let completed_at = timestamp_string();
    let mut summary = summarize(&rows);
    let performance_platform_identity =
        performance_platform_identity(&bindings, &rows, &runtime_parity, &args.repo_root);
    insert_obj(
        &mut summary,
        "known_good_pass",
        expectation_rows_summary(
            &rows,
            |row| {
                value_str(row, "variant") == Some("good")
                    && matches!(value_str(row, "expected"), Some("compile_pass" | "verify_pass"))
            },
            "known-good programs matched their expected compile or verification status",
        ),
    );
    insert_obj(
        &mut summary,
        "known_flawed_rejection",
        expectation_rows_summary(
            &rows,
            |row| {
                value_str(row, "variant") == Some("flawed")
                    && value_str(row, "expected") == Some("verify_fail")
            },
            "known-flawed programs were rejected by verification",
        ),
    );
    insert_obj(
        &mut summary,
        "known_good_compile_acceptance",
        compile_acceptance_summary(&rows, "good"),
    );
    insert_obj(
        &mut summary,
        "known_flawed_compile_acceptance",
        compile_acceptance_summary(&rows, "flawed"),
    );
    insert_obj(
        &mut summary,
        "trust_cg_exceptions",
        trust_cg_exception_summary(&rows, &args.trust_cg_mode),
    );
    insert_obj(&mut summary, "runtime_parity", runtime_parity_report_summary(&runtime_parity));
    insert_obj(&mut summary, "backward_pass", backward_pass_summary(&rows));
    insert_obj(&mut summary, "unsupported_mir_gate", unsupported_mir_gate_summary(&rows));
    insert_obj(
        &mut summary,
        "unsupported_frontend_lowering_gate",
        unsupported_frontend_lowering_gate_summary(&rows),
    );
    insert_obj(&mut summary, "codegen_output_evidence", codegen_output_evidence_summary(&rows));
    insert_obj(&mut summary, "hello_world_gate", hello_world_gate_summary(&rows));
    insert_obj(
        &mut summary,
        "repair_evidence",
        repair_evidence_summary(&args.repo_root, &report_dir),
    );
    summary.insert(
        "duration_seconds".to_string(),
        json!(round_seconds(start.elapsed().as_secs_f64())),
    );
    summary.insert(
        "toolchain_integrity_status".to_string(),
        json!(toolchain_integrity["status"].as_str().unwrap_or("unknown")),
    );
    summary.insert(
        "toolchain_mutated".to_string(),
        json!(toolchain_integrity["status"].as_str() == Some(TOOLCHAIN_MUTATED)),
    );
    summary.insert(
        "runtime_parity_status".to_string(),
        json!(runtime_parity["status"].as_str().unwrap_or("unknown")),
    );
    summary.insert(
        "runtime_parity_failed".to_string(),
        json!(runtime_parity["summary"]["failed"].as_u64().unwrap_or(0)),
    );
    insert_obj(&mut summary, "upstream_baseline", upstream_baseline.clone());
    let program_index_evidence = program_index_evidence_summary(&programs, &raw_index);
    insert_obj(
        &mut summary,
        "program_index_evidence",
        program_index_evidence_summary_for_report(&program_index_evidence),
    );
    let proof_design_verifier_evidence = proof_design_verifier_evidence(
        &args,
        &rows,
        &bindings,
        &program_index_evidence,
        &toolchain_integrity,
        &report_dir,
    );
    insert_obj(
        &mut summary,
        "proof_design_verifier_evidence",
        proof_design_verifier_evidence_summary_for_report(&proof_design_verifier_evidence),
    );
    let strict_performance_evidence = strict_superiority_performance_evidence(
        &args,
        &rows,
        &runtime_parity,
        &program_index_evidence,
        &performance_platform_identity,
    );
    insert_obj(
        &mut summary,
        "strict_superiority_performance_evidence",
        strict_superiority_performance_evidence_summary_for_report(&strict_performance_evidence),
    );

    let report = json!({
        "schema": REPORT_SCHEMA,
        "runner": {
            "implementation": "rust",
            "entrypoint": "targo trust benchmark program-index",
            "python_used": false,
        },
        "run_id": args.run_id,
        "started_at": started_at,
        "completed_at": completed_at,
        "repo_root": args.repo_root.to_string_lossy(),
        "repo_head": repo_head(&args.repo_root),
        "repo_dirty": repo_dirty(&args.repo_root),
        "repo_dirty_metadata": repo_dirty_metadata(&args.repo_root),
        "target_arch": performance_platform_identity["target_arch"],
        "target_triple": performance_platform_identity["target_triple"],
        "host_arch": performance_platform_identity["host_arch"],
        "host_triple": performance_platform_identity["host_triple"],
        "performance_platform_identity": performance_platform_identity,
        "index": path_for_report(&args.index, &args.repo_root),
        "dry_run": args.dry_run,
        "trust_cg_mode": args.trust_cg_mode,
        "build_profile": args.build_profile.as_str(),
        "build_profile_detail": build_profile_report(args.build_profile),
        "compile_measurement_mode": args.compile_measurement_mode.as_str(),
        "compile_measurement": compile_measurement_report(args.compile_measurement_mode),
        "repetitions": args.repetitions,
        "timeout_seconds": args.timeout_seconds,
        "runtime_parity": runtime_parity,
        "strict_superiority_performance_evidence": strict_performance_evidence,
        "upstream_baseline": upstream_baseline,
        "corpus": corpus_summary(&programs, &args.slots),
        "program_index_evidence": program_index_evidence,
        "proof_design_verifier_evidence": proof_design_verifier_evidence,
        "toolchain_integrity": toolchain_integrity,
        "stage2_preflight": stage2_preflight_state(&bindings, &args.repo_root),
        "trust_unlock_path": trust_unlock_path(&bindings, &args.repo_root),
        "slot_bindings": bindings.iter().map(|binding| json!({
            "slot": binding.id,
            "mode": binding.profile.mode,
            "binary": binding.binary,
            "source": binding.source,
        })).collect::<Vec<_>>(),
        "summary": summary,
        "results": rows,
    });
    write_report(&report, &report_path)?;

    let runtime_parity_blocked =
        args.runtime_parity && !args.dry_run && runtime_parity["status"].as_str() != Some("passed");
    let backward_pass_blocked =
        report["summary"]["backward_pass"]["status"].as_str() == Some("partial");
    let proof_design_verifier_blocked =
        report["summary"]["proof_design_verifier_evidence"]["required"].as_bool() == Some(true)
            && report["summary"]["proof_design_verifier_evidence"]["status"].as_str()
                != Some("passed");
    let failed = report["summary"]["failed"].as_u64().unwrap_or(0) > 0
        || report["summary"]["toolchain_mutated"].as_bool().unwrap_or(false)
        || report["summary"]["upstream_baseline"]["status"].as_str() == Some("blocked")
        || report["summary"]["runtime_parity_failed"].as_u64().unwrap_or(0) > 0
        || runtime_parity_blocked
        || backward_pass_blocked
        || proof_design_verifier_blocked;
    Ok((if failed { 1 } else { 0 }, Some(report_path)))
}

fn write_missing_required_slots_report(
    args: &ProgramIndexArgs,
    raw_index: &Value,
    programs: &[Program],
    bindings: &[SlotBinding],
    missing_required: &[String],
    report_path: &Path,
) -> Result<PathBuf, ProgramIndexError> {
    let started_at = timestamp_string();
    let mut rows = Vec::new();
    let missing: BTreeSet<&str> = missing_required.iter().map(String::as_str).collect();
    for program in programs {
        for binding in bindings {
            let expected = expected_status(&binding.id, program);
            let reason = if missing.contains(binding.id.as_str()) {
                "required slot binary not found"
            } else {
                "blocked by missing required slot binary"
            };
            rows.push(skipped_row(
                binding,
                program,
                &expected,
                reason,
                raw_index,
                args.build_profile,
                args.compile_measurement_mode,
                args.repetitions,
            ));
        }
    }
    apply_result_classification(&mut rows);

    let completed_at = timestamp_string();
    let mut summary = summarize(&rows);
    let performance_platform_identity = performance_platform_identity(
        bindings,
        &rows,
        &runtime_parity_not_requested(),
        &args.repo_root,
    );
    let required_slots = json!({
        "status": "missing_required_slots",
        "required": true,
        "missing": missing_required,
        "message": format!("required slot binary not found for: {}", missing_required.join(", ")),
    });
    summary.insert("required_slots".to_string(), required_slots.clone());
    insert_obj(
        &mut summary,
        "known_good_compile_acceptance",
        compile_acceptance_summary(&rows, "good"),
    );
    insert_obj(
        &mut summary,
        "known_flawed_compile_acceptance",
        compile_acceptance_summary(&rows, "flawed"),
    );
    insert_obj(&mut summary, "unsupported_mir_gate", unsupported_mir_gate_summary(&rows));
    insert_obj(
        &mut summary,
        "unsupported_frontend_lowering_gate",
        unsupported_frontend_lowering_gate_summary(&rows),
    );
    insert_obj(&mut summary, "codegen_output_evidence", codegen_output_evidence_summary(&rows));
    insert_obj(&mut summary, "hello_world_gate", hello_world_gate_summary(&rows));
    summary.insert("duration_seconds".to_string(), json!(0.0));
    summary.insert("toolchain_integrity_status".to_string(), json!("not_applicable"));
    summary.insert("toolchain_mutated".to_string(), json!(false));
    summary.insert(
        "runtime_parity_status".to_string(),
        json!(if args.runtime_parity { "blocked" } else { "not_requested" }),
    );
    summary.insert("runtime_parity_failed".to_string(), json!(0));
    let upstream_baseline = upstream_baseline_integrity(bindings, &args.repo_root);
    insert_obj(&mut summary, "upstream_baseline", upstream_baseline.clone());
    let program_index_evidence = program_index_evidence_summary(programs, raw_index);
    insert_obj(
        &mut summary,
        "program_index_evidence",
        program_index_evidence_summary_for_report(&program_index_evidence),
    );
    let proof_design_verifier_evidence = proof_design_verifier_evidence(
        args,
        &rows,
        bindings,
        &program_index_evidence,
        &toolchain_integrity_not_applicable("missing required slot binaries blocked execution"),
        report_path.parent().unwrap_or_else(|| Path::new(".")),
    );
    insert_obj(
        &mut summary,
        "proof_design_verifier_evidence",
        proof_design_verifier_evidence_summary_for_report(&proof_design_verifier_evidence),
    );

    let runtime_parity = if args.runtime_parity {
        runtime_parity_not_applicable("missing required slot binaries blocked runtime parity", true)
    } else {
        runtime_parity_not_requested()
    };
    let strict_performance_evidence = strict_superiority_performance_evidence(
        args,
        &rows,
        &runtime_parity,
        &program_index_evidence,
        &performance_platform_identity,
    );
    insert_obj(
        &mut summary,
        "strict_superiority_performance_evidence",
        strict_superiority_performance_evidence_summary_for_report(&strict_performance_evidence),
    );
    let toolchain_integrity =
        toolchain_integrity_not_applicable("missing required slot binaries blocked execution");
    let report = json!({
        "schema": REPORT_SCHEMA,
        "runner": {
            "implementation": "rust",
            "entrypoint": "targo trust benchmark program-index",
            "python_used": false,
        },
        "run_id": args.run_id,
        "started_at": started_at,
        "completed_at": completed_at,
        "repo_root": args.repo_root.to_string_lossy(),
        "repo_head": repo_head(&args.repo_root),
        "repo_dirty": repo_dirty(&args.repo_root),
        "repo_dirty_metadata": repo_dirty_metadata(&args.repo_root),
        "target_arch": performance_platform_identity["target_arch"],
        "target_triple": performance_platform_identity["target_triple"],
        "host_arch": performance_platform_identity["host_arch"],
        "host_triple": performance_platform_identity["host_triple"],
        "performance_platform_identity": performance_platform_identity,
        "index": path_for_report(&args.index, &args.repo_root),
        "dry_run": args.dry_run,
        "trust_cg_mode": args.trust_cg_mode,
        "build_profile": args.build_profile.as_str(),
        "build_profile_detail": build_profile_report(args.build_profile),
        "compile_measurement_mode": args.compile_measurement_mode.as_str(),
        "compile_measurement": compile_measurement_report(args.compile_measurement_mode),
        "repetitions": args.repetitions,
        "timeout_seconds": args.timeout_seconds,
        "runtime_parity": runtime_parity,
        "strict_superiority_performance_evidence": strict_performance_evidence,
        "upstream_baseline": upstream_baseline,
        "corpus": corpus_summary(programs, &args.slots),
        "program_index_evidence": program_index_evidence,
        "proof_design_verifier_evidence": proof_design_verifier_evidence,
        "toolchain_integrity": toolchain_integrity,
        "stage2_preflight": stage2_preflight_state(bindings, &args.repo_root),
        "trust_unlock_path": trust_unlock_path(bindings, &args.repo_root),
        "required_slots": required_slots,
        "slot_bindings": bindings.iter().map(|binding| json!({
            "slot": binding.id,
            "mode": binding.profile.mode,
            "binary": binding.binary,
            "source": binding.source,
        })).collect::<Vec<_>>(),
        "summary": summary,
        "results": rows,
    });
    write_report(&report, report_path)?;
    Ok(report_path.to_path_buf())
}

fn slot_profile(slot_id: &str) -> Option<SlotProfile> {
    match slot_id {
        "upstream-rustc" => Some(SlotProfile {
            id: "upstream-rustc",
            mode: "compile",
            fallback_binary: "rustc",
            extra_args: &[],
        }),
        "trust-noverify" => Some(SlotProfile {
            id: "trust-noverify",
            mode: "compile",
            fallback_binary: "trustc",
            extra_args: &["-Z", "trust-verify=off"],
        }),
        "trust-verify" => Some(SlotProfile {
            id: "trust-verify",
            mode: "verify",
            fallback_binary: "trustc",
            extra_args: &["-Z", "trust-verify-level=1", "-Z", "trust-verify-output=json"],
        }),
        "llvm" => Some(SlotProfile {
            id: "llvm",
            mode: "compile",
            fallback_binary: "trustc",
            extra_args: &["-Z", "trust-verify=off", "-Z", "codegen-backend=llvm"],
        }),
        "trust-cg" => Some(SlotProfile {
            id: "trust-cg",
            mode: "compile",
            fallback_binary: "trustc",
            extra_args: &["-Z", "trust-verify=off", "-Z", "codegen-backend=trust_cg"],
        }),
        _ => None,
    }
}

fn load_index(
    index_path: &Path,
    repo_root: &Path,
) -> Result<(Value, Vec<Program>), ProgramIndexError> {
    let text = crate::input_limits::read_bounded_utf8_file(
        index_path,
        crate::input_limits::MAX_SAVED_PROOF_REPORT_BYTES,
    )
    .map_err(|error| ProgramIndexError::new(format!("read {}: {error}", index_path.display())))?;
    let raw: Value = serde_json::from_str(&text).map_err(|error| {
        ProgramIndexError::new(format!("{}: invalid JSON: {error}", index_path.display()))
    })?;
    if raw["schema"].as_str() != Some(INDEX_SCHEMA) {
        return Err(ProgramIndexError::new(format!(
            "{}: expected schema {INDEX_SCHEMA}, got {:?}",
            index_path.display(),
            raw["schema"].as_str()
        )));
    }
    let raw_programs = raw["programs"]
        .as_array()
        .ok_or_else(|| ProgramIndexError::new("programs must be a non-empty list"))?;
    if raw_programs.is_empty() {
        return Err(ProgramIndexError::new("programs must be a non-empty list"));
    }
    let mut programs = Vec::new();
    for row in raw_programs {
        programs.push(parse_program(row, repo_root)?);
    }
    validate_program_ids(&programs)?;
    validate_pairs(&programs)?;
    let gaps = expected_known_gaps(&raw)?;
    validate_expected_known_gap_hooks(&raw, &gaps)?;
    Ok((raw, programs))
}

fn parse_program(row: &Value, repo_root: &Path) -> Result<Program, ProgramIndexError> {
    let object =
        row.as_object().ok_or_else(|| ProgramIndexError::new("program rows must be objects"))?;
    let id = required_str(object, "id")?;
    let pair_id = required_str(object, "pair_id")?;
    let variant = required_str(object, "variant")?;
    if variant != "good" && variant != "flawed" {
        return Err(ProgramIndexError::new(format!("{id}: variant must be good or flawed")));
    }
    let relative_path = required_str(object, "path")?;
    let path = resolve_source_path(repo_root, &relative_path, &id)?;
    let source_sha256 = file_sha256(&path)
        .map_err(|error| ProgramIndexError::new(format!("{id}: hash source: {error}")))?;
    let obligations_raw = object
        .get("obligations")
        .and_then(Value::as_array)
        .ok_or_else(|| ProgramIndexError::new(format!("{id}: obligations must be a list")))?;
    if obligations_raw.is_empty() {
        return Err(ProgramIndexError::new(format!("{id}: obligations must be non-empty")));
    }
    let mut obligations = Vec::new();
    for obligation in obligations_raw {
        let Some(value) = obligation.as_str() else {
            return Err(ProgramIndexError::new(format!(
                "{id}: obligations entries must be strings"
            )));
        };
        obligations.push(value.to_string());
    }
    let suite = required_str(object, "suite")?;
    let metadata = object.get("metadata").cloned().unwrap_or_else(|| json!({}));
    if !metadata.is_object() {
        return Err(ProgramIndexError::new(format!("{id}: metadata must be an object")));
    }
    Ok(Program {
        id,
        pair_id,
        variant,
        path,
        relative_path,
        source_sha256,
        obligations,
        suite,
        metadata,
    })
}

fn required_str(object: &Map<String, Value>, key: &str) -> Result<String, ProgramIndexError> {
    object
        .get(key)
        .and_then(Value::as_str)
        .filter(|value| !value.is_empty())
        .map(str::to_string)
        .ok_or_else(|| ProgramIndexError::new(format!("program row missing field `{key}`")))
}

fn resolve_source_path(
    repo_root: &Path,
    relative_path: &str,
    program_id: &str,
) -> Result<PathBuf, ProgramIndexError> {
    let raw_path = Path::new(relative_path);
    if raw_path.is_absolute() {
        return Err(ProgramIndexError::new(format!("{program_id}: source path must be relative")));
    }
    let source = repo_root.join(raw_path);
    let root = repo_root
        .canonicalize()
        .map_err(|error| ProgramIndexError::new(format!("canonicalize repo root: {error}")))?;
    let canonical_source = source.canonicalize().map_err(|error| {
        ProgramIndexError::new(format!(
            "{program_id}: source path `{relative_path}` is not readable: {error}"
        ))
    })?;
    if !canonical_source.starts_with(&root) {
        return Err(ProgramIndexError::new(format!(
            "{program_id}: source path `{relative_path}` escapes repo root"
        )));
    }
    Ok(canonical_source)
}

fn validate_program_ids(programs: &[Program]) -> Result<(), ProgramIndexError> {
    let mut seen = BTreeSet::new();
    let mut duplicates = Vec::new();
    for program in programs {
        if !seen.insert(program.id.clone()) {
            duplicates.push(program.id.clone());
        }
    }
    if duplicates.is_empty() {
        Ok(())
    } else {
        Err(ProgramIndexError::new(format!("duplicate program ids: {}", duplicates.join(", "))))
    }
}

fn validate_pairs(programs: &[Program]) -> Result<(), ProgramIndexError> {
    let mut pairs: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for program in programs {
        pairs.entry(program.pair_id.clone()).or_default().insert(program.variant.clone());
    }
    let invalid: Vec<String> = pairs
        .into_iter()
        .filter_map(|(pair, variants)| {
            (variants != BTreeSet::from(["flawed".to_string(), "good".to_string()])).then_some(pair)
        })
        .collect();
    if invalid.is_empty() {
        Ok(())
    } else {
        Err(ProgramIndexError::new(format!(
            "pairs must contain exactly good and flawed variants: {}",
            invalid.join(", ")
        )))
    }
}

fn filter_programs(
    programs: &[Program],
    program_ids: &[String],
    variant: Option<&str>,
    suite: Option<&str>,
    limit: Option<usize>,
) -> Result<Vec<Program>, ProgramIndexError> {
    let wanted: BTreeSet<&str> = program_ids.iter().map(String::as_str).collect();
    let mut selected = Vec::new();
    for program in programs {
        if !wanted.is_empty()
            && !wanted.contains(program.id.as_str())
            && !wanted.contains(program.pair_id.as_str())
        {
            continue;
        }
        if variant.is_some_and(|wanted| wanted != program.variant) {
            continue;
        }
        if suite.is_some_and(|wanted| wanted != program.suite) {
            continue;
        }
        selected.push(program.clone());
    }
    if !wanted.is_empty() {
        let known: BTreeSet<&str> = programs
            .iter()
            .flat_map(|program| [program.id.as_str(), program.pair_id.as_str()])
            .collect();
        let missing: Vec<&str> = wanted.difference(&known).copied().collect();
        if !missing.is_empty() {
            return Err(ProgramIndexError::new(format!(
                "unknown program or pair id(s): {}",
                missing.join(", ")
            )));
        }
    }
    if let Some(limit) = limit {
        selected.truncate(limit);
    }
    if selected.is_empty() {
        return Err(ProgramIndexError::new("program filter selected no programs"));
    }
    Ok(selected)
}

fn parse_slot_overrides(values: &[String]) -> Result<BTreeMap<String, String>, ProgramIndexError> {
    let mut overrides = BTreeMap::new();
    for value in values {
        let Some((slot, binary)) = value.split_once('=') else {
            return Err(ProgramIndexError::new(format!(
                "--slot-bin must use SLOT=PATH syntax: {value}"
            )));
        };
        reject_deprecated_trust_cg_slot(slot, "--slot-bin")?;
        if slot_profile(slot).is_none() {
            return Err(ProgramIndexError::new(format!("unknown slot in --slot-bin: {slot}")));
        }
        if binary.is_empty() {
            return Err(ProgramIndexError::new(format!("empty binary path for slot {slot}")));
        }
        overrides.insert(slot.to_string(), binary.to_string());
    }
    Ok(overrides)
}

fn resolve_slots(
    slot_ids: &[String],
    overrides: &BTreeMap<String, String>,
    repo_root: &Path,
) -> Vec<SlotBinding> {
    slot_ids
        .iter()
        .filter_map(|slot_id| {
            slot_profile(slot_id).map(|profile| resolve_slot(profile, overrides, repo_root))
        })
        .collect()
}

fn resolve_slot(
    profile: SlotProfile,
    overrides: &BTreeMap<String, String>,
    repo_root: &Path,
) -> SlotBinding {
    if let Some(override_value) = overrides.get(profile.id) {
        let resolved = if is_trust_owned_slot(profile.id) {
            resolve_absolute_executable(override_value)
        } else {
            resolve_executable(override_value)
        };
        return SlotBinding {
            id: profile.id.to_string(),
            profile,
            binary: resolved,
            source: explicit_slot_source(profile.id, override_value),
        };
    }
    if matches!(profile.id, "trust-noverify" | "trust-verify" | "llvm" | "trust-cg") {
        for candidate in trustc_candidates(repo_root) {
            if is_executable_path(&candidate) {
                return SlotBinding {
                    id: profile.id.to_string(),
                    profile,
                    binary: Some(candidate.to_string_lossy().into_owned()),
                    source: "repo-stage2".to_string(),
                };
            }
        }
        return SlotBinding {
            id: profile.id.to_string(),
            profile,
            binary: None,
            source: "missing".to_string(),
        };
    }
    let resolved = which(profile.fallback_binary);
    SlotBinding {
        id: profile.id.to_string(),
        profile,
        binary: resolved.clone(),
        source: if resolved.is_some() { "path" } else { "missing" }.to_string(),
    }
}

fn explicit_slot_source(slot_id: &str, value: &str) -> String {
    if is_trust_owned_slot(slot_id) {
        if resolve_absolute_executable(value).is_some() {
            "override:absolute".to_string()
        } else if Path::new(value).is_absolute() {
            "missing".to_string()
        } else {
            "invalid-relative-override".to_string()
        }
    } else if is_executable_string(value) {
        "override".to_string()
    } else {
        "missing".to_string()
    }
}

fn is_trust_owned_slot(slot_id: &str) -> bool {
    matches!(slot_id, "trust-noverify" | "trust-verify" | "llvm" | "trust-cg")
}

fn resolved_binary_name(binding: &SlotBinding) -> Option<&str> {
    binding
        .binary
        .as_deref()
        .and_then(|binary| Path::new(binary).file_name())
        .and_then(OsStr::to_str)
}

fn upstream_baseline_integrity(bindings: &[SlotBinding], repo_root: &Path) -> Value {
    let mut entries = Vec::new();
    let mut blockers = Vec::new();
    for binding in bindings.iter().filter(|binding| binding.id == RUNTIME_BASELINE_SLOT) {
        let entry = upstream_baseline_binding_integrity(binding, repo_root);
        blockers.extend(
            entry["blockers"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .map(str::to_string),
        );
        entries.push(entry);
    }
    let status = if entries.is_empty() {
        "not_applicable"
    } else if blockers.is_empty() {
        "passed"
    } else {
        "blocked"
    };
    json!({
        "schema": "trust.program-index.upstream-baseline-integrity.v1",
        "status": status,
        "baseline_slot": RUNTIME_BASELINE_SLOT,
        "entries": entries,
        "blockers": blockers,
    })
}

fn upstream_baseline_binding_integrity(binding: &SlotBinding, repo_root: &Path) -> Value {
    let mut blockers = Vec::new();
    let Some(binary) = binding.binary.as_deref() else {
        return json!({
            "slot": binding.id,
            "status": "blocked",
            "binary": Value::Null,
            "source": binding.source,
            "blockers": ["upstream-rustc baseline binary is missing"],
            "version_probe": Value::Null,
            "sysroot_probe": Value::Null,
        });
    };

    let binary_path = absolutize(Path::new(binary), repo_root);
    let binary_report_path = path_for_report(&binary_path, repo_root);
    let stage2_roots = stage2_roots_for_binary(binary, repo_root);
    if !stage2_roots.is_empty() {
        blockers.push(
            "upstream-rustc baseline resolves inside this Trust repo stage2 tree".to_string(),
        );
    }
    if path_is_inside_repo(&binary_path, repo_root) {
        blockers.push("upstream-rustc baseline binary is inside this Trust checkout".to_string());
    }
    if resolved_binary_name(binding).is_some_and(trust_compiler_binary_name) {
        blockers.push(format!(
            "upstream-rustc baseline binary name `{}` is Trust-owned",
            resolved_binary_name(binding).unwrap_or("<unknown>")
        ));
    }

    let version_probe = compiler_identity_probe(binary, &["-vV"]);
    if probe_failed(&version_probe) {
        blockers.push("upstream-rustc -vV probe must succeed".to_string());
    }
    if probe_declares_trust(&version_probe) {
        blockers.push("upstream-rustc -vV output declares a Trust toolchain".to_string());
    }
    let version_text = probe_text(&version_probe);
    if probe_field(&version_text, "binary").as_deref() != Some("rustc") {
        blockers.push("upstream-rustc -vV output must declare `binary: rustc`".to_string());
    }
    match probe_field(&version_text, "commit-hash") {
        Some(commit) if full_git_sha(&commit) => {}
        Some(commit) => blockers.push(format!(
            "upstream-rustc -vV output must declare a full commit-hash, got `{commit}`"
        )),
        None => blockers.push("upstream-rustc -vV output must declare commit-hash".to_string()),
    }
    for field in ["host", "release"] {
        if probe_field(&version_text, field).as_deref().is_none_or(str::is_empty) {
            blockers.push(format!("upstream-rustc -vV output must declare {field}"));
        }
    }
    let sysroot_probe = compiler_identity_probe(binary, &["--print", "sysroot"]);
    if probe_failed(&sysroot_probe) {
        blockers.push("upstream-rustc --print sysroot probe must succeed".to_string());
    }
    if probe_declares_trust(&sysroot_probe) {
        blockers.push("upstream-rustc sysroot output declares a Trust toolchain".to_string());
    }
    let sysroot_text = probe_text(&sysroot_probe);
    let sysroot = sysroot_text.lines().next().map(str::trim).unwrap_or("");
    if sysroot.is_empty() {
        blockers.push("upstream-rustc --print sysroot must emit a nonempty sysroot".to_string());
    } else {
        let sysroot_path = absolutize(Path::new(sysroot), repo_root);
        if path_is_inside_repo(&sysroot_path, repo_root) {
            blockers.push("upstream-rustc sysroot resolves inside this Trust checkout".to_string());
        }
    }

    json!({
        "slot": binding.id,
        "status": if blockers.is_empty() { "passed" } else { "blocked" },
        "binary": binary_report_path,
        "source": binding.source,
        "blockers": blockers,
        "stage2_roots": stage2_roots
            .iter()
            .map(|root| path_for_report(root, repo_root))
            .collect::<Vec<_>>(),
        "version_probe": version_probe,
        "sysroot_probe": sysroot_probe,
    })
}

fn path_is_inside_repo(path: &Path, repo_root: &Path) -> bool {
    let path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let repo_root = repo_root.canonicalize().unwrap_or_else(|_| repo_root.to_path_buf());
    path.starts_with(repo_root)
}

fn trust_compiler_binary_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase().replace('_', "-");
    lower == "trustc"
        || lower == "targo"
        || lower == "targo-trust"
        || lower.starts_with("trust-")
        || lower.contains("trustc")
}

fn compiler_identity_probe(binary: &str, args: &[&str]) -> Value {
    let argv = std::iter::once(binary.to_string())
        .chain(args.iter().map(|arg| arg.to_string()))
        .collect::<Vec<_>>();
    let mut command = Command::new(binary);
    command.args(args).env_clear();
    let output = match crate::bounded_process::output(
        &mut command,
        &format!("compiler identity probe for {binary}"),
        IDENTITY_PROBE_MAX_STREAM_BYTES,
        IDENTITY_PROBE_TIMEOUT,
    ) {
        Ok(output) => output,
        Err(error) => {
            let status = if error.contains("timeout") {
                "timeout"
            } else if error.contains("could not start") {
                "unavailable"
            } else {
                "failed"
            };
            return json!({
                "status": status,
                "argv": argv,
                "error": error,
                "trust_marker": false,
            });
        }
    };
    let stdout = match String::from_utf8(output.stdout) {
        Ok(stdout) => compact_probe_text(&stdout),
        Err(_) => {
            return json!({
                "status": "failed",
                "argv": argv,
                "error": "compiler identity stdout was not valid UTF-8",
                "trust_marker": false,
            });
        }
    };
    let stderr = match String::from_utf8(output.stderr) {
        Ok(stderr) => compact_probe_text(&stderr),
        Err(_) => {
            return json!({
                "status": "failed",
                "argv": argv,
                "error": "compiler identity stderr was not valid UTF-8",
                "trust_marker": false,
            });
        }
    };
    json!({
        "status": if output.status.success() { "available" } else { "failed" },
        "argv": argv,
        "exit_code": output.status.code(),
        "stdout": stdout,
        "stderr": stderr,
        "trust_marker": text_declares_trust_toolchain(&stdout)
            || text_declares_trust_toolchain(&stderr),
    })
}

fn compact_probe_text(text: &str) -> String {
    let text = text.trim();
    let mut compact = String::new();
    for ch in text.chars().take(1000) {
        compact.push(ch);
    }
    if text.chars().nth(1000).is_some() {
        compact.push_str("...");
    }
    compact
}

fn probe_declares_trust(probe: &Value) -> bool {
    probe.get("trust_marker").and_then(Value::as_bool) == Some(true)
}

fn probe_failed(probe: &Value) -> bool {
    probe.get("status").and_then(Value::as_str) != Some("available")
}

fn probe_text(probe: &Value) -> String {
    [probe.get("stdout"), probe.get("stderr")]
        .into_iter()
        .filter_map(|value| value.and_then(Value::as_str))
        .filter(|value| !value.trim().is_empty())
        .collect::<Vec<_>>()
        .join("\n")
}

fn probe_field(text: &str, field: &str) -> Option<String> {
    let prefix = format!("{field}:");
    text.lines()
        .find_map(|line| line.trim().strip_prefix(&prefix).map(str::trim))
        .filter(|value| !value.is_empty())
        .map(str::to_string)
}

fn full_git_sha(value: &str) -> bool {
    value.len() == 40 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn text_declares_trust_toolchain(text: &str) -> bool {
    let lower = text.to_ascii_lowercase().replace('\\', "/");
    lower.contains("/trust/")
        || lower.contains("trustc")
        || lower.contains("targo-trust")
        || lower.contains("rust-trust")
        || lower.contains("toolchain: trust")
        || lower.contains("release: trust")
        || lower.contains("-trust")
}

fn slot_diagnostics(binding: &SlotBinding, raw_index: &Value) -> Value {
    json!({
        "canonical_binary": binding.profile.fallback_binary,
        "trust_owned": is_trust_owned_slot(&binding.id),
        "trust_owned_binary_name": if is_trust_owned_slot(&binding.id) {
            Value::String(binding.profile.fallback_binary.to_string())
        } else {
            Value::Null
        },
        "resolved_binary_name": resolved_binary_name(binding),
        "source": binding.source,
        "sysroot_path": Value::Null,
        "sysroot_query": {
            "status": "not_probed",
            "reason": "Rust runner records compiler behavior through benchmark invocations",
        },
        "index_schema": raw_index.get("schema").and_then(Value::as_str),
    })
}

fn stage2_preflight_state(bindings: &[SlotBinding], repo_root: &Path) -> Value {
    let missing_slots: Vec<String> = bindings
        .iter()
        .filter(|binding| binding.binary.is_none())
        .map(|binding| binding.id.clone())
        .collect();
    let noncanonical_slots: Vec<String> = bindings
        .iter()
        .filter(|binding| {
            is_trust_owned_slot(&binding.id)
                && binding.binary.is_some()
                && resolved_binary_name(binding) != Some(binding.profile.fallback_binary)
        })
        .map(|binding| binding.id.clone())
        .collect();
    let stage2_roots = stage2_roots_for_bindings(bindings, repo_root)
        .into_iter()
        .map(|root| path_for_report(&root, repo_root))
        .collect::<Vec<_>>();
    let status = if !missing_slots.is_empty() {
        "missing_slots"
    } else if !noncanonical_slots.is_empty() {
        "noncanonical_trust_entrypoints"
    } else if stage2_roots.is_empty() {
        "no_repo_stage2_slots"
    } else {
        "ready"
    };
    json!({
        "schema": STAGE2_PREFLIGHT_SCHEMA,
        "status": status,
        "stage2_roots": stage2_roots,
        "missing_slots": missing_slots,
        "noncanonical_slots": noncanonical_slots,
        "slot_bindings": bindings.iter().map(|binding| json!({
            "slot": binding.id,
            "mode": binding.profile.mode,
            "binary": binding.binary,
            "source": binding.source,
            "canonical_binary": binding.profile.fallback_binary,
            "resolved_binary_name": resolved_binary_name(binding),
            "trust_owned": is_trust_owned_slot(&binding.id),
            "extra_args": binding.profile.extra_args,
        })).collect::<Vec<_>>(),
    })
}

fn trust_unlock_path(bindings: &[SlotBinding], repo_root: &Path) -> Value {
    let trust_bindings: Vec<&SlotBinding> =
        bindings.iter().filter(|binding| is_trust_owned_slot(&binding.id)).collect();
    let missing_slots: Vec<String> = trust_bindings
        .iter()
        .filter(|binding| binding.binary.is_none())
        .map(|binding| binding.id.clone())
        .collect();
    let noncanonical_slots: Vec<String> = trust_bindings
        .iter()
        .filter(|binding| {
            binding.binary.is_some()
                && resolved_binary_name(binding) != Some(binding.profile.fallback_binary)
        })
        .map(|binding| binding.id.clone())
        .collect();
    let ready_slots: Vec<String> = trust_bindings
        .iter()
        .filter(|binding| {
            binding.binary.is_some()
                && resolved_binary_name(binding) == Some(binding.profile.fallback_binary)
        })
        .map(|binding| binding.id.clone())
        .collect();
    let (status, reason) = if trust_bindings.is_empty() {
        ("not_applicable", "no Trust-owned program-index slots were selected".to_string())
    } else if !missing_slots.is_empty() {
        (
            "blocked_missing_slots",
            format!("Trust-owned slot binaries are missing: {}", missing_slots.join(", ")),
        )
    } else if !noncanonical_slots.is_empty() {
        (
            "blocked_noncanonical_entrypoints",
            format!(
                "Trust-owned slots resolved to non-canonical executable names: {}",
                noncanonical_slots.join(", ")
            ),
        )
    } else {
        (
            "ready_for_trust_compile_evidence",
            "all selected Trust-owned slots resolved to canonical Trust entrypoints".to_string(),
        )
    };
    json!({
        "schema": UNLOCK_PATH_SCHEMA,
        "status": status,
        "reason": reason,
        "trust_owned_slots": trust_bindings.iter().map(|binding| json!({
            "slot": binding.id,
            "mode": binding.profile.mode,
            "canonical_binary": binding.profile.fallback_binary,
            "resolved_binary": binding.binary,
            "resolved_binary_name": resolved_binary_name(binding),
            "canonical_entrypoint": binding.binary.is_some()
                && resolved_binary_name(binding) == Some(binding.profile.fallback_binary),
            "source": binding.source,
            "required_for_public_trust_evidence": true,
            "extra_args": binding.profile.extra_args,
        })).collect::<Vec<_>>(),
        "required_slots": trust_bindings.iter().map(|binding| binding.id.clone()).collect::<Vec<_>>(),
        "ready_slots": ready_slots,
        "missing_slots": missing_slots,
        "noncanonical_slots": noncanonical_slots,
        "canonical_binaries": trust_bindings
            .iter()
            .map(|binding| binding.profile.fallback_binary)
            .collect::<BTreeSet<_>>(),
        "lookup_order": trustc_lookup_specs(repo_root),
        "evidence_transition": {
            "from": "missing_required_slots",
            "to": "accepted_trust_compile_evidence",
            "accepted_when": [
                "all requested Trust-owned slots resolve to canonical trustc entrypoints",
                "the command is run with --require-slots so missing Trust slots fail closed",
                "compile slots accept known-good and known-flawed rows as expected",
                "trust-verify accepts known-good rows and rejects known-flawed rows unless an expected known gap applies",
                "ambient rustc/cargo names are not counted as Trust evidence; same-sysroot compatibility aliases are recorded as compatibility evidence",
            ],
        },
    })
}

fn trustc_lookup_specs(repo_root: &Path) -> Value {
    json!([
        {
            "kind": "slot-bin",
            "flag": "--slot-bin SLOT=PATH",
            "description": "explicit per-slot executable override; Trust-owned slots require absolute executable paths",
        },
        {
            "kind": "repo-stage2",
            "path": path_for_report(&repo_root.join("build/host/stage2/bin/trustc"), repo_root),
            "description": "repo-local host stage2 Trust compiler",
        },
        {
            "kind": "repo-stage2-glob",
            "pattern": "build/*/stage2/bin/trustc",
            "description": "repo-local target stage2 Trust compiler",
        },
    ])
}

fn compile_measurement_report(mode: CompileMeasurementMode) -> Value {
    json!({
        "schema": COMPILE_MEASUREMENT_PROFILE_SCHEMA,
        "mode": mode.as_str(),
        "phase": "compile_artifact",
        "requested_incremental": mode.requested_incremental(),
        "default": matches!(mode, CompileMeasurementMode::ColdArtifact),
        "evidence_classification": match mode {
            CompileMeasurementMode::ColdArtifact => "cold artifact compile timing; not incremental efficiency evidence",
            CompileMeasurementMode::WarmIncremental => {
                "warmup compile followed by measured rustc -C incremental compile"
            }
        },
        "timing_field": "duration_seconds",
        "runtime_measurements_separate": true,
    })
}

fn build_profile_report(profile: BuildProfile) -> Value {
    json!({
        "profile": profile.as_str(),
        "rustc_args": profile.rustc_args(),
        "release_like": matches!(profile, BuildProfile::Release),
        "debug_like": matches!(profile, BuildProfile::Debug),
    })
}

fn run_slot(
    binding: &SlotBinding,
    program: &Program,
    repo_root: &Path,
    report_dir: &Path,
    timeout_seconds: u64,
    raw_index: &Value,
    build_profile: BuildProfile,
    measurement_mode: CompileMeasurementMode,
    repetitions: usize,
) -> Result<Value, ProgramIndexError> {
    let artifacts_dir = report_dir.join("artifacts").join(&binding.id);
    let logs_dir = report_dir.join("logs").join(&binding.id);
    fs::create_dir_all(&artifacts_dir)
        .map_err(|error| ProgramIndexError::new(format!("create artifacts dir: {error}")))?;
    fs::create_dir_all(&logs_dir)
        .map_err(|error| ProgramIndexError::new(format!("create logs dir: {error}")))?;
    let expected = expected_status(&binding.id, program);
    if binding.binary.is_none() {
        return Ok(skipped_row(
            binding,
            program,
            &expected,
            "slot binary not found",
            raw_index,
            build_profile,
            measurement_mode,
            repetitions,
        ));
    }
    let mut samples = Vec::with_capacity(repetitions);
    for sample_index in 1..=repetitions {
        samples.push(run_slot_sample(
            binding,
            program,
            repo_root,
            &artifacts_dir,
            &logs_dir,
            timeout_seconds,
            &expected,
            build_profile,
            measurement_mode,
            sample_index,
            repetitions,
            report_dir,
        )?);
    }

    let representative_index = representative_sample_index(&samples);
    let representative = &samples[representative_index];
    let observed = aggregate_observed(&samples);
    let outcome =
        if samples.iter().all(|sample| sample.outcome == "passed") { "passed" } else { "failed" };
    let resource_usage = aggregate_resource_usage(&samples);
    let duration_seconds = resource_usage
        .get("elapsed_seconds")
        .and_then(Value::as_f64)
        .unwrap_or(representative.result.duration_seconds);
    let peak_rss_bytes = resource_usage.get("peak_rss_bytes").cloned().unwrap_or(Value::Null);
    let sample_reports = samples
        .iter()
        .map(|sample| sample_report(sample, report_dir))
        .collect::<Result<Vec<_>, _>>()?;
    let mut row = common_row(binding, program, raw_index);
    insert_str(&mut row, "command_display", command_display(&representative.command));
    insert_arr(&mut row, "command", representative.command.iter().map(|arg| json!(arg)).collect());
    insert_str(&mut row, "expected", expected);
    insert_str(&mut row, "observed", observed);
    insert_str(&mut row, "outcome", outcome);
    if samples.iter().any(|sample| sample.warmup.as_ref().is_some_and(|warmup| !warmup.valid)) {
        insert_str(
            &mut row,
            "measurement_failure_reason",
            "warm incremental measurement requested but warmup did not match the expected result",
        );
    }
    insert_optional_i32(&mut row, "exit_code", representative.result.exit_code);
    row.insert(
        "timed_out".to_string(),
        json!(samples.iter().any(|sample| sample.result.timed_out)),
    );
    row.insert("duration_seconds".to_string(), json!(round_seconds(duration_seconds)));
    row.insert("peak_rss_bytes".to_string(), peak_rss_bytes);
    row.insert("resource_usage".to_string(), resource_usage);
    if let Some(warmup) = representative.warmup.as_ref() {
        row.insert("incremental_warmup".to_string(), warmup_report(warmup, report_dir));
    }
    row.insert(
        "measurement_profile".to_string(),
        compile_measurement_profile(
            measurement_mode,
            build_profile,
            "measured",
            Some(if measurement_mode.requested_incremental() {
                "warmup compile completed before measured rustc -C incremental compile"
            } else {
                "CARGO_INCREMENTAL=0"
            }),
            representative.incremental_dir.as_deref(),
            Some(report_dir),
            representative.warmup.as_ref(),
        ),
    );
    row.insert("output_exists".to_string(), json!(representative.result.output_exists));
    insert_optional_u64(
        &mut row,
        "output_size_bytes",
        file_size_or_none(&representative.result.output_path),
    );
    insert_optional_str(
        &mut row,
        "output_sha256",
        file_sha256_or_none(&representative.result.output_path)?,
    );
    insert_optional_u64(&mut row, "stdout_bytes", Some(representative.result.stdout_bytes));
    insert_optional_u64(&mut row, "stderr_bytes", Some(representative.result.stderr_bytes));
    insert_str(
        &mut row,
        "output_path",
        relative_to_report(&representative.result.output_path, report_dir),
    );
    insert_str(
        &mut row,
        "stdout_path",
        relative_to_report(&representative.result.stdout_path, report_dir),
    );
    insert_str(
        &mut row,
        "stderr_path",
        relative_to_report(&representative.result.stderr_path, report_dir),
    );
    insert_str(&mut row, "stderr_excerpt", &representative.result.stderr_excerpt);
    insert_str(&mut row, "stderr_tail_excerpt", &representative.result.stderr_tail_excerpt);
    row.insert("transport".to_string(), aggregate_transport_summary(&samples));
    row.insert("requested_repetitions".to_string(), json!(repetitions));
    row.insert("sample_count".to_string(), json!(samples.len()));
    row.insert(
        "sample_aggregation".to_string(),
        sample_aggregation_report(&samples, representative.sample_index),
    );
    row.insert("samples".to_string(), Value::Array(sample_reports));
    if binding.id == "trust-cg" && outcome != "passed" {
        insert_str(&mut row, "trust_cg_exception_class", &representative.exception_class);
    }
    Ok(Value::Object(row))
}

fn run_slot_sample(
    binding: &SlotBinding,
    program: &Program,
    repo_root: &Path,
    artifacts_dir: &Path,
    logs_dir: &Path,
    timeout_seconds: u64,
    expected: &str,
    build_profile: BuildProfile,
    measurement_mode: CompileMeasurementMode,
    sample_index: usize,
    repetitions: usize,
    report_dir: &Path,
) -> Result<SlotRunSample, ProgramIndexError> {
    let artifact_name = sanitize_crate_name(&program.id);
    let output_path =
        sampled_path(&artifacts_dir.join(format!("{artifact_name}.o")), sample_index, repetitions);
    let stdout_path = sampled_path(
        &logs_dir.join(format!("{artifact_name}.stdout.log")),
        sample_index,
        repetitions,
    );
    let stderr_path = sampled_path(
        &logs_dir.join(format!("{artifact_name}.stderr.log")),
        sample_index,
        repetitions,
    );
    let incremental_dir = measurement_mode.requested_incremental().then(|| {
        incremental_dir_for_sample(report_dir, binding, program, sample_index, repetitions)
    });
    let warmup = if measurement_mode.uses_warmup() {
        Some(run_incremental_warmup(
            binding,
            program,
            repo_root,
            artifacts_dir,
            logs_dir,
            timeout_seconds,
            expected,
            incremental_dir
                .as_deref()
                .expect("warm incremental mode should have an incremental dir"),
            build_profile,
            sample_index,
            repetitions,
        )?)
    } else {
        None
    };
    remove_file_if_exists(&output_path)?;
    let command = build_command(
        binding,
        program,
        &output_path,
        false,
        incremental_dir.as_deref(),
        build_profile,
    )?;
    let result = execute_command(
        &command,
        repo_root,
        &compiler_env(&binding.id, measurement_mode),
        timeout_seconds,
        &stdout_path,
        &stderr_path,
        &output_path,
        binding.profile.mode,
    )?;
    let observed = result.status.clone();
    let exception_class = classify_trust_cg_exception(&result.stderr_excerpt, &observed);
    let warmup_valid = warmup.as_ref().map(|warmup| warmup.valid).unwrap_or(true);
    let outcome = if observed == expected && warmup_valid { "passed" } else { "failed" };
    Ok(SlotRunSample {
        sample_index,
        command,
        result,
        observed,
        outcome: outcome.to_string(),
        exception_class,
        warmup,
        incremental_dir,
    })
}

fn sample_report(sample: &SlotRunSample, report_dir: &Path) -> Result<Value, ProgramIndexError> {
    let mut object = Map::new();
    object.insert("sample_index".to_string(), json!(sample.sample_index));
    insert_str(&mut object, "command_display", command_display(&sample.command));
    insert_arr(&mut object, "command", sample.command.iter().map(|arg| json!(arg)).collect());
    insert_str(&mut object, "observed", &sample.observed);
    insert_str(&mut object, "outcome", &sample.outcome);
    insert_optional_i32(&mut object, "exit_code", sample.result.exit_code);
    object.insert("timed_out".to_string(), json!(sample.result.timed_out));
    object.insert(
        "duration_seconds".to_string(),
        json!(round_seconds(sample.result.duration_seconds)),
    );
    object.insert(
        "peak_rss_bytes".to_string(),
        sample.result.resource_usage["peak_rss_bytes"].clone(),
    );
    object.insert("resource_usage".to_string(), sample.result.resource_usage.clone());
    if let Some(incremental_dir) = sample.incremental_dir.as_deref() {
        insert_str(&mut object, "incremental_dir", relative_to_report(incremental_dir, report_dir));
    } else {
        object.insert("incremental_dir".to_string(), Value::Null);
    }
    if let Some(warmup) = sample.warmup.as_ref() {
        object.insert("incremental_warmup".to_string(), warmup_report(warmup, report_dir));
    }
    object.insert("output_exists".to_string(), json!(sample.result.output_exists));
    insert_optional_u64(
        &mut object,
        "output_size_bytes",
        file_size_or_none(&sample.result.output_path),
    );
    insert_optional_str(
        &mut object,
        "output_sha256",
        file_sha256_or_none(&sample.result.output_path)?,
    );
    insert_optional_u64(&mut object, "stdout_bytes", Some(sample.result.stdout_bytes));
    insert_optional_u64(&mut object, "stderr_bytes", Some(sample.result.stderr_bytes));
    insert_str(
        &mut object,
        "output_path",
        relative_to_report(&sample.result.output_path, report_dir),
    );
    insert_str(
        &mut object,
        "stdout_path",
        relative_to_report(&sample.result.stdout_path, report_dir),
    );
    insert_str(
        &mut object,
        "stderr_path",
        relative_to_report(&sample.result.stderr_path, report_dir),
    );
    insert_str(&mut object, "stderr_excerpt", &sample.result.stderr_excerpt);
    insert_str(&mut object, "stderr_tail_excerpt", &sample.result.stderr_tail_excerpt);
    object.insert("transport".to_string(), sample.result.transport.clone());
    Ok(Value::Object(object))
}

fn aggregate_observed(samples: &[SlotRunSample]) -> String {
    let Some(first) = samples.first().map(|sample| sample.observed.as_str()) else {
        return "not_run".to_string();
    };
    if samples.iter().all(|sample| sample.observed == first) {
        first.to_string()
    } else {
        "mixed".to_string()
    }
}

fn representative_sample_index(samples: &[SlotRunSample]) -> usize {
    if let Some((index, _)) =
        samples.iter().enumerate().find(|(_, sample)| sample.outcome != "passed")
    {
        return index;
    }
    let durations: Vec<f64> = samples.iter().map(|sample| sample.result.duration_seconds).collect();
    let median = median_f64(&durations).unwrap_or(0.0);
    samples
        .iter()
        .enumerate()
        .min_by(|(_, left), (_, right)| {
            let left_delta = (left.result.duration_seconds - median).abs();
            let right_delta = (right.result.duration_seconds - median).abs();
            left_delta.total_cmp(&right_delta)
        })
        .map(|(index, _)| index)
        .unwrap_or(0)
}

fn aggregate_resource_usage(samples: &[SlotRunSample]) -> Value {
    let elapsed_values: Vec<f64> =
        samples.iter().map(|sample| sample.result.duration_seconds).collect();
    let user_cpu_values = resource_f64_values(samples, "user_cpu_seconds");
    let system_cpu_values = resource_f64_values(samples, "system_cpu_seconds");
    let peak_rss_values = resource_i64_values(samples, "peak_rss_bytes");
    let peak_rss_raw_values = resource_i64_values(samples, "peak_rss_raw");
    let peak_rss_raw_unit = common_resource_str(samples, "peak_rss_raw_unit")
        .or_else(|| first_resource_str(samples, "peak_rss_raw_unit").map(str::to_string));
    let peak_rss_raw = peak_rss_raw_values.iter().copied().max();
    let peak_rss_bytes = match (peak_rss_raw, peak_rss_raw_unit.as_deref()) {
        (Some(raw), Some(unit)) => normalize_peak_rss_raw_with_unit(raw, unit)
            .or_else(|| peak_rss_values.iter().copied().max()),
        _ => peak_rss_values.iter().copied().max(),
    };
    json!({
        "source": common_resource_str(samples, "source")
            .or_else(|| first_resource_str(samples, "source").map(str::to_string)),
        "elapsed_seconds": median_f64(&elapsed_values).map(round_seconds),
        "user_cpu_seconds": median_f64(&user_cpu_values).map(round_seconds),
        "system_cpu_seconds": median_f64(&system_cpu_values).map(round_seconds),
        "peak_rss_bytes": peak_rss_bytes,
        "peak_rss_raw": peak_rss_raw,
        "peak_rss_raw_unit": peak_rss_raw_unit,
        "aggregation": {
            "sample_count": samples.len(),
            "elapsed_seconds_policy": "median",
            "cpu_seconds_policy": "median",
            "peak_rss_policy": "max",
        },
    })
}

fn aggregate_transport_summary(samples: &[SlotRunSample]) -> Value {
    let mut object = empty_transport_summary_object();
    let keys: Vec<String> = object.keys().cloned().collect();
    for sample in samples {
        for key in &keys {
            increment(&mut object, key, int_field(&sample.result.transport, key));
        }
    }
    object.insert("sample_count".to_string(), json!(samples.len()));
    Value::Object(object)
}

fn sample_aggregation_report(
    samples: &[SlotRunSample],
    representative_sample_index: usize,
) -> Value {
    let duration_values: Vec<f64> =
        samples.iter().map(|sample| sample.result.duration_seconds).collect();
    let user_cpu_values = resource_f64_values(samples, "user_cpu_seconds");
    let system_cpu_values = resource_f64_values(samples, "system_cpu_seconds");
    let cpu_values: Vec<f64> = samples
        .iter()
        .filter_map(|sample| {
            let usage = &sample.result.resource_usage;
            Some(
                usage.get("user_cpu_seconds")?.as_f64()?
                    + usage.get("system_cpu_seconds")?.as_f64()?,
            )
        })
        .collect();
    let peak_rss_values = resource_i64_values(samples, "peak_rss_bytes");
    let peak_rss_raw_values = resource_i64_values(samples, "peak_rss_raw");
    json!({
        "status": "aggregated",
        "sample_count": samples.len(),
        "representative_sample_index": representative_sample_index,
        "representative_policy": if samples.iter().any(|sample| sample.outcome != "passed") {
            "first_non_passing_sample"
        } else {
            "nearest_duration_median_sample"
        },
        "aggregate_field_policy": {
            "duration_seconds": "median",
            "resource_usage.elapsed_seconds": "median",
            "resource_usage.user_cpu_seconds": "median",
            "resource_usage.system_cpu_seconds": "median",
            "peak_rss_bytes": "max",
            "resource_usage.peak_rss_bytes": "max",
        },
        "duration_seconds": numeric_stats_f64(&duration_values),
        "user_cpu_seconds": numeric_stats_f64(&user_cpu_values),
        "system_cpu_seconds": numeric_stats_f64(&system_cpu_values),
        "cpu_seconds": numeric_stats_f64(&cpu_values),
        "peak_rss_bytes": numeric_stats_i64(&peak_rss_values),
        "peak_rss_raw": numeric_stats_i64(&peak_rss_raw_values),
        "outcomes": string_counts_from_values(samples.iter().map(|sample| sample.outcome.as_str())),
        "observed": string_counts_from_values(samples.iter().map(|sample| sample.observed.as_str())),
    })
}

fn insert_empty_sample_fields(
    row: &mut Map<String, Value>,
    repetitions: usize,
    status: &str,
    reason: &str,
) {
    row.insert("requested_repetitions".to_string(), json!(repetitions));
    row.insert("sample_count".to_string(), json!(0));
    row.insert("samples".to_string(), Value::Array(Vec::new()));
    row.insert(
        "sample_aggregation".to_string(),
        json!({
            "status": status,
            "reason": reason,
            "sample_count": 0,
            "requested_repetitions": repetitions,
            "duration_seconds": Value::Null,
            "peak_rss_bytes": Value::Null,
        }),
    );
}

fn planned_row(
    binding: &SlotBinding,
    program: &Program,
    report_dir: &Path,
    raw_index: &Value,
    build_profile: BuildProfile,
    measurement_mode: CompileMeasurementMode,
    repetitions: usize,
) -> Value {
    let mut row = common_row(binding, program, raw_index);
    let output_path = report_dir
        .join("artifacts")
        .join(&binding.id)
        .join(format!("{}.o", sanitize_crate_name(&program.id)));
    let incremental_dir = incremental_dir_for(report_dir, binding, program);
    let incremental_arg = if measurement_mode.requested_incremental() {
        Some(incremental_dir.as_path())
    } else {
        None
    };
    let command = if binding.binary.is_some() {
        build_command(binding, program, &output_path, false, incremental_arg, build_profile)
            .unwrap_or_default()
    } else {
        Vec::new()
    };
    insert_arr(&mut row, "command", command.iter().map(|arg| json!(arg)).collect());
    insert_str(&mut row, "command_display", command_display(&command));
    insert_str(&mut row, "expected", expected_status(&binding.id, program));
    insert_str(&mut row, "observed", "planned");
    insert_str(&mut row, "outcome", "planned");
    row.insert(
        "measurement_profile".to_string(),
        compile_measurement_profile(
            measurement_mode,
            build_profile,
            "planned",
            Some("dry-run planned command; no timing measured"),
            incremental_arg,
            Some(report_dir),
            None,
        ),
    );
    row.insert("output_sha256".to_string(), Value::Null);
    insert_empty_sample_fields(
        &mut row,
        repetitions,
        "planned",
        "dry-run planned command; no samples measured",
    );
    Value::Object(row)
}

fn skipped_row(
    binding: &SlotBinding,
    program: &Program,
    expected: &str,
    reason: &str,
    raw_index: &Value,
    build_profile: BuildProfile,
    measurement_mode: CompileMeasurementMode,
    repetitions: usize,
) -> Value {
    let mut row = common_row(binding, program, raw_index);
    insert_arr(&mut row, "command", Vec::new());
    insert_str(&mut row, "command_display", "");
    insert_str(&mut row, "expected", expected);
    insert_str(&mut row, "observed", "slot_skipped");
    insert_str(&mut row, "outcome", "skipped");
    insert_str(&mut row, "skip_reason", reason);
    row.insert("exit_code".to_string(), Value::Null);
    row.insert("timed_out".to_string(), json!(false));
    row.insert("duration_seconds".to_string(), json!(0.0));
    row.insert("peak_rss_bytes".to_string(), Value::Null);
    row.insert("resource_usage".to_string(), empty_resource_usage("not-run", 0.0));
    row.insert(
        "measurement_profile".to_string(),
        compile_measurement_profile(
            measurement_mode,
            build_profile,
            "not-run",
            Some(reason),
            None,
            None,
            None,
        ),
    );
    row.insert("output_exists".to_string(), json!(false));
    row.insert("output_size_bytes".to_string(), Value::Null);
    row.insert("output_sha256".to_string(), Value::Null);
    row.insert("stdout_bytes".to_string(), json!(0));
    row.insert("stderr_bytes".to_string(), json!(0));
    row.insert("transport".to_string(), empty_transport_summary());
    insert_empty_sample_fields(&mut row, repetitions, "not-run", reason);
    Value::Object(row)
}

fn run_incremental_warmup(
    binding: &SlotBinding,
    program: &Program,
    repo_root: &Path,
    artifacts_dir: &Path,
    logs_dir: &Path,
    timeout_seconds: u64,
    expected: &str,
    incremental_dir: &Path,
    build_profile: BuildProfile,
    sample_index: usize,
    repetitions: usize,
) -> Result<WarmupMeasurement, ProgramIndexError> {
    if incremental_dir.is_dir() {
        fs::remove_dir_all(incremental_dir).map_err(|error| {
            ProgramIndexError::new(format!(
                "clear incremental dir {}: {error}",
                incremental_dir.display()
            ))
        })?;
    }
    fs::create_dir_all(incremental_dir).map_err(|error| {
        ProgramIndexError::new(format!(
            "create incremental dir {}: {error}",
            incremental_dir.display()
        ))
    })?;

    let artifact_name = sanitize_crate_name(&program.id);
    let output_path = sampled_path(
        &artifacts_dir.join(format!("{artifact_name}.warmup.o")),
        sample_index,
        repetitions,
    );
    let stdout_path = sampled_path(
        &logs_dir.join(format!("{artifact_name}.warmup.stdout.log")),
        sample_index,
        repetitions,
    );
    let stderr_path = sampled_path(
        &logs_dir.join(format!("{artifact_name}.warmup.stderr.log")),
        sample_index,
        repetitions,
    );
    remove_file_if_exists(&output_path)?;
    let command =
        build_command(binding, program, &output_path, false, Some(incremental_dir), build_profile)?;
    let result = execute_command(
        &command,
        repo_root,
        &compiler_env(&binding.id, CompileMeasurementMode::WarmIncremental),
        timeout_seconds,
        &stdout_path,
        &stderr_path,
        &output_path,
        binding.profile.mode,
    )?;
    let valid = result.status == expected && !result.timed_out;
    Ok(WarmupMeasurement { command, result, expected: expected.to_string(), valid })
}

fn warmup_report(warmup: &WarmupMeasurement, report_dir: &Path) -> Value {
    json!({
        "status": if warmup.valid { "passed" } else { "failed" },
        "expected": warmup.expected.clone(),
        "observed": warmup.result.status.clone(),
        "valid_for_incremental_measurement": warmup.valid,
        "command": warmup.command.iter().map(|arg| json!(arg)).collect::<Vec<_>>(),
        "command_display": command_display(&warmup.command),
        "exit_code": warmup.result.exit_code,
        "timed_out": warmup.result.timed_out,
        "duration_seconds": round_seconds(warmup.result.duration_seconds),
        "peak_rss_bytes": warmup.result.resource_usage["peak_rss_bytes"].clone(),
        "resource_usage": warmup.result.resource_usage.clone(),
        "output_exists": warmup.result.output_exists,
        "output_path": relative_to_report(&warmup.result.output_path, report_dir),
        "stdout_path": relative_to_report(&warmup.result.stdout_path, report_dir),
        "stderr_path": relative_to_report(&warmup.result.stderr_path, report_dir),
        "stderr_excerpt": warmup.result.stderr_excerpt.clone(),
        "stderr_tail_excerpt": warmup.result.stderr_tail_excerpt.clone(),
    })
}

fn compile_measurement_profile(
    mode: CompileMeasurementMode,
    build_profile: BuildProfile,
    status: &str,
    note: Option<&str>,
    incremental_dir: Option<&Path>,
    report_dir: Option<&Path>,
    warmup: Option<&WarmupMeasurement>,
) -> Value {
    let measured = status == "measured";
    let warmup_valid = warmup.map(|warmup| warmup.valid).unwrap_or(false);
    let incremental = measured && mode.requested_incremental() && warmup_valid;
    let cache_state = match (status, mode, warmup_valid) {
        ("measured", CompileMeasurementMode::ColdArtifact, _) => "cold_artifact",
        ("measured", CompileMeasurementMode::WarmIncremental, true) => "warm_incremental",
        ("measured", CompileMeasurementMode::WarmIncremental, false) => "incremental_warmup_failed",
        ("planned", CompileMeasurementMode::ColdArtifact, _) => "planned_cold_artifact",
        ("planned", CompileMeasurementMode::WarmIncremental, _) => "planned_warm_incremental",
        ("not-run", _, _) => "not_run",
        _ => "unknown",
    };
    let incremental_dir = incremental_dir
        .and_then(|path| report_dir.map(|report_dir| relative_to_report(path, report_dir)));
    json!({
        "schema": COMPILE_MEASUREMENT_PROFILE_SCHEMA,
        "mode": mode.as_str(),
        "build_profile": build_profile.as_str(),
        "phase": "compile_artifact",
        "status": status,
        "cache_state": cache_state,
        "requested_incremental": mode.requested_incremental(),
        "incremental": incremental,
        "incremental_env": format!("CARGO_INCREMENTAL={}", mode.cargo_incremental_env()),
        "rustc_incremental_arg": incremental_dir.as_ref().map(|path| format!("-C incremental={path}")),
        "incremental_dir": incremental_dir,
        "warmup_required": mode.uses_warmup(),
        "warmup_valid": warmup.map(|warmup| warmup.valid),
        "timing_field": "duration_seconds",
        "resource_usage_field": "resource_usage",
        "runtime_measurements_separate": true,
        "note": note,
    })
}

fn common_row(binding: &SlotBinding, program: &Program, raw_index: &Value) -> Map<String, Value> {
    let mut row = Map::new();
    insert_str(&mut row, "program_id", &program.id);
    insert_str(&mut row, "pair_id", &program.pair_id);
    insert_str(&mut row, "variant", &program.variant);
    insert_str(&mut row, "suite", &program.suite);
    insert_str(&mut row, "source", &program.relative_path);
    insert_str(&mut row, "source_sha256", &program.source_sha256);
    insert_arr(
        &mut row,
        "obligations",
        program.obligations.iter().map(|value| json!(value)).collect(),
    );
    row.insert("metadata".to_string(), program.metadata.clone());
    insert_str(&mut row, "slot", &binding.id);
    insert_str(&mut row, "slot_mode", binding.profile.mode);
    match &binding.binary {
        Some(binary) => insert_str(&mut row, "slot_binary", binary),
        None => {
            row.insert("slot_binary".to_string(), Value::Null);
        }
    }
    insert_str(&mut row, "slot_binary_source", &binding.source);
    row.insert("slot_diagnostics".to_string(), slot_diagnostics(binding, raw_index));
    insert_str(&mut row, "canonical_binary", binding.profile.fallback_binary);
    row.insert("trust_owned".to_string(), json!(is_trust_owned_slot(&binding.id)));
    if is_trust_owned_slot(&binding.id) {
        insert_str(&mut row, "trust_owned_binary_name", binding.profile.fallback_binary);
    } else {
        row.insert("trust_owned_binary_name".to_string(), Value::Null);
    }
    match resolved_binary_name(binding) {
        Some(name) => insert_str(&mut row, "resolved_binary_name", name),
        None => {
            row.insert("resolved_binary_name".to_string(), Value::Null);
        }
    }
    row.insert("sysroot_path".to_string(), Value::Null);
    row.insert(
        "sysroot_query".to_string(),
        json!({
            "status": "not_probed",
            "reason": "Rust runner keeps program-index compilation side effects to selected benchmark commands",
        }),
    );
    row.insert("backward_pass".to_string(), backward_pass_row(raw_index, program, binding));
    row
}

fn expected_status(slot_id: &str, program: &Program) -> String {
    if slot_id == "trust-verify" {
        if program.variant == "good" {
            "verify_pass".to_string()
        } else {
            "verify_fail".to_string()
        }
    } else {
        "compile_pass".to_string()
    }
}

fn incremental_dir_for(report_dir: &Path, binding: &SlotBinding, program: &Program) -> PathBuf {
    report_dir.join("incremental").join(&binding.id).join(sanitize_crate_name(&program.id))
}

fn incremental_dir_for_sample(
    report_dir: &Path,
    binding: &SlotBinding,
    program: &Program,
    sample_index: usize,
    repetitions: usize,
) -> PathBuf {
    let base = incremental_dir_for(report_dir, binding, program);
    if repetitions == 1 { base } else { base.join(format!("sample-{sample_index}")) }
}

fn sampled_path(path: &Path, sample_index: usize, repetitions: usize) -> PathBuf {
    if repetitions == 1 {
        return path.to_path_buf();
    }
    let Some(file_name) = path.file_name().and_then(OsStr::to_str) else {
        return path.to_path_buf();
    };
    path.with_file_name(format!("{file_name}.sample-{sample_index}"))
}

fn remove_file_if_exists(path: &Path) -> Result<(), ProgramIndexError> {
    match fs::remove_file(path) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(ProgramIndexError::new(format!("remove {}: {error}", path.display()))),
    }
}

fn build_command(
    binding: &SlotBinding,
    program: &Program,
    output_path: &Path,
    link: bool,
    incremental_dir: Option<&Path>,
    build_profile: BuildProfile,
) -> Result<Vec<String>, ProgramIndexError> {
    let binary = binding
        .binary
        .as_ref()
        .ok_or_else(|| ProgramIndexError::new("cannot build command for missing binary"))?;
    let crate_name = sanitize_crate_name(&format!(
        "{}_{}{}",
        program.id,
        binding.id,
        if link { "_runtime" } else { "" }
    ));
    let mut command = vec![
        binary.clone(),
        "--edition=2021".to_string(),
        "--crate-type=bin".to_string(),
        "--crate-name".to_string(),
        crate_name,
        "--color=never".to_string(),
    ];
    command.extend(binding.profile.extra_args.iter().map(|arg| (*arg).to_string()));
    command.extend(build_profile.rustc_args().iter().map(|arg| (*arg).to_string()));
    if let Some(incremental_dir) = incremental_dir {
        command.push("-C".to_string());
        command.push(format!("incremental={}", incremental_dir.display()));
    }
    command.push(if link { "--emit=link" } else { "--emit=obj" }.to_string());
    command.push("-o".to_string());
    command.push(output_path.to_string_lossy().into_owned());
    command.push(program.path.to_string_lossy().into_owned());
    Ok(command)
}

fn execute_command(
    command: &[String],
    cwd: &Path,
    env_map: &BTreeMap<String, String>,
    timeout_seconds: u64,
    stdout_path: &Path,
    stderr_path: &Path,
    output_path: &Path,
    slot_mode: &str,
) -> Result<ExecutionResult, ProgramIndexError> {
    let stdout_file = open_capture_file(stdout_path)
        .map_err(|error| ProgramIndexError::new(format!("create stdout log: {error}")))?;
    let mut stderr_file = open_capture_file(stderr_path)
        .map_err(|error| ProgramIndexError::new(format!("create stderr log: {error}")))?;
    let child_stdout = stdout_file
        .try_clone()
        .map_err(|error| ProgramIndexError::new(format!("clone stdout log: {error}")))?;
    let child_stderr = stderr_file
        .try_clone()
        .map_err(|error| ProgramIndexError::new(format!("clone stderr log: {error}")))?;
    let run = run_command_with_resource_usage(
        command,
        cwd,
        env_map,
        timeout_seconds,
        child_stdout,
        child_stderr,
    );
    validate_capture_path_identity(&stdout_file, stdout_path)?;
    validate_capture_path_identity(&stderr_file, stderr_path)?;
    let stdout_bytes = capture_len(&stdout_file, stdout_path)?;
    let stderr_bytes = capture_len(&stderr_file, stderr_path)?;
    let stderr_text = read_capture_text_from_file(&mut stderr_file, stderr_path)?;
    let stderr_tail_text = read_tail_capture_text_from_file(&mut stderr_file, stderr_path)?;
    let transport = parse_transport_file_from_file(&mut stderr_file, stderr_path, cwd)?;
    let output_exists = output_path.is_file();
    let stderr_for_status = if stderr_tail_text == stderr_text {
        stderr_text.clone()
    } else {
        format!("{stderr_text}\n{stderr_tail_text}")
    };
    let status = classify_status(
        run.exit_code,
        run.timed_out,
        output_exists,
        &stderr_for_status,
        &transport,
        slot_mode,
    );
    Ok(ExecutionResult {
        status,
        exit_code: run.exit_code,
        duration_seconds: run.elapsed_seconds,
        timed_out: run.timed_out,
        stdout_path: stdout_path.to_path_buf(),
        stderr_path: stderr_path.to_path_buf(),
        stdout_bytes,
        stderr_bytes,
        output_path: output_path.to_path_buf(),
        output_exists,
        resource_usage: run.resource_usage,
        transport,
        stderr_excerpt: excerpt_text(&stderr_text),
        stderr_tail_excerpt: stderr_tail_text,
    })
}

fn run_command_with_resource_usage(
    command: &[String],
    cwd: &Path,
    env_map: &BTreeMap<String, String>,
    timeout_seconds: u64,
    stdout_file: File,
    stderr_file: File,
) -> CommandRun {
    #[cfg(unix)]
    {
        return run_command_wait4(command, cwd, env_map, timeout_seconds, stdout_file, stderr_file);
    }
    #[cfg(not(unix))]
    {
        return run_command_poll(command, cwd, env_map, timeout_seconds, stdout_file, stderr_file);
    }
}

#[cfg(unix)]
fn run_command_wait4(
    command: &[String],
    cwd: &Path,
    env_map: &BTreeMap<String, String>,
    timeout_seconds: u64,
    stdout_file: File,
    stderr_file: File,
) -> CommandRun {
    let started = Instant::now();
    let Some((program, args)) = command.split_first() else {
        return CommandRun {
            exit_code: Some(127),
            timed_out: false,
            elapsed_seconds: 0.0,
            resource_usage: empty_resource_usage("startup-error", 0.0),
        };
    };
    let stdout_monitor = match stdout_file.try_clone() {
        Ok(file) => file,
        Err(error) => return command_startup_error(started, error),
    };
    let stderr_monitor = match stderr_file.try_clone() {
        Ok(file) => file,
        Err(error) => return command_startup_error(started, error),
    };
    let mut child_command = Command::new(program);
    child_command
        .args(args)
        .current_dir(cwd)
        .env_clear()
        .envs(env_map)
        .stdout(Stdio::from(stdout_file))
        .stderr(Stdio::from(stderr_file));
    crate::bounded_process::configure_process_group(&mut child_command);

    let mut child = match child_command.spawn() {
        Ok(child) => child,
        Err(error) => {
            return CommandRun {
                exit_code: Some(127),
                timed_out: false,
                elapsed_seconds: round_seconds(started.elapsed().as_secs_f64()),
                resource_usage: json!({
                    "source": "startup-error",
                    "elapsed_seconds": round_seconds(started.elapsed().as_secs_f64()),
                    "error": error.to_string(),
                    "user_cpu_seconds": null,
                    "system_cpu_seconds": null,
                    "peak_rss_bytes": null,
                    "peak_rss_raw": null,
                    "peak_rss_raw_unit": null,
                }),
            };
        }
    };

    let child_pid = child.id();
    let pid = child_pid as libc::pid_t;
    let Some(deadline) = started.checked_add(Duration::from_secs(timeout_seconds)) else {
        let _ = crate::bounded_process::terminate_process_group(child_pid);
        let _ = child.kill();
        let _ = child.wait();
        let elapsed = round_seconds(started.elapsed().as_secs_f64());
        return CommandRun {
            exit_code: Some(127),
            timed_out: false,
            elapsed_seconds: elapsed,
            resource_usage: empty_resource_usage("invalid-timeout", elapsed),
        };
    };
    let mut child = Some(child);
    loop {
        // Observe exit without reaping so the numeric PID remains reserved as
        // this process group's PGID while every descendant is terminated.
        // Reaping first would allow a PID/PGID reuse race against an unrelated
        // process group.
        let observed = crate::bounded_process::exited_without_reaping(
            child.as_mut().expect("benchmark child remains owned until reap"),
        );
        let exited = match observed {
            Ok(exited) => exited,
            Err(_) => {
                let _ = crate::bounded_process::terminate_process_group(child_pid);
                let _ = child.as_mut().and_then(|child| child.kill().ok());
                let _ = child.as_mut().and_then(|child| child.wait().ok());
                drop(child.take());
                let elapsed = round_seconds(started.elapsed().as_secs_f64());
                return CommandRun {
                    exit_code: Some(127),
                    timed_out: false,
                    elapsed_seconds: elapsed,
                    resource_usage: empty_resource_usage("waitid-error", elapsed),
                };
            }
        };
        if exited {
            let _ = crate::bounded_process::terminate_process_group(child_pid);
            let mut status: libc::c_int = 0;
            let mut usage = std::mem::MaybeUninit::<libc::rusage>::zeroed();
            let waited = unsafe { libc::wait4(pid, &mut status, 0, usage.as_mut_ptr()) };
            drop(child.take());
            let elapsed = round_seconds(started.elapsed().as_secs_f64());
            if waited == pid {
                let usage = unsafe { usage.assume_init() };
                return CommandRun {
                    exit_code: wait_status_to_exit_code(status),
                    timed_out: false,
                    elapsed_seconds: elapsed,
                    resource_usage: resource_usage_from_rusage(&usage, elapsed),
                };
            }
            return CommandRun {
                exit_code: Some(127),
                timed_out: false,
                elapsed_seconds: elapsed,
                resource_usage: empty_resource_usage("wait4-error", elapsed),
            };
        }
        if capture_limit_exceeded(&stdout_monitor, &stderr_monitor) {
            let _ = crate::bounded_process::terminate_process_group(child_pid);
            let mut status: libc::c_int = 0;
            let mut usage = std::mem::MaybeUninit::<libc::rusage>::zeroed();
            let waited = unsafe { libc::wait4(pid, &mut status, 0, usage.as_mut_ptr()) };
            drop(child.take());
            truncate_capture(&stdout_monitor);
            truncate_capture(&stderr_monitor);
            let elapsed = round_seconds(started.elapsed().as_secs_f64());
            let base = if waited == pid {
                resource_usage_from_rusage(unsafe { &usage.assume_init() }, elapsed)
            } else {
                empty_resource_usage("output-limit", elapsed)
            };
            return CommandRun {
                exit_code: Some(127),
                timed_out: false,
                elapsed_seconds: elapsed,
                resource_usage: annotate_lifecycle_error(base, Some("output_limit_exceeded")),
            };
        }
        if Instant::now() >= deadline {
            let _ = crate::bounded_process::terminate_process_group(child_pid);
            let mut status: libc::c_int = 0;
            let mut usage = std::mem::MaybeUninit::<libc::rusage>::zeroed();
            let waited = unsafe { libc::wait4(pid, &mut status, 0, usage.as_mut_ptr()) };
            drop(child.take());
            let elapsed = round_seconds(started.elapsed().as_secs_f64());
            let resource_usage = if waited == pid {
                let usage = unsafe { usage.assume_init() };
                resource_usage_from_rusage(&usage, elapsed)
            } else {
                empty_resource_usage("timeout", elapsed)
            };
            return CommandRun {
                exit_code: if waited == pid { wait_status_to_exit_code(status) } else { None },
                timed_out: true,
                elapsed_seconds: elapsed,
                resource_usage,
            };
        }
        thread::sleep(Duration::from_millis(50));
    }
}

#[cfg(not(unix))]
fn run_command_poll(
    command: &[String],
    cwd: &Path,
    env_map: &BTreeMap<String, String>,
    timeout_seconds: u64,
    stdout_file: File,
    stderr_file: File,
) -> CommandRun {
    let started = Instant::now();
    let Some((program, args)) = command.split_first() else {
        return CommandRun {
            exit_code: Some(127),
            timed_out: false,
            elapsed_seconds: 0.0,
            resource_usage: empty_resource_usage("startup-error", 0.0),
        };
    };
    let stdout_monitor = match stdout_file.try_clone() {
        Ok(file) => file,
        Err(error) => return command_startup_error(started, error),
    };
    let stderr_monitor = match stderr_file.try_clone() {
        Ok(file) => file,
        Err(error) => return command_startup_error(started, error),
    };
    let mut child = match Command::new(program)
        .args(args)
        .current_dir(cwd)
        .env_clear()
        .envs(env_map)
        .stdout(Stdio::from(stdout_file))
        .stderr(Stdio::from(stderr_file))
        .spawn()
    {
        Ok(child) => child,
        Err(_) => {
            return CommandRun {
                exit_code: Some(127),
                timed_out: false,
                elapsed_seconds: round_seconds(started.elapsed().as_secs_f64()),
                resource_usage: empty_resource_usage(
                    "startup-error",
                    started.elapsed().as_secs_f64(),
                ),
            };
        }
    };
    let Some(deadline) = started.checked_add(Duration::from_secs(timeout_seconds)) else {
        let _ = child.kill();
        let _ = child.wait();
        let elapsed = round_seconds(started.elapsed().as_secs_f64());
        return CommandRun {
            exit_code: Some(127),
            timed_out: false,
            elapsed_seconds: elapsed,
            resource_usage: non_unix_process_usage("invalid-timeout", elapsed),
        };
    };
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let elapsed = round_seconds(started.elapsed().as_secs_f64());
                return CommandRun {
                    exit_code: status.code(),
                    timed_out: false,
                    elapsed_seconds: elapsed,
                    resource_usage: non_unix_process_usage("std", elapsed),
                };
            }
            Ok(None) if capture_limit_exceeded(&stdout_monitor, &stderr_monitor) => {
                let _ = child.kill();
                let _ = child.wait();
                truncate_capture(&stdout_monitor);
                truncate_capture(&stderr_monitor);
                let elapsed = round_seconds(started.elapsed().as_secs_f64());
                return CommandRun {
                    exit_code: Some(127),
                    timed_out: false,
                    elapsed_seconds: elapsed,
                    resource_usage: annotate_lifecycle_error(
                        non_unix_process_usage("output-limit", elapsed),
                        Some("output_limit_exceeded"),
                    ),
                };
            }
            Ok(None) if Instant::now() >= deadline => {
                let _ = child.kill();
                let status = child.wait().ok();
                let elapsed = round_seconds(started.elapsed().as_secs_f64());
                return CommandRun {
                    exit_code: status.and_then(|status| status.code()),
                    timed_out: true,
                    elapsed_seconds: elapsed,
                    resource_usage: non_unix_process_usage("std", elapsed),
                };
            }
            Ok(None) => thread::sleep(Duration::from_millis(50)),
            Err(error) => {
                // A failed status query must not abandon a live process.
                let _ = child.kill();
                let _ = child.wait();
                let elapsed = round_seconds(started.elapsed().as_secs_f64());
                let mut usage = non_unix_process_usage("std-error", elapsed);
                if let Some(object) = usage.as_object_mut() {
                    object.insert("error".to_string(), Value::String(error.to_string()));
                }
                return CommandRun {
                    exit_code: Some(127),
                    timed_out: false,
                    elapsed_seconds: elapsed,
                    resource_usage: usage,
                };
            }
        }
    }
}

#[cfg(not(unix))]
fn non_unix_process_usage(source: &str, elapsed_seconds: f64) -> Value {
    let mut usage = empty_resource_usage(source, elapsed_seconds);
    if let Some(object) = usage.as_object_mut() {
        object.insert("process_containment".to_string(), json!("leader_only"));
        object.insert("descendant_containment".to_string(), json!(false));
        object.insert(
            "containment_note".to_string(),
            json!(
                "the command leader is deadline/output bounded and reaped; full descendant containment requires platform job-object support"
            ),
        );
    }
    usage
}

fn command_startup_error(started: Instant, error: std::io::Error) -> CommandRun {
    let elapsed = round_seconds(started.elapsed().as_secs_f64());
    CommandRun {
        exit_code: Some(127),
        timed_out: false,
        elapsed_seconds: elapsed,
        resource_usage: json!({
            "source": "startup-error",
            "elapsed_seconds": elapsed,
            "error": error.to_string(),
            "user_cpu_seconds": null,
            "system_cpu_seconds": null,
            "peak_rss_bytes": null,
            "peak_rss_raw": null,
            "peak_rss_raw_unit": null,
        }),
    }
}

fn capture_limit_exceeded(stdout: &File, stderr: &File) -> bool {
    [stdout, stderr]
        .into_iter()
        .any(|file| file.metadata().map_or(true, |metadata| metadata.len() > MAX_COMMAND_LOG_BYTES))
}

fn truncate_capture(file: &File) {
    if file.metadata().is_ok_and(|metadata| metadata.len() > MAX_COMMAND_LOG_BYTES) {
        let _ = file.set_len(MAX_COMMAND_LOG_BYTES);
    }
}

fn annotate_lifecycle_error(mut usage: Value, error: Option<&str>) -> Value {
    if let (Some(object), Some(error)) = (usage.as_object_mut(), error) {
        object.insert("lifecycle_error".to_string(), Value::String(error.to_string()));
    }
    usage
}

#[cfg(unix)]
fn wait_status_to_exit_code(status: libc::c_int) -> Option<i32> {
    if libc::WIFEXITED(status) {
        Some(libc::WEXITSTATUS(status))
    } else if libc::WIFSIGNALED(status) {
        Some(-libc::WTERMSIG(status))
    } else {
        None
    }
}

#[cfg(unix)]
fn resource_usage_from_rusage(usage: &libc::rusage, elapsed_seconds: f64) -> Value {
    let peak_rss_raw = usage.ru_maxrss as i64;
    json!({
        "source": "os.wait4",
        "elapsed_seconds": elapsed_seconds,
        "user_cpu_seconds": timeval_seconds(usage.ru_utime),
        "system_cpu_seconds": timeval_seconds(usage.ru_stime),
        "peak_rss_bytes": normalize_ru_maxrss(peak_rss_raw),
        "peak_rss_raw": peak_rss_raw,
        "peak_rss_raw_unit": ru_maxrss_unit(),
    })
}

#[cfg(unix)]
fn timeval_seconds(value: libc::timeval) -> f64 {
    round_seconds(value.tv_sec as f64 + (value.tv_usec as f64 / 1_000_000.0))
}

fn empty_resource_usage(source: &str, elapsed_seconds: f64) -> Value {
    json!({
        "source": source,
        "elapsed_seconds": round_seconds(elapsed_seconds),
        "user_cpu_seconds": null,
        "system_cpu_seconds": null,
        "peak_rss_bytes": null,
        "peak_rss_raw": null,
        "peak_rss_raw_unit": null,
    })
}

fn normalize_ru_maxrss(value: i64) -> i64 {
    if cfg!(target_os = "macos") { value } else { value * 1024 }
}

fn ru_maxrss_unit() -> &'static str {
    if cfg!(target_os = "macos") { "bytes" } else { "kilobytes" }
}

fn compiler_env(
    _slot_id: &str,
    measurement_mode: CompileMeasurementMode,
) -> BTreeMap<String, String> {
    let mut env_map: BTreeMap<String, String> = env::vars().collect();
    for key in [
        "RUSTFLAGS",
        "RUSTFLAGS_BOOTSTRAP",
        "RUSTFLAGS_NOT_BOOTSTRAP",
        "MAGIC_EXTRA_RUSTFLAGS",
        "CARGO_ENCODED_RUSTFLAGS",
    ] {
        env_map.remove(key);
    }
    env_map.insert(
        "CARGO_INCREMENTAL".to_string(),
        measurement_mode.cargo_incremental_env().to_string(),
    );
    env_map.insert("CARGO_TERM_COLOR".to_string(), "never".to_string());
    env_map.insert("RUST_BACKTRACE".to_string(), "0".to_string());
    // Verification mode and scope are carried by tracked rustc options.  The
    // retired TRUST_VERIFY_POLICY label was ignored by current trustc and made
    // the benchmark transcript imply a policy input that no longer existed.
    scrub_retired_compiler_policy_env(&mut env_map);
    env_map
}

fn scrub_retired_compiler_policy_env(env_map: &mut BTreeMap<String, String>) {
    env_map.remove("TRUST_VERIFY");
    env_map.remove("TRUST_VERIFY_POLICY");
    env_map.remove("TRUST_DUMP_ONLY");
}

fn runtime_env() -> BTreeMap<String, String> {
    let mut env_map: BTreeMap<String, String> = env::vars().collect();
    env_map.insert("RUST_BACKTRACE".to_string(), "0".to_string());
    env_map
}

fn classify_status(
    exit_code: Option<i32>,
    timed_out: bool,
    output_exists: bool,
    stderr_text: &str,
    transport: &Value,
    slot_mode: &str,
) -> String {
    if timed_out {
        return "timeout".to_string();
    }
    if slot_mode == "verify" {
        let failed = int_field(transport, "failed") + int_field(transport, "crate_total_failed");
        let unknown = int_field(transport, "unknown");
        let runtime_checked = int_field(transport, "runtime_checked");
        let total =
            int_field(transport, "total").max(int_field(transport, "crate_total_obligations"));
        if failed > 0 || looks_like_failed_verification(stderr_text, exit_code) {
            return "verify_fail".to_string();
        }
        if !matches!(exit_code, Some(0) | None) {
            return "tool_failure".to_string();
        }
        if total > 0 && unknown == 0 && runtime_checked == 0 {
            return "verify_pass".to_string();
        }
        if total > 0 {
            return "verify_inconclusive".to_string();
        }
        return "verify_no_transport".to_string();
    }
    if exit_code == Some(0) && output_exists {
        "compile_pass".to_string()
    } else if exit_code == Some(0) {
        "missing_output".to_string()
    } else {
        "compile_fail".to_string()
    }
}

fn looks_like_failed_verification(stderr_text: &str, exit_code: Option<i32>) -> bool {
    let lowered = stderr_text.to_ascii_lowercase();
    [
        "trust full verification failed",
        "failed obligations are not permitted",
        "native full verifier status",
        "outcome\":\"failed",
        " failed obligation",
        "verification failed",
        "[failed]",
    ]
    .iter()
    .any(|marker| lowered.contains(marker))
        || (!matches!(exit_code, Some(0) | None) && lowered.contains("trust-verify"))
}

fn parse_transport_file_from_file(
    file: &mut File,
    path: &Path,
    materialization_root: &Path,
) -> Result<Value, ProgramIndexError> {
    file.seek(SeekFrom::Start(0)).map_err(|error| {
        ProgramIndexError::new(format!("seek transport {}: {error}", path.display()))
    })?;
    let reader = BufReader::new(file);
    let mut summary = empty_transport_summary_object();
    for line in reader.lines() {
        let line = line.map_err(|error| {
            ProgramIndexError::new(format!("read transport {}: {error}", path.display()))
        })?;
        parse_transport_line(line.trim(), &mut summary, materialization_root);
    }
    Ok(Value::Object(summary))
}

fn parse_transport_line(
    stripped: &str,
    summary: &mut Map<String, Value>,
    materialization_root: &Path,
) {
    let Some(payload) = stripped.strip_prefix(TRANSPORT_PREFIX) else {
        return;
    };
    let Ok(message) = serde_json::from_str::<Value>(payload) else {
        increment(summary, "malformed_lines", 1);
        return;
    };
    match message["type"].as_str() {
        Some("function_result") => {
            increment(summary, "function_results", 1);
            for key in ["proved", "failed", "unknown", "runtime_checked", "total"] {
                increment(summary, key, int_field(&message, key));
            }
            summarize_obligation_results(&message, summary, materialization_root);
        }
        Some("crate_summary") => {
            increment(summary, "crate_summaries", 1);
            increment(summary, "crate_total_obligations", int_field(&message, "total_obligations"));
            increment(summary, "crate_total_failed", int_field(&message, "total_failed"));
        }
        _ => {}
    }
}

fn summarize_obligation_results(
    message: &Value,
    summary: &mut Map<String, Value>,
    materialization_root: &Path,
) {
    let Some(results) = message.get("results").and_then(Value::as_array) else {
        return;
    };
    increment(summary, "obligation_results", results.len() as i64);
    for result in results {
        let outcome = result.get("outcome").and_then(Value::as_str);
        match outcome {
            Some("failed") => increment(summary, "failed_results", 1),
            Some("proved") => increment(summary, "proved_results", 1),
            Some("unknown") | Some("timeout") => increment(summary, "unknown_results", 1),
            Some("runtime_checked") => increment(summary, "runtime_checked_results", 1),
            _ => {}
        }
        if nonempty_json_payload(result.get("counterexample")) {
            increment(summary, "counterexamples", 1);
        }
        if nonempty_json_payload(result.get("counterexample_model")) {
            increment(summary, "counterexample_models", 1);
        }
        if ["repair_candidate", "repair", "suggestion", "fix"]
            .iter()
            .any(|key| nonempty_json_payload(result.get(*key)))
        {
            increment(summary, "repair_candidates", 1);
        }
        match serde_json::from_value::<trust_types::TransportObligationResult>(result.clone()) {
            Ok(typed) => {
                increment(summary, "typed_transport_results", 1);
                let native_advertised = typed.native_trust_ir.is_some();
                let native_present =
                    typed.native_trust_ir.as_ref().is_some_and(|native| native.present);
                let proof_present = typed.proof_evidence.is_some();
                if native_present {
                    increment(summary, "native_trust_ir_results", 1);
                }
                if proof_present {
                    increment(summary, "proof_evidence_results", 1);
                }
                // Presence of a typed native/proof envelope advertises the
                // direct lane even when `present=false`; that row must engage
                // the completeness gate and fail instead of being mistaken
                // for untouched legacy transport.
                if native_advertised || proof_present {
                    increment(summary, "native_evidence_results", 1);
                }
                if outcome == Some("proved")
                    && crate::report::transport_obligation_has_publishable_native_proof(
                        &typed,
                        materialization_root,
                    )
                {
                    increment(summary, "publishable_native_proof_results", 1);
                }
            }
            Err(_) => {
                increment(summary, "malformed_typed_transport_results", 1);
                // A malformed row that nevertheless names native fields is an
                // attempted direct-lane row, not legacy absence. Engage the
                // fail-closed native gate even though typed validation failed.
                if nonempty_json_payload(result.get("native_trust_ir"))
                    || nonempty_json_payload(result.get("proof_evidence"))
                {
                    increment(summary, "native_evidence_results", 1);
                }
            }
        }

        let diagnostic_text = serde_json::to_string(result).unwrap_or_default();
        if let Some(category) = unsupported_frontend_lowering_category(&diagnostic_text) {
            increment(summary, "unsupported_frontend_lowering_results", 1);
            increment(summary, category.transport_counter(), 1);
        }
    }
}

fn nonempty_json_payload(value: Option<&Value>) -> bool {
    match value {
        Some(Value::Null) | None => false,
        Some(Value::String(value)) => !value.trim().is_empty(),
        Some(Value::Array(values)) => !values.is_empty(),
        Some(Value::Object(values)) => !values.is_empty(),
        Some(_) => true,
    }
}

fn empty_transport_summary() -> Value {
    Value::Object(empty_transport_summary_object())
}

fn empty_transport_summary_object() -> Map<String, Value> {
    [
        "function_results",
        "crate_summaries",
        "malformed_lines",
        "proved",
        "failed",
        "unknown",
        "runtime_checked",
        "total",
        "crate_total_obligations",
        "crate_total_failed",
        "obligation_results",
        "proved_results",
        "failed_results",
        "unknown_results",
        "runtime_checked_results",
        "counterexamples",
        "counterexample_models",
        "repair_candidates",
        "native_trust_ir_results",
        "proof_evidence_results",
        "native_evidence_results",
        "typed_transport_results",
        "malformed_typed_transport_results",
        "publishable_native_proof_results",
        "unsupported_frontend_lowering_results",
        "unsupported_mir_results",
        "unsupported_thir_results",
        "unsupported_trust_ir_results",
    ]
    .into_iter()
    .map(|key| (key.to_string(), json!(0)))
    .collect()
}

fn increment(object: &mut Map<String, Value>, key: &str, amount: i64) {
    let current = object.get(key).and_then(Value::as_i64).unwrap_or(0);
    object.insert(key.to_string(), json!(current + amount));
}

fn int_field(value: &Value, key: &str) -> i64 {
    value.get(key).and_then(Value::as_i64).unwrap_or(0)
}

fn open_capture_file(path: &Path) -> std::io::Result<File> {
    let mut options = OpenOptions::new();
    // The parent authenticates and parses the exact descriptor after the child
    // finishes, so it must remain readable as well as writable.
    options.read(true).write(true).create(true).truncate(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;

        options.mode(0o600).custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC);
    }
    let file = options.open(path)?;
    if !file.metadata()?.is_file() {
        return Err(std::io::Error::other(format!(
            "capture is not a regular file: {}",
            path.display()
        )));
    }
    Ok(file)
}

fn validate_capture_path_identity(file: &File, path: &Path) -> Result<(), ProgramIndexError> {
    let opened = file.metadata().map_err(|error| {
        ProgramIndexError::new(format!("inspect opened capture {}: {error}", path.display()))
    })?;
    let current = fs::symlink_metadata(path).map_err(|error| {
        ProgramIndexError::new(format!("reinspect capture path {}: {error}", path.display()))
    })?;
    let same = !current.file_type().is_symlink()
        && current.is_file()
        && same_capture_identity(&opened, &current);
    if !same {
        return Err(ProgramIndexError::new(format!(
            "capture path changed while its command ran: {}",
            path.display()
        )));
    }
    Ok(())
}

#[cfg(unix)]
fn same_capture_identity(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    use std::os::unix::fs::MetadataExt as _;

    left.dev() == right.dev() && left.ino() == right.ino()
}

#[cfg(not(unix))]
fn same_capture_identity(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    left.is_file() && right.is_file() && left.len() == right.len()
}

fn capture_len(file: &File, path: &Path) -> Result<u64, ProgramIndexError> {
    let len = file
        .metadata()
        .map_err(|error| {
            ProgramIndexError::new(format!("read capture metadata {}: {error}", path.display()))
        })?
        .len();
    if len > MAX_COMMAND_LOG_BYTES {
        return Err(ProgramIndexError::new(format!(
            "capture {} exceeded the {MAX_COMMAND_LOG_BYTES}-byte retention bound",
            path.display()
        )));
    }
    Ok(len)
}

fn capture_sha256(file: &mut File, path: &Path) -> Result<String, ProgramIndexError> {
    let expected = capture_len(file, path)?;
    file.seek(SeekFrom::Start(0)).map_err(|error| {
        ProgramIndexError::new(format!("seek capture {} for hashing: {error}", path.display()))
    })?;
    let mut hasher = Sha256::new();
    let copied =
        std::io::copy(&mut file.take(MAX_COMMAND_LOG_BYTES + 1), &mut hasher).map_err(|error| {
            ProgramIndexError::new(format!("hash capture {}: {error}", path.display()))
        })?;
    if copied != expected {
        return Err(ProgramIndexError::new(format!(
            "capture {} changed while it was hashed",
            path.display()
        )));
    }
    Ok(trust_types::digest::lowercase_hex(hasher.finalize().as_slice()))
}

#[cfg(test)]
fn read_capture_text(path: &Path) -> Result<String, ProgramIndexError> {
    let mut file = File::open(path).map_err(|error| {
        ProgramIndexError::new(format!("read capture {}: {error}", path.display()))
    })?;
    read_capture_text_from_file(&mut file, path)
}

fn read_capture_text_from_file(file: &mut File, path: &Path) -> Result<String, ProgramIndexError> {
    file.seek(SeekFrom::Start(0)).map_err(|error| {
        ProgramIndexError::new(format!("seek capture {}: {error}", path.display()))
    })?;
    let mut buffer = Vec::new();
    let mut limited = std::io::Read::by_ref(file).take(MAX_CAPTURE_BYTES as u64);
    limited.read_to_end(&mut buffer).map_err(|error| {
        ProgramIndexError::new(format!("read capture {}: {error}", path.display()))
    })?;
    String::from_utf8(buffer).map_err(|_| {
        ProgramIndexError::new(format!("capture {} was not valid UTF-8", path.display()))
    })
}

fn read_tail_capture_text_from_file(
    file: &mut File,
    path: &Path,
) -> Result<String, ProgramIndexError> {
    let len = file
        .metadata()
        .map_err(|error| {
            ProgramIndexError::new(format!("read capture metadata {}: {error}", path.display()))
        })?
        .len();
    let tail_len = EXCERPT_BYTES.min(len as usize);
    if len > tail_len as u64 {
        file.seek(SeekFrom::End(-(tail_len as i64))).map_err(|error| {
            ProgramIndexError::new(format!("seek capture tail {}: {error}", path.display()))
        })?;
    } else {
        file.seek(SeekFrom::Start(0)).map_err(|error| {
            ProgramIndexError::new(format!("seek capture start {}: {error}", path.display()))
        })?;
    }
    let mut buffer = Vec::with_capacity(tail_len);
    file.read_to_end(&mut buffer).map_err(|error| {
        ProgramIndexError::new(format!("read capture tail {}: {error}", path.display()))
    })?;
    let text = String::from_utf8_lossy(&buffer).into_owned();
    if len > tail_len as u64 {
        Ok(format!("[truncated stderr tail excerpt to last {tail_len} bytes]\n{text}"))
    } else {
        Ok(text)
    }
}

fn excerpt_text(text: &str) -> String {
    let bytes = text.as_bytes();
    if bytes.len() <= EXCERPT_BYTES {
        return text.to_string();
    }
    format!(
        "{}\n[truncated stderr excerpt at {EXCERPT_BYTES} bytes]",
        String::from_utf8_lossy(&bytes[..EXCERPT_BYTES])
    )
}

fn tail_excerpt_text(text: &str) -> String {
    let bytes = text.as_bytes();
    if bytes.len() <= EXCERPT_BYTES {
        return text.to_string();
    }
    format!(
        "[truncated stderr tail excerpt to last {EXCERPT_BYTES} bytes]\n{}",
        String::from_utf8_lossy(&bytes[bytes.len() - EXCERPT_BYTES..])
    )
}

fn classify_trust_cg_exception(stderr_excerpt: &str, observed: &str) -> String {
    let lowered = stderr_excerpt.to_ascii_lowercase();
    if observed == "missing_output" {
        return "pipeline_emit_failure".to_string();
    }
    if observed == "slot_skipped"
        || [
            "unknown codegen backend",
            "could not find codegen backend",
            "failed to load codegen backend",
            "rustc_codegen_trust_cg",
            "codegen-backend=trust_cg",
        ]
        .iter()
        .any(|marker| lowered.contains(marker))
    {
        return "missing_backend".to_string();
    }
    if [
        "trust_cg pipeline failed",
        "failed to emit object",
        "lowering failed",
        "not implemented",
        "unsupported",
    ]
    .iter()
    .any(|marker| lowered.contains(marker))
    {
        return "pipeline_emit_failure".to_string();
    }
    if ["linking with", "undefined symbols", "eh_personality", "panic_unwind"]
        .iter()
        .any(|marker| lowered.contains(marker))
    {
        return "link_or_runtime_surface".to_string();
    }
    "unknown_trust_cg_failure".to_string()
}

fn apply_trust_cg_mode(rows: &mut [Value], trust_cg_mode: &str) {
    for row in rows {
        if value_str(row, "slot") != Some("trust-cg") || value_str(row, "outcome") != Some("failed")
        {
            continue;
        }
        set_default(row, "pre_exception_outcome", row["outcome"].clone());
        set_str(row, "trust_cg_mode", trust_cg_mode);
        if trust_cg_mode == "report" {
            set_str(row, "outcome", "excepted");
            let class =
                value_str(row, "trust_cg_exception_class").unwrap_or("unknown_trust_cg_failure");
            set_str(row, "expected_known_gap_id", format!("trust_cg-{class}"));
            set_str(
                row,
                "expected_known_gap_reason",
                "trust-cg is experimental and report-only in the default benchmark mode",
            );
        }
    }
}

fn expected_known_gaps(index: &Value) -> Result<Vec<Value>, ProgramIndexError> {
    let Some(raw_gaps) = index.get("expected_known_gaps") else {
        return Ok(Vec::new());
    };
    let gaps = raw_gaps
        .as_array()
        .ok_or_else(|| ProgramIndexError::new("expected_known_gaps must be a list"))?;
    for gap in gaps {
        validate_expected_known_gap(gap)?;
    }
    Ok(gaps.clone())
}

fn validate_expected_known_gap(gap: &Value) -> Result<(), ProgramIndexError> {
    let object = gap
        .as_object()
        .ok_or_else(|| ProgramIndexError::new("expected_known_gaps entries must be objects"))?;
    let gap_id = object.get("id").and_then(Value::as_str).unwrap_or("<unknown>");
    match object.get("reason").and_then(Value::as_str) {
        Some(reason) if !reason.trim().is_empty() => {}
        _ => {
            return Err(ProgramIndexError::new(format!(
                "expected_known_gaps {gap_id}: entries must declare a non-empty reason"
            )));
        }
    }
    if object.get("slot").and_then(Value::as_str) == Some("trust-cg")
        || object
            .get("slots")
            .and_then(Value::as_array)
            .is_some_and(|slots| slots.iter().any(|slot| slot.as_str() == Some("trust-cg")))
    {
        return Err(ProgramIndexError::new(format!(
            "expected_known_gaps {gap_id}: trust_cg gaps are modeled by trust_cg_mode"
        )));
    }
    if !object.contains_key("observed") {
        return Err(ProgramIndexError::new(format!(
            "expected_known_gaps {gap_id}: non-trust-cg gaps must declare observed statuses"
        )));
    }
    let observed = string_list(&gap["observed"], "observed")?;
    if observed.iter().any(|value| value == "verify_pass") {
        return Err(ProgramIndexError::new(format!(
            "expected_known_gaps {gap_id}: verify_pass must remain a regression, not an expected known gap"
        )));
    }
    if !(object.contains_key("stderr_contains_any")
        || object.contains_key("stderr_contains_all")
        || object.contains_key("transport_min"))
    {
        return Err(ProgramIndexError::new(format!(
            "expected_known_gaps {gap_id}: non-trust-cg gaps require stderr_contains_any, stderr_contains_all, or transport_min"
        )));
    }
    if let Some(value) = object.get("stderr_contains_any") {
        let _ = string_list(value, "stderr_contains_any")?;
    }
    if let Some(value) = object.get("stderr_contains_all") {
        let _ = string_list(value, "stderr_contains_all")?;
    }
    if let Some(value) = object.get("transport_min") {
        validate_transport_minimums(value)?;
    }
    Ok(())
}

fn validate_expected_known_gap_hooks(
    index: &Value,
    gaps: &[Value],
) -> Result<(), ProgramIndexError> {
    let mut gap_ids = BTreeSet::new();
    for gap in gaps {
        let id =
            gap.get("id").and_then(Value::as_str).filter(|id| !id.is_empty()).ok_or_else(|| {
                ProgramIndexError::new("expected_known_gaps entries must declare id")
            })?;
        if !gap_ids.insert(id.to_string()) {
            return Err(ProgramIndexError::new(format!("duplicate expected_known_gaps id: {id}")));
        }
    }
    if gap_ids.is_empty() {
        return Ok(());
    }

    let hooks = index
        .get("expectation_model")
        .and_then(|value| value.get("program_exception_hooks"))
        .and_then(Value::as_object)
        .ok_or_else(|| {
            ProgramIndexError::new(
                "expected_known_gaps require expectation_model.program_exception_hooks",
            )
        })?;
    let program_ids: BTreeSet<String> = index
        .get("programs")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(|program| program.get("id").and_then(Value::as_str))
        .map(str::to_string)
        .collect();
    let mut referenced = BTreeSet::new();
    for (program_key, hook_values) in hooks {
        if program_key != "all.good"
            && program_key != "all.flawed"
            && !program_ids.contains(program_key)
        {
            return Err(ProgramIndexError::new(format!(
                "program_exception_hooks {program_key}: selector must be a program id or all.good/all.flawed"
            )));
        }
        let hooks = string_list(hook_values, "program_exception_hooks")?;
        for hook in hooks {
            if hook == "trust_cg_exception_model" {
                continue;
            }
            if !gap_ids.contains(&hook) {
                return Err(ProgramIndexError::new(format!(
                    "program_exception_hooks {program_key} references unknown gap id {hook}"
                )));
            }
            referenced.insert(hook);
        }
    }
    let missing: Vec<String> = gap_ids.difference(&referenced).cloned().collect();
    if missing.is_empty() {
        Ok(())
    } else {
        Err(ProgramIndexError::new(format!(
            "expected_known_gaps not referenced by program_exception_hooks: {}",
            missing.join(", ")
        )))
    }
}

fn expected_gap_hooks(
    index: &Value,
    gaps: &[Value],
) -> Result<BTreeMap<String, BTreeSet<String>>, ProgramIndexError> {
    if gaps.is_empty() {
        return Ok(BTreeMap::new());
    }
    validate_expected_known_gap_hooks(index, gaps)?;
    let hooks = index
        .get("expectation_model")
        .and_then(|value| value.get("program_exception_hooks"))
        .and_then(Value::as_object)
        .ok_or_else(|| {
            ProgramIndexError::new(
                "expected_known_gaps require expectation_model.program_exception_hooks",
            )
        })?;
    let mut parsed = BTreeMap::new();
    for (selector, hook_values) in hooks {
        let gap_ids = string_list(hook_values, "program_exception_hooks")?
            .into_iter()
            .filter(|gap_id| gap_id != "trust_cg_exception_model")
            .collect::<BTreeSet<_>>();
        if !gap_ids.is_empty() {
            parsed.insert(selector.clone(), gap_ids);
        }
    }
    Ok(parsed)
}

fn allowed_expected_gap_ids_for_row(
    row: &Value,
    hooks: &BTreeMap<String, BTreeSet<String>>,
) -> BTreeSet<String> {
    let mut allowed = BTreeSet::new();
    if let Some(program_id) = value_str(row, "program_id") {
        if let Some(ids) = hooks.get(program_id) {
            allowed.extend(ids.iter().cloned());
        }
    }
    match value_str(row, "variant") {
        Some("good") => {
            if let Some(ids) = hooks.get("all.good") {
                allowed.extend(ids.iter().cloned());
            }
        }
        Some("flawed") => {
            if let Some(ids) = hooks.get("all.flawed") {
                allowed.extend(ids.iter().cloned());
            }
        }
        _ => {}
    }
    allowed
}

fn apply_expected_known_gaps(
    rows: &mut [Value],
    gaps: &[Value],
    hooks: &BTreeMap<String, BTreeSet<String>>,
) {
    for row in rows {
        if value_str(row, "slot") == Some("trust-cg") || value_str(row, "outcome") != Some("failed")
        {
            continue;
        }
        let allowed_gap_ids = allowed_expected_gap_ids_for_row(row, hooks);
        if allowed_gap_ids.is_empty() {
            continue;
        }
        for gap in gaps {
            let Some(gap_id) = gap.get("id").and_then(Value::as_str) else {
                continue;
            };
            if !allowed_gap_ids.contains(gap_id) {
                continue;
            }
            if known_gap_matches(row, gap) {
                set_default(row, "pre_exception_outcome", row["outcome"].clone());
                set_str(row, "outcome", "excepted");
                set_str(row, "expected_known_gap_id", gap_id);
                set_str(
                    row,
                    "expected_known_gap_reason",
                    gap["reason"].as_str().unwrap_or("matched expected known-gap metadata"),
                );
                break;
            }
        }
    }
}

fn apply_unsupported_mir_gate(
    rows: &mut [Value],
    gaps: &[Value],
    hooks: &BTreeMap<String, BTreeSet<String>>,
) {
    for row in rows {
        if value_str(row, "slot") != Some("trust-verify")
            || matches!(value_str(row, "outcome"), Some("planned" | "skipped"))
            || !row_has_unsupported_mir(row)
        {
            continue;
        }
        if unsupported_mir_allowed_by_expected_gap(row, gaps, hooks) {
            set_str(row, "unsupported_mir_gate_status", "allowed_expected_gap");
            set_str(
                row,
                "unsupported_mir_gate_reason",
                "matched expected known-gap metadata that explicitly declares unsupported MIR",
            );
            continue;
        }
        set_default(row, "pre_unsupported_mir_outcome", row["outcome"].clone());
        if let Some(object) = row.as_object_mut() {
            if let Some(expected_gap_id) = object.remove("expected_known_gap_id") {
                object.insert(
                    "unsupported_mir_gate_overrode_expected_gap_id".to_string(),
                    expected_gap_id,
                );
            }
            object.remove("expected_known_gap_reason");
        }
        set_str(row, "outcome", "failed");
        set_str(row, "unsupported_mir_gate_status", "failed");
        set_str(
            row,
            "unsupported_mir_gate_reason",
            "trust-verify emitted unsupported MIR for a supported program-index row",
        );
    }
}

fn unsupported_mir_allowed_by_expected_gap(
    row: &Value,
    gaps: &[Value],
    hooks: &BTreeMap<String, BTreeSet<String>>,
) -> bool {
    let allowed_gap_ids = allowed_expected_gap_ids_for_row(row, hooks);
    gaps.iter().any(|gap| {
        gap.get("id").and_then(Value::as_str).is_some_and(|gap_id| allowed_gap_ids.contains(gap_id))
            && gap_declares_unsupported_mir(gap)
            && known_gap_matches(row, gap)
    })
}

fn gap_declares_unsupported_mir(gap: &Value) -> bool {
    ["stderr_contains_any", "stderr_contains_all"].iter().any(|key| {
        gap.get(*key)
            .and_then(|value| string_list(value, key).ok())
            .is_some_and(|values| values.iter().any(|value| text_contains_unsupported_mir(value)))
    })
}

fn row_has_unsupported_mir(row: &Value) -> bool {
    let stderr = format!(
        "{}\n{}",
        value_str(row, "stderr_excerpt").unwrap_or(""),
        value_str(row, "stderr_tail_excerpt").unwrap_or("")
    );
    text_contains_unsupported_mir(&stderr)
}

fn text_contains_unsupported_mir(value: &str) -> bool {
    let lowered = value.to_ascii_lowercase();
    lowered.contains("unsupportedmir") || contains_unsupported_whitespace_mir(&lowered)
}

fn contains_unsupported_whitespace_mir(value: &str) -> bool {
    let mut remaining = value;
    while let Some(offset) = remaining.find("unsupported") {
        let after = &remaining[offset + "unsupported".len()..];
        let mut chars = after.chars();
        if chars.next().is_some_and(char::is_whitespace) {
            let after_whitespace = after.trim_start_matches(char::is_whitespace);
            if after_whitespace.starts_with("mir") {
                return true;
            }
        }
        remaining = &after[after.char_indices().nth(1).map_or(after.len(), |(index, _)| index)..];
    }
    false
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UnsupportedFrontendLoweringCategory {
    TypedTrustIr,
    Thir,
    LegacyMir,
}

impl UnsupportedFrontendLoweringCategory {
    fn as_str(self) -> &'static str {
        match self {
            Self::TypedTrustIr => "typed_trust_ir",
            Self::Thir => "thir",
            Self::LegacyMir => "legacy_mir",
        }
    }

    fn transport_counter(self) -> &'static str {
        match self {
            Self::TypedTrustIr => "unsupported_trust_ir_results",
            Self::Thir => "unsupported_thir_results",
            Self::LegacyMir => "unsupported_mir_results",
        }
    }
}

fn unsupported_frontend_lowering_category(
    value: &str,
) -> Option<UnsupportedFrontendLoweringCategory> {
    let lowered = value.to_ascii_lowercase();
    let trust_ir_context = ["trustir", "trust-ir", "trust_ir", "trust ir"]
        .iter()
        .any(|marker| lowered.contains(marker));
    let typed_native_requirement = [
        "typed trustir native evidence",
        "typed trust-ir native evidence",
        "typed trust_ir native evidence",
        "typed trust ir native evidence",
    ]
    .iter()
    .any(|marker| lowered.contains(marker));
    let explicit_trust_ir_gap = lowered.contains("unsupportedtrustir")
        || lowered.contains("unsupported trustir")
        || lowered.contains("unsupported trust-ir")
        || lowered.contains("unsupported trust_ir")
        || lowered.contains("unsupported trust ir")
        || lowered.contains("trust.trust_ir.native.unsupported_reason")
        || (typed_native_requirement
            && ["requires", "failed to lower", "unsupported"]
                .iter()
                .any(|marker| lowered.contains(marker)))
        || (lowered.contains("nativeverificationbundle") && lowered.contains("failed to lower"))
        || (trust_ir_context
            && [
                "lowering failed",
                "failed to lower",
                "unsupported operation",
                "evidence status: unsupported",
            ]
            .iter()
            .any(|marker| lowered.contains(marker)));
    if explicit_trust_ir_gap {
        return Some(UnsupportedFrontendLoweringCategory::TypedTrustIr);
    }
    if lowered.contains("unsupportedthir")
        || lowered.contains("unsupported thir")
        || lowered.contains("trust.thir.unsupported")
    {
        return Some(UnsupportedFrontendLoweringCategory::Thir);
    }
    text_contains_unsupported_mir(&lowered)
        .then_some(UnsupportedFrontendLoweringCategory::LegacyMir)
}

fn row_unsupported_frontend_lowering_category(
    row: &Value,
) -> Option<UnsupportedFrontendLoweringCategory> {
    let transport = row.get("transport").unwrap_or(&Value::Null);
    for (counter, category) in [
        ("unsupported_trust_ir_results", UnsupportedFrontendLoweringCategory::TypedTrustIr),
        ("unsupported_thir_results", UnsupportedFrontendLoweringCategory::Thir),
        ("unsupported_mir_results", UnsupportedFrontendLoweringCategory::LegacyMir),
    ] {
        if transport_counter(transport, counter) > 0 {
            return Some(category);
        }
    }
    let stderr = format!(
        "{}\n{}",
        value_str(row, "stderr_excerpt").unwrap_or(""),
        value_str(row, "stderr_tail_excerpt").unwrap_or("")
    );
    unsupported_frontend_lowering_category(&stderr)
}

fn gap_declares_unsupported_frontend_lowering(gap: &Value) -> bool {
    ["stderr_contains_any", "stderr_contains_all"].iter().any(|key| {
        gap.get(*key).and_then(|value| string_list(value, key).ok()).is_some_and(|values| {
            values.iter().any(|value| unsupported_frontend_lowering_category(value).is_some())
        })
    })
}

fn unsupported_frontend_lowering_allowed_by_expected_gap(
    row: &Value,
    gaps: &[Value],
    hooks: &BTreeMap<String, BTreeSet<String>>,
) -> bool {
    let allowed_gap_ids = allowed_expected_gap_ids_for_row(row, hooks);
    gaps.iter().any(|gap| {
        gap.get("id").and_then(Value::as_str).is_some_and(|gap_id| allowed_gap_ids.contains(gap_id))
            && gap_declares_unsupported_frontend_lowering(gap)
            && known_gap_matches(row, gap)
    })
}

fn apply_unsupported_frontend_lowering_gate(
    rows: &mut [Value],
    gaps: &[Value],
    hooks: &BTreeMap<String, BTreeSet<String>>,
) {
    let native_lane_observed = rows.iter().any(|row| {
        value_str(row, "slot") == Some("trust-verify")
            && transport_counter(&row["transport"], "native_evidence_results") > 0
    });

    for row in rows {
        if value_str(row, "slot") != Some("trust-verify")
            || matches!(value_str(row, "outcome"), Some("planned" | "skipped"))
        {
            continue;
        }

        if let Some(category) = row_unsupported_frontend_lowering_category(row) {
            set_str(row, "unsupported_frontend_lowering_category", category.as_str());
            if unsupported_frontend_lowering_allowed_by_expected_gap(row, gaps, hooks) {
                set_str(row, "unsupported_frontend_lowering_gate_status", "allowed_expected_gap");
                set_str(
                    row,
                    "unsupported_frontend_lowering_gate_reason",
                    "matched hooked expected-gap metadata that explicitly declares this unsupported frontend/lowering diagnostic",
                );
                continue;
            }
            fail_unsupported_frontend_lowering_row(
                row,
                "unsupported_lowering",
                &format!(
                    "trust-verify reported an unsupported {} frontend/lowering path",
                    category.as_str()
                ),
            );
            continue;
        }

        let malformed = transport_counter(&row["transport"], "malformed_typed_transport_results");
        if malformed != 0 {
            fail_unsupported_frontend_lowering_row(
                row,
                "missing_native_evidence",
                &format!(
                    "compiler transport contained {malformed} obligation row(s) that failed typed validation; frontend/native evidence cannot be established"
                ),
            );
            continue;
        }

        if !native_lane_observed {
            set_str(row, "unsupported_frontend_lowering_gate_status", "diagnostic_surface_only");
            set_str(
                row,
                "unsupported_frontend_lowering_gate_reason",
                "no explicit unsupported diagnostic was observed, but this legacy transport carried no native TrustIr evidence from which producer completeness could be established",
            );
            continue;
        }

        let transport = &row["transport"];
        let total = transport_counter(transport, "obligation_results");
        let typed = transport_counter(transport, "typed_transport_results");
        let native = transport_counter(transport, "native_trust_ir_results");
        let proved = transport_counter(transport, "proved_results");
        let publishable = transport_counter(transport, "publishable_native_proof_results");
        if total == 0
            || typed != total
            || malformed != 0
            || native != total
            || publishable != proved
        {
            fail_unsupported_frontend_lowering_row(
                row,
                "missing_native_evidence",
                &format!(
                    "typed TrustIr verifier ingress requires typed native input for every obligation and publication-grade native proof for every proved obligation (results={total}, typed={typed}, malformed={malformed}, native={native}, proved={proved}, publishable_proofs={publishable})"
                ),
            );
        } else {
            set_str(row, "unsupported_frontend_lowering_gate_status", "native_evidence_complete");
            set_str(
                row,
                "unsupported_frontend_lowering_gate_reason",
                "typed TrustIr verifier ingress covers every obligation and every proved obligation has publication-grade bound native proof evidence; this does not identify the Rust/Lean frontend producer",
            );
        }
    }
}

fn fail_unsupported_frontend_lowering_row(row: &mut Value, status: &str, reason: &str) {
    set_default(row, "pre_unsupported_frontend_lowering_outcome", row["outcome"].clone());
    if let Some(object) = row.as_object_mut() {
        if let Some(expected_gap_id) = object.remove("expected_known_gap_id") {
            object.insert(
                "unsupported_frontend_lowering_gate_overrode_expected_gap_id".to_string(),
                expected_gap_id,
            );
        }
        object.remove("expected_known_gap_reason");
    }
    set_str(row, "outcome", "failed");
    set_str(row, "unsupported_frontend_lowering_gate_status", status);
    set_str(row, "unsupported_frontend_lowering_gate_reason", reason);
}

fn known_gap_matches(row: &Value, gap: &Value) -> bool {
    let scalar_filters = [
        ("slot", "slot"),
        ("program_id", "program_id"),
        ("pair_id", "pair_id"),
        ("variant", "variant"),
        ("suite", "suite"),
    ];
    for (gap_key, row_key) in scalar_filters {
        if let Some(gap_value) = gap.get(gap_key).and_then(Value::as_str) {
            if value_str(row, row_key) != Some(gap_value) {
                return false;
            }
        }
    }
    let list_filters = [
        ("slots", "slot"),
        ("program_ids", "program_id"),
        ("pair_ids", "pair_id"),
        ("variants", "variant"),
        ("suites", "suite"),
        ("observed", "observed"),
    ];
    for (gap_key, row_key) in list_filters {
        if let Some(gap_values) = gap.get(gap_key) {
            let Ok(values) = string_list(gap_values, gap_key) else {
                return false;
            };
            let Some(row_value) = value_str(row, row_key) else {
                return false;
            };
            if !values.iter().any(|value| value == row_value) {
                return false;
            }
        }
    }
    let stderr = format!(
        "{}\n{}",
        value_str(row, "stderr_excerpt").unwrap_or(""),
        value_str(row, "stderr_tail_excerpt").unwrap_or("")
    );
    if let Some(needles) = gap.get("stderr_contains_any") {
        let Ok(needles) = string_list(needles, "stderr_contains_any") else {
            return false;
        };
        if !needles.iter().any(|needle| stderr.contains(needle)) {
            return false;
        }
    }
    if let Some(needles) = gap.get("stderr_contains_all") {
        let Ok(needles) = string_list(needles, "stderr_contains_all") else {
            return false;
        };
        if !needles.iter().all(|needle| stderr.contains(needle)) {
            return false;
        }
    }
    if let Some(minimums) = gap.get("transport_min") {
        if !transport_minimums_match(minimums, row.get("transport").unwrap_or(&Value::Null)) {
            return false;
        }
    }
    true
}

fn string_list(value: &Value, key: &str) -> Result<Vec<String>, ProgramIndexError> {
    let Some(values) = value.as_array() else {
        return Err(ProgramIndexError::new(format!(
            "expected_known_gaps {key} must be a non-empty list"
        )));
    };
    if values.is_empty() {
        return Err(ProgramIndexError::new(format!(
            "expected_known_gaps {key} must be a non-empty list"
        )));
    }
    values
        .iter()
        .map(|value| {
            value.as_str().filter(|value| !value.is_empty()).map(str::to_string).ok_or_else(|| {
                ProgramIndexError::new(format!(
                    "expected_known_gaps {key} entries must be non-empty strings"
                ))
            })
        })
        .collect()
}

fn validate_transport_minimums(value: &Value) -> Result<(), ProgramIndexError> {
    let object = value.as_object().ok_or_else(|| {
        ProgramIndexError::new("expected_known_gaps transport_min must be an object")
    })?;
    if object.is_empty() {
        return Err(ProgramIndexError::new("expected_known_gaps transport_min must be non-empty"));
    }
    let mut has_positive = false;
    for (key, value) in object {
        if key.is_empty() {
            return Err(ProgramIndexError::new(
                "expected_known_gaps transport_min keys must be strings",
            ));
        }
        let Some(minimum) = value.as_i64() else {
            return Err(ProgramIndexError::new(
                "expected_known_gaps transport_min values must be integers",
            ));
        };
        if minimum < 0 {
            return Err(ProgramIndexError::new(
                "expected_known_gaps transport_min values must be non-negative",
            ));
        }
        has_positive |= minimum > 0;
    }
    if !has_positive {
        return Err(ProgramIndexError::new(
            "expected_known_gaps transport_min must include at least one positive predicate",
        ));
    }
    Ok(())
}

fn transport_minimums_match(minimums: &Value, transport: &Value) -> bool {
    if validate_transport_minimums(minimums).is_err() {
        return false;
    }
    let Some(object) = minimums.as_object() else {
        return false;
    };
    for (key, minimum) in object {
        if int_field(transport, key) < minimum.as_i64().unwrap_or(0) {
            return false;
        }
    }
    true
}

fn preserve_pre_exception_outcomes(rows: &mut [Value]) {
    for row in rows {
        let outcome = row["outcome"].clone();
        set_default(row, "pre_exception_outcome", outcome);
    }
}

fn apply_result_classification(rows: &mut [Value]) {
    for row in rows {
        match value_str(row, "outcome") {
            Some("excepted") => {
                set_str(row, "classification", "expected-known-gap");
                let reason = value_str(row, "expected_known_gap_reason")
                    .unwrap_or("matched expected known-gap metadata")
                    .to_string();
                set_str(row, "classification_reason", reason);
            }
            Some("failed") => {
                set_str(row, "classification", "regression");
                let reason = value_str(row, "measurement_failure_reason")
                    .or_else(|| value_str(row, "unsupported_mir_gate_reason"))
                    .map(str::to_string)
                    .unwrap_or_else(|| {
                        format!(
                            "observed {} but expected {}",
                            value_str(row, "observed").unwrap_or("unknown"),
                            value_str(row, "expected").unwrap_or("unknown")
                        )
                    });
                set_str(row, "classification_reason", reason);
            }
            Some("skipped") => {
                set_str(row, "classification", "not-run");
                let reason =
                    value_str(row, "skip_reason").unwrap_or("slot was not executed").to_string();
                set_str(row, "classification_reason", reason);
            }
            Some("planned") => {
                set_str(row, "classification", "planned");
                set_str(row, "classification_reason", "dry-run command plan");
            }
            _ => {
                set_str(row, "classification", "as-expected");
                let reason = format!(
                    "observed {} matched expected {}",
                    value_str(row, "observed").unwrap_or("unknown"),
                    value_str(row, "expected").unwrap_or("unknown")
                );
                set_str(row, "classification_reason", reason);
            }
        }
        refresh_backward_pass_observed(row);
    }
}

fn summarize(rows: &[Value]) -> Map<String, Value> {
    let mut counts = outcome_counts(rows, "outcome");
    insert_obj(&mut counts, "classifications", string_counts(rows, "classification"));
    let pre_exception = pre_exception_summary(rows);
    counts.insert(
        "raw_failed_before_exceptions".to_string(),
        json!(pre_exception["failed"].as_u64().unwrap_or(0)),
    );
    counts.insert("pre_exception".to_string(), Value::Object(pre_exception));
    insert_obj(&mut counts, "compile_resource_usage", compile_resource_summary(rows));
    counts
}

fn outcome_counts(rows: &[Value], key: &str) -> Map<String, Value> {
    let mut counts = BTreeMap::from([
        ("passed".to_string(), 0_u64),
        ("failed".to_string(), 0_u64),
        ("excepted".to_string(), 0_u64),
        ("skipped".to_string(), 0_u64),
        ("planned".to_string(), 0_u64),
    ]);
    for row in rows {
        let outcome = value_str(row, key).or_else(|| value_str(row, "outcome"));
        if let Some(value) = outcome {
            if let Some(count) = counts.get_mut(value) {
                *count += 1;
            }
        }
    }
    let mut object: Map<String, Value> =
        counts.into_iter().map(|(key, count)| (key, json!(count))).collect();
    object.insert("total_rows".to_string(), json!(rows.len()));
    object
}

fn pre_exception_summary(rows: &[Value]) -> Map<String, Value> {
    let mut counts = outcome_counts(rows, "pre_exception_outcome");
    insert_obj(
        &mut counts,
        "failures_by_slot",
        count_failed_by(rows, "slot", "pre_exception_outcome"),
    );
    insert_obj(
        &mut counts,
        "failures_by_observed",
        count_failed_by(rows, "observed", "pre_exception_outcome"),
    );
    insert_obj(
        &mut counts,
        "failures_by_expected",
        count_failed_by(rows, "expected", "pre_exception_outcome"),
    );
    counts
}

fn count_failed_by(rows: &[Value], field: &str, outcome_key: &str) -> Map<String, Value> {
    let mut counts = BTreeMap::<String, u64>::new();
    for row in rows {
        if value_str(row, outcome_key).or_else(|| value_str(row, "outcome")) != Some("failed") {
            continue;
        }
        if let Some(value) = value_str(row, field) {
            *counts.entry(value.to_string()).or_default() += 1;
        }
    }
    counts.into_iter().map(|(key, count)| (key, json!(count))).collect()
}

fn corpus_summary(programs: &[Program], selected_slots: &[String]) -> Value {
    let mut variants =
        BTreeMap::<String, u64>::from([("good".to_string(), 0), ("flawed".to_string(), 0)]);
    let mut suites = BTreeMap::<String, u64>::new();
    let mut obligations = BTreeMap::<String, u64>::new();
    let mut pairs = BTreeSet::<String>::new();
    for program in programs {
        *variants.entry(program.variant.clone()).or_default() += 1;
        *suites.entry(program.suite.clone()).or_default() += 1;
        pairs.insert(program.pair_id.clone());
        for obligation in &program.obligations {
            *obligations.entry(obligation.clone()).or_default() += 1;
        }
    }
    json!({
        "programs": programs.len(),
        "pairs": pairs.len(),
        "variants": variants,
        "suites": suites,
        "obligations": obligations,
        "slots": selected_slots,
    })
}

fn program_index_evidence_summary(programs: &[Program], raw_index: &Value) -> Value {
    let mut gating_suites = index_suite_list(raw_index, "gating_suites");
    if gating_suites.is_empty() {
        gating_suites.insert(PROOF_DESIGN_SUITE.to_string());
    }
    let mut candidate_suites = index_suite_list(raw_index, "candidate_suites");
    if candidate_suites.is_empty() {
        candidate_suites.insert(PROOF_DESIGN_CANDIDATE_SUITE.to_string());
    }

    let selected_suite_names: BTreeSet<String> =
        programs.iter().map(|program| program.suite.clone()).collect();
    let mut selected_suites = Map::new();
    let mut selected_pairs = BTreeSet::<String>::new();
    let mut selected_candidate_rows = 0_u64;
    let mut selected_gating_rows = 0_u64;
    let mut selected_admissible_gating_rows = 0_u64;
    let mut blocked_gating_suites = Vec::<String>::new();

    for program in programs {
        selected_pairs.insert(program.pair_id.clone());
    }

    for suite in &selected_suite_names {
        let suite_programs: Vec<&Program> =
            programs.iter().filter(|program| &program.suite == suite).collect();
        let mut pair_ids = BTreeSet::<String>::new();
        let mut candidate_program_ids = Vec::<String>::new();
        let mut obligations = BTreeMap::<String, u64>::new();
        for program in &suite_programs {
            pair_ids.insert(program.pair_id.clone());
            for obligation in &program.obligations {
                *obligations.entry(obligation.clone()).or_default() += 1;
            }
            if program_is_candidate_evidence(program, &candidate_suites) {
                candidate_program_ids.push(program.id.clone());
            }
        }

        let candidate_rows = candidate_program_ids.len() as u64;
        let gating = gating_suites.contains(suite);
        let candidate_evidence = candidate_suites.contains(suite);
        if candidate_rows > 0 {
            selected_candidate_rows += candidate_rows;
        }
        if gating {
            selected_gating_rows += suite_programs.len() as u64;
            if candidate_rows == 0 && !candidate_evidence {
                selected_admissible_gating_rows += suite_programs.len() as u64;
            } else {
                blocked_gating_suites.push(suite.clone());
            }
        }

        let admissible_for_domination = gating && !candidate_evidence && candidate_rows == 0;
        let evidence_class = if candidate_evidence {
            "candidate_non_gating"
        } else if admissible_for_domination {
            "admissible_gating"
        } else if gating {
            "blocked_gating_candidate_contamination"
        } else {
            "informational_non_gating"
        };
        selected_suites.insert(
            suite.clone(),
            json!({
                "programs": suite_programs.len(),
                "pairs": pair_ids.len(),
                "candidate_rows": candidate_rows,
                "candidate_program_ids": candidate_program_ids,
                "gating": gating,
                "candidate_evidence": candidate_evidence,
                "non_gating": !gating,
                "admissible_for_domination": admissible_for_domination,
                "evidence_class": evidence_class,
                "obligations": obligations,
            }),
        );
    }

    let status = if !blocked_gating_suites.is_empty() {
        "blocked"
    } else if selected_candidate_rows > 0 && selected_gating_rows > 0 {
        "mixed_candidate_non_gating"
    } else if selected_candidate_rows > 0 {
        "candidate_non_gating"
    } else if selected_gating_rows > 0 {
        "admissible"
    } else {
        "informational"
    };
    let selected_suite_counts = selected_suites
        .iter()
        .map(|(suite, evidence)| {
            let programs = evidence["programs"].as_u64().unwrap_or(0);
            (suite.clone(), json!(programs))
        })
        .collect::<Map<String, Value>>();
    let admissible_for_domination = selected_candidate_rows == 0
        && selected_gating_rows > 0
        && blocked_gating_suites.is_empty();

    json!({
        "schema": PROGRAM_INDEX_EVIDENCE_SCHEMA,
        "status": status,
        "model_source": if raw_index.get("suite_evidence_model").is_some() {
            "index.suite_evidence_model"
        } else {
            "default-proof-design-policy"
        },
        "selected_programs": programs.len(),
        "selected_pairs": selected_pairs.len(),
        "selected_suite_count": selected_suites.len(),
        "selected_suite_counts": selected_suite_counts,
        "selected_suites": selected_suites,
        "declared_gating_suites": gating_suites,
        "declared_candidate_suites": candidate_suites,
        "selected_gating_rows": selected_gating_rows,
        "selected_admissible_gating_rows": selected_admissible_gating_rows,
        "selected_candidate_rows": selected_candidate_rows,
        "blocked_gating_suites": blocked_gating_suites,
        "admissible_for_domination": admissible_for_domination,
        "domination_policy": {
            "proof-design": "gating evidence; candidate rows must be absent",
            "proof-design-candidates": "candidate evidence only; non-gating for domination",
        },
    })
}

fn program_index_evidence_summary_for_report(evidence: &Value) -> Value {
    json!({
        "schema": PROGRAM_INDEX_EVIDENCE_SCHEMA,
        "status": evidence["status"],
        "selected_programs": evidence["selected_programs"],
        "selected_pairs": evidence["selected_pairs"],
        "selected_suite_count": evidence["selected_suite_count"],
        "selected_suite_counts": evidence["selected_suite_counts"],
        "selected_gating_rows": evidence["selected_gating_rows"],
        "selected_admissible_gating_rows": evidence["selected_admissible_gating_rows"],
        "selected_candidate_rows": evidence["selected_candidate_rows"],
        "blocked_gating_suites": evidence["blocked_gating_suites"],
        "admissible_for_domination": evidence["admissible_for_domination"],
    })
}

fn proof_design_verifier_evidence(
    args: &ProgramIndexArgs,
    rows: &[Value],
    bindings: &[SlotBinding],
    program_index_evidence: &Value,
    toolchain_integrity: &Value,
    report_dir: &Path,
) -> Value {
    let proof_design_suite = program_index_evidence
        .get("selected_suites")
        .and_then(|suites| suites.get(PROOF_DESIGN_SUITE))
        .unwrap_or(&Value::Null);
    let selected_programs = proof_design_suite.get("programs").and_then(Value::as_u64).unwrap_or(0);
    let proof_design_claim = args.suite.as_deref() == Some(PROOF_DESIGN_SUITE)
        || args.slots.iter().any(|slot| slot == PROOF_FUNCTIONAL_SLOT_ID);
    let required = selected_programs > 0 && proof_design_claim;
    if !required {
        let reason = if selected_programs == 0 {
            "selected program-index corpus did not include proof-design gating rows"
        } else {
            "proof-design rows were selected for non-proof benchmark evidence without the trust-verify proof slot"
        };
        return json!({
            "schema": PROOF_DESIGN_VERIFIER_EVIDENCE_SCHEMA,
            "status": if selected_programs == 0 { "not_applicable" } else { "not_claimed" },
            "required": false,
            "admissible_for_domination": false,
            "reason": reason,
            "selected_programs": selected_programs,
            "verifier_rows": 0,
            "accepted_rows": 0,
            "blocked_reasons": [],
            "stage2_binding": Value::Null,
            "transport_protocol": "stderr-line-prefix",
            "transport_prefix": TRANSPORT_PREFIX,
            "transport_sources": [],
            "rows": [],
        });
    }

    let mut blockers = Vec::<String>::new();
    if args.dry_run {
        blockers.push("proof-design verifier evidence must be a non-dry-run report".to_string());
    }
    if program_index_evidence.get("status").and_then(Value::as_str) != Some("admissible")
        || program_index_evidence.get("admissible_for_domination").and_then(Value::as_bool)
            != Some(true)
        || proof_design_suite.get("admissible_for_domination").and_then(Value::as_bool)
            != Some(true)
    {
        blockers.push(
            "program_index_evidence must be admissible proof-design gating evidence".to_string(),
        );
    }
    match toolchain_integrity.get("status").and_then(Value::as_str) {
        Some("unchanged") => {}
        Some(status) => blockers.push(format!(
            "toolchain_integrity.status must be unchanged for proof-design verifier evidence, got `{status}`"
        )),
        None => blockers
            .push("toolchain_integrity.status must be present for proof-design verifier evidence"
                .to_string()),
    }

    let stage2_binding =
        proof_design_stage2_binding(bindings, &args.repo_root, PROOF_FUNCTIONAL_SLOT_ID);
    if stage2_binding.get("status").and_then(Value::as_str) != Some("bound") {
        let status = stage2_binding.get("status").and_then(Value::as_str).unwrap_or("unknown");
        blockers.push(format!(
            "proof-design verifier slot {PROOF_FUNCTIONAL_SLOT_ID} must bind to repo-local build/*/stage2/bin/trustc, got status `{status}`"
        ));
    }

    let proof_rows = rows
        .iter()
        .filter(|row| {
            value_str(row, "suite") == Some(PROOF_DESIGN_SUITE)
                && value_str(row, "slot") == Some(PROOF_FUNCTIONAL_SLOT_ID)
        })
        .collect::<Vec<_>>();
    if proof_rows.len() as u64 != selected_programs {
        blockers.push(format!(
            "selected proof-design programs={selected_programs} but report contains {} proof-design {PROOF_FUNCTIONAL_SLOT_ID} rows",
            proof_rows.len()
        ));
    }

    let mut row_evidence = Vec::new();
    let mut accepted_rows = 0_u64;
    let mut good_rows = 0_u64;
    let mut flawed_rows = 0_u64;
    let mut total_obligations = 0_u64;
    let mut proved_obligations = 0_u64;
    let mut failed_obligations = 0_u64;
    let mut transport_sources = BTreeSet::<String>::new();

    for row in proof_rows {
        let evidence = proof_design_row_verifier_evidence(row, report_dir);
        if evidence.get("accepted").and_then(Value::as_bool) == Some(true) {
            accepted_rows += 1;
        }
        match evidence.get("variant").and_then(Value::as_str) {
            Some("good") => good_rows += 1,
            Some("flawed") => flawed_rows += 1,
            _ => {}
        }
        total_obligations += evidence.get("total_obligations").and_then(Value::as_u64).unwrap_or(0);
        proved_obligations +=
            evidence.get("proved_obligations").and_then(Value::as_u64).unwrap_or(0);
        failed_obligations +=
            evidence.get("failed_obligations").and_then(Value::as_u64).unwrap_or(0);
        if let Some(path) = evidence
            .get("transport_source")
            .and_then(|source| source.get("stderr_path"))
            .and_then(Value::as_str)
        {
            transport_sources.insert(path.to_string());
        }
        blockers.extend(
            evidence
                .get("blockers")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .map(str::to_string),
        );
        row_evidence.push(evidence);
    }

    if good_rows == 0 {
        blockers.push("proof-design verifier evidence must include known-good rows".to_string());
    }
    if flawed_rows == 0 {
        blockers.push("proof-design verifier evidence must include known-flawed rows".to_string());
    }

    blockers.sort();
    blockers.dedup();
    let status = if blockers.is_empty() { "passed" } else { "blocked" };
    json!({
        "schema": PROOF_DESIGN_VERIFIER_EVIDENCE_SCHEMA,
        "status": status,
        "required": true,
        "admissible_for_domination": status == "passed",
        "domination_policy": "proof-design gating evidence requires clean trust-verify observations from repo-local stage2 trustc with structured TRUST_JSON transport",
        "selected_programs": selected_programs,
        "verifier_slot": PROOF_FUNCTIONAL_SLOT_ID,
        "verifier_rows": row_evidence.len(),
        "accepted_rows": accepted_rows,
        "good_rows": good_rows,
        "flawed_rows": flawed_rows,
        "total_obligations": total_obligations,
        "proved_obligations": proved_obligations,
        "failed_obligations": failed_obligations,
        "blocked_reasons": blockers,
        "stage2_binding": stage2_binding,
        "toolchain_integrity_status": toolchain_integrity.get("status").and_then(Value::as_str),
        "transport_protocol": "stderr-line-prefix",
        "transport_prefix": TRANSPORT_PREFIX,
        "transport_sources": transport_sources.into_iter().collect::<Vec<_>>(),
        "rows": row_evidence,
    })
}

const PROOF_FUNCTIONAL_SLOT_ID: &str = "trust-verify";

fn proof_design_stage2_binding(bindings: &[SlotBinding], repo_root: &Path, slot_id: &str) -> Value {
    let Some(binding) = bindings.iter().find(|binding| binding.id == slot_id) else {
        return json!({
            "slot": slot_id,
            "status": "missing_slot",
            "binary": Value::Null,
            "source": Value::Null,
            "canonical_binary": "trustc",
            "canonical_entrypoint": false,
            "repo_stage2": false,
            "stage2_roots": [],
        });
    };
    let Some(binary) = binding.binary.as_deref() else {
        return json!({
            "slot": binding.id,
            "status": "missing_binary",
            "binary": Value::Null,
            "source": binding.source,
            "canonical_binary": binding.profile.fallback_binary,
            "resolved_binary_name": Value::Null,
            "canonical_entrypoint": false,
            "repo_stage2": false,
            "stage2_roots": [],
        });
    };
    let roots = stage2_roots_for_binary(binary, repo_root);
    let canonical_entrypoint =
        resolved_binary_name(binding) == Some(binding.profile.fallback_binary);
    let repo_stage2 = !roots.is_empty();
    let status = if !repo_stage2 {
        "non_repo_stage2"
    } else if !canonical_entrypoint {
        "noncanonical_entrypoint"
    } else {
        "bound"
    };
    json!({
        "slot": binding.id,
        "status": status,
        "binary": binary,
        "binary_report_path": path_for_report(Path::new(binary), repo_root),
        "source": binding.source,
        "canonical_binary": binding.profile.fallback_binary,
        "resolved_binary_name": resolved_binary_name(binding),
        "canonical_entrypoint": canonical_entrypoint,
        "repo_stage2": repo_stage2,
        "stage2_roots": roots
            .iter()
            .map(|root| path_for_report(root, repo_root))
            .collect::<Vec<_>>(),
        "extra_args": binding.profile.extra_args,
    })
}

fn proof_design_row_verifier_evidence(row: &Value, report_dir: &Path) -> Value {
    let program = value_str(row, "program_id").unwrap_or("<unknown>");
    let variant = value_str(row, "variant").unwrap_or("<unknown>");
    let expected = match variant {
        "good" => Some("verify_pass"),
        "flawed" => Some("verify_fail"),
        _ => None,
    };
    let transport = row.get("transport").unwrap_or(&Value::Null);
    let total = transport_counter(transport, "total");
    let obligation_results = transport_counter(transport, "obligation_results");
    let proved = transport_counter(transport, "proved");
    let proved_results = transport_counter(transport, "proved_results");
    let failed = transport_counter(transport, "failed");
    let failed_results = transport_counter(transport, "failed_results");
    let unknown = transport_counter(transport, "unknown");
    let unknown_results = transport_counter(transport, "unknown_results");
    let runtime_checked = transport_counter(transport, "runtime_checked");
    let runtime_checked_results = transport_counter(transport, "runtime_checked_results");
    let function_results = transport_counter(transport, "function_results");
    let malformed_lines = transport_counter(transport, "malformed_lines");
    let typed_transport = transport_counter(transport, "typed_transport_results");
    let malformed_typed = transport_counter(transport, "malformed_typed_transport_results");
    let native_trust_ir = transport_counter(transport, "native_trust_ir_results");
    let publishable_native_proofs =
        transport_counter(transport, "publishable_native_proof_results");
    let counterexamples = transport_counter(transport, "counterexamples")
        + transport_counter(transport, "counterexample_models");
    let repair_candidates = transport_counter(transport, "repair_candidates");
    let mut blockers = Vec::<String>::new();

    if expected.is_none() {
        blockers.push(format!("{program}: variant must be good or flawed, got `{variant}`"));
    }
    if value_str(row, "expected") != expected {
        blockers.push(format!(
            "{program}: expected must be {:?}, got {:?}",
            expected,
            value_str(row, "expected")
        ));
    }
    if value_str(row, "observed") != expected {
        blockers.push(format!(
            "{program}: observed must be {:?}, got {:?}",
            expected,
            value_str(row, "observed")
        ));
    }
    if value_str(row, "outcome") != Some("passed") {
        blockers.push(format!(
            "{program}: outcome must be passed, got {:?}",
            value_str(row, "outcome")
        ));
    }
    if value_str(row, "classification") != Some("as-expected") {
        blockers.push(format!(
            "{program}: classification must be as-expected, got {:?}",
            value_str(row, "classification")
        ));
    }
    if value_str(row, "unsupported_frontend_lowering_gate_status")
        != Some("native_evidence_complete")
    {
        blockers.push(format!(
            "{program}: typed TrustIr verifier-ingress gate must be native_evidence_complete"
        ));
    }
    if row.get("obligations").and_then(Value::as_array).is_none_or(|items| items.is_empty()) {
        blockers.push(format!("{program}: obligations must be nonempty"));
    }
    if function_results == 0 {
        blockers.push(format!("{program}: transport must include TRUST_JSON function_result rows"));
    }
    if malformed_lines != 0 {
        blockers.push(format!("{program}: transport has malformed TRUST_JSON lines"));
    }
    if total == 0 {
        blockers.push(format!("{program}: transport total obligations must be positive"));
    }
    if total != obligation_results {
        blockers.push(format!(
            "{program}: transport.total={total} must match obligation_results={obligation_results}"
        ));
    }
    if typed_transport != obligation_results
        || native_trust_ir != obligation_results
        || malformed_typed != 0
    {
        blockers.push(format!(
            "{program}: typed TrustIr verifier-ingress evidence must cover every obligation (obligations={obligation_results}, typed={typed_transport}, native_trust_ir={native_trust_ir}, malformed={malformed_typed})"
        ));
    }
    if publishable_native_proofs != proved_results {
        blockers.push(format!(
            "{program}: publication-grade native proofs must cover every proved obligation (proved={proved_results}, publishable={publishable_native_proofs})"
        ));
    }
    if proved != proved_results {
        blockers.push(format!(
            "{program}: transport.proved={proved} must match proved_results={proved_results}"
        ));
    }
    if failed != failed_results {
        blockers.push(format!(
            "{program}: transport.failed={failed} must match failed_results={failed_results}"
        ));
    }
    if unknown != unknown_results {
        blockers.push(format!(
            "{program}: transport.unknown={unknown} must match unknown_results={unknown_results}"
        ));
    }
    if runtime_checked != runtime_checked_results {
        blockers.push(format!(
            "{program}: transport.runtime_checked={runtime_checked} must match runtime_checked_results={runtime_checked_results}"
        ));
    }
    if unknown != 0 || runtime_checked != 0 {
        blockers.push(format!(
            "{program}: transport must have unknown=0 and runtime_checked=0, got unknown={unknown} runtime_checked={runtime_checked}"
        ));
    }
    if proved + failed + unknown + runtime_checked > total {
        blockers.push(format!(
            "{program}: transport counters exceed total={total}, got proved={proved} failed={failed} unknown={unknown} runtime_checked={runtime_checked}"
        ));
    }
    match variant {
        "good" if proved != total || failed != 0 => blockers.push(format!(
            "{program}: good proof-design row must prove all obligations and have failed=0"
        )),
        "flawed" if failed == 0 => {
            blockers.push(format!("{program}: flawed proof-design row must fail obligations"))
        }
        _ => {}
    }

    let sample_sources = row
        .get("samples")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(|sample| sample.get("stderr_path").and_then(Value::as_str))
        .map(|path| {
            json!({
                "kind": "stderr_log",
                "path": path,
                "protocol": "stderr-line-prefix",
                "prefix": TRANSPORT_PREFIX,
            })
        })
        .collect::<Vec<_>>();
    let stderr_path = value_str(row, "stderr_path").map(str::to_string);
    let stdout_path = value_str(row, "stdout_path").map(str::to_string);
    let output_path = value_str(row, "output_path").map(str::to_string);
    let accepted = blockers.is_empty();
    let transport_evidence = json!({
        "protocol": "stderr-line-prefix",
        "prefix": TRANSPORT_PREFIX,
        "function_results": function_results,
        "crate_summaries": transport_counter(transport, "crate_summaries"),
        "malformed_lines": malformed_lines,
        "total": total,
        "obligation_results": obligation_results,
        "proved": proved,
        "proved_results": proved_results,
        "failed": failed,
        "failed_results": failed_results,
        "unknown": unknown,
        "unknown_results": unknown_results,
        "runtime_checked": runtime_checked,
        "runtime_checked_results": runtime_checked_results,
        "typed_transport_results": typed_transport,
        "malformed_typed_transport_results": malformed_typed,
        "native_trust_ir_results": native_trust_ir,
        "publishable_native_proof_results": publishable_native_proofs,
        "counterexamples": transport_counter(transport, "counterexamples"),
        "counterexample_models": transport_counter(transport, "counterexample_models"),
        "repair_candidates": repair_candidates,
    });
    let transport_source = json!({
        "kind": "stderr_log",
        "stderr_path": stderr_path,
        "stdout_path": stdout_path,
        "output_path": output_path,
        "protocol": "stderr-line-prefix",
        "prefix": TRANSPORT_PREFIX,
        "relative_to": report_dir.to_string_lossy(),
    });

    json!({
        "program_id": program,
        "pair_id": value_str(row, "pair_id"),
        "variant": variant,
        "source": value_str(row, "source"),
        "source_sha256": value_str(row, "source_sha256"),
        "slot": value_str(row, "slot"),
        "slot_binary": value_str(row, "slot_binary"),
        "slot_binary_source": value_str(row, "slot_binary_source"),
        "expected": value_str(row, "expected"),
        "observed": value_str(row, "observed"),
        "outcome": value_str(row, "outcome"),
        "classification": value_str(row, "classification"),
        "accepted": accepted,
        "blockers": blockers,
        "obligations": row.get("obligations").cloned().unwrap_or(Value::Null),
        "total_obligations": total,
        "proved_obligations": proved,
        "failed_obligations": failed,
        "unknown_obligations": unknown,
        "runtime_checked_obligations": runtime_checked,
        "counterexample_payloads": counterexamples,
        "repair_candidate_payloads": repair_candidates,
        "transport": transport_evidence,
        "transport_source": transport_source,
        "sample_transport_sources": sample_sources,
        "sample_count": row.get("sample_count").and_then(Value::as_u64).unwrap_or(0),
    })
}

fn transport_counter(value: &Value, key: &str) -> u64 {
    value
        .get(key)
        .and_then(|value| {
            value.as_u64().or_else(|| value.as_i64().and_then(|value| value.try_into().ok()))
        })
        .unwrap_or(0)
}

fn proof_design_verifier_evidence_summary_for_report(evidence: &Value) -> Value {
    json!({
        "schema": PROOF_DESIGN_VERIFIER_EVIDENCE_SCHEMA,
        "status": evidence["status"],
        "required": evidence["required"],
        "admissible_for_domination": evidence["admissible_for_domination"],
        "selected_programs": evidence["selected_programs"],
        "verifier_slot": evidence["verifier_slot"],
        "verifier_rows": evidence["verifier_rows"],
        "accepted_rows": evidence["accepted_rows"],
        "good_rows": evidence["good_rows"],
        "flawed_rows": evidence["flawed_rows"],
        "total_obligations": evidence["total_obligations"],
        "proved_obligations": evidence["proved_obligations"],
        "failed_obligations": evidence["failed_obligations"],
        "stage2_binding_status": evidence["stage2_binding"]["status"],
        "toolchain_integrity_status": evidence["toolchain_integrity_status"],
        "transport_protocol": evidence["transport_protocol"],
        "transport_sources": evidence["transport_sources"],
        "blocked_reasons": evidence["blocked_reasons"],
    })
}

fn index_suite_list(raw_index: &Value, key: &str) -> BTreeSet<String> {
    raw_index["suite_evidence_model"][key]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .filter(|value| !value.is_empty())
        .map(str::to_string)
        .collect()
}

fn program_is_candidate_evidence(program: &Program, candidate_suites: &BTreeSet<String>) -> bool {
    candidate_suites.contains(&program.suite)
        || program.metadata.get("candidate").and_then(Value::as_bool) == Some(true)
}

fn strict_superiority_performance_evidence(
    args: &ProgramIndexArgs,
    rows: &[Value],
    runtime_parity: &Value,
    program_index_evidence: &Value,
    platform_identity: &Value,
) -> Value {
    let candidate_rejection = performance_candidate_rejection(program_index_evidence);
    let mut lanes = Map::new();
    lanes.insert(
        "clean_release_compile".to_string(),
        compile_performance_lane(
            args,
            rows,
            &candidate_rejection,
            platform_identity,
            "clean_release_compile",
            "Clean release compile duration evidence from cold artifact compiles",
            BuildProfile::Release,
            CompileMeasurementMode::ColdArtifact,
            "duration_seconds",
        ),
    );
    lanes.insert(
        "incremental_debug_compile".to_string(),
        compile_performance_lane(
            args,
            rows,
            &candidate_rejection,
            platform_identity,
            "incremental_debug_compile",
            "Warm incremental debug compile duration evidence",
            BuildProfile::Debug,
            CompileMeasurementMode::WarmIncremental,
            "duration_seconds",
        ),
    );
    lanes.insert(
        "runtime_geomean".to_string(),
        runtime_performance_lane(
            args,
            runtime_parity,
            &candidate_rejection,
            platform_identity,
            "runtime_geomean",
            "Linked release runtime geomean evidence",
            BuildProfile::Release,
            "run_duration_seconds",
        ),
    );
    lanes.insert(
        "binary_size".to_string(),
        runtime_performance_lane(
            args,
            runtime_parity,
            &candidate_rejection,
            platform_identity,
            "binary_size",
            "Linked release executable size evidence",
            BuildProfile::Release,
            "executable_size_bytes",
        ),
    );

    let measured_lanes =
        lanes.values().filter(|lane| lane["status"].as_str() == Some("measured")).count();
    let blocked_lanes =
        lanes.values().filter(|lane| lane["status"].as_str() == Some("blocked")).count();
    let status = if measured_lanes == lanes.len() {
        "complete"
    } else if measured_lanes > 0 {
        "partial"
    } else {
        "blocked"
    };
    let blocked_reasons = lanes
        .values()
        .flat_map(|lane| {
            lane["blocked_reasons"].as_array().into_iter().flatten().filter_map(Value::as_str)
        })
        .map(str::to_string)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();

    json!({
        "schema": STRICT_SUPERIORITY_PERFORMANCE_SCHEMA,
        "status": status,
        "admissible_for_domination": status == "complete",
        "measured_lanes": measured_lanes,
        "blocked_lanes": blocked_lanes,
        "blocked_reasons": blocked_reasons,
        "target_arch": platform_identity["target_arch"],
        "target_triple": platform_identity["target_triple"],
        "host": {
            "arch": platform_identity["host_arch"],
            "triple": platform_identity["host_triple"],
        },
        "host_arch": platform_identity["host_arch"],
        "host_triple": platform_identity["host_triple"],
        "platform_identity": platform_identity,
        "repetitions": args.repetitions,
        "runtime_repetitions": 1,
        "build_profile": args.build_profile.as_str(),
        "build_profile_detail": build_profile_report(args.build_profile),
        "compile_measurement_mode": args.compile_measurement_mode.as_str(),
        "dry_run": args.dry_run,
        "candidate_rejection": candidate_rejection,
        "baseline_slot": RUNTIME_BASELINE_SLOT,
        "trust_slots": trust_performance_slots(rows, runtime_parity),
        "lanes": Value::Object(lanes),
    })
}

fn strict_superiority_performance_evidence_summary_for_report(evidence: &Value) -> Value {
    json!({
        "schema": STRICT_SUPERIORITY_PERFORMANCE_SCHEMA,
        "status": evidence["status"],
        "admissible_for_domination": evidence["admissible_for_domination"],
        "measured_lanes": evidence["measured_lanes"],
        "blocked_lanes": evidence["blocked_lanes"],
        "blocked_reasons": evidence["blocked_reasons"],
        "target_arch": evidence["target_arch"],
        "target_triple": evidence["target_triple"],
        "host_arch": evidence["host_arch"],
        "host_triple": evidence["host_triple"],
        "repetitions": evidence["repetitions"],
        "runtime_repetitions": evidence["runtime_repetitions"],
        "build_profile": evidence["build_profile"],
        "compile_measurement_mode": evidence["compile_measurement_mode"],
        "dry_run": evidence["dry_run"],
        "candidate_rejected": evidence["candidate_rejection"]["rejected"],
        "lane_statuses": evidence["lanes"]
            .as_object()
            .map(|lanes| {
                lanes.iter()
                    .map(|(lane, evidence)| (lane.clone(), evidence["status"].clone()))
                    .collect::<Map<String, Value>>()
            })
            .unwrap_or_default(),
    })
}

fn performance_candidate_rejection(program_index_evidence: &Value) -> Value {
    let selected_candidate_rows =
        program_index_evidence["selected_candidate_rows"].as_u64().unwrap_or(0);
    let status = program_index_evidence["status"].as_str().unwrap_or("unknown");
    let blocked_gating_suites = program_index_evidence["blocked_gating_suites"]
        .as_array()
        .map(|items| !items.is_empty())
        .unwrap_or(false);
    let rejected = selected_candidate_rows > 0
        || matches!(status, "candidate_non_gating" | "mixed_candidate_non_gating" | "blocked")
        || blocked_gating_suites;
    json!({
        "schema": PROGRAM_INDEX_EVIDENCE_SCHEMA,
        "rejected": rejected,
        "status": status,
        "selected_candidate_rows": selected_candidate_rows,
        "selected_gating_rows": program_index_evidence["selected_gating_rows"],
        "selected_admissible_gating_rows": program_index_evidence["selected_admissible_gating_rows"],
        "admissible_for_domination": program_index_evidence["admissible_for_domination"],
        "blocked_gating_suites": program_index_evidence["blocked_gating_suites"],
        "reason": if rejected {
            "candidate or contaminated program-index evidence is non-gating for strict-superiority performance claims"
        } else {
            "no selected candidate rows were present in the performance source data"
        },
    })
}

fn compile_performance_lane(
    args: &ProgramIndexArgs,
    rows: &[Value],
    candidate_rejection: &Value,
    platform_identity: &Value,
    lane_id: &str,
    description: &str,
    required_profile: BuildProfile,
    required_measurement: CompileMeasurementMode,
    metric: &str,
) -> Value {
    let mut blocked_reasons =
        performance_common_blockers(args, candidate_rejection, platform_identity);
    if args.build_profile != required_profile {
        blocked_reasons.push(format!(
            "requires --build-profile {}, got {}",
            required_profile.as_str(),
            args.build_profile.as_str()
        ));
    }
    if args.compile_measurement_mode != required_measurement {
        blocked_reasons.push(format!(
            "requires --compile-measurement {}, got {}",
            required_measurement.as_str(),
            args.compile_measurement_mode.as_str()
        ));
    }

    let baseline = compile_slot_performance(rows, RUNTIME_BASELINE_SLOT, metric);
    let trust_slots = compile_trust_slots(rows);
    let trust = trust_slots
        .iter()
        .map(|slot| (slot.clone(), compile_slot_performance(rows, slot, metric)))
        .collect::<Map<String, Value>>();
    if baseline["value"].as_f64().is_none() {
        blocked_reasons
            .push(format!("baseline slot {RUNTIME_BASELINE_SLOT} has no measured {metric}"));
    }
    if trust
        .values()
        .all(|slot| slot["value"].as_f64().is_none() && slot["value"].as_u64().is_none())
    {
        blocked_reasons
            .push("no Trust compile comparison slot has measured performance data".to_string());
    }

    let comparisons = performance_comparisons(&baseline, &trust, metric, false);
    performance_lane_report(
        args,
        platform_identity,
        lane_id,
        description,
        required_profile,
        Some(required_measurement),
        metric,
        blocked_reasons,
        baseline,
        Value::Object(trust),
        comparisons,
    )
}

fn runtime_performance_lane(
    args: &ProgramIndexArgs,
    runtime_parity: &Value,
    candidate_rejection: &Value,
    platform_identity: &Value,
    lane_id: &str,
    description: &str,
    required_profile: BuildProfile,
    metric: &str,
) -> Value {
    let mut blocked_reasons =
        performance_common_blockers(args, candidate_rejection, platform_identity);
    if args.build_profile != required_profile {
        blocked_reasons.push(format!(
            "requires --build-profile {}, got {}",
            required_profile.as_str(),
            args.build_profile.as_str()
        ));
    }
    if runtime_parity["requested"].as_bool() != Some(true) {
        blocked_reasons.push(
            "--runtime-parity is required for linked runtime and binary-size lanes".to_string(),
        );
    }
    if runtime_parity["status"].as_str() != Some("passed") {
        blocked_reasons.push(format!(
            "runtime parity status is {}",
            runtime_parity["status"].as_str().unwrap_or("unknown")
        ));
    }

    let rows = runtime_parity["rows"].as_array().cloned().unwrap_or_default();
    let baseline = runtime_slot_performance(&rows, RUNTIME_BASELINE_SLOT, metric);
    let trust_slots = runtime_trust_slots(&rows);
    let trust = trust_slots
        .iter()
        .map(|slot| (slot.clone(), runtime_slot_performance(&rows, slot, metric)))
        .collect::<Map<String, Value>>();
    if baseline["value"].as_f64().is_none() && baseline["value"].as_u64().is_none() {
        blocked_reasons
            .push(format!("baseline slot {RUNTIME_BASELINE_SLOT} has no measured {metric}"));
    }
    if trust
        .values()
        .all(|slot| slot["value"].as_f64().is_none() && slot["value"].as_u64().is_none())
    {
        blocked_reasons
            .push("no Trust runtime comparison slot has measured performance data".to_string());
    }

    let comparisons =
        performance_comparisons(&baseline, &trust, metric, metric.ends_with("size_bytes"));
    performance_lane_report(
        args,
        platform_identity,
        lane_id,
        description,
        required_profile,
        None,
        metric,
        blocked_reasons,
        baseline,
        Value::Object(trust),
        comparisons,
    )
}

fn performance_common_blockers(
    args: &ProgramIndexArgs,
    candidate_rejection: &Value,
    platform_identity: &Value,
) -> Vec<String> {
    let mut blockers = Vec::new();
    if args.dry_run {
        blockers.push("dry-run report contains planned commands only".to_string());
    }
    if candidate_rejection["rejected"].as_bool() == Some(true) {
        blockers.push("candidate_data_rejected".to_string());
    }
    blockers.extend(
        platform_identity["blockers"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .map(|reason| format!("platform_identity: {reason}")),
    );
    blockers
}

fn performance_lane_report(
    args: &ProgramIndexArgs,
    platform_identity: &Value,
    lane_id: &str,
    description: &str,
    required_profile: BuildProfile,
    required_measurement: Option<CompileMeasurementMode>,
    metric: &str,
    blocked_reasons: Vec<String>,
    rust: Value,
    trust: Value,
    comparisons: Value,
) -> Value {
    let status = if blocked_reasons.is_empty() { "measured" } else { "blocked" };
    json!({
        "schema": STRICT_SUPERIORITY_PERFORMANCE_SCHEMA,
        "lane": lane_id,
        "description": description,
        "status": status,
        "admissible_for_domination": status == "measured",
        "blocked_reasons": blocked_reasons,
        "metric": metric,
        "lower_is_better": true,
        "required_build_profile": required_profile.as_str(),
        "required_compile_measurement_mode": required_measurement.map(CompileMeasurementMode::as_str),
        "actual_build_profile": args.build_profile.as_str(),
        "actual_compile_measurement_mode": args.compile_measurement_mode.as_str(),
        "target_arch": platform_identity["target_arch"],
        "target_triple": platform_identity["target_triple"],
        "host_arch": platform_identity["host_arch"],
        "host_triple": platform_identity["host_triple"],
        "platform_identity_status": platform_identity["status"],
        "repetitions": args.repetitions,
        "runtime_repetitions": 1,
        "rust": rust,
        "trust": trust,
        "comparisons": comparisons,
    })
}

fn compile_slot_performance(rows: &[Value], slot: &str, metric: &str) -> Value {
    let selected = rows
        .iter()
        .filter(|row| {
            value_str(row, "slot") == Some(slot)
                && value_str(row, "slot_mode") == Some("compile")
                && value_str(row, "outcome") == Some("passed")
                && row["measurement_profile"]["status"].as_str() == Some("measured")
                && row["sample_count"].as_u64().unwrap_or(0) > 0
        })
        .collect::<Vec<_>>();
    let durations = compile_sample_f64_values(&selected, "duration_seconds");
    let sizes = compile_sample_f64_values(&selected, "output_size_bytes");
    let metric_values = if metric == "output_size_bytes" { &sizes } else { &durations };
    json!({
        "slot": slot,
        "value": performance_metric_value(metric_values, metric),
        "value_kind": performance_value_kind(metric),
        "rows": selected.len(),
        "sample_count": metric_values.len(),
        "duration_seconds": performance_stats_f64(&durations),
        "size_bytes": performance_stats_f64(&sizes),
        "programs": selected.iter().filter_map(|row| value_str(row, "program_id")).collect::<BTreeSet<_>>().into_iter().collect::<Vec<_>>(),
        "outcomes": string_counts_from_values(selected.iter().filter_map(|row| value_str(row, "outcome"))),
    })
}

fn runtime_slot_performance(rows: &[Value], slot: &str, metric: &str) -> Value {
    let selected = rows
        .iter()
        .filter(|row| {
            value_str(row, "slot") == Some(slot)
                && row["runtime_participant"].as_bool() == Some(true)
                && value_str(row, "runtime_classification") == Some("runtime-parity")
                && value_str(row, "build_status") == Some("compile_pass")
                && value_str(row, "run_status") == Some("run_complete")
        })
        .collect::<Vec<_>>();
    let durations = selected
        .iter()
        .filter_map(|row| value_as_f64(&row["run_duration_seconds"]))
        .collect::<Vec<_>>();
    let sizes = selected
        .iter()
        .filter_map(|row| value_as_f64(&row["executable_size_bytes"]))
        .collect::<Vec<_>>();
    let metric_values = if metric == "executable_size_bytes" { &sizes } else { &durations };
    json!({
        "slot": slot,
        "value": performance_metric_value(metric_values, metric),
        "value_kind": performance_value_kind(metric),
        "rows": selected.len(),
        "sample_count": metric_values.len(),
        "duration_seconds": performance_stats_f64(&durations),
        "size_bytes": performance_stats_f64(&sizes),
        "programs": selected.iter().filter_map(|row| value_str(row, "program_id")).collect::<BTreeSet<_>>().into_iter().collect::<Vec<_>>(),
        "classifications": string_counts_from_values(selected.iter().filter_map(|row| value_str(row, "runtime_classification"))),
    })
}

fn compile_sample_f64_values(rows: &[&Value], key: &str) -> Vec<f64> {
    let mut values = Vec::new();
    for row in rows {
        let before = values.len();
        if let Some(samples) = row["samples"].as_array() {
            values.extend(samples.iter().filter_map(|sample| value_as_f64(&sample[key])));
        }
        if values.len() == before {
            values.extend(value_as_f64(&row[key]));
        }
    }
    values.into_iter().filter(|value| value.is_finite() && *value > 0.0).collect()
}

fn compile_trust_slots(rows: &[Value]) -> Vec<String> {
    rows.iter()
        .filter(|row| {
            value_str(row, "slot_mode") == Some("compile")
                && row["trust_owned"].as_bool() == Some(true)
                && value_str(row, "slot") != Some("trust-verify")
        })
        .filter_map(|row| value_str(row, "slot").map(str::to_string))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn runtime_trust_slots(rows: &[Value]) -> Vec<String> {
    rows.iter()
        .filter(|row| {
            row["runtime_participant"].as_bool() == Some(true)
                && value_str(row, "slot") != Some(RUNTIME_BASELINE_SLOT)
        })
        .filter_map(|row| value_str(row, "slot").map(str::to_string))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn trust_performance_slots(rows: &[Value], runtime_parity: &Value) -> Value {
    let mut slots = compile_trust_slots(rows).into_iter().collect::<BTreeSet<_>>();
    if let Some(runtime_rows) = runtime_parity["rows"].as_array() {
        slots.extend(runtime_trust_slots(runtime_rows));
    }
    json!(slots.into_iter().collect::<Vec<_>>())
}

fn performance_comparisons(
    rust: &Value,
    trust: &Map<String, Value>,
    metric: &str,
    integer_values: bool,
) -> Value {
    let rust_value = value_as_f64(&rust["value"]);
    Value::Array(
        trust
            .iter()
            .map(|(slot, evidence)| {
                let trust_value = value_as_f64(&evidence["value"]);
                let ratio = rust_value.zip(trust_value).and_then(|(rust_value, trust_value)| {
                    (rust_value > 0.0).then(|| round_ratio(trust_value / rust_value))
                });
                json!({
                    "trust_slot": slot,
                    "metric": metric,
                    "rust_value": performance_optional_value(rust_value, integer_values),
                    "trust_value": performance_optional_value(trust_value, integer_values),
                    "ratio_vs_rust": ratio,
                    "trust_at_most_rust": rust_value
                        .zip(trust_value)
                        .map(|(rust_value, trust_value)| trust_value <= rust_value),
                    "trust_strictly_better": rust_value
                        .zip(trust_value)
                        .map(|(rust_value, trust_value)| trust_value < rust_value),
                    "comparison_policy": "lower_is_better",
                })
            })
            .collect(),
    )
}

fn performance_metric_value(values: &[f64], metric: &str) -> Value {
    let Some(value) = geomean_f64(values) else {
        return Value::Null;
    };
    if metric.ends_with("size_bytes") {
        json!(value.round() as u64)
    } else {
        json!(round_seconds(value))
    }
}

fn performance_value_kind(metric: &str) -> &'static str {
    if metric.ends_with("size_bytes") { "geomean_size_bytes" } else { "geomean_seconds" }
}

fn performance_optional_value(value: Option<f64>, integer: bool) -> Value {
    match (value, integer) {
        (Some(value), true) => json!(value.round() as u64),
        (Some(value), false) => json!(round_seconds(value)),
        (None, _) => Value::Null,
    }
}

fn performance_stats_f64(values: &[f64]) -> Value {
    let mut sorted = values
        .iter()
        .copied()
        .filter(|value| value.is_finite() && *value > 0.0)
        .collect::<Vec<_>>();
    if sorted.is_empty() {
        return Value::Null;
    }
    sorted.sort_by(|left, right| left.total_cmp(right));
    json!({
        "count": sorted.len(),
        "p50": p50_sorted_f64(&sorted).map(round_seconds),
        "p95": p95_sorted_f64(&sorted).map(round_seconds),
        "max": round_seconds(sorted[sorted.len() - 1]),
        "geomean": geomean_f64(&sorted).map(round_seconds),
        "min": round_seconds(sorted[0]),
    })
}

fn p95_sorted_f64(sorted: &[f64]) -> Option<f64> {
    (!sorted.is_empty()).then(|| sorted[nearest_rank_index(sorted.len(), 0.95)])
}

fn geomean_f64(values: &[f64]) -> Option<f64> {
    let positive = values
        .iter()
        .copied()
        .filter(|value| value.is_finite() && *value > 0.0)
        .collect::<Vec<_>>();
    if positive.is_empty() {
        return None;
    }
    Some((positive.iter().map(|value| value.ln()).sum::<f64>() / positive.len() as f64).exp())
}

fn value_as_f64(value: &Value) -> Option<f64> {
    value
        .as_f64()
        .or_else(|| value.as_i64().map(|value| value as f64))
        .or_else(|| value.as_u64().map(|value| value as f64))
        .filter(|value| value.is_finite())
}

fn round_ratio(value: f64) -> f64 {
    (value * 1_000_000.0).round() / 1_000_000.0
}

fn compile_resource_summary(rows: &[Value]) -> Map<String, Value> {
    let mut by_slot = Map::new();
    let slots: BTreeSet<String> =
        rows.iter().filter_map(|row| value_str(row, "slot").map(str::to_string)).collect();
    for slot in slots {
        let slot_rows: Vec<Value> = rows
            .iter()
            .filter(|row| value_str(row, "slot") == Some(slot.as_str()))
            .cloned()
            .collect();
        by_slot.insert(
            slot,
            json!({
                "duration_seconds_total": round_seconds(numeric_sum(&slot_rows, "duration_seconds")),
                "peak_rss_bytes_max": max_i64_or_none(&slot_rows, "peak_rss_bytes"),
                "sample_count_total": sample_count_sum(&slot_rows),
            }),
        );
    }
    let mut object = Map::new();
    object.insert(
        "duration_seconds_total".to_string(),
        json!(round_seconds(numeric_sum(rows, "duration_seconds"))),
    );
    object.insert(
        "peak_rss_bytes_max".to_string(),
        option_i64(max_i64_or_none(rows, "peak_rss_bytes")),
    );
    object.insert(
        "timed_out".to_string(),
        json!(rows.iter().filter(|row| row["timed_out"].as_bool() == Some(true)).count()),
    );
    object.insert(
        "rows_with_peak_rss".to_string(),
        json!(rows.iter().filter(|row| row["peak_rss_bytes"].as_i64().is_some()).count()),
    );
    object.insert("sample_count_total".to_string(), json!(sample_count_sum(rows)));
    object.insert(
        "rows_with_samples".to_string(),
        json!(rows.iter().filter(|row| row["sample_count"].as_u64().unwrap_or(0) > 0).count()),
    );
    insert_obj(&mut object, "measurement_profiles", measurement_profile_summary(rows));
    object.insert("by_slot".to_string(), Value::Object(by_slot));
    object
}

fn measurement_profile_summary(rows: &[Value]) -> Map<String, Value> {
    let mut cache_states = BTreeMap::<String, u64>::new();
    let mut statuses = BTreeMap::<String, u64>::new();
    let mut modes = BTreeMap::<String, u64>::new();
    let mut incremental_rows = 0_u64;
    let mut non_incremental_rows = 0_u64;
    let mut requested_incremental_rows = 0_u64;
    let mut measured_incremental_rows = 0_u64;
    let mut measured_non_incremental_rows = 0_u64;
    let mut runtime_separate_rows = 0_u64;
    let mut missing_profile_rows = 0_u64;

    for row in rows {
        let Some(profile) = row.get("measurement_profile").and_then(Value::as_object) else {
            missing_profile_rows += 1;
            continue;
        };
        if let Some(cache_state) = profile.get("cache_state").and_then(Value::as_str) {
            *cache_states.entry(cache_state.to_string()).or_default() += 1;
        }
        if let Some(status) = profile.get("status").and_then(Value::as_str) {
            *statuses.entry(status.to_string()).or_default() += 1;
        }
        if let Some(mode) = profile.get("mode").and_then(Value::as_str) {
            *modes.entry(mode.to_string()).or_default() += 1;
        }
        if profile.get("requested_incremental").and_then(Value::as_bool) == Some(true) {
            requested_incremental_rows += 1;
        }
        match profile.get("incremental").and_then(Value::as_bool) {
            Some(true) => {
                incremental_rows += 1;
                if profile.get("status").and_then(Value::as_str) == Some("measured") {
                    measured_incremental_rows += 1;
                }
            }
            Some(false) => {
                non_incremental_rows += 1;
                if profile.get("status").and_then(Value::as_str) == Some("measured") {
                    measured_non_incremental_rows += 1;
                }
            }
            None => {}
        }
        if profile.get("runtime_measurements_separate").and_then(Value::as_bool) == Some(true) {
            runtime_separate_rows += 1;
        }
    }

    let mut object = Map::new();
    object.insert("schema".to_string(), json!(COMPILE_MEASUREMENT_PROFILE_SCHEMA));
    object.insert("missing_profile_rows".to_string(), json!(missing_profile_rows));
    object.insert("incremental_rows".to_string(), json!(incremental_rows));
    object.insert("non_incremental_rows".to_string(), json!(non_incremental_rows));
    object.insert("requested_incremental_rows".to_string(), json!(requested_incremental_rows));
    object.insert("measured_incremental_rows".to_string(), json!(measured_incremental_rows));
    object
        .insert("measured_non_incremental_rows".to_string(), json!(measured_non_incremental_rows));
    object.insert("runtime_measurements_separate_rows".to_string(), json!(runtime_separate_rows));
    let modes: Map<String, Value> =
        modes.into_iter().map(|(key, value)| (key, json!(value))).collect();
    let cache_states: Map<String, Value> =
        cache_states.into_iter().map(|(key, value)| (key, json!(value))).collect();
    let statuses: Map<String, Value> =
        statuses.into_iter().map(|(key, value)| (key, json!(value))).collect();
    insert_obj(&mut object, "modes", modes);
    insert_obj(&mut object, "cache_states", cache_states);
    insert_obj(&mut object, "statuses", statuses);
    object
}

fn expectation_rows_summary<F>(rows: &[Value], predicate: F, description: &str) -> Value
where
    F: Fn(&Value) -> bool,
{
    let selected: Vec<Value> = rows.iter().filter(|row| predicate(row)).cloned().collect();
    let counts = outcome_counts(&selected, "outcome");
    let pre_exception = pre_exception_summary(&selected);
    json!({
        "description": description,
        "status": expectation_status(&counts),
        "passed": counts["passed"],
        "failed": counts["failed"],
        "excepted": counts["excepted"],
        "skipped": counts["skipped"],
        "planned": counts["planned"],
        "total_rows": counts["total_rows"],
        "raw_failed_before_exceptions": pre_exception["failed"],
        "failures_by_slot": pre_exception["failures_by_slot"],
        "failures_by_observed": pre_exception["failures_by_observed"],
        "outcomes_by_slot": outcome_counts_by_string_key(&selected, "slot"),
        "observed": string_counts(&selected, "observed"),
        "expected": string_counts(&selected, "expected"),
        "classifications": string_counts(&selected, "classification"),
    })
}

fn compile_acceptance_summary(rows: &[Value], variant: &str) -> Value {
    expectation_rows_summary(
        rows,
        |row| {
            value_str(row, "variant") == Some(variant)
                && value_str(row, "slot_mode") == Some("compile")
                && value_str(row, "expected") == Some("compile_pass")
        },
        &format!("compile-mode slots accepted known-{variant} programs as Rust programs"),
    )
}

fn codegen_output_evidence_summary(rows: &[Value]) -> Value {
    let compile_rows: Vec<Value> =
        rows.iter().filter(|row| value_str(row, "slot_mode") == Some("compile")).cloned().collect();
    let with_output: Vec<Value> = compile_rows
        .iter()
        .filter(|row| row["output_exists"].as_bool() == Some(true))
        .cloned()
        .collect();
    let nonempty_output: Vec<Value> = with_output
        .iter()
        .filter(|row| row["output_size_bytes"].as_u64().is_some_and(|size| size > 0))
        .cloned()
        .collect();
    let status = if compile_rows.is_empty() {
        "not_applicable"
    } else if value_str(&compile_rows[0], "outcome") == Some("planned")
        && compile_rows.iter().all(|row| value_str(row, "outcome") == Some("planned"))
    {
        "planned"
    } else if nonempty_output.len() == compile_rows.len() {
        "complete"
    } else if !nonempty_output.is_empty() {
        "partial"
    } else {
        "missing"
    };
    json!({
        "schema": "trust.compile-verify-program-index.codegen-output-evidence.v1",
        "status": status,
        "description": "Counts non-empty compiler outputs for compile-mode slots; this is output-presence evidence, not semantic object parity.",
        "compile_rows": compile_rows.len(),
        "rows_with_output": with_output.len(),
        "rows_with_nonempty_output": nonempty_output.len(),
        "by_slot": compile_output_counts_by_slot(&compile_rows),
        "by_variant": {
            "rows_with_nonempty_output": string_counts(&nonempty_output, "variant"),
            "outcomes": string_counts(&compile_rows, "outcome"),
        },
    })
}

fn compile_output_counts_by_slot(rows: &[Value]) -> Value {
    let mut by_slot = Map::new();
    let slots: BTreeSet<String> =
        rows.iter().filter_map(|row| value_str(row, "slot").map(str::to_string)).collect();
    for slot in slots {
        let slot_rows: Vec<Value> = rows
            .iter()
            .filter(|row| value_str(row, "slot") == Some(slot.as_str()))
            .cloned()
            .collect();
        let nonempty = slot_rows
            .iter()
            .filter(|row| row["output_size_bytes"].as_u64().is_some_and(|size| size > 0))
            .count();
        by_slot.insert(
            slot,
            json!({
                "rows": slot_rows.len(),
                "rows_with_output": slot_rows
                    .iter()
                    .filter(|row| row["output_exists"].as_bool() == Some(true))
                    .count(),
                "rows_with_nonempty_output": nonempty,
                "outcomes": string_counts(&slot_rows, "outcome"),
            }),
        );
    }
    Value::Object(by_slot)
}

fn hello_world_gate_summary(rows: &[Value]) -> Value {
    let selected: Vec<Value> = rows
        .iter()
        .filter(|row| {
            value_str(row, "program_id").is_some_and(|id| id.contains("hello_world"))
                || value_str(row, "pair_id").is_some_and(|id| id.contains("hello_world"))
        })
        .cloned()
        .collect();
    let counts = outcome_counts(&selected, "outcome");
    json!({
        "schema": "trust.program-index.hello-world-gate.v1",
        "status": expectation_status(&counts),
        "total_rows": selected.len(),
        "outcomes": counts,
        "raw_failed_before_exceptions": pre_exception_summary(&selected)["failed"],
        "failure_phases": string_counts(&selected, "observed"),
        "stderr_categories": Value::Object(Map::new()),
        "trust_owned_binary_names": string_counts(&selected, "trust_owned_binary_name"),
        "sysroot_paths": string_counts(&selected, "sysroot_path"),
    })
}

fn unsupported_frontend_lowering_gate_summary(rows: &[Value]) -> Value {
    let selected = rows
        .iter()
        .filter(|row| value_str(row, "slot") == Some("trust-verify"))
        .cloned()
        .collect::<Vec<_>>();
    let failed_rows = selected
        .iter()
        .filter(|row| {
            matches!(
                value_str(row, "unsupported_frontend_lowering_gate_status"),
                Some("unsupported_lowering" | "missing_native_evidence")
            )
        })
        .cloned()
        .collect::<Vec<_>>();
    let allowed_rows = selected
        .iter()
        .filter(|row| {
            value_str(row, "unsupported_frontend_lowering_gate_status")
                == Some("allowed_expected_gap")
        })
        .cloned()
        .collect::<Vec<_>>();
    let native_complete_rows = selected
        .iter()
        .filter(|row| {
            value_str(row, "unsupported_frontend_lowering_gate_status")
                == Some("native_evidence_complete")
        })
        .cloned()
        .collect::<Vec<_>>();
    let diagnostic_only_rows = selected
        .iter()
        .filter(|row| {
            value_str(row, "unsupported_frontend_lowering_gate_status")
                == Some("diagnostic_surface_only")
        })
        .cloned()
        .collect::<Vec<_>>();
    let planned =
        selected.iter().filter(|row| value_str(row, "outcome") == Some("planned")).count();
    let skipped =
        selected.iter().filter(|row| value_str(row, "outcome") == Some("skipped")).count();
    let status = if selected.is_empty() {
        "not_applicable"
    } else if !failed_rows.is_empty() {
        "failed"
    } else if planned == selected.len() {
        "planned"
    } else if skipped == selected.len() {
        "not_run"
    } else if !allowed_rows.is_empty() {
        "passed_with_expected_gaps"
    } else if native_complete_rows.len() == selected.len() {
        "passed"
    } else if !native_complete_rows.is_empty() {
        "mixed_native_and_diagnostic_evidence"
    } else {
        "diagnostic_surface_only"
    };
    let sum_transport = |key: &str| {
        selected.iter().map(|row| transport_counter(&row["transport"], key)).sum::<u64>()
    };
    json!({
        "schema": UNSUPPORTED_FRONTEND_LOWERING_GATE_SCHEMA,
        "status": status,
        "description": "Producer-neutral transition gate for explicit unsupported Rust/Lean frontend, THIR, legacy MIR, and typed TrustIr lowering diagnostics. Rust/THIR and Lean/Clean lower directly to canonical typed TrustIr. Once typed TrustIr verifier ingress is observed, every obligation must carry typed native input and every proved obligation must carry publication-grade bound proof evidence. Transport currently cannot authenticate that the producer was the direct Rust/Lean frontend, so this gate grants no direct-frontend proof authority; authenticated MIR-derived material is retained only as temporary compatibility and differential evidence, not canonical semantics.",
        "frontend_transition": {
            "direct_frontend_proof_authority": false,
            "direct_frontend_status": "structural_non_authoritative",
            "producer_authenticated_by_transport": false,
            "mir_compatibility_proof_path_retained": true,
        },
        "backward_compatibility": {
            "legacy_gate_preserved": true,
            "legacy_summary_field": "unsupported_mir_gate",
            "legacy_schema": UNSUPPORTED_MIR_GATE_SCHEMA,
        },
        "observation_scope": {
            "stderr": "bounded first/tail excerpts only",
            "transport": "all parsed TRUST_JSON obligation rows within the bounded capture",
            "thir_completeness": "explicit diagnostics only; absence does not prove that every producer-side THIR unsupported ledger entry was emitted",
            "completeness_claim": status == "passed",
            "completeness_claim_scope": "typed_trust_ir_verifier_ingress_only",
        },
        "total_rows": selected.len(),
        "failed": failed_rows.len(),
        "allowed_expected_gap": allowed_rows.len(),
        "native_evidence_complete": native_complete_rows.len(),
        "diagnostic_surface_only": diagnostic_only_rows.len(),
        "diagnostic_categories": string_counts(&selected, "unsupported_frontend_lowering_category"),
        "native_evidence": {
            "obligation_results": sum_transport("obligation_results"),
            "typed_transport_results": sum_transport("typed_transport_results"),
            "malformed_typed_transport_results": sum_transport("malformed_typed_transport_results"),
            "native_trust_ir_results": sum_transport("native_trust_ir_results"),
            "proof_evidence_results": sum_transport("proof_evidence_results"),
            "publishable_native_proof_results": sum_transport("publishable_native_proof_results"),
            "proved_results": sum_transport("proved_results"),
        },
        "failed_rows": unsupported_frontend_lowering_gate_row_refs(&failed_rows),
        "allowed_rows": unsupported_frontend_lowering_gate_row_refs(&allowed_rows),
    })
}

fn unsupported_frontend_lowering_gate_row_refs(rows: &[Value]) -> Value {
    Value::Array(
        rows.iter()
            .take(UNSUPPORTED_MIR_GATE_ROW_LIMIT)
            .map(|row| {
                json!({
                    "program_id": row.get("program_id").cloned().unwrap_or(Value::Null),
                    "variant": row.get("variant").cloned().unwrap_or(Value::Null),
                    "observed": row.get("observed").cloned().unwrap_or(Value::Null),
                    "expected": row.get("expected").cloned().unwrap_or(Value::Null),
                    "stderr_path": row.get("stderr_path").cloned().unwrap_or(Value::Null),
                    "category": row.get("unsupported_frontend_lowering_category").cloned().unwrap_or(Value::Null),
                    "status": row.get("unsupported_frontend_lowering_gate_status").cloned().unwrap_or(Value::Null),
                    "reason": row.get("unsupported_frontend_lowering_gate_reason").cloned().unwrap_or(Value::Null),
                })
            })
            .collect(),
    )
}

fn unsupported_mir_gate_summary(rows: &[Value]) -> Value {
    let selected: Vec<Value> =
        rows.iter().filter(|row| value_str(row, "slot") == Some("trust-verify")).cloned().collect();
    let failed_rows: Vec<Value> = selected
        .iter()
        .filter(|row| value_str(row, "unsupported_mir_gate_status") == Some("failed"))
        .cloned()
        .collect();
    let allowed_rows: Vec<Value> = selected
        .iter()
        .filter(|row| value_str(row, "unsupported_mir_gate_status") == Some("allowed_expected_gap"))
        .cloned()
        .collect();
    let unsupported_rows: Vec<Value> =
        selected.iter().filter(|row| row_has_unsupported_mir(row)).cloned().collect();
    let planned =
        selected.iter().filter(|row| value_str(row, "outcome") == Some("planned")).count();
    let skipped =
        selected.iter().filter(|row| value_str(row, "outcome") == Some("skipped")).count();
    let status = if selected.is_empty() {
        "not_applicable"
    } else if !failed_rows.is_empty() {
        "failed"
    } else if !allowed_rows.is_empty() {
        "passed_with_expected_gaps"
    } else if planned == selected.len() {
        "planned"
    } else if skipped == selected.len() {
        "not_run"
    } else {
        "passed"
    };
    json!({
        "schema": UNSUPPORTED_MIR_GATE_SCHEMA,
        "status": status,
        "description": "Hard gate requiring zero UnsupportedMir/unsupported MIR diagnostics for supported trust-verify rows. Only matching expected-known-gap metadata with an explicit unsupported-MIR signature can allow the diagnostic.",
        "total_rows": selected.len(),
        "unsupported_rows": unsupported_rows.len(),
        "failed": failed_rows.len(),
        "allowed_expected_gap": allowed_rows.len(),
        "by_variant": {
            "failed": string_counts(&failed_rows, "variant"),
            "allowed_expected_gap": string_counts(&allowed_rows, "variant"),
            "unsupported": string_counts(&unsupported_rows, "variant"),
        },
        "failed_rows": unsupported_mir_gate_row_refs(&failed_rows),
        "allowed_rows": unsupported_mir_gate_row_refs(&allowed_rows),
    })
}

fn unsupported_mir_gate_row_refs(rows: &[Value]) -> Value {
    Value::Array(
        rows.iter()
            .take(UNSUPPORTED_MIR_GATE_ROW_LIMIT)
            .map(|row| {
                json!({
                    "program_id": row.get("program_id").cloned().unwrap_or(Value::Null),
                    "variant": row.get("variant").cloned().unwrap_or(Value::Null),
                    "observed": row.get("observed").cloned().unwrap_or(Value::Null),
                    "expected": row.get("expected").cloned().unwrap_or(Value::Null),
                    "stderr_path": row.get("stderr_path").cloned().unwrap_or(Value::Null),
                    "reason": row.get("unsupported_mir_gate_reason").cloned().unwrap_or(Value::Null),
                })
            })
            .collect(),
    )
}

fn expectation_status(counts: &Map<String, Value>) -> &'static str {
    let total = counts["total_rows"].as_u64().unwrap_or(0);
    if total == 0 {
        "not_applicable"
    } else if counts["failed"].as_u64().unwrap_or(0) > 0 {
        "failed"
    } else if counts["passed"].as_u64().unwrap_or(0) == total {
        "passed"
    } else if counts["excepted"].as_u64().unwrap_or(0) > 0 {
        "passed_with_exceptions"
    } else if counts["skipped"].as_u64().unwrap_or(0) == total {
        "not_run"
    } else if counts["planned"].as_u64().unwrap_or(0) == total {
        "planned"
    } else {
        "partial"
    }
}

fn trust_cg_exception_summary(rows: &[Value], trust_cg_mode: &str) -> Value {
    let trust_cg_rows: Vec<Value> =
        rows.iter().filter(|row| value_str(row, "slot") == Some("trust-cg")).cloned().collect();
    let exception_rows: Vec<Value> = trust_cg_rows
        .iter()
        .filter(|row| row.get("trust_cg_exception_class").and_then(Value::as_str).is_some())
        .cloned()
        .collect();
    let reported =
        exception_rows.iter().filter(|row| value_str(row, "outcome") == Some("excepted")).count();
    let fatal =
        exception_rows.iter().filter(|row| value_str(row, "outcome") == Some("failed")).count();
    let non_exception_failures = trust_cg_rows
        .iter()
        .filter(|row| {
            value_str(row, "outcome") == Some("failed")
                && row.get("trust_cg_exception_class").and_then(Value::as_str).is_none()
        })
        .count();
    let skipped =
        trust_cg_rows.iter().filter(|row| value_str(row, "outcome") == Some("skipped")).count();
    let status = if trust_cg_rows.is_empty() {
        "not_applicable"
    } else if fatal > 0 || non_exception_failures > 0 {
        "failed"
    } else if reported > 0 {
        "reported"
    } else if skipped == trust_cg_rows.len() {
        "not_run"
    } else {
        "clean"
    };
    json!({
        "mode": trust_cg_mode,
        "status": status,
        "total_rows": trust_cg_rows.len(),
        "exception_rows": exception_rows.len(),
        "reported": reported,
        "fatal": fatal,
        "non_exception_failures": non_exception_failures,
        "skipped": skipped,
        "classes": string_counts(&exception_rows, "trust_cg_exception_class"),
        "outcomes": string_counts(&trust_cg_rows, "outcome"),
        "observed": string_counts(&trust_cg_rows, "observed"),
        "skipped_reasons": string_counts(&trust_cg_rows, "skip_reason"),
    })
}

fn run_runtime_parity(
    programs: &[Program],
    bindings: &[SlotBinding],
    repo_root: &Path,
    report_dir: &Path,
    timeout_seconds: u64,
    build_profile: BuildProfile,
) -> Result<Value, ProgramIndexError> {
    let mut rows = Vec::new();
    for program in programs {
        let mut program_rows = Vec::new();
        for binding in bindings {
            program_rows.push(run_runtime_slot(
                binding,
                program,
                repo_root,
                report_dir,
                timeout_seconds,
                build_profile,
            )?);
        }
        apply_runtime_parity_classification(&mut program_rows, RUNTIME_BASELINE_SLOT);
        rows.extend(program_rows);
    }
    let summary = summarize_runtime_parity(&rows);
    let status = if summary["failed"].as_u64().unwrap_or(0) > 0 {
        "failed"
    } else if summary["comparison_passed"].as_u64().unwrap_or(0) > 0 {
        "passed"
    } else if summary["baseline_passed"].as_u64().unwrap_or(0) > 0 {
        "baseline_only"
    } else {
        "not_applicable"
    };
    Ok(json!({
        "schema": RUNTIME_PARITY_SCHEMA,
        "requested": true,
        "enabled": true,
        "status": status,
        "baseline_slot": RUNTIME_BASELINE_SLOT,
        "summary": summary,
        "rows": rows,
    }))
}

fn runtime_parity_not_requested() -> Value {
    runtime_parity_not_applicable("runtime parity was not requested", false)
}

fn runtime_parity_not_applicable(reason: &str, requested: bool) -> Value {
    json!({
        "schema": RUNTIME_PARITY_SCHEMA,
        "requested": requested,
        "enabled": false,
        "status": "not_applicable",
        "baseline_slot": RUNTIME_BASELINE_SLOT,
        "reason": reason,
        "summary": summarize_runtime_parity(&[]),
        "rows": [],
    })
}

fn run_runtime_slot(
    binding: &SlotBinding,
    program: &Program,
    repo_root: &Path,
    report_dir: &Path,
    timeout_seconds: u64,
    build_profile: BuildProfile,
) -> Result<Value, ProgramIndexError> {
    if binding.binary.is_none() {
        return Ok(runtime_not_applicable_row(binding, program, "slot binary not found"));
    }
    if binding.profile.mode != "compile" {
        return Ok(runtime_not_applicable_row(
            binding,
            program,
            &format!("slot mode {} is excluded from runtime parity", binding.profile.mode),
        ));
    }
    let artifacts_dir = report_dir.join("runtime/artifacts").join(&binding.id);
    let logs_dir = report_dir.join("runtime/logs").join(&binding.id);
    fs::create_dir_all(&artifacts_dir).map_err(|error| {
        ProgramIndexError::new(format!("create runtime artifacts dir: {error}"))
    })?;
    fs::create_dir_all(&logs_dir)
        .map_err(|error| ProgramIndexError::new(format!("create runtime logs dir: {error}")))?;
    let executable_path = artifacts_dir.join(runtime_executable_name(program));
    let build_stdout_path =
        logs_dir.join(format!("{}.build.stdout.log", sanitize_crate_name(&program.id)));
    let build_stderr_path =
        logs_dir.join(format!("{}.build.stderr.log", sanitize_crate_name(&program.id)));
    let command = build_command(binding, program, &executable_path, true, None, build_profile)?;
    let build_result = execute_command(
        &command,
        repo_root,
        &compiler_env(&binding.id, CompileMeasurementMode::ColdArtifact),
        timeout_seconds,
        &build_stdout_path,
        &build_stderr_path,
        &executable_path,
        "compile",
    )?;
    let mut row = runtime_row_identity(binding, program);
    row.insert("runtime_participant".to_string(), json!(true));
    insert_arr(&mut row, "build_command", command.iter().map(|arg| json!(arg)).collect());
    insert_str(&mut row, "build_command_display", command_display(&command));
    insert_str(&mut row, "build_status", &build_result.status);
    insert_optional_i32(&mut row, "build_exit_code", build_result.exit_code);
    row.insert("build_timed_out".to_string(), json!(build_result.timed_out));
    row.insert(
        "build_duration_seconds".to_string(),
        json!(round_seconds(build_result.duration_seconds)),
    );
    row.insert(
        "build_peak_rss_bytes".to_string(),
        build_result.resource_usage["peak_rss_bytes"].clone(),
    );
    row.insert("build_resource_usage".to_string(), build_result.resource_usage);
    insert_str(
        &mut row,
        "build_stdout_path",
        relative_to_report(&build_result.stdout_path, report_dir),
    );
    insert_str(
        &mut row,
        "build_stderr_path",
        relative_to_report(&build_result.stderr_path, report_dir),
    );
    insert_optional_u64(&mut row, "build_stdout_bytes", Some(build_result.stdout_bytes));
    insert_optional_u64(&mut row, "build_stderr_bytes", Some(build_result.stderr_bytes));
    insert_str(&mut row, "build_stderr_excerpt", build_result.stderr_excerpt);
    insert_str(&mut row, "build_stderr_tail_excerpt", build_result.stderr_tail_excerpt);
    insert_str(&mut row, "executable_path", relative_to_report(&executable_path, report_dir));
    row.insert("executable_exists".to_string(), json!(executable_path.is_file()));
    insert_optional_u64(&mut row, "executable_size_bytes", file_size_or_none(&executable_path));
    insert_optional_str(&mut row, "executable_sha256", file_sha256_or_none(&executable_path)?);
    if build_result.status != "compile_pass" {
        insert_runtime_empty_fields(&mut row);
        return Ok(Value::Object(row));
    }
    let run_stdout_path =
        logs_dir.join(format!("{}.run.stdout.log", sanitize_crate_name(&program.id)));
    let run_stderr_path =
        logs_dir.join(format!("{}.run.stderr.log", sanitize_crate_name(&program.id)));
    let run_command = vec![executable_path.to_string_lossy().into_owned()];
    insert_arr(&mut row, "run_command", run_command.iter().map(|arg| json!(arg)).collect());
    insert_str(&mut row, "run_command_display", command_display(&run_command));
    let mut run_stdout = open_capture_file(&run_stdout_path)
        .map_err(|error| ProgramIndexError::new(format!("create runtime stdout: {error}")))?;
    let mut run_stderr = open_capture_file(&run_stderr_path)
        .map_err(|error| ProgramIndexError::new(format!("create runtime stderr: {error}")))?;
    let child_stdout = run_stdout
        .try_clone()
        .map_err(|error| ProgramIndexError::new(format!("clone runtime stdout: {error}")))?;
    let child_stderr = run_stderr
        .try_clone()
        .map_err(|error| ProgramIndexError::new(format!("clone runtime stderr: {error}")))?;
    let run = run_command_with_resource_usage(
        &run_command,
        repo_root,
        &runtime_env(),
        timeout_seconds,
        child_stdout,
        child_stderr,
    );
    validate_capture_path_identity(&run_stdout, &run_stdout_path)?;
    validate_capture_path_identity(&run_stderr, &run_stderr_path)?;
    let stdout_bytes = capture_len(&run_stdout, &run_stdout_path)?;
    let stderr_bytes = capture_len(&run_stderr, &run_stderr_path)?;
    let stdout_sha256 = capture_sha256(&mut run_stdout, &run_stdout_path)?;
    let stderr_sha256 = capture_sha256(&mut run_stderr, &run_stderr_path)?;
    let stdout_text = read_capture_text_from_file(&mut run_stdout, &run_stdout_path)?;
    let stderr_text = read_capture_text_from_file(&mut run_stderr, &run_stderr_path)?;
    let normalized_stderr = normalize_runtime_stderr(&stderr_text);
    insert_str(&mut row, "run_status", classify_runtime_status(&run));
    insert_optional_i32(&mut row, "run_exit_code", run.exit_code);
    row.insert("run_timed_out".to_string(), json!(run.timed_out));
    row.insert("run_duration_seconds".to_string(), json!(round_seconds(run.elapsed_seconds)));
    row.insert("run_resource_usage".to_string(), run.resource_usage.clone());
    row.insert("run_peak_rss_bytes".to_string(), run.resource_usage["peak_rss_bytes"].clone());
    insert_str(&mut row, "run_stdout_path", relative_to_report(&run_stdout_path, report_dir));
    insert_str(&mut row, "run_stderr_path", relative_to_report(&run_stderr_path, report_dir));
    insert_optional_u64(&mut row, "run_stdout_bytes", Some(stdout_bytes));
    insert_optional_u64(&mut row, "run_stderr_bytes", Some(stderr_bytes));
    insert_optional_str(&mut row, "run_stdout_sha256", Some(stdout_sha256));
    insert_optional_str(&mut row, "run_stderr_sha256", Some(stderr_sha256));
    insert_str(&mut row, "run_stderr_normalized_sha256", trust_types::digest::stable_sha256_hex(normalized_stderr.as_bytes()));
    insert_str(&mut row, "run_stderr_normalization", "rust-panic-thread-id");
    row.insert(
        "run_stderr_normalized_differs_from_raw".to_string(),
        json!(normalized_stderr != stderr_text),
    );
    insert_str(&mut row, "run_stdout_excerpt", excerpt_text(&stdout_text));
    insert_str(&mut row, "run_stderr_excerpt", excerpt_text(&stderr_text));
    insert_str(&mut row, "run_stderr_tail_excerpt", tail_excerpt_text(&stderr_text));
    Ok(Value::Object(row))
}

fn runtime_row_identity(binding: &SlotBinding, program: &Program) -> Map<String, Value> {
    let mut row = Map::new();
    insert_str(&mut row, "program_id", &program.id);
    insert_str(&mut row, "pair_id", &program.pair_id);
    insert_str(&mut row, "variant", &program.variant);
    insert_str(&mut row, "suite", &program.suite);
    insert_str(&mut row, "source", &program.relative_path);
    insert_str(&mut row, "source_sha256", &program.source_sha256);
    insert_arr(
        &mut row,
        "obligations",
        program.obligations.iter().map(|value| json!(value)).collect(),
    );
    row.insert("metadata".to_string(), program.metadata.clone());
    insert_str(&mut row, "slot", &binding.id);
    insert_str(&mut row, "slot_mode", binding.profile.mode);
    match &binding.binary {
        Some(binary) => insert_str(&mut row, "slot_binary", binary),
        None => {
            row.insert("slot_binary".to_string(), Value::Null);
        }
    }
    insert_str(&mut row, "slot_binary_source", &binding.source);
    row
}

fn runtime_not_applicable_row(binding: &SlotBinding, program: &Program, reason: &str) -> Value {
    let mut row = runtime_row_identity(binding, program);
    row.insert("runtime_participant".to_string(), json!(false));
    insert_str(&mut row, "runtime_classification", "runtime-not-applicable");
    insert_str(&mut row, "runtime_classification_reason", reason);
    insert_arr(&mut row, "build_command", Vec::new());
    insert_str(&mut row, "build_command_display", "");
    insert_str(&mut row, "build_status", "not_run");
    row.insert("build_exit_code".to_string(), Value::Null);
    row.insert("build_timed_out".to_string(), json!(false));
    row.insert("build_duration_seconds".to_string(), json!(0.0));
    row.insert("build_peak_rss_bytes".to_string(), Value::Null);
    row.insert("build_resource_usage".to_string(), empty_resource_usage("not-run", 0.0));
    row.insert("build_stdout_path".to_string(), Value::Null);
    row.insert("build_stderr_path".to_string(), Value::Null);
    row.insert("build_stdout_bytes".to_string(), json!(0));
    row.insert("build_stderr_bytes".to_string(), json!(0));
    insert_str(&mut row, "build_stderr_excerpt", "");
    insert_str(&mut row, "build_stderr_tail_excerpt", "");
    row.insert("executable_path".to_string(), Value::Null);
    row.insert("executable_exists".to_string(), json!(false));
    row.insert("executable_size_bytes".to_string(), Value::Null);
    row.insert("executable_sha256".to_string(), Value::Null);
    insert_runtime_empty_fields(&mut row);
    Value::Object(row)
}

fn insert_runtime_empty_fields(row: &mut Map<String, Value>) {
    insert_arr(row, "run_command", Vec::new());
    insert_str(row, "run_command_display", "");
    insert_str(row, "run_status", "not_run");
    row.insert("run_exit_code".to_string(), Value::Null);
    row.insert("run_timed_out".to_string(), json!(false));
    row.insert("run_duration_seconds".to_string(), json!(0.0));
    row.insert("run_resource_usage".to_string(), empty_resource_usage("not-run", 0.0));
    row.insert("run_peak_rss_bytes".to_string(), Value::Null);
    row.insert("run_stdout_path".to_string(), Value::Null);
    row.insert("run_stderr_path".to_string(), Value::Null);
    row.insert("run_stdout_bytes".to_string(), json!(0));
    row.insert("run_stderr_bytes".to_string(), json!(0));
    row.insert("run_stdout_sha256".to_string(), Value::Null);
    row.insert("run_stderr_sha256".to_string(), Value::Null);
    row.insert("run_stderr_normalized_sha256".to_string(), Value::Null);
    insert_str(row, "run_stderr_normalization", "rust-panic-thread-id");
    row.insert("run_stderr_normalized_differs_from_raw".to_string(), json!(false));
    insert_str(row, "run_stdout_excerpt", "");
    insert_str(row, "run_stderr_excerpt", "");
    insert_str(row, "run_stderr_tail_excerpt", "");
}

fn classify_runtime_status(run: &CommandRun) -> &'static str {
    if run.timed_out {
        "timeout"
    } else if run.exit_code.is_none() {
        "runtime_unknown"
    } else {
        "run_complete"
    }
}

fn apply_runtime_parity_classification(rows: &mut [Value], baseline_slot: &str) {
    let baseline = rows.iter().find(|row| value_str(row, "slot") == Some(baseline_slot)).cloned();
    let baseline_ready = baseline.as_ref().is_some_and(runtime_row_ready);
    for row in rows {
        set_str(row, "runtime_baseline_slot", baseline_slot);
        if row["runtime_participant"].as_bool() != Some(true) {
            continue;
        }
        if value_str(row, "slot") == Some(baseline_slot) {
            if runtime_row_ready(row) {
                mark_runtime_row(row, "runtime-parity", "baseline runtime result");
            } else {
                mark_runtime_row(
                    row,
                    "runtime-not-applicable",
                    "baseline did not produce a completed runtime result",
                );
            }
            continue;
        }
        if !baseline_ready {
            mark_runtime_row(
                row,
                "runtime-not-applicable",
                format!("baseline slot {baseline_slot} did not produce a completed runtime result"),
            );
            continue;
        }
        if !runtime_row_ready(row) {
            mark_runtime_row(
                row,
                "runtime-divergence",
                "slot did not produce a completed runtime result",
            );
            set_arr(row, "runtime_differences", vec![json!("build_or_run_status")]);
            continue;
        }
        let differences = runtime_differences(row, baseline.as_ref().expect("checked"));
        if differences.is_empty() {
            mark_runtime_row(row, "runtime-parity", "runtime output matched baseline");
            set_arr(row, "runtime_differences", Vec::new());
        } else {
            mark_runtime_row(
                row,
                "runtime-divergence",
                "runtime exit status or output differed from baseline",
            );
            set_arr(
                row,
                "runtime_differences",
                differences.into_iter().map(Value::String).collect(),
            );
        }
    }
}

fn runtime_row_ready(row: &Value) -> bool {
    value_str(row, "build_status") == Some("compile_pass")
        && value_str(row, "run_status") == Some("run_complete")
}

fn runtime_differences(row: &Value, baseline: &Value) -> Vec<String> {
    let mut differences = Vec::new();
    for key in ["run_exit_code", "run_stdout_sha256"] {
        if row.get(key) != baseline.get(key) {
            differences.push(key.to_string());
        }
    }
    let stderr_key = if row["run_stderr_normalized_sha256"].is_null()
        || baseline["run_stderr_normalized_sha256"].is_null()
    {
        "run_stderr_sha256"
    } else {
        "run_stderr_normalized_sha256"
    };
    if row.get(stderr_key) != baseline.get(stderr_key) {
        differences.push(stderr_key.to_string());
    }
    differences
}

fn mark_runtime_row(row: &mut Value, classification: &str, reason: impl AsRef<str>) {
    set_str(row, "runtime_classification", classification);
    set_str(row, "runtime_classification_reason", reason.as_ref());
}

fn summarize_runtime_parity(rows: &[Value]) -> Value {
    json!({
        "passed": rows.iter().filter(|row| value_str(row, "runtime_classification") == Some("runtime-parity")).count(),
        "failed": rows.iter().filter(|row| value_str(row, "runtime_classification") == Some("runtime-divergence")).count(),
        "not_applicable": rows.iter().filter(|row| value_str(row, "runtime_classification") == Some("runtime-not-applicable")).count(),
        "known_gap": rows.iter().filter(|row| value_str(row, "runtime_classification") == Some("runtime-known-gap")).count(),
        "baseline_passed": rows.iter().filter(|row| value_str(row, "slot") == Some(RUNTIME_BASELINE_SLOT) && value_str(row, "runtime_classification") == Some("runtime-parity")).count(),
        "comparison_passed": rows.iter().filter(|row| value_str(row, "slot") != Some(RUNTIME_BASELINE_SLOT) && value_str(row, "runtime_classification") == Some("runtime-parity")).count(),
        "comparison_failed": rows.iter().filter(|row| value_str(row, "slot") != Some(RUNTIME_BASELINE_SLOT) && value_str(row, "runtime_classification") == Some("runtime-divergence")).count(),
        "total_rows": rows.len(),
        "classifications": string_counts(rows, "runtime_classification"),
        "build_duration_seconds_total": round_seconds(numeric_sum(rows, "build_duration_seconds")),
        "run_duration_seconds_total": round_seconds(numeric_sum(rows, "run_duration_seconds")),
        "build_peak_rss_bytes_max": max_i64_or_none(rows, "build_peak_rss_bytes"),
        "run_peak_rss_bytes_max": max_i64_or_none(rows, "run_peak_rss_bytes"),
    })
}

fn runtime_parity_report_summary(runtime_parity: &Value) -> Value {
    let rows = runtime_parity["rows"].as_array().cloned().unwrap_or_default();
    json!({
        "requested": runtime_parity["requested"].as_bool().unwrap_or(false),
        "enabled": runtime_parity["enabled"].as_bool().unwrap_or(false),
        "status": runtime_parity["status"].as_str().unwrap_or("unknown"),
        "baseline_slot": runtime_parity["baseline_slot"].as_str(),
        "passed": runtime_parity["summary"]["passed"].as_u64().unwrap_or(0),
        "failed": runtime_parity["summary"]["failed"].as_u64().unwrap_or(0),
        "not_applicable": runtime_parity["summary"]["not_applicable"].as_u64().unwrap_or(0),
        "known_gap": runtime_parity["summary"]["known_gap"].as_u64().unwrap_or(0),
        "baseline_passed": runtime_parity["summary"]["baseline_passed"].as_u64().unwrap_or(0),
        "comparison_passed": runtime_parity["summary"]["comparison_passed"].as_u64().unwrap_or(0),
        "comparison_failed": runtime_parity["summary"]["comparison_failed"].as_u64().unwrap_or(0),
        "total_rows": runtime_parity["summary"]["total_rows"].as_u64().unwrap_or(rows.len() as u64),
        "classifications": runtime_parity["summary"]["classifications"].clone(),
        "participant_slots": rows.iter().filter(|row| row["runtime_participant"].as_bool() == Some(true)).filter_map(|row| value_str(row, "slot")).collect::<BTreeSet<_>>().into_iter().collect::<Vec<_>>(),
        "build_duration_seconds_total": round_seconds(numeric_sum(&rows, "build_duration_seconds")),
        "run_duration_seconds_total": round_seconds(numeric_sum(&rows, "run_duration_seconds")),
        "build_peak_rss_bytes_max": max_i64_or_none(&rows, "build_peak_rss_bytes"),
        "run_peak_rss_bytes_max": max_i64_or_none(&rows, "run_peak_rss_bytes"),
    })
}

fn backward_pass_row(raw_index: &Value, program: &Program, binding: &SlotBinding) -> Value {
    let expected = backward_pass_expected(raw_index, &program.variant);
    let evidence = if binding.id == "trust-verify" {
        "pending_verifier_result"
    } else {
        "not_applicable_to_compile_slot"
    };
    json!({
        "expected": expected,
        "observed": "pending",
        "evidence": evidence,
    })
}

fn refresh_backward_pass_observed(row: &mut Value) {
    if value_str(row, "slot") != Some("trust-verify") {
        set_nested_str(row, &["backward_pass", "observed"], "not_applicable");
        set_nested_str(row, &["backward_pass", "evidence"], "not_applicable_to_compile_slot");
        return;
    }
    if value_str(row, "outcome") == Some("planned") {
        set_nested_str(row, &["backward_pass", "observed"], "planned");
        set_nested_str(row, &["backward_pass", "evidence"], "planned");
        return;
    }
    let observed = backward_pass_observed(row);
    set_nested_str(row, &["backward_pass", "observed"], observed);
    let evidence = if observed == value_str(&row["backward_pass"], "expected").unwrap_or("") {
        if observed == "counterexample_or_repair_candidate" {
            "counterexample_or_repair_payload"
        } else {
            "transport_classification"
        }
    } else if value_str(row, "classification") == Some("expected-known-gap") {
        "documented_known_gap"
    } else {
        "missing_or_mismatched"
    };
    set_nested_str(row, &["backward_pass", "evidence"], evidence);
}

fn backward_pass_observed(row: &Value) -> &'static str {
    match (value_str(row, "variant"), value_str(row, "observed")) {
        (Some("good"), Some("verify_pass")) => "no_repair_needed",
        (Some("flawed"), Some("verify_fail")) => {
            let transport = &row["transport"];
            let backward_payload = int_field(transport, "counterexamples")
                + int_field(transport, "counterexample_models")
                + int_field(transport, "repair_candidates");
            if backward_payload > 0 {
                "counterexample_or_repair_candidate"
            } else if int_field(transport, "function_results") == 0 {
                "missing_transport"
            } else {
                "missing_backward_payload"
            }
        }
        (_, Some("verify_inconclusive")) => "inconclusive",
        (_, Some("timeout")) => "timeout",
        (_, Some("verify_no_transport")) => "missing_transport",
        _ => "not_available",
    }
}

fn backward_pass_expected(raw_index: &Value, variant: &str) -> String {
    raw_index["expectation_model"]["default_by_variant"][variant]["backward_pass"]["expected"]
        .as_str()
        .unwrap_or(if variant == "good" {
            "no_repair_needed"
        } else {
            "counterexample_or_repair_candidate"
        })
        .to_string()
}

fn backward_pass_summary(rows: &[Value]) -> Value {
    let trust_rows: Vec<Value> =
        rows.iter().filter(|row| value_str(row, "slot") == Some("trust-verify")).cloned().collect();
    let all_planned = !trust_rows.is_empty()
        && trust_rows.iter().all(|row| value_str(row, "outcome") == Some("planned"));
    json!({
        "status": if trust_rows.is_empty() { "not_applicable" } else if all_planned { "planned" } else if trust_rows.iter().any(|row| row["backward_pass"]["evidence"].as_str() == Some("missing_or_mismatched")) { "partial" } else { "reported" },
        "total_rows": trust_rows.len(),
        "expected": nested_string_counts(&trust_rows, &["backward_pass", "expected"]),
        "observed": nested_string_counts(&trust_rows, &["backward_pass", "observed"]),
        "evidence": nested_string_counts(&trust_rows, &["backward_pass", "evidence"]),
    })
}

fn repair_evidence_summary(repo_root: &Path, report_dir: &Path) -> Value {
    let real_e2e =
        repo_root.join("crates/trust-backprop/tests/program_index_real_verifier_repair_e2e.rs");
    let deterministic =
        repo_root.join("crates/trust-backprop/tests/deterministic_feedback_loop_fixture.rs");
    let explicit_report = report_dir.join("repair-e2e/repair-proof-improvement.json");
    let validation_errors = if explicit_report.is_file() {
        validate_repair_e2e_report(&explicit_report).unwrap_or_else(|errors| errors)
    } else {
        Vec::new()
    };
    let status = if explicit_report.is_file() && validation_errors.is_empty() {
        "real_e2e_report_validated"
    } else if explicit_report.is_file() {
        "artifact_present_unvalidated"
    } else if real_e2e.is_file() {
        "available_not_run"
    } else if deterministic.is_file() {
        "unit_only_available"
    } else {
        "not_available"
    };
    json!({
        "status": status,
        "deterministic_unit_test": path_if_exists(repo_root, &deterministic),
        "real_stage2_e2e_test": path_if_exists(repo_root, &real_e2e),
        "real_stage2_e2e_report": path_if_exists(repo_root, &explicit_report),
        "validation_errors": validation_errors,
        "note": "real repair evidence requires the ignored trust-backprop stage2 E2E; this benchmark records availability unless that artifact is present"
    })
}

fn validate_repair_e2e_report(path: &Path) -> Result<Vec<String>, Vec<String>> {
    let report = match crate::input_limits::read_bounded_utf8_file(
        path,
        crate::input_limits::MAX_SAVED_PROOF_REPORT_BYTES,
    )
    .ok()
    .and_then(|text| serde_json::from_str::<Value>(&text).ok())
    {
        Some(report) => report,
        None => return Err(vec!["repair report is not readable JSON".to_string()]),
    };
    let mut errors = Vec::new();
    if report["schema"].as_str() != Some("trust.repair-e2e.proof-improvement.v1") {
        errors
            .push("repair report schema is not trust.repair-e2e.proof-improvement.v1".to_string());
    }
    if report["improvement"]["improved"].as_bool() != Some(true) {
        errors.push("repair report does not claim improved=true".to_string());
    }
    require_positive_delta(&report, &["improvement", "proved_delta"], &mut errors);
    require_negative_delta(&report, &["improvement", "failed_delta"], &mut errors);
    require_positive_delta(&report, &["improvement", "divzero_proved_delta"], &mut errors);
    require_negative_delta(&report, &["improvement", "divzero_failed_delta"], &mut errors);
    if report["before"]["divzero_counterexamples"].as_array().map_or(true, Vec::is_empty) {
        errors.push("repair report lacks before.divzero_counterexamples".to_string());
    }
    if errors.is_empty() { Ok(Vec::new()) } else { Err(errors) }
}

fn require_positive_delta(report: &Value, path: &[&str], errors: &mut Vec<String>) {
    if nested_i64(report, path).unwrap_or(0) <= 0 {
        errors.push(format!("{} must be positive", path.join(".")));
    }
}

fn require_negative_delta(report: &Value, path: &[&str], errors: &mut Vec<String>) {
    if nested_i64(report, path).unwrap_or(0) >= 0 {
        errors.push(format!("{} must be negative", path.join(".")));
    }
}

fn nested_i64(value: &Value, path: &[&str]) -> Option<i64> {
    let mut current = value;
    for key in path {
        current = current.get(*key)?;
    }
    current.as_i64()
}

fn normalize_runtime_stderr(text: &str) -> String {
    let mut output = String::with_capacity(text.len());
    for line in text.lines() {
        output.push_str(&normalize_panic_thread_id_line(line));
        output.push('\n');
    }
    if !text.ends_with('\n') {
        output.pop();
    }
    output
}

fn normalize_panic_thread_id_line(line: &str) -> String {
    let Some(thread_start) = line.find("thread '") else {
        return line.to_string();
    };
    let Some(name_end_rel) = line[thread_start + 8..].find("' (") else {
        return line.to_string();
    };
    let digits_start = thread_start + 8 + name_end_rel + 3;
    let rest = &line[digits_start..];
    let digits_len = rest.chars().take_while(|ch| ch.is_ascii_digit()).count();
    if digits_len == 0 || !rest[digits_len..].starts_with(") panicked") {
        return line.to_string();
    }
    format!("{}<thread-id>{}", &line[..digits_start], &rest[digits_len..])
}

fn stage2_roots_for_bindings(bindings: &[SlotBinding], repo_root: &Path) -> Vec<PathBuf> {
    let mut roots = BTreeSet::new();
    for binding in bindings {
        let Some(binary) = binding.binary.as_ref() else {
            continue;
        };
        for root in stage2_roots_for_binary(binary, repo_root) {
            roots.insert(root);
        }
    }
    roots.into_iter().collect()
}

fn monitored_stage2_slots(bindings: &[SlotBinding], repo_root: &Path) -> BTreeSet<String> {
    bindings
        .iter()
        .filter(|binding| {
            binding
                .binary
                .as_ref()
                .is_some_and(|binary| !stage2_roots_for_binary(binary, repo_root).is_empty())
        })
        .map(|binding| binding.id.clone())
        .collect()
}

fn stage2_roots_for_binary(binary: &str, repo_root: &Path) -> Vec<PathBuf> {
    let binary_path = absolutize(Path::new(binary), repo_root);
    let mut candidates = vec![binary_path.clone()];
    if let Ok(resolved) = binary_path.canonicalize() {
        if resolved != binary_path {
            candidates.push(resolved);
        }
    }
    let repo_build = repo_root.join("build");
    let mut roots = BTreeSet::new();
    for candidate in candidates {
        for ancestor in candidate.ancestors() {
            if ancestor.file_name() == Some(OsStr::new("stage2"))
                && ancestor.starts_with(&repo_build)
            {
                roots.insert(ancestor.to_path_buf());
                break;
            }
        }
    }
    roots.into_iter().collect()
}

fn capture_stage2_snapshot(
    repo_root: &Path,
    roots: &[PathBuf],
) -> Result<Value, ProgramIndexError> {
    let roots = roots.iter().cloned().collect::<BTreeSet<_>>();
    let root_identities = roots
        .iter()
        .map(|root| stage2_path_for_report(root, repo_root))
        .collect::<std::io::Result<Vec<_>>>()
        .map_err(|error| {
            ProgramIndexError::new(format!("identify stage2 snapshot roots: {error}"))
        })?;
    let mut artifacts = Vec::new();
    let mut errors = Vec::new();
    for root in &roots {
        match fs::symlink_metadata(root) {
            Ok(metadata) if metadata.file_type().is_symlink() => {
                errors.push(format!(
                    "{}: stage2 root is a symlink",
                    path_for_report(root, repo_root)
                ));
                continue;
            }
            Ok(metadata) if !metadata.is_dir() => {
                errors.push(format!(
                    "{}: stage2 root is not a directory",
                    path_for_report(root, repo_root)
                ));
                continue;
            }
            Ok(_) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                errors.push(format!(
                    "{}: stage2 root does not exist",
                    path_for_report(root, repo_root)
                ));
                continue;
            }
            Err(error) => {
                errors.push(format!(
                    "{}: inspect stage2 root: {error}",
                    path_for_report(root, repo_root)
                ));
                continue;
            }
        }
        let mut paths = Vec::new();
        collect_stage2_paths(root, repo_root, &mut paths, &mut errors);
        paths.sort();
        for path in paths {
            match snapshot_stage2_artifact(&path, repo_root) {
                Ok(Some(artifact)) => artifacts.push(artifact),
                Ok(None) => {}
                Err(error) => {
                    errors.push(format!("{}: {error}", path_for_report(&path, repo_root)))
                }
            }
        }
    }
    artifacts.sort_by_key(|artifact| artifact["path"].as_str().unwrap_or("").to_string());
    errors.sort();
    let digest = digest_json_rows(&root_identities, &artifacts, &errors)?;
    Ok(json!({
        "schema": STAGE2_SNAPSHOT_SCHEMA,
        "captured_at": timestamp_string(),
        "repo_root": repo_root.to_string_lossy(),
        "roots": root_identities,
        "artifact_count": artifacts.len(),
        "artifacts": artifacts,
        "errors": errors,
        "digest_schema": STAGE2_SNAPSHOT_DIGEST_SCHEMA,
        "digest": digest,
    }))
}

fn collect_stage2_paths(
    root: &Path,
    repo_root: &Path,
    paths: &mut Vec<PathBuf>,
    errors: &mut Vec<String>,
) {
    let entries = match fs::read_dir(root) {
        Ok(entries) => entries,
        Err(error) => {
            errors.push(format!(
                "{}: read stage2 directory: {error}",
                path_for_report(root, repo_root)
            ));
            return;
        }
    };
    for entry in entries {
        let entry = match entry {
            Ok(entry) => entry,
            Err(error) => {
                errors.push(format!(
                    "{}: enumerate stage2 directory entry: {error}",
                    path_for_report(root, repo_root)
                ));
                continue;
            }
        };
        let path = entry.path();
        paths.push(path.clone());
        match entry.file_type() {
            Ok(kind) if kind.is_dir() && !kind.is_symlink() => {
                collect_stage2_paths(&path, repo_root, paths, errors);
            }
            Ok(_) => {}
            Err(error) => errors.push(format!(
                "{}: inspect stage2 directory entry type: {error}",
                path_for_report(&path, repo_root)
            )),
        }
    }
}

fn stage2_path_for_report(path: &Path, repo_root: &Path) -> std::io::Result<String> {
    let report_path = path.strip_prefix(repo_root).unwrap_or(path);
    report_path.to_str().map(str::to_owned).ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!("stage2 artifact path is not valid UTF-8: {report_path:?}"),
        )
    })
}

fn stage2_metadata_unchanged(before: &fs::Metadata, after: &fs::Metadata) -> bool {
    let before_type = before.file_type();
    let after_type = after.file_type();
    if before_type.is_file() != after_type.is_file()
        || before_type.is_dir() != after_type.is_dir()
        || before_type.is_symlink() != after_type.is_symlink()
    {
        return false;
    }

    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;

        before.dev() == after.dev()
            && before.ino() == after.ino()
            && before.mode() == after.mode()
            && before.nlink() == after.nlink()
            && before.uid() == after.uid()
            && before.gid() == after.gid()
            && before.len() == after.len()
            && before.mtime() == after.mtime()
            && before.mtime_nsec() == after.mtime_nsec()
            && before.ctime() == after.ctime()
            && before.ctime_nsec() == after.ctime_nsec()
    }
    #[cfg(windows)]
    {
        use std::os::windows::fs::MetadataExt as _;

        before.file_attributes() == after.file_attributes()
            && before.creation_time() == after.creation_time()
            && before.last_write_time() == after.last_write_time()
            && before.file_size() == after.file_size()
            && before.volume_serial_number() == after.volume_serial_number()
            && before.number_of_links() == after.number_of_links()
            && before.file_index() == after.file_index()
    }
    #[cfg(not(any(unix, windows)))]
    {
        before.len() == after.len() && before.modified().ok() == after.modified().ok()
    }
}

fn stage2_changed_during_capture(path: &Path) -> std::io::Error {
    std::io::Error::other(format!(
        "stage2 artifact changed while its snapshot was being captured: {}",
        path.display()
    ))
}

fn stable_stage2_file_sha256(
    path: &Path,
    initial_metadata: &fs::Metadata,
) -> std::io::Result<String> {
    let mut file = File::open(path)?;
    let opened_before = file.metadata()?;
    if !opened_before.is_file() || !stage2_metadata_unchanged(initial_metadata, &opened_before) {
        return Err(stage2_changed_during_capture(path));
    }
    let digest = trust_types::digest::stable_sha256_hex_reader(&mut file)?;
    let opened_after = file.metadata()?;
    let path_after = fs::symlink_metadata(path)?;
    if !stage2_metadata_unchanged(&opened_before, &opened_after)
        || !stage2_metadata_unchanged(initial_metadata, &path_after)
    {
        return Err(stage2_changed_during_capture(path));
    }
    Ok(digest)
}

fn snapshot_stage2_artifact(path: &Path, repo_root: &Path) -> std::io::Result<Option<Value>> {
    let metadata = fs::symlink_metadata(path)?;
    if metadata.is_dir() {
        let after = fs::symlink_metadata(path)?;
        if !stage2_metadata_unchanged(&metadata, &after) {
            return Err(stage2_changed_during_capture(path));
        }
        return Ok(None);
    }
    let kind = if metadata.file_type().is_symlink() {
        "symlink"
    } else if metadata.is_file() {
        "file"
    } else {
        "other"
    };
    let modified = metadata.modified()?;
    let modified_ns = modified
        .duration_since(UNIX_EPOCH)
        .map_err(|error| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("stage2 artifact modification time predates the Unix epoch: {error}"),
            )
        })?
        .as_nanos();
    let mut object = Map::new();
    insert_str(&mut object, "path", stage2_path_for_report(path, repo_root)?);
    insert_str(&mut object, "kind", kind);
    object.insert("size_bytes".to_string(), json!(metadata.len()));
    object.insert("mtime_ns".to_string(), json!(modified_ns));
    if kind == "file" {
        insert_str(&mut object, "sha256", stable_stage2_file_sha256(path, &metadata)?);
    } else if kind == "symlink" {
        let target = fs::read_link(path)?;
        let target = target.to_str().ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("stage2 symlink target is not valid UTF-8: {target:?}"),
            )
        })?;
        let after = fs::symlink_metadata(path)?;
        if !stage2_metadata_unchanged(&metadata, &after) {
            return Err(stage2_changed_during_capture(path));
        }
        object.insert("link_target".to_string(), json!(target));
        object.insert("sha256".to_string(), Value::Null);
    } else {
        let after = fs::symlink_metadata(path)?;
        if !stage2_metadata_unchanged(&metadata, &after) {
            return Err(stage2_changed_during_capture(path));
        }
        object.insert("sha256".to_string(), Value::Null);
    }
    Ok(Some(Value::Object(object)))
}

fn compare_stage2_snapshots(
    before: &Value,
    after: &Value,
    before_path: Option<&Path>,
    after_path: Option<&Path>,
    report_dir: &Path,
) -> Value {
    let changes = diff_stage2_artifacts(before, after);
    let before_errors = before["errors"].as_array().cloned().unwrap_or_default();
    let after_errors = after["errors"].as_array().cloned().unwrap_or_default();
    let mutated = !changes.is_empty() || !before_errors.is_empty() || !after_errors.is_empty();
    json!({
        "status": if mutated { TOOLCHAIN_MUTATED } else { "unchanged" },
        "classification": if mutated { TOOLCHAIN_MUTATED } else { "as-expected" },
        "monitored": true,
        "reason": if mutated { "stage2 artifacts changed or could not be read consistently" } else { "stage2 artifacts were unchanged between preflight snapshots" },
        "roots": before["roots"].clone(),
        "before_snapshot_path": before_path.map(|path| relative_to_report(path, report_dir)),
        "after_snapshot_path": after_path.map(|path| relative_to_report(path, report_dir)),
        "before_digest": before["digest"].clone(),
        "after_digest": after["digest"].clone(),
        "artifact_count_before": before["artifact_count"].clone(),
        "artifact_count_after": after["artifact_count"].clone(),
        "changed_artifact_count": changes.len(),
        "changed_artifacts": changes.into_iter().take(50).collect::<Vec<_>>(),
        "change_limit": 50,
        "before_errors": before_errors,
        "after_errors": after_errors,
    })
}

fn diff_stage2_artifacts(before: &Value, after: &Value) -> Vec<Value> {
    let before_map = snapshot_artifacts_by_path(before);
    let after_map = snapshot_artifacts_by_path(after);
    let paths: BTreeSet<String> = before_map.keys().chain(after_map.keys()).cloned().collect();
    let mut changes = Vec::new();
    for path in paths {
        let before_value = before_map.get(&path);
        let after_value = after_map.get(&path);
        if before_value == after_value {
            continue;
        }
        changes.push(json!({
            "path": path,
            "change": if before_value.is_none() { "added" } else if after_value.is_none() { "removed" } else { "modified" },
            "before": before_value.cloned(),
            "after": after_value.cloned(),
        }));
    }
    changes
}

fn snapshot_artifacts_by_path(snapshot: &Value) -> BTreeMap<String, Value> {
    snapshot["artifacts"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|artifact| {
            artifact["path"].as_str().map(|path| (path.to_string(), artifact.clone()))
        })
        .collect()
}

fn toolchain_integrity_not_applicable(reason: &str) -> Value {
    json!({
        "status": "not_applicable",
        "classification": "not_applicable",
        "monitored": false,
        "reason": reason,
    })
}

fn annotate_toolchain_integrity(
    rows: &mut [Value],
    integrity: &Value,
    monitored_slots: &BTreeSet<String>,
) {
    if integrity["status"].as_str() != Some(TOOLCHAIN_MUTATED) {
        return;
    }
    for row in rows {
        if value_str(row, "slot").is_some_and(|slot| monitored_slots.contains(slot)) {
            set_str(row, "toolchain_integrity_status", TOOLCHAIN_MUTATED);
            if let Some(reason) = integrity["reason"].as_str() {
                set_str(row, "toolchain_integrity_reason", reason);
            }
        }
    }
}

fn write_named_report(value: &Value, path: &Path) -> Result<PathBuf, ProgramIndexError> {
    write_report(value, path)?;
    Ok(path.to_path_buf())
}

fn write_report(value: &Value, path: &Path) -> Result<(), ProgramIndexError> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| {
        ProgramIndexError::new(format!("serialize {}: {error}", path.display()))
    })?;
    bytes.push(b'\n');
    crate::durable_io::atomic_write_private(path, &bytes).map_err(|error| {
        ProgramIndexError::new(format!("durably publish {}: {error}", path.display()))
    })
}

fn print_terminal_summary(report_path: &Path) {
    let Ok(text) = crate::input_limits::read_bounded_utf8_file(
        report_path,
        crate::input_limits::MAX_SAVED_PROOF_REPORT_BYTES,
    ) else {
        println!("program-index report: {}", report_path.display());
        return;
    };
    let Ok(report) = serde_json::from_str::<Value>(&text) else {
        println!("program-index report: {}", report_path.display());
        return;
    };
    let summary = &report["summary"];
    println!("program-index report: {}", report_path.display());
    println!(
        "program-index status: passed={} failed={} excepted={} skipped={} raw_failed={} toolchain={}",
        summary["passed"].as_u64().unwrap_or(0),
        summary["failed"].as_u64().unwrap_or(0),
        summary["excepted"].as_u64().unwrap_or(0),
        summary["skipped"].as_u64().unwrap_or(0),
        summary["raw_failed_before_exceptions"].as_u64().unwrap_or(0),
        summary["toolchain_integrity_status"].as_str().unwrap_or("unknown"),
    );
    println!(
        "program-index coverage: known_good={} known_flawed_rejection={} backward_pass={} trust_cg_exceptions={} runtime_parity={} unsupported_frontend_lowering={} unsupported_mir={} repair_evidence={} proof_design_verifier={}",
        summary["known_good_pass"]["status"].as_str().unwrap_or("unknown"),
        summary["known_flawed_rejection"]["status"].as_str().unwrap_or("unknown"),
        summary["backward_pass"]["status"].as_str().unwrap_or("unknown"),
        summary["trust_cg_exceptions"]["status"].as_str().unwrap_or("unknown"),
        summary["runtime_parity"]["status"].as_str().unwrap_or("unknown"),
        summary["unsupported_frontend_lowering_gate"]["status"].as_str().unwrap_or("unknown"),
        summary["unsupported_mir_gate"]["status"].as_str().unwrap_or("unknown"),
        summary["repair_evidence"]["status"].as_str().unwrap_or("unknown"),
        summary["proof_design_verifier_evidence"]["status"].as_str().unwrap_or("unknown"),
    );
    if report["required_slots"]["status"].as_str() == Some("missing_required_slots") {
        let missing = report["required_slots"]["missing"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .collect::<Vec<_>>()
            .join(", ");
        println!("program-index missing required slots: {missing}");
    }
    if report["runtime_parity"]["requested"].as_bool() == Some(true) {
        println!(
            "program-index runtime parity: status={} passed={} failed={} not_applicable={}",
            report["runtime_parity"]["status"].as_str().unwrap_or("unknown"),
            report["runtime_parity"]["summary"]["passed"].as_u64().unwrap_or(0),
            report["runtime_parity"]["summary"]["failed"].as_u64().unwrap_or(0),
            report["runtime_parity"]["summary"]["not_applicable"].as_u64().unwrap_or(0),
        );
    }
}

fn print_programs(programs: &[Program]) {
    println!("{:32} {:8} {:14} source", "id", "variant", "suite");
    println!("{:32} {:8} {:14} {}", "-".repeat(32), "-".repeat(8), "-".repeat(14), "-".repeat(40));
    for program in programs {
        println!(
            "{:32} {:8} {:14} {}",
            program.id, program.variant, program.suite, program.relative_path
        );
    }
}

fn repo_head(root: &Path) -> Option<String> {
    crate::controlled_git::canonical_head(
        root,
        "benchmark repository HEAD probe",
        IDENTITY_PROBE_MAX_STREAM_BYTES,
        GIT_PROBE_TIMEOUT,
    )
    .ok()
}

fn performance_platform_identity(
    bindings: &[SlotBinding],
    rows: &[Value],
    runtime_parity: &Value,
    repo_root: &Path,
) -> Value {
    let measured_slots = measured_performance_slots(rows, runtime_parity);
    let mut blockers = BTreeSet::new();
    let mut observed_triples = BTreeSet::new();
    let mut probe_cache = BTreeMap::<String, Value>::new();
    let mut slot_probes = Vec::new();

    if measured_slots.is_empty() {
        blockers.insert("no compiler slot contributed measured performance data".to_string());
    }

    for slot in &measured_slots {
        let Some(binding) = bindings.iter().find(|binding| binding.id == *slot) else {
            blockers.insert(format!("measured compiler slot {slot} has no resolved binding"));
            continue;
        };
        let Some(binary) = binding.binary.as_deref() else {
            blockers.insert(format!("measured compiler slot {slot} has no executable binary"));
            continue;
        };
        let probe = probe_cache
            .entry(binary.to_string())
            .or_insert_with(|| compiler_identity_probe(binary, &["-vV"]))
            .clone();
        let declared_host = if probe_failed(&probe) {
            blockers.insert(format!(
                "measured compiler slot {slot} -vV probe status is {}",
                probe["status"].as_str().unwrap_or("unknown")
            ));
            None
        } else {
            probe_field(&probe_text(&probe), "host")
        };
        match declared_host.as_deref() {
            Some(triple) if valid_compiler_host_triple(triple) => {
                observed_triples.insert(triple.to_string());
            }
            Some(triple) => {
                blockers.insert(format!(
                    "measured compiler slot {slot} declared invalid host triple `{triple}`"
                ));
            }
            None if !probe_failed(&probe) => {
                blockers.insert(format!(
                    "measured compiler slot {slot} -vV output did not declare host"
                ));
            }
            None => {}
        }
        slot_probes.push(json!({
            "slot": slot,
            "binary": path_for_report(Path::new(binary), repo_root),
            "declared_host": declared_host,
            "probe": probe,
        }));
    }

    if observed_triples.len() > 1 {
        blockers.insert(format!(
            "measured compiler slots declared conflicting host triples: {}",
            observed_triples.iter().cloned().collect::<Vec<_>>().join(", ")
        ));
    }
    let observed_triples = observed_triples.into_iter().collect::<Vec<_>>();
    let consistent_triple =
        (blockers.is_empty() && observed_triples.len() == 1).then(|| observed_triples[0].clone());
    let target_arch = consistent_triple
        .as_deref()
        .and_then(|triple| triple.split_once('-').map(|(arch, _)| arch.to_string()));
    let status = if consistent_triple.is_some() { "passed" } else { "blocked" };

    json!({
        "schema": STRICT_SUPERIORITY_PLATFORM_IDENTITY_SCHEMA,
        "status": status,
        "source": "selected measured compiler `-vV` host fields",
        "measurement_scope": "default compiler targets; program-index passes no --target option",
        "target_arch": target_arch,
        "target_triple": consistent_triple,
        "host_arch": target_arch,
        "host_triple": consistent_triple,
        "runner": {
            "arch": env::consts::ARCH,
            "os": env::consts::OS,
            "family": env::consts::FAMILY,
        },
        "measured_slots": measured_slots,
        "observed_host_triples": observed_triples,
        "slot_probes": slot_probes,
        "blockers": blockers.into_iter().collect::<Vec<_>>(),
    })
}

fn measured_performance_slots(rows: &[Value], runtime_parity: &Value) -> BTreeSet<String> {
    let mut slots = rows
        .iter()
        .filter(|row| {
            value_str(row, "slot_mode") == Some("compile")
                && value_str(row, "outcome") == Some("passed")
                && row["measurement_profile"]["status"].as_str() == Some("measured")
                && row["sample_count"].as_u64().unwrap_or(0) > 0
        })
        .filter_map(|row| value_str(row, "slot").map(str::to_string))
        .collect::<BTreeSet<_>>();
    slots.extend(
        runtime_parity["rows"]
            .as_array()
            .into_iter()
            .flatten()
            .filter(|row| {
                row["runtime_participant"].as_bool() == Some(true)
                    && value_str(row, "runtime_classification") == Some("runtime-parity")
                    && value_str(row, "build_status") == Some("compile_pass")
                    && value_str(row, "run_status") == Some("run_complete")
            })
            .filter_map(|row| value_str(row, "slot").map(str::to_string)),
    );
    slots
}

fn valid_compiler_host_triple(value: &str) -> bool {
    value.len() <= 255
        && value.contains('-')
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'))
}

fn repo_dirty(root: &Path) -> Option<bool> {
    git_status_porcelain_lines(root).map(|lines| !lines.is_empty())
}

fn repo_dirty_metadata(root: &Path) -> Value {
    let Some(lines) = git_status_porcelain_lines(root) else {
        return json!({"available": false, "dirty": null, "porcelain_v1": []});
    };
    json!({
        "available": true,
        "dirty": !lines.is_empty(),
        "porcelain_v1": lines,
        "untracked_files": "all",
        "ignore_submodules": "none",
    })
}

fn git_status_porcelain_lines(root: &Path) -> Option<Vec<String>> {
    crate::controlled_git::exact_status_porcelain_v1(
        root,
        "benchmark repository cleanliness probe",
        GIT_PROBE_MAX_STREAM_BYTES,
        GIT_PROBE_TIMEOUT,
    )
    .ok()
}

fn discover_repo_root() -> Result<PathBuf, std::io::Error> {
    if let Ok(root) = env::var("TRUST_REPO_ROOT") {
        let root = PathBuf::from(root);
        if root.join("examples/bench/program_index/index.json").is_file() {
            return Ok(root);
        }
    }
    let cwd = env::current_dir()?;
    for ancestor in cwd.ancestors() {
        if ancestor.join("examples/bench/program_index/index.json").is_file() {
            return Ok(ancestor.to_path_buf());
        }
    }
    Ok(Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .to_path_buf())
}

fn value_after<'a>(
    args: &'a [String],
    index: usize,
    option: &str,
) -> Result<&'a str, ProgramIndexError> {
    args.get(index + 1)
        .map(String::as_str)
        .filter(|value| !value.starts_with('-'))
        .ok_or_else(|| ProgramIndexError::new(format!("{option} requires a value")))
}

fn value_in<'a>(option: &'a str, prefix: &str) -> &'a str {
    option.strip_prefix(prefix).expect("prefix checked")
}

fn deprecated_trust_cg_cli_spelling(deprecated: &str, canonical: &str) -> ProgramIndexError {
    ProgramIndexError::new(format!("deprecated option `{deprecated}`; use `{canonical}`"))
}

fn reject_deprecated_trust_cg_slot(slot: &str, option: &str) -> Result<(), ProgramIndexError> {
    if slot == "trust_cg" {
        return Err(ProgramIndexError::new(format!(
            "{option} uses deprecated slot spelling `trust_cg`; use `trust-cg`"
        )));
    }
    Ok(())
}

fn reject_deprecated_slot_bin_value(value: &str) -> Result<(), ProgramIndexError> {
    if let Some((slot, _)) = value.split_once('=') {
        reject_deprecated_trust_cg_slot(slot, "--slot-bin")?;
    }
    Ok(())
}

fn parse_slot_values(
    args: &[String],
    start: usize,
) -> Result<(Vec<String>, usize), ProgramIndexError> {
    let mut slots = Vec::new();
    let mut index = start;
    while index < args.len() && !args[index].starts_with('-') {
        for slot in split_slot_list(&args[index])? {
            slots.push(slot);
        }
        index += 1;
    }
    if slots.is_empty() {
        return Err(ProgramIndexError::new("--slots requires at least one slot"));
    }
    Ok((slots, index))
}

fn split_slot_list(value: &str) -> Result<Vec<String>, ProgramIndexError> {
    let slots: Vec<String> =
        value.split(',').filter(|slot| !slot.is_empty()).map(str::to_string).collect();
    for slot in &slots {
        reject_deprecated_trust_cg_slot(slot, "--slots")?;
        if slot_profile(slot).is_none() {
            return Err(ProgramIndexError::new(format!("unknown slot `{slot}`")));
        }
    }
    if slots.is_empty() {
        return Err(ProgramIndexError::new("--slots requires at least one slot"));
    }
    Ok(slots)
}

fn parse_variant(value: &str) -> Result<String, ProgramIndexError> {
    match value {
        "good" | "flawed" => Ok(value.to_string()),
        other => {
            Err(ProgramIndexError::new(format!("--variant must be good or flawed, got `{other}`")))
        }
    }
}

fn parse_trust_cg_mode(value: &str) -> Result<String, ProgramIndexError> {
    match value {
        "report" | "enforce" => Ok(value.to_string()),
        other => Err(ProgramIndexError::new(format!(
            "--trust-cg-mode must be report or enforce, got `{other}`"
        ))),
    }
}

fn parse_build_profile(value: &str) -> Result<BuildProfile, ProgramIndexError> {
    match value {
        "debug" => Ok(BuildProfile::Debug),
        "release" => Ok(BuildProfile::Release),
        other => Err(ProgramIndexError::new(format!(
            "--build-profile must be debug or release, got `{other}`"
        ))),
    }
}

fn parse_compile_measurement_mode(
    value: &str,
) -> Result<CompileMeasurementMode, ProgramIndexError> {
    match value {
        "cold-artifact" | "cold_artifact" | "cold" => Ok(CompileMeasurementMode::ColdArtifact),
        "warm-incremental" | "warm_incremental" | "incremental" => {
            Ok(CompileMeasurementMode::WarmIncremental)
        }
        other => Err(ProgramIndexError::new(format!(
            "--compile-measurement must be cold-artifact or warm-incremental, got `{other}`"
        ))),
    }
}

fn parse_usize(value: &str, option: &str) -> Result<usize, ProgramIndexError> {
    value
        .parse()
        .map_err(|_| ProgramIndexError::new(format!("{option} must be a positive integer")))
}

fn parse_u64(value: &str, option: &str) -> Result<u64, ProgramIndexError> {
    value
        .parse()
        .map_err(|_| ProgramIndexError::new(format!("{option} must be a positive integer")))
}

fn is_help_arg(value: &str) -> bool {
    matches!(value, "help" | "--help" | "-h")
}

fn absolutize(path: &Path, base: &Path) -> PathBuf {
    if path.is_absolute() { path.to_path_buf() } else { base.join(path) }
}

fn trustc_candidates(repo_root: &Path) -> Vec<PathBuf> {
    let mut candidates = vec![repo_root.join("build/host/stage2/bin/trustc")];
    let build_dir = repo_root.join("build");
    if let Ok(entries) = fs::read_dir(build_dir) {
        for entry in entries.flatten() {
            let stage2_bin = entry.path().join("stage2/bin");
            candidates.push(stage2_bin.join("trustc"));
        }
    }
    candidates
}

fn resolve_executable(value: &str) -> Option<String> {
    if value.contains('/') || value.contains('\\') {
        let path = PathBuf::from(value);
        return is_executable_path(&path).then(|| path.to_string_lossy().into_owned());
    }
    which(value)
}

fn resolve_absolute_executable(value: &str) -> Option<String> {
    let path = PathBuf::from(value);
    (path.is_absolute() && is_executable_path(&path)).then(|| path.to_string_lossy().into_owned())
}

fn is_executable_string(value: &str) -> bool {
    resolve_executable(value).is_some()
}

fn which(program: &str) -> Option<String> {
    let paths = env::var_os("PATH")?;
    for dir in env::split_paths(&paths) {
        let candidate = dir.join(program);
        if is_executable_path(&candidate) {
            return Some(candidate.to_string_lossy().into_owned());
        }
    }
    None
}

fn is_executable_path(path: &Path) -> bool {
    if !path.is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::metadata(path)
            .map(|metadata| metadata.permissions().mode() & 0o111 != 0)
            .unwrap_or(false)
    }
    #[cfg(not(unix))]
    {
        true
    }
}

fn sanitize_crate_name(value: &str) -> String {
    let mut sanitized: String = value
        .chars()
        .map(|ch| if ch.is_ascii_alphanumeric() || ch == '_' { ch } else { '_' })
        .collect();
    if sanitized.is_empty() || sanitized.chars().next().is_some_and(|ch| ch.is_ascii_digit()) {
        sanitized.insert_str(0, "bench_");
    }
    sanitized
}

fn runtime_executable_name(program: &Program) -> String {
    format!("{}{}", sanitize_crate_name(&program.id), env::consts::EXE_SUFFIX)
}

fn command_display(command: &[String]) -> String {
    command
        .iter()
        .map(|arg| {
            if arg.chars().all(|ch| ch.is_ascii_alphanumeric() || "-_./:=+".contains(ch)) {
                arg.clone()
            } else {
                format!("'{}'", arg.replace('\'', "'\\''"))
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

fn file_size_or_none(path: &Path) -> Option<u64> {
    fs::metadata(path).map(|metadata| metadata.len()).ok()
}

fn file_sha256_or_none(path: &Path) -> Result<Option<String>, ProgramIndexError> {
    if !path.is_file() {
        return Ok(None);
    }
    file_sha256(path)
        .map(Some)
        .map_err(|error| ProgramIndexError::new(format!("hash {}: {error}", path.display())))
}

fn file_sha256(path: &Path) -> std::io::Result<String> {
    let mut file = File::open(path)?;
    trust_types::digest::stable_sha256_hex_reader(&mut file)
}


fn update_digest_field(hasher: &mut Sha256, domain: &[u8], bytes: &[u8]) {
    hasher.update((domain.len() as u64).to_be_bytes());
    hasher.update(domain);
    hasher.update((bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
}

fn digest_json_rows<T: Serialize>(
    roots: &[String],
    rows: &[T],
    errors: &[String],
) -> Result<String, ProgramIndexError> {
    let mut hasher = Sha256::new();
    hasher.update(STAGE2_SNAPSHOT_DIGEST_SCHEMA.as_bytes());
    hasher.update([0]);
    hasher.update((roots.len() as u64).to_be_bytes());
    for root in roots {
        update_digest_field(&mut hasher, b"root", root.as_bytes());
    }
    hasher.update((rows.len() as u64).to_be_bytes());
    for (index, row) in rows.iter().enumerate() {
        let encoded = serde_json::to_vec(row).map_err(|error| {
            ProgramIndexError::new(format!("serialize stage2 snapshot digest row {index}: {error}"))
        })?;
        update_digest_field(&mut hasher, b"row", &encoded);
    }
    hasher.update((errors.len() as u64).to_be_bytes());
    for error in errors {
        update_digest_field(&mut hasher, b"error", error.as_bytes());
    }
    Ok(trust_types::digest::lowercase_hex(hasher.finalize().as_slice()))
}



fn path_for_report(path: &Path, repo_root: &Path) -> String {
    path.strip_prefix(repo_root)
        .map(Path::to_path_buf)
        .unwrap_or_else(|_| path.to_path_buf())
        .to_string_lossy()
        .into_owned()
}

fn relative_to_report(path: &Path, report_dir: &Path) -> String {
    path.strip_prefix(report_dir)
        .map(Path::to_path_buf)
        .unwrap_or_else(|_| path.to_path_buf())
        .to_string_lossy()
        .into_owned()
}

fn path_if_exists(repo_root: &Path, path: &Path) -> Option<String> {
    path.exists().then(|| path_for_report(path, repo_root))
}

fn string_counts(rows: &[Value], key: &str) -> Value {
    let mut counts = BTreeMap::<String, u64>::new();
    for row in rows {
        if let Some(value) = value_str(row, key) {
            *counts.entry(value.to_string()).or_default() += 1;
        }
    }
    json!(counts)
}

fn nested_string_counts(rows: &[Value], path: &[&str]) -> Value {
    let mut counts = BTreeMap::<String, u64>::new();
    for row in rows {
        let mut value = row;
        for key in path {
            value = &value[*key];
        }
        if let Some(value) = value.as_str() {
            *counts.entry(value.to_string()).or_default() += 1;
        }
    }
    json!(counts)
}

fn outcome_counts_by_string_key(rows: &[Value], key: &str) -> Value {
    let groups: BTreeSet<String> =
        rows.iter().filter_map(|row| value_str(row, key).map(str::to_string)).collect();
    let mut object = Map::new();
    for group in groups {
        let selected: Vec<Value> = rows
            .iter()
            .filter(|row| value_str(row, key) == Some(group.as_str()))
            .cloned()
            .collect();
        object.insert(group, Value::Object(outcome_counts(&selected, "outcome")));
    }
    Value::Object(object)
}

fn numeric_sum(rows: &[Value], key: &str) -> f64 {
    rows.iter().filter_map(|row| row[key].as_f64()).sum()
}

fn sample_count_sum(rows: &[Value]) -> u64 {
    rows.iter().map(|row| row["sample_count"].as_u64().unwrap_or(0)).sum()
}

fn numeric_stats_f64(values: &[f64]) -> Value {
    let mut sorted = values.iter().copied().filter(|value| value.is_finite()).collect::<Vec<_>>();
    if sorted.is_empty() {
        return Value::Null;
    }
    sorted.sort_by(|left, right| left.total_cmp(right));
    let mean = sorted.iter().sum::<f64>() / sorted.len() as f64;
    let variance =
        sorted.iter().map(|value| (value - mean).powi(2)).sum::<f64>() / sorted.len() as f64;
    json!({
        "count": sorted.len(),
        "min": round_seconds(sorted[0]),
        "max": round_seconds(sorted[sorted.len() - 1]),
        "median": median_sorted_f64(&sorted).map(round_seconds),
        "p50": p50_sorted_f64(&sorted).map(round_seconds),
        "stdev": round_seconds(variance.sqrt()),
    })
}

fn numeric_stats_i64(values: &[i64]) -> Value {
    if values.is_empty() {
        return Value::Null;
    }
    let mut sorted = values.to_vec();
    sorted.sort_unstable();
    let mean = sorted.iter().map(|value| *value as f64).sum::<f64>() / sorted.len() as f64;
    let variance = sorted.iter().map(|value| (*value as f64 - mean).powi(2)).sum::<f64>()
        / sorted.len() as f64;
    json!({
        "count": sorted.len(),
        "min": sorted[0],
        "max": sorted[sorted.len() - 1],
        "median": median_sorted_i64(&sorted).map(round_seconds),
        "p50": p50_sorted_i64(&sorted),
        "stdev": round_seconds(variance.sqrt()),
    })
}

fn median_f64(values: &[f64]) -> Option<f64> {
    let mut sorted = values.iter().copied().filter(|value| value.is_finite()).collect::<Vec<_>>();
    if sorted.is_empty() {
        return None;
    }
    sorted.sort_by(|left, right| left.total_cmp(right));
    median_sorted_f64(&sorted)
}

fn median_sorted_f64(sorted: &[f64]) -> Option<f64> {
    if sorted.is_empty() {
        return None;
    }
    let midpoint = sorted.len() / 2;
    if sorted.len() % 2 == 0 {
        Some((sorted[midpoint - 1] + sorted[midpoint]) / 2.0)
    } else {
        Some(sorted[midpoint])
    }
}

fn median_sorted_i64(sorted: &[i64]) -> Option<f64> {
    if sorted.is_empty() {
        return None;
    }
    let midpoint = sorted.len() / 2;
    if sorted.len() % 2 == 0 {
        Some((sorted[midpoint - 1] as f64 + sorted[midpoint] as f64) / 2.0)
    } else {
        Some(sorted[midpoint] as f64)
    }
}

fn p50_sorted_f64(sorted: &[f64]) -> Option<f64> {
    (!sorted.is_empty()).then(|| sorted[nearest_rank_index(sorted.len(), 0.50)])
}

fn p50_sorted_i64(sorted: &[i64]) -> Option<i64> {
    (!sorted.is_empty()).then(|| sorted[nearest_rank_index(sorted.len(), 0.50)])
}

fn nearest_rank_index(len: usize, percentile: f64) -> usize {
    (((percentile * len as f64).ceil() as usize).saturating_sub(1)).min(len.saturating_sub(1))
}

fn resource_f64_values(samples: &[SlotRunSample], key: &str) -> Vec<f64> {
    samples
        .iter()
        .filter_map(|sample| sample.result.resource_usage.get(key).and_then(Value::as_f64))
        .filter(|value| value.is_finite())
        .collect()
}

fn resource_i64_values(samples: &[SlotRunSample], key: &str) -> Vec<i64> {
    samples
        .iter()
        .filter_map(|sample| {
            let value = sample.result.resource_usage.get(key)?;
            value.as_i64().or_else(|| value.as_u64().and_then(|value| i64::try_from(value).ok()))
        })
        .collect()
}

fn common_resource_str(samples: &[SlotRunSample], key: &str) -> Option<String> {
    let first = first_resource_str(samples, key)?;
    samples
        .iter()
        .all(|sample| sample.result.resource_usage.get(key).and_then(Value::as_str) == Some(first))
        .then(|| first.to_string())
}

fn first_resource_str<'a>(samples: &'a [SlotRunSample], key: &str) -> Option<&'a str> {
    samples.iter().find_map(|sample| sample.result.resource_usage.get(key).and_then(Value::as_str))
}

fn normalize_peak_rss_raw_with_unit(raw: i64, unit: &str) -> Option<i64> {
    match unit {
        "bytes" => Some(raw),
        "kilobytes" => raw.checked_mul(1024),
        _ => None,
    }
}

fn string_counts_from_values<'a>(values: impl Iterator<Item = &'a str>) -> Value {
    let mut counts = BTreeMap::<String, u64>::new();
    for value in values {
        *counts.entry(value.to_string()).or_default() += 1;
    }
    json!(counts)
}

fn max_i64_or_none(rows: &[Value], key: &str) -> Option<i64> {
    rows.iter().filter_map(|row| row[key].as_i64()).max()
}

fn option_i64(value: Option<i64>) -> Value {
    value.map_or(Value::Null, |value| json!(value))
}

fn value_str<'a>(value: &'a Value, key: &str) -> Option<&'a str> {
    value.get(key).and_then(Value::as_str)
}

fn insert_str(object: &mut Map<String, Value>, key: &str, value: impl AsRef<str>) {
    object.insert(key.to_string(), json!(value.as_ref()));
}

fn insert_optional_str(object: &mut Map<String, Value>, key: &str, value: Option<String>) {
    object.insert(key.to_string(), value.map_or(Value::Null, |value| json!(value)));
}

fn insert_optional_u64(object: &mut Map<String, Value>, key: &str, value: Option<u64>) {
    object.insert(key.to_string(), value.map_or(Value::Null, |value| json!(value)));
}

fn insert_optional_i32(object: &mut Map<String, Value>, key: &str, value: Option<i32>) {
    object.insert(key.to_string(), value.map_or(Value::Null, |value| json!(value)));
}

fn insert_arr(object: &mut Map<String, Value>, key: &str, value: Vec<Value>) {
    object.insert(key.to_string(), Value::Array(value));
}

fn insert_obj(object: &mut Map<String, Value>, key: &str, value: impl Into<Value>) {
    object.insert(key.to_string(), value.into());
}

fn set_str(value: &mut Value, key: &str, new_value: impl AsRef<str>) {
    if let Some(object) = value.as_object_mut() {
        object.insert(key.to_string(), json!(new_value.as_ref()));
    }
}

fn set_arr(value: &mut Value, key: &str, new_value: Vec<Value>) {
    if let Some(object) = value.as_object_mut() {
        object.insert(key.to_string(), Value::Array(new_value));
    }
}

fn set_default(value: &mut Value, key: &str, new_value: Value) {
    if let Some(object) = value.as_object_mut() {
        object.entry(key.to_string()).or_insert(new_value);
    }
}

fn set_nested_str(value: &mut Value, path: &[&str], new_value: &str) {
    if path.is_empty() {
        return;
    }
    let mut current = value;
    for key in &path[..path.len() - 1] {
        let Some(next) = current.get_mut(*key) else {
            return;
        };
        current = next;
    }
    if let Some(object) = current.as_object_mut() {
        object.insert(path[path.len() - 1].to_string(), json!(new_value));
    }
}

fn round_seconds(value: f64) -> f64 {
    let rounded = (value * 1_000_000.0).round() / 1_000_000.0;
    if rounded == 0.0 { 0.0 } else { rounded }
}

fn default_run_id() -> String {
    format!("program-index-{}", unix_seconds())
}

fn timestamp_string() -> String {
    format!("unix:{}", unix_seconds())
}

fn unix_seconds() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_secs()
}

#[cfg(test)]
mod compiler_environment_tests {
    use super::*;

    struct SerializationFailure;

    impl Serialize for SerializationFailure {
        fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            Err(serde::ser::Error::custom("intentional serialization failure"))
        }
    }

    fn frontend_gate_row(stderr: &str, transport: Value) -> Value {
        json!({
            "slot": "trust-verify",
            "program_id": "fixture",
            "variant": "good",
            "expected": "verify_pass",
            "observed": "verify_pass",
            "outcome": "passed",
            "stderr_excerpt": stderr,
            "stderr_tail_excerpt": "",
            "transport": transport,
        })
    }

    fn frontend_transport(native_evidence: u64, publishable_proofs: u64) -> Value {
        let mut transport = empty_transport_summary_object();
        for (key, value) in [
            ("function_results", 1),
            ("obligation_results", 1),
            ("proved_results", 1),
            ("typed_transport_results", 1),
            ("native_trust_ir_results", native_evidence),
            ("proof_evidence_results", native_evidence),
            ("native_evidence_results", native_evidence),
            ("publishable_native_proof_results", publishable_proofs),
        ] {
            transport.insert(key.to_string(), json!(value));
        }
        Value::Object(transport)
    }

    #[test]
    fn benchmark_capture_limit_is_fail_closed_and_truncates_retention() {
        let temp = tempfile::tempdir().expect("capture fixture");
        let stdout = File::create(temp.path().join("stdout.log")).expect("stdout fixture");
        let stderr = File::create(temp.path().join("stderr.log")).expect("stderr fixture");
        stdout.set_len(MAX_COMMAND_LOG_BYTES + 1).expect("oversized sparse capture");
        assert!(capture_limit_exceeded(&stdout, &stderr));
        truncate_capture(&stdout);
        assert_eq!(stdout.metadata().expect("capture metadata").len(), MAX_COMMAND_LOG_BYTES);
    }

    #[test]
    fn stage2_snapshot_digest_is_domain_separated_length_bound_and_fail_closed() {
        let embedded_separator =
            digest_json_rows::<Value>(&[], &[], &["first\nerror:second".to_string()])
                .expect("digest embedded separator");
        let separate_errors =
            digest_json_rows::<Value>(&[], &[], &["first".to_string(), "second".to_string()])
                .expect("digest separate errors");
        assert_ne!(embedded_separator, separate_errors);

        let row = digest_json_rows(&[], &[json!("same bytes")], &[]).expect("digest row");
        let error = digest_json_rows::<Value>(&[], &[], &["\"same bytes\"".to_string()])
            .expect("digest error");
        assert_ne!(row, error, "row and error domains must never alias");

        let no_roots = digest_json_rows::<Value>(&[], &[], &[]).expect("digest no roots");
        let one_root = digest_json_rows::<Value>(&["build/host/stage2".to_string()], &[], &[])
            .expect("digest one root");
        assert_ne!(no_roots, one_root, "monitored roots are part of snapshot identity");

        let serialization_error = digest_json_rows(&[], &[SerializationFailure], &[])
            .expect_err("serialization failure must abort snapshot identity");
        assert!(
            serialization_error.0.contains("serialize stage2 snapshot digest row 0"),
            "{serialization_error}"
        );
    }

    #[test]
    fn stage2_snapshot_records_directory_enumeration_failures() {
        let temp = tempfile::tempdir().expect("stage2 enumeration fixture");
        let not_a_directory = temp.path().join("stage2-file");
        fs::write(&not_a_directory, b"not a directory").expect("write stage2 file fixture");
        let mut paths = Vec::new();
        let mut errors = Vec::new();

        collect_stage2_paths(&not_a_directory, temp.path(), &mut paths, &mut errors);

        assert!(paths.is_empty());
        assert_eq!(errors.len(), 1);
        assert!(errors[0].contains("read stage2 directory"), "{}", errors[0]);
    }

    #[cfg(unix)]
    #[test]
    fn stage2_snapshot_rejects_non_utf8_artifact_identity() {
        use std::ffi::OsString;
        use std::os::unix::ffi::OsStringExt as _;

        let root = Path::new("stage2-root");
        let path = root.join(OsString::from_vec(b"artifact-\xff".to_vec()));

        let error = stage2_path_for_report(&path, root)
            .expect_err("lossy stage2 artifact identities must fail closed");
        assert_eq!(error.kind(), std::io::ErrorKind::InvalidData);
        assert!(error.to_string().contains("not valid UTF-8"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn stage2_snapshot_rejects_symlink_roots() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().expect("stage2 symlink-root fixture");
        let real_root = temp.path().join("real-stage2");
        fs::create_dir(&real_root).expect("create real stage2 root");
        fs::write(real_root.join("trustc"), b"tool binary").expect("write stage2 artifact");
        let linked_root = temp.path().join("stage2");
        symlink(&real_root, &linked_root).expect("create stage2 root symlink");

        let snapshot = capture_stage2_snapshot(temp.path(), &[linked_root])
            .expect("symlink-root rejection snapshot");
        assert_eq!(snapshot["artifact_count"], 0);
        assert_eq!(snapshot["errors"].as_array().map(Vec::len), Some(1));
        assert!(snapshot["errors"][0].as_str().unwrap().contains("root is a symlink"));
    }

    #[test]
    fn benchmark_semantic_capture_rejects_non_utf8() {
        let temp = tempfile::tempdir().expect("capture fixture");
        let path = temp.path().join("stderr.log");
        fs::write(&path, [0xff]).expect("non-UTF-8 fixture");
        assert!(read_capture_text(&path).expect_err("non-UTF-8 must reject").0.contains("UTF-8"));
    }

    #[test]
    fn benchmark_capture_descriptor_is_readable_after_writing() {
        use std::io::Write as _;

        let temp = tempfile::tempdir().expect("capture fixture");
        let path = temp.path().join("stderr.log");
        let mut capture = open_capture_file(&path).expect("open capture");
        capture.write_all(b"TRUST_JSON:{}\n").expect("write capture");
        capture.flush().expect("flush capture");
        assert_eq!(
            read_capture_text_from_file(&mut capture, &path).expect("read capture descriptor"),
            "TRUST_JSON:{}\n"
        );
    }

    #[cfg(unix)]
    #[test]
    fn benchmark_capture_rejects_symlink_and_path_replacement() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().expect("capture fixture");
        let target = temp.path().join("target.log");
        fs::write(&target, b"target").expect("target fixture");
        let symlink_path = temp.path().join("symlink.log");
        symlink(&target, &symlink_path).expect("symlink fixture");
        assert!(open_capture_file(&symlink_path).is_err(), "capture followed a symlink leaf");

        let path = temp.path().join("capture.log");
        let capture = open_capture_file(&path).expect("open capture");
        let displaced = temp.path().join("displaced.log");
        fs::rename(&path, &displaced).expect("displace capture path");
        fs::write(&path, b"forged replacement").expect("replace capture path");
        assert!(
            validate_capture_path_identity(&capture, &path)
                .expect_err("path replacement must fail")
                .0
                .contains("changed")
        );
    }

    #[cfg(unix)]
    #[test]
    fn benchmark_runner_terminates_background_descendants_before_reaping_leader() {
        let temp = tempfile::tempdir().expect("process fixture");
        let pid_path = temp.path().join("background.pid");
        let marker_path = temp.path().join("background-survived");
        let command = vec![
            "/bin/sh".to_string(),
            "-c".to_string(),
            "sh -c 'trap \"\" HUP; sleep 1; printf survived > \"$MARKER_FILE\"' & \
             printf '%s' \"$!\" > \"$PID_FILE\"; exit 0"
                .to_string(),
        ];
        let env = BTreeMap::from([
            ("PID_FILE".to_string(), pid_path.to_string_lossy().into_owned()),
            ("MARKER_FILE".to_string(), marker_path.to_string_lossy().into_owned()),
        ]);
        let run = run_command_with_resource_usage(
            &command,
            temp.path(),
            &env,
            2,
            File::create(temp.path().join("stdout.log")).expect("stdout"),
            File::create(temp.path().join("stderr.log")).expect("stderr"),
        );
        assert_eq!(run.exit_code, Some(0));
        let pid: i32 =
            fs::read_to_string(&pid_path).expect("background pid").parse().expect("numeric pid");
        // A terminated grandchild can remain briefly as an init-owned zombie,
        // so kill(pid, 0) is not a reliable liveness assertion. Prove that it
        // cannot execute after cleanup instead.
        thread::sleep(Duration::from_millis(1_200));
        assert!(!marker_path.exists(), "background descendant {pid} survived and wrote its marker");
    }

    #[test]
    fn benchmark_timeout_rejects_unbounded_values() {
        let args = vec![format!("--timeout={}", MAX_BENCHMARK_TIMEOUT_SECONDS + 1)];
        assert!(
            parse_program_index_args(&args)
                .expect_err("unbounded timeout must fail")
                .0
                .contains("must not exceed")
        );
    }

    #[test]
    fn unsupported_frontend_lowering_detection_is_specific_and_transitional() {
        assert_eq!(
            unsupported_frontend_lowering_category(
                "compiler full verification requires typed TrustIr native evidence: failed to \
                 lower f into typed TrustIr NativeVerificationBundle input: unsupported operation"
            ),
            Some(UnsupportedFrontendLoweringCategory::TypedTrustIr)
        );
        assert_eq!(
            unsupported_frontend_lowering_category("3 unsupported THIR shape(s)"),
            Some(UnsupportedFrontendLoweringCategory::Thir)
        );
        assert_eq!(
            unsupported_frontend_lowering_category("error: UnsupportedMir in legacy verifier"),
            Some(UnsupportedFrontendLoweringCategory::LegacyMir)
        );
        assert_eq!(
            unsupported_frontend_lowering_category("unsupported operation in unrelated CLI mode"),
            None,
            "generic unsupported text must not be mislabeled as a frontend lowering gap"
        );
    }

    #[test]
    fn unsupported_frontend_gate_preserves_legacy_schema_and_requires_native_evidence() {
        let mut rows = vec![
            frontend_gate_row(
                "compiler full verification requires typed TrustIr native evidence: failed to \
                 lower fixture into typed TrustIr NativeVerificationBundle input",
                empty_transport_summary(),
            ),
            frontend_gate_row("", frontend_transport(1, 0)),
            frontend_gate_row("", frontend_transport(1, 1)),
        ];
        apply_unsupported_frontend_lowering_gate(&mut rows, &[], &BTreeMap::new());

        assert_eq!(rows[0]["unsupported_frontend_lowering_gate_status"], "unsupported_lowering");
        assert_eq!(rows[0]["unsupported_frontend_lowering_category"], "typed_trust_ir");
        assert_eq!(rows[0]["outcome"], "failed");
        assert_eq!(rows[1]["unsupported_frontend_lowering_gate_status"], "missing_native_evidence");
        assert_eq!(rows[1]["outcome"], "failed");
        assert_eq!(
            rows[2]["unsupported_frontend_lowering_gate_status"],
            "native_evidence_complete"
        );
        assert_eq!(rows[2]["outcome"], "passed");

        let summary = unsupported_frontend_lowering_gate_summary(&rows);
        assert_eq!(summary["schema"], UNSUPPORTED_FRONTEND_LOWERING_GATE_SCHEMA);
        assert_eq!(summary["status"], "failed");
        assert_eq!(summary["observation_scope"]["completeness_claim"], false);
        assert_eq!(
            summary["observation_scope"]["completeness_claim_scope"],
            "typed_trust_ir_verifier_ingress_only"
        );
        assert_eq!(summary["frontend_transition"]["direct_frontend_proof_authority"], false);
        assert_eq!(
            summary["frontend_transition"]["direct_frontend_status"],
            "structural_non_authoritative"
        );
        assert_eq!(summary["frontend_transition"]["producer_authenticated_by_transport"], false);
        assert_eq!(summary["frontend_transition"]["mir_compatibility_proof_path_retained"], true);
        assert!(
            summary["observation_scope"]["thir_completeness"]
                .as_str()
                .expect("THIR scope")
                .contains("absence does not prove")
        );
        assert_eq!(unsupported_mir_gate_summary(&rows)["schema"], UNSUPPORTED_MIR_GATE_SCHEMA);
    }

    #[test]
    fn unsupported_frontend_gate_rejects_absent_or_malformed_typed_native_rows() {
        let mut absent_transport = frontend_transport(0, 0);
        absent_transport["native_evidence_results"] = json!(1);
        let mut malformed_transport = empty_transport_summary();
        malformed_transport["obligation_results"] = json!(1);
        malformed_transport["malformed_typed_transport_results"] = json!(1);
        let mut rows = vec![
            frontend_gate_row("", absent_transport),
            frontend_gate_row("", malformed_transport),
        ];

        apply_unsupported_frontend_lowering_gate(&mut rows, &[], &BTreeMap::new());

        for row in rows {
            assert_eq!(row["unsupported_frontend_lowering_gate_status"], "missing_native_evidence");
            assert_eq!(row["outcome"], "failed");
        }
    }

    #[test]
    fn transport_native_counter_distinguishes_advertised_from_present() {
        let mut summary = empty_transport_summary_object();
        let message = json!({
            "results": [{
                "kind": "assertion",
                "description": "fixture",
                "location": null,
                "outcome": "unknown",
                "solver": "fixture",
                "time_ms": 0,
                "native_trust_ir": {
                    "suite": "trust-wp",
                    "backend": "trust-wp",
                    "present": false,
                    "diagnostics": []
                }
            }]
        });
        let root = tempfile::tempdir().expect("materialization root");

        summarize_obligation_results(&message, &mut summary, root.path());

        assert_eq!(summary["typed_transport_results"], 1);
        assert_eq!(summary["native_evidence_results"], 1);
        assert_eq!(summary["native_trust_ir_results"], 0);
    }

    #[test]
    fn unsupported_frontend_gate_allows_only_explicit_hooked_gap_metadata() {
        let diagnostic = "compiler full verification requires typed TrustIr native evidence: failed to lower fixture";
        let mut rows = vec![frontend_gate_row(diagnostic, empty_transport_summary())];
        let gaps = vec![json!({
            "id": "typed-trust-ir-gap",
            "program_id": "fixture",
            "slot": "trust-verify",
            "stderr_contains_any": ["typed TrustIr native evidence: failed to lower"],
            "reason": "temporary direct frontend gap",
        })];
        let hooks = BTreeMap::from([(
            "fixture".to_string(),
            BTreeSet::from(["typed-trust-ir-gap".to_string()]),
        )]);
        apply_unsupported_frontend_lowering_gate(&mut rows, &gaps, &hooks);
        assert_eq!(rows[0]["unsupported_frontend_lowering_gate_status"], "allowed_expected_gap");
        assert_eq!(rows[0]["outcome"], "passed");

        let mut unhooked = vec![frontend_gate_row(diagnostic, empty_transport_summary())];
        apply_unsupported_frontend_lowering_gate(&mut unhooked, &gaps, &BTreeMap::new());
        assert_eq!(
            unhooked[0]["unsupported_frontend_lowering_gate_status"],
            "unsupported_lowering"
        );
        assert_eq!(unhooked[0]["outcome"], "failed");
    }

    #[test]
    fn retired_compiler_policy_is_not_forwarded() {
        let mut env_map = BTreeMap::from([
            ("TRUST_VERIFY".to_string(), "1".to_string()),
            ("TRUST_VERIFY_POLICY".to_string(), "ambient".to_string()),
            ("TRUST_DUMP_ONLY".to_string(), "1".to_string()),
            ("RUST_BACKTRACE".to_string(), "0".to_string()),
        ]);

        scrub_retired_compiler_policy_env(&mut env_map);

        assert!(!env_map.contains_key("TRUST_VERIFY"));
        assert!(!env_map.contains_key("TRUST_VERIFY_POLICY"));
        assert!(!env_map.contains_key("TRUST_DUMP_ONLY"));
        assert_eq!(env_map.get("RUST_BACKTRACE").map(String::as_str), Some("0"));
    }

    #[test]
    fn verifier_benchmark_slot_relies_on_batteries_on_compiler_policy() {
        let profile = slot_profile("trust-verify").expect("verifier slot");
        assert_eq!(
            profile.extra_args,
            ["-Z", "trust-verify-level=1", "-Z", "trust-verify-output=json"]
        );
    }
}
