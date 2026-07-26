// targo trust: Cargo subcommand for Trust verification
//
// Usage:
//   targo trust check            -- verify the current crate
//   targo trust check path.rs    -- verify a single file
//   targo trust build            -- verify and build (check + codegen)
//   targo trust check --format json
//
// targo trust invokes the built Trust compiler with an explicit verifier mode,
// captures verification diagnostics from stderr, requires structured TRUST_JSON
// transport, and produces a summary report.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use std::{env, fs};

use anyhow::Context;
use serde::{Deserialize, Serialize};

mod benchmark_cli;
mod bounded_process;
mod cache_cli;
mod cargo_cache_materialization_cli;
mod cli;
mod config;
mod controlled_git;
mod dep_evidence;
mod dep_tcb;
mod diff;
mod diff_git;
mod diff_report;
mod doctor;
mod durable_io;
mod examples_cli;
mod exploit_find;
mod external_checker;
mod gap;
mod hardened_lab;
mod init;
mod input_limits;
mod intent;
mod lean_cli;
mod pipeline;
mod project_root;
mod proof_concurrency;
mod proof_concurrency_producer;
mod release_cli;
mod report;
mod report_query;
mod rewrite_loop;
mod rust_vs_trust;
mod script_cli;
mod self_improve;
mod self_verify_cli;
mod solver_detect;
mod source_analysis;
mod stage2_tools;
mod temporal_cli;
mod trust_added;
mod types;
mod verify_binary_evidence;
mod verify_examples_cli;

// Process environment is shared by Rust's parallel test threads. Every
// test-only environment override in this crate uses this one lock and an RAII
// guard, so otherwise unrelated probe and RUSTFLAGS tests cannot race.
#[cfg(test)]
pub(crate) static TEST_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

#[cfg(test)]
mod tests;

use cli::{SubcommandArgs, parse_subcommand_args, print_usage, print_usage_stdout};
use config::{DEFAULT_CODEGEN_BACKEND, DEFAULT_TRUST_PROFILE, TrustConfig};
// tests.rs uses `super::DoctorReport` etc. These are pulled in here so
// the `super::` spelling resolves in test scope; under cargo check the
// compiler doesn't see tests.rs as a direct consumer (it sees them via
// the #[cfg(test)] mod tests; only when --tests is set), hence the
// allow. Keeping them as a `use` is still useful so the imports
// survive any future restructuring.
#[cfg(test)]
#[allow(unused_imports)]
use doctor::{
    DoctorBackendSource, DoctorBackendStatus, DoctorCheckReportMode, DoctorCompilerStatus,
    DoctorConfigSourceKind, DoctorConfigStatus, DoctorDailyDriverStatus, DoctorReport,
    DoctorSolverStatus, backend_status, describe_capability, describe_config_source,
    load_doctor_config,
};
use doctor::{
    apply_configured_trust_profile, build_doctor_report, doctor_solver_has_native_source_route,
    doctor_suite_has_native_source_route, is_source_solver_routed,
    mark_doctor_in_process_solver_routes, print_doctor_terminal, print_solvers_terminal,
    supported_source_solver_names, verifier_suite_statuses,
};
use pipeline::{
    CompilerRun, apply_native_runtime_env, build_native_command_with_json_transport,
    detect_native_rustc_capabilities, discover_native_rustc_checked, has_output_path_flag,
    run_compiler, run_rewrite_loop, run_standalone_check, trust_verify_disable_diagnostic,
};
use project_root::resolve_project_root;
use report::UnsafeMemoryReportRequest;
use trust_decompile::{
    DecompilationArtifact, DecompileError, DecompileOptions, DecompileOutputKind, decompile_binary,
};
use trust_lift::{
    BinaryFunctionSelection, BinaryLiftOptions, ExactReplayInstructionWitness,
    ExactReplaySelectedImage, LiftError, LiftedBinary, lift_binary_to_trust_ir,
};
use trust_proof_cert::{
    BinaryCertificateCheckRequest, CheckedBinaryCertificateAuditExport,
    CheckedBinaryCertificateAuditExportBundleEntry, CheckedBinaryCertificateExternalCheckerRunner,
    CheckedBinaryCertificateManifest, CheckedBinaryCertificateManifestAcceptanceRequest,
    CheckedBinaryCertificateManifestEntry, CheckedBinaryCertificateSourceBackpropagationGate,
    SolverProofExport, StructuralBinaryCertificateChecker, UnsupportedLedgerSummary,
    accept_checked_certificate_manifest_entry, checked_certificate_audit_export_bundle_path,
    digest_binary_origin, load_checked_certificate_artifact_ref,
    persist_checked_certificate_audit_export_bundle, persist_solver_proof_export_artifacts,
    produce_checked_certificate_artifact,
};
use trust_report::{
    BinaryCertificateCheckReport, BinaryProofGradeGateReport, build_binary_verification_report,
};
use trust_router::{IncrementalAYSession, MemoryGuard, Router};
use trust_symex::{
    BinaryMachineReplayConfig, BinaryReplayConfig, BinaryReplayInput, BinaryReplayStatus,
    BinaryReplayTarget, BoundedMachineCodeAddressMap, BoundedMachineCodeArchitecture,
    BoundedMachineCodeImage, BoundedMachineCodeReplayBackend, BoundedMachineCodeSegment,
    BoundedMachineCodeSegmentPermissions, BoundedMachineInstructionBytes,
    replay_binary_counterexample_with_machine_replay,
};
use trust_types::{
    Aarch64SyncBoundarySemanticFact, BinaryArtifactDigest, BinaryArtifactDigestIdentity,
    BinaryArtifactFormat, BinaryOrigin, BinarySegment, BinarySelectedImageIdentity,
    BinarySourceProvenanceSummary, BinaryVerificationStatus, BinaryVerificationSummary,
    DecompiledOutput, PreservedSymbolicFormula, PreservedSymbolicFormulaEvidence,
    ProofCertificateProductionCheckerEvidenceStatus, ProofCertificateStatus,
    ReconstructionValidationStatus, ReplayStatus, SerializableVc, SolverDispatchRecord,
    SolverDispatchStatus, SolverQuerySemantics, SourceSpan, TargetValidationBlocker, TrustLevel,
    UnsupportedLedger, UnsupportedRecord, VcKind, VerifiableFunction, VerificationCondition,
};

const PROOF_DUMP_MAX_STREAM_BYTES: usize = 128 * 1024 * 1024;
const PROOF_DUMP_TIMEOUT: Duration = Duration::from_secs(2 * 60 * 60);
use trust_vcgen::lift_adapter::generate_binary_vcs;
use types::{
    BinaryLiftFunctionReport, BinaryLiftReport, BinaryLiftStatus, BinarySolverResultReport,
    BinarySolverSummary, BinaryVcKindCount, BinaryVerifyFunctionReport, BinaryVerifyReport,
    DecompileBinaryEvidenceReport, DecompileEvidenceBlockerReport, DecompileFunctionReport,
    DecompileProofCertificateEvidenceReport, DecompileProofGradeEvidenceReport,
    DecompileReleaseGateReport, DecompileReport, DecompileSolverDispatchEvidenceReport,
    DecompileTarget, DecompileUnsupportedLedgerReport, ExploitFindReport, ExploitFindStatus,
    ExploitFindTarget, OutputFormat, ProofGradeReleaseAarch64OrderingMonitorEvidenceReport,
    ProofGradeReleaseCheckedCertificateDigestEntryReport, ProofGradeReleaseEvidenceDigestReport,
    ProofGradeReleaseSelectedImageReport, ProofGradeReleaseTranscriptReport,
    ProofGradeReleaseTranscriptRowReport, ProofGradeReleaseVcDigestEntryReport,
    ReleaseTranscriptBindingReport, Subcommand,
};
use verify_binary_evidence::{
    CheckedCertificateArtifactImportRecord, CheckedCertificateImportReport,
    CheckedCertificateLoaderBlockerRecord, CheckedCertificateProductionReport,
    CheckedCertificateReplayDigestIdentityRecord, EXACT_REPLAY_BYTE_RANGE_FACT_DIAGNOSTIC_PREFIX,
    EXACT_REPLAY_CONTROL_FLOW_FACT_DIAGNOSTIC_PREFIX,
    EXACT_REPLAY_MEMORY_EFFECT_FACT_DIAGNOSTIC_PREFIX,
    EXACT_REPLAY_SLICE_ATTESTATION_ACCEPTED_DIAGNOSTIC,
    EXACT_REPLAY_SLICE_ATTESTATION_REJECTED_PREFIX,
    EXACT_REPLAY_TRANSCRIPT_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX, LoadedCheckedCertificateArtifact,
    VerifyBinaryEvidence, checked_certificate_replay_digest_identity_record,
    dispatch_has_exact_replay_slice_attestation, load_checked_certificate_artifact_rows,
    load_normalized_solver_proof_export_artifact,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BinarySolverRoute {
    AYIncremental,
}

const UNBOUND_TRUST_REPO_COMMIT: &str = "unbound";

impl BinarySolverRoute {
    fn backend_label(self) -> &'static str {
        match self {
            Self::AYIncremental => "ay-incremental",
        }
    }
}

fn version_text() -> String {
    format!(
        "targo-trust {version}\ntrust.identity=targo trust\ntrust.command=targo trust\ntrust.package=targo-trust\ntrust.source_package={source_package}\ntrust.version={version}\ntrust-repo-commit-hash: {trust_repo_commit_hash}\n",
        source_package = env!("CARGO_PKG_NAME"),
        version = env!("CARGO_PKG_VERSION"),
        trust_repo_commit_hash = embedded_trust_repo_commit_hash(option_env!("CFG_VER_HASH")),
    )
}

fn embedded_trust_repo_commit_hash(value: Option<&str>) -> &str {
    value.filter(|value| is_canonical_git_commit(value)).unwrap_or(UNBOUND_TRUST_REPO_COMMIT)
}

fn print_version() {
    print!("{}", version_text());
}

fn main() -> ExitCode {
    // Trust: Windows' main-thread stack (~1 MB) is far smaller than Unix's
    // (~8 MB default), so the deeply-recursive verifier / proof-report processing
    // overflows it and aborts with STATUS_STACK_OVERFLOW (0xC00000FD) — even after
    // producing correct results. Run the real work on a thread with a large stack
    // (the same technique rustc uses for its driver). Applied on all platforms for
    // consistency; override the size (bytes) with TRUST_STACK_SIZE.
    let stack_size = std::env::var("TRUST_STACK_SIZE")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(512 * 1024 * 1024);
    std::thread::Builder::new()
        .name("targo-trust-main".to_string())
        .stack_size(stack_size)
        .spawn(run_main)
        .expect("failed to spawn targo-trust main worker thread")
        .join()
        .unwrap_or(ExitCode::FAILURE)
}

fn run_main() -> ExitCode {
    let args = match unicode_command_arguments(env::args_os()) {
        Ok(args) => args,
        Err(error) => {
            eprintln!("targo trust: {error}");
            return ExitCode::from(2);
        }
    };

    // targo invokes us as: targo-trust trust <subcommand> [args...]
    let start = if args.get(1).is_some_and(|a| a == "trust") { 2 } else { 1 };

    let subcommand = args.get(start).map(|s| s.as_str());

    match subcommand {
        Some("--version") | Some("-V") => {
            print_version();
            ExitCode::SUCCESS
        }
        // Trust accepts two authoritative languages, so `check` dispatches on
        // the operand's language before it dispatches on cargo semantics. A
        // `.lean` operand names a whole verification input; handing it to the
        // Rust lane would make cargo, not the kernel, decide its fate.
        Some("check") if lean_cli::selects_lean_lane(&args[start + 1..]) => {
            lean_cli::run_check(&args[start + 1..])
        }
        Some("check") => run_subcommand(Subcommand::Check, &args[start + 1..]),
        Some("test") => run_subcommand(Subcommand::Test, &args[start + 1..]),
        // Compiling Clean to an artifact is the `clean compile` leg, which
        // judges nothing; routing it through `build` would let a caller read a
        // successful compile as a discharged proof. Point at the lane that
        // actually checks instead of guessing.
        Some("build") if lean_cli::selects_lean_lane(&args[start + 1..]) => {
            eprintln!(
                "targo trust build: a Clean/Lean operand has no build lane — `targo trust check \
                 <file.lean>` kernel-checks it"
            );
            ExitCode::from(2)
        }
        Some("build") => {
            // Compile first, then apply the post-build evidence boundaries.
            // These boundaries do not execute or credit a second proof as
            // evidence for the artifact just built: trustc does not yet publish
            // the authenticated semantic-input/output bindings needed to join
            // such results to that artifact.
            let build_result = run_subcommand(Subcommand::Build, &args[start + 1..]);
            // In order, temporal, Kani, and Creusot inspect the resolved
            // package graph only to detect an active opt-in. An opted-in
            // package is rejected with an explicit unbound-evidence setup
            // error; a package with no active temporal engine edge, Kani
            // dependency, or Creusot-family dependency is a no-op
            // pass-through. See temporal_cli::gate_build,
            // pipeline::kani_gate::gate_build, and
            // pipeline::creusot_gate::gate_build.
            let build_result = temporal_cli::gate_build(build_result, &args[start + 1..]);
            let build_result = pipeline::kani_gate::gate_build(build_result, &args[start + 1..]);
            pipeline::creusot_gate::gate_build(build_result, &args[start + 1..])
        }
        Some("version") => release_cli::run_version_subcommand(&args[start + 1..]),
        Some("release") => release_cli::run_release_subcommand(&args[start + 1..]),
        Some("verify") => script_cli::run_verify_subcommand(&args[start + 1..]),
        Some("examples") => examples_cli::run_examples_subcommand(&args[start + 1..]),
        Some("self-improve") => self_improve::run_self_improve_subcommand(&args[start + 1..]),
        Some("deps") => script_cli::run_deps_subcommand(&args[start + 1..]),
        Some("gate") => script_cli::run_gate_subcommand(&args[start + 1..]),
        Some("falsify") => script_cli::run_falsify_subcommand(&args[start + 1..]),
        Some("survey") => script_cli::run_survey_subcommand(&args[start + 1..]),
        Some("gap") => script_cli::run_gap_subcommand(&args[start + 1..]),
        Some("cite-discharge") => script_cli::run_cite_discharge_subcommand(&args[start + 1..]),
        Some("repo") => script_cli::run_repo_subcommand(&args[start + 1..]),
        Some("bootstrap") => script_cli::run_bootstrap_subcommand(&args[start + 1..]),
        Some("benchmark") => benchmark_cli::run_benchmark_subcommand(&args[start + 1..]),
        Some("lift") => run_lift_subcommand(&args[start + 1..]),
        Some("verify-binary") => run_verify_binary_subcommand(&args[start + 1..]),
        Some("decompile") => run_decompile_subcommand(&args[start + 1..]),
        Some("convert") => run_convert_subcommand(&args[start + 1..]),
        Some("exploit-find") => run_exploit_find_subcommand(&args[start + 1..]),
        Some("hardened-lab") => hardened_lab::run_hardened_lab_subcommand(&args[start + 1..]),
        Some("proof-concurrency") => proof_concurrency::run_subcommand(&args[start + 1..]),
        Some("proof-concurrency-producer") => {
            proof_concurrency_producer::run_subcommand(&args[start + 1..])
        }
        Some(external_checker::INTERNAL_CHECKER_SUPERVISOR_SUBCOMMAND) => {
            external_checker::run_checker_supervisor(&args[start + 1..])
        }
        Some("domination") => rust_vs_trust::run_subcommand(&args[start + 1..]),
        Some("report-query") => report_query::run_report_query_subcommand(&args[start + 1..]),
        Some("report") => run_subcommand(Subcommand::Report, &args[start + 1..]),
        Some("loop") => run_subcommand(Subcommand::Loop, &args[start + 1..]),
        Some("diff") => run_subcommand(Subcommand::Diff, &args[start + 1..]),
        Some("init") => run_init_subcommand(&args[start + 1..]),
        Some("temporal") => temporal_cli::run_temporal_subcommand(&args[start + 1..]),
        Some("solvers") => run_subcommand(Subcommand::Solvers, &args[start + 1..]),
        Some("doctor") => run_doctor_subcommand(&args[start + 1..]),
        Some("reflect-clean") => run_reflect_clean_subcommand(&args[start + 1..]),
        Some("prove") => run_prove_subcommand(&args[start + 1..]),
        Some("cache") => cache_cli::dispatch(&args[start + 1..]),
        Some("proof-cert") => dep_evidence::run_subcommand(&args[start + 1..]),
        Some("help") | Some("--help") | None => {
            print_usage_stdout();
            ExitCode::SUCCESS
        }
        Some(other) => {
            eprintln!("targo trust: unknown subcommand `{other}`");
            print_usage();
            ExitCode::from(2)
        }
    }
}

fn unicode_command_arguments(
    arguments: impl IntoIterator<Item = OsString>,
) -> Result<Vec<String>, String> {
    arguments
        .into_iter()
        .enumerate()
        .map(|(index, argument)| {
            argument.into_string().map_err(|argument| {
                format!(
                    "argument {index} is not valid Unicode and cannot be used in an evidence-grade command: {argument:?}"
                )
            })
        })
        .collect()
}

/// Compile a Trust source file with the in-tree `trustc` and its tracked MIR-dump option,
/// returning the directory of dumped `VerifiableFunction` JSON. Dump generation
/// uses the explicit dump-only + allow_l0_gaps lane: extraction still runs for every
/// function, while solver/certifier dispatch cannot terminate or delay the
/// compiler. `prove` independently judges the complete dump and still fails on
/// every rejected obligation.
fn compile_to_dump(source: &std::path::Path) -> std::io::Result<tempfile::TempDir> {
    let discovery = discover_native_rustc_checked().ok_or_else(|| {
        std::io::Error::other(
            "no canonical trustc beside targo-trust or under build/*/stage{2,3}/bin \
             (run ./x.py build first)",
        )
    })?;
    let trustc = discovery.rustc;
    let capabilities = detect_native_rustc_capabilities(&trustc);
    if !capabilities.trust_verify {
        return Err(std::io::Error::other(format!(
            "discovered compiler does not support Trust verification: {}",
            trustc.display()
        )));
    }

    // An owned, mode-0700 temporary directory prevents concurrent `prove
    // --source` processes from deleting or consuming each other's evidence.
    let dump = tempfile::Builder::new().prefix("targo-trust-prove-dump-").tempdir()?;
    // Full lib compile (the MIR verify pass — which writes the dumps — runs during
    // optimization, so a metadata-only build would skip it).
    let mut command = std::process::Command::new(&trustc);
    apply_native_runtime_env(&mut command, &trustc);
    // Emit one coverage decision for every MIR body. A dump directory alone
    // cannot reveal bodies skipped before extraction (including
    // `#[trust::skip]`), so `prove --source` consumes this completeness
    // channel and rejects every partial dump.
    command
        .env("TRUST_COVERAGE_DEBUG", "1")
        .args(["--edition", "2021", "-Ztrust-policy=advisory", "--crate-type", "lib"])
        .arg("-Z")
        .arg(format!("trust-dump=mir-only:{}", dump.path().display()))
        .arg("-o")
        .arg(dump.path().join("out.rlib"))
        .arg(source);
    let output = bounded_process::output(
        &mut command,
        "trustc proof-dump compilation",
        PROOF_DUMP_MAX_STREAM_BYTES,
        PROOF_DUMP_TIMEOUT,
    )
    .map_err(std::io::Error::other)?;
    let status = output.status;
    let compiler_stderr = String::from_utf8(output.stderr).map_err(|error| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!("trustc proof-dump stderr was not UTF-8: {error}"),
        )
    })?;
    let compiler_stdout = String::from_utf8(output.stdout).map_err(|error| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!("trustc proof-dump stdout was not UTF-8: {error}"),
        )
    })?;

    // Preserve ordinary compiler diagnostics while keeping the internal
    // coverage protocol out of end-user output.
    for line in compiler_stderr.lines() {
        if !line.starts_with("TRUST_COVERAGE: ") {
            eprintln!("{}", escape_terminal_controls(line));
        }
    }
    for line in compiler_stdout.lines() {
        println!("{}", escape_terminal_controls(line));
    }

    // A non-zero compiler status can leave a partial set of per-function dumps.
    // Treating that subset as the whole source would let a later proof succeed
    // while silently omitting the function that caused compilation to abort.
    // Survey verification suppresses proof-result escalation only. Any remaining
    // compiler failure is therefore an invalid (and potentially partial) proof
    // input rather than a proof verdict.
    if !status.success() {
        return Err(std::io::Error::other(format!(
            "{} failed while producing proof input ({})",
            trustc.display(),
            status,
        )));
    }

    let coverage = parse_proof_dump_coverage(&compiler_stderr);
    if coverage.analyzed.is_empty() && coverage.skipped.is_empty() {
        return Err(std::io::Error::other(format!(
            "{} emitted no per-body proof coverage; refusing an uncheckable partial dump",
            trustc.display()
        )));
    }
    if !coverage.skipped.is_empty() {
        return Err(std::io::Error::other(format!(
            "{} skipped {} MIR body/bodies while producing proof input: {}",
            trustc.display(),
            coverage.skipped.len(),
            coverage.skipped.join(", "),
        )));
    }

    // Parse every generated file and compare a multiset of def-paths against
    // the compiler's analyzed-body multiset. This catches serialization
    // failures, filename collisions/overwrites, and any future early-return
    // path that emits coverage without a dump.
    let mut dumped = BTreeMap::<String, usize>::new();
    for entry in std::fs::read_dir(dump.path())? {
        let entry = entry?;
        let path = entry.path();
        if path.extension().and_then(|extension| extension.to_str()) != Some("json") {
            continue;
        }
        let bytes =
            input_limits::read_bounded_file(&path, input_limits::MAX_SAVED_PROOF_REPORT_BYTES)?;
        let function: VerifiableFunction = serde_json::from_slice(&bytes).map_err(|error| {
            std::io::Error::other(format!("invalid proof dump {}: {error}", path.display()))
        })?;
        *dumped.entry(function.def_path).or_default() += 1;
    }
    if dumped.is_empty() {
        return Err(std::io::Error::other(format!(
            "{} produced no VerifiableFunction JSON dumps",
            trustc.display()
        )));
    }
    if dumped != coverage.analyzed {
        return Err(std::io::Error::other(format!(
            "{} produced an incomplete proof dump: compiler coverage {:?}, dump contents {:?}",
            trustc.display(),
            coverage.analyzed,
            dumped,
        )));
    }
    Ok(dump)
}

#[derive(Debug, Default, PartialEq, Eq)]
struct ProofDumpCoverage {
    analyzed: BTreeMap<String, usize>,
    skipped: Vec<String>,
}

fn parse_proof_dump_coverage(stderr: &str) -> ProofDumpCoverage {
    let mut coverage = ProofDumpCoverage::default();
    for line in stderr.lines() {
        let Some(event) = line.strip_prefix("TRUST_COVERAGE: ") else {
            continue;
        };
        let Some((function, decision)) = event.split_once(" => ") else {
            continue;
        };
        if decision.starts_with("skipped:") {
            coverage.skipped.push(format!("{function} ({decision})"));
        } else if decision == "zero-obligation" || decision.starts_with("analyzed:") {
            *coverage.analyzed.entry(function.to_string()).or_default() += 1;
        }
    }
    coverage
}

/// `targo trust prove [--self] [--kernel] [--require-axioms=3] [--budget-secs=30] [--dump-dir <dir>]`
/// — the §6 driver. Reads MIR-extracted `VerifiableFunction`s (from a
/// caller-selected dump dir or a source compiled into a private dump), runs the
/// reflect → ground → **inhabit** pipeline over each, and reports how many Trust
/// functions' contracts are grounded + PROVEN in the real Clean kernel modulo a
/// term-level axiom closure ⊆ 3 foundational axioms, ATOP the kernel TCB. When the
/// whole MODELED corpus is kernel-checked it prints the honest triumphant line —
/// bounded RELATIVE TO the trusted MirSem model + trusted rustc front-end reflection,
/// over the straight-line-scalar + single-branch fragment — alongside the
/// verification-DEPTH headline (FULLY-FAITHFUL rate), never an unconditional
/// "all of Trust proven". Produce dumps with the tracked
/// `-Ztrust-dump=mir-only:<dir>` compiler option during a
/// nonfatal Trust build. See
/// docs/TRUST-BASE-AND-SCOPE.md (TCB + scope) and
/// docs/PLAN-clean-dependent-type-reflection.md (§6).
#[derive(Debug, Default, PartialEq, Eq)]
struct ProveArgs {
    dump_dir: Option<PathBuf>,
    require_axioms: Option<usize>,
    budget_secs: Option<u64>,
    self_mode: bool,
    source: Option<PathBuf>,
    json: bool,
    help: bool,
}

fn parse_prove_args(args: &[String]) -> Result<ProveArgs, String> {
    fn set_path(slot: &mut Option<PathBuf>, value: &str, option: &str) -> Result<(), String> {
        if value.is_empty() {
            return Err(format!("{option} requires a non-empty path"));
        }
        if slot.replace(PathBuf::from(value)).is_some() {
            return Err(format!("{option} may only be specified once"));
        }
        Ok(())
    }

    fn parse_axiom_limit(value: &str) -> Result<usize, String> {
        value
            .parse::<usize>()
            .map_err(|_| format!("--require-axioms requires a non-negative integer, got `{value}`"))
    }

    fn parse_budget(value: &str) -> Result<u64, String> {
        match value.parse::<u64>() {
            Ok(value) if value > 0 => Ok(value),
            _ => Err(format!("--budget-secs requires a positive integer, got `{value}`")),
        }
    }

    let mut parsed = ProveArgs::default();
    let mut index = 0;
    let mut positional_only = false;
    while index < args.len() {
        let argument = &args[index];
        if positional_only {
            set_path(&mut parsed.source, argument, "source path")?;
            index += 1;
            continue;
        }
        match argument.as_str() {
            "--" => positional_only = true,
            "--dump-dir" => {
                index += 1;
                let value = args.get(index).ok_or("--dump-dir requires a path")?;
                set_path(&mut parsed.dump_dir, value, "--dump-dir")?;
            }
            "--source" => {
                index += 1;
                let value = args.get(index).ok_or("--source requires a Rust source path")?;
                set_path(&mut parsed.source, value, "--source")?;
            }
            "--require-axioms" => {
                index += 1;
                let value = args.get(index).ok_or("--require-axioms requires a value")?;
                if parsed.require_axioms.replace(parse_axiom_limit(value)?).is_some() {
                    return Err("--require-axioms may only be specified once".to_string());
                }
            }
            "--budget-secs" => {
                index += 1;
                let value = args.get(index).ok_or("--budget-secs requires a value")?;
                if parsed.budget_secs.replace(parse_budget(value)?).is_some() {
                    return Err("--budget-secs may only be specified once".to_string());
                }
            }
            "--kernel" => {
                // The prove pipeline always kernel-checks. Preserve this explicit
                // spelling for the documented evidence command.
            }
            "--json" | "--format=json" => parsed.json = true,
            "--format" => {
                index += 1;
                match args.get(index).map(String::as_str) {
                    Some("json") => parsed.json = true,
                    Some("terminal") | Some("text") => parsed.json = false,
                    Some(value) => return Err(format!("unsupported prove format `{value}`")),
                    None => return Err("--format requires a value".to_string()),
                }
            }
            "--self" => parsed.self_mode = true,
            "--help" | "-h" => parsed.help = true,
            _ if argument.starts_with("--dump-dir=") => {
                let value = argument.trim_start_matches("--dump-dir=");
                set_path(&mut parsed.dump_dir, value, "--dump-dir")?;
            }
            _ if argument.starts_with("--source=") => {
                let value = argument.trim_start_matches("--source=");
                set_path(&mut parsed.source, value, "--source")?;
            }
            _ if argument.starts_with("--require-axioms=") => {
                let value = argument.trim_start_matches("--require-axioms=");
                if parsed.require_axioms.replace(parse_axiom_limit(value)?).is_some() {
                    return Err("--require-axioms may only be specified once".to_string());
                }
            }
            _ if argument.starts_with("--budget-secs=") => {
                let value = argument.trim_start_matches("--budget-secs=");
                if parsed.budget_secs.replace(parse_budget(value)?).is_some() {
                    return Err("--budget-secs may only be specified once".to_string());
                }
            }
            _ if argument.ends_with(".rs") && !argument.starts_with('-') => {
                set_path(&mut parsed.source, argument, "source path")?;
            }
            _ => return Err(format!("unknown prove option or input `{argument}`")),
        }
        index += 1;
    }

    if parsed.source.is_some() && parsed.dump_dir.is_some() {
        return Err("--source and --dump-dir are mutually exclusive proof inputs".to_string());
    }
    Ok(parsed)
}

fn resolve_prove_dump_dir(
    explicit: Option<PathBuf>,
    self_mode: bool,
    self_dump: &Path,
) -> Option<PathBuf> {
    explicit.or_else(|| (self_mode && self_dump.exists()).then(|| self_dump.to_path_buf()))
}

fn run_prove_subcommand(args: &[String]) -> ExitCode {
    use trust_clean::prove_dump_dir_with_budget;

    let parsed = match parse_prove_args(args) {
        Ok(parsed) => parsed,
        Err(error) => {
            eprintln!("targo trust prove: {error}");
            eprintln!(
                "usage: targo trust prove [--self] [--kernel] [--require-axioms=3] [--budget-secs=30] [--json] \
                 [--dump-dir <dir> | --source <file.rs>]"
            );
            return ExitCode::from(2);
        }
    };
    if parsed.help {
        println!(
            "usage: targo trust prove [--self] [--kernel] [--require-axioms=3] [--budget-secs=30] [--json] \
             [--dump-dir <dir> | --source <file.rs>]"
        );
        return ExitCode::SUCCESS;
    }

    let mut dump_dir = parsed.dump_dir;
    let mut owned_dump: Option<tempfile::TempDir> = None;
    let require_axioms = parsed.require_axioms;
    let budget_secs = parsed.budget_secs.unwrap_or(30);
    let self_mode = parsed.self_mode;
    let source = parsed.source;

    // `--source <file.rs>`: compile it with the in-tree `trustc` + its tracked dump option
    // to produce real `VerifiableFunction` dumps, then prove those — the genuine
    // compile → dump → prove path (`prove --self` over a target).
    if let Some(src) = &source {
        match compile_to_dump(src) {
            Ok(d) => {
                dump_dir = Some(d.path().to_path_buf());
                owned_dump = Some(d);
            }
            Err(e) => {
                eprintln!("targo trust prove: compiling {}: {e}", src.display());
                return ExitCode::from(2);
            }
        }
    }

    // The conventional self-build dump location for `--self`.
    let self_dump = PathBuf::from("target/trust-mir-dump");

    // Resolve only an explicit proof input: a flag/source-produced dump or (for
    // --self) the conventional self-build dump. The
    // old fallback to checked-in test fixtures made a bare `prove` invocation
    // analyze unrelated sample code while appearing to prove the caller's
    // project.
    let resolved_dir = resolve_prove_dump_dir(dump_dir, self_mode, &self_dump);
    // Keep a `--source` dump alive until all proof work has consumed it.
    let _owned_dump = owned_dump;
    if self_mode && resolved_dir.is_none() {
        // `--self` over the whole tree needs the codebase's MIR dumped first.
        eprintln!(
            "targo trust prove --self: no MIR dump at {}.\n\
             To prove ALL of Trust, first dump every function's VerifiableFunction during a build:\n\
             \n    RUSTFLAGS_NOT_BOOTSTRAP=\"-Ztrust-policy=advisory -Ztrust-dump=mir-only:{}\" ./x.py build --stage 2\n\
             \nthen re-run `targo trust prove --self --kernel --require-axioms=3`.\n\
             (Each function the build compiles is written as <def_path>.json for the prover to reconstruct.)",
            self_dump.display(),
            self_dump.display()
        );
        return ExitCode::from(2);
    }
    let Some(dir) = resolved_dir else {
        eprintln!(
            "targo trust prove: no proof input; pass --source <file.rs> or --dump-dir <dir>, \
             or use --self after producing the whole-tree dump"
        );
        return ExitCode::from(2);
    };
    if !dir.exists() {
        eprintln!(
            "targo trust prove: no VerifiableFunction dump dir at {} \
             (pass --dump-dir <dir>, use -Ztrust-dump=mir-only:<dir> during a nonfatal Trust build, or run from the workspace)",
            dir.display()
        );
        return ExitCode::from(2);
    }

    // SCALABILITY / FAIL-CLOSED BUDGET — the real-crate CLI path bounds each function's
    // proof work by a per-function WALL-CLOCK budget so an uncurated crate with a
    // pathological body (e.g. `rustc_version`'s 1.5 MB `version_meta_for`, whose
    // `vc_refute` case-split search does not terminate) COMPLETES the scorecard —
    // declined, fail-closed — instead of HANGING. Default 30s: generous enough to
    // clear every real body's true single-invocation runtime while still catching
    // genuine non-termination. `--budget-secs` is explicit, validated, and
    // recorded in the command line; ambient environment cannot change proof work.
    let mut sc = match prove_dump_dir_with_budget(&dir, budget_secs) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("targo trust prove: reading {}: {e}", dir.display());
            return ExitCode::from(2);
        }
    };
    if sc.total == 0 {
        eprintln!(
            "targo trust prove: {} contained no verifiable functions; refusing a vacuous proof",
            dir.display()
        );
        return ExitCode::FAILURE;
    }
    if let Err(error) = sc.validate_aggregate_invariants() {
        eprintln!(
            "targo trust prove: scorecard accounting failed closed before publication: {error}"
        );
        return ExitCode::from(2);
    }
    // Trust: Lean↔Clean BRIDGE GATE (§6 bridge_agreement) — DEFAULT-ON, batteries
    // included: machine-import trust-ir's real Lean semIntBinOp semantics from the
    // VENDORED, sha256-manifested .oleans and kernel-check the per-op agreement
    // theorems (axiom_deps = ∅), so the reanchor_line's residual-trust re-key is
    // backed by a live run, not a stale citation. All 18 arms plus the composed
    // conjunction are always checked. FAIL-CLOSED: a gate failure is
    // reported loudly below and sc.bridge_agreement stays None (bridge_line then
    // states "not run — no claim"); it never silently passes.
    let bridge_gate_error = sc.attach_bridge_agreement().err().map(|e| e.to_string());

    if parsed.json {
        let status = if sc.kernel_rejected == 0 && bridge_gate_error.is_none() {
            "measured"
        } else {
            "rejected"
        };
        let document = serde_json::json!({
            "schema": "trust.prove-scorecard.v1",
            "status": status,
            "claim_boundary": "Coverage measurement over the declared dump population; incomplete, declined, SMT-only, or unsupported work receives no proof credit.",
            "budget_secs_per_function": budget_secs,
            "scorecard": &sc,
            "bridge_gate_error": bridge_gate_error.as_deref(),
        });
        match serde_json::to_string_pretty(&document) {
            Ok(rendered) => println!("{rendered}"),
            Err(error) => {
                eprintln!("targo trust prove: could not serialize scorecard: {error}");
                return ExitCode::from(2);
            }
        }
    } else {
        println!("{}", sc.headline());
        // The verification-DEPTH headline is printed RIGHT BESIDE the grounding numbers so
        // the two are never conflated: grounding measures contract-INHABITATION, the depth
        // headline reports the FULLY-FAITHFUL rate (single-digit), the spec-free fraction,
        // and the kernel-proven-vs-SMT-only safety-VC split.
        println!("{}", sc.depth_headline());
        println!(
            "  functions: {} | contracts grounded+proven (axiom closure ⊆ 3, atop kernel TCB): {}",
            sc.total, sc.inhabited
        );
        println!(
            "  obligations: {} total = {} postcondition + {} safety VCs ({} reconstructed to modulo-3 kernel proofs)",
            sc.total_obligations,
            sc.postcondition_obligations,
            sc.safety_obligations,
            sc.safety_discharged
        );
        println!(
            "    contract-types grounded but outside inhabitation subset: {}",
            sc.type_grounded_not_inhabited
        );
        println!("    not grounded: {}", sc.not_grounded);
        println!("    unsound (kernel-rejected): {}", sc.kernel_rejected);
        // SCALABILITY / FAIL-CLOSED BUDGET — functions DECLINED because their per-function
        // proof work exceeded the explicit/default wall-clock budget.
        // A declined function is counted in `functions` (total) but contributes NOTHING to
        // any proven/inhabited/faithful tally — strictly fail-closed, so the prover COMPLETES
        // on a real crate instead of hanging on one pathological body. This is honest
        // measurement at real-crate scale, never a false certificate.
        if sc.declined > 0 {
            println!(
                "    declined (per-function budget exceeded, fail-closed — NOT proven/faithful): {} [{}]",
                sc.declined,
                sc.declined_paths.join(", ")
            );
        }
        // Structural-depth + faithfulness instruments (the sharpened plan §6 requires the
        // depth metric — structural vs over-approximated — and faithfulness certification).
        println!("  {}", sc.depth_line());
        println!("  {}", sc.faithfulness_line());
        println!("  {}", sc.loop_coverage_line());
        // GOAL-ITEM #1 (trust-ir RE-ANCHOR) §6 WITNESS SWITCH-OVER: of the fully-faithful functions,
        // how many now SHIP the trust-ir-keyed refinement (relocated onto the universal IR
        // denotation) as the PRIMARY faithfulness witness vs the MirSem proven-equivalent fallback.
        // This is the live, shipped verdict that the re-anchor is real — not just a parallel theory.
        println!("  {}", sc.reanchor_line());
        // Trust: the Lean↔Clean BRIDGE line (§6 bridge_agreement) — the per-op agreement
        // between trust-ir's IMPORTED Lean semantics and the trust-clean denotation,
        // with forms, side conditions, and fail-closed controls stated plainly.
        println!("  {}", sc.bridge_line());
        if let Some(err) = &bridge_gate_error {
            eprintln!("  ✗ Lean↔Clean bridge gate FAILED CLOSED (no agreement is claimed): {err}");
        }
        // The faithfulness META-THEOREM (goal #4 capstone): the checked-by-construction MirSem
        // refinement — the Clean denotation is kernel-proven (by induction) to equal the MIR
        // operational semantics for the modeled fragment, so "proven" is end-to-end.
        println!("  {}", sc.refinement_line());
        if !sc.proven.is_empty() {
            println!("  PROVEN: {}", sc.proven.join(", "));
        }
        let safety_remaining = sc.safety_obligations - sc.safety_discharged;
        if safety_remaining > 0 {
            println!(
                "  note: {safety_remaining} safety VCs remain SMT-only; their SMT→CIC \
             reconstruction (beyond the guarded-check/linear-contradiction fragment) \
             is the remaining step for full §6."
            );
        }
    }

    // Soundness is non-negotiable: any kernel rejection fails the command.
    if sc.kernel_rejected > 0 {
        for r in &sc.rejections {
            eprintln!("  ✗ {r}");
        }
        return ExitCode::FAILURE;
    }
    if bridge_gate_error.is_some() {
        // The bridge is default-on and is part of the proof claim printed
        // above. Reporting its failure while returning success made the
        // documented fail-closed gate advisory in practice.
        return ExitCode::FAILURE;
    }
    // `--require-axioms=N` is the full §6 gate. This producer establishes an
    // upper bound of three foundational axioms; it cannot honestly establish a
    // stronger N<3 claim. For N>=3, every function and every safety VC must be
    // reconstructed in the kernel.
    if let Some(limit) = require_axioms {
        if limit < 3 {
            eprintln!(
                "targo trust prove: requested axiom bound {limit}, but this proof producer \
                 establishes only the documented bound of 3"
            );
            return ExitCode::FAILURE;
        }
        if sc.total == 0
            || sc.inhabited != sc.total
            || sc.safety_discharged != sc.safety_obligations
        {
            return ExitCode::FAILURE;
        }
    }
    ExitCode::SUCCESS
}

/// `targo trust reflect-clean <file.rs>...` — reflect each function's contract
/// (native `requires`/`ensures` signature clauses, plus explicit upstream
/// compatibility attributes) into a Clean dependent type and
/// report kernel-checked coverage. This makes the spec-as-type pipeline runnable:
/// a function's contract becomes a Clean dependent `Type` the kernel validates.
/// See docs/PLAN-clean-dependent-type-reflection.md.
#[derive(Debug, Default, PartialEq, Eq)]
struct ReflectCleanArgs {
    require_axioms: Option<usize>,
    kernel: bool,
    paths: Vec<PathBuf>,
    help: bool,
}

fn parse_reflect_clean_args(args: &[String]) -> Result<ReflectCleanArgs, String> {
    fn set_axiom_limit(parsed: &mut ReflectCleanArgs, value: &str) -> Result<(), String> {
        let value = value.parse::<usize>().map_err(|_| {
            format!("--require-axioms requires a non-negative integer, got `{value}`")
        })?;
        if parsed.require_axioms.replace(value).is_some() {
            return Err("--require-axioms may only be specified once".to_string());
        }
        Ok(())
    }

    let mut parsed = ReflectCleanArgs::default();
    let mut index = 0;
    let mut paths_only = false;
    while index < args.len() {
        let argument = &args[index];
        if paths_only {
            parsed.paths.push(PathBuf::from(argument));
            index += 1;
            continue;
        }
        match argument.as_str() {
            "--" => paths_only = true,
            "--kernel" => parsed.kernel = true,
            "--help" | "-h" => parsed.help = true,
            "--require-axioms" => {
                index += 1;
                let value = args.get(index).ok_or("--require-axioms requires a value")?;
                set_axiom_limit(&mut parsed, value)?;
            }
            _ if argument.starts_with("--require-axioms=") => {
                set_axiom_limit(&mut parsed, argument.trim_start_matches("--require-axioms="))?;
            }
            _ if argument.starts_with('-') => {
                return Err(format!("unknown reflect-clean option `{argument}`"));
            }
            _ => parsed.paths.push(PathBuf::from(argument)),
        }
        index += 1;
    }
    Ok(parsed)
}

fn run_reflect_clean_subcommand(args: &[String]) -> ExitCode {
    use std::collections::BTreeSet;

    use trust_clean::{
        GroundOutcome, KernelGroundingSession, ProofTerm, axiom_closure, carrier_context,
        infer_type, is_foundational, reflect_source_function,
    };

    // Accept files and directories (whole-crate driving): walk `.rs` under
    // directories without following directory symlinks. The old recursive
    // `Path::is_dir` walk could escape the requested tree or loop forever on a
    // symlink cycle, and silently ignored read errors.
    fn collect_rs(dir: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
        let mut pending = vec![dir.to_path_buf()];
        let mut visited = BTreeSet::new();
        while let Some(dir) = pending.pop() {
            let canonical = std::fs::canonicalize(&dir)?;
            if !visited.insert(canonical) {
                continue;
            }
            for entry in std::fs::read_dir(&dir)? {
                let entry = entry?;
                let path = entry.path();
                let file_type = entry.file_type()?;
                if file_type.is_symlink() {
                    continue;
                }
                if file_type.is_dir() {
                    if path.file_name().and_then(|name| name.to_str()) != Some("target") {
                        pending.push(path);
                    }
                } else if file_type.is_file()
                    && path.extension().and_then(|extension| extension.to_str()) == Some("rs")
                {
                    out.push(path);
                }
            }
        }
        Ok(())
    }

    let parsed = match parse_reflect_clean_args(args) {
        Ok(parsed) => parsed,
        Err(error) => {
            eprintln!("targo trust reflect-clean: {error}");
            eprintln!(
                "usage: targo trust reflect-clean [--kernel] [--require-axioms N] <file.rs | dir>..."
            );
            return ExitCode::from(2);
        }
    };
    if parsed.help {
        println!(
            "usage: targo trust reflect-clean [--kernel] [--require-axioms N] <file.rs | dir>..."
        );
        return ExitCode::SUCCESS;
    }

    let require_axioms = parsed.require_axioms;
    let kernel = parsed.kernel;
    let mut files: Vec<PathBuf> = Vec::new();
    for path in parsed.paths {
        if path.is_dir() {
            if let Err(error) = collect_rs(&path, &mut files) {
                eprintln!("targo trust reflect-clean: walking {}: {error}", path.display());
                return ExitCode::from(2);
            }
        } else if path.is_file()
            && path.extension().and_then(|extension| extension.to_str()) == Some("rs")
        {
            files.push(path);
        } else {
            eprintln!(
                "targo trust reflect-clean: input is not a readable Rust file or directory: {}",
                path.display()
            );
            return ExitCode::from(2);
        }
    }
    if files.is_empty() {
        eprintln!(
            "usage: targo trust reflect-clean [--kernel] [--require-axioms N] <file.rs | dir>..."
        );
        return ExitCode::from(2);
    }
    files.sort();
    files.dedup();

    let ctx = carrier_context();
    let mut session = kernel.then(KernelGroundingSession::new);
    let mut kernel_modulo3 = 0usize;
    let (mut total, mut reflected, mut failed) = (0usize, 0usize, 0usize);
    let mut vocabulary: BTreeSet<String> = BTreeSet::new();
    for path in &files {
        let content = match input_limits::read_bounded_utf8_file(
            path,
            input_limits::MAX_SAVED_PROOF_REPORT_BYTES,
        ) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("targo trust reflect-clean: reading {}: {e}", path.display());
                return ExitCode::from(2);
            }
        };
        let funcs = crate::source_analysis::extract_functions_from_source(&content, path);
        if funcs.is_empty() {
            continue;
        }
        println!("{}:", path.display());
        for func in &funcs {
            total += 1;
            // Sanitization preserves newlines, and `func.line` is one-based.
            // Use that exact occurrence: searching by name attributed every
            // duplicate-name function (common in sibling modules) to the first
            // declaration's contract block.
            let header_idx = func.line.saturating_sub(1);
            let (reqs, ens) = match scan_contract_exprs(&content, header_idx, &func.name) {
                Ok(contracts) => contracts,
                Err(error) => {
                    failed += 1;
                    println!("  - {} : fail-closed contract scan ({error})", func.name);
                    continue;
                }
            };
            let typed: Vec<(&str, &str)> =
                func.typed_params.iter().map(|(n, t)| (n.as_str(), t.as_str())).collect();
            let ret = func.return_type.as_deref();
            let term = match reflect_source_function(&typed, ret, &reqs, &ens) {
                Ok(t) => t,
                Err(e) => {
                    failed += 1;
                    println!("  - {} : fail-closed ({e})", func.name);
                    continue;
                }
            };
            if let Some(s) = &mut session {
                match s.check(&term) {
                    GroundOutcome::Modulo3 => {
                        reflected += 1;
                        kernel_modulo3 += 1;
                        println!(
                            "  \u{2713} {} : grounded in REAL kernel, modulo 3 axioms",
                            func.name
                        );
                    }
                    GroundOutcome::Residue(r) => {
                        failed += 1;
                        println!(
                            "  \u{2717} {} : rests on non-foundational axioms: {r:?}",
                            func.name
                        );
                    }
                    GroundOutcome::NotGrounded => {
                        failed += 1;
                        println!("  - {} : not yet groundable in real kernel", func.name);
                    }
                    GroundOutcome::KernelRejected(e) => {
                        failed += 1;
                        println!("  \u{2717} {} : real kernel rejected ({e})", func.name);
                    }
                }
            } else {
                match infer_type(&term, &ctx, &[]) {
                    Ok(ProofTerm::Sort(1)) => {
                        reflected += 1;
                        vocabulary.extend(axiom_closure(&term, &ctx).axioms);
                        println!("  \u{2713} {} : kernel-checked dependent type", func.name);
                    }
                    Ok(_) | Err(_) => {
                        failed += 1;
                        println!("  \u{2717} {} : reflected but not a well-formed Type", func.name);
                    }
                }
            }
        }
    }

    if total == 0 {
        eprintln!("targo trust reflect-clean: no functions found; refusing vacuous success");
        return ExitCode::FAILURE;
    }

    if kernel {
        println!(
            "\n{kernel_modulo3}/{total} functions GROUNDED IN THE REAL CLEAN KERNEL modulo 3 axioms \
             ({} not yet groundable / rejected)",
            total - kernel_modulo3
        );
        if let Some(n) = require_axioms {
            if n >= 3 && kernel_modulo3 == total {
                println!(
                    "\n\u{2713} ALL {total} contract TYPES kernel-verified in Clean modulo 3 axioms.\n\
                     (each spec is a well-formed Clean dependent type resting on only the 3 \
                     foundational axioms. Proving each function INHABITS its contract — that the \
                     body satisfies the spec — is the remaining inhabitation step via SMT→kernel.)"
                );
                return ExitCode::SUCCESS;
            }
            if n < 3 {
                println!(
                    "\n\u{2717} requested axiom bound {n}, but this reflector establishes only the documented bound of 3."
                );
                return ExitCode::FAILURE;
            }
            println!(
                "\n\u{2717} NOT modulo {n}: {} of {total} contracts not yet grounded modulo 3 in the \
                 real kernel.",
                total - kernel_modulo3
            );
            return ExitCode::FAILURE;
        }
        return if failed == 0 { ExitCode::SUCCESS } else { ExitCode::FAILURE };
    }
    println!(
        "\n{reflected}/{total} functions reflected to kernel-checked dependent types \
         ({failed} fail-closed / unreflectable)"
    );
    // Honest axiom accounting: the reflected types are well-formed modulo the
    // carrier vocabulary (declared axioms), NOT yet reduced to the 3 foundational
    // — that reduction (pinning carriers as Clean kernel definitions) is S1.
    let carriers: Vec<&String> = vocabulary.iter().filter(|a| !is_foundational(a)).collect();
    let foundational = vocabulary.len() - carriers.len();
    println!("\naxiom basis of the reflected types:");
    println!("  foundational (propext/Quot.sound/Classical.choice): {foundational}");
    println!(
        "  carrier-vocabulary axioms (trusted encoding, to discharge to the 3 \
         foundational via the Clean kernel — S1): {}",
        carriers.len()
    );

    if let Some(n) = require_axioms {
        if carriers.is_empty() && vocabulary.len() <= n {
            println!(
                "\n\u{2713} reflected types proven modulo {} foundational axioms.",
                vocabulary.len()
            );
            return ExitCode::SUCCESS;
        }
        println!(
            "\n\u{2717} NOT modulo {n} axioms: {} carrier-vocabulary axioms remain (encoding not \
             yet grounded in the Clean kernel — S1). Trust is not yet proven modulo {n}.",
            carriers.len()
        );
        return ExitCode::FAILURE;
    }
    if failed == 0 { ExitCode::SUCCESS } else { ExitCode::FAILURE }
}

/// Collect a function's first-class native signature clauses, then ingest
/// exact upstream `contracts::{requires,ensures}` attributes as an explicitly
/// labelled compatibility source. Bare/custom attributes are never treated as
/// Trust contracts.
fn scan_contract_exprs(
    source: &str,
    header_idx: usize,
    function_name: &str,
) -> Result<(Vec<String>, Vec<String>), String> {
    let lines = source.lines().collect::<Vec<_>>();
    let mut requires = Vec::new();
    let mut ensures = Vec::new();
    let mut native_requires = Vec::new();
    let mut native_ensures = Vec::new();

    let header_offset = header_idx
        .checked_sub(1)
        .and_then(|previous_line| source.match_indices('\n').nth(previous_line))
        .map_or(0, |(offset, _)| offset + 1);
    let native =
        trust_backprop::native_contract_clause_spans(source).map_err(|error| error.to_string())?;
    let owner = function_keyword_offset(source, header_offset, function_name);
    if let Some(owner) = owner {
        for clause in native.iter().filter(|clause| clause.function_offset == owner) {
            let expression = source
                .get(clause.expression.clone())
                .ok_or("native contract span is not a UTF-8 source range")?
                .trim()
                .to_string();
            match clause.kind {
                trust_backprop::ContractClauseKind::Requires => native_requires.push(expression),
                trust_backprop::ContractClauseKind::Ensures => native_ensures.push(expression),
                _ => return Err("unsupported native contract clause kind".to_string()),
            }
        }
    }

    let mut i = header_idx.min(lines.len());
    while i > 0 {
        while i > 0 && contract_scan_trivia(lines[i - 1]) {
            i -= 1;
        }
        if i == 0 {
            break;
        }

        // Locate the start of the immediately preceding outer attribute. Net
        // square-bracket depth works for both single-line and multiline
        // attributes, including indexed expressions inside a contract.
        let end = i;
        let mut start = i;
        let mut reverse_depth = 0isize;
        let mut attribute_start = None;
        while start > 0 {
            start -= 1;
            let line = lines[start];
            reverse_depth += line.chars().filter(|character| *character == ']').count() as isize;
            reverse_depth -= line.chars().filter(|character| *character == '[').count() as isize;
            if reverse_depth == 0 {
                if line.trim_start().starts_with("#[") {
                    attribute_start = Some(start);
                }
                break;
            }
            if reverse_depth < 0 {
                break;
            }
        }
        let Some(start) = attribute_start else {
            break;
        };

        let attribute = lines[start..end].join("\n");
        if let Some((kind, expression)) = contract_attr_expr(&attribute)? {
            match kind {
                "requires" => requires.push(expression),
                "ensures" => ensures.push(expression),
                _ => unreachable!("contract_attr_expr returns a canonical kind"),
            }
        }
        // Unrelated attributes are part of the same attribute block, so keep
        // walking until a real source line is reached.
        i = start;
    }
    requires.reverse();
    ensures.reverse();
    requires.extend(native_requires);
    ensures.extend(native_ensures);
    Ok((requires, ensures))
}

fn function_keyword_offset(
    source: &str,
    header_offset: usize,
    function_name: &str,
) -> Option<usize> {
    let suffix = source.get(header_offset..)?;
    for (relative, _) in suffix.match_indices("fn") {
        let offset = header_offset + relative;
        let before = source[..offset].chars().next_back();
        let after_fn = &source[offset + 2..];
        if before.is_some_and(|ch| ch == '_' || ch.is_alphanumeric()) {
            continue;
        }
        let rest = after_fn.trim_start();
        let Some(after_name) = rest.strip_prefix(function_name) else {
            continue;
        };
        if after_name.chars().next().is_none_or(|ch| !(ch == '_' || ch.is_alphanumeric())) {
            return Some(offset);
        }
    }
    None
}

fn contract_scan_trivia(line: &str) -> bool {
    let line = line.trim();
    line.is_empty()
        || line.starts_with("//")
        || line.starts_with("/*")
        || line.starts_with('*')
        || line.starts_with("*/")
}

/// Extract a contract attribute by its exact path basename. Substring matching
/// used to misread unrelated attributes such as `cfg(feature = "requires")` as
/// specifications.
fn contract_attr_expr(attribute: &str) -> Result<Option<(&'static str, String)>, String> {
    let Some(inner) = attribute.trim_start().strip_prefix("#[") else {
        return Ok(None);
    };
    let inner = inner.trim_start();
    let name_end = inner.find(['(', '=', ' ', '\t', '\n', ']']).unwrap_or(inner.len());
    let path = inner[..name_end].trim().trim_start_matches("::");
    let segments = path.split("::").collect::<Vec<_>>();
    let kind = match segments.as_slice() {
        ["contracts", "requires"]
        | ["core", "contracts", "requires"]
        | ["std", "contracts", "requires"] => "requires",
        ["contracts", "ensures"]
        | ["core", "contracts", "ensures"]
        | ["std", "contracts", "ensures"] => "ensures",
        _ => return Ok(None),
    };
    let open = attribute
        .find('(')
        .ok_or_else(|| format!("malformed compatibility attribute `{path}`: missing `(`"))?;
    let close = matching_outer_paren(attribute, open)
        .ok_or_else(|| format!("malformed compatibility attribute `{path}`: unbalanced payload"))?;
    if !attribute[close + 1..].trim().eq("]") {
        return Err(format!("malformed compatibility attribute `{path}`: trailing tokens"));
    }
    let payload = attribute[open + 1..close].trim();
    if payload.is_empty() {
        return Err(format!("malformed compatibility attribute `{path}`: empty payload"));
    }
    let expression =
        if kind == "ensures" { desugar_upstream_ensures(payload)? } else { payload.to_string() };
    Ok(Some((kind, expression)))
}

fn matching_outer_paren(text: &str, open: usize) -> Option<usize> {
    let mut depth = 0usize;
    let mut quote = None;
    let mut escaped = false;
    for (relative, character) in text[open..].char_indices() {
        if let Some(active) = quote {
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == active {
                quote = None;
            }
            continue;
        }
        match character {
            '"' | '\'' => quote = Some(character),
            '(' => depth += 1,
            ')' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(open + relative);
                }
            }
            _ => {}
        }
    }
    None
}

fn desugar_upstream_ensures(payload: &str) -> Result<String, String> {
    let payload = payload.trim();
    let Some(after_open) = payload.strip_prefix('|') else {
        return Err("upstream compatibility ensures must use `|result| predicate`".to_string());
    };
    let close = after_open
        .find('|')
        .ok_or("upstream compatibility ensures has an unterminated result binder")?;
    let binder = after_open[..close].trim();
    if binder.is_empty()
        || !binder.bytes().enumerate().all(|(index, byte)| {
            if index == 0 {
                byte == b'_' || byte.is_ascii_alphabetic()
            } else {
                byte == b'_' || byte.is_ascii_alphanumeric()
            }
        })
    {
        return Err(
            "upstream compatibility ensures result binder must be one identifier".to_string()
        );
    }
    let expression = after_open[close + 1..].trim();
    if expression.is_empty() {
        return Err("upstream compatibility ensures predicate is empty".to_string());
    }
    Ok(replace_identifier(expression, binder, "result"))
}

fn replace_identifier(source: &str, from: &str, to: &str) -> String {
    let mut output = String::with_capacity(source.len());
    let mut cursor = 0usize;
    for (offset, _) in source.match_indices(from) {
        let before = source[..offset].chars().next_back();
        let after = source[offset + from.len()..].chars().next();
        let boundary = |character: char| !(character == '_' || character.is_alphanumeric());
        if before.is_none_or(boundary) && after.is_none_or(boundary) {
            output.push_str(&source[cursor..offset]);
            output.push_str(to);
            cursor = offset + from.len();
        }
    }
    output.push_str(&source[cursor..]);
    output
}

#[derive(Debug, Clone)]
struct LiftReportInput {
    format: Option<String>,
    architecture: Option<String>,
    binary_entry: Option<u64>,
    functions: Vec<LiftedTrustIrFunctionSummary>,
    unsupported: Vec<String>,
    failures: Vec<String>,
}

#[derive(Debug, Clone)]
struct LiftedTrustIrFunctionSummary {
    name: String,
    entry: Option<u64>,
    blocks: usize,
    statements: usize,
    vcs: usize,
    instruction_provenance: Vec<BinaryOrigin>,
}

#[derive(Debug, Clone)]
struct VerifyBinaryReportInput {
    format: Option<String>,
    architecture: Option<String>,
    binary_entry: Option<u64>,
    functions: Vec<VerifiedBinaryFunctionSummary>,
    solver_results: Vec<BinarySolverResultReport>,
    proof_evidence: VerifyBinaryEvidence,
    unsupported: Vec<String>,
    failures: Vec<String>,
}

#[derive(Debug, Clone)]
struct VerifiedBinaryFunctionSummary {
    name: String,
    entry: Option<u64>,
    blocks: usize,
    statements: usize,
    vcs: usize,
    vc_counts: Vec<BinaryVcKindCount>,
}

#[derive(Debug, Clone)]
struct ExploitFindArgs {
    format: OutputFormat,
    input: String,
    target: ExploitFindTarget,
    entry: Option<String>,
    all_functions: bool,
    strict: bool,
}

fn run_lift_subcommand(args: &[String]) -> ExitCode {
    if args.iter().any(|arg| arg == "--help" || arg == "-h") {
        print!("{}", lift_usage_text());
        return ExitCode::SUCCESS;
    }

    let sub_args = match parse_subcommand_args(args) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("targo trust: {e}");
            return ExitCode::from(2);
        }
    };

    if matches!(sub_args.format, OutputFormat::Html) {
        eprintln!("targo trust: lift does not support --format html yet; use terminal or json");
        return ExitCode::from(2);
    }

    if sub_args.entry.is_some() && sub_args.all_functions {
        eprintln!("targo trust: lift accepts either --entry or --all, not both");
        return ExitCode::from(2);
    }

    let binary = match lift_binary_arg(&sub_args) {
        Ok(binary) => binary,
        Err(e) => {
            eprintln!("targo trust: {e}");
            return ExitCode::from(2);
        }
    };

    let entry = match parse_lift_entry(sub_args.entry.as_deref()) {
        Ok(entry) => entry,
        Err(e) => {
            eprintln!("targo trust: {e}");
            return ExitCode::from(2);
        }
    };

    let binary_path = Path::new(binary);
    let bytes = match read_binary_artifact(binary_path) {
        Ok(bytes) => bytes,
        Err(error) => {
            eprintln!("targo trust: failed to read {}: {error}", binary_path.display());
            return ExitCode::from(2);
        }
    };

    let options = lift_options(entry, sub_args.all_functions, sub_args.strict);
    let output = lift_report_input_from_result(lift_binary_to_trust_ir(&bytes, options));
    let report =
        build_lift_report(binary_path, entry, sub_args.all_functions, sub_args.strict, output);

    match sub_args.format {
        OutputFormat::Json => match serde_json::to_string_pretty(&report) {
            Ok(json) => println!("{json}"),
            Err(error) => {
                eprintln!("targo trust: failed to serialize lift report: {error}");
                return ExitCode::from(2);
            }
        },
        OutputFormat::Terminal => {
            print!("{}", render_lift_terminal(&report));
        }
        OutputFormat::Html => unreachable!("lift rejects HTML before lifting"),
    }

    if lift_should_fail(&report) { ExitCode::FAILURE } else { ExitCode::SUCCESS }
}

fn run_verify_binary_subcommand(args: &[String]) -> ExitCode {
    if args.iter().any(|arg| arg == "--help" || arg == "-h") {
        print!("{}", verify_binary_usage_text());
        return ExitCode::SUCCESS;
    }

    let sub_args = match parse_subcommand_args(args) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("targo trust: {e}");
            return ExitCode::from(2);
        }
    };
    if let Some(error) = checked_certificate_checker_configuration_error(&sub_args) {
        eprintln!("targo trust verify-binary: {error}");
        return ExitCode::from(2);
    }

    if matches!(sub_args.format, OutputFormat::Html) {
        eprintln!(
            "targo trust: verify-binary does not support --format html yet; use terminal or json"
        );
        return ExitCode::from(2);
    }

    if sub_args.entry.is_some() && sub_args.all_functions {
        eprintln!("targo trust: verify-binary accepts either --entry or --all, not both");
        return ExitCode::from(2);
    }
    let solver_route = match select_verify_binary_solver(sub_args.solver.as_deref()) {
        Ok(route) => route,
        Err(message) => {
            emit_cli_diagnostic(
                sub_args.format,
                "verify-binary",
                "solver_route_rejected",
                &message,
                2,
            );
            return ExitCode::from(2);
        }
    };

    let binary = match binary_subcommand_arg(&sub_args, "verify-binary") {
        Ok(binary) => binary,
        Err(e) => {
            eprintln!("targo trust: {e}");
            return ExitCode::from(2);
        }
    };

    let entry = match parse_lift_entry(sub_args.entry.as_deref()) {
        Ok(entry) => entry,
        Err(e) => {
            eprintln!("targo trust: {e}");
            return ExitCode::from(2);
        }
    };

    let binary_path = Path::new(binary);
    let bytes = match read_binary_artifact(binary_path) {
        Ok(bytes) => bytes,
        Err(error) => {
            eprintln!("targo trust: failed to read {}: {error}", binary_path.display());
            return ExitCode::from(2);
        }
    };
    let binary_artifact_digest_identity = binary_artifact_digest_identity_from_parser(&bytes);

    let options = lift_options(entry, sub_args.all_functions, sub_args.strict);
    let mut output = verify_binary_report_input_from_result_with_route_path_and_digest_identity(
        lift_binary_to_trust_ir(&bytes, options),
        solver_route,
        Some(binary_path),
        Some(&bytes),
        binary_artifact_digest_identity,
    );

    let checked_certificate_import: Option<CheckedCertificateImportReport> =
        if sub_args.checked_certificate_artifacts.is_empty()
            && sub_args.checked_certificate_manifests.is_empty()
        {
            None
        } else {
            match output.proof_evidence.load_and_import_checked_certificate_artifacts_and_manifests(
                &sub_args.checked_certificate_artifacts,
                &sub_args.checked_certificate_manifests,
            ) {
                Ok(report) => Some(report),
                Err(error) => {
                    if matches!(sub_args.format, OutputFormat::Json) {
                        Some(CheckedCertificateImportReport::loader_failure(
                            "verify-binary",
                            sub_args.checked_certificate_artifacts.len(),
                            sub_args.checked_certificate_manifests.len(),
                            error,
                        ))
                    } else {
                        emit_cli_diagnostic(
                            sub_args.format,
                            "verify-binary",
                            "checked_certificate_import_failed",
                            &format!(
                                "failed to load checked certificate artifact or manifest: {error}"
                            ),
                            2,
                        );
                        return ExitCode::from(2);
                    }
                }
            }
        };
    let checked_certificate_import_failed = checked_certificate_import
        .as_ref()
        .is_some_and(CheckedCertificateImportReport::loader_failed);
    let checked_certificate_production: Option<CheckedCertificateProductionReport> =
        sub_args.checked_certificate_export_dir.as_deref().map(|export_dir| {
            output.proof_evidence.produce_checked_certificate_artifacts(
                Path::new(export_dir),
                sub_args.checked_certificate_checker.as_deref().map(Path::new),
                current_unix_ms(),
            )
        });

    let mut report = build_verify_binary_report(
        binary_path,
        entry,
        sub_args.all_functions,
        sub_args.strict,
        output,
    );
    report.checked_certificate_import = checked_certificate_import;
    report.checked_certificate_production = checked_certificate_production;

    match sub_args.format {
        OutputFormat::Json => match serialize_verify_binary_json_with_route(
            &report,
            sub_args.solver.as_deref(),
            solver_route,
        ) {
            Ok(json) => println!("{json}"),
            Err(error) => {
                eprintln!("targo trust: failed to serialize verify-binary report: {error}");
                return ExitCode::from(2);
            }
        },
        OutputFormat::Terminal => {
            print!("{}", render_verify_binary_terminal(&report));
        }
        OutputFormat::Html => unreachable!("verify-binary rejects HTML before lifting"),
    }

    if checked_certificate_import_failed {
        ExitCode::from(2)
    } else if verify_binary_should_fail(&report) {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

fn select_verify_binary_solver(solver: Option<&str>) -> Result<BinarySolverRoute, String> {
    match solver {
        None | Some("ay") => Ok(BinarySolverRoute::AYIncremental),
        Some(other) if solver_detect::is_known_solver(other) => {
            let backend = BinarySolverRoute::AYIncremental.backend_label();
            Err(format!(
                "verify-binary --solver {other} is unsupported for binary VCs; only `ay` is wired to the incremental binary route (`{backend}`)"
            ))
        }
        Some(other) => {
            let known = solver_detect::known_solver_names().join(", ");
            Err(format!(
                "unknown verify-binary solver `{other}`; known source-level solvers are {known}, but only `ay` is wired for binary VCs"
            ))
        }
    }
}

fn current_unix_ms() -> u64 {
    let millis = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_millis())
        .unwrap_or(0);
    millis.min(u128::from(u64::MAX)) as u64
}

fn stable_json_sha256<T: Serialize>(value: &T) -> Option<String> {
    serde_json::to_vec(value).ok().map(|bytes| trust_types::digest::stable_sha256_hex(&bytes))
}

const RELEASE_TRANSCRIPT_BINDING_SCHEMA: &str = "targo-trust-release-transcript-binding.v1";
const PROOF_GRADE_RELEASE_TRANSCRIPT_SCHEMA: &str = "trust.proof-grade-release-transcript.v1";
const PROOF_GRADE_RELEASE_TRANSCRIPT_ROW_SCHEMA: &str = "trust.proof-grade-row.v1";
const PROOF_GRADE_RELEASE_TRANSCRIPT_ROW_TYPE: &str = "binary-decompilation-proof-grade";
const PROOF_GRADE_RELEASE_TRANSCRIPT_ROW_BINDING_SCHEMA: &str = "trust.proof-grade-row-binding.v1";
const PROOF_GRADE_RELEASE_VC_DIGEST_ENTRY_SCHEMA: &str = "trust.vc-digest-entry.v1";
const PROOF_GRADE_RELEASE_CHECKED_CERTIFICATE_DIGEST_ENTRY_SCHEMA: &str =
    "trust.checked-certificate-readback-digest-entry.v1";
const PROOF_GRADE_RELEASE_TRANSCRIPT_REAL_EVIDENCE_ORIGIN: &str = "targo_trust_release_export";
const PROOF_GRADE_RELEASE_TRANSCRIPT_SYNTHETIC_EVIDENCE_ORIGIN: &str = "synthetic_fixture";

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct TargetConsumerDigestBinding {
    required: bool,
    evidence_sha256: Option<String>,
    binding_sha256: Option<String>,
}

#[derive(Serialize)]
struct ProofGradeReleaseTranscriptRowBindingProfile<'a> {
    schema_version: &'static str,
    row_schema_version: &'a str,
    row_type: &'a str,
    evidence_origin: &'a str,
    status: &'a str,
    accepted: bool,
    rejection_reason: &'a Option<String>,
    candidate_commit: &'a Option<String>,
    proof_required_vc_count: usize,
    binary_digest: &'a Option<String>,
    selected_image: &'a Option<ProofGradeReleaseSelectedImageReport>,
    vc_digests: &'a [ProofGradeReleaseVcDigestEntryReport],
    checked_certificate_digests: &'a [ProofGradeReleaseCheckedCertificateDigestEntryReport],
    replay_transcript_digests: &'a [String],
    provenance_artifact_digests: &'a [String],
    unsupported_ledgers_empty: bool,
    target_proof_consumer_artifact_digests: &'a [String],
    exact_source_ownership_evidence: &'a ProofGradeReleaseEvidenceDigestReport,
    type_ownership_evidence: &'a ProofGradeReleaseEvidenceDigestReport,
    aarch64_ordering_monitor_evidence:
        &'a [ProofGradeReleaseAarch64OrderingMonitorEvidenceReport],
    blockers: &'a [String],
}

fn proof_grade_release_transcript_report(
    rows: &[ProofGradeReleaseTranscriptRowReport],
) -> ProofGradeReleaseTranscriptReport {
    let rows =
        rows.iter().cloned().map(validate_proof_grade_release_transcript_row).collect::<Vec<_>>();
    let accepted_proof_grade_rows =
        rows.iter().filter(|row| row.accepted).cloned().collect::<Vec<_>>();
    let blocked_proof_grade_rows =
        rows.iter().filter(|row| !row.accepted).cloned().collect::<Vec<_>>();
    ProofGradeReleaseTranscriptReport {
        schema_version: PROOF_GRADE_RELEASE_TRANSCRIPT_SCHEMA.to_string(),
        accepted_proof_grade_rows,
        blocked_proof_grade_rows,
    }
}

fn write_proof_grade_release_transcript_report(
    path: &Path,
    report: &ProofGradeReleaseTranscriptReport,
) -> anyhow::Result<()> {
    if let Some(parent) = path.parent().filter(|parent| !parent.as_os_str().is_empty()) {
        fs::create_dir_all(parent).with_context(|| {
            format!("create proof-grade release transcript directory {}", parent.display())
        })?;
    }
    let json =
        serde_json::to_string_pretty(report).context("serialize proof-grade release transcript")?;
    fs::write(path, format!("{json}\n"))
        .with_context(|| format!("write proof-grade release transcript to {}", path.display()))
}

fn load_proof_grade_release_transcript_report(
    path: &Path,
) -> anyhow::Result<ProofGradeReleaseTranscriptReport> {
    let json =
        input_limits::read_bounded_file(path, input_limits::MAX_RELEASE_TRANSCRIPT_REPORT_BYTES)
            .with_context(|| {
                format!("read proof-grade release transcript from {}", path.display())
            })?;
    serde_json::from_slice(&json)
        .with_context(|| format!("parse proof-grade release transcript from {}", path.display()))
}

fn write_and_readback_proof_grade_release_transcript_artifact(
    path: &Path,
    report: &ProofGradeReleaseTranscriptReport,
) -> anyhow::Result<String> {
    validate_proof_grade_release_transcript_artifact(report)
        .context("validate proof-grade release transcript before write")?;
    write_proof_grade_release_transcript_report(path, report)?;
    let written_bytes =
        input_limits::read_bounded_file(path, input_limits::MAX_RELEASE_TRANSCRIPT_REPORT_BYTES)
            .with_context(|| {
                format!("read written proof-grade release transcript from {}", path.display())
            })?;
    let written_digest = trust_types::digest::stable_sha256_hex(&written_bytes);
    let readback = load_proof_grade_release_transcript_report(path)?;
    validate_proof_grade_release_transcript_artifact(&readback)
        .context("validate proof-grade release transcript readback")?;
    if &readback != report {
        anyhow::bail!(
            "proof-grade release transcript readback from {} did not match emitted artifact",
            path.display()
        );
    }
    Ok(format!("sha256:{written_digest}"))
}

fn write_and_readback_proof_grade_release_transcript_rows(
    path: &Path,
    rows: &[ProofGradeReleaseTranscriptRowReport],
) -> anyhow::Result<String> {
    let report = proof_grade_release_transcript_report(rows);
    write_and_readback_proof_grade_release_transcript_artifact(path, &report)
}

fn validate_proof_grade_release_transcript_artifact(
    report: &ProofGradeReleaseTranscriptReport,
) -> anyhow::Result<()> {
    let mut blockers = Vec::new();
    if report.schema_version != PROOF_GRADE_RELEASE_TRANSCRIPT_SCHEMA {
        blockers.push(format!("schema_version must be `{PROOF_GRADE_RELEASE_TRANSCRIPT_SCHEMA}`"));
    }
    if report.accepted_proof_grade_rows.is_empty() {
        blockers.push("accepted_proof_grade_rows must contain at least one row".to_string());
    }
    if !report.blocked_proof_grade_rows.is_empty() {
        blockers.push(format!(
            "blocked_proof_grade_rows must be empty for release artifacts; found {} blocked row(s)",
            report.blocked_proof_grade_rows.len()
        ));
    }
    for (index, row) in report.accepted_proof_grade_rows.iter().enumerate() {
        let validated = validate_proof_grade_release_transcript_row(row.clone());
        if !validated.accepted {
            blockers.push(format!(
                "accepted_proof_grade_rows[{index}] rejected during readback validation: {}",
                validated
                    .rejection_reason
                    .as_deref()
                    .unwrap_or("proof-grade release transcript row is incomplete")
            ));
        } else if validated != *row {
            blockers.push(format!(
                "accepted_proof_grade_rows[{index}] is not the canonical validated row"
            ));
        }
    }
    if blockers.is_empty() {
        Ok(())
    } else {
        anyhow::bail!("proof-grade release transcript artifact rejected: {}", blockers.join("; "))
    }
}

struct ProofGradeReleaseTranscriptRowInput<'a> {
    evidence_origin: &'a str,
    candidate_commit: Option<String>,
    binary_artifact_digest_identity: &'a BinaryArtifactDigestIdentity,
    vc_sha256s: Vec<String>,
    checked_certificate_sha256s: Vec<String>,
    replay_transcript_sha256s: Vec<String>,
    provenance_sha256s: Vec<String>,
    unsupported_ledgers_empty: bool,
    target_consumer: &'a TargetConsumerDigestBinding,
    exact_source_ownership_sha256: Option<String>,
    type_ownership_sha256: Option<String>,
    aarch64_ordering_monitor_evidence: Vec<ProofGradeReleaseAarch64OrderingMonitorEvidenceReport>,
}

fn proof_grade_release_transcript_row_report(
    input: ProofGradeReleaseTranscriptRowInput<'_>,
) -> ProofGradeReleaseTranscriptRowReport {
    let ProofGradeReleaseTranscriptRowInput {
        evidence_origin,
        candidate_commit,
        binary_artifact_digest_identity,
        vc_sha256s,
        checked_certificate_sha256s,
        replay_transcript_sha256s,
        provenance_sha256s,
        unsupported_ledgers_empty,
        target_consumer,
        exact_source_ownership_sha256,
        type_ownership_sha256,
        aarch64_ordering_monitor_evidence,
    } = input;

    let mut blockers = Vec::new();
    let evidence_origin = evidence_origin.to_string();
    if evidence_origin != PROOF_GRADE_RELEASE_TRANSCRIPT_REAL_EVIDENCE_ORIGIN {
        blockers.push(format!(
            "evidence_origin must be `{PROOF_GRADE_RELEASE_TRANSCRIPT_REAL_EVIDENCE_ORIGIN}` for accepted proof-grade release transcript rows"
        ));
    }

    let candidate_commit = match candidate_commit {
        Some(commit) if is_canonical_git_commit(&commit) => {
            if evidence_origin == PROOF_GRADE_RELEASE_TRANSCRIPT_REAL_EVIDENCE_ORIGIN
                && release_transcript_candidate_commit()
                    .as_deref()
                    .is_some_and(|current| current != commit)
            {
                blockers.push(
                    "candidate_commit does not match the current release candidate commit"
                        .to_string(),
                );
            }
            Some(commit)
        }
        Some(_) => {
            blockers.push(
                "candidate_commit must be a full 40-character lowercase git commit".to_string(),
            );
            None
        }
        None => {
            blockers.push("candidate_commit is missing".to_string());
            None
        }
    };

    let binary_digest = match binary_artifact_digest_identity.root_artifact_digest.as_ref() {
        Some(root) if root.algorithm == "sha256" => match sha256_digest_uri(&root.value) {
            Some(digest) => Some(digest),
            None => {
                blockers.push("binary_digest must be a canonical sha256:<hex> digest".to_string());
                None
            }
        },
        Some(_) => {
            blockers.push("binary_digest algorithm is not sha256".to_string());
            None
        }
        None => {
            blockers.push("binary_digest is missing".to_string());
            None
        }
    };

    let selected_image = match binary_artifact_digest_identity.selected_image.as_ref() {
        Some(selected) => {
            if selected.file_size == 0 {
                blockers.push("selected_image.identity has zero file_size".to_string());
            }
            if selected.end_offset().is_none() {
                blockers.push("selected_image.identity range overflows u64".to_string());
            }
            match sha256_digest_uri(&selected.sha256) {
                Some(digest) => Some(ProofGradeReleaseSelectedImageReport {
                    identity: format!(
                        "file_offset={}:file_size={}",
                        selected.file_offset, selected.file_size
                    ),
                    digest,
                }),
                None => {
                    blockers.push(
                        "selected_image.digest must be a canonical sha256:<hex> digest".to_string(),
                    );
                    None
                }
            }
        }
        None => {
            blockers.push("selected_image must identify the replayed image".to_string());
            None
        }
    };

    let proof_required_vc_count = vc_sha256s.len();
    let vc_digests = release_transcript_vc_digest_entries(
        vc_sha256s,
        candidate_commit.as_deref(),
        binary_digest.as_deref(),
        selected_image.as_ref(),
        &mut blockers,
    );
    let checked_certificate_digests = release_transcript_checked_certificate_digest_entries(
        checked_certificate_sha256s,
        &vc_digests,
        proof_required_vc_count,
        candidate_commit.as_deref(),
        binary_digest.as_deref(),
        selected_image.as_ref(),
        &mut blockers,
    );
    let replay_transcript_digests = release_transcript_digest_list(
        replay_transcript_sha256s,
        "replay_transcript_digests",
        &mut blockers,
    );
    let provenance_artifact_digests = release_transcript_digest_list(
        provenance_sha256s,
        "provenance_artifact_digests",
        &mut blockers,
    );

    if !unsupported_ledgers_empty {
        blockers.push("unsupported_ledgers_empty must be true".to_string());
    }

    let target_proof_consumer_artifact_digests =
        target_proof_consumer_artifact_digests(target_consumer, &mut blockers);
    let exact_source_ownership_evidence = release_transcript_required_evidence_digest(
        exact_source_ownership_sha256,
        "exact_source_ownership_evidence",
        &mut blockers,
    );
    let type_ownership_evidence = release_transcript_required_evidence_digest(
        type_ownership_sha256,
        "type_ownership_evidence",
        &mut blockers,
    );
    for (index, evidence) in aarch64_ordering_monitor_evidence.iter().enumerate() {
        if evidence.status != "accepted" {
            blockers.push(format!(
                "aarch64_ordering_monitor_evidence[{index}] status is `{}`; proof-grade rows require accepted ordering/monitor evidence when present",
                evidence.status
            ));
        }
        if evidence.digest.as_deref().is_none_or(|digest| !is_canonical_digest_uri(digest)) {
            blockers.push(format!(
                "aarch64_ordering_monitor_evidence[{index}].digest must be a canonical sha256:<hex> digest"
            ));
        }
        if !evidence.blockers.is_empty() {
            blockers.push(format!(
                "aarch64_ordering_monitor_evidence[{index}] has blocker(s): {}",
                evidence.blockers.join("; ")
            ));
        }
    }

    if !blockers.is_empty() {
        blockers.push(format!(
            "release_transcript_binding_digest cannot be computed until all {PROOF_GRADE_RELEASE_TRANSCRIPT_ROW_BINDING_SCHEMA} inputs are accepted"
        ));
    }
    let accepted = blockers.is_empty();
    let rejection_reason = (!accepted).then(|| blockers.join("; "));

    let mut row = ProofGradeReleaseTranscriptRowReport {
        schema_version: PROOF_GRADE_RELEASE_TRANSCRIPT_ROW_SCHEMA.to_string(),
        row_type: PROOF_GRADE_RELEASE_TRANSCRIPT_ROW_TYPE.to_string(),
        evidence_origin,
        status: if accepted { "accepted" } else { "blocked" }.to_string(),
        accepted,
        rejection_reason,
        candidate_commit,
        proof_required_vc_count,
        binary_digest,
        selected_image,
        vc_digests,
        checked_certificate_digests,
        replay_transcript_digests,
        provenance_artifact_digests,
        unsupported_ledgers_empty,
        target_proof_consumer_artifact_digests,
        exact_source_ownership_evidence,
        type_ownership_evidence,
        aarch64_ordering_monitor_evidence,
        release_transcript_binding_digest: None,
        blockers,
    };
    if row.accepted {
        row.release_transcript_binding_digest =
            proof_grade_release_transcript_row_binding_digest(&row);
        if row.release_transcript_binding_digest.is_none() {
            row.accepted = false;
            row.status = "blocked".to_string();
            row.blockers.push(format!(
                "release_transcript_binding_digest could not be computed with {PROOF_GRADE_RELEASE_TRANSCRIPT_ROW_BINDING_SCHEMA}"
            ));
            row.rejection_reason = Some(row.blockers.join("; "));
        }
    }
    row
}

fn release_transcript_candidate_commit() -> Option<String> {
    let cwd = env::current_dir().ok()?;
    release_transcript_candidate_commit_in(&cwd)
}

fn release_transcript_candidate_commit_in(repo_dir: &Path) -> Option<String> {
    // Do not process-cache this identity. The binary is also exercised as an
    // in-process library by tests and orchestration, and one OnceLock keyed by
    // the first cwd silently stamped later repositories (or a later HEAD in
    // the same worktree) with stale release provenance.
    let repo_root = controlled_git::resolve_repo_root(repo_dir).ok()?;
    controlled_git::canonical_head(
        &repo_root,
        "release transcript git commit discovery",
        1024 * 1024,
        Duration::from_secs(30),
    )
    .ok()
}

#[cfg(test)]
fn parse_canonical_git_commit_output(stdout: Vec<u8>) -> Option<String> {
    let stdout = String::from_utf8(stdout).ok()?;
    let commit =
        stdout.strip_suffix("\r\n").or_else(|| stdout.strip_suffix('\n')).unwrap_or(&stdout);
    if commit.contains(['\r', '\n']) || !is_canonical_git_commit(commit) {
        return None;
    }
    Some(commit.to_string())
}

fn escape_terminal_controls(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len());
    for character in value.chars() {
        if character.is_control() {
            escaped.extend(character.escape_default());
        } else {
            escaped.push(character);
        }
    }
    escaped
}

fn release_transcript_vc_digest_entries(
    values: Vec<String>,
    candidate_commit: Option<&str>,
    binary_digest: Option<&str>,
    selected_image: Option<&ProofGradeReleaseSelectedImageReport>,
    blockers: &mut Vec<String>,
) -> Vec<ProofGradeReleaseVcDigestEntryReport> {
    let inventory_count = values.len();
    if inventory_count == 0 {
        blockers.push("vc_digests must be a non-empty typed digest inventory".to_string());
        return Vec::new();
    }

    let Some(candidate_commit) = candidate_commit else {
        return Vec::new();
    };
    let Some(binary_digest) = binary_digest else {
        return Vec::new();
    };
    let Some(selected_image) = selected_image else {
        return Vec::new();
    };

    let mut entries = Vec::new();
    let mut seen = BTreeSet::new();
    for (inventory_index, value) in values.into_iter().enumerate() {
        match sha256_digest_uri(&value) {
            Some(digest) => {
                if !seen.insert(digest.clone()) {
                    blockers.push(format!(
                        "vc_digests[{inventory_index}].digest duplicates an earlier VC digest"
                    ));
                }
                entries.push(ProofGradeReleaseVcDigestEntryReport {
                    schema_version: PROOF_GRADE_RELEASE_VC_DIGEST_ENTRY_SCHEMA.to_string(),
                    artifact_kind: "verification-condition".to_string(),
                    digest_algorithm: "sha256".to_string(),
                    digest,
                    candidate_commit: candidate_commit.to_string(),
                    binary_digest: binary_digest.to_string(),
                    selected_image: selected_image.clone(),
                    inventory_index,
                    inventory_count,
                    vc_id: format!("proof-required-vc-{inventory_index}"),
                });
            }
            None => blockers.push(format!(
                "vc_digests[{inventory_index}].digest is not a canonical sha256:<hex> digest"
            )),
        }
    }
    entries
}

fn release_transcript_checked_certificate_digest_entries(
    values: Vec<String>,
    vc_digests: &[ProofGradeReleaseVcDigestEntryReport],
    proof_required_vc_count: usize,
    candidate_commit: Option<&str>,
    binary_digest: Option<&str>,
    selected_image: Option<&ProofGradeReleaseSelectedImageReport>,
    blockers: &mut Vec<String>,
) -> Vec<ProofGradeReleaseCheckedCertificateDigestEntryReport> {
    let inventory_count = values.len();
    if inventory_count == 0 {
        blockers.push(
            "checked_certificate_digests must be a non-empty typed digest inventory".to_string(),
        );
        return Vec::new();
    }
    if inventory_count != proof_required_vc_count {
        blockers.push(format!(
            "checked_certificate_digests inventory_count {inventory_count} does not match proof_required_vc_count {proof_required_vc_count}"
        ));
    }
    if vc_digests.len() != proof_required_vc_count {
        blockers.push(format!(
            "vc_digests typed inventory has {} accepted entrie(s), expected {proof_required_vc_count}",
            vc_digests.len()
        ));
    }

    let Some(candidate_commit) = candidate_commit else {
        return Vec::new();
    };
    let Some(binary_digest) = binary_digest else {
        return Vec::new();
    };
    let Some(selected_image) = selected_image else {
        return Vec::new();
    };

    let mut entries = Vec::new();
    let mut seen_certificates = BTreeSet::new();
    let mut seen_vcs = BTreeSet::new();
    for (inventory_index, value) in values.into_iter().enumerate() {
        let Some(vc_digest) = vc_digests.get(inventory_index).map(|entry| entry.digest.clone())
        else {
            blockers.push(format!(
                "checked_certificate_digests[{inventory_index}].vc_digest has no matching vc_digests entry"
            ));
            continue;
        };
        match sha256_digest_uri(&value) {
            Some(digest) => {
                if !seen_certificates.insert(digest.clone()) {
                    blockers.push(format!(
                        "checked_certificate_digests[{inventory_index}].digest duplicates an earlier checked certificate digest"
                    ));
                }
                if !seen_vcs.insert(vc_digest.clone()) {
                    blockers.push(format!(
                        "checked_certificate_digests[{inventory_index}].vc_digest duplicates an earlier VC digest binding"
                    ));
                }
                entries.push(ProofGradeReleaseCheckedCertificateDigestEntryReport {
                    schema_version:
                        PROOF_GRADE_RELEASE_CHECKED_CERTIFICATE_DIGEST_ENTRY_SCHEMA.to_string(),
                    artifact_kind: "checked-certificate-readback".to_string(),
                    digest_algorithm: "sha256".to_string(),
                    digest,
                    candidate_commit: candidate_commit.to_string(),
                    binary_digest: binary_digest.to_string(),
                    selected_image: selected_image.clone(),
                    inventory_index,
                    inventory_count,
                    vc_digest,
                    certificate_role: "checked-certificate".to_string(),
                    readback_status: "accepted".to_string(),
                });
            }
            None => blockers.push(format!(
                "checked_certificate_digests[{inventory_index}].digest is not a canonical sha256:<hex> digest"
            )),
        }
    }
    entries
}

fn is_canonical_git_commit(value: &str) -> bool {
    value.len() == 40
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn sha256_digest_uri(value: &str) -> Option<String> {
    trust_types::digest::is_stable_sha256_hex(value).then(|| format!("sha256:{value}"))
}

fn release_transcript_digest_list(
    values: Vec<String>,
    field: &str,
    blockers: &mut Vec<String>,
) -> Vec<String> {
    let mut digests = Vec::new();
    let mut saw_value = false;
    for (index, value) in values.into_iter().enumerate() {
        saw_value = true;
        match sha256_digest_uri(&value) {
            Some(digest) => push_unique_digest(&mut digests, digest),
            None => {
                blockers.push(format!("{field}[{index}] is not a canonical sha256:<hex> digest"))
            }
        }
    }
    if !saw_value {
        blockers.push(format!("{field} must be a non-empty list"));
    }
    digests
}

fn release_transcript_required_evidence_digest(
    value: Option<String>,
    field: &str,
    blockers: &mut Vec<String>,
) -> ProofGradeReleaseEvidenceDigestReport {
    match value {
        Some(value) => match sha256_digest_uri(&value) {
            Some(digest) => ProofGradeReleaseEvidenceDigestReport {
                status: "accepted".to_string(),
                digest: Some(digest),
            },
            None => {
                blockers.push(format!("{field}.digest is not a canonical sha256:<hex> digest"));
                ProofGradeReleaseEvidenceDigestReport {
                    status: "blocked".to_string(),
                    digest: None,
                }
            }
        },
        None => {
            blockers.push(format!("{field}.digest is missing"));
            ProofGradeReleaseEvidenceDigestReport::default()
        }
    }
}

fn is_canonical_digest_uri(value: &str) -> bool {
    value.strip_prefix("sha256:").is_some_and(trust_types::digest::is_stable_sha256_hex)
}

fn target_proof_consumer_artifact_digests(
    target_consumer: &TargetConsumerDigestBinding,
    blockers: &mut Vec<String>,
) -> Vec<String> {
    let mut digests = Vec::new();
    push_target_consumer_digest(
        &mut digests,
        blockers,
        target_consumer.evidence_sha256.as_deref(),
        "target proof-consumer evidence digest",
        true,
    );
    push_target_consumer_digest(
        &mut digests,
        blockers,
        target_consumer.binding_sha256.as_deref(),
        "target proof-consumer binding digest",
        true,
    );
    if digests.is_empty() {
        blockers
            .push("target_proof_consumer_artifact_digests must be a non-empty list".to_string());
    }
    digests
}

fn push_target_consumer_digest(
    digests: &mut Vec<String>,
    blockers: &mut Vec<String>,
    digest: Option<&str>,
    label: &str,
    required: bool,
) {
    match digest {
        Some(digest) => match sha256_digest_uri(digest) {
            Some(digest) => push_unique_digest(digests, digest),
            None => blockers.push(format!("{label} is not canonical SHA-256 hex")),
        },
        None if required => blockers.push(format!("{label} is missing")),
        None => {}
    }
}

fn push_unique_digest(digests: &mut Vec<String>, digest: String) {
    if !digests.iter().any(|existing| existing == &digest) {
        digests.push(digest);
    }
}

fn release_transcript_digest_values(values: impl IntoIterator<Item = String>) -> Vec<String> {
    values.into_iter().filter(|value| !value.trim().is_empty()).collect()
}

fn proof_grade_release_transcript_row_binding_digest(
    row: &ProofGradeReleaseTranscriptRowReport,
) -> Option<String> {
    let profile = ProofGradeReleaseTranscriptRowBindingProfile {
        schema_version: PROOF_GRADE_RELEASE_TRANSCRIPT_ROW_BINDING_SCHEMA,
        row_schema_version: &row.schema_version,
        row_type: &row.row_type,
        evidence_origin: &row.evidence_origin,
        status: &row.status,
        accepted: row.accepted,
        rejection_reason: &row.rejection_reason,
        candidate_commit: &row.candidate_commit,
        proof_required_vc_count: row.proof_required_vc_count,
        binary_digest: &row.binary_digest,
        selected_image: &row.selected_image,
        vc_digests: &row.vc_digests,
        checked_certificate_digests: &row.checked_certificate_digests,
        replay_transcript_digests: &row.replay_transcript_digests,
        provenance_artifact_digests: &row.provenance_artifact_digests,
        unsupported_ledgers_empty: row.unsupported_ledgers_empty,
        target_proof_consumer_artifact_digests: &row.target_proof_consumer_artifact_digests,
        exact_source_ownership_evidence: &row.exact_source_ownership_evidence,
        type_ownership_evidence: &row.type_ownership_evidence,
        aarch64_ordering_monitor_evidence: &row.aarch64_ordering_monitor_evidence,
        blockers: &row.blockers,
    };
    stable_json_sha256(&profile).map(|digest| format!("sha256:{digest}"))
}

fn validate_proof_grade_release_transcript_row(
    mut row: ProofGradeReleaseTranscriptRowReport,
) -> ProofGradeReleaseTranscriptRowReport {
    let mut validation_blockers = Vec::new();

    if row.accepted {
        if row.status != "accepted" {
            validation_blockers
                .push(format!("accepted row status must be `accepted`, got `{}`", row.status));
        }
        if row.rejection_reason.is_some() {
            validation_blockers.push("accepted row rejection_reason must be null".to_string());
        }
        if !row.blockers.is_empty() {
            validation_blockers.push("accepted row blockers must be an empty list".to_string());
        }
        if row.evidence_origin != PROOF_GRADE_RELEASE_TRANSCRIPT_REAL_EVIDENCE_ORIGIN {
            validation_blockers.push(format!(
                "accepted row evidence_origin must be `{PROOF_GRADE_RELEASE_TRANSCRIPT_REAL_EVIDENCE_ORIGIN}`"
            ));
        }
        validate_accepted_proof_grade_release_transcript_inputs(&row, &mut validation_blockers);
        match (
            row.release_transcript_binding_digest.as_deref(),
            proof_grade_release_transcript_row_binding_digest(&row),
        ) {
            (Some(actual), Some(expected)) if actual == expected => {}
            (Some(actual), Some(expected)) => validation_blockers.push(format!(
                "release_transcript_binding_digest `{actual}` does not match canonical {PROOF_GRADE_RELEASE_TRANSCRIPT_ROW_BINDING_SCHEMA} digest `{expected}`"
            )),
            (None, Some(_)) => {
                validation_blockers.push("release_transcript_binding_digest is missing".to_string())
            }
            (_, None) => validation_blockers.push(format!(
                "release_transcript_binding_digest could not be recomputed with {PROOF_GRADE_RELEASE_TRANSCRIPT_ROW_BINDING_SCHEMA}"
            )),
        }
    }

    if !validation_blockers.is_empty() {
        for blocker in validation_blockers {
            if !row.blockers.iter().any(|existing| existing == &blocker) {
                row.blockers.push(blocker);
            }
        }
        row.accepted = false;
        row.status = "blocked".to_string();
        row.rejection_reason = Some(row.blockers.join("; "));
    }

    row
}

fn validate_accepted_proof_grade_release_transcript_inputs(
    row: &ProofGradeReleaseTranscriptRowReport,
    validation_blockers: &mut Vec<String>,
) {
    if row.schema_version != PROOF_GRADE_RELEASE_TRANSCRIPT_ROW_SCHEMA {
        validation_blockers.push(format!(
            "accepted row schema_version must be `{PROOF_GRADE_RELEASE_TRANSCRIPT_ROW_SCHEMA}`"
        ));
    }
    if row.row_type != PROOF_GRADE_RELEASE_TRANSCRIPT_ROW_TYPE {
        validation_blockers.push(format!(
            "accepted row row_type must be `{PROOF_GRADE_RELEASE_TRANSCRIPT_ROW_TYPE}`"
        ));
    }
    match row.candidate_commit.as_deref() {
        Some(commit) if is_canonical_git_commit(commit) => {
            if release_transcript_candidate_commit()
                .as_deref()
                .is_some_and(|current| current != commit)
            {
                validation_blockers.push(
                    "candidate_commit does not match the current release candidate commit"
                        .to_string(),
                );
            }
        }
        _ => validation_blockers
            .push("candidate_commit must be a full 40-character lowercase git commit".to_string()),
    }
    if row.proof_required_vc_count == 0 {
        validation_blockers.push("proof_required_vc_count must be a positive integer".to_string());
    }
    if row.binary_digest.as_deref().is_none_or(|digest| !is_canonical_digest_uri(digest)) {
        validation_blockers
            .push("binary_digest must be a canonical sha256:<hex> digest".to_string());
    }
    match row.selected_image.as_ref() {
        Some(selected_image) => {
            if selected_image.identity.trim().is_empty() {
                validation_blockers.push("selected_image.identity must be non-empty".to_string());
            }
            if !is_canonical_digest_uri(&selected_image.digest) {
                validation_blockers.push(
                    "selected_image.digest must be a canonical sha256:<hex> digest".to_string(),
                );
            }
        }
        None => {
            validation_blockers.push("selected_image must identify the replayed image".to_string());
        }
    }

    validate_release_vc_digest_inventory(row, validation_blockers);
    validate_release_checked_certificate_digest_inventory(row, validation_blockers);
    validate_release_digest_uri_list(
        &row.replay_transcript_digests,
        "replay_transcript_digests",
        validation_blockers,
    );
    validate_release_digest_uri_list(
        &row.provenance_artifact_digests,
        "provenance_artifact_digests",
        validation_blockers,
    );
    validate_release_digest_uri_list(
        &row.target_proof_consumer_artifact_digests,
        "target_proof_consumer_artifact_digests",
        validation_blockers,
    );
    if !row.unsupported_ledgers_empty {
        validation_blockers.push("unsupported_ledgers_empty must be true".to_string());
    }
    validate_release_evidence_digest_report(
        &row.exact_source_ownership_evidence,
        "exact_source_ownership_evidence",
        validation_blockers,
    );
    validate_release_evidence_digest_report(
        &row.type_ownership_evidence,
        "type_ownership_evidence",
        validation_blockers,
    );
    for (index, evidence) in row.aarch64_ordering_monitor_evidence.iter().enumerate() {
        if evidence.status != "accepted" {
            validation_blockers.push(format!(
                "aarch64_ordering_monitor_evidence[{index}] status must be accepted"
            ));
        }
        if evidence.digest.as_deref().is_none_or(|digest| !is_canonical_digest_uri(digest)) {
            validation_blockers.push(format!(
                "aarch64_ordering_monitor_evidence[{index}].digest must be a canonical sha256:<hex> digest"
            ));
        }
        if !evidence.blockers.is_empty() {
            validation_blockers
                .push(format!("aarch64_ordering_monitor_evidence[{index}] blockers must be empty"));
        }
    }
}

fn validate_release_vc_digest_inventory(
    row: &ProofGradeReleaseTranscriptRowReport,
    validation_blockers: &mut Vec<String>,
) {
    let expected = row.proof_required_vc_count;
    if row.vc_digests.is_empty() {
        validation_blockers
            .push("vc_digests must be a non-empty typed digest inventory".to_string());
        return;
    }
    if row.vc_digests.len() != expected {
        validation_blockers.push(format!(
            "proof_required_vc_count {expected} does not match vc_digests length {}",
            row.vc_digests.len()
        ));
    }

    let mut seen_digests = BTreeSet::new();
    let mut seen_indexes = BTreeSet::new();
    for (index, entry) in row.vc_digests.iter().enumerate() {
        let label = format!("vc_digests[{index}]");
        validate_release_digest_inventory_common(
            entry.schema_version.as_str(),
            PROOF_GRADE_RELEASE_VC_DIGEST_ENTRY_SCHEMA,
            entry.artifact_kind.as_str(),
            "verification-condition",
            entry.digest_algorithm.as_str(),
            entry.digest.as_str(),
            entry.candidate_commit.as_str(),
            entry.binary_digest.as_str(),
            &entry.selected_image,
            entry.inventory_index,
            entry.inventory_count,
            row,
            &label,
            validation_blockers,
        );
        if entry.vc_id.trim().is_empty() {
            validation_blockers.push(format!("{label}.vc_id must be non-empty"));
        }
        if is_canonical_digest_uri(&entry.digest) && !seen_digests.insert(entry.digest.clone()) {
            validation_blockers.push(format!("{label}.digest duplicates an earlier VC digest"));
        }
        if !seen_indexes.insert(entry.inventory_index) {
            validation_blockers
                .push(format!("{label}.inventory_index duplicates an earlier VC entry"));
        }
    }
}

fn validate_release_checked_certificate_digest_inventory(
    row: &ProofGradeReleaseTranscriptRowReport,
    validation_blockers: &mut Vec<String>,
) {
    let expected = row.proof_required_vc_count;
    if row.checked_certificate_digests.is_empty() {
        validation_blockers.push(
            "checked_certificate_digests must be a non-empty typed digest inventory".to_string(),
        );
        return;
    }
    if row.checked_certificate_digests.len() != expected {
        validation_blockers.push(format!(
            "proof_required_vc_count {expected} does not match checked_certificate_digests length {}",
            row.checked_certificate_digests.len()
        ));
    }

    let vc_digest_set =
        row.vc_digests.iter().map(|entry| entry.digest.clone()).collect::<BTreeSet<_>>();
    let mut seen_certificate_digests = BTreeSet::new();
    let mut seen_vc_digests = BTreeSet::new();
    let mut seen_indexes = BTreeSet::new();
    for (index, entry) in row.checked_certificate_digests.iter().enumerate() {
        let label = format!("checked_certificate_digests[{index}]");
        validate_release_digest_inventory_common(
            entry.schema_version.as_str(),
            PROOF_GRADE_RELEASE_CHECKED_CERTIFICATE_DIGEST_ENTRY_SCHEMA,
            entry.artifact_kind.as_str(),
            "checked-certificate-readback",
            entry.digest_algorithm.as_str(),
            entry.digest.as_str(),
            entry.candidate_commit.as_str(),
            entry.binary_digest.as_str(),
            &entry.selected_image,
            entry.inventory_index,
            entry.inventory_count,
            row,
            &label,
            validation_blockers,
        );
        if !is_canonical_digest_uri(&entry.vc_digest) {
            validation_blockers
                .push(format!("{label}.vc_digest must be a canonical sha256:<hex> digest"));
        } else if !vc_digest_set.contains(&entry.vc_digest) {
            validation_blockers.push(format!("{label}.vc_digest is not present in vc_digests"));
        }
        if entry.certificate_role != "checked-certificate" {
            validation_blockers
                .push(format!("{label}.certificate_role must be checked-certificate"));
        }
        if entry.readback_status != "accepted" {
            validation_blockers.push(format!("{label}.readback_status must be accepted"));
        }
        if is_canonical_digest_uri(&entry.digest)
            && !seen_certificate_digests.insert(entry.digest.clone())
        {
            validation_blockers
                .push(format!("{label}.digest duplicates an earlier checked certificate digest"));
        }
        if is_canonical_digest_uri(&entry.vc_digest)
            && !seen_vc_digests.insert(entry.vc_digest.clone())
        {
            validation_blockers
                .push(format!("{label}.vc_digest duplicates an earlier checked VC binding"));
        }
        if !seen_indexes.insert(entry.inventory_index) {
            validation_blockers.push(format!(
                "{label}.inventory_index duplicates an earlier checked certificate entry"
            ));
        }
    }
    for vc_digest in vc_digest_set {
        if !seen_vc_digests.contains(&vc_digest) {
            validation_blockers.push(format!(
                "checked_certificate_digests is missing readback for VC digest {vc_digest}"
            ));
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn validate_release_digest_inventory_common(
    schema_version: &str,
    expected_schema_version: &str,
    artifact_kind: &str,
    expected_artifact_kind: &str,
    digest_algorithm: &str,
    digest: &str,
    candidate_commit: &str,
    binary_digest: &str,
    selected_image: &ProofGradeReleaseSelectedImageReport,
    inventory_index: usize,
    inventory_count: usize,
    row: &ProofGradeReleaseTranscriptRowReport,
    label: &str,
    validation_blockers: &mut Vec<String>,
) {
    if schema_version != expected_schema_version {
        validation_blockers
            .push(format!("{label}.schema_version must be `{expected_schema_version}`"));
    }
    if artifact_kind != expected_artifact_kind {
        validation_blockers
            .push(format!("{label}.artifact_kind must be `{expected_artifact_kind}`"));
    }
    if digest_algorithm != "sha256" {
        validation_blockers.push(format!("{label}.digest_algorithm must be `sha256`"));
    }
    if !is_canonical_digest_uri(digest) {
        validation_blockers.push(format!("{label}.digest must be a canonical sha256:<hex> digest"));
    }
    if Some(candidate_commit) != row.candidate_commit.as_deref() {
        validation_blockers
            .push(format!("{label}.candidate_commit must match row candidate_commit"));
    }
    if Some(binary_digest) != row.binary_digest.as_deref() {
        validation_blockers.push(format!("{label}.binary_digest must match row binary_digest"));
    }
    if row.selected_image.as_ref() != Some(selected_image) {
        validation_blockers.push(format!("{label}.selected_image must match row selected_image"));
    }
    if inventory_index >= row.proof_required_vc_count {
        validation_blockers
            .push(format!("{label}.inventory_index must be less than proof_required_vc_count"));
    }
    if inventory_count != row.proof_required_vc_count {
        validation_blockers
            .push(format!("{label}.inventory_count must match proof_required_vc_count"));
    }
}

fn validate_release_digest_uri_list(
    values: &[String],
    field: &str,
    validation_blockers: &mut Vec<String>,
) {
    if values.is_empty() {
        validation_blockers.push(format!("{field} must be a non-empty list"));
        return;
    }
    let mut seen = BTreeSet::new();
    for (index, digest) in values.iter().enumerate() {
        if !is_canonical_digest_uri(digest) {
            validation_blockers
                .push(format!("{field}[{index}] must be a canonical sha256:<hex> digest"));
        } else if !seen.insert(digest.clone()) {
            validation_blockers.push(format!("{field}[{index}] duplicates an earlier digest"));
        }
    }
}

fn validate_release_evidence_digest_report(
    evidence: &ProofGradeReleaseEvidenceDigestReport,
    field: &str,
    validation_blockers: &mut Vec<String>,
) {
    if evidence.status != "accepted" {
        validation_blockers.push(format!("{field}.status must be accepted"));
    }
    if evidence.digest.as_deref().is_none_or(|digest| !is_canonical_digest_uri(digest)) {
        validation_blockers.push(format!("{field}.digest must be a canonical sha256:<hex> digest"));
    }
}

fn decompile_report_unsupported_ledgers_empty(report: &DecompileReport) -> bool {
    report.unsupported == 0
        && report.binary_evidence.unsupported_ledger.empty
        && report.binary_evidence.verification_unsupported_ledger.empty
        && report
            .production_proof_grade_evidence
            .as_ref()
            .is_some_and(|evidence| evidence.unsupported_ledger_empty)
}

fn release_transcript_binding_report(
    binary_artifact_digest_identity: &BinaryArtifactDigestIdentity,
    vc_sha256: Option<String>,
    checked_certificate_sha256: Option<String>,
    replay_transcript_sha256: Option<String>,
    provenance_sha256: Option<String>,
    target_consumer: &TargetConsumerDigestBinding,
) -> ReleaseTranscriptBindingReport {
    let binary_sha256 = binary_artifact_digest_identity
        .root_artifact_digest
        .as_ref()
        .map(|digest| digest.value.clone());
    let selected_image_sha256 = binary_artifact_digest_identity
        .selected_image
        .as_ref()
        .map(|selected| selected.sha256.clone());
    let selected_image_file_offset = binary_artifact_digest_identity
        .selected_image
        .as_ref()
        .map(|selected| selected.file_offset);
    let selected_image_file_size =
        binary_artifact_digest_identity.selected_image.as_ref().map(|selected| selected.file_size);

    let mut blockers = binary_artifact_digest_identity
        .digest_identity_blockers()
        .into_iter()
        .map(|blocker| format!("binary artifact digest identity: {blocker}"))
        .collect::<Vec<_>>();
    push_digest_binding_blocker(&mut blockers, vc_sha256.as_deref(), "VC digest");
    push_digest_binding_blocker(
        &mut blockers,
        checked_certificate_sha256.as_deref(),
        "checked certificate digest",
    );
    push_digest_binding_blocker(
        &mut blockers,
        replay_transcript_sha256.as_deref(),
        "replay transcript digest",
    );
    push_digest_binding_blocker(
        &mut blockers,
        provenance_sha256.as_deref(),
        "binary provenance digest",
    );
    if target_consumer.required {
        push_digest_binding_blocker(
            &mut blockers,
            target_consumer.evidence_sha256.as_deref(),
            "target-consumer evidence digest",
        );
        push_digest_binding_blocker(
            &mut blockers,
            target_consumer.binding_sha256.as_deref(),
            "target-consumer binding digest",
        );
    }

    let commit_input = serde_json::json!({
        "schema_version": RELEASE_TRANSCRIPT_BINDING_SCHEMA,
        "binary_sha256": binary_sha256.clone(),
        "selected_image_sha256": selected_image_sha256.clone(),
        "selected_image_file_offset": selected_image_file_offset,
        "selected_image_file_size": selected_image_file_size,
        "vc_sha256": vc_sha256.clone(),
        "checked_certificate_sha256": checked_certificate_sha256.clone(),
        "replay_transcript_sha256": replay_transcript_sha256.clone(),
        "provenance_sha256": provenance_sha256.clone(),
        "target_consumer_evidence_sha256": target_consumer.evidence_sha256.clone(),
        "target_consumer_binding_sha256": target_consumer.binding_sha256.clone(),
    });
    let commit_sha256 = stable_json_sha256(&commit_input).unwrap_or_else(|| {
        blockers.push("release transcript binding commit could not be serialized".to_string());
        String::new()
    });
    let status = if blockers.is_empty() { "accepted" } else { "rejected" };

    ReleaseTranscriptBindingReport {
        schema_version: RELEASE_TRANSCRIPT_BINDING_SCHEMA.to_string(),
        commit_sha256,
        binary_sha256,
        selected_image_sha256,
        selected_image_file_offset,
        selected_image_file_size,
        vc_sha256,
        checked_certificate_sha256,
        replay_transcript_sha256,
        provenance_sha256,
        target_consumer_evidence_sha256: target_consumer.evidence_sha256.clone(),
        target_consumer_binding_sha256: target_consumer.binding_sha256.clone(),
        status: status.to_string(),
        blockers,
    }
}

fn push_digest_binding_blocker(blockers: &mut Vec<String>, digest: Option<&str>, label: &str) {
    match digest {
        Some(digest) if trust_types::digest::is_stable_sha256_hex(digest) => {}
        Some(_) => blockers.push(format!("{label} is not canonical SHA-256 hex")),
        None => blockers.push(format!("{label} is missing")),
    }
}

fn target_consumer_digest_binding_for_report(
    report: &DecompileReport,
    evidence: Option<&TargetProofConsumerEvidenceReport>,
) -> TargetConsumerDigestBinding {
    let required = binary_derived_conversion_requires_target_gate(report.target);
    TargetConsumerDigestBinding {
        required,
        evidence_sha256: evidence.and_then(stable_json_sha256),
        binding_sha256: evidence
            .and_then(|evidence| evidence.binding.as_ref())
            .and_then(stable_json_sha256),
    }
}

#[derive(Serialize)]
struct ReleaseTranscriptExactSourceOwnershipBinding<'a> {
    schema_version: &'static str,
    source_provenance: &'a BinarySourceProvenanceSummary,
    checked_certificate_source_backpropagation_gate:
        &'a CheckedBinaryCertificateSourceBackpropagationGate,
    source_backpropagation_gate_sha256: &'a Option<String>,
}

#[derive(Serialize)]
struct ReleaseTranscriptTypeOwnershipBinding<'a> {
    schema_version: &'static str,
    target: &'a str,
    output_kind: &'a Option<String>,
    typed_target_output: bool,
    target_proof_consumer_evidence_sha256: &'a Option<String>,
    target_proof_consumer_binding_sha256: &'a Option<String>,
}

fn release_transcript_exact_source_ownership_sha256(
    report: &DecompileReport,
    source_backpropagation_gate: &CheckedBinaryCertificateSourceBackpropagationGate,
    source_backpropagation_gate_sha256: &Option<String>,
) -> Option<String> {
    if !report.source_provenance.effective_source_backpropagation_allowed()
        || !source_backpropagation_gate.source_backpropagation_allowed
        || !source_backpropagation_gate.exact_source_provenance
        || !source_backpropagation_gate_sha256.as_deref().is_some_and(trust_types::digest::is_stable_sha256_hex)
    {
        return None;
    }

    stable_json_sha256(&ReleaseTranscriptExactSourceOwnershipBinding {
        schema_version: "trust.proof-grade-exact-source-ownership.v1",
        source_provenance: &report.source_provenance,
        checked_certificate_source_backpropagation_gate: source_backpropagation_gate,
        source_backpropagation_gate_sha256,
    })
}

fn release_transcript_import_exact_source_ownership_sha256(
    artifact: &CheckedCertificateArtifactImportRecord,
) -> Option<String> {
    if !artifact.source_backpropagation_gate.source_backpropagation_allowed
        || !artifact.source_backpropagation_gate.exact_source_provenance
        || !artifact
            .source_backpropagation_gate_sha256
            .as_deref()
            .is_some_and(trust_types::digest::is_stable_sha256_hex)
    {
        return None;
    }

    stable_json_sha256(&ReleaseTranscriptExactSourceOwnershipBinding {
        schema_version: "trust.proof-grade-exact-source-ownership.v1",
        source_provenance: &artifact.source_backpropagation_gate.source_provenance,
        checked_certificate_source_backpropagation_gate: &artifact.source_backpropagation_gate,
        source_backpropagation_gate_sha256: &artifact.source_backpropagation_gate_sha256,
    })
}

fn release_transcript_type_ownership_sha256(
    report: &DecompileReport,
    target_consumer: &TargetConsumerDigestBinding,
    target_proof_consumer_evidence: Option<&TargetProofConsumerEvidenceReport>,
) -> Option<String> {
    let evidence = target_proof_consumer_evidence?;
    if !decompile_output_is_typed(report)
        || !target_proof_consumer_accepted_for_report(report, evidence)
        || target_consumer
            .evidence_sha256
            .as_deref()
            .is_none_or(|digest| !trust_types::digest::is_stable_sha256_hex(digest))
        || target_consumer
            .binding_sha256
            .as_deref()
            .is_none_or(|digest| !trust_types::digest::is_stable_sha256_hex(digest))
    {
        return None;
    }

    stable_json_sha256(&ReleaseTranscriptTypeOwnershipBinding {
        schema_version: "trust.proof-grade-type-ownership.v1",
        target: report.target.label(),
        output_kind: &report.output_kind,
        typed_target_output: true,
        target_proof_consumer_evidence_sha256: &target_consumer.evidence_sha256,
        target_proof_consumer_binding_sha256: &target_consumer.binding_sha256,
    })
}

fn release_transcript_import_type_ownership_sha256(
    target_consumer: &TargetConsumerDigestBinding,
) -> Option<String> {
    if !target_consumer.required
        || target_consumer
            .evidence_sha256
            .as_deref()
            .is_none_or(|digest| !trust_types::digest::is_stable_sha256_hex(digest))
        || target_consumer
            .binding_sha256
            .as_deref()
            .is_none_or(|digest| !trust_types::digest::is_stable_sha256_hex(digest))
    {
        return None;
    }

    let output_kind = None;
    stable_json_sha256(&ReleaseTranscriptTypeOwnershipBinding {
        schema_version: "trust.proof-grade-type-ownership.v1",
        target: "synthetic-import",
        output_kind: &output_kind,
        typed_target_output: true,
        target_proof_consumer_evidence_sha256: &target_consumer.evidence_sha256,
        target_proof_consumer_binding_sha256: &target_consumer.binding_sha256,
    })
}

fn decompile_output_is_typed(report: &DecompileReport) -> bool {
    serde_json::from_str::<serde_json::Value>(report.output_content.as_deref().unwrap_or_default())
        .ok()
        .and_then(|value| value.get("typed").and_then(serde_json::Value::as_bool))
        .unwrap_or(false)
}

fn release_transcript_aarch64_ordering_monitor_evidence(
    report: &DecompileReport,
) -> Vec<ProofGradeReleaseAarch64OrderingMonitorEvidenceReport> {
    report
        .binary_evidence
        .unsupported_ledger
        .records
        .iter()
        .chain(report.binary_evidence.verification_unsupported_ledger.records.iter())
        .filter_map(|record| record.aarch64_atomic_semantic_fact())
        .map(|fact| {
            let digest = stable_json_sha256(&fact).map(|digest| format!("sha256:{digest}"));
            let blockers = fact.proof_grade_rejection_reason().into_iter().collect::<Vec<_>>();
            ProofGradeReleaseAarch64OrderingMonitorEvidenceReport {
                status: if fact.proof_grade_gate_accepted() { "accepted" } else { "rejected" }
                    .to_string(),
                opcode: fact.opcode,
                ordering: format!("{:?}", fact.ordering),
                exclusive_monitor: format!("{:?}", fact.exclusive_monitor),
                digest,
                blockers,
            }
        })
        .collect()
}

fn emit_cli_diagnostic(
    format: OutputFormat,
    command: &'static str,
    status: &'static str,
    diagnostic: &str,
    exit_code: u8,
) {
    if matches!(format, OutputFormat::Json) {
        let report =
            CliDiagnosticReport { command, status, diagnostic: diagnostic.to_string(), exit_code };
        match serde_json::to_string_pretty(&report) {
            Ok(json) => eprintln!("{json}"),
            Err(_) => eprintln!("targo trust: {diagnostic}"),
        }
    } else {
        eprintln!("targo trust: {diagnostic}");
    }
}

fn write_requested_proof_grade_release_transcript_artifact(
    format: OutputFormat,
    command: &'static str,
    path: Option<&str>,
    rows: &[ProofGradeReleaseTranscriptRowReport],
) -> bool {
    let Some(path) = path else { return false };
    match write_and_readback_proof_grade_release_transcript_rows(Path::new(path), rows) {
        Ok(digest) => {
            eprintln!(
                "targo trust: wrote proof-grade release transcript artifact {} ({digest})",
                path
            );
            false
        }
        Err(error) => {
            emit_cli_diagnostic(
                format,
                command,
                "proof_grade_release_transcript_rejected",
                &format!("proof-grade release transcript artifact rejected: {error}"),
                1,
            );
            true
        }
    }
}

fn solver_route_diagnostic(
    requested_solver: Option<&str>,
    solver_route: BinarySolverRoute,
) -> BinaryCliSolverRouteDiagnostic {
    let requested = requested_solver.unwrap_or("auto");
    let selected = solver_route.backend_label();
    BinaryCliSolverRouteDiagnostic {
        requested: requested.to_string(),
        selected: selected.to_string(),
        status: "routed".to_string(),
        detail: format!(
            "verify-binary binary VCs are routed through `{selected}`; only `ay` is wired for this command"
        ),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct CliDiagnosticReport {
    command: &'static str,
    status: &'static str,
    diagnostic: String,
    exit_code: u8,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct BinaryCliSolverRouteDiagnostic {
    requested: String,
    selected: String,
    status: String,
    detail: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct ConvertCliGateReport {
    accepted: bool,
    status: String,
    target: String,
    proof_grade_artifact: bool,
    validation: String,
    source_backpropagation_gate: SourceBackpropagationGateReport,
    checked_certificate_evidence: ConvertCheckedCertificateEvidenceReport,
    #[serde(skip_serializing_if = "Option::is_none")]
    target_proof_consumer_evidence: Option<TargetProofConsumerEvidenceReport>,
    reason: String,
    blockers: Vec<String>,
    validation_blockers: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct SourceBackpropagationGateReport {
    accepted: bool,
    status: String,
    source_provenance: String,
    binary_verification_evidence: String,
    reconstruction_evidence: String,
    checked_certificate_source_backpropagation_gate: String,
    reason: String,
    blockers: Vec<SourceBackpropagationBlockerReport>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct SourceBackpropagationBlockerReport {
    code: String,
    stage: String,
    feature: String,
    detail: String,
    evidence_required: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct ConvertCheckedCertificateEvidenceReport {
    required: bool,
    status: String,
    proof_grade_release_accepted: bool,
    loader: ConvertCheckedCertificateLoaderReport,
    checked_artifact_rows: usize,
    accepted_certificate_rows: usize,
    imported_artifact_rows: usize,
    rejected_artifact_rows: usize,
    unmatched_artifact_rows: usize,
    normalized_solver_proof_exports: usize,
    proof_export_readback_rows: usize,
    checked_certificate_readback_rows: usize,
    checker_successes: usize,
    checked_certificates: usize,
    production_checker_evidence_rows: usize,
    production_checked_certificates: usize,
    missing_production_checked_certificates: usize,
    raw_solver_proof_bytes_sufficient: bool,
    production_positive_golden_inventory: ProductionPositiveGoldenInventoryReport,
    artifacts: Vec<CheckedCertificateArtifactImportRecord>,
    readback_records: Vec<ConvertCheckedCertificateReadbackRecord>,
    readback_row_details: Vec<ConvertCheckedCertificateReadbackRowDecisionRecord>,
    accepted_certificates: Vec<CheckedCertificateAcceptedEvidenceRecord>,
    proof_grade_release_transcript_rows: Vec<ProofGradeReleaseTranscriptRowReport>,
    proof_grade_release_blockers: Vec<ConvertCheckedCertificateBlockerRecord>,
    blockers: Vec<ConvertCheckedCertificateBlockerRecord>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct ProductionPositiveGoldenInventoryReport {
    required: bool,
    status: String,
    target: String,
    missing_artifacts: Vec<ProductionPositiveGoldenArtifactRecord>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct ProductionPositiveGoldenArtifactRecord {
    artifact: String,
    stage: String,
    status: String,
    detail: String,
    evidence_required: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct ConvertCheckedCertificateLoaderReport {
    status: String,
    implementation: String,
    requested_artifacts: usize,
    requested_manifests: usize,
    loaded_artifacts: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    production_export: Option<ConvertCheckedCertificateProductionExportReport>,
    #[serde(skip_serializing_if = "Option::is_none")]
    external_checker: Option<ConvertCheckedCertificateExternalCheckerReport>,
    artifacts: Vec<CheckedCertificateArtifactImportRecord>,
    readback_records: Vec<ConvertCheckedCertificateReadbackRecord>,
    #[serde(skip_serializing_if = "Option::is_none")]
    blocker: Option<ConvertCheckedCertificateBlockerRecord>,
    diagnostics: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct ConvertCheckedCertificateProductionExportReport {
    status: String,
    export_dir: String,
    checker_selection: String,
    candidate_dispatches: usize,
    canonical_binding_candidates: usize,
    proof_export_candidates: usize,
    exported_artifacts: usize,
    rejected_dispatches: usize,
    artifact_paths: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    manifest_path: Option<String>,
    source_backpropagation_gate: CheckedBinaryCertificateSourceBackpropagationGate,
    #[serde(skip_serializing_if = "Option::is_none")]
    source_backpropagation_gate_sha256: Option<String>,
    blockers: Vec<ConvertCheckedCertificateBlockerRecord>,
    diagnostics: Vec<String>,
}

#[derive(Debug, Clone)]
struct ProducedCheckedCertificateArtifacts {
    report: ConvertCheckedCertificateProductionExportReport,
    artifact_paths: Vec<String>,
}

#[derive(Debug, Clone)]
struct ConvertProofExportCandidate {
    dispatch: SolverDispatchRecord,
    canonical_vc_bytes: Vec<u8>,
    format: String,
    proof_path: PathBuf,
    proof_sha256: String,
    replay_transcript_digest: Option<String>,
}

#[derive(Debug, Clone)]
struct ConvertCheckedCertificateProductionSuccess {
    artifact_path: String,
    manifest_entry: CheckedBinaryCertificateManifestEntry,
    audit_export: CheckedBinaryCertificateAuditExport,
}

#[derive(Debug, Clone, Default)]
struct ConvertProofExportCandidateScan {
    candidate_dispatches: usize,
    canonical_binding_candidates: usize,
    proof_export_candidates: usize,
    candidates: Vec<ConvertProofExportCandidate>,
    blockers: Vec<ConvertCheckedCertificateBlockerRecord>,
    diagnostics: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct ConvertCheckedCertificateExternalCheckerReport {
    status: String,
    checker_path: String,
    checked_at_unix_ms: u64,
    rows_attempted: usize,
    rows_checked: usize,
    rows_failed: usize,
    diagnostics: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct ConvertCheckedCertificateReadbackRecord {
    source: String,
    status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    artifact_path: Option<String>,
    dispatch_id: String,
    vc_sha256: String,
    origin_sha256: String,
    proof_sha256: String,
    proof_export_sha256: String,
    certificate_sha256: String,
    binary_artifact_digest_identity: BinaryArtifactDigestIdentity,
    source_backpropagation_gate: CheckedBinaryCertificateSourceBackpropagationGate,
    #[serde(skip_serializing_if = "Option::is_none")]
    manifest_identity_sha256: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    source_backpropagation_gate_sha256: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    replay_transcript_digest: Option<String>,
    replay_digest_identity: CheckedCertificateReplayDigestIdentityRecord,
    checker: String,
    checker_version: String,
    format: String,
    production_checker_evidence_status: String,
    production_checked: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    production_checker_evidence_sha256: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    production_checker_evidence_detail: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    external_checker_status: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    external_checker_evidence_sha256: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    external_checker_binary_sha256: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    external_checker_invocation_sha256: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    external_checker_stdout_sha256: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    external_checker_stderr_sha256: Option<String>,
    release_transcript_binding: ReleaseTranscriptBindingReport,
    proof_grade_release_transcript_row: ProofGradeReleaseTranscriptRowReport,
    query_semantics: String,
    replay: String,
    checked_at_unix_ms: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct ConvertCheckedCertificateReadbackRowDecisionRecord {
    source: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    artifact_path: Option<String>,
    dispatch_id: String,
    certificate_sha256: String,
    vc_sha256: String,
    origin_sha256: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    manifest_identity_sha256: Option<String>,
    readback_accepted: bool,
    readback_status: String,
    proof_grade_release_accepted: bool,
    proof_grade_release_status: String,
    detail: String,
    blockers: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct ConvertCheckedCertificateBlockerRecord {
    code: String,
    stage: String,
    feature: String,
    detail: String,
    evidence_required: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct TargetProofConsumerEvidenceReport {
    target: String,
    status: String,
    target_semantics_consumed: bool,
    records: Vec<TargetProofConsumerRecordReport>,
    #[serde(skip_serializing_if = "Option::is_none")]
    binding: Option<TargetProofBindingReport>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    binding_sha256: Option<String>,
    blockers: Vec<TargetProofConsumerBlockerReport>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct TargetProofConsumerRecordReport {
    kind: String,
    identifier: String,
    accepted: bool,
    detail: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    formula_schema: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    formula_sort: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    formula_digest: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    formula_origin: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct TargetProofConsumerBlockerReport {
    code: String,
    detail: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct TargetProofBindingReport {
    target: String,
    target_output: String,
    status: String,
    target_semantics_consumed: bool,
    inputs: Vec<TargetProofBindingInputReport>,
    blockers: Vec<TargetProofConsumerBlockerReport>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct TargetProofBindingInputReport {
    kind: String,
    identifier: String,
    canonical_source: String,
    target_output: String,
    consumed_by_target_semantics: bool,
    detail: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    formula_schema: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    formula_sort: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    formula_digest: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    formula_origin: Option<String>,
}

#[derive(Debug, Clone)]
struct TrustIrTargetArtifactEvidence {
    target_output: String,
    records: Vec<TargetProofConsumerRecordReport>,
    binding_inputs: Vec<TargetProofBindingInputReport>,
    blockers: Vec<TargetProofConsumerBlockerReport>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct DecompileTargetEvidenceReport {
    target: String,
    output_validation: String,
    output_trust_level: String,
    target_validation_blocker_count: usize,
    symbolic_formula_preservation: DecompileSymbolicFormulaPreservationReport,
    target_validation_blockers: Vec<TargetValidationBlocker>,
    #[serde(skip_serializing_if = "Option::is_none")]
    target_proof_consumer_evidence: Option<TargetProofConsumerEvidenceReport>,
    blockers: Vec<DecompileEvidenceBlockerReport>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct DecompileSymbolicFormulaPreservationReport {
    preserved_count: usize,
    consumer_accepted: bool,
    formula_evidence: Vec<PreservedSymbolicFormulaEvidence>,
    formulas: Vec<PreservedSymbolicFormula>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct ExploitEvidenceGateReport {
    accepted: bool,
    status: String,
    proof_grade_complete: bool,
    unsupported_evidence_blocks_completion: bool,
    exploit_found: bool,
    claim_capture: String,
    replay: String,
    independent_refutation: String,
    reduction: String,
    attribution: String,
    regression_emission: String,
    required_evidence: Vec<String>,
    blockers: Vec<String>,
    reason: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct ExploitClaimCaptureRecord {
    claim_id: String,
    status: String,
    source: String,
    target: String,
    function: String,
    vc_kind: String,
    location: Option<String>,
    solver: String,
    solver_status: String,
    raw_counterexample_present: bool,
    replay_required: bool,
    independent_refutation_required: bool,
    diagnostic: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct ExploitAnalyzerStageRecord {
    stage: String,
    status: String,
    target: String,
    claim_ids: Vec<String>,
    evidence_required: Vec<String>,
    evidence_present: bool,
    blocks_exploit_confirmation: bool,
    diagnostic: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct CheckedCertificateRefutationAccountingReport {
    required_vcs: usize,
    solver_dispatches: usize,
    proved_vcs: usize,
    raw_solver_candidates: usize,
    exact_replayed_candidates: usize,
    checked_unsat_refutations: usize,
    missing_checked_unsat_refutations: usize,
    all_required_vcs_checked_unsat: bool,
    independent_refutation_status: ExploitFindStatus,
    independent_refutation_satisfied: bool,
    diagnostic: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct CheckedCertificateAcceptedEvidenceRecord {
    source: String,
    status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    artifact_path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    dispatch_id: Option<String>,
    certificate_sha256: String,
    checker: String,
    checker_version: String,
    format: String,
    checked_at_unix_ms: u64,
    vc_sha256: String,
    origin_sha256: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    proof_export_sha256: Option<String>,
    source_backpropagation_gate: CheckedBinaryCertificateSourceBackpropagationGate,
    #[serde(skip_serializing_if = "Option::is_none")]
    manifest_identity_sha256: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    source_backpropagation_gate_sha256: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    replay_transcript_digest: Option<String>,
    replay_digest_identity: CheckedCertificateReplayDigestIdentityRecord,
    release_transcript_binding: ReleaseTranscriptBindingReport,
    proof_grade_release_transcript_row: ProofGradeReleaseTranscriptRowReport,
    production_checker_evidence_status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    production_checker_evidence_sha256: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct CheckedCertificateEvidenceSummaryReport {
    status: String,
    required_vcs: usize,
    solver_dispatches: usize,
    checked_artifact_rows: usize,
    accepted_certificate_rows: usize,
    imported_artifact_rows: usize,
    rejected_artifact_rows: usize,
    unmatched_artifact_rows: usize,
    normalized_solver_proof_exports: usize,
    checker_successes: usize,
    checked_certificates: usize,
    missing_checked_certificates: usize,
    raw_solver_proof_bytes: usize,
    raw_solver_proof_byte_count: usize,
    raw_solver_proof_bytes_sufficient: bool,
    loader: CheckedCertificateEvidenceLoaderReport,
    artifacts: Vec<CheckedCertificateArtifactImportRecord>,
    accepted_certificates: Vec<CheckedCertificateAcceptedEvidenceRecord>,
    proof_grade_release_transcript_rows: Vec<ProofGradeReleaseTranscriptRowReport>,
    blockers: Vec<CheckedCertificateEvidenceBlockerReport>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct CheckedCertificateEvidenceLoaderReport {
    status: String,
    implementation: String,
    requested_artifacts: usize,
    requested_manifests: usize,
    loaded_artifacts: usize,
    imported_artifacts: usize,
    rejected_artifacts: usize,
    unmatched_artifacts: usize,
    dispatches_missing_canonical_binding: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    blocker: Option<CheckedCertificateEvidenceBlockerReport>,
    diagnostics: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct CheckedCertificateEvidenceBlockerReport {
    code: String,
    stage: String,
    detail: String,
    evidence_required: Vec<String>,
}

#[derive(Serialize)]
struct ConvertJsonReport<'a> {
    #[serde(flatten)]
    report: &'a DecompileReport,
    #[serde(skip_serializing_if = "Option::is_none")]
    trust_cg_output: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    target_proof_consumer_evidence: Option<TargetProofConsumerEvidenceReport>,
    target_evidence: DecompileTargetEvidenceReport,
    checked_certificate_readback: ConvertCheckedCertificateEvidenceReport,
    proof_grade_release_transcript: ProofGradeReleaseTranscriptReport,
    conversion_gate: ConvertCliGateReport,
}

#[derive(Serialize)]
struct DecompileJsonReport<'a> {
    #[serde(flatten)]
    report: &'a DecompileReport,
    #[serde(skip_serializing_if = "Option::is_none")]
    trust_cg_output: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    target_proof_consumer_evidence: Option<TargetProofConsumerEvidenceReport>,
    target_evidence: DecompileTargetEvidenceReport,
    checked_certificate_readback: ConvertCheckedCertificateEvidenceReport,
    proof_grade_release_transcript: ProofGradeReleaseTranscriptReport,
    artifact_gate: ConvertCliGateReport,
}

#[derive(Serialize)]
struct ExploitFindJsonReport<'a> {
    #[serde(flatten)]
    report: &'a ExploitFindReport,
    typed_scaffold: exploit_find::TypedExploitFindScaffold,
    claim_capture_records: Vec<ExploitClaimCaptureRecord>,
    analyzer_stage_records: Vec<ExploitAnalyzerStageRecord>,
    evidence_gate: ExploitEvidenceGateReport,
    checked_certificate_refutation_accounting: CheckedCertificateRefutationAccountingReport,
}

#[cfg(test)]
fn build_convert_cli_gate(report: &DecompileReport) -> ConvertCliGateReport {
    build_convert_cli_gate_with_loader(report, convert_checked_certificate_loader_not_requested())
}

fn build_convert_cli_gate_with_loader(
    report: &DecompileReport,
    checked_certificate_loader: ConvertCheckedCertificateLoaderReport,
) -> ConvertCliGateReport {
    let proof_grade_artifact = report.output_trust_level == "proof_grade";
    let checked_certificate_readback_available =
        convert_checked_certificate_loader_has_readback(&checked_certificate_loader);
    let production_checked_certificate_available =
        convert_checked_certificate_loader_has_complete_production_checked_readback(
            &checked_certificate_loader,
        );
    let target_proof_consumer_evidence =
        build_target_proof_consumer_evidence(report, &checked_certificate_loader);
    let checked_certificate_source_backpropagation_gate =
        checked_certificate_source_backpropagation_gate_status_for_convert_loader(
            &checked_certificate_loader,
        );
    let production_positive_golden_inventory = build_production_positive_golden_inventory(
        report,
        proof_grade_artifact,
        &checked_certificate_loader,
    );
    let source_backpropagation_gate =
        build_decompile_source_backpropagation_gate_with_checked_certificate_status(
            report,
            "targo-trust::binary-source-backprop",
            checked_certificate_source_backpropagation_gate.as_str(),
        );
    let (blockers, validation_blockers) = convert_gate_blockers(
        report,
        checked_certificate_readback_available,
        production_checked_certificate_available,
        target_proof_consumer_evidence.as_ref(),
        &production_positive_golden_inventory,
    );
    let target_consumer_digest_binding =
        target_consumer_digest_binding_for_report(report, target_proof_consumer_evidence.as_ref());

    let reason = if blockers.is_empty() {
        "conversion artifact accepted".to_string()
    } else {
        blockers.join("; ")
    };
    let accepted = blockers.is_empty() && !decompile_should_fail(report);
    let checked_certificate_evidence = build_convert_checked_certificate_evidence(
        report,
        proof_grade_artifact,
        checked_certificate_loader,
        &blockers,
        production_positive_golden_inventory,
        &target_consumer_digest_binding,
        target_proof_consumer_evidence.as_ref(),
    );

    ConvertCliGateReport {
        accepted,
        status: if accepted { "accepted".into() } else { "rejected".into() },
        target: report.target.label().to_string(),
        proof_grade_artifact,
        validation: report.output_validation.clone(),
        source_backpropagation_gate,
        checked_certificate_evidence,
        target_proof_consumer_evidence,
        reason,
        blockers,
        validation_blockers,
    }
}

fn convert_gate_blockers(
    report: &DecompileReport,
    checked_certificate_readback_available: bool,
    production_checked_certificate_available: bool,
    target_proof_consumer_evidence: Option<&TargetProofConsumerEvidenceReport>,
    production_positive_golden_inventory: &ProductionPositiveGoldenInventoryReport,
) -> (Vec<String>, Vec<String>) {
    let proof_grade_artifact = report.output_trust_level == "proof_grade";
    let mut blockers = Vec::new();
    let mut validation_blockers = Vec::new();
    let source_provenance_blocked_by_target_validation = report
        .target_validation_blockers
        .iter()
        .any(|blocker| blocker.feature == "exact-source-provenance");

    if report.output_trust_level != "proof_grade" {
        blockers.push(format!(
            "output trust is `{}`; proof-grade conversion output is not available",
            report.output_trust_level
        ));
    }
    if report.output_validation != "translation_validated" {
        let blocker = format!(
            "output validation is `{}`; translation validation has not accepted this artifact",
            report.output_validation
        );
        validation_blockers.push(blocker.clone());
        blockers.push(blocker);
    }
    if proof_grade_artifact
        && !report.source_provenance.effective_source_backpropagation_allowed()
        && !source_provenance_blocked_by_target_validation
    {
        let source_blockers = report
            .source_provenance
            .typed_diagnostics()
            .into_iter()
            .map(|diagnostic| format!("exact-source-provenance: {}", diagnostic.message))
            .collect::<Vec<_>>();
        validation_blockers.extend(source_blockers.iter().cloned());
        blockers.extend(source_blockers);
    }
    if proof_grade_artifact
        && binary_derived_conversion_requires_checked_certificate_gate(report.target)
        && !production_checked_certificate_available
        && !report
            .target_validation_blockers
            .iter()
            .any(target_blocker_mentions_checked_certificate)
    {
        let production_blockers =
            binary_derived_conversion_missing_checked_certificate_production_blockers(
                report.target,
                checked_certificate_readback_available,
            );
        validation_blockers.extend(production_blockers.iter().cloned());
        blockers.extend(production_blockers);
    }
    if proof_grade_artifact
        && binary_derived_conversion_requires_target_gate(report.target)
        && report.target_validation_blockers.is_empty()
        && !target_proof_consumer_evidence
            .is_some_and(|evidence| target_proof_consumer_accepted_for_report(report, evidence))
    {
        let derived_blockers = binary_derived_conversion_missing_target_gate_blockers(
            report.target,
            checked_certificate_readback_available,
        );
        validation_blockers.extend(derived_blockers.iter().cloned());
        blockers.extend(derived_blockers);
        if let Some(evidence) = target_proof_consumer_evidence {
            let proof_consumer_blockers = target_proof_consumer_gate_blockers(evidence);
            validation_blockers.extend(proof_consumer_blockers.iter().cloned());
            blockers.extend(proof_consumer_blockers);
        }
    }
    let target_blockers = report
        .target_validation_blockers
        .iter()
        .map(format_target_validation_blocker)
        .collect::<Vec<_>>();
    validation_blockers.extend(target_blockers.iter().cloned());
    blockers.extend(target_blockers);
    if proof_grade_artifact && !report.source_provenance.effective_source_backpropagation_allowed()
    {
        let source_blockers = report
            .source_provenance
            .typed_diagnostics()
            .into_iter()
            .map(|diagnostic| {
                format!(
                    "binary source provenance blocked proof-grade conversion: {}: {}",
                    diagnostic.kind.label(),
                    diagnostic.message
                )
            })
            .collect::<Vec<_>>();
        validation_blockers.extend(source_blockers.iter().cloned());
        blockers.extend(source_blockers);
    }
    if report.unsupported > 0 {
        blockers.push(format!(
            "unsupported conversion/lift coverage remains: {} item(s)",
            report.unsupported
        ));
    }
    if report.failures > 0 {
        blockers.push(format!("conversion pipeline failures remain: {} item(s)", report.failures));
    }
    if proof_grade_artifact
        && binary_derived_conversion_requires_checked_certificate_gate(report.target)
        && blockers.is_empty()
        && (!decompile_production_proof_grade_evidence_accepts(report)
            || production_positive_golden_inventory.status == "blocked")
    {
        let blocker = binary_derived_conversion_missing_production_proof_grade_evidence_blocker(
            report,
            Some(production_positive_golden_inventory),
        );
        validation_blockers.push(blocker.clone());
        blockers.push(blocker);
    }

    (blockers, validation_blockers)
}

fn decompile_production_proof_grade_evidence_accepts(report: &DecompileReport) -> bool {
    decompile_production_proof_grade_evidence_missing_requirements(report).is_empty()
}

fn decompile_production_proof_grade_evidence_missing_requirements(
    report: &DecompileReport,
) -> Vec<String> {
    let Some(evidence) = report.production_proof_grade_evidence.as_ref() else {
        return vec![
            "trust_decompile_binary_release_gate".to_string(),
            "proof_grade_binary_verification".to_string(),
            "checked_certificate_identity".to_string(),
            "exact_replay_identity".to_string(),
            "binary_artifact_digest_identity".to_string(),
            "nonzero_required_vcs".to_string(),
            "empty_unsupported_ledger".to_string(),
        ];
    };

    let mut missing = Vec::new();
    if evidence.producer != "trust-decompile::binary-release-gate" {
        missing.push("trust_decompile_binary_release_gate".to_string());
    }
    if evidence.artifact_trust_level != "proof_grade" {
        missing.push("proof_grade_decompile_artifact".to_string());
    }
    if evidence.binary_verification_trust_level != "proof_grade"
        || evidence.binary_verification_status != "proved"
    {
        missing.push("proof_grade_binary_verification".to_string());
    }
    if evidence.required_vcs == 0 {
        missing.push("nonzero_required_vcs".to_string());
    }
    if evidence.proved_vcs < evidence.required_vcs {
        missing.push("all_required_vcs_proved".to_string());
    }
    if !evidence.checked_certificate_identity {
        missing.push("checked_certificate_identity".to_string());
    }
    if !evidence.exact_replay_identity || evidence.binary_replay != "replayed" {
        missing.push("exact_replay_identity".to_string());
    }
    if !evidence.binary_artifact_digest_identity {
        missing.push("binary_artifact_digest_identity".to_string());
    }
    if !evidence.exact_source_provenance {
        missing.push("exact_source_provenance".to_string());
    }
    if !evidence.reconstruction_accepted {
        missing.push("accepted_reconstruction_validation".to_string());
    }
    if !evidence.target_validation_accepted {
        missing.push("target_semantic_validation".to_string());
    }
    if !evidence.unsupported_ledger_empty {
        missing.push("empty_unsupported_ledger".to_string());
    }
    missing
}

fn binary_derived_conversion_missing_production_proof_grade_evidence_blocker(
    report: &DecompileReport,
    inventory: Option<&ProductionPositiveGoldenInventoryReport>,
) -> String {
    let missing = decompile_production_proof_grade_evidence_missing_requirements(report);
    let missing_artifacts = inventory
        .map(|inventory| {
            inventory
                .missing_artifacts
                .iter()
                .map(|artifact| artifact.artifact.as_str())
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let mut clauses = Vec::new();
    if !missing.is_empty() {
        clauses.push(format!("missing {}", missing.join(", ")));
    }
    if !missing_artifacts.is_empty() {
        clauses.push(format!(
            "missing production-positive artifacts {}",
            missing_artifacts.join(", ")
        ));
    }
    if clauses.is_empty() {
        clauses.push("missing production-positive proof-grade release inventory".to_string());
    }
    format!(
        "production-proof-grade-cli-evidence-missing: binary-derived {} proof-grade conversion is not backed by a real targo trust decompile/convert proof-grade CLI artifact; {}",
        report.target.label(),
        clauses.join("; ")
    )
}

fn build_verify_binary_source_backpropagation_gate(
    report: &BinaryVerifyReport,
) -> SourceBackpropagationGateReport {
    let proof_evidence = build_binary_verify_proof_evidence_report(report);
    let checked_certificate_source_backpropagation_gate =
        checked_certificate_source_backpropagation_gate_status_for_verify_report(report);
    let verification_evidence = if proof_evidence.proof_grade_gate.accepted {
        "proof_grade"
    } else if report.proof_evidence.required_vcs > 0
        || !report.proof_evidence.solver_dispatch.is_empty()
    {
        "partial"
    } else {
        "missing"
    };
    source_backpropagation_gate_report(
        "targo-trust::verify-binary-source-backprop",
        "missing",
        verification_evidence,
        "missing",
        checked_certificate_source_backpropagation_gate.as_str(),
        Vec::new(),
    )
}

fn build_decompile_source_backpropagation_gate(
    report: &DecompileReport,
    stage: &'static str,
) -> SourceBackpropagationGateReport {
    build_decompile_source_backpropagation_gate_with_checked_certificate_status(
        report, stage, "missing",
    )
}

fn build_decompile_source_backpropagation_gate_with_checked_certificate_status(
    report: &DecompileReport,
    stage: &'static str,
    checked_certificate_source_backpropagation_gate: &str,
) -> SourceBackpropagationGateReport {
    source_backpropagation_gate_report(
        stage,
        source_backpropagation_source_provenance_status(&report.source_provenance).as_str(),
        "missing",
        decompile_reconstruction_evidence_status(report).as_str(),
        checked_certificate_source_backpropagation_gate,
        source_backpropagation_source_provenance_blockers(&report.source_provenance, stage),
    )
}

fn source_backpropagation_gate_report(
    stage: &'static str,
    source_provenance: &str,
    binary_verification_evidence: &str,
    reconstruction_evidence: &str,
    checked_certificate_source_backpropagation_gate: &str,
    mut blockers: Vec<SourceBackpropagationBlockerReport>,
) -> SourceBackpropagationGateReport {
    if source_provenance != "accepted"
        && !blockers.iter().any(|blocker| blocker.code == "exact-source-provenance-missing")
    {
        blockers.push(source_backpropagation_blocker(
            stage,
            "exact-source-provenance-missing",
            "exact-source-provenance",
            "binary-derived source backpropagation requires accepted exact source provenance before source rewrite planning",
            vec!["exact_binary_source_provenance"],
        ));
    }
    if binary_verification_evidence != "proof_grade" {
        blockers.push(source_backpropagation_blocker(
            stage,
            "proof-grade-binary-verification-missing",
            "proof-grade-binary-verification",
            format!(
                "binary-derived source backpropagation requires proof-grade binary verification evidence before source rewrite planning; current binary verification evidence is `{binary_verification_evidence}`"
            ),
            vec![
                "proof_grade_binary_verification",
                "checked_certificate_identity",
                "replay_grade_binary_artifact_identity",
            ],
        ));
    }
    if reconstruction_evidence != "accepted" {
        blockers.push(source_backpropagation_blocker(
            stage,
            "accepted-reconstruction-target-validation-missing",
            "reconstruction-target-validation",
            format!(
                "binary-derived source backpropagation requires accepted reconstruction and target validation before source rewrite planning; current reconstruction evidence is `{reconstruction_evidence}`"
            ),
            vec!["accepted_reconstruction", "target_semantic_validation"],
        ));
    }
    if checked_certificate_source_backpropagation_gate != "accepted" {
        let (code, detail) = if checked_certificate_source_backpropagation_gate == "missing" {
            (
                "checked-certificate-source-backpropagation-gate-missing",
                "binary-derived proposals require checked certificate source_backpropagation_gate acceptance before source rewrite planning; source_backpropagation_gate=missing"
                    .to_string(),
            )
        } else {
            (
                "checked-certificate-source-backpropagation-gate-rejected",
                format!(
                    "binary-derived proposals require checked certificate source_backpropagation_gate acceptance before source rewrite planning; current checked certificate source_backpropagation_gate evidence is `{checked_certificate_source_backpropagation_gate}`"
                ),
            )
        };
        blockers.push(source_backpropagation_blocker(
            stage,
            code,
            "checked-certificate-source-backpropagation-gate",
            detail,
            vec!["checked_certificate_source_backpropagation_gate"],
        ));
    }

    let accepted = blockers.is_empty();
    let reason = if accepted {
        "source backpropagation evidence accepted".to_string()
    } else {
        blockers
            .iter()
            .map(|blocker| format!("{}: {}", blocker.code, blocker.detail))
            .collect::<Vec<_>>()
            .join("; ")
    };

    SourceBackpropagationGateReport {
        accepted,
        status: if accepted { "accepted".into() } else { "rejected".into() },
        source_provenance: source_provenance.to_string(),
        binary_verification_evidence: binary_verification_evidence.to_string(),
        reconstruction_evidence: reconstruction_evidence.to_string(),
        checked_certificate_source_backpropagation_gate:
            checked_certificate_source_backpropagation_gate.to_string(),
        reason,
        blockers,
    }
}

fn checked_certificate_source_backpropagation_gate_status_for_verify_report(
    report: &BinaryVerifyReport,
) -> String {
    if let Some(import) = &report.checked_certificate_import {
        let imported_gates = import
            .artifacts
            .iter()
            .filter(|artifact| artifact.status == "imported")
            .map(|artifact| &artifact.source_backpropagation_gate)
            .collect::<Vec<_>>();
        if !imported_gates.is_empty() {
            return checked_certificate_source_backpropagation_gate_status(imported_gates);
        }
    }

    if let Some(production) = &report.checked_certificate_production {
        if production.requested {
            return checked_certificate_source_backpropagation_gate_status([
                &production.source_backpropagation_gate
            ]);
        }
    }

    "missing".to_string()
}

fn checked_certificate_source_backpropagation_gate_status_for_convert_loader(
    loader: &ConvertCheckedCertificateLoaderReport,
) -> String {
    let readback_gates = loader
        .readback_records
        .iter()
        .filter(|record| record.status == "readback")
        .map(|record| &record.source_backpropagation_gate)
        .collect::<Vec<_>>();
    if !readback_gates.is_empty() {
        return checked_certificate_source_backpropagation_gate_status(readback_gates);
    }

    let artifact_gates = loader
        .artifacts
        .iter()
        .filter(|artifact| artifact.status == "readback")
        .map(|artifact| &artifact.source_backpropagation_gate)
        .collect::<Vec<_>>();
    if !artifact_gates.is_empty() {
        return checked_certificate_source_backpropagation_gate_status(artifact_gates);
    }

    if let Some(production) = &loader.production_export {
        if production.status != "not_requested" {
            return checked_certificate_source_backpropagation_gate_status([
                &production.source_backpropagation_gate
            ]);
        }
    }

    "missing".to_string()
}

fn checked_certificate_source_backpropagation_gate_status<'a>(
    gates: impl IntoIterator<Item = &'a CheckedBinaryCertificateSourceBackpropagationGate>,
) -> String {
    let mut saw_gate = false;
    let mut all_accepted = true;
    for gate in gates {
        saw_gate = true;
        all_accepted = all_accepted
            && checked_certificate_source_backpropagation_gate_allows_source_rewrites(gate);
    }

    if !saw_gate {
        "missing".to_string()
    } else if all_accepted {
        "accepted".to_string()
    } else {
        "rejected".to_string()
    }
}

fn checked_certificate_source_backpropagation_gate_allows_source_rewrites(
    gate: &CheckedBinaryCertificateSourceBackpropagationGate,
) -> bool {
    gate.source_backpropagation_allowed
        && gate.replay_grade_artifact_identity
        && gate.checked_certificate_identity
        && gate.exact_replay_identity
        && gate.accepted_reconstruction_validation
        && gate.accepted_target_validation
        && gate.exact_source_provenance
        && gate.source_provenance.effective_source_backpropagation_allowed()
        && gate.unsupported_ledger_summary.is_empty()
        && (gate.preserved_symbolic_formulas == 0 || gate.symbolic_formula_consumer_accepted)
        && gate.blockers.is_empty()
}

fn source_backpropagation_source_provenance_status(
    source_provenance: &BinarySourceProvenanceSummary,
) -> String {
    if source_provenance.effective_source_backpropagation_allowed() {
        "accepted".to_string()
    } else if source_provenance.status == "unavailable"
        && source_provenance.exact_mapping_count == 0
    {
        "missing".to_string()
    } else {
        "rejected".to_string()
    }
}

fn source_backpropagation_source_provenance_blockers(
    source_provenance: &BinarySourceProvenanceSummary,
    stage: &'static str,
) -> Vec<SourceBackpropagationBlockerReport> {
    if source_provenance.effective_source_backpropagation_allowed() {
        return Vec::new();
    }
    source_provenance
        .typed_diagnostics()
        .into_iter()
        .map(|diagnostic| {
            source_backpropagation_blocker(
                stage,
                "exact-source-provenance-missing",
                "exact-source-provenance",
                format!("{}: {}", diagnostic.kind.label(), diagnostic.message),
                vec!["exact_binary_source_provenance"],
            )
        })
        .collect()
}

fn decompile_reconstruction_evidence_status(report: &DecompileReport) -> String {
    if report.output_trust_level == "proof_grade"
        && report.output_validation == "translation_validated"
        && report.target_validation_blockers.is_empty()
        && report.unsupported == 0
        && report.failures == 0
    {
        "accepted".to_string()
    } else if report.output_kind.is_some() || report.output_content.is_some() {
        "partial".to_string()
    } else {
        "missing".to_string()
    }
}

fn source_backpropagation_blocker(
    stage: &'static str,
    code: &'static str,
    feature: &'static str,
    detail: impl Into<String>,
    evidence_required: Vec<&'static str>,
) -> SourceBackpropagationBlockerReport {
    SourceBackpropagationBlockerReport {
        code: code.to_string(),
        stage: stage.to_string(),
        feature: feature.to_string(),
        detail: detail.into(),
        evidence_required: evidence_required.into_iter().map(str::to_string).collect(),
    }
}

fn build_target_proof_consumer_evidence(
    report: &DecompileReport,
    checked_certificate_loader: &ConvertCheckedCertificateLoaderReport,
) -> Option<TargetProofConsumerEvidenceReport> {
    if !binary_derived_conversion_requires_target_gate(report.target) {
        return None;
    }
    if let Some(evidence) = target_proof_consumer_evidence_from_output(report) {
        return Some(normalize_target_proof_consumer_evidence(report, evidence));
    }
    Some(synthesized_target_proof_consumer_evidence(report, checked_certificate_loader))
}

fn target_proof_consumer_evidence_from_output(
    report: &DecompileReport,
) -> Option<TargetProofConsumerEvidenceReport> {
    let output = serde_json::from_str::<serde_json::Value>(report.output_content.as_ref()?).ok()?;
    let evidence = output
        .get("target_proof_consumer_evidence")
        .or_else(|| output.get("target_proof_consumer"))?;
    serde_json::from_value(evidence.clone()).ok()
}

fn normalize_target_proof_consumer_evidence(
    report: &DecompileReport,
    mut evidence: TargetProofConsumerEvidenceReport,
) -> TargetProofConsumerEvidenceReport {
    let expected_target = report.target.label();
    if evidence.target.is_empty() {
        evidence.target = expected_target.to_string();
    }
    if evidence.target != expected_target {
        push_target_proof_consumer_blocker(
            &mut evidence.blockers,
            TargetProofConsumerBlockerReport {
                code: "target-proof-consumer-target-mismatch".to_string(),
                detail: format!(
                    "target proof-consumer evidence is for `{}` but conversion target is `{expected_target}`",
                    evidence.target
                ),
            },
        );
    }
    if report.target == DecompileTarget::TrustIr {
        normalize_trust_ir_target_proof_consumer_binding(report, &mut evidence);
    }
    for blocker in target_proof_consumer_symbolic_formula_blockers(report, &evidence) {
        if !evidence
            .blockers
            .iter()
            .any(|existing| existing.code == blocker.code && existing.detail == blocker.detail)
        {
            evidence.blockers.push(blocker);
        }
    }
    normalize_target_proof_consumer_binding_digest(&mut evidence);
    let binding_blockers = target_proof_consumer_binding_blockers(report, &evidence);
    if !target_proof_consumer_accepted_for_report(report, &evidence) {
        evidence.status = "rejected".to_string();
        evidence.target_semantics_consumed = false;
        for blocker in binding_blockers {
            if !evidence
                .blockers
                .iter()
                .any(|existing| existing.code == blocker.code && existing.detail == blocker.detail)
            {
                evidence.blockers.push(blocker);
            }
        }
        if evidence.blockers.is_empty() {
            push_target_proof_consumer_blocker(
                &mut evidence.blockers,
                TargetProofConsumerBlockerReport {
                    code: "target-proof-consumer-not-accepted".to_string(),
                    detail: format!(
                        "{} target semantics have not accepted every formula, checked-certificate, and replay input",
                        expected_target
                    ),
                },
            );
        }
    }
    evidence
}

fn normalize_target_proof_consumer_binding_digest(
    evidence: &mut TargetProofConsumerEvidenceReport,
) {
    match evidence.binding.as_ref().and_then(stable_json_sha256) {
        Some(computed) => match evidence.binding_sha256.as_deref() {
            Some(supplied) if !trust_types::digest::is_stable_sha256_hex(supplied) => {
                evidence.blockers.push(TargetProofConsumerBlockerReport {
                    code: "target-proof-consumer-binding-digest-noncanonical".to_string(),
                    detail: format!(
                        "{} target proof-consumer binding digest is not canonical lowercase SHA-256",
                        evidence.target
                    ),
                });
                evidence.binding_sha256 = Some(computed);
            }
            Some(supplied) if supplied != computed => {
                evidence.blockers.push(TargetProofConsumerBlockerReport {
                    code: "target-proof-consumer-binding-digest-mismatch".to_string(),
                    detail: format!(
                        "{} target proof-consumer binding digest does not match the carried binding artifact",
                        evidence.target
                    ),
                });
                evidence.binding_sha256 = Some(computed);
            }
            Some(_) => {}
            None => {
                evidence.binding_sha256 = Some(computed);
            }
        },
        None if evidence.status == "accepted" || evidence.target_semantics_consumed => {
            evidence.blockers.push(TargetProofConsumerBlockerReport {
                code: "target-proof-consumer-binding-missing".to_string(),
                detail: format!(
                    "{} target proof-consumer acceptance is missing a digest-bound binding artifact",
                    evidence.target
                ),
            });
        }
        None => {}
    }
}

fn synthesized_target_proof_consumer_evidence(
    report: &DecompileReport,
    checked_certificate_loader: &ConvertCheckedCertificateLoaderReport,
) -> TargetProofConsumerEvidenceReport {
    if report.target == DecompileTarget::TrustIr {
        return synthesized_trust_ir_target_proof_consumer_evidence(report);
    }

    let target = report.target.label();
    let target_identifier = match report.target {
        DecompileTarget::TrustCg => "trust_cg-lir",
        DecompileTarget::Wasm => "wasm32",
        DecompileTarget::TrustIr | DecompileTarget::Rust => target,
    };
    let target_label = target.to_ascii_uppercase();
    let mut records = vec![TargetProofConsumerRecordReport {
        kind: "target_semantics".to_string(),
        identifier: target_identifier.to_string(),
        accepted: false,
        detail: format!(
            "{target_label} target semantics have not consumed conversion proof inputs"
        ),
        formula_schema: None,
        formula_sort: None,
        formula_digest: None,
        formula_origin: None,
    }];

    let symbolic_formulas = report
        .preserved_symbolic_formulas
        .iter()
        .filter(|formula| decompile_artifact_target_label(&formula.target) == target)
        .collect::<Vec<_>>();
    records.extend(symbolic_formulas.iter().map(|formula| {
        let evidence = formula.evidence();
        TargetProofConsumerRecordReport {
            kind: "symbolic_formula".to_string(),
            identifier: target_proof_consumer_formula_identifier(formula),
            accepted: false,
            detail: format!(
                "symbolic formula JSON/SMT-LIB/sort metadata is preserved, but {target_label} target semantics have not consumed it: schema={} sort={} digest={} origin={}",
                evidence.schema, evidence.sort, evidence.digest, evidence.origin
            ),
            formula_schema: Some(evidence.schema),
            formula_sort: Some(evidence.sort),
            formula_digest: Some(evidence.digest),
            formula_origin: Some(evidence.origin),
        }
    }));

    if checked_certificate_loader.readback_records.is_empty() {
        records.push(TargetProofConsumerRecordReport {
            kind: "checked_certificate".to_string(),
            identifier: "missing".to_string(),
            accepted: false,
            detail: format!(
                "no checked certificate metadata was carried into the {target_label} target proof consumer"
            ),
            formula_schema: None,
            formula_sort: None,
            formula_digest: None,
            formula_origin: None,
        });
        records.push(TargetProofConsumerRecordReport {
            kind: "proof_replay".to_string(),
            identifier: "missing".to_string(),
            accepted: false,
            detail: format!(
                "no proof replay metadata was carried into the {target_label} target proof consumer"
            ),
            formula_schema: None,
            formula_sort: None,
            formula_digest: None,
            formula_origin: None,
        });
    } else {
        for record in &checked_certificate_loader.readback_records {
            records.push(TargetProofConsumerRecordReport {
                kind: "checked_certificate".to_string(),
                identifier: record.dispatch_id.clone(),
                accepted: false,
                detail: format!(
                    "checked certificate checker={} format={} sha256={} is preserved, but {target_label} target semantics have not consumed it",
                    record.checker, record.format, record.certificate_sha256
                ),
                formula_schema: None,
                formula_sort: None,
                formula_digest: None,
                formula_origin: None,
            });
            records.push(TargetProofConsumerRecordReport {
                kind: "proof_replay".to_string(),
                identifier: record.dispatch_id.clone(),
                accepted: false,
                detail: format!(
                    "proof replay status {} is preserved for the checked certificate, but {target_label} target semantics have not consumed it",
                    record.replay
                ),
                formula_schema: None,
                formula_sort: None,
                formula_digest: None,
                formula_origin: None,
            });
        }
    }

    let mut blockers = vec![TargetProofConsumerBlockerReport {
        code: "target-semantics-not-consumed".to_string(),
        detail: format!(
            "{target_label} target semantics have not consumed symbolic formula, checked-certificate, or replay metadata"
        ),
    }];
    for formula in &symbolic_formulas {
        let evidence = formula.evidence();
        blockers.push(TargetProofConsumerBlockerReport {
            code: "symbolic-formula-not-consumed-by-target-semantics".to_string(),
            detail: format!(
                "preserved symbolic formula is not consumed by {target_label} target semantics: identifier={} schema={} sort={} digest={} origin={}",
                target_proof_consumer_formula_identifier(formula),
                evidence.schema,
                evidence.sort,
                evidence.digest,
                evidence.origin
            ),
        });
    }
    if checked_certificate_loader.readback_records.is_empty() {
        blockers.push(TargetProofConsumerBlockerReport {
            code: "missing-checked-proof-certificate".to_string(),
            detail: format!(
                "{target_label} target proof consumer has no checked-certificate metadata to consume"
            ),
        });
        blockers.push(TargetProofConsumerBlockerReport {
            code: "missing-proof-replay-metadata".to_string(),
            detail: format!(
                "{target_label} target proof consumer has no proof replay metadata to consume"
            ),
        });
    } else {
        let replayed = checked_certificate_loader
            .readback_records
            .iter()
            .filter(|record| record.replay == "replayed")
            .count();
        blockers.push(TargetProofConsumerBlockerReport {
            code: "checked-certificate-not-consumed-by-target-semantics".to_string(),
            detail: format!(
                "{} checked certificate metadata record(s) are preserved but not consumed by {target_label} target semantics",
                checked_certificate_loader.readback_records.len()
            ),
        });
        blockers.push(TargetProofConsumerBlockerReport {
            code: "proof-replay-not-consumed-by-target-semantics".to_string(),
            detail: format!(
                "{} proof replay metadata record(s) are preserved ({} replayed) but not consumed by {target_label} target semantics",
                checked_certificate_loader.readback_records.len(),
                replayed
            ),
        });
    }

    TargetProofConsumerEvidenceReport {
        target: target.to_string(),
        status: "rejected".to_string(),
        target_semantics_consumed: false,
        records,
        binding: None,
        binding_sha256: None,
        blockers,
    }
}

fn synthesized_trust_ir_target_proof_consumer_evidence(
    report: &DecompileReport,
) -> TargetProofConsumerEvidenceReport {
    let evidence = trust_ir_target_artifact_evidence(report);
    let accepted = evidence.blockers.is_empty();
    let blockers = evidence.blockers;
    let binding = TargetProofBindingReport {
        target: "trust_ir".to_string(),
        target_output: evidence.target_output.clone(),
        status: if accepted { "accepted" } else { "rejected" }.to_string(),
        target_semantics_consumed: accepted,
        inputs: evidence.binding_inputs,
        blockers: blockers.clone(),
    };
    let binding_sha256 = stable_json_sha256(&binding);

    TargetProofConsumerEvidenceReport {
        target: "trust_ir".to_string(),
        status: if accepted { "accepted" } else { "rejected" }.to_string(),
        target_semantics_consumed: accepted,
        records: evidence.records,
        binding: Some(binding),
        binding_sha256,
        blockers,
    }
}

fn normalize_trust_ir_target_proof_consumer_binding(
    report: &DecompileReport,
    evidence: &mut TargetProofConsumerEvidenceReport,
) {
    let expected = trust_ir_target_artifact_evidence(report);
    for blocker in &expected.blockers {
        push_target_proof_consumer_blocker(&mut evidence.blockers, blocker.clone());
    }

    match evidence.binding.as_ref() {
        Some(binding) => {
            if binding.target != "trust_ir" {
                push_target_proof_consumer_blocker(
                    &mut evidence.blockers,
                    TargetProofConsumerBlockerReport {
                        code: "trust_ir-target-proof-binding-target-mismatch".to_string(),
                        detail: format!(
                            "TrustIr target proof binding is for `{}` but expected `trust_ir`",
                            binding.target
                        ),
                    },
                );
            }
            if binding.target_output != expected.target_output {
                push_target_proof_consumer_blocker(
                    &mut evidence.blockers,
                    TargetProofConsumerBlockerReport {
                        code: "trust_ir-target-output-digest-mismatch".to_string(),
                        detail: format!(
                            "TrustIr target proof binding names `{}` but current output content is `{}`",
                            binding.target_output, expected.target_output
                        ),
                    },
                );
            }
            for required in &expected.binding_inputs {
                if !binding.inputs.iter().any(|input| {
                    input.kind == required.kind
                        && input.identifier == required.identifier
                        && input.target_output == expected.target_output
                        && input.consumed_by_target_semantics
                }) {
                    push_target_proof_consumer_blocker(
                        &mut evidence.blockers,
                        TargetProofConsumerBlockerReport {
                            code: "trust_ir-target-proof-binding-input-missing".to_string(),
                            detail: format!(
                                "TrustIr target proof binding lacks consumed `{}` input `{}` for `{}`",
                                required.kind, required.identifier, expected.target_output
                            ),
                        },
                    );
                }
            }
        }
        None => push_target_proof_consumer_blocker(
            &mut evidence.blockers,
            TargetProofConsumerBlockerReport {
                code: "trust_ir-target-proof-binding-missing".to_string(),
                detail: format!(
                    "TrustIr target proof-consumer evidence lacks a content-addressed binding for `{}`",
                    expected.target_output
                ),
            },
        ),
    }

    for required in &expected.records {
        if !evidence.records.iter().any(|record| {
            record.kind == required.kind
                && record.identifier == required.identifier
                && record.accepted
        }) {
            push_target_proof_consumer_blocker(
                &mut evidence.blockers,
                TargetProofConsumerBlockerReport {
                    code: "trust_ir-target-proof-consumer-record-missing".to_string(),
                    detail: format!(
                        "TrustIr target proof-consumer evidence lacks accepted `{}` record `{}`",
                        required.kind, required.identifier
                    ),
                },
            );
        }
    }
}

fn trust_ir_target_artifact_evidence(report: &DecompileReport) -> TrustIrTargetArtifactEvidence {
    let target_output = report
        .output_content
        .as_deref()
        .map(trust_ir_target_output_identifier)
        .unwrap_or_else(|| "trust_ir-json:missing".to_string());
    let mut blockers = Vec::new();

    if report.output_kind.as_deref() != Some("trust_ir_json") {
        push_target_proof_consumer_blocker(
            &mut blockers,
            TargetProofConsumerBlockerReport {
                code: "trust_ir-target-output-kind-mismatch".to_string(),
                detail: format!(
                    "TrustIr target consumer requires emitted `trust_ir_json` output, found `{}`",
                    report.output_kind.as_deref().unwrap_or("missing")
                ),
            },
        );
    }

    let Some(output_content) = report.output_content.as_deref() else {
        push_target_proof_consumer_blocker(
            &mut blockers,
            TargetProofConsumerBlockerReport {
                code: "trust_ir-target-artifact-missing".to_string(),
                detail: "TrustIr target consumer requires emitted TrustIr JSON output_content"
                    .to_string(),
            },
        );
        return trust_ir_target_artifact_evidence_result(target_output, blockers, None, None);
    };

    let artifact = match serde_json::from_str::<serde_json::Value>(output_content) {
        Ok(artifact) => artifact,
        Err(error) => {
            push_target_proof_consumer_blocker(
                &mut blockers,
                TargetProofConsumerBlockerReport {
                    code: "trust_ir-target-artifact-unparseable".to_string(),
                    detail: format!(
                        "TrustIr target consumer could not parse emitted TrustIr JSON artifact: {error}"
                    ),
                },
            );
            return trust_ir_target_artifact_evidence_result(target_output, blockers, None, None);
        }
    };

    if artifact.get("module").is_none() {
        push_target_proof_consumer_blocker(
            &mut blockers,
            TargetProofConsumerBlockerReport {
                code: "trust_ir-target-artifact-module-missing".to_string(),
                detail: "emitted TrustIr JSON artifact lacks a `module` object".to_string(),
            },
        );
    }
    let lifted_identity = trust_ir_lifted_artifact_identity(report, &artifact, &mut blockers);
    let refinement_identity =
        trust_ir_reconstruction_refinement_identity(report, &artifact, &mut blockers);
    if !report.target_validation_blockers.is_empty() {
        push_target_proof_consumer_blocker(
            &mut blockers,
            TargetProofConsumerBlockerReport {
                code: "trust_ir-target-validation-blockers-present".to_string(),
                detail: format!(
                    "TrustIr target identity has {} target validation blocker(s)",
                    report.target_validation_blockers.len()
                ),
            },
        );
    }

    trust_ir_target_artifact_evidence_result(
        target_output,
        blockers,
        lifted_identity,
        refinement_identity,
    )
}

fn trust_ir_target_artifact_evidence_result(
    target_output: String,
    blockers: Vec<TargetProofConsumerBlockerReport>,
    lifted_identity: Option<String>,
    refinement_identity: Option<String>,
) -> TrustIrTargetArtifactEvidence {
    let accepted = blockers.is_empty();
    let target_artifact_accepted = target_output != "trust_ir-json:missing"
        && !blockers.iter().any(|blocker| blocker.code == "trust_ir-target-artifact-unparseable");
    let lifted_accepted = lifted_identity.is_some();
    let refinement_accepted = refinement_identity.is_some();
    let lifted_identifier =
        lifted_identity.unwrap_or_else(|| "lifted-binary-trust_ir:unaccepted".to_string());
    let refinement_identifier = refinement_identity
        .unwrap_or_else(|| "structured-trust_ir-refinement:unaccepted".to_string());

    let records = vec![
        TargetProofConsumerRecordReport {
            kind: "target_semantics".to_string(),
            identifier: "trust_ir-identity-consumer".to_string(),
            accepted,
            detail: if accepted {
                format!(
                    "TrustIr target semantics consumed the content-addressed lifted TrustIr artifact `{target_output}`"
                )
            } else {
                "TrustIr target semantics did not accept the emitted artifact identity".to_string()
            },
            formula_schema: None,
            formula_sort: None,
            formula_digest: None,
            formula_origin: None,
        },
        TargetProofConsumerRecordReport {
            kind: "target_artifact".to_string(),
            identifier: target_output.clone(),
            accepted: target_artifact_accepted,
            detail: format!("emitted TrustIr target artifact is addressed as `{target_output}`"),
            formula_schema: None,
            formula_sort: None,
            formula_digest: None,
            formula_origin: None,
        },
        TargetProofConsumerRecordReport {
            kind: "lifted_binary_trust_ir".to_string(),
            identifier: lifted_identifier.clone(),
            accepted: lifted_accepted,
            detail: if lifted_accepted {
                "emitted TrustIr functions match the selected lifted binary TrustIr functions"
                    .to_string()
            } else {
                "emitted TrustIr functions do not prove identity with the selected lifted binary TrustIr functions"
                    .to_string()
            },
            formula_schema: None,
            formula_sort: None,
            formula_digest: None,
            formula_origin: None,
        },
        TargetProofConsumerRecordReport {
            kind: "reconstruction_refinement".to_string(),
            identifier: refinement_identifier.clone(),
            accepted: refinement_accepted,
            detail: if refinement_accepted {
                "structured TrustIr identity/refinement relation is validated for the emitted target"
                    .to_string()
            } else {
                "structured TrustIr identity/refinement relation is not accepted for the emitted target"
                    .to_string()
            },
            formula_schema: None,
            formula_sort: None,
            formula_digest: None,
            formula_origin: None,
        },
    ];
    let binding_inputs = vec![
        trust_ir_target_binding_input(
            "target_artifact",
            target_output.as_str(),
            "targo_trust.decompile.output_content",
            target_output.as_str(),
            target_artifact_accepted,
            "content-addressed emitted TrustIr JSON artifact",
        ),
        trust_ir_target_binding_input(
            "lifted_binary_trust_ir",
            lifted_identifier.as_str(),
            "trust_decompile.lifted_binary_trust_ir",
            target_output.as_str(),
            lifted_accepted,
            "selected lifted binary TrustIr function identity",
        ),
        trust_ir_target_binding_input(
            "reconstruction_refinement",
            refinement_identifier.as_str(),
            "trust_decompile.reconstruction.validation_records",
            target_output.as_str(),
            refinement_accepted,
            "structured TrustIr identity/refinement validation relation",
        ),
    ];

    TrustIrTargetArtifactEvidence { target_output, records, binding_inputs, blockers }
}

fn trust_ir_target_binding_input(
    kind: &str,
    identifier: &str,
    canonical_source: &str,
    target_output: &str,
    consumed_by_target_semantics: bool,
    detail: &str,
) -> TargetProofBindingInputReport {
    TargetProofBindingInputReport {
        kind: kind.to_string(),
        identifier: identifier.to_string(),
        canonical_source: canonical_source.to_string(),
        target_output: target_output.to_string(),
        consumed_by_target_semantics,
        detail: detail.to_string(),
        formula_schema: None,
        formula_sort: None,
        formula_digest: None,
        formula_origin: None,
    }
}

fn trust_ir_target_output_identifier(output_content: &str) -> String {
    format!("trust_ir-json:sha256:{}", trust_types::digest::stable_sha256_hex(output_content.as_bytes()))
}

fn trust_ir_lifted_artifact_identity(
    report: &DecompileReport,
    artifact: &serde_json::Value,
    blockers: &mut Vec<TargetProofConsumerBlockerReport>,
) -> Option<String> {
    let Some(functions) = artifact.get("functions").and_then(serde_json::Value::as_array) else {
        push_target_proof_consumer_blocker(
            blockers,
            TargetProofConsumerBlockerReport {
                code: "trust_ir-lifted-artifact-functions-missing".to_string(),
                detail: "emitted TrustIr JSON artifact lacks a `functions` array".to_string(),
            },
        );
        return None;
    };

    if report.functions_decompiled == 0 || report.functions.is_empty() {
        push_target_proof_consumer_blocker(
            blockers,
            TargetProofConsumerBlockerReport {
                code: "trust_ir-lifted-artifact-empty".to_string(),
                detail:
                    "TrustIr target consumer requires at least one selected lifted binary function"
                        .to_string(),
            },
        );
        return None;
    }
    if functions.len() != report.functions.len() || functions.len() != report.functions_decompiled {
        push_target_proof_consumer_blocker(
            blockers,
            TargetProofConsumerBlockerReport {
                code: "trust_ir-lifted-artifact-mismatch".to_string(),
                detail: format!(
                    "emitted TrustIr function count {} does not match report function count {} / functions_decompiled {}",
                    functions.len(),
                    report.functions.len(),
                    report.functions_decompiled
                ),
            },
        );
        return None;
    }

    let mut projection = Vec::with_capacity(report.functions.len());
    for expected in &report.functions {
        let Some(expected_entry) = parse_report_hex_address(&expected.entry) else {
            push_target_proof_consumer_blocker(
                blockers,
                TargetProofConsumerBlockerReport {
                    code: "trust_ir-lifted-artifact-report-entry-invalid".to_string(),
                    detail: format!(
                        "report function `{}` has non-hex entry `{}`",
                        expected.name, expected.entry
                    ),
                },
            );
            return None;
        };
        let matched = functions.iter().any(|function| {
            function.get("name").and_then(serde_json::Value::as_str) == Some(expected.name.as_str())
                && function.get("entry").and_then(serde_json::Value::as_u64) == Some(expected_entry)
        });
        if !matched {
            push_target_proof_consumer_blocker(
                blockers,
                TargetProofConsumerBlockerReport {
                    code: "trust_ir-lifted-artifact-mismatch".to_string(),
                    detail: format!(
                        "emitted TrustIr artifact does not contain selected lifted function `{}` at {}",
                        expected.name, expected.entry
                    ),
                },
            );
            return None;
        }
        projection.push(serde_json::json!({
            "name": expected.name,
            "entry": expected.entry,
            "blocks": expected.blocks,
            "instructions": expected.instructions,
            "statements": expected.statements,
            "memory_facts": expected.memory_facts,
        }));
    }

    let bytes = serde_json::to_vec(&projection)
        .expect("serializing TrustIr lifted-function identity projection should not fail");
    Some(format!("lifted-binary-trust_ir:sha256:{}", trust_types::digest::stable_sha256_hex(&bytes)))
}

fn trust_ir_reconstruction_refinement_identity(
    report: &DecompileReport,
    artifact: &serde_json::Value,
    blockers: &mut Vec<TargetProofConsumerBlockerReport>,
) -> Option<String> {
    if report.output_validation != "lifted_trust_ir_partial" {
        push_target_proof_consumer_blocker(
            blockers,
            TargetProofConsumerBlockerReport {
                code: "trust_ir-refinement-validation-missing".to_string(),
                detail: format!(
                    "TrustIr target identity requires `lifted_trust_ir_partial` validation, found `{}`",
                    report.output_validation
                ),
            },
        );
        return None;
    }
    let trust_level =
        artifact.get("trust_level").and_then(serde_json::Value::as_str).unwrap_or("unknown");
    let refinement_projection = serde_json::json!({
        "target": "trust_ir",
        "output_validation": report.output_validation,
        "output_kind": report.output_kind,
        "artifact_trust_level": trust_level,
        "functions_decompiled": report.functions_decompiled,
    });
    let bytes = serde_json::to_vec(&refinement_projection)
        .expect("serializing TrustIr refinement identity projection should not fail");
    Some(format!("structured-trust_ir-refinement:sha256:{}", trust_types::digest::stable_sha256_hex(&bytes)))
}

fn parse_report_hex_address(address: &str) -> Option<u64> {
    let hex = address.strip_prefix("0x").or_else(|| address.strip_prefix("0X"))?;
    u64::from_str_radix(hex, 16).ok()
}

fn push_target_proof_consumer_blocker(
    blockers: &mut Vec<TargetProofConsumerBlockerReport>,
    blocker: TargetProofConsumerBlockerReport,
) {
    if !blockers
        .iter()
        .any(|existing| existing.code == blocker.code && existing.detail == blocker.detail)
    {
        blockers.push(blocker);
    }
}

fn target_proof_consumer_formula_identifier(formula: &PreservedSymbolicFormula) -> String {
    let function = formula.function.as_deref().unwrap_or("unknown");
    let block =
        formula.block.map(|block| format!("bb{block}")).unwrap_or_else(|| "bb_unknown".to_string());
    let statement = formula
        .statement_index
        .map(|statement| format!("stmt{statement}"))
        .unwrap_or_else(|| "stmt_unknown".to_string());
    format!("{function}::{block}::{statement}::{}", formula.location)
}

fn target_proof_consumer_symbolic_formula_blockers(
    report: &DecompileReport,
    evidence: &TargetProofConsumerEvidenceReport,
) -> Vec<TargetProofConsumerBlockerReport> {
    report
        .preserved_symbolic_formulas
        .iter()
        .filter(|formula| decompile_artifact_target_label(&formula.target) == report.target.label())
        .filter(|formula| !target_proof_consumer_has_accepted_formula(evidence, formula))
        .map(|formula| {
            let formula_evidence = formula.evidence();
            TargetProofConsumerBlockerReport {
                code: "symbolic-formula-schema-aware-consumer-missing".to_string(),
                detail: format!(
                    "target proof consumer did not accept preserved trust_symbolic.formula with exact schema-aware evidence: identifier={} schema={} sort={} digest={} origin={}",
                    target_proof_consumer_formula_identifier(formula),
                    formula_evidence.schema,
                    formula_evidence.sort,
                    formula_evidence.digest,
                    formula_evidence.origin
                ),
            }
        })
        .collect()
}

fn target_proof_consumer_has_accepted_formula(
    evidence: &TargetProofConsumerEvidenceReport,
    formula: &PreservedSymbolicFormula,
) -> bool {
    evidence
        .records
        .iter()
        .any(|record| target_proof_consumer_record_consumes_formula(record, formula))
}

fn target_proof_consumer_record_consumes_formula(
    record: &TargetProofConsumerRecordReport,
    formula: &PreservedSymbolicFormula,
) -> bool {
    let evidence = formula.evidence();
    record.kind == "symbolic_formula"
        && record.accepted
        && record.identifier == target_proof_consumer_formula_identifier(formula)
        && record.formula_schema.as_deref() == Some(evidence.schema.as_str())
        && record.formula_sort.as_deref() == Some(evidence.sort.as_str())
        && record.formula_digest.as_deref() == Some(evidence.digest.as_str())
        && record.formula_origin.as_deref() == Some(evidence.origin.as_str())
}

fn target_proof_consumer_has_accepted_formulas(
    report: &DecompileReport,
    evidence: &TargetProofConsumerEvidenceReport,
) -> bool {
    report
        .preserved_symbolic_formulas
        .iter()
        .filter(|formula| decompile_artifact_target_label(&formula.target) == report.target.label())
        .all(|formula| target_proof_consumer_has_accepted_formula(evidence, formula))
}

fn target_proof_consumer_accepted_for_report(
    report: &DecompileReport,
    evidence: &TargetProofConsumerEvidenceReport,
) -> bool {
    if report.target == DecompileTarget::TrustIr {
        return evidence.target == "trust_ir"
            && evidence.status == "accepted"
            && evidence.target_semantics_consumed
            && evidence.blockers.is_empty()
            && target_proof_consumer_has_accepted_kind(evidence, "target_semantics")
            && target_proof_consumer_has_accepted_kind(evidence, "target_artifact")
            && target_proof_consumer_has_accepted_kind(evidence, "lifted_binary_trust_ir")
            && target_proof_consumer_has_accepted_kind(evidence, "reconstruction_refinement")
            && evidence.records.iter().all(|record| record.accepted)
            && evidence.binding.as_ref().is_some_and(|binding| {
                binding.target == "trust_ir"
                    && binding.status == "accepted"
                    && binding.target_semantics_consumed
                    && binding.blockers.is_empty()
                    && binding.inputs.iter().all(|input| input.consumed_by_target_semantics)
            });
    }

    evidence.target == report.target.label()
        && evidence.status == "accepted"
        && evidence.target_semantics_consumed
        && evidence.blockers.is_empty()
        && target_proof_consumer_has_binding_digest(evidence)
        && target_proof_consumer_has_accepted_kind(evidence, "target_semantics")
        && target_proof_consumer_has_accepted_kind(evidence, "checked_certificate")
        && target_proof_consumer_has_accepted_kind(evidence, "proof_replay")
        && target_proof_consumer_binding_accepted_for_report(report, evidence)
        && target_proof_consumer_has_accepted_formulas(report, evidence)
        && evidence.records.iter().all(|record| record.accepted)
}

fn target_proof_consumer_binding_accepted_for_report(
    report: &DecompileReport,
    evidence: &TargetProofConsumerEvidenceReport,
) -> bool {
    target_proof_consumer_binding_blockers(report, evidence).is_empty()
}

fn target_proof_consumer_binding_blockers(
    report: &DecompileReport,
    evidence: &TargetProofConsumerEvidenceReport,
) -> Vec<TargetProofConsumerBlockerReport> {
    if !binary_derived_conversion_requires_target_gate(report.target) {
        return Vec::new();
    }

    let expected_target = report.target.label();
    let Some(binding) = evidence.binding.as_ref() else {
        return vec![TargetProofConsumerBlockerReport {
            code: "target-proof-consumer-binding-missing".to_string(),
            detail: format!(
                "{expected_target} target proof-consumer evidence is accepted only with an accepted target-output binding"
            ),
        }];
    };

    let mut blockers = Vec::new();
    if binding.target != expected_target {
        blockers.push(TargetProofConsumerBlockerReport {
            code: "target-proof-consumer-binding-target-mismatch".to_string(),
            detail: format!(
                "target proof-consumer binding is for `{}` but conversion target is `{expected_target}`",
                binding.target
            ),
        });
    }
    if binding.status != "accepted" {
        blockers.push(TargetProofConsumerBlockerReport {
            code: "target-proof-consumer-binding-not-accepted".to_string(),
            detail: format!(
                "{expected_target} target proof-consumer binding status is `{}`",
                binding.status
            ),
        });
    }
    if !binding.target_semantics_consumed {
        blockers.push(TargetProofConsumerBlockerReport {
            code: "target-proof-consumer-binding-semantics-not-consumed".to_string(),
            detail: format!(
                "{expected_target} target proof-consumer binding did not consume target semantics"
            ),
        });
    }
    if binding.target_output.trim().is_empty() {
        blockers.push(TargetProofConsumerBlockerReport {
            code: "target-proof-consumer-binding-output-missing".to_string(),
            detail: format!("{expected_target} target proof-consumer binding has no target output"),
        });
    }
    for blocker in &binding.blockers {
        blockers.push(TargetProofConsumerBlockerReport {
            code: blocker.code.clone(),
            detail: format!(
                "{expected_target} target proof-consumer binding blocker: {}",
                blocker.detail
            ),
        });
    }

    for requirement in target_proof_consumer_required_binding_inputs(report) {
        let accepted_record = evidence
            .records
            .iter()
            .find(|record| record.kind == requirement.record_kind && record.accepted);
        let Some(record) = accepted_record else {
            blockers.push(TargetProofConsumerBlockerReport {
                code: "target-proof-consumer-binding-record-missing".to_string(),
                detail: format!(
                    "{expected_target} target proof-consumer binding requires an accepted {} record",
                    requirement.record_kind
                ),
            });
            continue;
        };

        let bound = binding.inputs.iter().any(|input| {
            input.identifier == record.identifier
                && input.canonical_source == requirement.canonical_source
                && input.consumed_by_target_semantics
                && input.target_output == binding.target_output
        });
        if !bound {
            blockers.push(TargetProofConsumerBlockerReport {
                code: "target-proof-consumer-binding-input-missing".to_string(),
                detail: format!(
                    "{expected_target} target proof-consumer binding does not consume {} input `{}` from {}",
                    requirement.record_kind, record.identifier, requirement.canonical_source
                ),
            });
        }
    }

    blockers
}

#[derive(Debug, Clone, Copy)]
struct TargetProofConsumerBindingRequirement {
    record_kind: &'static str,
    canonical_source: &'static str,
}

fn target_proof_consumer_required_binding_inputs(
    report: &DecompileReport,
) -> Vec<TargetProofConsumerBindingRequirement> {
    let mut requirements = vec![
        TargetProofConsumerBindingRequirement {
            record_kind: "binary_provenance",
            canonical_source: "trust_binary.provenance",
        },
        TargetProofConsumerBindingRequirement {
            record_kind: "checked_certificate",
            canonical_source: "trust_proof.checked_certificate",
        },
        TargetProofConsumerBindingRequirement {
            record_kind: "proof_replay",
            canonical_source: "trust_proof.proof_replay",
        },
    ];
    if report
        .preserved_symbolic_formulas
        .iter()
        .any(|formula| decompile_artifact_target_label(&formula.target) == report.target.label())
    {
        requirements.push(TargetProofConsumerBindingRequirement {
            record_kind: "symbolic_formula",
            canonical_source: "trust_symbolic.formula",
        });
    }
    requirements
}

fn target_proof_consumer_has_binding_digest(evidence: &TargetProofConsumerEvidenceReport) -> bool {
    evidence.binding.is_some()
        && evidence.binding_sha256.as_deref().is_some_and(trust_types::digest::is_stable_sha256_hex)
}

fn target_proof_consumer_has_accepted_kind(
    evidence: &TargetProofConsumerEvidenceReport,
    kind: &str,
) -> bool {
    evidence.records.iter().any(|record| record.kind == kind && record.accepted)
}

fn target_proof_consumer_gate_blockers(
    evidence: &TargetProofConsumerEvidenceReport,
) -> Vec<String> {
    if evidence.blockers.is_empty() {
        return vec![format!(
            "target-proof-consumer-not-accepted: {} target proof consumer status is `{}`",
            evidence.target, evidence.status
        )];
    }
    evidence
        .blockers
        .iter()
        .map(|blocker| format!("target-proof-consumer:{}: {}", blocker.code, blocker.detail))
        .collect()
}

fn build_decompile_target_evidence(
    report: &DecompileReport,
    target_proof_consumer_evidence: Option<&TargetProofConsumerEvidenceReport>,
) -> DecompileTargetEvidenceReport {
    let symbolic_formula_preservation = DecompileSymbolicFormulaPreservationReport {
        preserved_count: report.preserved_symbolic_formulas.len(),
        consumer_accepted: decompile_symbolic_formula_consumer_accepted(
            report,
            target_proof_consumer_evidence,
        ),
        formula_evidence: report
            .preserved_symbolic_formulas
            .iter()
            .map(PreservedSymbolicFormula::evidence)
            .collect(),
        formulas: report.preserved_symbolic_formulas.clone(),
    };
    let mut blockers = report
        .target_validation_blockers
        .iter()
        .map(decompile_target_validation_blocker_report)
        .collect::<Vec<_>>();

    if binary_derived_conversion_requires_target_gate(report.target) {
        if let Some(evidence) = target_proof_consumer_evidence {
            blockers.extend(evidence.blockers.iter().map(|blocker| {
                DecompileEvidenceBlockerReport {
                    code: blocker.code.clone(),
                    stage: "targo-trust::target-proof-consumer".to_string(),
                    feature: "target-proof-consumer".to_string(),
                    detail: blocker.detail.clone(),
                    evidence_required: vec!["target_semantic_validation".to_string()],
                }
            }));
        }
    }

    if symbolic_formula_preservation.preserved_count > 0
        && !symbolic_formula_preservation.consumer_accepted
    {
        blockers.push(DecompileEvidenceBlockerReport {
            code: "symbolic-formula-preservation-not-consumed".to_string(),
            stage: "targo-trust::target-evidence".to_string(),
            feature: "symbolic-formula-preservation".to_string(),
            detail: format!(
                "{} preserved symbolic formula record(s) are audit evidence until target semantics consume them",
                symbolic_formula_preservation.preserved_count
            ),
            evidence_required: vec![
                "preserved_symbolic_formula".to_string(),
                "target_semantic_validation".to_string(),
            ],
        });
    }

    DecompileTargetEvidenceReport {
        target: report.target.label().to_string(),
        output_validation: report.output_validation.clone(),
        output_trust_level: report.output_trust_level.clone(),
        target_validation_blocker_count: report.target_validation_blockers.len(),
        symbolic_formula_preservation,
        target_validation_blockers: report.target_validation_blockers.clone(),
        target_proof_consumer_evidence: target_proof_consumer_evidence.cloned(),
        blockers,
    }
}

fn decompile_symbolic_formula_consumer_accepted(
    report: &DecompileReport,
    target_proof_consumer_evidence: Option<&TargetProofConsumerEvidenceReport>,
) -> bool {
    report.preserved_symbolic_formulas.is_empty()
        || target_proof_consumer_evidence.is_some_and(|evidence| {
            target_proof_consumer_accepted_for_report(report, evidence)
                && target_proof_consumer_has_accepted_formulas(report, evidence)
        })
}

fn decompile_target_validation_blocker_report(
    blocker: &TargetValidationBlocker,
) -> DecompileEvidenceBlockerReport {
    DecompileEvidenceBlockerReport {
        code: decompile_target_validation_blocker_code(blocker),
        stage: if blocker.stage.trim().is_empty() {
            "target-validation".to_string()
        } else {
            blocker.stage.clone()
        },
        feature: blocker.feature.clone(),
        detail: format_target_validation_blocker(blocker),
        evidence_required: decompile_target_validation_evidence_required(blocker),
    }
}

fn decompile_target_validation_blocker_code(blocker: &TargetValidationBlocker) -> String {
    if let Some(code) = target_validation_blocker_machine_code(blocker) {
        return code.to_string();
    }

    let text = format!(
        "{} {} {}",
        blocker.stage.to_ascii_lowercase(),
        blocker.feature.to_ascii_lowercase(),
        blocker.reason.to_ascii_lowercase()
    );
    if text.contains("symbolic") {
        "symbolic-formula-preservation-not-consumed".to_string()
    } else if text.contains("refinement") {
        "target-refinement-consumer-missing".to_string()
    } else if text.contains("source") || text.contains("provenance") {
        "exact-source-provenance-missing".to_string()
    } else if text.contains("replay") {
        "exact-machine-replay-missing".to_string()
    } else if text.contains("checked") || text.contains("certificate") || text.contains("proof") {
        "checked-certificate-missing".to_string()
    } else if text.contains("unsupported") || text.contains("supported-ledger") {
        "unsupported-ledger-nonempty".to_string()
    } else {
        "target-semantic-validation-missing".to_string()
    }
}

fn target_validation_blocker_machine_code(blocker: &TargetValidationBlocker) -> Option<&str> {
    nonempty_target_validation_blocker_code(&blocker.code)
        .or_else(|| {
            blocker.diagnostics.iter().find_map(|diagnostic| {
                diagnostic
                    .strip_prefix("blocker-code=")
                    .and_then(nonempty_target_validation_blocker_code)
            })
        })
        .or_else(|| stable_target_validation_blocker_feature(&blocker.feature))
}

fn nonempty_target_validation_blocker_code(value: &str) -> Option<&str> {
    let value = value.trim();
    (!value.is_empty()).then_some(value)
}

fn stable_target_validation_blocker_feature(value: &str) -> Option<&str> {
    let value = value.trim();
    (!value.is_empty()
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.' | b':')))
    .then_some(value)
}

fn decompile_target_validation_evidence_required(blocker: &TargetValidationBlocker) -> Vec<String> {
    let mut required = blocker
        .diagnostics
        .iter()
        .filter_map(|diagnostic| diagnostic.strip_prefix("required-evidence="))
        .map(str::to_string)
        .collect::<Vec<_>>();
    if required.is_empty() {
        if blocker.feature.contains("refinement") || blocker.reason.contains("refinement") {
            required.push("target_refinement_metadata".to_string());
        }
        required.push("target_semantic_validation".to_string());
    }
    required
}

fn binary_derived_conversion_requires_target_gate(target: DecompileTarget) -> bool {
    matches!(target, DecompileTarget::TrustIr | DecompileTarget::TrustCg | DecompileTarget::Wasm)
}

fn binary_derived_conversion_requires_checked_certificate_gate(target: DecompileTarget) -> bool {
    matches!(target, DecompileTarget::TrustIr | DecompileTarget::TrustCg | DecompileTarget::Wasm)
}

fn binary_derived_conversion_missing_checked_certificate_production_blockers(
    target: DecompileTarget,
    checked_certificate_readback_available: bool,
) -> Vec<String> {
    let target = target.label();
    if checked_certificate_readback_available {
        vec![format!(
            "missing-checked-certificate-production-evidence: binary-derived {target} conversion has checked certificate readback, but no production checker evidence was attached to any checked certificate row"
        )]
    } else {
        vec![format!(
            "missing-checked-certificate-production-evidence: binary-derived {target} conversion has no checked certificate production evidence in the CLI report"
        )]
    }
}

fn binary_derived_conversion_missing_target_gate_blockers(
    target: DecompileTarget,
    checked_certificate_readback_available: bool,
) -> Vec<String> {
    let target = target.label();
    let mut blockers = vec![format!(
        "missing-target-semantic-validation: binary-derived {target} conversion has no target semantics validation evidence in the convert report"
    )];
    if !checked_certificate_readback_available {
        blockers.push(format!(
            "missing-checked-proof-certificate: binary-derived {target} conversion has no checked proof certificate evidence in the convert report"
        ));
    }
    blockers
}

fn build_convert_checked_certificate_evidence(
    report: &DecompileReport,
    proof_grade_artifact: bool,
    loader: ConvertCheckedCertificateLoaderReport,
    gate_blockers: &[String],
    production_positive_golden_inventory: ProductionPositiveGoldenInventoryReport,
    target_consumer_digest_binding: &TargetConsumerDigestBinding,
    target_proof_consumer_evidence: Option<&TargetProofConsumerEvidenceReport>,
) -> ConvertCheckedCertificateEvidenceReport {
    let required = binary_derived_conversion_requires_checked_certificate_gate(report.target);
    let mut loader = loader;
    let checked_artifact_rows = loader.loaded_artifacts;
    let readback_records = loader
        .readback_records
        .iter()
        .cloned()
        .map(|mut record| {
            record.release_transcript_binding = convert_readback_release_transcript_binding(
                &record,
                target_consumer_digest_binding,
            );
            record.proof_grade_release_transcript_row =
                convert_readback_proof_grade_release_transcript_row(
                    report,
                    &record,
                    target_consumer_digest_binding,
                    target_proof_consumer_evidence,
                );
            record
        })
        .collect::<Vec<_>>();
    loader.readback_records = readback_records.clone();
    let proof_export_readback_rows =
        readback_records.iter().filter(|record| !record.proof_export_sha256.is_empty()).count();
    let checked_certificate_readback_rows =
        readback_records.iter().filter(|record| record.status == "readback").count();
    let production_checker_evidence_rows =
        readback_records.iter().filter(|record| record.production_checked).count();
    let imported_artifact_rows = 0;
    let rejected_artifact_rows = 0;
    let unmatched_artifact_rows = checked_artifact_rows.saturating_sub(readback_records.len());
    let checker_successes = checked_certificate_readback_rows;
    let checked_certificates = checked_certificate_readback_rows;
    let production_checked_certificates = production_checker_evidence_rows;
    let missing_production_checked_certificates =
        checked_certificates.saturating_sub(production_checked_certificates);
    let artifacts = convert_checked_certificate_artifact_rows(&loader);
    let accepted_certificates =
        convert_accepted_checked_certificate_evidence_records(&loader, &readback_records);
    let accepted_certificate_rows = accepted_certificates.len();
    let mut blockers = report
        .target_validation_blockers
        .iter()
        .filter(|blocker| target_blocker_mentions_checked_certificate(blocker))
        .map(convert_checked_certificate_blocker_from_target)
        .collect::<Vec<_>>();

    if required && !proof_grade_artifact {
        blockers.push(ConvertCheckedCertificateBlockerRecord {
            code: "proof-grade-artifact-missing".to_string(),
            stage: "targo-trust::convert-gate".to_string(),
            feature: "proof-grade-conversion-output".to_string(),
            detail: format!(
                "output trust is `{}`; checked certificate evidence cannot release a non-proof-grade conversion artifact",
                report.output_trust_level
            ),
            evidence_required: vec!["proof_grade_conversion_artifact".to_string()],
        });
    }

    if required
        && proof_grade_artifact
        && report.target_validation_blockers.is_empty()
        && proof_export_readback_rows == 0
        && checked_certificates == 0
    {
        blockers.push(ConvertCheckedCertificateBlockerRecord {
            code: "normalized-solver-proof-export-missing".to_string(),
            stage: "targo-trust::convert-gate".to_string(),
            feature: "missing-checked-proof-certificate".to_string(),
            detail: format!(
                "binary-derived {} conversion has no normalized solver proof export or checked proof certificate evidence in the convert report",
                report.target.label()
            ),
            evidence_required: vec![
                "normalized_solver_proof_export".to_string(),
                "checker_success".to_string(),
                "checked_certificate_artifact".to_string(),
            ],
        });
    }

    if required && proof_grade_artifact && missing_production_checked_certificates > 0 {
        blockers.push(ConvertCheckedCertificateBlockerRecord {
            code: "checked-certificate-production-evidence-missing".to_string(),
            stage: "targo-trust::convert-gate".to_string(),
            feature: "checked-certificate-production".to_string(),
            detail: format!(
                "binary-derived {} conversion has {} checked certificate readback row(s), but {} lack production checker evidence",
                report.target.label(),
                checked_certificates,
                missing_production_checked_certificates
            ),
            evidence_required: vec![
                "production_checker_evidence".to_string(),
                "checked_certificate_artifact".to_string(),
            ],
        });
    }

    if required && proof_grade_artifact && checked_certificates > 0 {
        let missing_manifest_identity = readback_records
            .iter()
            .filter(|record| record.status == "readback")
            .filter(|record| record.manifest_identity_sha256.is_none())
            .count();
        if missing_manifest_identity > 0 {
            blockers.push(ConvertCheckedCertificateBlockerRecord {
                code: "checked-certificate-manifest-identity-missing".to_string(),
                stage: "targo-trust::convert-gate".to_string(),
                feature: "checked-certificate-manifest-identity".to_string(),
                detail: format!(
                    "binary-derived {} conversion has {missing_manifest_identity} checked certificate row(s) without per-VC manifest identity",
                    report.target.label()
                ),
                evidence_required: vec!["checked_certificate_manifest_identity".to_string()],
            });
        }

        let missing_source_gate_identity = readback_records
            .iter()
            .filter(|record| record.status == "readback")
            .filter(|record| record.source_backpropagation_gate_sha256.is_none())
            .count();
        if missing_source_gate_identity > 0 {
            blockers.push(ConvertCheckedCertificateBlockerRecord {
                code: "checked-certificate-source-backpropagation-gate-identity-missing"
                    .to_string(),
                stage: "targo-trust::convert-gate".to_string(),
                feature: "checked-certificate-source-backpropagation-gate".to_string(),
                detail: format!(
                    "binary-derived {} conversion has {missing_source_gate_identity} checked certificate row(s) without source-backpropagation gate identity",
                    report.target.label()
                ),
                evidence_required: vec![
                    "checked_certificate_source_backpropagation_gate".to_string(),
                ],
            });
        }

        let rejected_replay_digest_identity = readback_records
            .iter()
            .filter(|record| record.status == "readback")
            .filter(|record| record.replay_digest_identity.status != "accepted")
            .count();
        if rejected_replay_digest_identity > 0 {
            blockers.push(ConvertCheckedCertificateBlockerRecord {
                code: "replay-digest-identity-missing".to_string(),
                stage: "targo-trust::convert-gate".to_string(),
                feature: "replay-digest-identity".to_string(),
                detail: format!(
                    "binary-derived {} conversion has {rejected_replay_digest_identity} checked certificate row(s) without accepted replay transcript and binary artifact digest identity",
                    report.target.label()
                ),
                evidence_required: vec![
                    "machine_replay_transcript".to_string(),
                    "binary_artifact_digest_identity".to_string(),
                ],
            });
        }

        let rejected_release_transcript_bindings = readback_records
            .iter()
            .filter(|record| record.status == "readback")
            .filter(|record| record.release_transcript_binding.status != "accepted")
            .count();
        if rejected_release_transcript_bindings > 0 {
            blockers.push(ConvertCheckedCertificateBlockerRecord {
                code: "release-transcript-binding-missing".to_string(),
                stage: "targo-trust::convert-gate".to_string(),
                feature: "release-transcript-binding".to_string(),
                detail: format!(
                    "binary-derived {} conversion has {rejected_release_transcript_bindings} checked certificate row(s) without accepted release transcript binding",
                    report.target.label()
                ),
                evidence_required: release_transcript_binding_evidence_required(
                    target_consumer_digest_binding.required,
                ),
            });
        }

        let incomplete_release_transcript_rows = readback_records
            .iter()
            .filter(|record| record.status == "readback")
            .filter(|record| !record.proof_grade_release_transcript_row.accepted)
            .count();
        if incomplete_release_transcript_rows > 0 {
            blockers.push(ConvertCheckedCertificateBlockerRecord {
                code: "proof-grade-release-transcript-row-incomplete".to_string(),
                stage: "targo-trust::convert-gate".to_string(),
                feature: "proof-grade-release-transcript-row".to_string(),
                detail: format!(
                    "binary-derived {} conversion has {incomplete_release_transcript_rows} checked certificate row(s) without an accepted proof-grade release transcript row",
                    report.target.label()
                ),
                evidence_required: proof_grade_release_transcript_row_evidence_required(
                    target_consumer_digest_binding.required,
                ),
            });
        }
    }

    if required {
        if let Some(blocker) = loader.blocker.clone() {
            blockers.push(blocker);
        }
        if let Some(production) = loader.production_export.as_ref() {
            for blocker in &production.blockers {
                push_convert_checked_certificate_blocker(&mut blockers, blocker.clone());
            }
        }
    }

    let mut proof_grade_release_blockers = Vec::new();
    if required {
        for blocker in &blockers {
            push_convert_checked_certificate_blocker(
                &mut proof_grade_release_blockers,
                blocker.clone(),
            );
        }
        for blocker in convert_checked_certificate_release_blockers(gate_blockers) {
            push_convert_checked_certificate_blocker(&mut proof_grade_release_blockers, blocker);
        }
    }
    for blocker in &proof_grade_release_blockers {
        push_convert_checked_certificate_blocker(&mut blockers, blocker.clone());
    }
    let proof_grade_release_accepted = required
        && proof_grade_artifact
        && checked_certificates > 0
        && production_checked_certificates == checked_certificates
        && blockers.is_empty();
    let status = if !required {
        "not_required"
    } else if proof_grade_release_accepted {
        "accepted"
    } else {
        "blocked"
    };
    let row_blockers = if blockers.is_empty() {
        gate_blockers.to_vec()
    } else {
        blockers
            .iter()
            .map(|blocker| format!("{}: {}", blocker.code, blocker.detail))
            .collect::<Vec<_>>()
    };
    let readback_row_details = convert_checked_certificate_readback_row_details(
        required,
        proof_grade_artifact,
        &readback_records,
        &row_blockers,
    );
    let proof_grade_release_transcript_rows = readback_records
        .iter()
        .map(|record| record.proof_grade_release_transcript_row.clone())
        .collect::<Vec<_>>();

    ConvertCheckedCertificateEvidenceReport {
        required,
        status: status.to_string(),
        loader,
        checked_artifact_rows,
        accepted_certificate_rows,
        imported_artifact_rows,
        rejected_artifact_rows,
        unmatched_artifact_rows,
        normalized_solver_proof_exports: proof_export_readback_rows,
        proof_export_readback_rows,
        checked_certificate_readback_rows,
        checker_successes,
        checked_certificates,
        production_checker_evidence_rows,
        production_checked_certificates,
        missing_production_checked_certificates,
        raw_solver_proof_bytes_sufficient: false,
        production_positive_golden_inventory,
        artifacts,
        readback_records,
        readback_row_details,
        accepted_certificates,
        proof_grade_release_transcript_rows,
        proof_grade_release_accepted,
        proof_grade_release_blockers,
        blockers,
    }
}

fn push_convert_checked_certificate_blocker(
    blockers: &mut Vec<ConvertCheckedCertificateBlockerRecord>,
    blocker: ConvertCheckedCertificateBlockerRecord,
) {
    if !blockers.iter().any(|existing| {
        existing.code == blocker.code
            && existing.stage == blocker.stage
            && existing.feature == blocker.feature
            && existing.detail == blocker.detail
    }) {
        blockers.push(blocker);
    }
}

fn convert_checked_certificate_release_blockers(
    gate_blockers: &[String],
) -> Vec<ConvertCheckedCertificateBlockerRecord> {
    gate_blockers
        .iter()
        .map(|blocker| convert_checked_certificate_release_blocker(blocker))
        .collect()
}

fn convert_checked_certificate_release_blocker(
    blocker: &str,
) -> ConvertCheckedCertificateBlockerRecord {
    let blocker_lower = blocker.to_ascii_lowercase();
    if blocker_mentions_selected_image_replay_identity(&blocker_lower) {
        return ConvertCheckedCertificateBlockerRecord {
            code: "selected-image-replay-identity-missing".to_string(),
            stage: "targo-trust::convert-release-gate".to_string(),
            feature: "selected-image-replay-identity".to_string(),
            detail: blocker.to_string(),
            evidence_required: vec![
                "selected_image_digest_identity".to_string(),
                "machine_replay_transcript".to_string(),
            ],
        };
    }
    if blocker_mentions_target_refinement_consumer(&blocker_lower) {
        return ConvertCheckedCertificateBlockerRecord {
            code: "target-refinement-consumer-missing".to_string(),
            stage: "targo-trust::convert-release-gate".to_string(),
            feature: "target-refinement-consumer".to_string(),
            detail: blocker.to_string(),
            evidence_required: vec![
                "target_refinement_metadata".to_string(),
                "target_semantic_validation".to_string(),
            ],
        };
    }
    if blocker_mentions_bounded_target_consumer(&blocker_lower) {
        return ConvertCheckedCertificateBlockerRecord {
            code: "target-semantic-validation-missing".to_string(),
            stage: "targo-trust::convert-release-gate".to_string(),
            feature: "target-semantic-validation".to_string(),
            detail: blocker.to_string(),
            evidence_required: vec!["target_semantic_validation".to_string()],
        };
    }
    if blocker_mentions_source_to_binary_roundtrip(&blocker_lower) {
        return ConvertCheckedCertificateBlockerRecord {
            code: "source-to-binary-roundtrip-evidence-missing".to_string(),
            stage: "targo-trust::convert-release-gate".to_string(),
            feature: "source-to-binary-roundtrip".to_string(),
            detail: blocker.to_string(),
            evidence_required: vec![
                "compile-back-artifact-digests-bound".to_string(),
                "compile-back-lifted-binary-trust_ir-bound".to_string(),
                "compile-back-reconstructed-trust_ir-sha256".to_string(),
                "compile-back-root-artifact-sha256".to_string(),
                "compile-back-selected-image-sha256".to_string(),
                "bidirectional_trust_ir_refinement".to_string(),
            ],
        };
    }
    if blocker_mentions_replay_artifact_digest_identity(&blocker_lower) {
        return ConvertCheckedCertificateBlockerRecord {
            code: "replay-artifact-digest-identity-missing".to_string(),
            stage: "targo-trust::convert-release-gate".to_string(),
            feature: "replay-artifact-digest-identity".to_string(),
            detail: blocker.to_string(),
            evidence_required: vec![
                "binary_artifact_digest_identity".to_string(),
                "machine_replay_transcript".to_string(),
            ],
        };
    }

    let (code, feature, evidence_required) = if blocker
        .contains("symbolic-formula-not-consumed-by-target-semantics")
        || blocker.contains("symbolic-formula-proof-semantics")
        || blocker.contains("symbolic formula")
    {
        (
            "symbolic-formula-preservation-not-consumed",
            "symbolic-formula-preservation",
            vec![
                "preserved_symbolic_formula".to_string(),
                "target_semantic_validation".to_string(),
            ],
        )
    } else if blocker.contains("missing-target-semantic-validation")
        || blocker.contains("target-semantic-validation")
        || blocker.contains("target-semantics-not-consumed")
        || blocker.contains("bounded-empty")
        || blocker.contains("target proof-consumer")
        || blocker.contains("target proof consumer")
    {
        (
            "target-semantic-validation-missing",
            "target-semantic-validation",
            vec!["target_semantic_validation".to_string()],
        )
    } else if blocker.contains("exact-machine-replay")
        || blocker.contains("machine replay")
        || blocker.contains("replay semantics")
        || blocker.contains("proof-replay-not-consumed-by-target-semantics")
        || blocker.contains("missing-proof-replay-metadata")
    {
        (
            "exact-machine-replay-missing",
            "exact-machine-replay",
            vec!["machine_replay_transcript".to_string()],
        )
    } else if blocker.contains("exact-source-provenance") {
        (
            "exact-source-provenance-missing",
            "exact-source-provenance",
            vec!["source_provenance_handoff".to_string()],
        )
    } else if blocker.contains("raw-solver-proof-bytes") {
        (
            "raw-solver-proof-bytes-audit-only",
            "checked-certificate-production",
            vec![
                "normalized_solver_proof_export".to_string(),
                "checker_success".to_string(),
                "checked_certificate_artifact".to_string(),
            ],
        )
    } else if blocker.contains("checked-certificate-production-evidence")
        || blocker.contains("production checker evidence")
    {
        (
            "checked-certificate-production-evidence-missing",
            "checked-certificate-production",
            vec![
                "production_checker_evidence".to_string(),
                "checked_certificate_artifact".to_string(),
            ],
        )
    } else if blocker.contains("missing-checked-proof-certificate")
        || blocker.contains("checked proof certificate")
    {
        (
            "checked-certificate-missing",
            "checked-certificate-loader",
            vec![
                "normalized_solver_proof_export".to_string(),
                "checker_success".to_string(),
                "checked_certificate_artifact".to_string(),
            ],
        )
    } else if blocker.contains("proof-grade conversion output") || blocker.contains("output trust")
    {
        (
            "proof-grade-artifact-missing",
            "proof-grade-conversion-output",
            vec!["proof_grade_conversion_artifact".to_string()],
        )
    } else if blocker.contains("production-proof-grade-cli-evidence")
        || blocker.contains("trust_decompile_binary_release_gate")
    {
        (
            "production-proof-grade-cli-evidence-missing",
            "production-proof-grade-cli-evidence",
            vec![
                "trust_decompile_binary_release_gate".to_string(),
                "proof_grade_binary_verification".to_string(),
                "checked_certificate_identity".to_string(),
                "exact_replay_identity".to_string(),
                "binary_artifact_digest_identity".to_string(),
                "nonzero_required_vcs".to_string(),
                "empty_unsupported_ledger".to_string(),
                "decompile_trust_cg_json_production_positive_golden".to_string(),
                "decompile_convert_trust_cg_json_production_positive_golden".to_string(),
                "checked_certificate_manifest".to_string(),
                "replay_identity".to_string(),
                "unsupported_ledger_elimination".to_string(),
                "production_cli_golden".to_string(),
            ],
        )
    } else if blocker.contains("translation validation") || blocker.contains("output validation") {
        (
            "translation-validation-missing",
            "translation-validation",
            vec!["translation_validation".to_string()],
        )
    } else if blocker.contains("unsupported conversion/lift coverage")
        || blocker.contains("supported-ledger")
        || blocker.contains("unsupported ledger")
        || blocker.contains("unsupported binary/decompilation ledger")
    {
        (
            "unsupported-ledger-nonempty",
            "unsupported-ledger",
            vec!["empty_unsupported_ledger".to_string()],
        )
    } else if blocker.contains("conversion pipeline failures") {
        (
            "conversion-pipeline-failure",
            "conversion-pipeline",
            vec!["successful_conversion_pipeline".to_string()],
        )
    } else {
        (
            "proof-grade-release-gate-blocked",
            "proof-grade-release-gate",
            vec!["proof_grade_release_gate_acceptance".to_string()],
        )
    };

    ConvertCheckedCertificateBlockerRecord {
        code: code.to_string(),
        stage: "targo-trust::convert-release-gate".to_string(),
        feature: feature.to_string(),
        detail: blocker.to_string(),
        evidence_required,
    }
}

fn blocker_mentions_selected_image_replay_identity(blocker_lower: &str) -> bool {
    (blocker_lower.contains("selected image")
        || blocker_lower.contains("selected-image")
        || blocker_lower.contains("matched_selected_image=false"))
        && (blocker_lower.contains("digest")
            || blocker_lower.contains("identity")
            || blocker_lower.contains("range"))
}

fn blocker_mentions_bounded_target_consumer(blocker_lower: &str) -> bool {
    blocker_lower.contains("bounded-empty")
        && (blocker_lower.contains("target-proof-consumer")
            || blocker_lower.contains("target proof-consumer")
            || blocker_lower.contains("target proof consumer"))
}

fn blocker_mentions_target_refinement_consumer(blocker_lower: &str) -> bool {
    blocker_lower.contains("refinement")
        && (blocker_lower.contains("target")
            || blocker_lower.contains("trust-cg")
            || blocker_lower.contains("wasm")
            || blocker_lower.contains("lir")
            || blocker_lower.contains("trust_ir"))
}

fn blocker_mentions_replay_artifact_digest_identity(blocker_lower: &str) -> bool {
    blocker_lower.contains("root binary artifact digest")
        || blocker_lower.contains("binary artifact digest identity")
        || blocker_lower.contains("matched_artifact_digest=false")
        || (blocker_lower.contains("artifact digest")
            && (blocker_lower.contains("replay") || blocker_lower.contains("machine-code")))
}

fn blocker_mentions_source_to_binary_roundtrip(blocker_lower: &str) -> bool {
    (blocker_lower.contains("compile-back")
        || blocker_lower.contains("compile back")
        || blocker_lower.contains("source-to-binary")
        || blocker_lower.contains("source to binary"))
        && (blocker_lower.contains("artifact digest")
            || blocker_lower.contains("artifact-digests")
            || blocker_lower.contains("roundtrip")
            || blocker_lower.contains("round-trip")
            || blocker_lower.contains("trust_ir")
            || blocker_lower.contains("trustir"))
}

fn build_production_positive_golden_inventory(
    report: &DecompileReport,
    proof_grade_artifact: bool,
    loader: &ConvertCheckedCertificateLoaderReport,
) -> ProductionPositiveGoldenInventoryReport {
    let required = report.target == DecompileTarget::TrustCg && proof_grade_artifact;
    let mut missing_artifacts = Vec::new();

    if required {
        let missing_release_requirements =
            decompile_production_proof_grade_evidence_missing_requirements(report);
        if !missing_release_requirements.is_empty() {
            missing_artifacts.push(production_positive_missing_artifact(
                "decompile --to trust-cg --json",
                "targo-trust::decompile",
                "missing production-positive targo trust decompile <binary> --to trust-cg --json golden with artifact_gate.accepted=true and production_proof_grade_evidence present",
                [
                    "artifact_gate.accepted=true",
                    "production_proof_grade_evidence",
                    "trust_decompile_binary_release_gate",
                ],
            ));
            missing_artifacts.push(production_positive_missing_artifact(
                "decompile -> convert --to trust-cg --json",
                "targo-trust::convert",
                "missing production-positive chained targo trust decompile <binary> --to trust-cg --json -> targo trust convert <binary> --to trust-cg --json golden with conversion_gate.accepted=true",
                [
                    "conversion_gate.accepted=true",
                    "artifact_gate.accepted=true",
                    "production_cli_golden",
                ],
            ));
        }

        let manifest_has_production_checked_certificate = loader.requested_manifests > 0
            && loader.readback_records.iter().any(|record| {
                record.status == "readback"
                    && record.production_checked
                    && !record.certificate_sha256.trim().is_empty()
            });
        if !manifest_has_production_checked_certificate {
            missing_artifacts.push(production_positive_missing_artifact(
                "checked cert manifest",
                "targo-trust::convert-loader",
                "missing loadable --checked-cert-manifest with production checked certificate rows bound to the proof-grade CLI golden",
                [
                    "--checked-cert-manifest",
                    "loadable_checked_certificate_manifest",
                    "production_checked_certificate",
                ],
            ));
        }

        let replay_identity_present =
            report.production_proof_grade_evidence.as_ref().is_some_and(|evidence| {
                evidence.exact_replay_identity
                    && evidence.binary_replay == "replayed"
                    && evidence.binary_artifact_digest_identity
            });
        if !replay_identity_present {
            missing_artifacts.push(production_positive_missing_artifact(
                "replay identity",
                "targo-trust::binary-replay",
                "missing exact replay identity tying machine replay transcript and binary artifact digest identity to the selected binary image",
                [
                    "exact_replay_identity",
                    "machine_replay_transcript",
                    "selected_image_digest_identity",
                    "binary_artifact_digest_identity",
                ],
            ));
        }

        let unsupported_ledger_eliminated = report
            .production_proof_grade_evidence
            .as_ref()
            .is_some_and(|evidence| evidence.unsupported_ledger_empty)
            && report.unsupported == 0
            && report.unsupported_items.is_empty();
        if !unsupported_ledger_eliminated {
            missing_artifacts.push(production_positive_missing_artifact(
                "unsupported-ledger elimination",
                "targo-trust::unsupported-ledger",
                "missing production golden proving empty unsupported ledger for the decompile/convert trust-cg chain",
                ["empty_unsupported_ledger", "unsupported_ledger_empty"],
            ));
        }
    }

    let status = if !required {
        "not_required"
    } else if missing_artifacts.is_empty() {
        "accepted"
    } else {
        "blocked"
    };

    ProductionPositiveGoldenInventoryReport {
        required,
        status: status.to_string(),
        target: report.target.label().to_string(),
        missing_artifacts,
    }
}

fn production_positive_missing_artifact(
    artifact: impl Into<String>,
    stage: impl Into<String>,
    detail: impl Into<String>,
    evidence_required: impl IntoIterator<Item = &'static str>,
) -> ProductionPositiveGoldenArtifactRecord {
    ProductionPositiveGoldenArtifactRecord {
        artifact: artifact.into(),
        stage: stage.into(),
        status: "missing".to_string(),
        detail: detail.into(),
        evidence_required: evidence_required.into_iter().map(str::to_string).collect(),
    }
}

fn release_transcript_binding_evidence_required(target_consumer_required: bool) -> Vec<String> {
    let mut evidence = vec![
        "release_transcript_binding_schema".to_string(),
        "release_transcript_binding_commit".to_string(),
        "binary_artifact_digest_identity".to_string(),
        "selected_image_digest_identity".to_string(),
        "vc_digest".to_string(),
        "checked_certificate_digest".to_string(),
        "machine_replay_transcript".to_string(),
        "binary_provenance_digest".to_string(),
    ];
    if target_consumer_required {
        evidence.push("target_consumer_evidence_digest".to_string());
        evidence.push("target_consumer_binding_digest".to_string());
    }
    evidence
}

fn proof_grade_release_transcript_row_evidence_required(
    _target_consumer_required: bool,
) -> Vec<String> {
    let evidence = vec![
        "proof_grade_release_transcript_row_schema".to_string(),
        "candidate_commit".to_string(),
        "binary_digest".to_string(),
        "selected_image_identity".to_string(),
        "selected_image_digest".to_string(),
        "vc_digests".to_string(),
        "checked_certificate_digests".to_string(),
        "replay_transcript_digests".to_string(),
        "provenance_artifact_digests".to_string(),
        "empty_unsupported_ledger".to_string(),
        "target_proof_consumer_artifact_digests".to_string(),
        "exact_source_ownership_evidence".to_string(),
        "type_ownership_evidence".to_string(),
        "aarch64_ordering_monitor_evidence".to_string(),
        "release_transcript_binding_digest".to_string(),
    ];
    evidence
}

fn convert_readback_release_transcript_binding(
    record: &ConvertCheckedCertificateReadbackRecord,
    target_consumer_digest_binding: &TargetConsumerDigestBinding,
) -> ReleaseTranscriptBindingReport {
    release_transcript_binding_report(
        &record.binary_artifact_digest_identity,
        Some(record.vc_sha256.clone()),
        Some(record.certificate_sha256.clone()),
        record.replay_transcript_digest.clone(),
        Some(record.origin_sha256.clone()),
        target_consumer_digest_binding,
    )
}

fn convert_readback_proof_grade_release_transcript_row(
    report: &DecompileReport,
    record: &ConvertCheckedCertificateReadbackRecord,
    target_consumer_digest_binding: &TargetConsumerDigestBinding,
    target_proof_consumer_evidence: Option<&TargetProofConsumerEvidenceReport>,
) -> ProofGradeReleaseTranscriptRowReport {
    proof_grade_release_transcript_row_report(ProofGradeReleaseTranscriptRowInput {
        evidence_origin: release_transcript_evidence_origin_for_convert_readback(report, record),
        candidate_commit: release_transcript_candidate_commit(),
        binary_artifact_digest_identity: &record.binary_artifact_digest_identity,
        vc_sha256s: release_transcript_digest_values([record.vc_sha256.clone()]),
        checked_certificate_sha256s: release_transcript_digest_values([record
            .certificate_sha256
            .clone()]),
        replay_transcript_sha256s: release_transcript_digest_values(
            record.replay_transcript_digest.clone(),
        ),
        provenance_sha256s: release_transcript_digest_values([record.origin_sha256.clone()]),
        unsupported_ledgers_empty: decompile_report_unsupported_ledgers_empty(report),
        target_consumer: target_consumer_digest_binding,
        exact_source_ownership_sha256: release_transcript_exact_source_ownership_sha256(
            report,
            &record.source_backpropagation_gate,
            &record.source_backpropagation_gate_sha256,
        ),
        type_ownership_sha256: release_transcript_type_ownership_sha256(
            report,
            target_consumer_digest_binding,
            target_proof_consumer_evidence,
        ),
        aarch64_ordering_monitor_evidence: release_transcript_aarch64_ordering_monitor_evidence(
            report,
        ),
    })
}

fn release_transcript_evidence_origin_for_convert_readback(
    report: &DecompileReport,
    record: &ConvertCheckedCertificateReadbackRecord,
) -> &'static str {
    if record.status == "readback"
        && record.production_checked
        && record.manifest_identity_sha256.as_deref().is_some_and(trust_types::digest::is_stable_sha256_hex)
        && record.source_backpropagation_gate_sha256.as_deref().is_some_and(trust_types::digest::is_stable_sha256_hex)
        && record.production_checker_evidence_sha256.as_deref().is_some_and(trust_types::digest::is_stable_sha256_hex)
        && record.replay_digest_identity.status == "accepted"
        && record.release_transcript_binding.status == "accepted"
        && decompile_production_proof_grade_evidence_accepts(report)
    {
        PROOF_GRADE_RELEASE_TRANSCRIPT_REAL_EVIDENCE_ORIGIN
    } else {
        "targo_trust_checked_certificate_readback"
    }
}

fn checked_certificate_import_release_transcript_binding(
    artifact: &CheckedCertificateArtifactImportRecord,
) -> ReleaseTranscriptBindingReport {
    checked_certificate_import_release_transcript_binding_with_target_consumer(
        artifact,
        &TargetConsumerDigestBinding::default(),
    )
}

fn checked_certificate_import_release_transcript_binding_with_target_consumer(
    artifact: &CheckedCertificateArtifactImportRecord,
    target_consumer: &TargetConsumerDigestBinding,
) -> ReleaseTranscriptBindingReport {
    release_transcript_binding_report(
        &artifact.binary_artifact_digest_identity,
        Some(artifact.vc_sha256.clone()),
        Some(artifact.certificate_sha256.clone()),
        artifact.replay_transcript_digest.clone(),
        Some(artifact.origin_sha256.clone()),
        target_consumer,
    )
}

fn checked_certificate_import_proof_grade_release_transcript_row(
    artifact: &CheckedCertificateArtifactImportRecord,
    unsupported_ledgers_empty: bool,
) -> ProofGradeReleaseTranscriptRowReport {
    checked_certificate_import_proof_grade_release_transcript_row_with_target_consumer(
        release_transcript_candidate_commit(),
        artifact,
        unsupported_ledgers_empty,
        &TargetConsumerDigestBinding::default(),
    )
}

fn checked_certificate_import_proof_grade_release_transcript_row_with_target_consumer(
    candidate_commit: Option<String>,
    artifact: &CheckedCertificateArtifactImportRecord,
    unsupported_ledgers_empty: bool,
    target_consumer: &TargetConsumerDigestBinding,
) -> ProofGradeReleaseTranscriptRowReport {
    proof_grade_release_transcript_row_report(ProofGradeReleaseTranscriptRowInput {
        evidence_origin: PROOF_GRADE_RELEASE_TRANSCRIPT_SYNTHETIC_EVIDENCE_ORIGIN,
        candidate_commit,
        binary_artifact_digest_identity: &artifact.binary_artifact_digest_identity,
        vc_sha256s: release_transcript_digest_values([artifact.vc_sha256.clone()]),
        checked_certificate_sha256s: release_transcript_digest_values([artifact
            .certificate_sha256
            .clone()]),
        replay_transcript_sha256s: release_transcript_digest_values(
            artifact.replay_transcript_digest.clone(),
        ),
        provenance_sha256s: release_transcript_digest_values([artifact.origin_sha256.clone()]),
        unsupported_ledgers_empty,
        target_consumer,
        exact_source_ownership_sha256: release_transcript_import_exact_source_ownership_sha256(
            artifact,
        ),
        type_ownership_sha256: release_transcript_import_type_ownership_sha256(target_consumer),
        aarch64_ordering_monitor_evidence: Vec::new(),
    })
}

fn convert_checked_certificate_readback_row_details(
    required: bool,
    proof_grade_artifact: bool,
    readback_records: &[ConvertCheckedCertificateReadbackRecord],
    gate_blockers: &[String],
) -> Vec<ConvertCheckedCertificateReadbackRowDecisionRecord> {
    readback_records
        .iter()
        .map(|record| {
            let readback_accepted = record.status == "readback"
                && !record.certificate_sha256.trim().is_empty()
                && !record.vc_sha256.trim().is_empty()
                && !record.origin_sha256.trim().is_empty();
            let release_transcript_blockers = record.release_transcript_binding.blockers.clone();
            let mut blockers = gate_blockers.to_vec();
            blockers.extend(release_transcript_blockers.iter().cloned());
            let proof_grade_release_accepted = required
                && proof_grade_artifact
                && readback_accepted
                && record.production_checked
                && blockers.is_empty();
            let detail = if proof_grade_release_accepted {
                "checked proof-cert readback row accepted for proof-grade release".to_string()
            } else if !readback_accepted {
                "checked proof-cert readback row is malformed or missing required digest metadata"
                    .to_string()
            } else if !required {
                "checked proof-cert readback row accepted for audit; this target does not require checked-certificate release evidence".to_string()
            } else if !proof_grade_artifact {
                "checked proof-cert readback row accepted for audit, but the output is not labeled proof-grade".to_string()
            } else if !record.production_checked {
                let production_detail = record
                    .production_checker_evidence_detail
                    .as_deref()
                    .unwrap_or("missing production checker evidence");
                format!(
                    "checked proof-cert readback row accepted for audit, but proof-grade release requires production checker evidence: {production_detail}"
                )
            } else if !release_transcript_blockers.is_empty() {
                format!(
                    "checked proof-cert readback row accepted for audit, but proof-grade release requires accepted release transcript binding: {}",
                    release_transcript_blockers.join("; ")
                )
            } else {
                format!(
                    "checked proof-cert readback row accepted for audit, but proof-grade release remains blocked: {}",
                    gate_blockers.join("; ")
                )
            };

            ConvertCheckedCertificateReadbackRowDecisionRecord {
                source: record.source.clone(),
                artifact_path: record.artifact_path.clone(),
                dispatch_id: record.dispatch_id.clone(),
                certificate_sha256: record.certificate_sha256.clone(),
                vc_sha256: record.vc_sha256.clone(),
                origin_sha256: record.origin_sha256.clone(),
                readback_accepted,
                manifest_identity_sha256: record.manifest_identity_sha256.clone(),
                readback_status: if readback_accepted { "accepted" } else { "rejected" }
                    .to_string(),
                proof_grade_release_accepted,
                proof_grade_release_status: if proof_grade_release_accepted {
                    "accepted"
                } else {
                    "rejected"
                }
                .to_string(),
                detail,
                blockers,
            }
        })
        .collect()
}

fn convert_checked_certificate_loader_has_readback(
    loader: &ConvertCheckedCertificateLoaderReport,
) -> bool {
    loader
        .readback_records
        .iter()
        .any(|record| record.status == "readback" && !record.certificate_sha256.trim().is_empty())
}

fn convert_checked_certificate_loader_has_complete_production_checked_readback(
    loader: &ConvertCheckedCertificateLoaderReport,
) -> bool {
    let mut readback_records = loader
        .readback_records
        .iter()
        .filter(|record| {
            record.status == "readback" && !record.certificate_sha256.trim().is_empty()
        })
        .peekable();
    readback_records.peek().is_some() && readback_records.all(|record| record.production_checked)
}

fn convert_checked_certificate_loader_not_requested() -> ConvertCheckedCertificateLoaderReport {
    ConvertCheckedCertificateLoaderReport {
        status: "not_requested".to_string(),
        implementation: "targo-trust::convert-metadata-only".to_string(),
        requested_artifacts: 0,
        requested_manifests: 0,
        loaded_artifacts: 0,
        production_export: None,
        external_checker: None,
        artifacts: Vec::new(),
        readback_records: Vec::new(),
        blocker: Some(convert_checked_certificate_loader_missing_blocker(
            "no production checked-certificate loader is wired for targo trust convert; checked certificate artifacts were not provided",
        )),
        diagnostics: Vec::new(),
    }
}

#[cfg(test)]
fn load_convert_checked_certificate_loader_report(
    artifact_paths: &[String],
    manifest_paths: &[String],
) -> Result<ConvertCheckedCertificateLoaderReport, trust_proof_cert::CertError> {
    load_convert_checked_certificate_loader_report_with_external_checker(
        artifact_paths,
        manifest_paths,
        None,
        0,
    )
}

fn load_convert_checked_certificate_loader_report_with_external_checker(
    artifact_paths: &[String],
    manifest_paths: &[String],
    checker_path: Option<&Path>,
    _checked_at_unix_ms: u64,
) -> Result<ConvertCheckedCertificateLoaderReport, trust_proof_cert::CertError> {
    if let Some(checker_path) = checker_path {
        return Err(trust_proof_cert::CertError::InvalidCertificate {
            reason: format!(
                "external checker `{}` cannot be attached to already-loaded certificate rows: the CLI has no authenticated solver-proof metadata/payload inputs for an import-only recheck; use --checked-cert-export-dir with --checked-cert-checker so Targo can bind all concrete artifacts",
                checker_path.display()
            ),
        });
    }
    if artifact_paths.is_empty() && manifest_paths.is_empty() {
        return Ok(convert_checked_certificate_loader_not_requested());
    }

    let rows = load_checked_certificate_artifact_rows(artifact_paths, manifest_paths)?;
    let artifacts =
        rows.iter().map(convert_checked_certificate_artifact_readback_row).collect::<Vec<_>>();
    let readback_records =
        rows.iter().map(convert_checked_certificate_readback_record).collect::<Vec<_>>();
    let blocker = if readback_records.is_empty() {
        Some(convert_checked_certificate_loader_missing_blocker(
            "checked certificate artifact paths/manifests were supplied, but no checked proof-cert artifacts were loaded",
        ))
    } else {
        None
    };

    Ok(ConvertCheckedCertificateLoaderReport {
        status: if readback_records.is_empty() { "loaded_empty" } else { "loaded" }.to_string(),
        implementation: "targo-trust::convert-proof-cert-readback".to_string(),
        requested_artifacts: artifact_paths.len(),
        requested_manifests: manifest_paths.len(),
        loaded_artifacts: artifacts.len(),
        production_export: None,
        external_checker: None,
        artifacts,
        readback_records,
        blocker,
        diagnostics: Vec::new(),
    })
}

fn load_convert_checked_certificate_loader_report_with_production_export(
    artifact_paths: &[String],
    manifest_paths: &[String],
    checker_path: Option<&Path>,
    checked_at_unix_ms: u64,
    production_export: Option<ConvertCheckedCertificateProductionExportReport>,
) -> Result<ConvertCheckedCertificateLoaderReport, trust_proof_cert::CertError> {
    let mut loader = load_convert_checked_certificate_loader_report_with_external_checker(
        artifact_paths,
        manifest_paths,
        checker_path,
        checked_at_unix_ms,
    )?;
    if let Some(production_export) = production_export {
        loader.diagnostics.extend(production_export.diagnostics.iter().cloned());
        loader.production_export = Some(production_export);
    }
    Ok(loader)
}

fn produce_convert_checked_certificate_artifacts_for_decompilation(
    artifact: &DecompilationArtifact,
    export_dir: &Path,
    checker_path: Option<&Path>,
    checked_at_unix_ms: u64,
) -> ProducedCheckedCertificateArtifacts {
    let mut scan = scan_decompilation_proof_export_candidates(artifact);
    let source_backpropagation_gate =
        convert_checked_certificate_source_backpropagation_gate_for_decompilation_artifact(
            artifact, &scan,
        );
    let checker_selection =
        checker_path.map(|path| path.display().to_string()).unwrap_or_else(|| "absent".to_string());
    let mut artifact_paths = Vec::new();

    let Some(checker_path) = checker_path else {
        scan.blockers.push(convert_checked_certificate_production_blocker(
            "checker-selection-missing",
            "checked-certificate-production",
            "checked certificate production requested, but --checked-cert-checker was not provided",
            ["production_checker"],
        ));
        let report = convert_checked_certificate_production_export_report(
            "blocked",
            export_dir,
            checker_selection,
            scan,
            artifact_paths.clone(),
            None,
            source_backpropagation_gate,
        );
        return ProducedCheckedCertificateArtifacts { report, artifact_paths };
    };

    let prepared_checker =
        match external_checker::prepare_external_checker(checker_path, checked_at_unix_ms) {
            Ok(prepared) => prepared,
            Err(error) => {
                scan.blockers.push(convert_checked_certificate_production_blocker(
                    "checker-unreadable",
                    "checked-certificate-production",
                    format!(
                        "checked certificate production checker `{}` is not readable: {error}",
                        checker_path.display()
                    ),
                    ["production_checker"],
                ));
                let report = convert_checked_certificate_production_export_report(
                    "blocked",
                    export_dir,
                    checker_selection,
                    scan,
                    artifact_paths.clone(),
                    None,
                    source_backpropagation_gate,
                );
                return ProducedCheckedCertificateArtifacts { report, artifact_paths };
            }
        };
    let checker_version = format!("external-sha256:{}", prepared_checker.checker_sha256);
    let checker_id = checker_path
        .file_name()
        .and_then(|name| name.to_str())
        .filter(|name| !name.trim().is_empty())
        .unwrap_or("checked-cert-checker")
        .to_string();
    let runner = &prepared_checker.runner;
    let mut manifest = CheckedBinaryCertificateManifest::new();
    let mut audit_exports = Vec::new();

    for candidate in &scan.candidates {
        let loaded_proof_export = match load_normalized_solver_proof_export_artifact(
            &candidate.proof_path,
            &candidate.dispatch,
            &candidate.canonical_vc_bytes,
            candidate.format.as_str(),
            candidate.proof_sha256.as_str(),
            candidate.replay_transcript_digest.as_deref(),
            &source_backpropagation_gate,
        ) {
            Ok(loaded) => loaded,
            Err(error) => {
                scan.blockers.push(convert_checked_certificate_production_blocker(
                    error.code,
                    "checked-certificate-production",
                    error.detail,
                    [
                        "normalized_solver_proof_export",
                        "content_addressed_proof_export",
                        "proof_export_binding",
                    ],
                ));
                continue;
            }
        };

        let checker = StructuralBinaryCertificateChecker::new(
            checker_id.clone(),
            checker_version.clone(),
            vec![candidate.format.clone()],
            checked_at_unix_ms,
        );
        let export = loaded_proof_export.artifact.proof_export.clone();
        let proof_export_artifact_ref = match persist_solver_proof_export_artifacts(
            export_dir, &export,
        ) {
            Ok(artifact_ref) => artifact_ref,
            Err(error) => {
                scan.blockers.push(convert_checked_certificate_production_blocker(
                    "normalized-proof-export-persist-failed",
                    "checked-certificate-production",
                    format!(
                        "normalized proof export sidecars could not be persisted for dispatch {}: {error}",
                        candidate.dispatch.id
                    ),
                    ["normalized_solver_proof_export"],
                ));
                continue;
            }
        };
        let mut request = BinaryCertificateCheckRequest::from_export(
            &candidate.dispatch,
            &candidate.canonical_vc_bytes,
            &export,
        );
        request.replay_transcript_digest = candidate.replay_transcript_digest.as_deref();
        match produce_checked_certificate_artifact(&checker, request, export_dir) {
            Ok(artifact_ref) => match accept_convert_checked_certificate_production_artifact(
                export_dir,
                candidate,
                &export,
                artifact_ref,
                runner,
                &proof_export_artifact_ref.metadata_path,
                &proof_export_artifact_ref.proof_path,
                &source_backpropagation_gate,
            ) {
                Ok(success) => {
                    artifact_paths.push(success.artifact_path);
                    manifest.add_certificate(success.manifest_entry);
                    audit_exports.push(success.audit_export);
                }
                Err(blocker) => scan.blockers.push(blocker),
            },
            Err(error) => scan.blockers.push(convert_checked_certificate_production_blocker(
                "checked-certificate-production-failed",
                "checked-certificate-production",
                format!(
                    "checked certificate production failed for dispatch {}: {error}",
                    candidate.dispatch.id
                ),
                ["checker_success", "checked_certificate_artifact"],
            )),
        }
    }

    let manifest_path = if !manifest.certificates.is_empty() {
        match persist_checked_certificate_audit_export_bundle(export_dir, &manifest, &audit_exports)
        {
            Ok(_) => {
                scan.diagnostics.push(format!(
                    "checked certificate production manifest written to {}",
                    trust_proof_cert::checked_certificate_manifest_path(export_dir).display()
                ));
                scan.diagnostics.push(format!(
                    "checked certificate production audit export bundle written to {}",
                    checked_certificate_audit_export_bundle_path(export_dir).display()
                ));
                Some(
                    trust_proof_cert::checked_certificate_manifest_path(export_dir)
                        .display()
                        .to_string(),
                )
            }
            Err(error) => {
                scan.blockers.push(convert_checked_certificate_production_blocker(
                    "checked-certificate-audit-export-write-failed",
                    "checked-certificate-production",
                    format!(
                        "checked certificate production manifest/audit export bundle could not be written: {error}"
                    ),
                    ["checked_certificate_manifest", "checked_certificate_audit_export"],
                ));
                None
            }
        }
    } else {
        None
    };

    let status = if !artifact_paths.is_empty() && scan.blockers.is_empty() {
        "exported"
    } else if !artifact_paths.is_empty() {
        "partial"
    } else {
        "blocked"
    };
    let report = convert_checked_certificate_production_export_report(
        status,
        export_dir,
        checker_selection,
        scan,
        artifact_paths.clone(),
        manifest_path,
        source_backpropagation_gate,
    );
    ProducedCheckedCertificateArtifacts { report, artifact_paths }
}

fn accept_convert_checked_certificate_production_artifact(
    export_dir: &Path,
    candidate: &ConvertProofExportCandidate,
    export: &SolverProofExport,
    artifact_ref: trust_proof_cert::CheckedBinaryCertificateArtifactRef,
    runner: &CheckedBinaryCertificateExternalCheckerRunner,
    proof_export_metadata_path: &Path,
    proof_export_payload_path: &Path,
    source_backpropagation_gate: &CheckedBinaryCertificateSourceBackpropagationGate,
) -> Result<ConvertCheckedCertificateProductionSuccess, ConvertCheckedCertificateBlockerRecord> {
    let artifact = load_checked_certificate_artifact_ref(&artifact_ref).map_err(|error| {
        convert_checked_certificate_production_blocker(
            "checked-certificate-artifact-readback-failed",
            "checked-certificate-production",
            format!(
                "checked certificate artifact readback failed for dispatch {}: {error}",
                candidate.dispatch.id
            ),
            ["checked_certificate_artifact"],
        )
    })?;
    let relative_artifact_path = artifact_ref.path.strip_prefix(export_dir).map_err(|_| {
        convert_checked_certificate_production_blocker(
            "checked-certificate-artifact-path-invalid",
            "checked-certificate-production",
            format!(
                "checked certificate artifact path `{}` is outside export dir `{}`",
                artifact_ref.path.display(),
                export_dir.display()
            ),
            ["checked_certificate_artifact"],
        )
    })?;
    let entry =
        CheckedBinaryCertificateManifestEntry::from_artifact(&artifact, relative_artifact_path);
    let production_evidence = runner
        .run_for_manifest_entry_with_artifacts(
            &entry,
            &artifact_ref.path,
            proof_export_metadata_path,
            proof_export_payload_path,
        )
        .map_err(|error| {
            convert_checked_certificate_production_blocker(
                "production-checker-evidence-failed",
                "checked-certificate-production",
                format!(
                    "production checked-certificate checker failed for dispatch {}: {error}",
                    candidate.dispatch.id
                ),
                ["production_checker_evidence"],
            )
        })?;
    let acceptance_request =
        CheckedBinaryCertificateManifestAcceptanceRequest::from_manifest_entry_and_solver_proof_export_metadata(
            &entry,
            export.normalized_metadata(),
        )
        .and_then(|request| request.with_production_checker_evidence(production_evidence))
        .and_then(|request| request.with_source_backpropagation_gate(source_backpropagation_gate.clone()))
        .map_err(|error| {
            convert_checked_certificate_production_blocker(
                "checked-certificate-acceptance-request-invalid",
                "checked-certificate-production",
                format!(
                    "checked certificate production acceptance request is invalid for dispatch {}: {error}",
                    candidate.dispatch.id
                ),
                ["checked_certificate_manifest", "production_checker_evidence"],
            )
        })?;
    let acceptance = accept_checked_certificate_manifest_entry(
        export_dir,
        &candidate.canonical_vc_bytes,
        &entry,
        &acceptance_request,
    )
    .map_err(|error| {
        convert_checked_certificate_production_blocker(
            "checked-certificate-acceptance-failed",
            "checked-certificate-production",
            format!(
                "checked certificate manifest acceptance failed for dispatch {}: {error}",
                candidate.dispatch.id
            ),
            ["checked_certificate_manifest", "production_checker_evidence"],
        )
    })?;
    let audit_export =
        CheckedBinaryCertificateAuditExport::from_manifest_acceptance(&entry, &acceptance)
            .map_err(|error| {
                convert_checked_certificate_production_blocker(
                    "checked-certificate-audit-export-build-failed",
                    "checked-certificate-production",
                    format!(
                        "checked certificate audit export could not include dispatch {}: {error}",
                        candidate.dispatch.id
                    ),
                    ["checked_certificate_audit_export"],
                )
            })?;
    let audit_export_json = audit_export.to_json().map_err(|error| {
        convert_checked_certificate_production_blocker(
            "checked-certificate-audit-export-build-failed",
            "checked-certificate-production",
            format!(
                "checked certificate audit export could not serialize dispatch {}: {error}",
                candidate.dispatch.id
            ),
            ["checked_certificate_audit_export"],
        )
    })?;
    let manifest_identity =
        CheckedBinaryCertificateAuditExportBundleEntry::from_audit_export_and_digest(
            &audit_export,
            trust_types::digest::stable_sha256_hex(audit_export_json.as_bytes()),
        )
        .map(|entry| entry.manifest_identity_sha256)
        .map_err(|error| {
            convert_checked_certificate_production_blocker(
                "checked-certificate-manifest-identity-invalid",
                "checked-certificate-production",
                format!(
                    "checked certificate manifest identity is invalid for dispatch {}: {error}",
                    candidate.dispatch.id
                ),
                ["checked_certificate_manifest_identity"],
            )
        })?;
    if manifest_identity.trim().is_empty() {
        return Err(convert_checked_certificate_production_blocker(
            "checked-certificate-manifest-identity-missing",
            "checked-certificate-production",
            format!(
                "checked certificate manifest identity is missing for dispatch {}",
                candidate.dispatch.id
            ),
            ["checked_certificate_manifest_identity"],
        ));
    }
    Ok(ConvertCheckedCertificateProductionSuccess {
        artifact_path: artifact_ref.path.display().to_string(),
        manifest_entry: entry,
        audit_export,
    })
}

fn convert_checked_certificate_source_backpropagation_gate_for_decompilation_artifact(
    artifact: &DecompilationArtifact,
    scan: &ConvertProofExportCandidateScan,
) -> CheckedBinaryCertificateSourceBackpropagationGate {
    let source_provenance = artifact.source_provenance.clone();
    let has_proof_export_candidate = !scan.candidates.is_empty();
    let replay_grade_artifact_identity = has_proof_export_candidate
        && artifact.reconstruction.trust_level == TrustLevel::ProofGrade
        && scan.candidates.iter().all(|candidate| {
            candidate
                .dispatch
                .binary_artifact_digest_identity
                .as_ref()
                .is_some_and(|identity| identity.digest_identity_blockers().is_empty())
        });
    let checked_certificate_identity = has_proof_export_candidate && replay_grade_artifact_identity;
    let exact_replay_identity = checked_certificate_identity
        && scan.candidates.iter().all(|candidate| {
            candidate.dispatch.replay == ReplayStatus::Replayed
                && candidate
                    .replay_transcript_digest
                    .as_deref()
                    .is_some_and(trust_types::digest::is_stable_sha256_hex)
        });
    let exact_source_provenance = source_provenance.effective_source_backpropagation_allowed();
    let reconstruction_validation_accepted =
        artifact.reconstruction.validation == ReconstructionValidationStatus::Validated;
    let target_outputs = artifact
        .reconstruction
        .outputs
        .iter()
        .filter(|output| output.target == artifact.reconstruction.target)
        .collect::<Vec<_>>();
    let accepted_target_validation = !target_outputs.is_empty()
        && target_outputs.iter().all(|output| output.target_validation_blockers.is_empty());
    let preserved_symbolic_formulas =
        target_outputs.iter().map(|output| output.preserved_symbolic_formulas.len()).sum();
    let symbolic_formula_consumer_accepted = target_outputs
        .iter()
        .all(|output| decompiled_output_symbolic_formulas_have_consumer(output));

    CheckedBinaryCertificateSourceBackpropagationGate::evaluated(
        source_provenance,
        replay_grade_artifact_identity,
        checked_certificate_identity,
        exact_replay_identity,
        reconstruction_validation_accepted,
        accepted_target_validation,
        exact_source_provenance,
    )
    .with_unsupported_ledger_summary(UnsupportedLedgerSummary::from_ledger(&artifact.unsupported))
    .with_symbolic_formula_consumer_evidence(
        preserved_symbolic_formulas,
        symbolic_formula_consumer_accepted,
    )
}

fn decompiled_output_symbolic_formulas_have_consumer(output: &DecompiledOutput) -> bool {
    output.preserved_symbolic_formulas.is_empty()
        || (output.target_validation_blockers.is_empty()
            && output.preserved_symbolic_formulas.iter().all(|formula| {
                output
                    .diagnostics
                    .iter()
                    .any(|diagnostic| formula.matches_schema_aware_consumer_diagnostic(diagnostic))
            }))
}

fn scan_decompilation_proof_export_candidates(
    artifact: &DecompilationArtifact,
) -> ConvertProofExportCandidateScan {
    let mut scan = ConvertProofExportCandidateScan::default();
    let mut seen_dispatches = BTreeSet::new();
    let dispatches = artifact.verification.solver_dispatch.iter().chain(
        artifact.functions.iter().flat_map(|function| function.verification.solver_dispatch.iter()),
    );

    for dispatch in dispatches {
        if !seen_dispatches.insert(dispatch.id.clone()) {
            continue;
        }
        if !dispatch_proves_binary_certificate_candidate(dispatch) {
            continue;
        }
        scan.candidate_dispatches += 1;
        let Some(canonical_vc_bytes) = canonical_vc_bytes_for_dispatch(dispatch) else {
            scan.blockers.push(convert_checked_certificate_production_blocker(
                "canonical-vc-missing",
                "checked-certificate-production",
                format!(
                    "solver dispatch {} is missing canonical VC bytes required for checked-certificate production",
                    dispatch.id
                ),
                ["canonical_vc"],
            ));
            continue;
        };
        if dispatch.origin.as_ref().and_then(|origin| digest_binary_origin(origin).ok()).is_none() {
            scan.blockers.push(convert_checked_certificate_production_blocker(
                "binary-origin-missing",
                "checked-certificate-production",
                format!(
                    "solver dispatch {} is missing binary-origin binding required for checked-certificate production",
                    dispatch.id
                ),
                ["binary_origin"],
            ));
            continue;
        }
        scan.canonical_binding_candidates += 1;

        if dispatch_has_raw_solver_proof_bytes_for_convert(dispatch) {
            scan.blockers.push(convert_checked_certificate_production_blocker(
                "raw-solver-proof-bytes-audit-only",
                "checked-certificate-production",
                format!(
                    "solver dispatch {} carries raw solver proof bytes; raw bytes are audit-only and cannot be exported as checked certificates",
                    dispatch.id
                ),
                ["normalized_solver_proof_export", "production_checker"],
            ));
            continue;
        }

        let replay_transcript_digest_raw =
            dispatch_exact_replay_transcript_artifact_digest_raw_for_release(dispatch);
        let replay_transcript_digest = replay_transcript_digest_raw
            .as_deref()
            .filter(|digest| trust_types::digest::is_stable_sha256_hex(digest))
            .map(str::to_string);
        if dispatch.replay == ReplayStatus::Replayed && replay_transcript_digest.is_none() {
            match replay_transcript_digest_raw {
                Some(digest) => scan.blockers.push(convert_checked_certificate_production_blocker(
                    "replay-transcript-digest-noncanonical",
                    "checked-certificate-production",
                    format!(
                        "solver dispatch {} replay transcript digest is not canonical lowercase SHA-256 hex: {digest}",
                        dispatch.id
                    ),
                    ["canonical_sha256_replay_transcript_digest"],
                )),
                None => scan.blockers.push(convert_checked_certificate_production_blocker(
                    "replay-transcript-digest-missing",
                    "checked-certificate-production",
                    format!(
                        "replayed solver dispatch {} is missing a canonical replay transcript digest required for checked-certificate production",
                        dispatch.id
                    ),
                    ["machine_replay_transcript", "canonical_sha256_replay_transcript_digest"],
                )),
            }
            continue;
        }

        let ProofCertificateStatus::Present {
            format,
            sha256: Some(proof_sha256),
            artifact_path: Some(path),
        } = &dispatch.certificate
        else {
            scan.blockers.push(convert_checked_certificate_production_blocker(
                "normalized-proof-export-missing",
                "checked-certificate-production",
                format!(
                    "solver dispatch {} has no normalized solver proof export path and digest",
                    dispatch.id
                ),
                ["normalized_solver_proof_export"],
            ));
            continue;
        };
        if format.trim().is_empty() || format == "solver-native" {
            scan.blockers.push(convert_checked_certificate_production_blocker(
                "normalized-proof-export-format-missing",
                "checked-certificate-production",
                format!(
                    "solver dispatch {} has proof format `{format}`; checked-certificate production requires a normalized proof format",
                    dispatch.id
                ),
                ["normalized_solver_proof_export"],
            ));
            continue;
        }
        scan.proof_export_candidates += 1;
        scan.candidates.push(ConvertProofExportCandidate {
            dispatch: dispatch.clone(),
            canonical_vc_bytes,
            format: format.clone(),
            proof_path: PathBuf::from(path),
            proof_sha256: proof_sha256.clone(),
            replay_transcript_digest,
        });
    }

    if scan.candidate_dispatches == 0 {
        scan.blockers.push(convert_checked_certificate_production_blocker(
            "solver-dispatch-missing",
            "checked-certificate-production",
            "decompile/convert artifact contains no proved binary solver dispatches for checked-certificate production",
            ["proved_binary_solver_dispatch"],
        ));
    } else if scan.proof_export_candidates == 0 {
        scan.blockers.push(convert_checked_certificate_production_blocker(
            "normalized-proof-export-missing",
            "checked-certificate-production",
            "decompile/convert artifact contains no normalized proof exports for checked-certificate production",
            ["normalized_solver_proof_export"],
        ));
    }

    scan
}

fn dispatch_exact_replay_transcript_artifact_digest_raw_for_release(
    record: &SolverDispatchRecord,
) -> Option<String> {
    record.diagnostics.iter().find_map(|diagnostic| {
        diagnostic
            .trim()
            .strip_prefix(EXACT_REPLAY_TRANSCRIPT_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX)
            .map(str::to_string)
    })
}

fn convert_checked_certificate_production_export_report(
    status: &str,
    export_dir: &Path,
    checker_selection: String,
    scan: ConvertProofExportCandidateScan,
    artifact_paths: Vec<String>,
    manifest_path: Option<String>,
    source_backpropagation_gate: CheckedBinaryCertificateSourceBackpropagationGate,
) -> ConvertCheckedCertificateProductionExportReport {
    let exported_artifacts = artifact_paths.len();
    let rejected_dispatches = scan.candidate_dispatches.saturating_sub(exported_artifacts);
    let mut diagnostics = scan.diagnostics;
    if exported_artifacts > 0 {
        diagnostics.push(format!(
            "checked certificate production exported {exported_artifacts} artifact(s) to {}",
            export_dir.display()
        ));
    }
    ConvertCheckedCertificateProductionExportReport {
        status: status.to_string(),
        export_dir: export_dir.display().to_string(),
        checker_selection,
        candidate_dispatches: scan.candidate_dispatches,
        canonical_binding_candidates: scan.canonical_binding_candidates,
        proof_export_candidates: scan.proof_export_candidates,
        exported_artifacts,
        rejected_dispatches,
        artifact_paths,
        manifest_path,
        source_backpropagation_gate_sha256: stable_json_sha256(&source_backpropagation_gate),
        source_backpropagation_gate,
        blockers: scan.blockers,
        diagnostics,
    }
}

fn convert_checked_certificate_production_blocker(
    code: impl Into<String>,
    stage: impl Into<String>,
    detail: impl Into<String>,
    evidence_required: impl IntoIterator<Item = &'static str>,
) -> ConvertCheckedCertificateBlockerRecord {
    ConvertCheckedCertificateBlockerRecord {
        code: code.into(),
        stage: format!("targo-trust::{}", stage.into()),
        feature: "checked-certificate-production".to_string(),
        detail: detail.into(),
        evidence_required: evidence_required.into_iter().map(str::to_string).collect(),
    }
}

fn dispatch_proves_binary_certificate_candidate(dispatch: &SolverDispatchRecord) -> bool {
    dispatch.status == SolverDispatchStatus::Unsat
        && dispatch.query_semantics == SolverQuerySemantics::SatIsCounterexample
}

fn canonical_vc_bytes_for_dispatch(dispatch: &SolverDispatchRecord) -> Option<Vec<u8>> {
    serde_json::to_vec(dispatch.vc.as_ref()?).ok()
}

fn dispatch_has_raw_solver_proof_bytes_for_convert(dispatch: &SolverDispatchRecord) -> bool {
    matches!(
        dispatch.result,
        Some(trust_types::VerificationResult::Proved { proof_certificate: Some(_), .. })
    )
}

fn convert_checked_certificate_loader_missing_blocker(
    detail: impl Into<String>,
) -> ConvertCheckedCertificateBlockerRecord {
    ConvertCheckedCertificateBlockerRecord {
        code: "convert-checked-certificate-loader-missing".to_string(),
        stage: "targo-trust::convert-loader".to_string(),
        feature: "checked-certificate-loader".to_string(),
        detail: detail.into(),
        evidence_required: vec![
            "checked_certificate_artifact".to_string(),
            "convert_checked_certificate_loader".to_string(),
        ],
    }
}

fn convert_checked_certificate_loader_failure_report(
    artifact_paths: &[String],
    manifest_paths: &[String],
    error: impl std::fmt::Display,
) -> ConvertCheckedCertificateLoaderReport {
    let detail = format!("failed to load checked certificate artifact or manifest: {error}");
    ConvertCheckedCertificateLoaderReport {
        status: "load_failed".to_string(),
        implementation: "targo-trust::convert-metadata-only".to_string(),
        requested_artifacts: artifact_paths.len(),
        requested_manifests: manifest_paths.len(),
        loaded_artifacts: 0,
        production_export: None,
        external_checker: None,
        artifacts: Vec::new(),
        readback_records: Vec::new(),
        blocker: Some(ConvertCheckedCertificateBlockerRecord {
            code: "convert-checked-certificate-load-failed".to_string(),
            stage: "targo-trust::convert-loader".to_string(),
            feature: "checked-certificate-loader".to_string(),
            detail: detail.clone(),
            evidence_required: vec![
                "loadable_checked_certificate_artifact".to_string(),
                "loadable_checked_certificate_manifest".to_string(),
            ],
        }),
        diagnostics: vec![detail],
    }
}

fn convert_checked_certificate_artifact_rows(
    loader: &ConvertCheckedCertificateLoaderReport,
) -> Vec<CheckedCertificateArtifactImportRecord> {
    loader.artifacts.clone()
}

fn convert_checked_certificate_artifact_readback_row(
    row: &LoadedCheckedCertificateArtifact,
) -> CheckedCertificateArtifactImportRecord {
    CheckedCertificateArtifactImportRecord {
        artifact_path: Some(row.path.clone()),
        certificate_sha256: row.artifact.certificate_sha256.clone(),
        checker: row.artifact.checker.clone(),
        checker_version: row.artifact.checker_version.clone(),
        format: row.artifact.format.clone(),
        checked_at_unix_ms: row.artifact.checked_at_unix_ms,
        vc_sha256: row.artifact.vc_sha256.clone(),
        origin_sha256: row.artifact.origin_sha256.clone(),
        proof_export_sha256: row.artifact.proof_export_sha256.clone(),
        binary_artifact_digest_identity: row.artifact.binary_artifact_digest_identity.clone(),
        source_backpropagation_gate: row.source_backpropagation_gate.clone(),
        manifest_identity_sha256: row.manifest_identity_sha256.clone(),
        source_backpropagation_gate_sha256: row.source_backpropagation_gate_sha256.clone(),
        replay_transcript_digest: row.replay_transcript_digest.clone(),
        replay_digest_identity: checked_certificate_replay_digest_identity_record(
            row.artifact.replay,
            row.replay_transcript_digest
                .clone()
                .or_else(|| row.artifact.replay_transcript_digest.clone()),
            Some(row.artifact.binary_artifact_digest_identity.clone()),
        ),
        production_checker_evidence_status: production_evidence_status_from_sha256(
            row.production_checker_evidence_sha256.as_deref(),
        )
        .to_string(),
        production_checker_evidence_sha256: row.production_checker_evidence_sha256.clone(),
        status: "readback".to_string(),
        dispatch_id: Some(row.artifact.dispatch_id.clone()),
        diagnostic: Some(
            "checked proof-cert artifact and normalized solver proof export metadata read back for conversion audit"
                .to_string(),
        ),
    }
}

fn convert_checked_certificate_readback_record(
    row: &LoadedCheckedCertificateArtifact,
) -> ConvertCheckedCertificateReadbackRecord {
    let production_evidence = checked_certificate_production_evidence_status(&row.artifact.checker);
    let production_checker_evidence_sha256 = row
        .production_checker_evidence_sha256
        .clone()
        .or_else(|| production_evidence_sha256(&production_evidence));
    let replay_transcript_digest = row
        .replay_transcript_digest
        .clone()
        .or_else(|| row.artifact.replay_transcript_digest.clone());
    let release_transcript_binding = release_transcript_binding_report(
        &row.artifact.binary_artifact_digest_identity,
        Some(row.artifact.vc_sha256.clone()),
        Some(row.artifact.certificate_sha256.clone()),
        replay_transcript_digest.clone(),
        Some(row.artifact.origin_sha256.clone()),
        &TargetConsumerDigestBinding::default(),
    );
    let proof_grade_release_transcript_row =
        proof_grade_release_transcript_row_report(ProofGradeReleaseTranscriptRowInput {
            evidence_origin: "targo_trust_checked_certificate_readback",
            candidate_commit: release_transcript_candidate_commit(),
            binary_artifact_digest_identity: &row.artifact.binary_artifact_digest_identity,
            vc_sha256s: release_transcript_digest_values([row.artifact.vc_sha256.clone()]),
            checked_certificate_sha256s: release_transcript_digest_values([row
                .artifact
                .certificate_sha256
                .clone()]),
            replay_transcript_sha256s: release_transcript_digest_values(
                replay_transcript_digest.clone(),
            ),
            provenance_sha256s: release_transcript_digest_values([row
                .artifact
                .origin_sha256
                .clone()]),
            unsupported_ledgers_empty: false,
            target_consumer: &TargetConsumerDigestBinding::default(),
            exact_source_ownership_sha256: None,
            type_ownership_sha256: None,
            aarch64_ordering_monitor_evidence: Vec::new(),
        });
    ConvertCheckedCertificateReadbackRecord {
        source: "checked_certificate_artifact".to_string(),
        status: "readback".to_string(),
        artifact_path: Some(row.path.clone()),
        dispatch_id: row.artifact.dispatch_id.clone(),
        vc_sha256: row.artifact.vc_sha256.clone(),
        origin_sha256: row.artifact.origin_sha256.clone(),
        proof_sha256: row.artifact.proof_sha256.clone(),
        proof_export_sha256: row.artifact.proof_export_sha256.clone(),
        certificate_sha256: row.artifact.certificate_sha256.clone(),
        binary_artifact_digest_identity: row.artifact.binary_artifact_digest_identity.clone(),
        source_backpropagation_gate: row.source_backpropagation_gate.clone(),
        manifest_identity_sha256: row.manifest_identity_sha256.clone(),
        source_backpropagation_gate_sha256: row.source_backpropagation_gate_sha256.clone(),
        replay_transcript_digest: replay_transcript_digest.clone(),
        replay_digest_identity: checked_certificate_replay_digest_identity_record(
            row.artifact.replay,
            replay_transcript_digest,
            Some(row.artifact.binary_artifact_digest_identity.clone()),
        ),
        checker: row.artifact.checker.clone(),
        checker_version: row.artifact.checker_version.clone(),
        format: row.artifact.format.clone(),
        production_checker_evidence_status: production_evidence_status_from_sha256(
            production_checker_evidence_sha256.as_deref(),
        )
        .to_string(),
        production_checked: production_checker_evidence_sha256.is_some(),
        production_checker_evidence_sha256,
        production_checker_evidence_detail: production_evidence_detail(&production_evidence)
            .or_else(|| {
                row.production_checker_evidence_sha256
                    .as_ref()
                    .map(|sha| format!("production checker evidence sha256={sha}"))
            }),
        external_checker_status: None,
        external_checker_evidence_sha256: None,
        external_checker_binary_sha256: None,
        external_checker_invocation_sha256: None,
        external_checker_stdout_sha256: None,
        external_checker_stderr_sha256: None,
        release_transcript_binding,
        proof_grade_release_transcript_row,
        query_semantics: solver_query_semantics_label(row.artifact.query_semantics).to_string(),
        replay: replay_status_label(row.artifact.replay).to_string(),
        checked_at_unix_ms: row.artifact.checked_at_unix_ms,
    }
}

fn checked_certificate_production_evidence_status(
    checker: &str,
) -> ProofCertificateProductionCheckerEvidenceStatus {
    ProofCertificateStatus::Checked {
        checker: checker.to_string(),
        format: "unknown".to_string(),
        sha256: None,
    }
    .production_checker_evidence_status()
}

fn production_evidence_sha256(
    status: &ProofCertificateProductionCheckerEvidenceStatus,
) -> Option<String> {
    match status {
        ProofCertificateProductionCheckerEvidenceStatus::Present { evidence } => {
            Some(evidence.production_checker_evidence_sha256.clone())
        }
        _ => None,
    }
}

fn production_evidence_status_from_sha256(sha256: Option<&str>) -> &'static str {
    if sha256.is_some_and(|sha| !sha.trim().is_empty()) { "present" } else { "missing" }
}

fn nonempty_digest(value: &str) -> Option<String> {
    (!value.trim().is_empty()).then(|| value.to_string())
}

fn production_evidence_detail(
    status: &ProofCertificateProductionCheckerEvidenceStatus,
) -> Option<String> {
    match status {
        ProofCertificateProductionCheckerEvidenceStatus::Present { evidence } => Some(format!(
            "production checker evidence sha256={} checker={} checker_version={}",
            evidence.production_checker_evidence_sha256, evidence.checker, evidence.checker_version
        )),
        ProofCertificateProductionCheckerEvidenceStatus::Malformed { reason } => {
            Some(reason.clone())
        }
        ProofCertificateProductionCheckerEvidenceStatus::Missing => None,
    }
}

fn convert_accepted_checked_certificate_evidence_records(
    loader: &ConvertCheckedCertificateLoaderReport,
    readback_records: &[ConvertCheckedCertificateReadbackRecord],
) -> Vec<CheckedCertificateAcceptedEvidenceRecord> {
    readback_records
        .iter()
        .filter(|record| record.status == "readback")
        .map(|record| CheckedCertificateAcceptedEvidenceRecord {
            source: "checked_certificate_readback".to_string(),
            status: "accepted".to_string(),
            artifact_path: record.artifact_path.clone(),
            dispatch_id: Some(record.dispatch_id.clone()),
            certificate_sha256: record.certificate_sha256.clone(),
            checker: record.checker.clone(),
            checker_version: record.checker_version.clone(),
            format: record.format.clone(),
            checked_at_unix_ms: record.checked_at_unix_ms,
            vc_sha256: record.vc_sha256.clone(),
            origin_sha256: record.origin_sha256.clone(),
            proof_export_sha256: nonempty_digest(&record.proof_export_sha256),
            source_backpropagation_gate: record.source_backpropagation_gate.clone(),
            manifest_identity_sha256: record.manifest_identity_sha256.clone(),
            source_backpropagation_gate_sha256: record.source_backpropagation_gate_sha256.clone(),
            replay_transcript_digest: record.replay_transcript_digest.clone(),
            replay_digest_identity: record.replay_digest_identity.clone(),
            release_transcript_binding: record.release_transcript_binding.clone(),
            proof_grade_release_transcript_row: record.proof_grade_release_transcript_row.clone(),
            production_checker_evidence_status: record.production_checker_evidence_status.clone(),
            production_checker_evidence_sha256: record.production_checker_evidence_sha256.clone(),
        })
        .filter(|record| {
            loader.artifacts.iter().any(|artifact| {
                artifact.status == "readback"
                    && artifact.certificate_sha256 == record.certificate_sha256
                    && artifact.vc_sha256 == record.vc_sha256
                    && artifact.origin_sha256 == record.origin_sha256
            })
        })
        .collect()
}

fn solver_query_semantics_label(semantics: SolverQuerySemantics) -> &'static str {
    match semantics {
        SolverQuerySemantics::SatIsCounterexample => "sat_is_counterexample",
        SolverQuerySemantics::SatIsFeasiblePath => "sat_is_feasible_path",
        SolverQuerySemantics::SatIsSatisfiableOnly => "sat_is_satisfiable_only",
        SolverQuerySemantics::Unknown => "unknown",
        _ => "unknown",
    }
}

fn solver_dispatch_status_label(status: SolverDispatchStatus) -> &'static str {
    match status {
        SolverDispatchStatus::NotDispatched => "not_dispatched",
        SolverDispatchStatus::Sat => "sat",
        SolverDispatchStatus::Unsat => "unsat",
        SolverDispatchStatus::Unknown => "unknown",
        SolverDispatchStatus::Timeout => "timeout",
        SolverDispatchStatus::Error => "error",
        SolverDispatchStatus::Unsupported => "unsupported",
        SolverDispatchStatus::Rejected => "rejected",
        _ => "unknown",
    }
}

fn replay_status_label(status: ReplayStatus) -> &'static str {
    match status {
        ReplayStatus::NotAttempted => "not_attempted",
        ReplayStatus::Replayed => "replayed",
        ReplayStatus::Spurious => "spurious",
        ReplayStatus::Failed => "failed",
        _ => "unknown",
    }
}

fn target_blocker_mentions_checked_certificate(blocker: &TargetValidationBlocker) -> bool {
    if let Some(code) = target_validation_blocker_machine_code(blocker) {
        return code.contains("checked") || code.contains("proof");
    }

    let text_mentions = blocker.feature.contains("checked")
        || blocker.feature.contains("proof")
        || blocker.reason.contains("checked certificate")
        || blocker.reason.contains("proof certificate");
    text_mentions
        || blocker.diagnostics.iter().any(|diagnostic| {
            diagnostic.contains("checked-certificate") || diagnostic.contains("proof")
        })
}

fn convert_checked_certificate_blocker_from_target(
    blocker: &TargetValidationBlocker,
) -> ConvertCheckedCertificateBlockerRecord {
    ConvertCheckedCertificateBlockerRecord {
        code: convert_checked_certificate_blocker_code(blocker),
        stage: blocker.stage.clone(),
        feature: blocker.feature.clone(),
        detail: blocker.reason.clone(),
        evidence_required: convert_checked_certificate_evidence_required(blocker),
    }
}

fn convert_checked_certificate_blocker_code(blocker: &TargetValidationBlocker) -> String {
    if let Some(code) = target_validation_blocker_machine_code(blocker) {
        return code.to_string();
    }

    if blocker.feature.contains("raw-solver-proof-bytes") {
        "raw-solver-proof-bytes-audit-only".to_string()
    } else if blocker.feature.contains("checked-certificate")
        || blocker.feature.contains("checked-proof")
    {
        "checked-certificate-missing".to_string()
    } else if blocker.feature.contains("proof") {
        "proof-evidence-missing".to_string()
    } else {
        "checked-certificate-evidence-blocked".to_string()
    }
}

fn convert_checked_certificate_evidence_required(blocker: &TargetValidationBlocker) -> Vec<String> {
    let mut required = blocker
        .diagnostics
        .iter()
        .filter_map(|diagnostic| diagnostic.strip_prefix("required-evidence="))
        .map(str::to_string)
        .collect::<Vec<_>>();
    if required.is_empty() {
        required.extend([
            "normalized_solver_proof_export".to_string(),
            "checker_success".to_string(),
            "checked_certificate_artifact".to_string(),
        ]);
    }
    required
}

fn format_target_validation_blocker(blocker: &TargetValidationBlocker) -> String {
    let function = blocker
        .function
        .as_ref()
        .map(|function| format!(" function `{function}`"))
        .unwrap_or_default();
    format!("{}{}: {}", blocker.feature, function, blocker.reason)
}

fn format_preserved_symbolic_formula(formula: &PreservedSymbolicFormula) -> String {
    let function = formula
        .function
        .as_ref()
        .map(|function| format!(" function `{function}`"))
        .unwrap_or_default();
    let block = formula.block.map(|block| format!(" bb{block}")).unwrap_or_default();
    let statement =
        formula.statement_index.map(|statement| format!(" stmt{statement}")).unwrap_or_default();
    let evidence = formula.evidence();
    format!(
        "{}{}{}{} {}: {:?} [schema={} sort={} digest={} origin={}]",
        decompile_artifact_target_label(&formula.target),
        function,
        block,
        statement,
        formula.location,
        formula.formula,
        evidence.schema,
        evidence.sort,
        evidence.digest,
        evidence.origin
    )
}

fn decompile_artifact_target_label(target: &trust_types::DecompileTarget) -> &str {
    match target {
        trust_types::DecompileTarget::TrustIr => "trust_ir",
        trust_types::DecompileTarget::Rust => "rust",
        trust_types::DecompileTarget::TrustCg => "trust-cg",
        trust_types::DecompileTarget::Wasm => "wasm",
        trust_types::DecompileTarget::PseudoSource => "pseudo_source",
        trust_types::DecompileTarget::Other(label) => label.as_str(),
        _ => "unknown",
    }
}

#[cfg(test)]
fn serialize_convert_json(report: &DecompileReport) -> serde_json::Result<String> {
    serialize_convert_json_with_checked_certificate_loader(
        report,
        convert_checked_certificate_loader_not_requested(),
    )
}

fn serialize_convert_json_with_checked_certificate_loader(
    report: &DecompileReport,
    checked_certificate_loader: ConvertCheckedCertificateLoaderReport,
) -> serde_json::Result<String> {
    let conversion_gate = build_convert_cli_gate_with_loader(report, checked_certificate_loader);
    let checked_certificate_readback = conversion_gate.checked_certificate_evidence.clone();
    let target_proof_consumer_evidence = conversion_gate.target_proof_consumer_evidence.clone();
    let target_evidence =
        build_decompile_target_evidence(report, target_proof_consumer_evidence.as_ref());
    let proof_grade_release_transcript = proof_grade_release_transcript_report(
        &checked_certificate_readback.proof_grade_release_transcript_rows,
    );
    serde_json::to_string_pretty(&ConvertJsonReport {
        report,
        trust_cg_output: convert_trust_cg_output(report),
        target_proof_consumer_evidence,
        target_evidence,
        checked_certificate_readback,
        proof_grade_release_transcript,
        conversion_gate,
    })
}

fn serialize_decompile_json_with_checked_certificate_loader(
    report: &DecompileReport,
    checked_certificate_loader: ConvertCheckedCertificateLoaderReport,
) -> serde_json::Result<String> {
    let artifact_gate = build_convert_cli_gate_with_loader(report, checked_certificate_loader);
    let checked_certificate_readback = artifact_gate.checked_certificate_evidence.clone();
    let target_proof_consumer_evidence = artifact_gate.target_proof_consumer_evidence.clone();
    let target_evidence =
        build_decompile_target_evidence(report, target_proof_consumer_evidence.as_ref());
    let proof_grade_release_transcript = proof_grade_release_transcript_report(
        &checked_certificate_readback.proof_grade_release_transcript_rows,
    );
    serde_json::to_string_pretty(&DecompileJsonReport {
        report,
        trust_cg_output: convert_trust_cg_output(report),
        target_proof_consumer_evidence,
        target_evidence,
        checked_certificate_readback,
        proof_grade_release_transcript,
        artifact_gate,
    })
}

fn convert_trust_cg_output(report: &DecompileReport) -> Option<serde_json::Value> {
    if report.target != DecompileTarget::TrustCg {
        return None;
    }
    serde_json::from_str(report.output_content.as_ref()?).ok()
}

fn build_exploit_evidence_gate(report: &ExploitFindReport) -> ExploitEvidenceGateReport {
    let stage_records = exploit_analyzer_stage_records(report.target, &report.binary_report);
    let claim_capture = exploit_stage_status(&stage_records, "claim_capture");
    let attribution = exploit_stage_status(&stage_records, "attribution");
    let regression_emission = exploit_stage_status(&stage_records, "regression_emission");
    let required_evidence = exploit_required_evidence();
    let unsupported_evidence_blocks_completion = stage_records
        .iter()
        .filter(|record| record.stage != "evidence_gate")
        .any(|record| record.status == ExploitFindStatus::Unsupported.label());
    let blockers = exploit_evidence_gate_blockers(report, &stage_records);
    let proof_grade_complete = blockers.is_empty();
    ExploitEvidenceGateReport {
        accepted: proof_grade_complete,
        status: if proof_grade_complete { "accepted".into() } else { "rejected".into() },
        proof_grade_complete,
        unsupported_evidence_blocks_completion,
        exploit_found: report.exploit_found && proof_grade_complete,
        claim_capture,
        replay: report.replay_status.label().to_string(),
        independent_refutation: report.independent_refutation_status.label().to_string(),
        reduction: report.reducer_status.label().to_string(),
        attribution,
        regression_emission,
        required_evidence,
        blockers,
        reason: if proof_grade_complete {
            "proof-grade exploit evidence accepted".to_string()
        } else {
            report.reason.clone()
        },
    }
}

fn build_checked_certificate_refutation_accounting(
    report: &ExploitFindReport,
) -> CheckedCertificateRefutationAccountingReport {
    let evidence = exploit_evidence_summary(&report.binary_report);
    let proof_evidence = &report.binary_report.proof_evidence;
    let required_vcs = evidence.required_vcs;
    let checked_unsat_refutations = evidence.checked_unsat_refutations;

    CheckedCertificateRefutationAccountingReport {
        required_vcs,
        solver_dispatches: proof_evidence.solver_dispatch.len(),
        proved_vcs: proof_evidence.proved_vcs(),
        raw_solver_candidates: evidence.raw_solver_candidates,
        exact_replayed_candidates: evidence.exact_replayed_candidates,
        checked_unsat_refutations,
        missing_checked_unsat_refutations: required_vcs.saturating_sub(checked_unsat_refutations),
        all_required_vcs_checked_unsat: evidence.all_required_vcs_checked_unsat,
        independent_refutation_status: evidence.independent_refutation_status,
        independent_refutation_satisfied: evidence.independent_refutation_status
            == ExploitFindStatus::Satisfied,
        diagnostic: report.independent_refutation_note.clone(),
    }
}

fn exploit_stage_status(records: &[ExploitAnalyzerStageRecord], stage: &str) -> String {
    records
        .iter()
        .find(|record| record.stage == stage)
        .map(|record| record.status.clone())
        .unwrap_or_else(|| "not_run".to_string())
}

fn exploit_required_evidence() -> Vec<String> {
    vec![
        "normalized_exploit_claim".to_string(),
        "machine_code_replay".to_string(),
        "independent_refutation".to_string(),
        "minimized_replayable_witness".to_string(),
        "target_attribution".to_string(),
        "regression_test_emission".to_string(),
    ]
}

fn exploit_evidence_gate_blockers(
    report: &ExploitFindReport,
    stage_records: &[ExploitAnalyzerStageRecord],
) -> Vec<String> {
    let mut blockers = stage_records
        .iter()
        .filter(|record| record.stage != "evidence_gate" && record.blocks_exploit_confirmation)
        .map(|record| {
            format!(
                "{} is `{}`; requires {}; {}",
                record.stage,
                record.status,
                record.evidence_required.join(","),
                record.diagnostic
            )
        })
        .collect::<Vec<_>>();

    if !report.exploit_found {
        blockers.push(
            "exploit_found is false; proof-grade exploit evidence requires a replay/refutation-backed exploit witness"
                .to_string(),
        );
    }
    if matches!(report.status, ExploitFindStatus::Unsupported) {
        blockers.push(
            "exploit-find status is `unsupported`; unsupported evidence cannot satisfy proof-grade completion"
                .to_string(),
        );
    }
    if report.binary_status != BinaryLiftStatus::Ok {
        blockers.push(format!(
            "binary lift status is `{}`; proof-grade exploit evidence requires `ok`",
            report.binary_status.label()
        ));
    }
    if report.vcs == 0 {
        blockers.push(
            "no binary VCs were generated; proof-grade exploit evidence requires checked obligations"
                .to_string(),
        );
    }

    blockers
}

fn serialize_exploit_find_json(report: &ExploitFindReport) -> serde_json::Result<String> {
    serde_json::to_string_pretty(&ExploitFindJsonReport {
        report,
        typed_scaffold: exploit_find::build_typed_exploit_find_scaffold(
            report.target,
            &report.binary_report,
        ),
        claim_capture_records: exploit_claim_capture_records(report.target, &report.binary_report),
        analyzer_stage_records: exploit_analyzer_stage_records(
            report.target,
            &report.binary_report,
        ),
        evidence_gate: build_exploit_evidence_gate(report),
        checked_certificate_refutation_accounting: build_checked_certificate_refutation_accounting(
            report,
        ),
    })
}

fn run_decompile_subcommand(args: &[String]) -> ExitCode {
    if args.iter().any(|arg| arg == "--help" || arg == "-h") {
        print!("{}", decompile_usage_text());
        return ExitCode::SUCCESS;
    }

    let sub_args = match parse_subcommand_args(args) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("targo trust: {e}");
            return ExitCode::from(2);
        }
    };
    if let Some(error) = checked_certificate_checker_configuration_error(&sub_args) {
        eprintln!("targo trust decompile: {error}");
        return ExitCode::from(2);
    }

    if matches!(sub_args.format, OutputFormat::Html) {
        eprintln!(
            "targo trust: decompile does not support --format html yet; use terminal or json"
        );
        return ExitCode::from(2);
    }

    if sub_args.entry.is_some() && sub_args.all_functions {
        eprintln!("targo trust: decompile accepts either --entry or --all, not both");
        return ExitCode::from(2);
    }

    let target = match parse_decompile_target(sub_args.to_ref.as_deref()) {
        Ok(target) => target,
        Err(e) => {
            eprintln!("targo trust: {e}");
            return ExitCode::from(2);
        }
    };

    let binary = match binary_subcommand_arg(&sub_args, "decompile") {
        Ok(binary) => binary,
        Err(e) => {
            eprintln!("targo trust: {e}");
            return ExitCode::from(2);
        }
    };

    let entry = match parse_lift_entry(sub_args.entry.as_deref()) {
        Ok(entry) => entry,
        Err(e) => {
            eprintln!("targo trust: {e}");
            return ExitCode::from(2);
        }
    };

    let binary_path = Path::new(binary);
    let bytes = match read_binary_artifact(binary_path) {
        Ok(bytes) => bytes,
        Err(error) => {
            eprintln!("targo trust: failed to read {}: {error}", binary_path.display());
            return ExitCode::from(2);
        }
    };

    let options =
        DecompileOptions::with_lift(lift_options(entry, sub_args.all_functions, sub_args.strict))
            .with_outputs([decompile_output_kind(target, sub_args.format)]);
    let binary_metadata = sniff_binary_metadata(&bytes);
    let decompile_result = decompile_binary(&bytes, options);
    let checked_at_unix_ms = current_unix_ms();
    let checked_certificate_production = decompile_result.as_ref().ok().and_then(|artifact| {
        sub_args.checked_certificate_export_dir.as_deref().map(|export_dir| {
            produce_convert_checked_certificate_artifacts_for_decompilation(
                artifact,
                Path::new(export_dir),
                sub_args.checked_certificate_checker.as_deref().map(Path::new),
                checked_at_unix_ms,
            )
        })
    });
    let mut checked_certificate_artifacts = sub_args.checked_certificate_artifacts.clone();
    let mut checked_certificate_manifests = sub_args.checked_certificate_manifests.clone();
    if let Some(production) = &checked_certificate_production {
        if let Some(manifest_path) = production.report.manifest_path.clone() {
            checked_certificate_manifests.push(manifest_path);
        } else {
            checked_certificate_artifacts.extend(production.artifact_paths.iter().cloned());
        }
    }
    let report = build_decompile_report_with_error_metadata(
        binary_path,
        entry,
        sub_args.all_functions,
        sub_args.strict,
        target,
        binary_metadata,
        decompile_result,
    );
    let checked_certificate_loader =
        match load_convert_checked_certificate_loader_report_with_production_export(
            &checked_certificate_artifacts,
            &checked_certificate_manifests,
            None,
            checked_at_unix_ms,
            checked_certificate_production.map(|production| production.report),
        ) {
            Ok(report) => report,
            Err(error) => {
                if matches!(sub_args.format, OutputFormat::Json) {
                    convert_checked_certificate_loader_failure_report(
                        &checked_certificate_artifacts,
                        &checked_certificate_manifests,
                        error,
                    )
                } else {
                    emit_cli_diagnostic(
                        sub_args.format,
                        "decompile",
                        "checked_certificate_loader_failed",
                        &format!(
                            "failed to load checked certificate artifact or manifest: {error}"
                        ),
                        2,
                    );
                    return ExitCode::from(2);
                }
            }
        };
    let checked_certificate_loader_failed = checked_certificate_loader.status == "load_failed";
    let artifact_gate =
        build_convert_cli_gate_with_loader(&report, checked_certificate_loader.clone());
    let checked_certificate_release_gate_failed = report.output_trust_level == "proof_grade"
        && artifact_gate.checked_certificate_evidence.required
        && !artifact_gate.checked_certificate_evidence.proof_grade_release_accepted;
    let release_transcript_artifact_failed =
        write_requested_proof_grade_release_transcript_artifact(
            sub_args.format,
            "decompile",
            sub_args.proof_grade_release_transcript_out.as_deref(),
            &artifact_gate.checked_certificate_evidence.proof_grade_release_transcript_rows,
        );

    match sub_args.format {
        OutputFormat::Json => match serialize_decompile_json_with_checked_certificate_loader(
            &report,
            checked_certificate_loader,
        ) {
            Ok(json) => println!("{json}"),
            Err(error) => {
                eprintln!("targo trust: failed to serialize decompile report: {error}");
                return ExitCode::from(2);
            }
        },
        OutputFormat::Terminal => {
            print!(
                "{}",
                render_decompile_terminal_with_command_and_loader(
                    "decompile",
                    &report,
                    Some(checked_certificate_loader.clone()),
                )
            );
        }
        OutputFormat::Html => unreachable!("decompile rejects HTML before lifting"),
    }

    if checked_certificate_loader_failed {
        ExitCode::from(2)
    } else if release_transcript_artifact_failed
        || checked_certificate_release_gate_failed
        || decompile_should_fail(&report)
    {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

fn run_convert_subcommand(args: &[String]) -> ExitCode {
    if args.iter().any(|arg| arg == "--help" || arg == "-h") {
        print!("{}", convert_usage_text());
        return ExitCode::SUCCESS;
    }

    let sub_args = match parse_subcommand_args(args) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("targo trust: {e}");
            return ExitCode::from(2);
        }
    };
    if let Some(error) = checked_certificate_checker_configuration_error(&sub_args) {
        eprintln!("targo trust convert: {error}");
        return ExitCode::from(2);
    }

    if matches!(sub_args.format, OutputFormat::Html) {
        eprintln!("targo trust: convert does not support --format html yet; use terminal or json");
        return ExitCode::from(2);
    }

    if sub_args.entry.is_some() && sub_args.all_functions {
        eprintln!("targo trust: convert accepts either --entry or --all, not both");
        return ExitCode::from(2);
    }

    let target = match parse_convert_target(sub_args.to_ref.as_deref()) {
        Ok(target) => target,
        Err(e) => {
            eprintln!("targo trust: {e}");
            return ExitCode::from(2);
        }
    };

    let binary = match binary_subcommand_arg(&sub_args, "convert") {
        Ok(binary) => binary,
        Err(e) => {
            eprintln!("targo trust: {e}");
            return ExitCode::from(2);
        }
    };

    let entry = match parse_lift_entry(sub_args.entry.as_deref()) {
        Ok(entry) => entry,
        Err(e) => {
            eprintln!("targo trust: {e}");
            return ExitCode::from(2);
        }
    };

    let binary_path = Path::new(binary);
    let bytes = match read_binary_artifact(binary_path) {
        Ok(bytes) => bytes,
        Err(error) => {
            eprintln!("targo trust: failed to read {}: {error}", binary_path.display());
            return ExitCode::from(2);
        }
    };

    let options =
        DecompileOptions::with_lift(lift_options(entry, sub_args.all_functions, sub_args.strict))
            .with_outputs([decompile_output_kind(target, sub_args.format)]);
    let binary_metadata = sniff_binary_metadata(&bytes);
    let decompile_result = decompile_binary(&bytes, options);
    let checked_at_unix_ms = current_unix_ms();
    let checked_certificate_production = decompile_result.as_ref().ok().and_then(|artifact| {
        sub_args.checked_certificate_export_dir.as_deref().map(|export_dir| {
            produce_convert_checked_certificate_artifacts_for_decompilation(
                artifact,
                Path::new(export_dir),
                sub_args.checked_certificate_checker.as_deref().map(Path::new),
                checked_at_unix_ms,
            )
        })
    });
    let mut checked_certificate_artifacts = sub_args.checked_certificate_artifacts.clone();
    let mut checked_certificate_manifests = sub_args.checked_certificate_manifests.clone();
    if let Some(production) = &checked_certificate_production {
        if let Some(manifest_path) = production.report.manifest_path.clone() {
            checked_certificate_manifests.push(manifest_path);
        } else {
            checked_certificate_artifacts.extend(production.artifact_paths.iter().cloned());
        }
    }
    let report = build_decompile_report_with_error_metadata(
        binary_path,
        entry,
        sub_args.all_functions,
        sub_args.strict,
        target,
        binary_metadata,
        decompile_result,
    );
    let checked_certificate_loader =
        match load_convert_checked_certificate_loader_report_with_production_export(
            &checked_certificate_artifacts,
            &checked_certificate_manifests,
            None,
            checked_at_unix_ms,
            checked_certificate_production.map(|production| production.report),
        ) {
            Ok(report) => report,
            Err(error) => {
                if matches!(sub_args.format, OutputFormat::Json) {
                    convert_checked_certificate_loader_failure_report(
                        &checked_certificate_artifacts,
                        &checked_certificate_manifests,
                        error,
                    )
                } else {
                    emit_cli_diagnostic(
                        sub_args.format,
                        "convert",
                        "checked_certificate_loader_failed",
                        &format!(
                            "failed to load checked certificate artifact or manifest: {error}"
                        ),
                        2,
                    );
                    return ExitCode::from(2);
                }
            }
        };
    let checked_certificate_loader_failed = checked_certificate_loader.status == "load_failed";
    let conversion_gate =
        build_convert_cli_gate_with_loader(&report, checked_certificate_loader.clone());
    let release_transcript_artifact_failed =
        write_requested_proof_grade_release_transcript_artifact(
            sub_args.format,
            "convert",
            sub_args.proof_grade_release_transcript_out.as_deref(),
            &conversion_gate.checked_certificate_evidence.proof_grade_release_transcript_rows,
        );

    match sub_args.format {
        OutputFormat::Json => match serialize_convert_json_with_checked_certificate_loader(
            &report,
            checked_certificate_loader,
        ) {
            Ok(json) => println!("{json}"),
            Err(error) => {
                eprintln!("targo trust: failed to serialize convert report: {error}");
                return ExitCode::from(2);
            }
        },
        OutputFormat::Terminal => {
            print!(
                "{}",
                render_convert_terminal_with_checked_certificate_loader(
                    &report,
                    checked_certificate_loader,
                )
            );
        }
        OutputFormat::Html => unreachable!("convert rejects HTML before lifting"),
    }

    if checked_certificate_loader_failed {
        ExitCode::from(2)
    } else if release_transcript_artifact_failed || !conversion_gate.accepted {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

fn run_exploit_find_subcommand(args: &[String]) -> ExitCode {
    if args.iter().any(|arg| arg == "--help" || arg == "-h") {
        print!("{}", exploit_find_usage_text());
        return ExitCode::SUCCESS;
    }

    let parsed = match parse_exploit_find_args(args) {
        Ok(parsed) => parsed,
        Err(error) => {
            eprintln!("targo trust: {error}");
            return ExitCode::from(2);
        }
    };

    if matches!(parsed.format, OutputFormat::Html) {
        eprintln!(
            "targo trust: exploit-find does not support --format html yet; use terminal or json"
        );
        return ExitCode::from(2);
    }

    if parsed.entry.is_some() && parsed.all_functions {
        eprintln!("targo trust: exploit-find accepts either --entry or --all, not both");
        return ExitCode::from(2);
    }

    let entry = match parse_lift_entry(parsed.entry.as_deref()) {
        Ok(entry) => entry,
        Err(error) => {
            eprintln!("targo trust: {error}");
            return ExitCode::from(2);
        }
    };

    let binary_path = Path::new(&parsed.input);
    let bytes = match read_binary_artifact(binary_path) {
        Ok(bytes) => bytes,
        Err(error) => {
            eprintln!("targo trust: failed to read {}: {error}", binary_path.display());
            return ExitCode::from(2);
        }
    };

    let options = lift_options(entry, parsed.all_functions, parsed.strict);
    let output = verify_binary_report_input_from_result_with_path(
        lift_binary_to_trust_ir(&bytes, options),
        Some(binary_path),
    );
    let binary_report =
        build_verify_binary_report(binary_path, entry, parsed.all_functions, parsed.strict, output);
    let report = build_exploit_find_report(parsed.target, binary_report);

    match parsed.format {
        OutputFormat::Json => match serialize_exploit_find_json(&report) {
            Ok(json) => println!("{json}"),
            Err(error) => {
                eprintln!("targo trust: failed to serialize exploit-find report: {error}");
                return ExitCode::from(2);
            }
        },
        OutputFormat::Terminal => {
            print!("{}", render_exploit_find_terminal(&report));
        }
        OutputFormat::Html => unreachable!("exploit-find rejects HTML before reporting"),
    }

    if exploit_find_should_fail(&report) { ExitCode::FAILURE } else { ExitCode::SUCCESS }
}

fn lift_binary_arg(sub_args: &SubcommandArgs) -> anyhow::Result<&str> {
    binary_subcommand_arg(sub_args, "lift")
}

fn binary_subcommand_arg<'a>(
    sub_args: &'a SubcommandArgs,
    command: &str,
) -> anyhow::Result<&'a str> {
    match sub_args.passthrough.as_slice() {
        [] => anyhow::bail!("{command} requires a binary path"),
        [binary] if binary.starts_with('-') => {
            anyhow::bail!("unexpected {command} option `{binary}`")
        }
        [binary] => Ok(binary),
        _ => anyhow::bail!("{command} accepts exactly one binary path"),
    }
}

/// Read one caller-selected binary as a stable, regular-file snapshot. Binary
/// lifting and verification retain the whole selected image, so the bound is
/// necessarily larger than metadata limits; it is still finite and is checked
/// before allocation as well as while the file is read.
fn read_binary_artifact(path: &Path) -> std::io::Result<Vec<u8>> {
    input_limits::read_bounded_file(path, input_limits::MAX_BINARY_ARTIFACT_BYTES)
}

fn checked_certificate_checker_configuration_error(sub_args: &SubcommandArgs) -> Option<String> {
    if sub_args.checked_certificate_checker.is_some()
        && sub_args.checked_certificate_export_dir.is_none()
    {
        Some(
            "--checked-cert-checker requires --checked-cert-export-dir; imported certificate rows do not carry authenticated concrete proof metadata/payload inputs for a new checker invocation"
                .to_string(),
        )
    } else {
        None
    }
}

fn lift_usage_text() -> &'static str {
    "targo trust lift: lift binary code into TrustIr\n\
\n\
Usage:\n\
  targo trust lift <binary> [--entry <addr>] [--all] [--json] [--strict|--allow-unsupported]\n\
\n\
Options:\n\
  --entry <addr>       Lift the function containing addr (decimal or 0x-prefixed hex)\n\
  --all                Lift all detected function symbols\n\
  --json               Emit JSON output\n\
  --strict             Fail when unsupported code is encountered (default)\n\
  --allow-unsupported  Permit partial lift coverage\n\
\n\
Supported binaries: little-endian ELF x86-64/AArch64 and little-endian Mach-O AArch64. AArch64 currently supports conservative lift/decompile coverage, with proof-grade replay, checked certificates, exact provenance, source-backprop reconstruction, and target validation still gated. AArch32, i386/32-bit x86, Mach-O x86-64, PE/COFF, big-endian, and unknown binaries fail closed for lifting.\n"
}

fn verify_binary_usage_text() -> &'static str {
    "targo trust verify-binary: lift binary code and generate binary verification conditions\n\
\n\
Usage:\n\
  targo trust verify-binary <binary> [--entry <addr>] [--all] [--solver ay] [--checked-cert-artifact <path>] [--checked-cert-manifest <path>] [--json] [--strict|--allow-unsupported]\n\
\n\
Options:\n\
  --entry <addr>       Verify the function containing addr (decimal or 0x-prefixed hex)\n\
  --all                Verify all detected function symbols\n\
  --solver ay          Use the incremental ay binary VC route (default)\n\
  --checked-cert-artifact <path>\n\
                       Import a checked certificate artifact; may be repeated\n\
  --checked-cert-manifest <path>\n\
                       Import checked certificate artifacts listed by manifest; may be repeated\n\
  --checked-cert-export-dir <dir>\n\
                       Produce checked certificate artifacts from normalized proof exports\n\
  --checked-cert-checker <path>\n\
                       Run an authenticated, bounded external checker during export (requires --checked-cert-export-dir)\n\
  --json               Emit JSON output\n\
  --strict             Fail when unsupported binary coverage is encountered (default)\n\
  --allow-unsupported  Permit partial binary coverage\n\
\n\
Supported binaries: little-endian ELF x86-64/AArch64 and little-endian Mach-O AArch64. AArch64 currently supports conservative lift/decompile coverage, with proof-grade replay, checked certificates, exact provenance, source-backprop reconstruction, and target validation still gated. AArch32, i386/32-bit x86, Mach-O x86-64, PE/COFF, big-endian, and unknown binaries fail closed for lifting.\n\
\n\
Proof-grade gates are based on structured solver dispatch evidence; raw solver proof bytes alone do not satisfy checked-certificate coverage. JSON includes source_backpropagation_gate; verified binary evidence alone does not grant source backpropagation without accepted reconstruction/target validation evidence.\n"
}

fn decompile_usage_text() -> &'static str {
    "targo trust decompile: produce conservative decompilation artifacts from a binary\n\
\n\
Usage:\n\
  targo trust decompile <binary> --to trust_ir|rust|trust-cg|wasm [--entry <addr>] [--all] [--checked-cert-artifact <path>] [--checked-cert-manifest <path>] [--checked-cert-export-dir <dir>] [--checked-cert-checker <path>] [--proof-grade-release-transcript-out <path>] [--json] [--strict|--allow-unsupported]\n\
\n\
Options:\n\
  --to <target>        Output target: trust_ir, rust, trust-cg, or wasm\n\
  --entry <addr>       Decompile the function containing addr (decimal or 0x-prefixed hex)\n\
  --all                Decompile all detected function symbols\n\
  --checked-cert-artifact <path>\n\
                       Reference a checked proof-cert artifact in JSON readback evidence; may be repeated\n\
  --checked-cert-manifest <path>\n\
                       Reference checked proof-cert artifacts listed by manifest; may be repeated\n\
  --checked-cert-export-dir <dir>\n\
                       Produce checked certificate artifacts from normalized proof exports in the decompile artifact\n\
  --checked-cert-checker <path>\n\
                       Run an authenticated, bounded external checker during export (requires --checked-cert-export-dir)\n\
  --proof-grade-release-transcript-out <path>\n\
                       Write/read back a validated proof-grade release transcript artifact\n\
  --json               Emit JSON output\n\
  --strict             Fail when unsupported binary coverage is encountered (default)\n\
  --allow-unsupported  Permit partial binary coverage\n\
\n\
Supported binaries: little-endian ELF x86-64/AArch64 and little-endian Mach-O AArch64. AArch64 currently supports conservative lift/decompile coverage, with proof-grade replay, checked certificates, exact provenance, source-backprop reconstruction, and target validation still gated. AArch32, i386/32-bit x86, Mach-O x86-64, PE/COFF, big-endian, and unknown binaries fail closed for decompilation.\n\
\n\
Trust labels: trust_ir, trust-cg, and wasm text outputs are partial unless validated; rust output is exploratory/not validated. JSON artifact_gate.source_backpropagation_gate names exact provenance, proof-grade binary verification, and accepted reconstruction/target validation requirements.\n"
}

fn convert_usage_text() -> &'static str {
    "targo trust convert: convert binary-derived TrustIr into bounded output targets\n\
\n\
Usage:\n\
  targo trust convert <binary> --to trust_ir|rust|trust-cg|wasm [--entry <addr>] [--all] [--checked-cert-artifact <path>] [--checked-cert-manifest <path>] [--checked-cert-export-dir <dir>] [--checked-cert-checker <path>] [--proof-grade-release-transcript-out <path>] [--json] [--strict|--allow-unsupported]\n\
\n\
Options:\n\
  --to <target>        Output target: trust_ir, rust, trust-cg, or wasm\n\
  --entry <addr>       Convert the function containing addr (decimal or 0x-prefixed hex)\n\
  --all                Convert all detected function symbols\n\
  --checked-cert-artifact <path>\n\
                       Reference a checked proof-cert artifact in JSON readback evidence; may be repeated\n\
  --checked-cert-manifest <path>\n\
                       Reference checked proof-cert artifacts listed by manifest; may be repeated\n\
  --checked-cert-export-dir <dir>\n\
                       Produce checked certificate artifacts from normalized proof exports in the conversion artifact\n\
  --checked-cert-checker <path>\n\
                       Run an authenticated, bounded external checker during export (requires --checked-cert-export-dir)\n\
  --proof-grade-release-transcript-out <path>\n\
                       Write/read back a validated proof-grade release transcript artifact\n\
  --json               Emit JSON output\n\
  --strict             Fail when unsupported binary coverage is encountered (default)\n\
  --allow-unsupported  Permit partial binary coverage\n\
\n\
Supported binaries: little-endian ELF x86-64/AArch64 and little-endian Mach-O AArch64. AArch64 currently supports conservative lift/decompile coverage, with proof-grade replay, checked certificates, exact provenance, source-backprop reconstruction, and target validation still gated. AArch32, i386/32-bit x86, Mach-O x86-64, PE/COFF, big-endian, and unknown binaries fail closed for conversion.\n\
\n\
Trust labels: trust_ir, trust-cg, and wasm text outputs are partial unless validated; rust output is exploratory. trust-codegen/wasm outputs are rejected by the conversion gate unless proof-grade validation is available. JSON conversion_gate.source_backpropagation_gate and checked_certificate_readback.proof_grade_release_* fields keep source-backprop permission and checked-certificate release acceptance separate from partial binary evidence.\n"
}

fn exploit_find_usage_text() -> &'static str {
    "targo trust exploit-find: conservative binary exploit-finding pipeline\n\
\n\
Usage:\n\
  targo trust exploit-find <input> --target compiler|verifier|lifter [--entry <addr>] [--all] [--json] [--strict|--allow-unsupported]\n\
\n\
Options:\n\
  --target <target>    Target under test: compiler, verifier, or lifter\n\
  --entry <addr>       Analyze the function containing addr (decimal or 0x-prefixed hex)\n\
  --all                Analyze all detected function symbols\n\
  --json               Emit JSON output\n\
  --format <fmt>       Output format: terminal (default) or json; html is rejected\n\
  --strict             Fail when unsupported binary coverage is encountered (default)\n\
  --allow-unsupported  Permit partial binary coverage, but exploit-find still fails closed\n\
\n\
This command runs binary lift/VC generation when possible and emits phase diagnostics for\n\
claim capture, replay, independent refutation, reduction, attribution, and regression emission.\n\
Raw solver failed/SAT output is only an unconfirmed candidate and is never reported as a confirmed exploit.\n"
}

fn parse_lift_entry(entry: Option<&str>) -> anyhow::Result<Option<u64>> {
    let Some(entry) = entry else {
        return Ok(None);
    };
    if entry.is_empty() {
        anyhow::bail!("--entry requires an address");
    }
    let parsed = if let Some(hex) = entry.strip_prefix("0x").or_else(|| entry.strip_prefix("0X")) {
        u64::from_str_radix(hex, 16)
            .with_context(|| format!("--entry must be a valid address: `{entry}`"))?
    } else {
        entry
            .parse::<u64>()
            .with_context(|| format!("--entry must be a valid address: `{entry}`"))?
    };
    Ok(Some(parsed))
}

fn lift_options(entry: Option<u64>, all_functions: bool, strict: bool) -> BinaryLiftOptions {
    let functions = match entry {
        Some(entry) => BinaryFunctionSelection::Addresses(vec![entry]),
        None if all_functions => BinaryFunctionSelection::All,
        None => BinaryFunctionSelection::Entry,
    };
    BinaryLiftOptions { functions, strict }
}

fn parse_decompile_target(target: Option<&str>) -> anyhow::Result<DecompileTarget> {
    let Some(target) = target else {
        anyhow::bail!("decompile requires --to trust_ir, rust, trust-cg, or wasm");
    };
    DecompileTarget::from_convert_str(target)
}

fn parse_convert_target(target: Option<&str>) -> anyhow::Result<DecompileTarget> {
    let Some(target) = target else {
        anyhow::bail!("convert requires --to trust_ir, rust, trust-cg, or wasm");
    };
    DecompileTarget::from_convert_str(target)
}

fn parse_exploit_find_args(args: &[String]) -> anyhow::Result<ExploitFindArgs> {
    let mut format = OutputFormat::Terminal;
    let mut input: Option<String> = None;
    let mut target: Option<ExploitFindTarget> = None;
    let mut entry: Option<String> = None;
    let mut all_functions = false;
    let mut strict = true;
    let mut i = 0;

    while i < args.len() {
        match args[i].as_str() {
            "--json" => {
                format = OutputFormat::Json;
            }
            "--format" => {
                i += 1;
                let value =
                    args.get(i).context("--format requires a value (terminal, json, html)")?;
                format = OutputFormat::from_str(value)?;
            }
            s if s.starts_with("--format=") => {
                let value = s.strip_prefix("--format=").expect("invariant: prefix checked");
                format = OutputFormat::from_str(value)?;
            }
            "--target" => {
                i += 1;
                let value =
                    args.get(i).context("--target requires compiler, verifier, or lifter")?;
                target = Some(ExploitFindTarget::from_str(value)?);
            }
            s if s.starts_with("--target=") => {
                let value = s.strip_prefix("--target=").expect("invariant: prefix checked");
                target = Some(ExploitFindTarget::from_str(value)?);
            }
            "--entry" => {
                i += 1;
                let value = args.get(i).context("--entry requires an address")?;
                entry = Some(value.clone());
            }
            s if s.starts_with("--entry=") => {
                let value = s.strip_prefix("--entry=").expect("invariant: prefix checked");
                entry = Some(value.to_string());
            }
            "--all" => {
                all_functions = true;
            }
            "--strict" => {
                strict = true;
            }
            "--allow-unsupported" => {
                strict = false;
            }
            option if option.starts_with('-') => {
                anyhow::bail!("unexpected exploit-find option `{option}`");
            }
            value => {
                if input.is_some() {
                    anyhow::bail!("exploit-find accepts exactly one input");
                }
                input = Some(value.to_string());
            }
        }
        i += 1;
    }

    let input = input.context("exploit-find requires an input path")?;
    let target = target.context("exploit-find requires --target compiler, verifier, or lifter")?;

    Ok(ExploitFindArgs { format, input, target, entry, all_functions, strict })
}

fn decompile_output_kind(target: DecompileTarget, format: OutputFormat) -> DecompileOutputKind {
    match target {
        DecompileTarget::TrustIr => {
            if matches!(format, OutputFormat::Json) {
                DecompileOutputKind::TrustIrJson
            } else {
                DecompileOutputKind::TrustIrText
            }
        }
        DecompileTarget::Rust => DecompileOutputKind::RustSkeleton,
        DecompileTarget::TrustCg => DecompileOutputKind::TrustCgText,
        DecompileTarget::Wasm => DecompileOutputKind::WasmText,
    }
}

fn lift_report_input_from_result(result: Result<LiftedBinary, LiftError>) -> LiftReportInput {
    match result {
        Ok(binary) => lift_report_input_from_binary(binary),
        Err(error) => {
            let message = error.to_string();
            if is_unsupported_lift_error(&error) {
                LiftReportInput {
                    format: None,
                    architecture: None,
                    binary_entry: None,
                    functions: Vec::new(),
                    unsupported: vec![message],
                    failures: Vec::new(),
                }
            } else {
                LiftReportInput {
                    format: None,
                    architecture: None,
                    binary_entry: None,
                    functions: Vec::new(),
                    unsupported: Vec::new(),
                    failures: vec![message],
                }
            }
        }
    }
}

fn lift_report_input_from_binary(binary: LiftedBinary) -> LiftReportInput {
    let format = Some(binary.format.to_string());
    let architecture = Some(binary.architecture.to_string());
    let binary_entry = binary.entry_point;
    let functions = binary
        .functions
        .into_iter()
        .map(|function| {
            let blocks = function.trust_ir_body.blocks.len();
            let statements =
                function.trust_ir_body.blocks.iter().map(|block| block.stmts.len()).sum();
            let vcs = generate_binary_vcs(&function).len();
            LiftedTrustIrFunctionSummary {
                instruction_provenance: instruction_provenance_for_lifted_function(&function),
                name: function.name,
                entry: Some(function.entry_point),
                blocks,
                statements,
                vcs,
            }
        })
        .collect::<Vec<_>>();
    let unsupported = binary
        .failures
        .into_iter()
        .map(|failure| {
            let entry = hex_addr(failure.entry_point);
            match failure.name {
                Some(name) => format!("{name} @ {entry}: {}", failure.error),
                None => format!("{entry}: {}", failure.error),
            }
        })
        .collect();

    LiftReportInput {
        format,
        architecture,
        binary_entry,
        functions,
        unsupported,
        failures: Vec::new(),
    }
}

#[cfg(test)]
fn verify_binary_report_input_from_result(
    result: Result<LiftedBinary, LiftError>,
) -> VerifyBinaryReportInput {
    verify_binary_report_input_from_result_with_route(result, BinarySolverRoute::AYIncremental)
}

fn verify_binary_report_input_from_result_with_path(
    result: Result<LiftedBinary, LiftError>,
    binary_path: Option<&Path>,
) -> VerifyBinaryReportInput {
    verify_binary_report_input_from_result_with_route_and_path(
        result,
        BinarySolverRoute::AYIncremental,
        binary_path,
        None,
    )
}

#[cfg(test)]
fn verify_binary_report_input_from_result_with_route(
    result: Result<LiftedBinary, LiftError>,
    solver_route: BinarySolverRoute,
) -> VerifyBinaryReportInput {
    verify_binary_report_input_from_result_with_route_and_path(result, solver_route, None, None)
}

fn verify_binary_report_input_from_result_with_route_and_path(
    result: Result<LiftedBinary, LiftError>,
    solver_route: BinarySolverRoute,
    binary_path: Option<&Path>,
    selected_image_bytes: Option<&[u8]>,
) -> VerifyBinaryReportInput {
    verify_binary_report_input_from_result_with_route_path_and_digest_identity(
        result,
        solver_route,
        binary_path,
        selected_image_bytes,
        None,
    )
}

fn verify_binary_report_input_from_result_with_route_path_and_digest_identity(
    result: Result<LiftedBinary, LiftError>,
    solver_route: BinarySolverRoute,
    binary_path: Option<&Path>,
    selected_image_bytes: Option<&[u8]>,
    binary_artifact_digest_identity: Option<BinaryArtifactDigestIdentity>,
) -> VerifyBinaryReportInput {
    match result {
        Ok(binary) => verify_binary_report_input_from_binary(
            binary,
            solver_route,
            binary_path,
            selected_image_bytes,
            binary_artifact_digest_identity,
        ),
        Err(error) => {
            let message = error.to_string();
            if is_unsupported_lift_error(&error) {
                VerifyBinaryReportInput {
                    format: None,
                    architecture: None,
                    binary_entry: None,
                    functions: Vec::new(),
                    solver_results: Vec::new(),
                    proof_evidence: VerifyBinaryEvidence::default(),
                    unsupported: vec![message],
                    failures: Vec::new(),
                }
            } else {
                VerifyBinaryReportInput {
                    format: None,
                    architecture: None,
                    binary_entry: None,
                    functions: Vec::new(),
                    solver_results: Vec::new(),
                    proof_evidence: VerifyBinaryEvidence::default(),
                    unsupported: Vec::new(),
                    failures: vec![message],
                }
            }
        }
    }
}

fn verify_binary_report_input_from_binary(
    binary: LiftedBinary,
    solver_route: BinarySolverRoute,
    binary_path: Option<&Path>,
    selected_image_bytes: Option<&[u8]>,
    binary_artifact_digest_identity: Option<BinaryArtifactDigestIdentity>,
) -> VerifyBinaryReportInput {
    let format = Some(binary.format.to_string());
    let architecture = Some(binary.architecture.to_string());
    let binary_entry = binary.entry_point;
    let router = binary_vc_router(solver_route);
    let replay_context = BinaryReplayContext::from_lifted_binary(&binary, selected_image_bytes);
    let model_assumptions = binary.memory_model.assumptions.clone();
    let mut solver_results = Vec::new();
    let mut proof_evidence = VerifyBinaryEvidence::default();
    let functions = binary
        .functions
        .into_iter()
        .map(|function| {
            let blocks = function.trust_ir_body.blocks.len();
            let statements =
                function.trust_ir_body.blocks.iter().map(|block| block.stmts.len()).sum();
            let vcs = generate_binary_vcs(&function);
            let vc_counts = count_vc_kinds(vcs.iter().map(|vc| &vc.kind));
            proof_evidence.add_required_vcs(vcs.len());
            let (reports, dispatch_records) = dispatch_binary_vcs_with_replay_evidence(
                &router,
                solver_route,
                binary_path,
                &function,
                replay_context.as_ref(),
                &vcs,
            );
            let mut dispatch_records = dispatch_records;
            bind_binary_dispatch_context(
                &mut dispatch_records,
                binary_artifact_digest_identity.as_ref(),
                &model_assumptions,
            );
            solver_results.extend(reports);
            proof_evidence.extend_solver_dispatch(dispatch_records);
            VerifiedBinaryFunctionSummary {
                name: function.name,
                entry: Some(function.entry_point),
                blocks,
                statements,
                vcs: vcs.len(),
                vc_counts,
            }
        })
        .collect::<Vec<_>>();
    let unsupported = binary
        .failures
        .into_iter()
        .map(|failure| {
            let entry = hex_addr(failure.entry_point);
            match failure.name {
                Some(name) => format!("{name} @ {entry}: {}", failure.error),
                None => format!("{entry}: {}", failure.error),
            }
        })
        .collect();

    VerifyBinaryReportInput {
        format,
        architecture,
        binary_entry,
        functions,
        solver_results,
        proof_evidence,
        unsupported,
        failures: Vec::new(),
    }
}

fn binary_artifact_digest_identity_from_parser(
    bytes: &[u8],
) -> Option<BinaryArtifactDigestIdentity> {
    let parsed = trust_binary_parse::parse_binary_with_identity(bytes).ok()?;
    Some(BinaryArtifactDigestIdentity {
        root_artifact_digest: Some(BinaryArtifactDigest {
            algorithm: parsed.identity.artifact.algorithm,
            value: parsed.identity.artifact.value,
        }),
        selected_image: Some(BinarySelectedImageIdentity {
            file_offset: parsed.identity.selected_image.file_offset,
            file_size: parsed.identity.selected_image.file_size,
            sha256: parsed.identity.selected_image.sha256,
        }),
    })
}

fn bind_binary_dispatch_context(
    dispatch_records: &mut [SolverDispatchRecord],
    binary_artifact_digest_identity: Option<&BinaryArtifactDigestIdentity>,
    model_assumptions: &[trust_types::ModelAssumption],
) {
    for dispatch in dispatch_records {
        if dispatch.binary_artifact_digest_identity.is_none() {
            dispatch.binary_artifact_digest_identity = binary_artifact_digest_identity.cloned();
        }
        if dispatch.assumptions.is_empty() {
            dispatch.assumptions = model_assumptions.to_vec();
        }
    }
}

/// Trust (2026-06-17 OOM cause #1+#2): the per-job solver memory ceiling, in MB,
/// for the production verification router.
///
/// Resolution order:
/// 1. An internal, explicit caller value (used by focused tests).
/// 2. Otherwise DERIVE a sane ceiling from total RAM: the aggregate
///    `memory_jobserver` machine budget (70% phys RAM) divided by the expected
///    number of concurrent jobs, so N workers' ceilings sum to ~the budget. This
///    default is never `unbounded`.
///
/// The returned ceiling is BOTH propagated into each spawned `ay` as
/// `--memory <mb>` (the per-process safety net) AND used as the reservation size
/// taken from the cross-process token bucket.
fn per_job_solver_memory_ceiling_mb(explicit_limit: Option<u64>) -> u64 {
    // Internal callers may supply an explicit ceiling, including 0 (unbounded).
    // Production verify-binary dispatch passes None and derives a bounded
    // value; ambient environment is not a second, unreported policy plane.
    if let Some(mb) = explicit_limit {
        return mb;
    }
    // Derive from total RAM via the jobserver budget.
    let budget_bytes = trust_router::memory_jobserver::machine_budget_bytes();
    if budget_bytes == 0 {
        // Total RAM undetectable: fall back to a conservative fixed ceiling
        // rather than leaving the solver unbounded.
        return DEFAULT_DERIVED_PER_JOB_CEILING_MB;
    }
    // Expected concurrent jobs ~= the parallelism cargo fans out (one trustc per
    // crate). We do not know it precisely here, so use a conservative divisor so
    // the per-job ceilings sum to roughly the budget under heavy fan-out while a
    // single solve still gets ample headroom. Floor at 1 GB so a legitimate
    // large solve is never throttled below a usable ceiling.
    let budget_mb = budget_bytes / (1024 * 1024);
    (budget_mb / EXPECTED_CONCURRENT_JOBS).max(1024)
}

/// Conservative estimate of concurrent verification workers cargo fans out
/// (~14 in the 2026-06-17 incident). Used only to divide the RAM budget into a
/// per-job ceiling when no runtime override is set.
const EXPECTED_CONCURRENT_JOBS: u64 = 14;

/// Fixed per-job ceiling (MB) used only when total RAM cannot be detected, so the
/// spawned solver is never left fully unbounded.
const DEFAULT_DERIVED_PER_JOB_CEILING_MB: u64 = 2048;

fn binary_vc_router(solver_route: BinarySolverRoute) -> Router {
    binary_vc_router_with_memory_limit(solver_route, None)
}

/// Construct the production binary-verification router with the per-job solver
/// memory ceiling threaded through.
///
/// `explicit_limit` is an internal override (`None` derives from RAM). The ceiling is wired
/// into BOTH:
///   * the `IncrementalAYSession` (`with_memory_limit_mb`), which propagates
///     `--memory <mb>` to every spawned `ay` and sizes the cross-process
///     reservation; and
///   * the `Router`'s `MemoryGuard` (`with_memory_guard`), so the per-process
///     RSS backstop is runtime-override/RAM-derived rather than the hardcoded default.
fn binary_vc_router_with_memory_limit(
    solver_route: BinarySolverRoute,
    explicit_limit: Option<u64>,
) -> Router {
    let ceiling_mb = per_job_solver_memory_ceiling_mb(explicit_limit);
    match solver_route {
        BinarySolverRoute::AYIncremental => {
            let session = IncrementalAYSession::new().with_memory_limit_mb(ceiling_mb);
            Router::with_backends(vec![Box::new(session)])
                .with_memory_guard(MemoryGuard::new(ceiling_mb))
        }
    }
}

fn dispatch_binary_vcs_with_replay_evidence(
    router: &Router,
    solver_route: BinarySolverRoute,
    binary_path: Option<&Path>,
    function: &trust_lift::LiftedFunction,
    replay_context: Option<&BinaryReplayContext>,
    vcs: &[VerificationCondition],
) -> (Vec<BinarySolverResultReport>, Vec<SolverDispatchRecord>) {
    let mut reports = Vec::with_capacity(vcs.len());
    let mut dispatch_records = Vec::with_capacity(vcs.len());

    // Trust: S2 stage (C) — engage the ay shared-prefix incremental batch.
    //
    // This lane's router is the sole-backend `IncrementalAYSession` shape
    // (`binary_vc_router`), so `Router::verify_all` routes the whole
    // function's VC set through the session's `verify_batch`: the function's
    // common assertion prefix is asserted ONCE at the solver's base scope and
    // each obligation is decided as a small push/pop delta (M·N → M+N assert
    // work). `verify_batch` is verdict-identical to per-VC dispatch by
    // construction — it returns one result per input VC IN INPUT ORDER, pairs
    // it with the ORIGINAL pre-conjoined VC, solves relaxable-nonlinear VCs on
    // the verbatim per-VC path over an empty base scope, and re-solves the
    // FULL formula out-of-process on any session fault (a shared fact is never
    // silently dropped). The report/dispatch records below keep reading the
    // ORIGINAL `vcs` slice, so every downstream artifact (SerializableVc,
    // replay attestation, cache keys) sees the full prefix∧obligation formula,
    // unchanged. The optimized path is canonical; A/B controls belong in tests,
    // not in an ambient production kill switch.
    let batched = router.verify_all(vcs);
    let results: Vec<trust_types::VerificationResult> = if batched.len() == vcs.len() {
        batched.into_iter().map(|(_, result)| result).collect()
    } else {
        // Defensive fail-closed: `verify_all` contractually returns one result
        // per input; on any violation re-dispatch per-VC rather than truncating
        // (a truncated zip would silently DROP obligations from the report).
        vcs.iter().map(|vc| router.verify_one(vc)).collect()
    };

    for ((index, vc), result) in vcs.iter().enumerate().zip(results) {
        let report = binary_solver_result_report_with_replay(
            &function.name,
            vc_kind_key(&vc.kind),
            format_solver_location(&vc.location),
            &result,
            Some(BinaryReplayAttempt { function, vc, context: replay_context }),
        );
        let replay = replay_status_for_solver_report(&report);
        let replay_diagnostics = exact_replay_slice_attestation_diagnostics_for_solver_result(
            &result,
            replay,
            function,
            vc,
            replay_context,
        );
        reports.push(report);
        dispatch_records.push(binary_solver_dispatch_record(BinarySolverDispatchRecordInput {
            solver_route,
            binary_path,
            function,
            index,
            vc,
            result,
            replay,
            diagnostics: replay_diagnostics,
        }));
    }

    (reports, dispatch_records)
}

struct BinarySolverDispatchRecordInput<'a> {
    solver_route: BinarySolverRoute,
    binary_path: Option<&'a Path>,
    function: &'a trust_lift::LiftedFunction,
    index: usize,
    vc: &'a VerificationCondition,
    result: trust_types::VerificationResult,
    replay: ReplayStatus,
    diagnostics: Vec<String>,
}

fn binary_solver_dispatch_record(
    input: BinarySolverDispatchRecordInput<'_>,
) -> SolverDispatchRecord {
    let BinarySolverDispatchRecordInput {
        solver_route,
        binary_path,
        function,
        index,
        vc,
        result,
        replay,
        diagnostics,
    } = input;

    let status = binary_solver_dispatch_status(&result);
    let certificate = binary_proof_certificate_status(&result);
    let elapsed_ms = Some(result.time_ms());
    SolverDispatchRecord {
        id: format!("{}:{:#x}:{index}", function.name, function.entry_point),
        function: Some(function.name.clone()),
        origin: Some(binary_dispatch_origin(binary_path, function, vc)),
        vc_kind: Some(vc.kind.clone()),
        vc: Some(SerializableVc::from_vc(vc)),
        solver: result.solver_name().to_string(),
        backend: Some(solver_route.backend_label().to_string()),
        status,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        result: Some(result),
        elapsed_ms,
        replay,
        certificate,
        diagnostics,
        ..Default::default()
    }
}

fn binary_dispatch_origin(
    binary_path: Option<&Path>,
    function: &trust_lift::LiftedFunction,
    vc: &VerificationCondition,
) -> BinaryOrigin {
    let instruction_address = vc.location.binary_address_value().unwrap_or(function.entry_point);
    let binary_path = binary_path.map(|path| path.display().to_string());
    let annotation = function
        .annotations
        .iter()
        .find(|annotation| annotation.binary_offset == instruction_address);

    if let Some(origin) = function
        .memory_accesses
        .iter()
        .map(|access| &access.origin)
        .find(|origin| origin.instruction_address == instruction_address)
    {
        return binary_origin_with_dispatch_context(
            origin.clone(),
            binary_path,
            function.entry_point,
            &vc.location,
            annotation,
        );
    }

    if let Some(annotation) = annotation {
        return BinaryOrigin {
            binary_path,
            function_entry: Some(function.entry_point),
            instruction_address,
            instruction_size: Some(annotation.instruction_size),
            encoding: Some(annotation.encoding),
            instruction_bytes: exact_annotation_instruction_bytes(annotation)
                .unwrap_or_default()
                .to_vec(),
            source: Some(vc.location.clone()),
        };
    }

    BinaryOrigin {
        binary_path,
        function_entry: Some(function.entry_point),
        instruction_address,
        instruction_size: None,
        encoding: None,
        instruction_bytes: Vec::new(),
        source: Some(vc.location.clone()),
    }
}

fn instruction_provenance_for_lifted_function(
    function: &trust_lift::LiftedFunction,
) -> Vec<BinaryOrigin> {
    function
        .annotations
        .iter()
        .map(|annotation| BinaryOrigin {
            binary_path: None,
            function_entry: Some(function.entry_point),
            instruction_address: annotation.binary_offset,
            instruction_size: Some(annotation.instruction_size),
            encoding: Some(annotation.encoding),
            instruction_bytes: exact_annotation_instruction_bytes(annotation)
                .unwrap_or_default()
                .to_vec(),
            source: Some(SourceSpan::binary_address(annotation.binary_offset)),
        })
        .collect()
}

fn binary_origin_with_dispatch_context(
    mut origin: BinaryOrigin,
    binary_path: Option<String>,
    function_entry: u64,
    source: &SourceSpan,
    annotation: Option<&trust_lift::cfg::ProofAnnotation>,
) -> BinaryOrigin {
    if origin.binary_path.is_none() {
        origin.binary_path = binary_path;
    }
    if origin.function_entry.is_none() {
        origin.function_entry = Some(function_entry);
    }
    if origin.source.is_none() {
        origin.source = Some(source.clone());
    }
    if !origin.instruction_bytes.is_empty() && exact_origin_instruction_bytes(&origin).is_none() {
        origin.instruction_bytes.clear();
    }
    if origin.instruction_bytes.is_empty() {
        if let Some(annotation) = annotation {
            if let Some(bytes) = exact_annotation_instruction_bytes(annotation) {
                origin.instruction_bytes = bytes.to_vec();
                origin.instruction_size = Some(annotation.instruction_size);
                origin.encoding = Some(annotation.encoding);
            }
        }
    }
    if origin.instruction_size.is_none() {
        origin.instruction_size = annotation.map(|annotation| annotation.instruction_size);
    }
    if origin.encoding.is_none() {
        origin.encoding = annotation.map(|annotation| annotation.encoding);
    }
    origin
}

fn exact_origin_instruction_bytes(origin: &BinaryOrigin) -> Option<&[u8]> {
    if origin.instruction_bytes.is_empty()
        || origin
            .instruction_size
            .is_some_and(|size| usize::from(size) != origin.instruction_bytes.len())
    {
        None
    } else {
        Some(&origin.instruction_bytes)
    }
}

fn exact_annotation_instruction_bytes(
    annotation: &trust_lift::cfg::ProofAnnotation,
) -> Option<&[u8]> {
    if annotation.instruction_bytes.is_empty()
        || usize::from(annotation.instruction_size) != annotation.instruction_bytes.len()
    {
        None
    } else {
        Some(&annotation.instruction_bytes)
    }
}

fn replay_status_for_solver_report(report: &BinarySolverResultReport) -> ReplayStatus {
    match report.replay_status.as_deref() {
        Some("replayed") => ReplayStatus::Replayed,
        Some("spurious") => ReplayStatus::Spurious,
        Some("failed") => ReplayStatus::Failed,
        _ => ReplayStatus::NotAttempted,
    }
}

fn exact_replay_slice_attestation_diagnostics_for_solver_result(
    result: &trust_types::VerificationResult,
    replay: ReplayStatus,
    function: &trust_lift::LiftedFunction,
    vc: &VerificationCondition,
    replay_context: Option<&BinaryReplayContext>,
) -> Vec<String> {
    if replay != ReplayStatus::Replayed {
        return Vec::new();
    }

    let Some(context) = replay_context else {
        return vec![exact_replay_slice_attestation_rejected_diagnostic([
            "exact replay selected-image byte/segment attestation was not run",
        ])];
    };
    let Some(trace_addresses) = result_counterexample_trace_addresses(result) else {
        return vec![exact_replay_slice_attestation_rejected_diagnostic([
            "missing replayed instruction trace for exact replay slice attestation",
        ])];
    };

    let function_context = context.for_function(function);
    let mut diagnostics = vec![exact_replay_slice_attestation_diagnostic(
        &function_context.exact_replay_slice_attestation_for_addresses(&trace_addresses),
    )];
    if let trust_types::VerificationResult::Failed {
        counterexample: Some(counterexample), ..
    } = result
    {
        if let Some(report) = attempt_bounded_machine_replay_report(
            counterexample,
            BinaryReplayAttempt { function, vc, context: replay_context },
        ) {
            diagnostics.extend(exact_replay_transcript_fact_diagnostics(&report));
        }
    }
    diagnostics
}

fn result_counterexample_trace_addresses(
    result: &trust_types::VerificationResult,
) -> Option<Vec<u64>> {
    match result {
        trust_types::VerificationResult::Failed {
            counterexample: Some(counterexample), ..
        } => counterexample_trace_addresses(counterexample),
        _ => None,
    }
}

fn exact_replay_slice_attestation_diagnostic(status: &ExactReplaySliceAttestationStatus) -> String {
    if status.accepted {
        EXACT_REPLAY_SLICE_ATTESTATION_ACCEPTED_DIAGNOSTIC.to_string()
    } else {
        exact_replay_slice_attestation_rejected_diagnostic(
            status.blockers.iter().map(String::as_str),
        )
    }
}

fn exact_replay_slice_attestation_rejected_diagnostic<'a>(
    blockers: impl IntoIterator<Item = &'a str>,
) -> String {
    let detail = blockers.into_iter().collect::<Vec<_>>().join(" | ");
    if detail.is_empty() {
        EXACT_REPLAY_SLICE_ATTESTATION_REJECTED_PREFIX.to_string()
    } else {
        format!("{EXACT_REPLAY_SLICE_ATTESTATION_REJECTED_PREFIX}: {detail}")
    }
}

fn exact_replay_transcript_fact_diagnostics(
    report: &trust_symex::BinaryReplayReport,
) -> Vec<String> {
    let machine = &report.machine_replay;
    if machine.status != trust_symex::BinaryMachineReplayStatus::Replayed {
        return Vec::new();
    }

    let mut diagnostics = Vec::new();
    diagnostics
        .extend(machine.byte_range_evidence.iter().map(exact_replay_byte_range_fact_diagnostic));
    diagnostics.extend(exact_replay_control_flow_fact_diagnostics(machine));
    diagnostics
        .extend(machine.effect_evidence.iter().map(exact_replay_memory_effect_fact_diagnostic));
    diagnostics.sort();
    diagnostics.dedup();
    diagnostics
}

fn exact_replay_byte_range_fact_diagnostic(
    evidence: &trust_symex::BinaryMachineReplayByteRangeEvidence,
) -> String {
    format!(
        "{EXACT_REPLAY_BYTE_RANGE_FACT_DIAGNOSTIC_PREFIX}instruction=0x{:x};step={};file_offset={};size={};instruction_bytes_sha256={}",
        evidence.instruction_address,
        step_fact(evidence.step),
        evidence.file_offset,
        evidence.size,
        trust_types::digest::stable_sha256_hex(&evidence.instruction_bytes)
    )
}

fn exact_replay_control_flow_fact_diagnostics(
    machine: &trust_symex::BinaryMachineReplayReport,
) -> Vec<String> {
    let mut diagnostics = machine
        .capability_evidence
        .iter()
        .map(exact_replay_control_flow_capability_fact_diagnostic)
        .collect::<Vec<_>>();
    let capability_keys = machine
        .capability_evidence
        .iter()
        .map(|evidence| (evidence.instruction_address, evidence.step))
        .collect::<BTreeSet<_>>();
    let architecture = machine
        .capability_evidence
        .first()
        .map(|evidence| evidence.architecture.as_str())
        .or_else(|| machine.effect_evidence.first().map(|evidence| evidence.architecture.as_str()))
        .unwrap_or("unknown");
    for instruction in &machine.observed_instruction_trace {
        let key = (instruction.origin.instruction_address, instruction.step);
        if capability_keys.contains(&key) {
            continue;
        }
        diagnostics.push(format!(
            "{EXACT_REPLAY_CONTROL_FLOW_FACT_DIAGNOSTIC_PREFIX}instruction=0x{:x};step={};architecture={};capability=fallthrough_or_no_branch_call_return;instruction_bytes_sha256={};validation_sha256={}",
            instruction.origin.instruction_address,
            step_fact(instruction.step),
            architecture,
            trust_types::digest::stable_sha256_hex(&instruction.origin.instruction_bytes),
            trust_types::digest::stable_sha256_hex(b"bounded machine replay observed no branch/call/return capability requirement")
        ));
    }
    diagnostics
}

fn exact_replay_control_flow_capability_fact_diagnostic(
    evidence: &trust_symex::BinaryMachineReplayCapabilityEvidence,
) -> String {
    format!(
        "{EXACT_REPLAY_CONTROL_FLOW_FACT_DIAGNOSTIC_PREFIX}instruction=0x{:x};step={};architecture={};capability={};instruction_bytes_sha256={};validation_sha256={}",
        evidence.instruction_address,
        step_fact(evidence.step),
        evidence.architecture,
        evidence.capability,
        trust_types::digest::stable_sha256_hex(&evidence.instruction_bytes),
        trust_types::digest::stable_sha256_hex(evidence.validation.as_bytes())
    )
}

fn exact_replay_memory_effect_fact_diagnostic(
    evidence: &trust_symex::BinaryMachineReplayEffectEvidence,
) -> String {
    let (memory_address, memory_width_bytes) = evidence
        .memory_access
        .map(|access| (format!("0x{:x}", access.address), access.width_bytes.to_string()))
        .unwrap_or_else(|| ("none".to_string(), "none".to_string()));
    format!(
        "{EXACT_REPLAY_MEMORY_EFFECT_FACT_DIAGNOSTIC_PREFIX}instruction=0x{:x};step={};witness_step={};architecture={};kind={};subject={};memory_address={};memory_width_bytes={};validation_sha256={}",
        evidence.instruction_address,
        step_fact(evidence.step),
        step_fact(evidence.witness_step),
        evidence.architecture,
        evidence.kind,
        evidence.subject.as_deref().unwrap_or("none"),
        memory_address,
        memory_width_bytes,
        trust_types::digest::stable_sha256_hex(evidence.validation.as_bytes())
    )
}

fn step_fact(step: Option<u32>) -> String {
    step.map(|step| step.to_string()).unwrap_or_else(|| "none".to_string())
}

fn binary_solver_dispatch_status(result: &trust_types::VerificationResult) -> SolverDispatchStatus {
    match result {
        trust_types::VerificationResult::Proved { .. } => SolverDispatchStatus::Unsat,
        trust_types::VerificationResult::Failed { .. } => SolverDispatchStatus::Sat,
        trust_types::VerificationResult::Unknown { .. } => SolverDispatchStatus::Unknown,
        trust_types::VerificationResult::Timeout { .. } => SolverDispatchStatus::Timeout,
        _ => SolverDispatchStatus::Unknown,
    }
}

fn binary_proof_certificate_status(
    result: &trust_types::VerificationResult,
) -> ProofCertificateStatus {
    match result {
        trust_types::VerificationResult::Proved { proof_certificate: Some(_), .. } => {
            ProofCertificateStatus::Present {
                format: "solver-native".to_string(),
                sha256: None,
                artifact_path: None,
            }
        }
        trust_types::VerificationResult::Proved { .. } => ProofCertificateStatus::Unavailable {
            reason: Some("solver did not return a proof artifact".to_string()),
        },
        _ => ProofCertificateStatus::NotRequested,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BinarySolverResultFields {
    status: String,
    time_ms: u64,
    detail: Option<String>,
    replay_status: Option<String>,
    replay_detail: Option<String>,
    replay_capability_evidence: Vec<trust_symex::BinaryMachineReplayCapabilityEvidence>,
    replay_capability_evidence_matched: Option<bool>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BinaryReplayFields {
    status: String,
    detail: String,
    capability_evidence: Vec<trust_symex::BinaryMachineReplayCapabilityEvidence>,
    capability_evidence_matched: Option<bool>,
}

#[derive(Debug, Clone)]
struct BinaryReplayContext {
    architecture: BoundedMachineCodeArchitecture,
    address_map: BoundedMachineCodeAddressMap,
    loaded_segments: Vec<BoundedMachineCodeSegment>,
    loaded_binary_segments: Vec<BinarySegment>,
    selected_image_bytes: Option<Vec<u8>>,
    root_artifact_digest: Option<BinaryArtifactDigest>,
    selected_image_identity: Option<BinarySelectedImageIdentity>,
    invalid_instruction_bytes: BTreeMap<u64, InvalidInstructionBytesReason>,
    exact_source_addresses: BTreeSet<u64>,
    exact_replay_attestations: BTreeMap<u64, ExactReplayInstructionAttestationSummary>,
    exact_replay_slice_blockers: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExactReplayInstructionAttestationSummary {
    accepted: bool,
    blockers: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExactReplaySliceAttestationStatus {
    accepted: bool,
    blockers: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum InvalidInstructionBytesReason {
    Missing,
    LengthMismatch {
        instruction_size: u8,
        byte_len: usize,
    },
    SelectedImageFileRangeMissing,
    SelectedImageRangeOutside {
        file_offset: u64,
        size: u64,
        selected_file_offset: u64,
        selected_file_size: u64,
    },
}

impl InvalidInstructionBytesReason {
    fn replay_detail(&self, address: u64) -> String {
        match self {
            Self::Missing => format!(
                "needs_machine_replay: original instruction bytes missing for trace address 0x{address:x}; cannot replay"
            ),
            Self::LengthMismatch { instruction_size, byte_len } => format!(
                "needs_machine_replay: original instruction byte length mismatch for trace address 0x{address:x}: instruction_size={instruction_size} but {byte_len} byte(s) were captured; cannot replay"
            ),
            Self::SelectedImageFileRangeMissing => format!(
                "needs_machine_replay: selected-image bytes are available but no file-backed executable byte range maps trace address 0x{address:x}; cannot replay"
            ),
            Self::SelectedImageRangeOutside {
                file_offset,
                size,
                selected_file_offset,
                selected_file_size,
            } => format!(
                "needs_machine_replay: selected-image byte range for trace address 0x{address:x} is outside selected loaded image: file_offset={file_offset} size={size} selected_file_offset={selected_file_offset} selected_file_size={selected_file_size}; cannot replay"
            ),
        }
    }
}

#[derive(Clone, Copy)]
struct BinaryReplayAttempt<'a> {
    function: &'a trust_lift::LiftedFunction,
    vc: &'a VerificationCondition,
    context: Option<&'a BinaryReplayContext>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct BinaryCliProofGradeGateReport {
    accepted: bool,
    status: String,
    final_trust_level: String,
    unsupported_ledger_empty: bool,
    all_required_vcs_proved: bool,
    checked_certificates_for_all_required_vcs: bool,
    checked_certificate_readback_for_all_required_vcs: bool,
    full_replay_coverage: bool,
    replay_semantics_satisfied: bool,
    exact_replay_slice_attestation_for_replayed_vcs: bool,
    replay_attestation_for_all_required_vcs: bool,
    source_backpropagation_handoff_for_all_required_vcs: bool,
    required_vcs: usize,
    solver_dispatches: usize,
    proved_vcs: usize,
    unproved_vcs: usize,
    non_proved_results: usize,
    checked_certificates: usize,
    missing_checked_certificates: usize,
    checked_certificate_readback_rows: usize,
    replayed_vcs: usize,
    exact_replay_slice_attested_vcs: usize,
    missing_exact_replay_slice_attestation: usize,
    certificate_only_replay_semantics_vcs: usize,
    replay_semantics_satisfied_vcs: usize,
    missing_machine_replay: usize,
    replay_attestation_rows: usize,
    source_backpropagation_handoff_rows: usize,
    raw_solver_proof_bytes: usize,
    raw_solver_proof_bytes_sufficient: bool,
    blockers: Vec<BinaryCliProofGradeBlockerReport>,
    rejections: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct BinaryCliProofGradeBlockerReport {
    code: String,
    stage: String,
    feature: String,
    detail: String,
    evidence_required: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct BinaryVerifyProofEvidenceReport {
    total_vcs: usize,
    solver_dispatches: usize,
    solver_dispatch_status_counts: BTreeMap<String, usize>,
    replay: ReplayStatus,
    replay_status_counts: BTreeMap<String, usize>,
    checked_certificate_coverage: BinaryCertificateCheckReport,
    raw_solver_proof_byte_count: usize,
    proof_grade_gate: BinaryProofGradeGateReport,
}

#[derive(Serialize)]
struct BinaryVerifyJsonReport<'a> {
    #[serde(flatten)]
    report: &'a BinaryVerifyReport,
    solver_route: BinaryCliSolverRouteDiagnostic,
    checked_certificate_evidence: CheckedCertificateEvidenceSummaryReport,
    proof_grade_release_transcript: ProofGradeReleaseTranscriptReport,
    proof_evidence: BinaryVerifyProofEvidenceReport,
    proof_grade_gate: BinaryCliProofGradeGateReport,
    source_backpropagation_gate: SourceBackpropagationGateReport,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExploitFindAnalysis {
    status: ExploitFindStatus,
    exploit_found: bool,
    independent_refutation_status: ExploitFindStatus,
    independent_refutation_note: String,
    reducer_status: ExploitFindStatus,
    reducer_note: String,
    synthesis_status: ExploitFindStatus,
    synthesis_note: String,
    replay_status: ExploitFindStatus,
    replay_note: String,
    reason: String,
    notes: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExploitEvidenceSummary {
    raw_solver_candidates: usize,
    exact_replayed_candidates: usize,
    checked_unsat_refutations: usize,
    deterministically_attributed_candidates: usize,
    deterministically_reduced_candidates: usize,
    required_vcs: usize,
    all_required_vcs_checked_unsat: bool,
    replay_status: ExploitFindStatus,
    independent_refutation_status: ExploitFindStatus,
    reduction_status: ExploitFindStatus,
    attribution_status: ExploitFindStatus,
    regression_status: ExploitFindStatus,
}

#[cfg(test)]
fn binary_solver_result_report(
    function: &str,
    vc_kind: String,
    location: Option<String>,
    result: &trust_types::VerificationResult,
) -> BinarySolverResultReport {
    binary_solver_result_report_with_replay(function, vc_kind, location, result, None)
}

fn binary_solver_result_report_with_replay(
    function: &str,
    vc_kind: String,
    location: Option<String>,
    result: &trust_types::VerificationResult,
    replay_attempt: Option<BinaryReplayAttempt<'_>>,
) -> BinarySolverResultReport {
    let fields = solver_result_fields(result, replay_attempt);
    BinarySolverResultReport {
        function: function.to_string(),
        vc_kind,
        location,
        solver: result.solver_name().to_string(),
        status: fields.status,
        time_ms: fields.time_ms,
        detail: fields.detail,
        replay_status: fields.replay_status,
        replay_detail: fields.replay_detail,
        replay_capability_evidence: fields.replay_capability_evidence,
        replay_capability_evidence_matched: fields.replay_capability_evidence_matched,
    }
}

fn solver_result_fields(
    result: &trust_types::VerificationResult,
    replay_attempt: Option<BinaryReplayAttempt<'_>>,
) -> BinarySolverResultFields {
    match result {
        trust_types::VerificationResult::Proved {
            time_ms, proof_certificate: Some(bytes), ..
        } => BinarySolverResultFields {
            status: "proved".into(),
            time_ms: *time_ms,
            detail: Some(format!(
                "raw solver proof bytes present ({} byte(s)); checked proof certificate is still required for proof-grade",
                bytes.len()
            )),
            replay_status: None,
            replay_detail: None,
            replay_capability_evidence: Vec::new(),
            replay_capability_evidence_matched: None,
        },
        trust_types::VerificationResult::Proved { time_ms, .. } => BinarySolverResultFields {
            status: "proved".into(),
            time_ms: *time_ms,
            detail: None,
            replay_status: None,
            replay_detail: None,
            replay_capability_evidence: Vec::new(),
            replay_capability_evidence_matched: None,
        },
        trust_types::VerificationResult::Failed {
            time_ms,
            counterexample: Some(counterexample),
            ..
        } => {
            let replay = binary_counterexample_replay_fields(counterexample, replay_attempt);
            BinarySolverResultFields {
                status: "failed".into(),
                time_ms: *time_ms,
                detail: Some(counterexample.to_string()),
                replay_status: Some(replay.status),
                replay_detail: Some(replay.detail),
                replay_capability_evidence: replay.capability_evidence,
                replay_capability_evidence_matched: replay.capability_evidence_matched,
            }
        }
        trust_types::VerificationResult::Failed { time_ms, counterexample: None, .. } => {
            BinarySolverResultFields {
                status: "failed".into(),
                time_ms: *time_ms,
                detail: Some("SAT without counterexample model".into()),
                replay_status: Some("not_attempted".into()),
                replay_detail: Some(
                    "needs_machine_replay: SAT without counterexample model; cannot replay".into(),
                ),
                replay_capability_evidence: Vec::new(),
                replay_capability_evidence_matched: None,
            }
        }
        trust_types::VerificationResult::Unknown { time_ms, reason, .. } => {
            BinarySolverResultFields {
                status: "unknown".into(),
                time_ms: *time_ms,
                detail: Some(reason.clone()),
                replay_status: None,
                replay_detail: None,
                replay_capability_evidence: Vec::new(),
                replay_capability_evidence_matched: None,
            }
        }
        trust_types::VerificationResult::Timeout { timeout_ms, .. } => BinarySolverResultFields {
            status: "timeout".into(),
            time_ms: *timeout_ms,
            detail: Some(format!("timeout after {timeout_ms}ms")),
            replay_status: None,
            replay_detail: None,
            replay_capability_evidence: Vec::new(),
            replay_capability_evidence_matched: None,
        },
        _ => BinarySolverResultFields {
            status: "unknown".into(),
            time_ms: 0,
            detail: Some("unrecognized solver result".into()),
            replay_status: None,
            replay_detail: None,
            replay_capability_evidence: Vec::new(),
            replay_capability_evidence_matched: None,
        },
    }
}

fn binary_counterexample_replay_fields(
    counterexample: &trust_types::Counterexample,
    replay_attempt: Option<BinaryReplayAttempt<'_>>,
) -> BinaryReplayFields {
    if let Some(attempt) = replay_attempt {
        if let Some(replay) = attempt_bounded_machine_replay(counterexample, attempt) {
            return replay;
        }
    }

    let detail = match &counterexample.trace {
        None => "needs_machine_replay: raw solver model has no execution trace; machine-code replay is required before treating it as a concrete binary witness".to_string(),
        Some(trace) if trace.steps.is_empty() => "needs_machine_replay: counterexample trace is empty; machine-code replay is required before treating it as a concrete binary witness".to_string(),
        Some(trace) => {
            let missing_program_points =
                trace.steps.iter().filter(|step| step.program_point.is_none()).count();
            if missing_program_points == trace.steps.len() {
                format!(
                    "needs_machine_replay: counterexample trace has {} step(s) but no lifted program points; machine-code replay is required before treating it as a concrete binary witness",
                    trace.steps.len()
                )
            } else if missing_program_points > 0 {
                format!(
                    "needs_machine_replay: counterexample trace has {missing_program_points} step(s) without lifted program points; machine-code replay is required before treating it as a concrete binary witness"
                )
            } else {
                format!(
                    "needs_machine_replay: counterexample trace has {} lifted step(s), but targo trust verify-binary has not run machine-code replay for it",
                    trace.steps.len()
                )
            }
        }
    };
    BinaryReplayFields {
        status: "not_attempted".into(),
        detail,
        capability_evidence: Vec::new(),
        capability_evidence_matched: None,
    }
}

impl BinaryReplayContext {
    fn from_lifted_binary(
        binary: &LiftedBinary,
        selected_image_bytes: Option<&[u8]>,
    ) -> Option<Self> {
        let architecture = bounded_machine_architecture(binary.architecture)?;
        if binary.source_provenance.status != trust_lift::LiftedSourceProvenanceStatus::Exact {
            return None;
        }
        let exact_source_addresses = binary
            .source_mappings
            .iter()
            .map(|mapping| mapping.binary_address)
            .collect::<BTreeSet<_>>();
        let loaded_segments =
            binary.segments.iter().filter_map(bounded_machine_code_segment).collect();
        let (exact_replay_attestations, exact_replay_slice_blockers) =
            exact_replay_attestations_for_binary(binary, selected_image_bytes);
        let (selected_image_bytes, root_artifact_digest, selected_image_identity) =
            selected_image_identity_from_bytes(selected_image_bytes);
        Some(Self {
            architecture,
            address_map: BoundedMachineCodeAddressMap::new(),
            loaded_segments,
            loaded_binary_segments: binary.segments.clone(),
            selected_image_bytes,
            root_artifact_digest,
            selected_image_identity,
            invalid_instruction_bytes: BTreeMap::new(),
            exact_source_addresses,
            exact_replay_attestations,
            exact_replay_slice_blockers,
        })
    }

    fn for_function(&self, function: &trust_lift::LiftedFunction) -> Self {
        let mut address_map = BoundedMachineCodeAddressMap::new();
        let mut invalid_instruction_bytes = BTreeMap::new();
        for annotation in function.annotations.iter() {
            if !self.exact_source_addresses.contains(&annotation.binary_offset) {
                continue;
            }
            if annotation.instruction_bytes.is_empty() {
                invalid_instruction_bytes
                    .insert(annotation.binary_offset, InvalidInstructionBytesReason::Missing);
                continue;
            }
            if usize::from(annotation.instruction_size) != annotation.instruction_bytes.len() {
                invalid_instruction_bytes.insert(
                    annotation.binary_offset,
                    InvalidInstructionBytesReason::LengthMismatch {
                        instruction_size: annotation.instruction_size,
                        byte_len: annotation.instruction_bytes.len(),
                    },
                );
                continue;
            }
            if self.selected_image_bytes.is_some() {
                let (file_offset, selected_bytes) =
                    match self.selected_image_instruction_bytes(annotation) {
                        Ok(mapped) => mapped,
                        Err(reason) => {
                            invalid_instruction_bytes.insert(annotation.binary_offset, reason);
                            continue;
                        }
                    };
                address_map.insert(
                    BoundedMachineInstructionBytes::new(annotation.binary_offset, selected_bytes)
                        .with_file_offset(file_offset),
                );
                continue;
            }
            address_map.insert(BoundedMachineInstructionBytes::new(
                annotation.binary_offset,
                annotation.instruction_bytes.clone(),
            ));
        }
        Self {
            architecture: self.architecture,
            address_map,
            loaded_segments: self.loaded_segments.clone(),
            loaded_binary_segments: self.loaded_binary_segments.clone(),
            selected_image_bytes: self.selected_image_bytes.clone(),
            root_artifact_digest: self.root_artifact_digest.clone(),
            selected_image_identity: self.selected_image_identity.clone(),
            invalid_instruction_bytes,
            exact_source_addresses: self.exact_source_addresses.clone(),
            exact_replay_attestations: self.exact_replay_attestations.clone(),
            exact_replay_slice_blockers: self.exact_replay_slice_blockers.clone(),
        }
    }

    fn has_exact_source_address(&self, address: u64) -> bool {
        self.exact_source_addresses.contains(&address)
    }

    fn has_instruction_bytes(&self, address: u64) -> bool {
        self.address_map.get(address).is_some()
    }

    fn invalid_instruction_bytes_reason(
        &self,
        address: u64,
    ) -> Option<&InvalidInstructionBytesReason> {
        self.invalid_instruction_bytes.get(&address)
    }

    fn instruction_bytes(&self, address: u64) -> Option<&[u8]> {
        let bytes = &self.address_map.get(address)?.bytes;
        (!bytes.is_empty()).then_some(bytes.as_slice())
    }

    fn selected_image_instruction_bytes(
        &self,
        annotation: &trust_lift::cfg::ProofAnnotation,
    ) -> Result<(u64, Vec<u8>), InvalidInstructionBytesReason> {
        let selected_image_bytes = self
            .selected_image_bytes
            .as_ref()
            .ok_or(InvalidInstructionBytesReason::SelectedImageFileRangeMissing)?;
        let selected_image = self
            .selected_image_identity
            .as_ref()
            .ok_or(InvalidInstructionBytesReason::SelectedImageFileRangeMissing)?;
        let size = u64::from(annotation.instruction_size);
        let file_offset = instruction_file_offset_for_segments(
            &self.loaded_binary_segments,
            annotation.binary_offset,
            size,
        )
        .ok_or(InvalidInstructionBytesReason::SelectedImageFileRangeMissing)?;
        let selected_start = file_offset.checked_sub(selected_image.file_offset).ok_or({
            InvalidInstructionBytesReason::SelectedImageRangeOutside {
                file_offset,
                size,
                selected_file_offset: selected_image.file_offset,
                selected_file_size: selected_image.file_size,
            }
        })?;
        let selected_end = selected_start.checked_add(size).ok_or({
            InvalidInstructionBytesReason::SelectedImageRangeOutside {
                file_offset,
                size,
                selected_file_offset: selected_image.file_offset,
                selected_file_size: selected_image.file_size,
            }
        })?;
        if selected_end > selected_image.file_size {
            return Err(InvalidInstructionBytesReason::SelectedImageRangeOutside {
                file_offset,
                size,
                selected_file_offset: selected_image.file_offset,
                selected_file_size: selected_image.file_size,
            });
        }
        let start = usize::try_from(selected_start).map_err(|_| {
            InvalidInstructionBytesReason::SelectedImageRangeOutside {
                file_offset,
                size,
                selected_file_offset: selected_image.file_offset,
                selected_file_size: selected_image.file_size,
            }
        })?;
        let end = usize::try_from(selected_end).map_err(|_| {
            InvalidInstructionBytesReason::SelectedImageRangeOutside {
                file_offset,
                size,
                selected_file_offset: selected_image.file_offset,
                selected_file_size: selected_image.file_size,
            }
        })?;
        if end > selected_image_bytes.len() {
            return Err(InvalidInstructionBytesReason::SelectedImageRangeOutside {
                file_offset,
                size,
                selected_file_offset: selected_image.file_offset,
                selected_file_size: selected_image.file_size,
            });
        }
        Ok((file_offset, selected_image_bytes[start..end].to_vec()))
    }

    fn exact_replay_slice_attestation_for_addresses(
        &self,
        addresses: &[u64],
    ) -> ExactReplaySliceAttestationStatus {
        let mut blockers = self.exact_replay_slice_blockers.clone();
        if addresses.is_empty() {
            blockers.push("no replayed instruction witnesses".to_string());
        }
        for address in addresses {
            match self.exact_replay_attestations.get(address) {
                Some(attestation) if attestation.accepted => {}
                Some(attestation) => blockers.extend(attestation.blockers.iter().map(|blocker| {
                    format!("instruction 0x{address:x}: {blocker}")
                })),
                None => blockers.push(format!(
                    "missing exact replay selected-image byte/segment attestation for instruction 0x{address:x}"
                )),
            }
        }
        blockers.sort();
        blockers.dedup();
        ExactReplaySliceAttestationStatus { accepted: blockers.is_empty(), blockers }
    }
}

fn selected_image_identity_from_bytes(
    selected_image_bytes: Option<&[u8]>,
) -> (Option<Vec<u8>>, Option<BinaryArtifactDigest>, Option<BinarySelectedImageIdentity>) {
    let Some(bytes) = selected_image_bytes else {
        return (None, None, None);
    };
    let Ok(file_size) = u64::try_from(bytes.len()) else {
        return (None, None, None);
    };
    let digest = trust_types::digest::stable_sha256_hex(bytes);
    (
        Some(bytes.to_vec()),
        Some(BinaryArtifactDigest::sha256(digest.clone())),
        Some(BinarySelectedImageIdentity { file_offset: 0, file_size, sha256: digest }),
    )
}

fn instruction_file_offset_for_segments(
    segments: &[BinarySegment],
    address: u64,
    size: u64,
) -> Option<u64> {
    if size == 0 {
        return None;
    }
    let range_end = address.checked_add(size)?;
    for segment in segments {
        if !segment.permissions.execute {
            continue;
        }
        let segment_start = segment.virtual_range.start;
        let segment_end = segment.virtual_range.end;
        if address < segment_start || range_end > segment_end {
            continue;
        }
        let file_offset = segment.file_offset?;
        let file_size = segment.file_size?;
        let relative = address.checked_sub(segment_start)?;
        if relative.checked_add(size)? > file_size {
            continue;
        }
        return file_offset.checked_add(relative);
    }
    None
}

fn exact_replay_attestations_for_binary(
    binary: &LiftedBinary,
    selected_image_bytes: Option<&[u8]>,
) -> (BTreeMap<u64, ExactReplayInstructionAttestationSummary>, Vec<String>) {
    let Some(selected_image_bytes) = selected_image_bytes else {
        return (
            BTreeMap::new(),
            vec!["missing selected image bytes for exact replay slice attestation".to_string()],
        );
    };
    let selected_image = ExactReplaySelectedImage::thin(selected_image_bytes);
    let mut attestations = BTreeMap::<u64, ExactReplayInstructionAttestationSummary>::new();
    let mut saw_witness = false;

    for function in &binary.functions {
        for annotation in &function.annotations {
            saw_witness = true;
            let witness = ExactReplayInstructionWitness::new(
                annotation.binary_offset,
                annotation.instruction_size,
                annotation.instruction_bytes.clone(),
            );
            let attestation = binary.attest_exact_replay_slice(selected_image, &[witness]);
            let summary = ExactReplayInstructionAttestationSummary {
                accepted: attestation.accepted,
                blockers: if attestation.accepted { Vec::new() } else { attestation.blockers },
            };
            attestations
                .entry(annotation.binary_offset)
                .and_modify(|existing| {
                    existing.accepted &= summary.accepted;
                    existing.blockers.extend(summary.blockers.iter().cloned());
                    existing.blockers.sort();
                    existing.blockers.dedup();
                })
                .or_insert(summary);
        }
    }

    let blockers = if saw_witness {
        Vec::new()
    } else {
        vec!["no lifted instruction witnesses for exact replay slice attestation".to_string()]
    };
    (attestations, blockers)
}

fn bounded_machine_code_segment(segment: &BinarySegment) -> Option<BoundedMachineCodeSegment> {
    let start = segment.virtual_range.start;
    let size = segment.virtual_range.end.checked_sub(start)?;
    if size == 0 {
        return None;
    }

    Some(BoundedMachineCodeSegment::new(
        start,
        size,
        BoundedMachineCodeSegmentPermissions::new(
            segment.permissions.read,
            segment.permissions.write,
            segment.permissions.execute,
        ),
    ))
}

fn bounded_machine_architecture(architecture: &str) -> Option<BoundedMachineCodeArchitecture> {
    match architecture {
        "aarch64" | "arm64" | "AArch64" => Some(BoundedMachineCodeArchitecture::Aarch64),
        "x86-64" | "x86_64" | "amd64" | "X86_64" => Some(BoundedMachineCodeArchitecture::X86_64),
        _ => None,
    }
}

struct BoundedMachineReplayAttemptReport {
    report: trust_symex::BinaryReplayReport,
    exact_original_bytes_replayed: bool,
}

enum BoundedMachineReplayAttemptOutcome {
    Fields(BinaryReplayFields),
    Report(Box<BoundedMachineReplayAttemptReport>),
}

fn attempt_bounded_machine_replay(
    counterexample: &trust_types::Counterexample,
    replay_attempt: BinaryReplayAttempt<'_>,
) -> Option<BinaryReplayFields> {
    match attempt_bounded_machine_replay_outcome(counterexample, replay_attempt)? {
        BoundedMachineReplayAttemptOutcome::Fields(fields) => Some(fields),
        BoundedMachineReplayAttemptOutcome::Report(outcome) => {
            Some(binary_replay_fields_from_report(
                &outcome.report,
                outcome.exact_original_bytes_replayed,
            ))
        }
    }
}

fn attempt_bounded_machine_replay_report(
    counterexample: &trust_types::Counterexample,
    replay_attempt: BinaryReplayAttempt<'_>,
) -> Option<trust_symex::BinaryReplayReport> {
    match attempt_bounded_machine_replay_outcome(counterexample, replay_attempt)? {
        BoundedMachineReplayAttemptOutcome::Fields(_) => None,
        BoundedMachineReplayAttemptOutcome::Report(outcome) => {
            let outcome = *outcome;
            outcome.exact_original_bytes_replayed.then_some(outcome.report)
        }
    }
}

fn attempt_bounded_machine_replay_outcome(
    counterexample: &trust_types::Counterexample,
    replay_attempt: BinaryReplayAttempt<'_>,
) -> Option<BoundedMachineReplayAttemptOutcome> {
    let Some(context) = replay_attempt.context else {
        return Some(BoundedMachineReplayAttemptOutcome::Fields(BinaryReplayFields {
            status: "not_attempted".into(),
            detail: "needs_machine_replay: exact source provenance or supported machine architecture is unavailable; cannot replay".into(),
            capability_evidence: Vec::new(),
            capability_evidence_matched: None,
        }));
    };
    let trace_addresses = counterexample_trace_addresses(counterexample)?;
    if trace_addresses.is_empty() {
        return None;
    }

    let function_context = context.for_function(replay_attempt.function);
    if let Some(address) =
        trace_addresses.iter().find(|address| !function_context.has_exact_source_address(**address))
    {
        return Some(BoundedMachineReplayAttemptOutcome::Fields(BinaryReplayFields {
            status: "not_attempted".into(),
            detail: format!(
                "needs_machine_replay: no exact source provenance for trace address 0x{address:x}; cannot replay"
            ),
            capability_evidence: Vec::new(),
            capability_evidence_matched: None,
        }));
    }
    if let Some((address, reason)) = trace_addresses.iter().find_map(|address| {
        function_context.invalid_instruction_bytes_reason(*address).map(|reason| (*address, reason))
    }) {
        return Some(BoundedMachineReplayAttemptOutcome::Fields(BinaryReplayFields {
            status: "not_attempted".into(),
            detail: reason.replay_detail(address),
            capability_evidence: Vec::new(),
            capability_evidence_matched: None,
        }));
    }
    if let Some(address) =
        trace_addresses.iter().find(|address| !function_context.has_instruction_bytes(**address))
    {
        return Some(BoundedMachineReplayAttemptOutcome::Fields(BinaryReplayFields {
            status: "not_attempted".into(),
            detail: format!(
                "needs_machine_replay: no original instruction bytes mapped for trace address 0x{address:x}; cannot replay"
            ),
            capability_evidence: Vec::new(),
            capability_evidence_matched: None,
        }));
    }

    let mut image = BoundedMachineCodeImage::with_address_map(
        function_context.architecture,
        function_context.address_map.clone(),
    );
    if let Some(artifact_digest) = function_context.root_artifact_digest.clone() {
        image = image.with_artifact_digest(artifact_digest);
    }
    if let Some(selected_image) = function_context.selected_image_identity.clone() {
        image = image.with_selected_image(selected_image);
    }
    for segment in function_context.loaded_segments.iter() {
        image.insert_segment(segment.start, segment.size, segment.permissions);
    }
    let backend =
        BoundedMachineCodeReplayBackend::new(image).with_max_instructions(trace_addresses.len());
    let mut input = BinaryReplayInput::new(counterexample.clone())
        .with_instruction_provenance(instruction_provenance_for_lifted_function(
            replay_attempt.function,
        ))
        .with_verification_condition(replay_attempt.vc.clone());
    let has_selected_image_identity = match (
        function_context.root_artifact_digest.clone(),
        function_context.selected_image_identity.clone(),
    ) {
        (Some(artifact_digest), Some(selected_image)) => {
            input = input
                .with_artifact_digest(artifact_digest)
                .with_selected_image(selected_image)
                .require_selected_image_identity();
            true
        }
        _ => false,
    };
    let machine_config = if has_selected_image_identity {
        BinaryMachineReplayConfig::default()
    } else {
        BinaryMachineReplayConfig {
            require_exact_artifact_digest: false,
            ..BinaryMachineReplayConfig::default()
        }
    };
    let replay_function = lifted_replay_function(replay_attempt.function);
    let report = replay_binary_counterexample_with_machine_replay(
        BinaryReplayTarget::lifted(&replay_function),
        &input,
        &BinaryReplayConfig::default(),
        &machine_config,
        &backend,
    );
    let exact_original_bytes_replayed =
        exact_original_bytes_replayed(&report, &function_context, &trace_addresses);

    Some(BoundedMachineReplayAttemptOutcome::Report(Box::new(BoundedMachineReplayAttemptReport {
        report,
        exact_original_bytes_replayed,
    })))
}

fn lifted_replay_function(function: &trust_lift::LiftedFunction) -> VerifiableFunction {
    VerifiableFunction {
        name: function.name.clone(),
        def_path: format!("binary::{}", function.name),
        span: SourceSpan::binary_address(function.entry_point),
        body: function.trust_ir_body.clone(),
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn counterexample_trace_addresses(
    counterexample: &trust_types::Counterexample,
) -> Option<Vec<u64>> {
    let trace = counterexample.trace.as_ref()?;
    let addresses = trace
        .steps
        .iter()
        .filter_map(|step| {
            step.program_point.as_deref().and_then(parse_address_from_counterexample_program_point)
        })
        .collect::<Vec<_>>();
    Some(addresses)
}

fn parse_address_from_counterexample_program_point(program_point: &str) -> Option<u64> {
    let bytes = program_point.as_bytes();
    let mut idx = 0;
    while idx + 2 <= bytes.len() {
        if bytes[idx] == b'0' && matches!(bytes.get(idx + 1), Some(b'x' | b'X')) {
            let start = idx + 2;
            let mut end = start;
            while end < bytes.len() && bytes[end].is_ascii_hexdigit() {
                end += 1;
            }
            if end > start {
                return u64::from_str_radix(&program_point[start..end], 16).ok();
            }
        }
        idx += 1;
    }
    None
}

fn exact_original_bytes_replayed(
    report: &trust_symex::BinaryReplayReport,
    context: &BinaryReplayContext,
    trace_addresses: &[u64],
) -> bool {
    if report.status != BinaryReplayStatus::Confirmed
        || report.machine_replay.status != trust_symex::BinaryMachineReplayStatus::Replayed
        || !report.machine_replay.matched_instruction_trace
        || trace_addresses.is_empty()
    {
        return false;
    }

    let observed = &report.machine_replay.observed_instruction_trace;
    observed.len() == trace_addresses.len()
        && observed.iter().zip(trace_addresses).all(|(instruction, address)| {
            instruction.origin.instruction_address == *address
                && exact_origin_instruction_bytes(&instruction.origin)
                    .is_some_and(|bytes| Some(bytes) == context.instruction_bytes(*address))
        })
}

fn binary_replay_fields_from_report(
    report: &trust_symex::BinaryReplayReport,
    exact_original_bytes_replayed: bool,
) -> BinaryReplayFields {
    let capability_evidence = report.machine_replay.capability_evidence.clone();
    let capability_evidence_matched = Some(report.machine_replay.matched_capability_evidence);
    match report.status {
        BinaryReplayStatus::Confirmed if exact_original_bytes_replayed => BinaryReplayFields {
            status: "replayed".into(),
            detail: format!("machine_replay_confirmed: {}", report.reason),
            capability_evidence,
            capability_evidence_matched,
        },
        BinaryReplayStatus::Confirmed => BinaryReplayFields {
            status: "not_attempted".into(),
            detail: format!(
                "needs_machine_replay: replay confirmation did not include exact original instruction bytes; failed closed: {}",
                report.reason
            ),
            capability_evidence,
            capability_evidence_matched,
        },
        BinaryReplayStatus::Spurious => BinaryReplayFields {
            status: "spurious".into(),
            detail: format!("machine_replay_spurious: {}", report.reason),
            capability_evidence,
            capability_evidence_matched,
        },
        BinaryReplayStatus::NeedsMachineReplay => BinaryReplayFields {
            status: "not_attempted".into(),
            detail: format!("needs_machine_replay: {}", report.reason),
            capability_evidence,
            capability_evidence_matched,
        },
        BinaryReplayStatus::Unsupported => BinaryReplayFields {
            status: "not_attempted".into(),
            detail: format!(
                "needs_machine_replay: unsupported bounded machine replay: {}",
                report.reason
            ),
            capability_evidence,
            capability_evidence_matched,
        },
        BinaryReplayStatus::Failed => BinaryReplayFields {
            status: "not_attempted".into(),
            detail: format!(
                "needs_machine_replay: bounded machine replay failed closed: {}",
                report.reason
            ),
            capability_evidence,
            capability_evidence_matched,
        },
        _ => BinaryReplayFields {
            status: "not_attempted".into(),
            detail: format!(
                "needs_machine_replay: unrecognized bounded machine replay status failed closed: {}",
                report.reason
            ),
            capability_evidence,
            capability_evidence_matched,
        },
    }
}

fn binary_verify_json_report<'a>(
    report: &'a BinaryVerifyReport,
    requested_solver: Option<&str>,
    solver_route: BinarySolverRoute,
) -> BinaryVerifyJsonReport<'a> {
    let checked_certificate_evidence = build_checked_certificate_evidence_summary(report);
    let proof_grade_release_transcript = proof_grade_release_transcript_report(
        &checked_certificate_evidence.proof_grade_release_transcript_rows,
    );
    BinaryVerifyJsonReport {
        report,
        solver_route: solver_route_diagnostic(requested_solver, solver_route),
        checked_certificate_evidence,
        proof_grade_release_transcript,
        proof_evidence: build_binary_verify_proof_evidence_report(report),
        proof_grade_gate: build_binary_cli_proof_grade_gate(report),
        source_backpropagation_gate: build_verify_binary_source_backpropagation_gate(report),
    }
}

#[cfg(test)]
fn serialize_verify_binary_json(report: &BinaryVerifyReport) -> serde_json::Result<String> {
    serialize_verify_binary_json_with_route(report, None, BinarySolverRoute::AYIncremental)
}

fn serialize_verify_binary_json_with_route(
    report: &BinaryVerifyReport,
    requested_solver: Option<&str>,
    solver_route: BinarySolverRoute,
) -> serde_json::Result<String> {
    serde_json::to_string_pretty(&binary_verify_json_report(report, requested_solver, solver_route))
}

fn build_binary_cli_proof_grade_gate(report: &BinaryVerifyReport) -> BinaryCliProofGradeGateReport {
    let evidence = &report.proof_evidence;
    let required_vcs = if evidence.required_vcs == 0 && report.vcs > 0 {
        report.vcs
    } else {
        evidence.required_vcs
    };
    let solver_dispatches = evidence.solver_dispatch.len();
    let proved_vcs = evidence.proved_vcs();
    let non_proved_results = solver_dispatches.saturating_sub(proved_vcs);
    let unproved_vcs = required_vcs.saturating_sub(proved_vcs);
    let checked_certificates = evidence.checked_certificates();
    let missing_checked_certificates = required_vcs.saturating_sub(checked_certificates);
    let replayed_vcs = evidence.replayed_vcs();
    let exact_replay_slice_attested_vcs = evidence.exact_replay_slice_attested_vcs();
    let missing_exact_replay_slice_attestation =
        replayed_vcs.saturating_sub(exact_replay_slice_attested_vcs);
    let certificate_only_replay_semantics_vcs = evidence.certificate_only_replay_semantics_vcs();
    let replay_semantics_satisfied_vcs = evidence.replay_semantics_satisfied_vcs();
    let missing_machine_replay = required_vcs.saturating_sub(replay_semantics_satisfied_vcs);
    let raw_solver_proof_bytes = evidence.raw_solver_proof_bytes();
    let unsupported_ledger_empty = report.unsupported == 0;
    let all_required_vcs_proved = required_vcs > 0
        && solver_dispatches == required_vcs
        && proved_vcs == required_vcs
        && non_proved_results == 0;
    let checked_certificates_for_all_required_vcs =
        all_required_vcs_proved && checked_certificates == required_vcs;
    let full_replay_coverage =
        required_vcs > 0 && solver_dispatches == required_vcs && replayed_vcs == required_vcs;
    let replay_semantics_satisfied = required_vcs > 0
        && solver_dispatches == required_vcs
        && replay_semantics_satisfied_vcs == required_vcs;
    let exact_replay_slice_attestation_for_replayed_vcs =
        replayed_vcs == 0 || missing_exact_replay_slice_attestation == 0;
    let (readback_rejected_rows, readback_unmatched_rows, readback_loader_failed) =
        verify_binary_checked_certificate_readback_stale_counts(report);
    let checked_certificate_readback_rows =
        verify_binary_checked_certificate_release_readback_rows(report);
    let checked_certificate_readback_for_all_required_vcs = required_vcs > 0
        && checked_certificate_readback_rows == required_vcs
        && readback_rejected_rows == 0
        && readback_unmatched_rows == 0
        && !readback_loader_failed;
    let replay_attestation_rows = verify_binary_replay_attestation_rows(report);
    let replay_attestation_for_all_required_vcs = required_vcs > 0
        && replay_attestation_rows == required_vcs
        && readback_rejected_rows == 0
        && readback_unmatched_rows == 0
        && !readback_loader_failed;
    let source_backpropagation_handoff_rows =
        verify_binary_source_backpropagation_handoff_rows(report);
    let source_backpropagation_handoff_for_all_required_vcs = required_vcs > 0
        && source_backpropagation_handoff_rows == required_vcs
        && readback_rejected_rows == 0
        && readback_unmatched_rows == 0
        && !readback_loader_failed;
    let raw_solver_proof_bytes_sufficient = false;

    let mut blockers = Vec::new();
    let mut rejections = Vec::new();
    if report.trust_level != "proof_grade" {
        push_binary_cli_proof_grade_blocker(
            &mut blockers,
            &mut rejections,
            "final-trust-level-not-proof-grade",
            "trust-level",
            format!(
                "final trust level is `{}`; proof-grade requires `proof_grade`",
                report.trust_level
            ),
            ["proof_grade_trust_level"],
        );
    }
    if !unsupported_ledger_empty {
        push_binary_cli_proof_grade_blocker(
            &mut blockers,
            &mut rejections,
            "unsupported-ledger-nonempty",
            "unsupported-ledger",
            format!(
                "unsupported records present: {} item(s); proof-grade requires an empty unsupported ledger",
                report.unsupported
            ),
            ["empty_unsupported_ledger"],
        );
    }
    if required_vcs == 0 {
        push_binary_cli_proof_grade_blocker(
            &mut blockers,
            &mut rejections,
            "required-binary-vcs-missing",
            "proof-grade-binary-verification",
            "no required binary VCs were generated; proof-grade requires proved binary VCs"
                .to_string(),
            ["nonzero_required_vcs"],
        );
    } else if !all_required_vcs_proved {
        push_binary_cli_proof_grade_blocker(
            &mut blockers,
            &mut rejections,
            "binary-vc-proof-coverage-missing",
            "proof-grade-binary-verification",
            format!(
                "required binary VCs are not all proved: {proved_vcs}/{required_vcs} proved, {unproved_vcs} unproved, {non_proved_results} non-proof solver result(s)"
            ),
            ["all_required_vcs_proved"],
        );
    }
    if missing_checked_certificates > 0 {
        push_binary_cli_proof_grade_blocker(
            &mut blockers,
            &mut rejections,
            "checked-certificate-coverage-missing",
            "checked-certificate-coverage",
            format!(
                "checked proof certificates missing: {checked_certificates}/{required_vcs} checked, {missing_checked_certificates} missing"
            ),
            ["checked_certificate_artifact"],
        );
    }
    if solver_dispatches == 0 && required_vcs == 0 {
        push_binary_cli_proof_grade_blocker(
            &mut blockers,
            &mut rejections,
            "machine-replay-status-missing",
            "exact-machine-replay",
            "machine replay status missing: no solver dispatch or replay records were produced"
                .to_string(),
            ["machine_replay_transcript"],
        );
    } else if !replay_semantics_satisfied {
        let replay_semantics_detail = if replayed_vcs > 0 {
            format!(
                "replay semantics missing: {replay_semantics_satisfied_vcs}/{required_vcs} satisfied ({replayed_vcs} machine replayed, {exact_replay_slice_attested_vcs} selected-image byte/segment attested, {certificate_only_replay_semantics_vcs} checked UNSAT certificate-only), {missing_machine_replay} missing"
            )
        } else {
            format!(
                "replay semantics missing: {replay_semantics_satisfied_vcs}/{required_vcs} satisfied ({replayed_vcs} exact-byte replayed, {certificate_only_replay_semantics_vcs} checked UNSAT certificate-only), {missing_machine_replay} missing"
            )
        };
        push_binary_cli_proof_grade_blocker(
            &mut blockers,
            &mut rejections,
            "exact-machine-replay-missing",
            "exact-machine-replay",
            replay_semantics_detail,
            ["machine_replay_transcript"],
        );
    }
    if missing_exact_replay_slice_attestation > 0 {
        let blockers_detail = evidence.exact_replay_slice_attestation_blockers();
        let detail_suffix = if blockers_detail.is_empty() {
            String::new()
        } else {
            format!(": {}", blockers_detail.join("; "))
        };
        push_binary_cli_proof_grade_blocker(
            &mut blockers,
            &mut rejections,
            "exact-replay-slice-attestation-missing",
            "exact-replay-slice-attestation",
            format!(
                "exact replay selected-image byte/segment attestation accepted {exact_replay_slice_attested_vcs}/{replayed_vcs} replayed VC(s); proof-grade replay requires selected-image bytes and executable segment byte-range attestation{detail_suffix}"
            ),
            [
                "selected_image_bytes",
                "exact_replay_instruction_witness",
                "executable_segment_byte_range_attestation",
            ],
        );
    }
    if raw_solver_proof_bytes > 0 {
        push_binary_cli_proof_grade_blocker(
            &mut blockers,
            &mut rejections,
            "raw-solver-proof-bytes-audit-only",
            "raw-solver-proof-bytes",
            format!(
                "raw solver proof bytes present for {raw_solver_proof_bytes} VC(s), but raw solver bytes are not checked proof certificates and cannot upgrade trust"
            ),
            ["normalized_solver_proof_export", "checker_success"],
        );
    } else if !checked_certificates_for_all_required_vcs {
        push_binary_cli_proof_grade_blocker(
            &mut blockers,
            &mut rejections,
            "raw-solver-proof-bytes-not-sufficient",
            "raw-solver-proof-bytes",
            "raw solver proof bytes are not sufficient for proof-grade; checked proof certificates are required"
                .to_string(),
            ["checked_certificate_artifact"],
        );
    }
    if report.trust_level == "proof_grade" {
        if !checked_certificate_readback_for_all_required_vcs {
            push_binary_cli_proof_grade_blocker(
                &mut blockers,
                &mut rejections,
                "checked-certificate-readback-missing",
                "checked-certificate-readback",
                format!(
                    "checked certificate manifest readback accepted {checked_certificate_readback_rows}/{required_vcs} required VC(s) with rejected={readback_rejected_rows} unmatched={readback_unmatched_rows}; proof-grade release requires current manifest-backed readback with production checker evidence"
                ),
                [
                    "checked_certificate_manifest",
                    "checked_certificate_readback",
                    "production_checker_evidence",
                ],
            );
        }
        if !replay_attestation_for_all_required_vcs {
            push_binary_cli_proof_grade_blocker(
                &mut blockers,
                &mut rejections,
                "replay-attestation-missing",
                "replay-attestation",
                format!(
                    "replay attestation accepted {replay_attestation_rows}/{required_vcs} required VC(s); proof-grade release requires checked replay transcript and selected binary artifact digest identity"
                ),
                [
                    "machine_replay_transcript",
                    "binary_artifact_digest_identity",
                    "selected_image_digest_identity",
                ],
            );
        }
        if !source_backpropagation_handoff_for_all_required_vcs {
            push_binary_cli_proof_grade_blocker(
                &mut blockers,
                &mut rejections,
                "checked-certificate-source-backpropagation-handoff-missing",
                "checked-certificate-source-backpropagation-gate",
                format!(
                    "checked certificate source-backpropagation handoff accepted {source_backpropagation_handoff_rows}/{required_vcs} required VC(s); proof-grade release requires accepted source provenance, reconstruction, target validation, and source-backpropagation gate identity"
                ),
                [
                    "checked_certificate_source_backpropagation_gate",
                    "source_provenance_handoff",
                    "accepted_reconstruction_validation",
                    "target_semantic_validation",
                ],
            );
        }
    }
    if let Some(import) = &report.checked_certificate_import {
        if import.loader_failed() {
            match import.loader_blocker.as_ref() {
                Some(blocker) => {
                    push_binary_cli_proof_grade_blocker(
                        &mut blockers,
                        &mut rejections,
                        "checked-certificate-load-failed",
                        "checked-certificate-loader",
                        format!("checked certificate loader blocked: {}", blocker.detail),
                        ["loadable_checked_certificate_artifact"],
                    );
                }
                None => push_binary_cli_proof_grade_blocker(
                    &mut blockers,
                    &mut rejections,
                    "checked-certificate-load-failed",
                    "checked-certificate-loader",
                    "checked certificate loader blocked before certificate evidence could be loaded"
                        .to_string(),
                    ["loadable_checked_certificate_artifact"],
                ),
            }
        }
    }
    if let Some(production) = &report.checked_certificate_production {
        if production.is_blocked() {
            if production.blocker_records.is_empty() {
                // Compatibility for legacy serialized reports that predate
                // typed production blocker records.
                for blocker in &production.blockers {
                    push_binary_cli_proof_grade_blocker(
                        &mut blockers,
                        &mut rejections,
                        "checked-certificate-production-blocked",
                        "checked-certificate-production",
                        format!("checked certificate production blocked: {blocker}"),
                        ["production_checker_evidence"],
                    );
                }
            } else {
                // Preserve the machine-readable production blocker identity.
                // Gate consumers must never infer state by matching wording in
                // the human diagnostic, which is intentionally free to improve.
                for record in &production.blocker_records {
                    let detail =
                        format!("checked certificate production blocked: {}", record.detail);
                    rejections.push(detail.clone());
                    blockers.push(BinaryCliProofGradeBlockerReport {
                        code: record.code.clone(),
                        stage: record.stage.clone(),
                        feature: "checked-certificate-production".to_string(),
                        detail,
                        evidence_required: record.evidence_required.clone(),
                    });
                }
            }
        }
    }

    let accepted = blockers.is_empty();
    BinaryCliProofGradeGateReport {
        accepted,
        status: if accepted { "accepted".into() } else { "rejected".into() },
        final_trust_level: report.trust_level.clone(),
        unsupported_ledger_empty,
        all_required_vcs_proved,
        checked_certificates_for_all_required_vcs,
        checked_certificate_readback_for_all_required_vcs,
        full_replay_coverage,
        replay_semantics_satisfied,
        exact_replay_slice_attestation_for_replayed_vcs,
        replay_attestation_for_all_required_vcs,
        source_backpropagation_handoff_for_all_required_vcs,
        required_vcs,
        solver_dispatches,
        proved_vcs,
        unproved_vcs,
        non_proved_results,
        checked_certificates,
        missing_checked_certificates,
        checked_certificate_readback_rows,
        replayed_vcs,
        exact_replay_slice_attested_vcs,
        missing_exact_replay_slice_attestation,
        certificate_only_replay_semantics_vcs,
        replay_semantics_satisfied_vcs,
        missing_machine_replay,
        replay_attestation_rows,
        source_backpropagation_handoff_rows,
        raw_solver_proof_bytes,
        raw_solver_proof_bytes_sufficient,
        blockers,
        rejections,
    }
}

fn push_binary_cli_proof_grade_blocker(
    blockers: &mut Vec<BinaryCliProofGradeBlockerReport>,
    rejections: &mut Vec<String>,
    code: &'static str,
    feature: &'static str,
    detail: impl Into<String>,
    evidence_required: impl IntoIterator<Item = &'static str>,
) {
    let detail = detail.into();
    rejections.push(detail.clone());
    blockers.push(BinaryCliProofGradeBlockerReport {
        code: code.to_string(),
        stage: "targo-trust::verify-binary-release-gate".to_string(),
        feature: feature.to_string(),
        detail,
        evidence_required: evidence_required.into_iter().map(str::to_string).collect(),
    });
}

fn verify_binary_checked_certificate_release_readback_rows(report: &BinaryVerifyReport) -> usize {
    report
        .checked_certificate_import
        .as_ref()
        .map(|import| {
            import
                .artifacts
                .iter()
                .filter(|artifact| verify_binary_checked_certificate_release_readback_row(artifact))
                .count()
        })
        .unwrap_or(0)
}

fn verify_binary_checked_certificate_release_readback_row(
    artifact: &CheckedCertificateArtifactImportRecord,
) -> bool {
    artifact.status == "imported"
        && checked_certificate_import_record_is_production_manifest_row(artifact)
        && checked_certificate_import_record_is_accepted_evidence(artifact)
}

fn verify_binary_replay_attestation_rows(report: &BinaryVerifyReport) -> usize {
    report
        .checked_certificate_import
        .as_ref()
        .map(|import| {
            import
                .artifacts
                .iter()
                .filter(|artifact| {
                    artifact.status == "imported"
                        && checked_certificate_import_record_is_production_manifest_row(artifact)
                        && artifact.replay_digest_identity.status == "accepted"
                })
                .count()
        })
        .unwrap_or(0)
}

fn verify_binary_source_backpropagation_handoff_rows(report: &BinaryVerifyReport) -> usize {
    report
        .checked_certificate_import
        .as_ref()
        .map(|import| {
            import
                .artifacts
                .iter()
                .filter(|artifact| {
                    artifact.status == "imported"
                        && checked_certificate_import_record_is_production_manifest_row(artifact)
                        && artifact
                            .source_backpropagation_gate_sha256
                            .as_deref()
                            .is_some_and(trust_types::digest::is_stable_sha256_hex)
                        && checked_certificate_source_backpropagation_gate_allows_source_rewrites(
                            &artifact.source_backpropagation_gate,
                        )
                })
                .count()
        })
        .unwrap_or(0)
}

fn verify_binary_checked_certificate_readback_stale_counts(
    report: &BinaryVerifyReport,
) -> (usize, usize, bool) {
    report
        .checked_certificate_import
        .as_ref()
        .map(|import| {
            (import.rejected_artifacts, import.unmatched_artifacts, import.loader_failed())
        })
        .unwrap_or((0, 0, false))
}

fn build_binary_verify_proof_evidence_report(
    report: &BinaryVerifyReport,
) -> BinaryVerifyProofEvidenceReport {
    let verification =
        build_binary_verification_report(&binary_verify_shared_verification_summary(report));
    BinaryVerifyProofEvidenceReport {
        total_vcs: verification.total_vcs,
        solver_dispatches: verification.solver_dispatches.len(),
        solver_dispatch_status_counts: verification.vc_status_counts,
        replay: verification.replay,
        replay_status_counts: verification.replay_status_counts,
        raw_solver_proof_byte_count: verification.certificate_checks.raw_solver_proof_byte_count,
        checked_certificate_coverage: verification.certificate_checks,
        proof_grade_gate: verification.proof_grade_gate,
    }
}

fn build_checked_certificate_evidence_summary(
    report: &BinaryVerifyReport,
) -> CheckedCertificateEvidenceSummaryReport {
    let proof_evidence = build_binary_verify_proof_evidence_report(report);
    let coverage = &proof_evidence.checked_certificate_coverage;
    let import = report.checked_certificate_import.as_ref();
    let production = report.checked_certificate_production.as_ref();
    let checked_artifact_rows = import.map(|report| report.artifacts.len()).unwrap_or(0);
    let imported_artifact_rows = import.map(|report| report.imported).unwrap_or(0);
    let rejected_artifact_rows = import.map(|report| report.rejected_artifacts).unwrap_or(0);
    let unmatched_artifact_rows = import.map(|report| report.unmatched_artifacts).unwrap_or(0);
    let loader_failed = import.is_some_and(CheckedCertificateImportReport::loader_failed);
    let normalized_solver_proof_exports =
        production.map(|report| report.proof_export_candidates).unwrap_or(0);
    let production_checker_successes = production
        .map(|report| {
            report
                .certificate_check_records
                .iter()
                .filter(|record| record.status == "checked")
                .count()
        })
        .unwrap_or(0);
    let checker_successes = imported_artifact_rows + production_checker_successes;
    let artifacts = import.map(|report| report.artifacts.clone()).unwrap_or_default();
    let unsupported_ledgers_empty = report.unsupported == 0;
    let accepted_certificates =
        accepted_checked_certificate_evidence_records(import, unsupported_ledgers_empty);
    let accepted_certificate_rows = accepted_certificates.len();
    let proof_grade_release_transcript_rows =
        checked_certificate_import_proof_grade_release_transcript_rows(
            import,
            unsupported_ledgers_empty,
        );
    let loader = checked_certificate_evidence_loader_report(import, production);
    let mut blockers = Vec::new();
    let rejected_production_manifest_rows = artifacts
        .iter()
        .filter(|artifact| artifact.status == "imported")
        .filter(|artifact| checked_certificate_import_record_is_production_manifest_row(artifact))
        .filter(|artifact| !checked_certificate_import_record_is_accepted_evidence(artifact))
        .count();
    let rejected_release_transcript_binding_rows = artifacts
        .iter()
        .filter(|artifact| artifact.status == "imported")
        .filter(|artifact| checked_certificate_import_record_is_production_manifest_row(artifact))
        .filter(|artifact| {
            checked_certificate_import_release_transcript_binding(artifact).status != "accepted"
        })
        .count();
    let incomplete_release_transcript_rows = artifacts
        .iter()
        .filter(|artifact| artifact.status == "imported")
        .filter(|artifact| checked_certificate_import_record_is_production_manifest_row(artifact))
        .filter(|artifact| {
            !checked_certificate_import_proof_grade_release_transcript_row(
                artifact,
                unsupported_ledgers_empty,
            )
            .accepted
        })
        .count();

    if let Some(blocker) =
        import.and_then(|report| report.loader_blocker.as_ref()).map(loader_blocker_report)
    {
        blockers.push(blocker);
    }

    if coverage.required_vcs > 0 && coverage.missing_checked_certificates > 0 {
        blockers.push(CheckedCertificateEvidenceBlockerReport {
            code: "checked-certificate-coverage-missing".to_string(),
            stage: "targo-trust::verify-binary".to_string(),
            detail: format!(
                "checked proof certificates missing: {}/{} checked, {} missing",
                coverage.checked_certificates,
                coverage.required_vcs,
                coverage.missing_checked_certificates
            ),
            evidence_required: vec!["checked_certificate_artifact".to_string()],
        });
    }
    if coverage.raw_solver_proof_bytes > 0 {
        blockers.push(CheckedCertificateEvidenceBlockerReport {
            code: "raw-solver-proof-bytes-audit-only".to_string(),
            stage: "targo-trust::verify-binary".to_string(),
            detail: format!(
                "raw solver proof bytes present for {} dispatch(es), but raw bytes are audit-only and cannot satisfy checked-certificate coverage",
                coverage.raw_solver_proof_bytes
            ),
            evidence_required: vec![
                "normalized_solver_proof_export".to_string(),
                "checker_success".to_string(),
            ],
        });
    }
    if rejected_artifact_rows > 0 {
        blockers.push(CheckedCertificateEvidenceBlockerReport {
            code: "checked-certificate-import-rejected".to_string(),
            stage: "targo-trust::verify-binary-import".to_string(),
            detail: format!(
                "{rejected_artifact_rows} checked certificate artifact row(s) were rejected during import"
            ),
            evidence_required: vec!["accepted_checked_certificate_artifact".to_string()],
        });
    }
    if rejected_production_manifest_rows > 0 {
        blockers.push(CheckedCertificateEvidenceBlockerReport {
            code: "checked-certificate-production-manifest-row-not-accepted".to_string(),
            stage: "targo-trust::verify-binary-import".to_string(),
            detail: format!(
                "{rejected_production_manifest_rows} production checked-certificate manifest row(s) were read back but lack aligned external checker/readback evidence, VC identity, binary artifact digest identity, replay digest identity, source gate identity, or proof metadata digest"
            ),
            evidence_required: vec![
                "external_checker_readback_evidence".to_string(),
                "checked_certificate_vc_identity".to_string(),
                "binary_artifact_digest_identity".to_string(),
                "replay_digest_identity".to_string(),
                "checked_certificate_source_backpropagation_gate_identity".to_string(),
                "proof_export_metadata_digest".to_string(),
            ],
        });
    }
    if rejected_release_transcript_binding_rows > 0 {
        blockers.push(CheckedCertificateEvidenceBlockerReport {
            code: "release-transcript-binding-missing".to_string(),
            stage: "targo-trust::verify-binary-import".to_string(),
            detail: format!(
                "{rejected_release_transcript_binding_rows} production checked-certificate manifest row(s) lack accepted release transcript binding"
            ),
            evidence_required: release_transcript_binding_evidence_required(false),
        });
    }
    if incomplete_release_transcript_rows > 0 {
        blockers.push(CheckedCertificateEvidenceBlockerReport {
            code: "proof-grade-release-transcript-row-incomplete".to_string(),
            stage: "targo-trust::verify-binary-import".to_string(),
            detail: format!(
                "{incomplete_release_transcript_rows} production checked-certificate manifest row(s) lack accepted proof-grade release transcript rows"
            ),
            evidence_required: proof_grade_release_transcript_row_evidence_required(false),
        });
    }
    if checked_artifact_rows == 0
        && coverage.required_vcs > 0
        && coverage.missing_checked_certificates > 0
    {
        blockers.push(CheckedCertificateEvidenceBlockerReport {
            code: "checked-certificate-loader-not-run".to_string(),
            stage: "targo-trust::verify-binary-import".to_string(),
            detail:
                "no checked certificate artifact rows were loaded for this verify-binary report"
                    .to_string(),
            evidence_required: vec!["--checked-cert-artifact".to_string()],
        });
    }
    if let Some(production) = production {
        if production.is_blocked() {
            blockers.extend(production.blocker_records.iter().map(|record| {
                CheckedCertificateEvidenceBlockerReport {
                    code: record.code.clone(),
                    stage: record.stage.clone(),
                    detail: record.detail.clone(),
                    evidence_required: record.evidence_required.clone(),
                }
            }));
        }
    }

    let status = if loader_failed {
        "blocked"
    } else if coverage.required_vcs == 0 {
        "not_required"
    } else if coverage.checked_certificates_satisfy_coverage
        && rejected_artifact_rows == 0
        && blockers.is_empty()
    {
        "accepted"
    } else {
        "blocked"
    };

    CheckedCertificateEvidenceSummaryReport {
        status: status.to_string(),
        required_vcs: coverage.required_vcs,
        solver_dispatches: coverage.solver_dispatches,
        checked_artifact_rows,
        accepted_certificate_rows,
        imported_artifact_rows,
        rejected_artifact_rows,
        unmatched_artifact_rows,
        normalized_solver_proof_exports,
        checker_successes,
        checked_certificates: coverage.checked_certificates,
        missing_checked_certificates: coverage.missing_checked_certificates,
        raw_solver_proof_bytes: coverage.raw_solver_proof_bytes,
        raw_solver_proof_byte_count: coverage.raw_solver_proof_byte_count,
        raw_solver_proof_bytes_sufficient: coverage.raw_solver_proof_bytes_satisfy_coverage,
        loader,
        artifacts,
        accepted_certificates,
        proof_grade_release_transcript_rows,
        blockers,
    }
}

fn checked_certificate_import_record_is_production_manifest_row(
    artifact: &CheckedCertificateArtifactImportRecord,
) -> bool {
    artifact.manifest_identity_sha256.is_some()
        || artifact.production_checker_evidence_sha256.is_some()
}

fn checked_certificate_import_record_is_accepted_evidence(
    artifact: &CheckedCertificateArtifactImportRecord,
) -> bool {
    if artifact.status != "imported" {
        return false;
    }
    if !checked_certificate_import_record_is_production_manifest_row(artifact) {
        return true;
    }

    trust_types::digest::is_stable_sha256_hex(&artifact.vc_sha256)
        && trust_types::digest::is_stable_sha256_hex(&artifact.origin_sha256)
        && trust_types::digest::is_stable_sha256_hex(&artifact.certificate_sha256)
        && trust_types::digest::is_stable_sha256_hex(&artifact.proof_export_sha256)
        && artifact.manifest_identity_sha256.as_deref().is_some_and(trust_types::digest::is_stable_sha256_hex)
        && artifact
            .source_backpropagation_gate_sha256
            .as_deref()
            .is_some_and(trust_types::digest::is_stable_sha256_hex)
        && artifact
            .production_checker_evidence_sha256
            .as_deref()
            .is_some_and(trust_types::digest::is_stable_sha256_hex)
        && artifact.binary_artifact_digest_identity.digest_identity_blockers().is_empty()
        && artifact.replay_digest_identity.status == "accepted"
        && checked_certificate_import_release_transcript_binding(artifact).status == "accepted"
}


fn checked_certificate_import_proof_grade_release_transcript_rows(
    import: Option<&CheckedCertificateImportReport>,
    unsupported_ledgers_empty: bool,
) -> Vec<ProofGradeReleaseTranscriptRowReport> {
    import
        .map(|report| {
            report
                .artifacts
                .iter()
                .filter(|artifact| artifact.status == "imported")
                .map(|artifact| {
                    checked_certificate_import_proof_grade_release_transcript_row(
                        artifact,
                        unsupported_ledgers_empty,
                    )
                })
                .collect()
        })
        .unwrap_or_default()
}

fn accepted_checked_certificate_evidence_records(
    import: Option<&CheckedCertificateImportReport>,
    unsupported_ledgers_empty: bool,
) -> Vec<CheckedCertificateAcceptedEvidenceRecord> {
    import
        .map(|report| {
            report
                .artifacts
                .iter()
                .filter(|artifact| checked_certificate_import_record_is_accepted_evidence(artifact))
                .map(|artifact| {
                    let release_transcript_binding =
                        checked_certificate_import_release_transcript_binding(artifact);
                    let proof_grade_release_transcript_row =
                        checked_certificate_import_proof_grade_release_transcript_row(
                            artifact,
                            unsupported_ledgers_empty,
                        );
                    CheckedCertificateAcceptedEvidenceRecord {
                        source: "checked_certificate_import".to_string(),
                        status: "accepted".to_string(),
                        artifact_path: artifact.artifact_path.clone(),
                        dispatch_id: artifact.dispatch_id.clone(),
                        certificate_sha256: artifact.certificate_sha256.clone(),
                        checker: artifact.checker.clone(),
                        checker_version: artifact.checker_version.clone(),
                        format: artifact.format.clone(),
                        checked_at_unix_ms: artifact.checked_at_unix_ms,
                        vc_sha256: artifact.vc_sha256.clone(),
                        origin_sha256: artifact.origin_sha256.clone(),
                        proof_export_sha256: nonempty_digest(&artifact.proof_export_sha256),
                        source_backpropagation_gate: artifact.source_backpropagation_gate.clone(),
                        manifest_identity_sha256: artifact.manifest_identity_sha256.clone(),
                        source_backpropagation_gate_sha256: artifact
                            .source_backpropagation_gate_sha256
                            .clone(),
                        replay_transcript_digest: artifact.replay_transcript_digest.clone(),
                        replay_digest_identity: artifact.replay_digest_identity.clone(),
                        release_transcript_binding,
                        proof_grade_release_transcript_row,
                        production_checker_evidence_status: artifact
                            .production_checker_evidence_status
                            .clone(),
                        production_checker_evidence_sha256: artifact
                            .production_checker_evidence_sha256
                            .clone(),
                    }
                })
                .collect()
        })
        .unwrap_or_default()
}

fn loader_blocker_report(
    blocker: &CheckedCertificateLoaderBlockerRecord,
) -> CheckedCertificateEvidenceBlockerReport {
    CheckedCertificateEvidenceBlockerReport {
        code: blocker.code.clone(),
        stage: blocker.stage.clone(),
        detail: blocker.detail.clone(),
        evidence_required: blocker.evidence_required.clone(),
    }
}

fn checked_certificate_evidence_loader_report(
    import: Option<&CheckedCertificateImportReport>,
    production: Option<&CheckedCertificateProductionReport>,
) -> CheckedCertificateEvidenceLoaderReport {
    if let Some(import) = import {
        let status = if import.loader_failed() {
            "load_failed"
        } else if import.rejected_artifacts > 0 {
            "loaded_with_rejections"
        } else if import.loaded_artifacts > 0 {
            "loaded"
        } else {
            "loaded_empty"
        };
        return CheckedCertificateEvidenceLoaderReport {
            status: status.to_string(),
            implementation: "targo-trust::verify-binary-import".to_string(),
            requested_artifacts: import.requested_artifacts,
            requested_manifests: import.requested_manifests,
            loaded_artifacts: import.loaded_artifacts,
            imported_artifacts: import.imported,
            rejected_artifacts: import.rejected_artifacts,
            unmatched_artifacts: import.unmatched_artifacts,
            dispatches_missing_canonical_binding: import.dispatches_missing_canonical_binding,
            blocker: import.loader_blocker.as_ref().map(loader_blocker_report),
            diagnostics: import.diagnostics.clone(),
        };
    }

    let status = match production {
        Some(production) if production.is_blocked() => "blocked",
        Some(production) if production.exported_artifacts > 0 => "exported",
        Some(_) => "requested",
        None => "not_requested",
    };
    CheckedCertificateEvidenceLoaderReport {
        status: status.to_string(),
        implementation: "targo-trust::verify-binary-import".to_string(),
        requested_artifacts: 0,
        requested_manifests: 0,
        loaded_artifacts: 0,
        imported_artifacts: 0,
        rejected_artifacts: 0,
        unmatched_artifacts: 0,
        dispatches_missing_canonical_binding: 0,
        blocker: None,
        diagnostics: Vec::new(),
    }
}

fn binary_verify_shared_verification_summary(
    report: &BinaryVerifyReport,
) -> BinaryVerificationSummary {
    let required_vcs = binary_verify_required_vcs(report);
    let mut summary = BinaryVerificationSummary {
        total_vcs: required_vcs,
        trust_level: binary_verify_shared_trust_level(report),
        solver_dispatch: report.proof_evidence.solver_dispatch.clone(),
        unsupported_ledger: unsupported_ledger_from_verify_binary_report(report),
        ..Default::default()
    };

    for dispatch in &summary.solver_dispatch {
        match (dispatch.status, dispatch.query_semantics) {
            (SolverDispatchStatus::Unsat, SolverQuerySemantics::SatIsCounterexample) => {
                summary.proved += 1;
            }
            (SolverDispatchStatus::Sat, SolverQuerySemantics::SatIsCounterexample) => {
                summary.failed += 1;
            }
            (SolverDispatchStatus::Timeout, _) => summary.timeout += 1,
            (SolverDispatchStatus::Unsupported, _) => summary.unsupported += 1,
            (SolverDispatchStatus::Rejected, _) => summary.rejected += 1,
            _ => summary.unknown += 1,
        }
    }

    let undispatched_vcs = required_vcs.saturating_sub(summary.solver_dispatch.len());
    summary.unknown = summary.unknown.saturating_add(undispatched_vcs);
    summary.unsupported =
        summary.unsupported.saturating_add(summary.unsupported_ledger.records.len());
    summary.replay = aggregate_verify_binary_replay(&summary.solver_dispatch);
    summary.status = binary_verify_shared_status(&summary);
    summary
}

fn binary_verify_shared_trust_level(report: &BinaryVerifyReport) -> TrustLevel {
    match trust_level_from_binary_report_label(&report.trust_level) {
        TrustLevel::ProofGrade if build_binary_cli_proof_grade_gate(report).accepted => {
            TrustLevel::ProofGrade
        }
        TrustLevel::ProofGrade => TrustLevel::Partial,
        trust_level => trust_level,
    }
}

fn binary_verify_required_vcs(report: &BinaryVerifyReport) -> usize {
    if report.proof_evidence.required_vcs == 0 && report.vcs > 0 {
        report.vcs
    } else {
        report.proof_evidence.required_vcs
    }
}

fn unsupported_ledger_from_verify_binary_report(report: &BinaryVerifyReport) -> UnsupportedLedger {
    UnsupportedLedger {
        records: report
            .unsupported_items
            .iter()
            .map(|item| UnsupportedRecord {
                stage: "targo trust verify-binary".to_string(),
                architecture: report.architecture.clone(),
                origin: None,
                opcode: None,
                operand: None,
                feature: item.clone(),
            })
            .collect(),
    }
}

fn trust_level_from_binary_report_label(label: &str) -> TrustLevel {
    match label {
        "proof_grade" => TrustLevel::ProofGrade,
        "exploratory" => TrustLevel::Exploratory,
        "rejected" => TrustLevel::Rejected,
        _ => TrustLevel::Partial,
    }
}

fn aggregate_verify_binary_replay(dispatches: &[SolverDispatchRecord]) -> ReplayStatus {
    if dispatches.is_empty() {
        ReplayStatus::NotAttempted
    } else if dispatches.iter().any(|dispatch| dispatch.replay == ReplayStatus::Failed) {
        ReplayStatus::Failed
    } else if dispatches.iter().any(|dispatch| dispatch.replay == ReplayStatus::Spurious) {
        ReplayStatus::Spurious
    } else if dispatches.iter().any(|dispatch| dispatch.replay == ReplayStatus::NotAttempted) {
        ReplayStatus::NotAttempted
    } else {
        ReplayStatus::Replayed
    }
}

fn binary_verify_shared_status(summary: &BinaryVerificationSummary) -> BinaryVerificationStatus {
    let total = summary.total_vcs;
    if total == 0 {
        if summary.rejected > 0 {
            return BinaryVerificationStatus::Rejected;
        }
        if summary.unsupported > 0 {
            return BinaryVerificationStatus::Unsupported;
        }
        return BinaryVerificationStatus::NotRun;
    }

    let non_zero_categories = [
        summary.proved,
        summary.failed,
        summary.unknown,
        summary.timeout,
        summary.unsupported,
        summary.rejected,
    ]
    .into_iter()
    .filter(|count| *count > 0)
    .count();

    if non_zero_categories > 1 {
        return BinaryVerificationStatus::Mixed;
    }

    if summary.proved == total {
        BinaryVerificationStatus::Proved
    } else if summary.failed == total {
        BinaryVerificationStatus::Refuted
    } else if summary.timeout == total {
        BinaryVerificationStatus::Timeout
    } else if summary.unsupported == total {
        BinaryVerificationStatus::Unsupported
    } else if summary.rejected == total {
        BinaryVerificationStatus::Rejected
    } else {
        BinaryVerificationStatus::Unknown
    }
}

fn binary_verify_counts_label(counts: &BTreeMap<String, usize>) -> String {
    if counts.is_empty() {
        return "none".to_string();
    }

    counts.iter().map(|(status, count)| format!("{status}={count}")).collect::<Vec<_>>().join(" ")
}

fn format_solver_location(location: &SourceSpan) -> Option<String> {
    if location == &SourceSpan::default() {
        return None;
    }
    if let Some(address) = location.binary_address_value() {
        return Some(hex_addr(address));
    }
    Some(format!("{}:{}:{}", location.file, location.line_start, location.col_start))
}

fn is_unsupported_lift_error(error: &LiftError) -> bool {
    matches!(
        error,
        LiftError::BinaryParserUnavailable
            | LiftError::UnsupportedMachine(_)
            | LiftError::UnsupportedBinaryFormat { .. }
            | LiftError::Disasm { .. }
            | LiftError::EmptyBlock { .. }
            | LiftError::UnsupportedSemantics { .. }
            | LiftError::UnsupportedEffect { .. }
            | LiftError::UnresolvedControlFlow { .. }
            | LiftError::MissingSuccessor { .. }
            | LiftError::UnrepresentableCfg { .. }
    )
}

fn count_vc_kinds<'a>(kinds: impl IntoIterator<Item = &'a VcKind>) -> Vec<BinaryVcKindCount> {
    let mut counts = BTreeMap::<String, usize>::new();
    for kind in kinds {
        *counts.entry(vc_kind_key(kind)).or_insert(0) += 1;
    }
    counts.into_iter().map(|(kind, count)| BinaryVcKindCount { kind, count }).collect()
}

fn vc_kind_key(kind: &VcKind) -> String {
    match kind {
        VcKind::ArithmeticOverflow { op, .. } => {
            format!("arithmetic_overflow:{}", debug_tag(op))
        }
        VcKind::ShiftOverflow { op, .. } => format!("shift_overflow:{}", debug_tag(op)),
        VcKind::DivisionByZero => "division_by_zero".to_string(),
        VcKind::RemainderByZero => "remainder_by_zero".to_string(),
        VcKind::IndexOutOfBounds => "index_out_of_bounds".to_string(),
        VcKind::SliceBoundsCheck => "slice_bounds_check".to_string(),
        VcKind::Assertion { message } => assertion_vc_kind_key(message),
        VcKind::Precondition { .. } => "precondition".to_string(),
        VcKind::Postcondition => "postcondition".to_string(),
        VcKind::CastOverflow { .. } => "cast_overflow".to_string(),
        VcKind::NegationOverflow { .. } => "negation_overflow".to_string(),
        VcKind::Unreachable => "unreachable".to_string(),
        VcKind::FloatDivisionByZero => "float_division_by_zero".to_string(),
        VcKind::FloatOverflowToInfinity { op, .. } => {
            format!("float_overflow_to_infinity:{}", debug_tag(op))
        }
        VcKind::UnsafeOperation { .. } => "unsafe_operation".to_string(),
        VcKind::BinaryAbiContradiction { .. } => "binary_abi_contradiction".to_string(),
        VcKind::FfiBoundaryViolation { .. } => "ffi_boundary_violation".to_string(),
        VcKind::UseAfterFree => "use_after_free".to_string(),
        VcKind::DoubleFree => "double_free".to_string(),
        VcKind::AliasingViolation { .. } => "aliasing_violation".to_string(),
        VcKind::LifetimeViolation => "lifetime_violation".to_string(),
        _ => normalize_vc_kind_description(&kind.description()),
    }
}

fn assertion_vc_kind_key(message: &str) -> String {
    if message.starts_with("binary memory write OOB") {
        "binary_memory_write_oob".to_string()
    } else if message.starts_with("binary memory read invalid") {
        "binary_memory_read_invalid".to_string()
    } else if message.starts_with("binary memory access invalid") {
        "binary_memory_access_invalid".to_string()
    } else if message.starts_with("stack pointer not restored") {
        "binary_stack_pointer_restoration".to_string()
    } else {
        "assertion".to_string()
    }
}

fn normalize_vc_kind_description(description: &str) -> String {
    description
        .chars()
        .map(|ch| if ch.is_ascii_alphanumeric() { ch.to_ascii_lowercase() } else { '_' })
        .collect::<String>()
        .split('_')
        .filter(|part| !part.is_empty())
        .collect::<Vec<_>>()
        .join("_")
}

fn debug_tag(value: &impl std::fmt::Debug) -> String {
    normalize_vc_kind_description(&format!("{value:?}"))
}

fn build_lift_report(
    binary_path: &Path,
    entry: Option<u64>,
    all_functions: bool,
    strict: bool,
    output: LiftReportInput,
) -> BinaryLiftReport {
    let functions = output
        .functions
        .into_iter()
        .map(|function| BinaryLiftFunctionReport {
            name: function.name,
            entry: function.entry.map(hex_addr),
            blocks: function.blocks,
            statements: function.statements,
            vcs: function.vcs,
            instruction_provenance: function.instruction_provenance,
        })
        .collect::<Vec<_>>();
    let blocks = functions.iter().map(|function| function.blocks).sum();
    let statements = functions.iter().map(|function| function.statements).sum();
    let vcs = functions.iter().map(|function| function.vcs).sum();
    let unsupported = output.unsupported.len();
    let failures = output.failures.len();
    let status = if failures > 0 {
        BinaryLiftStatus::Failed
    } else if unsupported > 0 {
        BinaryLiftStatus::Incomplete
    } else {
        BinaryLiftStatus::Ok
    };

    BinaryLiftReport {
        binary: binary_path.display().to_string(),
        format: output.format,
        architecture: output.architecture,
        selection: binary_selection_label(entry, all_functions).to_string(),
        entry: entry.map(hex_addr),
        binary_entry: output.binary_entry.map(hex_addr),
        strict,
        status,
        functions_lifted: functions.len(),
        blocks,
        statements,
        vcs,
        unsupported,
        failures,
        functions,
        unsupported_items: output.unsupported,
        failure_items: output.failures,
    }
}

fn lift_should_fail(report: &BinaryLiftReport) -> bool {
    report.failures > 0
        || report.strict && report.unsupported > 0
        || report.unsupported > 0 && report.functions_lifted == 0
}

fn build_verify_binary_report(
    binary_path: &Path,
    entry: Option<u64>,
    all_functions: bool,
    strict: bool,
    output: VerifyBinaryReportInput,
) -> BinaryVerifyReport {
    let functions = output
        .functions
        .into_iter()
        .map(|function| BinaryVerifyFunctionReport {
            name: function.name,
            entry: function.entry.map(hex_addr),
            blocks: function.blocks,
            statements: function.statements,
            vcs: function.vcs,
            vc_counts: function.vc_counts,
        })
        .collect::<Vec<_>>();
    let blocks = functions.iter().map(|function| function.blocks).sum();
    let statements = functions.iter().map(|function| function.statements).sum();
    let vcs = functions.iter().map(|function| function.vcs).sum();
    let vc_counts =
        merge_vc_counts(functions.iter().flat_map(|function| function.vc_counts.iter()));
    let unsupported = output.unsupported.len();
    let failures = output.failures.len();
    let status = if failures > 0 {
        BinaryLiftStatus::Failed
    } else if unsupported > 0 {
        BinaryLiftStatus::Incomplete
    } else {
        BinaryLiftStatus::Ok
    };

    let solver_results = summarize_solver_results_for_vcs(&output.solver_results, vcs);
    let verification_status = verification_status_for_binary_report(status, &solver_results, vcs);
    let trust_level = binary_report_trust_level(status, &solver_results, vcs);

    BinaryVerifyReport {
        binary: binary_path.display().to_string(),
        format: output.format,
        architecture: output.architecture,
        selection: binary_selection_label(entry, all_functions).to_string(),
        entry: entry.map(hex_addr),
        binary_entry: output.binary_entry.map(hex_addr),
        strict,
        status,
        verification_status,
        trust_level,
        solver_results,
        functions_analyzed: functions.len(),
        blocks,
        statements,
        vcs,
        vc_counts,
        unsupported,
        failures,
        functions,
        unsupported_items: output.unsupported,
        failure_items: output.failures,
        solver_result_items: output.solver_results,
        checked_certificate_import: None,
        checked_certificate_production: None,
        proof_evidence: output.proof_evidence,
    }
}

fn summarize_solver_results(results: &[BinarySolverResultReport]) -> BinarySolverSummary {
    if results.is_empty() {
        return BinarySolverSummary::not_run();
    }

    let mut summary = BinarySolverSummary {
        status: "mixed".into(),
        total: results.len(),
        proved: 0,
        failed: 0,
        unknown: 0,
        timeout: 0,
    };
    for result in results {
        match result.status.as_str() {
            "proved" => summary.proved += 1,
            "failed" => summary.failed += 1,
            "timeout" => summary.timeout += 1,
            _ => summary.unknown += 1,
        }
    }
    summary.status = if summary.failed > 0 {
        "failed".into()
    } else if summary.timeout > 0 {
        "timeout".into()
    } else if summary.unknown > 0 {
        "unknown".into()
    } else {
        "proved".into()
    };
    summary
}

fn summarize_solver_results_for_vcs(
    results: &[BinarySolverResultReport],
    generated_vcs: usize,
) -> BinarySolverSummary {
    if results.is_empty() && generated_vcs > 0 {
        return BinarySolverSummary {
            status: "unknown".into(),
            total: generated_vcs,
            proved: 0,
            failed: 0,
            unknown: generated_vcs,
            timeout: 0,
        };
    }
    summarize_solver_results(results)
}

fn verification_status_for_binary_report(
    lift_status: BinaryLiftStatus,
    solver_results: &BinarySolverSummary,
    generated_vcs: usize,
) -> String {
    if lift_status == BinaryLiftStatus::Failed {
        "failed".into()
    } else if generated_vcs == 0 {
        "not_run".into()
    } else {
        solver_results.status.clone()
    }
}

fn binary_report_trust_level(
    lift_status: BinaryLiftStatus,
    _solver_results: &BinarySolverSummary,
    _generated_vcs: usize,
) -> String {
    if lift_status == BinaryLiftStatus::Failed { "rejected".into() } else { "partial".into() }
}

#[cfg(test)]
fn build_decompile_report(
    binary_path: &Path,
    entry: Option<u64>,
    all_functions: bool,
    strict: bool,
    target: DecompileTarget,
    result: Result<DecompilationArtifact, DecompileError>,
) -> DecompileReport {
    // Production callers thread metadata from the already-read binary bytes.
    // This compatibility helper exists only for unit fixtures that predate the
    // byte-snapshot parameter, so a stable bounded test read preserves their
    // metadata assertions without reintroducing a production TOCTOU path.
    let binary_metadata =
        read_binary_artifact(binary_path).ok().and_then(|bytes| sniff_binary_metadata(&bytes));
    build_decompile_report_with_error_metadata(
        binary_path,
        entry,
        all_functions,
        strict,
        target,
        binary_metadata,
        result,
    )
}

fn build_decompile_report_with_error_metadata(
    binary_path: &Path,
    entry: Option<u64>,
    all_functions: bool,
    strict: bool,
    target: DecompileTarget,
    binary_metadata: Option<DecompileErrorMetadata>,
    result: Result<DecompilationArtifact, DecompileError>,
) -> DecompileReport {
    match result {
        Ok(artifact) => build_decompile_report_from_artifact(
            binary_path,
            entry,
            all_functions,
            strict,
            target,
            artifact,
        ),
        Err(error) => build_decompile_report_from_error(
            binary_path,
            entry,
            all_functions,
            strict,
            target,
            binary_metadata,
            error,
        ),
    }
}

fn build_decompile_report_from_artifact(
    binary_path: &Path,
    entry: Option<u64>,
    all_functions: bool,
    strict: bool,
    target: DecompileTarget,
    artifact: DecompilationArtifact,
) -> DecompileReport {
    let selected_output = artifact.reconstruction.outputs.first();
    let production_proof_grade_evidence =
        decompile_production_proof_grade_evidence_from_artifact(&artifact);
    let binary_evidence = decompile_binary_evidence_from_artifact(&artifact);
    let functions = artifact
        .functions
        .iter()
        .map(|function| {
            let blocks = function.lifted.as_ref().map_or(0, |lifted| lifted.body.blocks.len());
            let statements = function
                .lifted
                .as_ref()
                .map_or(0, |lifted| lifted.body.blocks.iter().map(|block| block.stmts.len()).sum());
            DecompileFunctionReport {
                name: function.name.clone(),
                entry: hex_addr(function.entry),
                blocks,
                instructions: function.coverage.instructions_lifted,
                statements,
                memory_facts: function.memory_accesses.len(),
                unsupported: function.unsupported.records.len(),
                instruction_provenance: function.instruction_provenance.clone(),
            }
        })
        .collect::<Vec<_>>();
    let blocks = functions.iter().map(|function| function.blocks).sum();
    let instructions = functions.iter().map(|function| function.instructions).sum();
    let statements = functions.iter().map(|function| function.statements).sum();
    let memory_facts = functions.iter().map(|function| function.memory_facts).sum();
    let unsupported_items = artifact
        .unsupported
        .records
        .iter()
        .filter(|record| !is_rust_skeleton_advisory(record))
        .map(format_unsupported_record)
        .collect::<Vec<_>>();
    let unsupported = unsupported_items.len();
    let status = if unsupported > 0 { BinaryLiftStatus::Incomplete } else { BinaryLiftStatus::Ok };

    DecompileReport {
        binary: binary_path.display().to_string(),
        format: Some(binary_artifact_format_label(artifact.binary.format).to_string()),
        architecture: Some(artifact.binary.architecture),
        selection: binary_selection_label(entry, all_functions).to_string(),
        entry: entry.map(hex_addr),
        binary_entry: artifact.binary.entry_point.map(hex_addr),
        source_provenance: artifact.source_provenance,
        strict,
        target,
        status,
        output_kind: selected_output
            .map(|output| decompiled_output_kind_label(output, target))
            .or_else(|| {
                Some(
                    decompile_output_kind_label(decompile_output_kind(
                        target,
                        OutputFormat::Terminal,
                    ))
                    .to_string(),
                )
            }),
        output_trust_level: selected_output
            .map(|output| trust_level_label(output.trust_level))
            .unwrap_or_else(|| decompile_target_trust_level(target))
            .to_string(),
        output_validation: selected_output
            .map(|output| decompiled_output_validation_label(output, target))
            .unwrap_or_else(|| decompile_target_validation(target).to_string()),
        validation_note: selected_output
            .map(|output| decompiled_output_validation_note(output, target))
            .unwrap_or_else(|| decompile_validation_note(target).to_string()),
        output_content: selected_output.and_then(|output| output.text.clone()),
        production_proof_grade_evidence,
        binary_evidence,
        target_validation_blockers: selected_output
            .map(|output| output.target_validation_blockers.clone())
            .unwrap_or_default(),
        preserved_symbolic_formulas: selected_output
            .map(|output| output.preserved_symbolic_formulas.clone())
            .unwrap_or_default(),
        functions_decompiled: functions.len(),
        blocks,
        instructions,
        statements,
        memory_facts,
        unsupported,
        failures: 0,
        functions,
        unsupported_items,
        failure_items: Vec::new(),
    }
}

fn build_decompile_report_from_error(
    binary_path: &Path,
    entry: Option<u64>,
    all_functions: bool,
    strict: bool,
    target: DecompileTarget,
    binary_metadata: Option<DecompileErrorMetadata>,
    error: DecompileError,
) -> DecompileReport {
    let message = error.to_string();
    let is_unsupported =
        matches!(&error, DecompileError::Lift(lift) if is_unsupported_lift_error(lift));
    let (status, unsupported_items, failure_items) = if is_unsupported {
        (BinaryLiftStatus::Incomplete, vec![message], Vec::new())
    } else {
        (BinaryLiftStatus::Failed, Vec::new(), vec![message])
    };
    let unsupported = unsupported_items.len();
    let failures = failure_items.len();
    let metadata =
        binary_metadata.or_else(|| decompile_error_metadata_from_error(&error)).unwrap_or_default();
    let binary_evidence = decompile_binary_evidence_from_error(&unsupported_items, &failure_items);

    DecompileReport {
        binary: binary_path.display().to_string(),
        format: metadata.format,
        architecture: metadata.architecture,
        selection: binary_selection_label(entry, all_functions).to_string(),
        entry: entry.map(hex_addr),
        binary_entry: metadata.binary_entry.map(hex_addr),
        source_provenance: BinarySourceProvenanceSummary::default(),
        strict,
        target,
        status,
        output_kind: None,
        output_trust_level: "rejected".to_string(),
        output_validation: "artifact_not_produced".to_string(),
        validation_note:
            "binary lift/decompilation failed before the requested artifact was produced"
                .to_string(),
        output_content: None,
        production_proof_grade_evidence: None,
        binary_evidence,
        target_validation_blockers: Vec::new(),
        preserved_symbolic_formulas: Vec::new(),
        functions_decompiled: 0,
        blocks: 0,
        instructions: 0,
        statements: 0,
        memory_facts: 0,
        unsupported,
        failures,
        functions: Vec::new(),
        unsupported_items,
        failure_items,
    }
}

fn decompile_production_proof_grade_evidence_from_artifact(
    artifact: &DecompilationArtifact,
) -> Option<DecompileProofGradeEvidenceReport> {
    let verification = &artifact.verification;
    if artifact.trust_level != TrustLevel::ProofGrade
        && verification.trust_level != TrustLevel::ProofGrade
        && verification.solver_dispatch.is_empty()
    {
        return None;
    }

    let checked_certificate_identity = !verification.solver_dispatch.is_empty()
        && verification.solver_dispatch.iter().all(|dispatch| dispatch.certificate.is_checked());
    let exact_replay_identity = !verification.solver_dispatch.is_empty()
        && verification.solver_dispatch.iter().all(|dispatch| {
            dispatch.replay == ReplayStatus::Replayed
                && dispatch_has_exact_replay_slice_attestation(dispatch)
        });
    let binary_artifact_digest_identity = artifact.binary.digest_identity_allows_proof_grade()
        && !verification.solver_dispatch.is_empty()
        && verification
            .solver_dispatch
            .iter()
            .all(SolverDispatchRecord::replay_digest_identity_allows_proof_grade);
    let target_validation_accepted = decompile_target_validation_accepted_for_proof_grade(artifact);
    let unsupported_ledger_empty = artifact.unsupported.records.is_empty()
        && verification.unsupported_ledger.records.is_empty();

    Some(DecompileProofGradeEvidenceReport {
        schema_version: "targo-trust-decompile-production-proof-grade-evidence.v1".to_string(),
        producer: "trust-decompile::binary-release-gate".to_string(),
        artifact_trust_level: trust_level_label(artifact.trust_level).to_string(),
        binary_verification_trust_level: trust_level_label(verification.trust_level).to_string(),
        binary_verification_status: binary_verification_status_label(verification.status)
            .to_string(),
        binary_replay: replay_status_label(verification.replay).to_string(),
        required_vcs: verification.total_vcs,
        proved_vcs: verification.proved,
        checked_certificate_identity,
        exact_replay_identity,
        binary_artifact_digest_identity,
        exact_source_provenance: artifact
            .source_provenance
            .effective_source_backpropagation_allowed(),
        reconstruction_accepted: artifact.reconstruction.validation
            == ReconstructionValidationStatus::Validated
            && artifact.reconstruction.trust_level == TrustLevel::ProofGrade,
        target_validation_accepted,
        unsupported_ledger_empty,
    })
}

fn decompile_target_validation_accepted_for_proof_grade(artifact: &DecompilationArtifact) -> bool {
    let target_outputs = artifact
        .reconstruction
        .outputs
        .iter()
        .filter(|output| output.target == artifact.reconstruction.target)
        .collect::<Vec<_>>();

    !target_outputs.is_empty()
        && target_outputs.iter().all(|output| {
            output.validation == ReconstructionValidationStatus::Validated
                && output.trust_level == TrustLevel::ProofGrade
                && output.target_validation_blockers.is_empty()
        })
}

fn decompile_binary_evidence_from_artifact(
    artifact: &DecompilationArtifact,
) -> DecompileBinaryEvidenceReport {
    let verification = &artifact.verification;
    let unsupported_ledger = decompile_unsupported_ledger_report(&artifact.unsupported);
    let verification_unsupported_ledger =
        decompile_unsupported_ledger_report(&verification.unsupported_ledger);
    let solver_dispatches = verification
        .solver_dispatch
        .iter()
        .map(decompile_solver_dispatch_evidence)
        .collect::<Vec<_>>();
    let checked_certificate_dispatches =
        solver_dispatches.iter().filter(|dispatch| dispatch.checked_certificate).count();
    let replayed_dispatches =
        solver_dispatches.iter().filter(|dispatch| dispatch.exact_replay).count();
    let replay_digest_identity_dispatches = solver_dispatches
        .iter()
        .filter(|dispatch| dispatch.replay_digest_identity_accepted)
        .count();
    let exact_instruction_provenance_dispatches =
        solver_dispatches.iter().filter(|dispatch| dispatch.exact_instruction_provenance).count();
    let exact_source_provenance_dispatches =
        solver_dispatches.iter().filter(|dispatch| dispatch.exact_source_provenance).count();
    let release_gate = decompile_binary_release_gate_report(
        verification,
        &solver_dispatches,
        &unsupported_ledger,
        &verification_unsupported_ledger,
        &artifact.source_provenance,
    );

    DecompileBinaryEvidenceReport {
        schema_version: "targo-trust-decompile-binary-evidence.v1".to_string(),
        verification_status: binary_verification_status_label(verification.status).to_string(),
        verification_trust_level: trust_level_label(verification.trust_level).to_string(),
        total_vcs: verification.total_vcs,
        proved_vcs: verification.proved,
        failed_vcs: verification.failed,
        unknown_vcs: verification.unknown,
        timeout_vcs: verification.timeout,
        unsupported_vcs: verification.unsupported,
        rejected_vcs: verification.rejected,
        replay_status: replay_status_label(verification.replay).to_string(),
        proof_certificate: decompile_proof_certificate_evidence(&verification.proof_certificate),
        checked_certificate_dispatches,
        replayed_dispatches,
        replay_digest_identity_dispatches,
        exact_instruction_provenance_dispatches,
        exact_source_provenance_dispatches,
        binary_artifact_digest_identity: BinaryArtifactDigestIdentity::from_metadata(
            &artifact.binary,
        ),
        unsupported_ledger,
        verification_unsupported_ledger,
        solver_dispatches,
        release_gate,
    }
}

fn decompile_binary_evidence_from_error(
    unsupported_items: &[String],
    failure_items: &[String],
) -> DecompileBinaryEvidenceReport {
    let mut ledger = UnsupportedLedger::default();
    ledger.records.extend(unsupported_items.iter().map(|feature| UnsupportedRecord {
        stage: "targo trust decompile".to_string(),
        architecture: None,
        origin: None,
        opcode: None,
        operand: None,
        feature: feature.clone(),
    }));
    ledger.records.extend(failure_items.iter().map(|feature| UnsupportedRecord {
        stage: "targo trust decompile".to_string(),
        architecture: None,
        origin: None,
        opcode: None,
        operand: None,
        feature: feature.clone(),
    }));

    let unsupported_ledger = decompile_unsupported_ledger_report(&ledger);
    let mut report = DecompileBinaryEvidenceReport {
        unsupported_ledger: unsupported_ledger.clone(),
        verification_unsupported_ledger: unsupported_ledger,
        ..DecompileBinaryEvidenceReport::default()
    };
    if !report.unsupported_ledger.empty {
        report.release_gate.blockers.push(decompile_evidence_blocker(
            "targo-trust::decompile-binary-evidence",
            "unsupported-ledger-nonempty",
            "unsupported-ledger",
            format!(
                "unsupported binary/decompilation ledger contains {} record(s)",
                report.unsupported_ledger.total_records
            ),
            ["empty_unsupported_ledger"],
        ));
        report.release_gate.reason = report
            .release_gate
            .blockers
            .iter()
            .map(|blocker| format!("{}: {}", blocker.code, blocker.detail))
            .collect::<Vec<_>>()
            .join("; ");
    }
    report
}

fn decompile_solver_dispatch_evidence(
    dispatch: &SolverDispatchRecord,
) -> DecompileSolverDispatchEvidenceReport {
    let exact_instruction_provenance =
        dispatch.origin.as_ref().is_some_and(decompile_origin_has_exact_instruction_provenance);
    let exact_source_provenance =
        dispatch.origin.as_ref().is_some_and(decompile_origin_has_exact_source_provenance);
    let replay_digest_identity_blockers = dispatch.replay_digest_identity_blockers();
    let replay_digest_identity_accepted = replay_digest_identity_blockers.is_empty();

    DecompileSolverDispatchEvidenceReport {
        id: dispatch.id.clone(),
        function: dispatch.function.clone(),
        status: solver_dispatch_status_label(dispatch.status).to_string(),
        query_semantics: solver_query_semantics_label(dispatch.query_semantics).to_string(),
        replay: replay_status_label(dispatch.replay).to_string(),
        proof_certificate: decompile_proof_certificate_evidence(&dispatch.certificate),
        checked_certificate: dispatch.certificate.is_checked(),
        exact_replay: dispatch.replay == ReplayStatus::Replayed
            && dispatch_has_exact_replay_slice_attestation(dispatch),
        exact_instruction_provenance,
        exact_source_provenance,
        replay_digest_identity_accepted,
        replay_digest_identity_blockers,
        binary_artifact_digest_identity: dispatch.binary_artifact_digest_identity.clone(),
        vc_kind: dispatch.vc_kind.as_ref().map(vc_kind_key),
        origin: dispatch.origin.clone(),
        diagnostics: dispatch.diagnostics.clone(),
    }
}

fn decompile_binary_release_gate_report(
    verification: &BinaryVerificationSummary,
    solver_dispatches: &[DecompileSolverDispatchEvidenceReport],
    unsupported_ledger: &DecompileUnsupportedLedgerReport,
    verification_unsupported_ledger: &DecompileUnsupportedLedgerReport,
    source_provenance: &BinarySourceProvenanceSummary,
) -> DecompileReleaseGateReport {
    let required_vcs = verification.total_vcs.max(solver_dispatches.len());
    let mut blockers = Vec::new();

    if required_vcs == 0 {
        blockers.push(decompile_evidence_blocker(
            "targo-trust::decompile-binary-evidence",
            "binary-verification-missing",
            "proof-grade-binary-verification",
            "no binary verification dispatch evidence was attached to the decompile artifact",
            ["binary_vc_solver_dispatch"],
        ));
    }
    if solver_dispatches.len() < required_vcs {
        blockers.push(decompile_evidence_blocker(
            "targo-trust::decompile-binary-evidence",
            "binary-verification-dispatch-coverage-missing",
            "proof-grade-binary-verification",
            format!(
                "binary verification dispatched {}/{} required VC(s)",
                solver_dispatches.len(),
                required_vcs
            ),
            ["binary_vc_solver_dispatch"],
        ));
    }
    if verification.proved < required_vcs {
        blockers.push(decompile_evidence_blocker(
            "targo-trust::decompile-binary-evidence",
            "binary-vc-proof-coverage-missing",
            "proof-grade-binary-verification",
            format!(
                "binary verification proved {}/{} required VC(s)",
                verification.proved, required_vcs
            ),
            ["all_required_vcs_proved"],
        ));
    }
    let checked = solver_dispatches.iter().filter(|dispatch| dispatch.checked_certificate).count();
    if checked < required_vcs {
        blockers.push(decompile_evidence_blocker(
            "targo-trust::decompile-binary-evidence",
            "checked-certificate-missing",
            "checked-certificate-coverage",
            format!("checked certificates cover {checked}/{required_vcs} required VC(s)"),
            ["normalized_solver_proof_export", "checker_success", "checked_certificate_artifact"],
        ));
    }
    let replayed = solver_dispatches.iter().filter(|dispatch| dispatch.exact_replay).count();
    if replayed < required_vcs {
        blockers.push(decompile_evidence_blocker(
            "targo-trust::decompile-binary-evidence",
            "exact-machine-replay-missing",
            "exact-machine-replay",
            format!("machine replay covers {replayed}/{required_vcs} required VC(s)"),
            ["machine_replay_transcript"],
        ));
    }
    let replayed_without_slice_attestation = solver_dispatches
        .iter()
        .filter(|dispatch| dispatch.replay == "replayed" && !dispatch.exact_replay)
        .count();
    if replayed_without_slice_attestation > 0 {
        blockers.push(decompile_evidence_blocker(
            "targo-trust::decompile-binary-evidence",
            "exact-replay-slice-attestation-missing",
            "exact-replay-slice-attestation",
            format!(
                "{replayed_without_slice_attestation} replayed dispatch(es) lack selected-image byte/segment attestation"
            ),
            [
                "selected_image_bytes",
                "exact_replay_instruction_witness",
                "executable_segment_byte_range_attestation",
            ],
        ));
    }
    let replay_digest = solver_dispatches
        .iter()
        .filter(|dispatch| dispatch.replay_digest_identity_accepted)
        .count();
    if replay_digest < required_vcs {
        blockers.push(decompile_evidence_blocker(
            "targo-trust::decompile-binary-evidence",
            "replay-artifact-digest-identity-missing",
            "replay-artifact-digest-identity",
            format!(
                "binary artifact digest identity covers {replay_digest}/{required_vcs} replay dispatch(es)"
            ),
            ["binary_artifact_digest_identity", "selected_image_digest_identity"],
        ));
    }
    let exact_instruction =
        solver_dispatches.iter().filter(|dispatch| dispatch.exact_instruction_provenance).count();
    if exact_instruction < required_vcs {
        blockers.push(decompile_evidence_blocker(
            "targo-trust::decompile-binary-evidence",
            "exact-instruction-provenance-missing",
            "exact-instruction-provenance",
            format!(
                "exact instruction byte provenance covers {exact_instruction}/{required_vcs} required VC(s)"
            ),
            ["instruction_bytes", "instruction_size"],
        ));
    }
    let exact_source =
        solver_dispatches.iter().filter(|dispatch| dispatch.exact_source_provenance).count();
    if exact_source < required_vcs || !source_provenance.effective_source_backpropagation_allowed()
    {
        blockers.push(decompile_evidence_blocker(
            "targo-trust::decompile-binary-evidence",
            "exact-source-provenance-missing",
            "exact-source-provenance",
            format!(
                "exact source provenance covers {exact_source}/{required_vcs} dispatch(es); source provenance status is `{}` with source_backpropagation_allowed={}",
                source_provenance.status,
                source_provenance.effective_source_backpropagation_allowed()
            ),
            ["exact_binary_source_provenance", "source_provenance_handoff"],
        ));
    }
    if !unsupported_ledger.empty {
        blockers.push(decompile_evidence_blocker(
            "targo-trust::decompile-binary-evidence",
            "unsupported-ledger-nonempty",
            "unsupported-ledger",
            format!(
                "decompile unsupported ledger contains {} record(s)",
                unsupported_ledger.total_records
            ),
            ["empty_unsupported_ledger"],
        ));
    }
    let unconsumed_sync_boundaries = unsupported_ledger
        .aarch64_sync_boundary_facts
        .iter()
        .filter(|fact| !fact.proof_grade_gate_accepted())
        .count();
    if unconsumed_sync_boundaries > 0 {
        let missing = decompile_sync_boundary_missing_witnesses(
            &unsupported_ledger.aarch64_sync_boundary_facts,
        );
        blockers.push(decompile_evidence_blocker(
            "targo-trust::decompile-binary-evidence",
            "aarch64-sync-boundary-not-proof-consumed",
            "aarch64-sync-boundary-proof-consumption",
            format!(
                "decompile unsupported ledger contains {unconsumed_sync_boundaries}/{} AArch64 sync boundary fact(s) not proof-consumed; missing witnesses: {}",
                unsupported_ledger.aarch64_sync_boundary_fact_count,
                decompile_missing_witnesses_label(&missing)
            ),
            decompile_sync_boundary_evidence_required(&missing),
        ));
    }
    if !verification_unsupported_ledger.empty {
        blockers.push(decompile_evidence_blocker(
            "targo-trust::decompile-binary-evidence",
            "verification-unsupported-ledger-nonempty",
            "unsupported-ledger",
            format!(
                "binary verification unsupported ledger contains {} record(s)",
                verification_unsupported_ledger.total_records
            ),
            ["empty_unsupported_ledger"],
        ));
    }
    let unconsumed_verification_sync_boundaries = verification_unsupported_ledger
        .aarch64_sync_boundary_facts
        .iter()
        .filter(|fact| !fact.proof_grade_gate_accepted())
        .count();
    if unconsumed_verification_sync_boundaries > 0 {
        let missing = decompile_sync_boundary_missing_witnesses(
            &verification_unsupported_ledger.aarch64_sync_boundary_facts,
        );
        blockers.push(decompile_evidence_blocker(
            "targo-trust::decompile-binary-evidence",
            "verification-aarch64-sync-boundary-not-proof-consumed",
            "aarch64-sync-boundary-proof-consumption",
            format!(
                "binary verification unsupported ledger contains {unconsumed_verification_sync_boundaries}/{} AArch64 sync boundary fact(s) not proof-consumed; missing witnesses: {}",
                verification_unsupported_ledger.aarch64_sync_boundary_fact_count,
                decompile_missing_witnesses_label(&missing)
            ),
            decompile_sync_boundary_evidence_required(&missing),
        ));
    }

    let accepted = blockers.is_empty()
        && required_vcs > 0
        && verification.trust_level == TrustLevel::ProofGrade
        && verification.status == BinaryVerificationStatus::Proved
        && verification.replay == ReplayStatus::Replayed;
    if accepted {
        DecompileReleaseGateReport {
            accepted,
            status: "accepted".to_string(),
            reason: "binary decompilation evidence accepted".to_string(),
            blockers,
        }
    } else {
        DecompileReleaseGateReport {
            accepted: false,
            status: "rejected".to_string(),
            reason: if blockers.is_empty() {
                format!(
                    "binary verification status={} trust_level={} replay={} did not satisfy the proof-grade release gate",
                    binary_verification_status_label(verification.status),
                    trust_level_label(verification.trust_level),
                    replay_status_label(verification.replay)
                )
            } else {
                blockers
                    .iter()
                    .map(|blocker| format!("{}: {}", blocker.code, blocker.detail))
                    .collect::<Vec<_>>()
                    .join("; ")
            },
            blockers,
        }
    }
}

fn decompile_sync_boundary_missing_witnesses(
    facts: &[Aarch64SyncBoundarySemanticFact],
) -> Vec<String> {
    let mut witnesses = BTreeSet::new();
    for fact in facts {
        if fact.proof_grade_gate_accepted() {
            continue;
        }
        if fact.missing_witnesses.is_empty() {
            witnesses.insert("proof model consumption".to_string());
        } else {
            witnesses.extend(fact.missing_witnesses.iter().cloned());
        }
    }
    witnesses.into_iter().collect()
}

fn decompile_sync_boundary_evidence_required(missing_witnesses: &[String]) -> Vec<String> {
    let mut evidence = BTreeSet::new();
    evidence.insert("aarch64_sync_boundary_proof_consumer".to_string());
    evidence.extend(missing_witnesses.iter().cloned());
    evidence.into_iter().collect()
}

fn decompile_missing_witnesses_label(missing_witnesses: &[String]) -> String {
    if missing_witnesses.is_empty() {
        "proof model consumption".to_string()
    } else {
        missing_witnesses.join(", ")
    }
}

fn decompile_proof_certificate_evidence(
    certificate: &ProofCertificateStatus,
) -> DecompileProofCertificateEvidenceReport {
    let production_checker_evidence_status =
        proof_certificate_production_checker_evidence_status_label(
            &certificate.production_checker_evidence_status(),
        );
    match certificate {
        ProofCertificateStatus::NotRequested => DecompileProofCertificateEvidenceReport {
            status: "not_requested".to_string(),
            production_checker_evidence_status,
            ..DecompileProofCertificateEvidenceReport::default()
        },
        ProofCertificateStatus::Unavailable { reason } => DecompileProofCertificateEvidenceReport {
            status: "unavailable".to_string(),
            reason: reason.clone(),
            production_checker_evidence_status,
            ..DecompileProofCertificateEvidenceReport::default()
        },
        ProofCertificateStatus::Present { format, sha256, artifact_path } => {
            DecompileProofCertificateEvidenceReport {
                status: "present".to_string(),
                format: Some(format.clone()),
                sha256: sha256.clone(),
                artifact_path: artifact_path.clone(),
                production_checker_evidence_status,
                ..DecompileProofCertificateEvidenceReport::default()
            }
        }
        ProofCertificateStatus::Checked { checker, format, sha256 } => {
            DecompileProofCertificateEvidenceReport {
                status: "checked".to_string(),
                checker: Some(checker.clone()),
                format: Some(format.clone()),
                sha256: sha256.clone(),
                production_checker_evidence_status,
                ..DecompileProofCertificateEvidenceReport::default()
            }
        }
        ProofCertificateStatus::Rejected { checker, reason } => {
            DecompileProofCertificateEvidenceReport {
                status: "rejected".to_string(),
                checker: checker.clone(),
                reason: Some(reason.clone()),
                production_checker_evidence_status,
                ..DecompileProofCertificateEvidenceReport::default()
            }
        }
        _ => DecompileProofCertificateEvidenceReport {
            status: "unknown".to_string(),
            production_checker_evidence_status,
            ..DecompileProofCertificateEvidenceReport::default()
        },
    }
}

fn proof_certificate_production_checker_evidence_status_label(
    status: &ProofCertificateProductionCheckerEvidenceStatus,
) -> String {
    match status {
        ProofCertificateProductionCheckerEvidenceStatus::Missing => "missing".to_string(),
        ProofCertificateProductionCheckerEvidenceStatus::Malformed { reason } => {
            format!("malformed: {reason}")
        }
        ProofCertificateProductionCheckerEvidenceStatus::Present { .. } => "present".to_string(),
    }
}

fn decompile_unsupported_ledger_report(
    ledger: &UnsupportedLedger,
) -> DecompileUnsupportedLedgerReport {
    let mut by_stage = BTreeMap::new();
    let mut by_feature = BTreeMap::new();
    for record in &ledger.records {
        *by_stage.entry(record.stage.clone()).or_insert(0) += 1;
        *by_feature.entry(record.feature.clone()).or_insert(0) += 1;
    }
    let aarch64_sync_boundary_facts = ledger.aarch64_sync_boundary_semantic_facts();
    let aarch64_sync_boundary_fact_count = aarch64_sync_boundary_facts.len();

    DecompileUnsupportedLedgerReport {
        empty: ledger.records.is_empty(),
        total_records: ledger.records.len(),
        by_stage,
        by_feature,
        by_family: ledger.family_counts(),
        aarch64_sync_boundary_facts,
        aarch64_sync_boundary_fact_count,
        records: ledger.records.clone(),
    }
}

fn decompile_origin_has_exact_instruction_provenance(origin: &BinaryOrigin) -> bool {
    origin
        .instruction_size
        .is_some_and(|size| size > 0 && usize::from(size) == origin.instruction_bytes.len())
}

fn decompile_origin_has_exact_source_provenance(origin: &BinaryOrigin) -> bool {
    origin.source.as_ref().is_some_and(|source| !source.is_binary())
}

fn decompile_evidence_blocker<I, S>(
    stage: impl Into<String>,
    code: impl Into<String>,
    feature: impl Into<String>,
    detail: impl Into<String>,
    evidence_required: I,
) -> DecompileEvidenceBlockerReport
where
    I: IntoIterator<Item = S>,
    S: Into<String>,
{
    DecompileEvidenceBlockerReport {
        code: code.into(),
        stage: stage.into(),
        feature: feature.into(),
        detail: detail.into(),
        evidence_required: evidence_required.into_iter().map(Into::into).collect(),
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
struct DecompileErrorMetadata {
    format: Option<String>,
    architecture: Option<String>,
    binary_entry: Option<u64>,
}

fn decompile_error_metadata_from_error(error: &DecompileError) -> Option<DecompileErrorMetadata> {
    match error {
        DecompileError::Lift(LiftError::UnsupportedBinaryFormat { format, .. }) => {
            Some(DecompileErrorMetadata {
                format: Some((*format).to_string()),
                ..DecompileErrorMetadata::default()
            })
        }
        _ => None,
    }
}

fn sniff_binary_metadata(bytes: &[u8]) -> Option<DecompileErrorMetadata> {
    if bytes.starts_with(b"\x7fELF") {
        return sniff_elf_metadata(bytes);
    }
    if bytes.starts_with(b"MZ") {
        return sniff_pe_metadata(bytes);
    }
    sniff_macho_metadata(bytes)
}

fn sniff_elf_metadata(bytes: &[u8]) -> Option<DecompileErrorMetadata> {
    let class = *bytes.get(4)?;
    let endian = *bytes.get(5)?;
    let machine = read_u16_at(bytes, 18, endian == 2)?;
    let binary_entry = match class {
        1 => read_u32_at(bytes, 24, endian == 2).map(u64::from),
        2 => read_u64_at(bytes, 24, endian == 2),
        _ => None,
    };
    Some(DecompileErrorMetadata {
        format: Some("ELF".to_string()),
        architecture: elf_machine_name(machine).map(str::to_string),
        binary_entry,
    })
}

fn sniff_pe_metadata(bytes: &[u8]) -> Option<DecompileErrorMetadata> {
    let pe_offset = read_u32_at(bytes, 0x3c, false)? as usize;
    if bytes.get(pe_offset..pe_offset.checked_add(4)?)? != b"PE\0\0" {
        return None;
    }
    let machine = read_u16_at(bytes, pe_offset.checked_add(4)?, false)?;
    Some(DecompileErrorMetadata {
        format: Some("PE/COFF".to_string()),
        architecture: pe_machine_name(machine).map(str::to_string),
        binary_entry: None,
    })
}

fn sniff_macho_metadata(bytes: &[u8]) -> Option<DecompileErrorMetadata> {
    match bytes.get(0..4)? {
        [0xcf, 0xfa, 0xed, 0xfe] => Some(DecompileErrorMetadata {
            format: Some("Mach-O".to_string()),
            architecture: read_i32_at(bytes, 4, false).and_then(macho_cpu_name).map(str::to_string),
            binary_entry: None,
        }),
        [0xfe, 0xed, 0xfa, 0xcf] => Some(DecompileErrorMetadata {
            format: Some("Mach-O".to_string()),
            architecture: read_i32_at(bytes, 4, true).and_then(macho_cpu_name).map(str::to_string),
            binary_entry: None,
        }),
        [0xca, 0xfe, 0xba, 0xbe] => sniff_fat_macho_metadata(bytes, false),
        [0xca, 0xfe, 0xba, 0xbf] => sniff_fat_macho_metadata(bytes, true),
        _ => None,
    }
}

fn sniff_fat_macho_metadata(bytes: &[u8], is_64: bool) -> Option<DecompileErrorMetadata> {
    let nfat = read_u32_at(bytes, 4, true)? as usize;
    let record_size = if is_64 { 32usize } else { 20usize };
    let mut selected = None;
    for index in 0..nfat {
        let offset = 8usize.checked_add(index.checked_mul(record_size)?)?;
        let cputype = read_i32_at(bytes, offset, true)?;
        let name = macho_cpu_name(cputype);
        if name == Some("AArch64") {
            selected = name;
            break;
        }
        if selected.is_none() {
            selected = name;
        }
    }
    Some(DecompileErrorMetadata {
        format: Some("Fat Mach-O".to_string()),
        architecture: selected.map(str::to_string),
        binary_entry: None,
    })
}

fn elf_machine_name(machine: u16) -> Option<&'static str> {
    match machine {
        0x03 => Some("x86"),
        0x28 => Some("ARM"),
        0x3e => Some("x86-64"),
        0xb7 => Some("AArch64"),
        _ => None,
    }
}

fn pe_machine_name(machine: u16) -> Option<&'static str> {
    match machine {
        0x014c => Some("x86"),
        0x01c0 | 0x01c4 => Some("ARM"),
        0x8664 => Some("x86-64"),
        0xaa64 => Some("AArch64"),
        _ => None,
    }
}

fn macho_cpu_name(cputype: i32) -> Option<&'static str> {
    match cputype {
        0x0100_0007 => Some("x86-64"),
        0x0100_000c => Some("AArch64"),
        0x0000_000c => Some("ARM"),
        _ => None,
    }
}

fn read_u16_at(bytes: &[u8], offset: usize, big_endian: bool) -> Option<u16> {
    let chunk = bytes.get(offset..offset.checked_add(2)?)?;
    Some(if big_endian {
        u16::from_be_bytes([chunk[0], chunk[1]])
    } else {
        u16::from_le_bytes([chunk[0], chunk[1]])
    })
}

fn read_u32_at(bytes: &[u8], offset: usize, big_endian: bool) -> Option<u32> {
    let chunk = bytes.get(offset..offset.checked_add(4)?)?;
    Some(if big_endian {
        u32::from_be_bytes([chunk[0], chunk[1], chunk[2], chunk[3]])
    } else {
        u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]])
    })
}

fn read_i32_at(bytes: &[u8], offset: usize, big_endian: bool) -> Option<i32> {
    let chunk = bytes.get(offset..offset.checked_add(4)?)?;
    Some(if big_endian {
        i32::from_be_bytes([chunk[0], chunk[1], chunk[2], chunk[3]])
    } else {
        i32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]])
    })
}

fn read_u64_at(bytes: &[u8], offset: usize, big_endian: bool) -> Option<u64> {
    let chunk = bytes.get(offset..offset.checked_add(8)?)?;
    Some(if big_endian {
        u64::from_be_bytes([
            chunk[0], chunk[1], chunk[2], chunk[3], chunk[4], chunk[5], chunk[6], chunk[7],
        ])
    } else {
        u64::from_le_bytes([
            chunk[0], chunk[1], chunk[2], chunk[3], chunk[4], chunk[5], chunk[6], chunk[7],
        ])
    })
}

fn decompile_should_fail(report: &DecompileReport) -> bool {
    report.failures > 0
        || report.output_trust_level == "rejected"
        || report.strict && report.unsupported > 0
        || report.unsupported > 0 && report.functions_decompiled == 0
}

#[cfg(test)]
fn convert_should_fail(report: &DecompileReport) -> bool {
    !build_convert_cli_gate(report).accepted
}

fn build_exploit_find_report(
    target: ExploitFindTarget,
    binary_report: BinaryVerifyReport,
) -> ExploitFindReport {
    let analysis = analyze_binary_exploit_find(target, &binary_report);

    ExploitFindReport {
        input: binary_report.binary.clone(),
        target,
        status: analysis.status,
        exploit_found: analysis.exploit_found,
        binary_status: binary_report.status,
        verification_status: binary_report.verification_status.clone(),
        functions_analyzed: binary_report.functions_analyzed,
        vcs: binary_report.vcs,
        vc_counts: binary_report.vc_counts.clone(),
        solver_results: binary_report.solver_results.clone(),
        unsupported: binary_report.unsupported,
        failures: binary_report.failures,
        independent_refutation_status: analysis.independent_refutation_status,
        independent_refutation_note: analysis.independent_refutation_note,
        reducer_status: analysis.reducer_status,
        reducer_note: analysis.reducer_note,
        synthesis_status: analysis.synthesis_status,
        synthesis_note: analysis.synthesis_note,
        replay_status: analysis.replay_status,
        replay_note: analysis.replay_note,
        reason: analysis.reason,
        binary_report,
        notes: analysis.notes,
    }
}

fn exploit_find_should_fail(report: &ExploitFindReport) -> bool {
    matches!(report.status, ExploitFindStatus::Unsupported)
        || !report.exploit_found
        || report.binary_status != BinaryLiftStatus::Ok
        || report.vcs == 0
        || report.solver_results.status != "proved"
}

fn analyze_binary_exploit_find(
    target: ExploitFindTarget,
    binary_report: &BinaryVerifyReport,
) -> ExploitFindAnalysis {
    let evidence = exploit_evidence_summary(binary_report);
    let replay_note = exploit_find_replay_note(&evidence);
    let independent_refutation_note = exploit_find_independent_refutation_note(&evidence);
    let reducer_note = exploit_find_reducer_note(&evidence);
    let synthesis_note =
        "exploit synthesis is not implemented; solver results are not normalized into replayable exploit witnesses"
            .to_string();
    let reason = exploit_find_fail_closed_reason(binary_report, &evidence);
    let claim_records = exploit_claim_capture_records(target, binary_report);
    let stage_records = exploit_analyzer_stage_records(target, binary_report);
    let mut notes = exploit_find_notes(binary_report);

    notes.extend(stage_records.iter().map(exploit_analyzer_stage_diagnostic));
    notes.extend(claim_records.iter().map(exploit_claim_capture_diagnostic));

    ExploitFindAnalysis {
        status: ExploitFindStatus::Unsupported,
        exploit_found: false,
        independent_refutation_status: evidence.independent_refutation_status,
        independent_refutation_note,
        reducer_status: evidence.reduction_status,
        reducer_note,
        synthesis_status: ExploitFindStatus::Unsupported,
        synthesis_note,
        replay_status: evidence.replay_status,
        replay_note,
        reason,
        notes,
    }
}

fn exploit_evidence_summary(binary_report: &BinaryVerifyReport) -> ExploitEvidenceSummary {
    let raw_solver_candidates =
        binary_report.solver_result_items.iter().filter(|item| item.status == "failed").count();
    let replayed_solver_items = binary_report
        .solver_result_items
        .iter()
        .filter(|item| item.status == "failed" && item.replay_status.as_deref() == Some("replayed"))
        .count();
    let replayed_sat_dispatches = binary_report
        .proof_evidence
        .solver_dispatch
        .iter()
        .filter(|dispatch| {
            dispatch.status == SolverDispatchStatus::Sat
                && dispatch.query_semantics == SolverQuerySemantics::SatIsCounterexample
                && dispatch.replay == ReplayStatus::Replayed
        })
        .count();
    let exact_replayed_candidates = replayed_solver_items.max(replayed_sat_dispatches);
    let checked_unsat_refutations = binary_report.proof_evidence.checked_certificates();
    let all_required_vcs_checked_unsat = binary_report.vcs > 0
        && binary_report.solver_results.status == "proved"
        && binary_report.proof_evidence.solver_dispatch.len() == binary_report.vcs
        && binary_report.proof_evidence.proved_vcs() == binary_report.vcs
        && checked_unsat_refutations == binary_report.vcs;
    let replay_status = if raw_solver_candidates == 0 {
        ExploitFindStatus::NotRun
    } else if exact_replayed_candidates >= raw_solver_candidates {
        ExploitFindStatus::Satisfied
    } else {
        ExploitFindStatus::Unsupported
    };
    let independent_refutation_status = if raw_solver_candidates > 0 {
        ExploitFindStatus::Unsupported
    } else {
        ExploitFindStatus::NotRun
    };
    let downstream_status = if raw_solver_candidates > 0
        || replay_status == ExploitFindStatus::Satisfied
        || independent_refutation_status == ExploitFindStatus::Satisfied
    {
        ExploitFindStatus::Unsupported
    } else {
        ExploitFindStatus::NotRun
    };
    let replayed_and_independently_refuted_candidates = raw_solver_candidates > 0
        && replay_status == ExploitFindStatus::Satisfied
        && independent_refutation_status == ExploitFindStatus::Satisfied;
    let deterministically_attributed_candidates =
        if replayed_and_independently_refuted_candidates { raw_solver_candidates } else { 0 };
    let attribution_status = if deterministically_attributed_candidates == raw_solver_candidates
        && raw_solver_candidates > 0
    {
        ExploitFindStatus::Satisfied
    } else {
        downstream_status
    };
    let deterministically_reduced_candidates =
        if replayed_and_independently_refuted_candidates { raw_solver_candidates } else { 0 };
    let reduction_status = if deterministically_reduced_candidates == raw_solver_candidates
        && raw_solver_candidates > 0
    {
        ExploitFindStatus::Satisfied
    } else {
        downstream_status
    };

    ExploitEvidenceSummary {
        raw_solver_candidates,
        exact_replayed_candidates,
        checked_unsat_refutations,
        deterministically_attributed_candidates,
        deterministically_reduced_candidates,
        required_vcs: binary_report.vcs,
        all_required_vcs_checked_unsat,
        replay_status,
        independent_refutation_status,
        reduction_status,
        attribution_status,
        regression_status: downstream_status,
    }
}

fn exploit_claim_capture_records(
    target: ExploitFindTarget,
    binary_report: &BinaryVerifyReport,
) -> Vec<ExploitClaimCaptureRecord> {
    binary_report
        .solver_result_items
        .iter()
        .filter(|item| item.status == "failed")
        .enumerate()
        .map(|(index, item)| {
            let claim_id = format!("raw-solver-candidate-{}", index + 1);
            ExploitClaimCaptureRecord {
                claim_id: claim_id.clone(),
                status: "unconfirmed".to_string(),
                source: "binary_solver_failed_result".to_string(),
                target: target.label().to_string(),
                function: item.function.clone(),
                vc_kind: item.vc_kind.clone(),
                location: item.location.clone(),
                solver: item.solver.clone(),
                solver_status: item.status.clone(),
                raw_counterexample_present: item.detail.is_some(),
                replay_required: true,
                independent_refutation_required: true,
                diagnostic: format!(
                    "{claim_id} captures a raw solver failed result only; machine-code replay and independent refutation are required before exploit confirmation"
                ),
            }
        })
        .collect()
}

fn exploit_analyzer_stage_records(
    target: ExploitFindTarget,
    binary_report: &BinaryVerifyReport,
) -> Vec<ExploitAnalyzerStageRecord> {
    let evidence = exploit_evidence_summary(binary_report);
    let claim_capture_status = if evidence.raw_solver_candidates > 0 {
        ExploitFindStatus::Unsupported
    } else {
        ExploitFindStatus::NotRun
    };
    let claim_ids: Vec<_> = exploit_claim_capture_records(target, binary_report)
        .into_iter()
        .map(|record| record.claim_id)
        .collect();
    let target_label = target.label().to_string();
    let mut records = vec![
        ExploitAnalyzerStageRecord {
            stage: "claim_capture".to_string(),
            status: claim_capture_status.label().to_string(),
            target: target_label.clone(),
            claim_ids: claim_ids.clone(),
            evidence_required: vec!["normalized_exploit_claim".to_string()],
            evidence_present: false,
            blocks_exploit_confirmation: true,
            diagnostic: exploit_find_claim_capture_note(binary_report, &evidence),
        },
        ExploitAnalyzerStageRecord {
            stage: "replay_requirement".to_string(),
            status: evidence.replay_status.label().to_string(),
            target: target_label.clone(),
            claim_ids: claim_ids.clone(),
            evidence_required: vec!["machine_code_replay".to_string()],
            evidence_present: evidence.replay_status == ExploitFindStatus::Satisfied,
            blocks_exploit_confirmation: evidence.replay_status != ExploitFindStatus::Satisfied,
            diagnostic: exploit_find_replay_note(&evidence),
        },
        ExploitAnalyzerStageRecord {
            stage: "independent_refutation".to_string(),
            status: evidence.independent_refutation_status.label().to_string(),
            target: target_label.clone(),
            claim_ids: claim_ids.clone(),
            evidence_required: vec![
                "independent_refutation".to_string(),
                "checked_unsat_evidence_bound_to_claim".to_string(),
            ],
            evidence_present: evidence.independent_refutation_status
                == ExploitFindStatus::Satisfied,
            blocks_exploit_confirmation: evidence.independent_refutation_status
                != ExploitFindStatus::Satisfied,
            diagnostic: exploit_find_independent_refutation_note(&evidence),
        },
        ExploitAnalyzerStageRecord {
            stage: "reduction".to_string(),
            status: evidence.reduction_status.label().to_string(),
            target: target_label.clone(),
            claim_ids: claim_ids.clone(),
            evidence_required: vec!["minimized_replayable_witness".to_string()],
            evidence_present: evidence.reduction_status == ExploitFindStatus::Satisfied,
            blocks_exploit_confirmation: evidence.reduction_status != ExploitFindStatus::Satisfied,
            diagnostic: exploit_find_reducer_note(&evidence),
        },
        ExploitAnalyzerStageRecord {
            stage: "attribution".to_string(),
            status: evidence.attribution_status.label().to_string(),
            target: target_label.clone(),
            claim_ids: claim_ids.clone(),
            evidence_required: vec!["target_attribution".to_string()],
            evidence_present: evidence.attribution_status == ExploitFindStatus::Satisfied,
            blocks_exploit_confirmation: evidence.attribution_status
                != ExploitFindStatus::Satisfied,
            diagnostic: exploit_find_attribution_note(target, &evidence),
        },
        ExploitAnalyzerStageRecord {
            stage: "regression_emission".to_string(),
            status: evidence.regression_status.label().to_string(),
            target: target_label.clone(),
            claim_ids: claim_ids.clone(),
            evidence_required: vec!["regression_test_emission".to_string()],
            evidence_present: false,
            blocks_exploit_confirmation: true,
            diagnostic: exploit_find_regression_note(&evidence),
        },
    ];
    records.push(ExploitAnalyzerStageRecord {
        stage: "evidence_gate".to_string(),
        status: ExploitFindStatus::Unsupported.label().to_string(),
        target: target_label,
        claim_ids,
        evidence_required: exploit_required_evidence(),
        evidence_present: false,
        blocks_exploit_confirmation: true,
        diagnostic: "exploit_found remains false until a normalized claim is independently refuted, replayed on machine code, reduced, attributed, and emitted as a regression".to_string(),
    });
    records
}

fn exploit_analyzer_stage_diagnostic(record: &ExploitAnalyzerStageRecord) -> String {
    format!(
        "phase.{}.status={}; target={}; claim_ids={}; evidence_required={}; evidence_present={}; blocks_exploit_confirmation={}; diagnostic={}",
        record.stage,
        record.status,
        record.target,
        record.claim_ids.join(","),
        record.evidence_required.join(","),
        record.evidence_present,
        record.blocks_exploit_confirmation,
        record.diagnostic
    )
}

fn exploit_claim_capture_diagnostic(record: &ExploitClaimCaptureRecord) -> String {
    format!(
        "claim_capture_record.{}.status={}; source={}; target={}; function={}; vc_kind={}; location={}; solver={}; solver_status={}; replay_required={}; independent_refutation_required={}; diagnostic={}",
        record.claim_id,
        record.status,
        record.source,
        record.target,
        record.function,
        record.vc_kind,
        record.location.as_deref().unwrap_or("unknown"),
        record.solver,
        record.solver_status,
        record.replay_required,
        record.independent_refutation_required,
        record.diagnostic
    )
}

fn exploit_find_claim_capture_note(
    binary_report: &BinaryVerifyReport,
    evidence: &ExploitEvidenceSummary,
) -> String {
    if evidence.raw_solver_candidates > 0 {
        format!(
            "{} raw solver candidate(s) were observed, but raw solver output is not a normalized exploit claim",
            evidence.raw_solver_candidates
        )
    } else if binary_report.solver_results.status == "proved" {
        "all generated binary VCs were proved, so no exploit claim was captured".to_string()
    } else {
        format!(
            "no replayable exploit claim was captured from solver status {}",
            binary_report.solver_results.status
        )
    }
}

fn exploit_find_replay_note(evidence: &ExploitEvidenceSummary) -> String {
    if evidence.raw_solver_candidates > 0 && evidence.replay_status == ExploitFindStatus::Satisfied
    {
        format!(
            "machine-code replay satisfied for {}/{} raw solver candidate(s)",
            evidence.exact_replayed_candidates, evidence.raw_solver_candidates
        )
    } else if evidence.raw_solver_candidates > 0 {
        format!(
            "machine-code replay is required for {} raw solver candidate(s); {}/{} have exact replay evidence",
            evidence.raw_solver_candidates,
            evidence.exact_replayed_candidates,
            evidence.raw_solver_candidates
        )
    } else {
        "machine-code replay did not run because there is no normalized exploit witness".to_string()
    }
}

fn exploit_find_independent_refutation_note(evidence: &ExploitEvidenceSummary) -> String {
    if evidence.independent_refutation_status == ExploitFindStatus::Satisfied {
        format!(
            "checked UNSAT certificate evidence satisfies independent refutation for {}/{} required VC(s)",
            evidence.checked_unsat_refutations, evidence.required_vcs
        )
    } else if evidence.raw_solver_candidates > 0
        && evidence.replay_status == ExploitFindStatus::Satisfied
    {
        "independent refutation requires checked UNSAT evidence bound to the replayed candidate; exact replay alone is not proof-grade exploit evidence"
            .to_string()
    } else if evidence.raw_solver_candidates > 0 {
        "independent refutation is required before confirmation, but no replay-backed claim exists"
            .to_string()
    } else if evidence.all_required_vcs_checked_unsat {
        "checked UNSAT certificate evidence proves verification VCs, but no exploit claim was captured for independent refutation".to_string()
    } else {
        "independent refutation did not run because no exploit claim was captured".to_string()
    }
}

fn exploit_find_reducer_note(evidence: &ExploitEvidenceSummary) -> String {
    if evidence.reduction_status == ExploitFindStatus::Satisfied {
        format!(
            "deterministic identity reduction recorded for {}/{} exact-replayed candidate(s)",
            evidence.deterministically_reduced_candidates, evidence.raw_solver_candidates
        )
    } else if evidence.raw_solver_candidates > 0 {
        "counterexample reduction is blocked until a replayed candidate has checked independent-refutation evidence"
            .to_string()
    } else {
        "counterexample reduction did not run because no exploit candidate was captured".to_string()
    }
}

fn exploit_find_attribution_note(
    target: ExploitFindTarget,
    evidence: &ExploitEvidenceSummary,
) -> String {
    let target_label = target.label();
    if evidence.attribution_status == ExploitFindStatus::Satisfied {
        format!(
            "attribution to the {target_label} target is satisfied for {}/{} exact-replayed candidate(s) using deterministic solver and replay provenance",
            evidence.deterministically_attributed_candidates, evidence.raw_solver_candidates
        )
    } else if evidence.raw_solver_candidates > 0 {
        format!(
            "attribution to the {target_label} target is blocked until replay and checked independent-refutation evidence are bound to the candidate"
        )
    } else {
        format!(
            "attribution to the {target_label} target did not run because no exploit claim was captured"
        )
    }
}

fn exploit_find_regression_note(evidence: &ExploitEvidenceSummary) -> String {
    if evidence.raw_solver_candidates > 0 {
        format!(
            "non-executable regression artifact placeholder recorded for {} candidate(s), but proof-grade completion requires a real executable regression test command after replay, independent refutation, reduction, and attribution",
            evidence.raw_solver_candidates
        )
    } else if evidence.all_required_vcs_checked_unsat {
        "regression artifact placeholder remains unsupported because checked refutation evidence has no replayable exploit witness or executable regression test command".to_string()
    } else {
        "regression test emission did not run because no confirmed exploit witness exists"
            .to_string()
    }
}

fn exploit_find_fail_closed_reason(
    binary_report: &BinaryVerifyReport,
    evidence: &ExploitEvidenceSummary,
) -> String {
    let verification_detail = if binary_report.vcs == 0 {
        "binary verification did not produce VCs".to_string()
    } else if evidence.raw_solver_candidates > 0
        && evidence.replay_status == ExploitFindStatus::Satisfied
    {
        format!(
            "binary solver produced {} exact-replayed raw failed result(s), but checked independent refutation and regression still block exploit confirmation",
            evidence.raw_solver_candidates
        )
    } else if evidence.all_required_vcs_checked_unsat {
        "checked UNSAT certificate evidence proves binary VCs, but exploit-find captured no replay-backed exploit claim to refute".to_string()
    } else if binary_report.solver_results.status == "proved" {
        "binary VCs were proved only as verification conditions, not exploit evidence".to_string()
    } else if evidence.raw_solver_candidates > 0 {
        format!(
            "binary solver produced {} raw failed result(s) that require replay",
            evidence.raw_solver_candidates
        )
    } else {
        format!(
            "binary verification is unproved: solver status is {}",
            binary_report.solver_results.status
        )
    };

    format!(
        "{verification_detail}; exploit-find fails closed because claim capture, replay, independent refutation, reduction, attribution, and regression emission are not proof/replay-backed"
    )
}

fn exploit_find_notes(binary_report: &BinaryVerifyReport) -> Vec<String> {
    let mut notes = vec![
        format!("binary status: {}", binary_report.status.label()),
        format!("verification status: {}", binary_report.verification_status),
        "No exploit witness is produced or confirmed by this command".to_string(),
        "Solver counterexamples, when present, require machine-code replay before they can be treated as concrete binary exploits".to_string(),
    ];

    if binary_report.unsupported > 0 {
        notes.push(format!(
            "unsupported binary coverage remains: {} item(s)",
            binary_report.unsupported
        ));
    }
    if binary_report.failures > 0 {
        notes.push(format!("binary pipeline failures: {} item(s)", binary_report.failures));
    }

    notes
}

fn is_rust_skeleton_advisory(record: &UnsupportedRecord) -> bool {
    record.feature.contains("Rust skeleton is exploratory")
}

fn format_unsupported_record(record: &UnsupportedRecord) -> String {
    let location = record
        .origin
        .as_ref()
        .map(|origin| format!(" @ 0x{:x}", origin.instruction_address))
        .unwrap_or_default();
    format!("{}{}: {}", record.stage, location, record.feature)
}

fn decompile_output_kind_label(kind: DecompileOutputKind) -> &'static str {
    match kind {
        DecompileOutputKind::TrustIrJson => "trust_ir_json",
        DecompileOutputKind::TrustIrText => "trust_ir_text",
        DecompileOutputKind::RustSkeleton => "rust_skeleton",
        DecompileOutputKind::TrustCgText => "trust_cg_text",
        DecompileOutputKind::WasmText => "wasm_text",
        DecompileOutputKind::TrustCgUnsupported => "trust_cg_unsupported",
        DecompileOutputKind::WasmUnsupported => "wasm_unsupported",
        _ => "unknown",
    }
}

fn decompiled_output_kind_label(output: &DecompiledOutput, target: DecompileTarget) -> String {
    match target {
        DecompileTarget::TrustCg => return "trust_cg_text".to_string(),
        DecompileTarget::Wasm => return "wasm_text".to_string(),
        _ => {}
    }
    if let Some(kind) =
        output.diagnostics.iter().find_map(|diagnostic| diagnostic.strip_prefix("format="))
    {
        return kind.replace('-', "_");
    }
    match target {
        DecompileTarget::TrustIr => "trust_ir".to_string(),
        DecompileTarget::Rust => "rust_skeleton".to_string(),
        DecompileTarget::TrustCg => "trust_cg_text".to_string(),
        DecompileTarget::Wasm => "wasm_text".to_string(),
    }
}

fn decompiled_output_validation_label(
    output: &DecompiledOutput,
    target: DecompileTarget,
) -> String {
    match target {
        DecompileTarget::TrustCg | DecompileTarget::Wasm => match output.validation {
            ReconstructionValidationStatus::Validated
                if output.trust_level == TrustLevel::Rejected =>
            {
                "inspectable_rejected".to_string()
            }
            ReconstructionValidationStatus::Validated => "validated_partial".to_string(),
            ReconstructionValidationStatus::Failed | ReconstructionValidationStatus::Refuted => {
                "translation_rejected".to_string()
            }
            ReconstructionValidationStatus::Unknown => "validation_unknown_partial".to_string(),
            ReconstructionValidationStatus::NotAttempted => {
                "translation_not_validated_partial".to_string()
            }
            _ => "validation_unknown_partial".to_string(),
        },
        _ => decompile_target_validation(target).to_string(),
    }
}

fn decompiled_output_validation_note(output: &DecompiledOutput, target: DecompileTarget) -> String {
    match target {
        DecompileTarget::TrustCg => match output.validation {
            ReconstructionValidationStatus::Validated => {
                "trust-cg text passed structural validation, but remains partial and is not proof-grade"
                    .to_string()
            }
            ReconstructionValidationStatus::Failed | ReconstructionValidationStatus::Refuted => {
                "trust-cg text conversion was rejected; no proof-grade artifact was produced"
                    .to_string()
            }
            _ => "trust-cg text output is partial unless validated; no proof-grade artifact was produced"
                .to_string(),
        },
        DecompileTarget::Wasm => match output.validation {
            ReconstructionValidationStatus::Validated => {
                "Wasm text passed subset validation, but remains partial and is not proof-grade"
                    .to_string()
            }
            ReconstructionValidationStatus::Failed | ReconstructionValidationStatus::Refuted => {
                "Wasm text conversion was rejected; no proof-grade artifact was produced"
                    .to_string()
            }
            _ => "Wasm text output is partial unless validated; no proof-grade artifact was produced"
                .to_string(),
        },
        _ => decompile_validation_note(target).to_string(),
    }
}

fn trust_level_label(level: TrustLevel) -> &'static str {
    match level {
        TrustLevel::ProofGrade => "proof_grade",
        TrustLevel::Partial => "partial",
        TrustLevel::Exploratory => "exploratory",
        TrustLevel::Rejected => "rejected",
        _ => "unknown",
    }
}

fn binary_verification_status_label(status: BinaryVerificationStatus) -> &'static str {
    match status {
        BinaryVerificationStatus::NotRun => "not_run",
        BinaryVerificationStatus::Proved => "proved",
        BinaryVerificationStatus::Refuted => "refuted",
        BinaryVerificationStatus::Unknown => "unknown",
        BinaryVerificationStatus::Timeout => "timeout",
        BinaryVerificationStatus::Unsupported => "unsupported",
        BinaryVerificationStatus::Rejected => "rejected",
        BinaryVerificationStatus::Mixed => "mixed",
        _ => "unknown",
    }
}

fn binary_artifact_format_label(format: BinaryArtifactFormat) -> &'static str {
    match format {
        BinaryArtifactFormat::Elf => "ELF",
        BinaryArtifactFormat::MachO => "Mach-O",
        BinaryArtifactFormat::FatMachO => "Fat Mach-O",
        BinaryArtifactFormat::Pe => "PE/COFF",
        BinaryArtifactFormat::Wasm => "Wasm",
        BinaryArtifactFormat::Raw => "Raw",
        BinaryArtifactFormat::Unknown => "unknown",
        _ => "unknown",
    }
}

fn binary_selection_label(entry: Option<u64>, all_functions: bool) -> &'static str {
    if all_functions {
        "all"
    } else if entry.is_some() {
        "address"
    } else {
        "entry"
    }
}

fn decompile_target_trust_level(target: DecompileTarget) -> &'static str {
    match target {
        DecompileTarget::TrustIr => "partial",
        DecompileTarget::Rust => "exploratory",
        DecompileTarget::TrustCg | DecompileTarget::Wasm => "partial",
    }
}

fn decompile_target_validation(target: DecompileTarget) -> &'static str {
    match target {
        DecompileTarget::TrustIr => "lifted_trust_ir_partial",
        DecompileTarget::Rust => "exploratory_not_validated",
        DecompileTarget::TrustCg => "trust_cg_text_partial",
        DecompileTarget::Wasm => "wasm_text_partial",
    }
}

fn decompile_validation_note(target: DecompileTarget) -> &'static str {
    match target {
        DecompileTarget::TrustIr => {
            "TrustIr output is partial; no verification summary is attached proving full coverage"
        }
        DecompileTarget::Rust => {
            "Rust output is exploratory/not validated; no reconstruction validation was performed"
        }
        DecompileTarget::TrustCg => {
            "trust-cg text output is partial unless validated; no proof-grade artifact was produced"
        }
        DecompileTarget::Wasm => {
            "Wasm text output is partial unless validated; no proof-grade artifact was produced"
        }
    }
}

fn merge_vc_counts<'a>(
    counts: impl IntoIterator<Item = &'a BinaryVcKindCount>,
) -> Vec<BinaryVcKindCount> {
    let mut merged = BTreeMap::<String, usize>::new();
    for count in counts {
        *merged.entry(count.kind.clone()).or_insert(0) += count.count;
    }
    merged.into_iter().map(|(kind, count)| BinaryVcKindCount { kind, count }).collect()
}

fn verify_binary_should_fail(report: &BinaryVerifyReport) -> bool {
    report.failures > 0
        || report.strict && report.unsupported > 0
        || report.unsupported > 0 && report.functions_analyzed == 0
        || report.vcs == 0
        || report.vcs > 0 && report.solver_results.status != "proved"
        || report
            .checked_certificate_import
            .as_ref()
            .is_some_and(CheckedCertificateImportReport::loader_failed)
        || report
            .checked_certificate_production
            .as_ref()
            .is_some_and(CheckedCertificateProductionReport::is_blocked)
}

fn render_lift_terminal(report: &BinaryLiftReport) -> String {
    use std::fmt::Write as _;

    let mut out = String::new();
    writeln!(out, "targo trust lift report").expect("write to string");
    writeln!(out, "binary: {}", report.binary).expect("write to string");
    writeln!(out, "format: {}", report.format.as_deref().unwrap_or("unknown"))
        .expect("write to string");
    writeln!(out, "architecture: {}", report.architecture.as_deref().unwrap_or("unknown"))
        .expect("write to string");
    writeln!(out, "selection: {}", report.selection).expect("write to string");
    writeln!(out, "entry: {}", report.entry.as_deref().unwrap_or("default"))
        .expect("write to string");
    writeln!(out, "binary entry: {}", report.binary_entry.as_deref().unwrap_or("unknown"))
        .expect("write to string");
    writeln!(out, "strict: {}", report.strict).expect("write to string");
    writeln!(out, "functions lifted: {}", report.functions_lifted).expect("write to string");
    writeln!(out, "blocks: {}", report.blocks).expect("write to string");
    writeln!(out, "statements: {}", report.statements).expect("write to string");
    writeln!(out, "vcs: {}", report.vcs).expect("write to string");
    writeln!(out, "unsupported: {}", report.unsupported).expect("write to string");
    writeln!(out, "failures: {}", report.failures).expect("write to string");
    writeln!(out, "status: {}", report.status.label()).expect("write to string");

    if !report.functions.is_empty() {
        writeln!(out, "functions:").expect("write to string");
        for function in &report.functions {
            writeln!(
                out,
                "  - {} @ {}: blocks={} statements={} vcs={}",
                function.name,
                function.entry.as_deref().unwrap_or("unknown"),
                function.blocks,
                function.statements,
                function.vcs
            )
            .expect("write to string");
        }
    }

    if !report.unsupported_items.is_empty() {
        writeln!(out, "unsupported items:").expect("write to string");
        for item in &report.unsupported_items {
            writeln!(out, "  - {item}").expect("write to string");
        }
    }

    if !report.failure_items.is_empty() {
        writeln!(out, "failures:").expect("write to string");
        for item in &report.failure_items {
            writeln!(out, "  - {item}").expect("write to string");
        }
    }

    out
}

fn render_verify_binary_terminal(report: &BinaryVerifyReport) -> String {
    use std::fmt::Write as _;

    let mut out = String::new();
    writeln!(out, "targo trust verify-binary report").expect("write to string");
    writeln!(out, "binary: {}", report.binary).expect("write to string");
    writeln!(out, "format: {}", report.format.as_deref().unwrap_or("unknown"))
        .expect("write to string");
    writeln!(out, "architecture: {}", report.architecture.as_deref().unwrap_or("unknown"))
        .expect("write to string");
    writeln!(out, "selection: {}", report.selection).expect("write to string");
    writeln!(out, "entry: {}", report.entry.as_deref().unwrap_or("default"))
        .expect("write to string");
    writeln!(out, "binary entry: {}", report.binary_entry.as_deref().unwrap_or("unknown"))
        .expect("write to string");
    writeln!(out, "strict: {}", report.strict).expect("write to string");
    writeln!(out, "functions analyzed: {}", report.functions_analyzed).expect("write to string");
    writeln!(out, "blocks: {}", report.blocks).expect("write to string");
    writeln!(out, "statements: {}", report.statements).expect("write to string");
    writeln!(out, "vcs generated: {}", report.vcs).expect("write to string");
    writeln!(out, "unsupported: {}", report.unsupported).expect("write to string");
    writeln!(out, "failures: {}", report.failures).expect("write to string");
    writeln!(out, "status: {}", report.status.label()).expect("write to string");
    writeln!(out, "verification status: {}", report.verification_status).expect("write to string");
    writeln!(out, "trust level: {}", report.trust_level).expect("write to string");
    let solver_route = solver_route_diagnostic(None, BinarySolverRoute::AYIncremental);
    writeln!(out, "solver route: {}", solver_route.selected).expect("write to string");
    writeln!(out, "solver route status: {}", solver_route.status).expect("write to string");
    writeln!(out, "solver route detail: {}", solver_route.detail).expect("write to string");
    writeln!(out, "solver results: {}", report.solver_results.status).expect("write to string");
    writeln!(
        out,
        "solver counts: total={} proved={} failed={} unknown={} timeout={}",
        report.solver_results.total,
        report.solver_results.proved,
        report.solver_results.failed,
        report.solver_results.unknown,
        report.solver_results.timeout
    )
    .expect("write to string");

    let proof_gate = build_binary_cli_proof_grade_gate(report);
    writeln!(out, "proof-grade gate: {}", proof_gate.status).expect("write to string");
    writeln!(
        out,
        "proof-grade gate detail: unsupported_empty={} vcs_proved={} checked_certs={} replay_coverage={} replay_semantics={} exact_replay_slice_attestation={} raw_solver_proof_bytes_sufficient={}",
        proof_gate.unsupported_ledger_empty,
        proof_gate.all_required_vcs_proved,
        proof_gate.checked_certificates_for_all_required_vcs,
        proof_gate.full_replay_coverage,
        proof_gate.replay_semantics_satisfied,
        proof_gate.exact_replay_slice_attestation_for_replayed_vcs,
        proof_gate.raw_solver_proof_bytes_sufficient
    )
    .expect("write to string");
    writeln!(
        out,
        "proof-grade counts: required_vcs={} proved={} checked_certs={} replayed={} exact_replay_slice_attested={} cert_only_replay_semantics={} replay_semantics_satisfied={} raw_solver_proof_bytes={}",
        proof_gate.required_vcs,
        proof_gate.proved_vcs,
        proof_gate.checked_certificates,
        proof_gate.replayed_vcs,
        proof_gate.exact_replay_slice_attested_vcs,
        proof_gate.certificate_only_replay_semantics_vcs,
        proof_gate.replay_semantics_satisfied_vcs,
        proof_gate.raw_solver_proof_bytes
    )
    .expect("write to string");

    let proof_evidence = build_binary_verify_proof_evidence_report(report);
    writeln!(
        out,
        "proof evidence: total_vcs={} solver_dispatches={} replay={:?} checked_certs={}/{} raw_solver_proof_byte_count={} shared_proof_grade_gate={}",
        proof_evidence.total_vcs,
        proof_evidence.solver_dispatches,
        proof_evidence.replay,
        proof_evidence.checked_certificate_coverage.checked_certificates,
        proof_evidence.checked_certificate_coverage.required_vcs,
        proof_evidence.raw_solver_proof_byte_count,
        if proof_evidence.proof_grade_gate.accepted { "accepted" } else { "rejected" }
    )
    .expect("write to string");
    write_source_backpropagation_gate_terminal(
        &mut out,
        &build_verify_binary_source_backpropagation_gate(report),
    );
    writeln!(
        out,
        "proof evidence solver dispatch counts: {}",
        binary_verify_counts_label(&proof_evidence.solver_dispatch_status_counts)
    )
    .expect("write to string");
    writeln!(
        out,
        "proof evidence replay counts: {}",
        binary_verify_counts_label(&proof_evidence.replay_status_counts)
    )
    .expect("write to string");
    writeln!(
        out,
        "proof evidence certificate coverage: candidates={} checked={} missing={} raw_solver_proof_bytes={} raw_solver_proof_byte_count={} raw_solver_bytes_sufficient={}",
        proof_evidence.checked_certificate_coverage.certificate_candidates,
        proof_evidence.checked_certificate_coverage.checked_certificates,
        proof_evidence.checked_certificate_coverage.missing_checked_certificates,
        proof_evidence.checked_certificate_coverage.raw_solver_proof_bytes,
        proof_evidence.checked_certificate_coverage.raw_solver_proof_byte_count,
        proof_evidence.checked_certificate_coverage.raw_solver_proof_bytes_satisfy_coverage
    )
    .expect("write to string");
    if let Some(import) = &report.checked_certificate_import {
        writeln!(
            out,
            "checked certificate import: loaded={} imported={} unmatched={} rejected={} dispatches_missing_canonical_binding={}",
            import.loaded_artifacts,
            import.imported,
            import.unmatched_artifacts,
            import.rejected_artifacts,
            import.dispatches_missing_canonical_binding
        )
        .expect("write to string");
        if !import.diagnostics.is_empty() {
            writeln!(out, "checked certificate import diagnostics:").expect("write to string");
            for diagnostic in &import.diagnostics {
                writeln!(out, "  - {diagnostic}").expect("write to string");
            }
        }
        if !import.artifacts.is_empty() {
            writeln!(out, "checked certificate import artifacts:").expect("write to string");
            for artifact in &import.artifacts {
                let path = artifact.artifact_path.as_deref().unwrap_or("<in-memory>");
                let dispatch = artifact.dispatch_id.as_deref().unwrap_or("<unmatched>");
                writeln!(
                    out,
                    "  - status={} checker={} checker_version={} format={} checked_at_unix_ms={} certificate_sha256={} vc_sha256={} origin_sha256={} dispatch={} path={}",
                    artifact.status,
                    artifact.checker,
                    artifact.checker_version,
                    artifact.format,
                    artifact.checked_at_unix_ms,
                    artifact.certificate_sha256,
                    artifact.vc_sha256,
                    artifact.origin_sha256,
                    dispatch,
                    path
                )
                .expect("write to string");
            }
        }
    }
    if let Some(production) = &report.checked_certificate_production {
        writeln!(
            out,
            "checked certificate production: status={} export_dir={} checker_selection={} candidates={} canonical_bindings={} proof_exports={} raw_solver_proof_bytes={} already_checked={} exported={} rejected={}",
            production.status,
            production.export_dir,
            production.checker_selection,
            production.candidate_dispatches,
            production.canonical_binding_candidates,
            production.proof_export_candidates,
            production.raw_solver_proof_byte_dispatches,
            production.already_checked_certificates,
            production.exported_artifacts,
            production.rejected_dispatches
        )
        .expect("write to string");
        if !production.blockers.is_empty() {
            writeln!(out, "checked certificate production blockers:").expect("write to string");
            for blocker in &production.blockers {
                writeln!(out, "  - {blocker}").expect("write to string");
            }
        }
        if !production.proof_export_records.is_empty() {
            writeln!(out, "checked certificate production proof exports:")
                .expect("write to string");
            for record in &production.proof_export_records {
                writeln!(
                    out,
                    "  - dispatch={} status={} canonical_binding={} proof_sha256={} proof_metadata_path={} proof_payload_path={} raw_solver_proof_bytes={} blockers={}",
                    record.dispatch_id,
                    record.status,
                    record.canonical_binding,
                    record.proof_sha256.as_deref().unwrap_or("none"),
                    record.proof_export_metadata_path.as_deref().unwrap_or("none"),
                    record.proof_export_payload_path.as_deref().unwrap_or("none"),
                    record
                        .raw_solver_proof_bytes
                        .as_ref()
                        .map(|raw| raw.byte_len.to_string())
                        .unwrap_or_else(|| "0".to_string()),
                    if record.blocker_codes.is_empty() {
                        "none".to_string()
                    } else {
                        record.blocker_codes.join(",")
                    }
                )
                .expect("write to string");
            }
        }
        if !production.certificate_check_records.is_empty() {
            writeln!(out, "checked certificate production checks:").expect("write to string");
            for record in &production.certificate_check_records {
                writeln!(
                    out,
                    "  - dispatch={} status={} certificate_status={} checker={} blockers={}",
                    record.dispatch_id,
                    record.status,
                    record.certificate_status,
                    record.checker.as_deref().unwrap_or("none"),
                    if record.blocker_codes.is_empty() {
                        "none".to_string()
                    } else {
                        record.blocker_codes.join(",")
                    }
                )
                .expect("write to string");
            }
        }
        if !production.export_row_records.is_empty() {
            writeln!(out, "checked certificate production export rows:").expect("write to string");
            for record in &production.export_row_records {
                writeln!(
                    out,
                    "  - dispatch={} vc_sha256={} origin_sha256={} assumption_digest={} query_semantics={:?} replay={:?} selected_image_sha256={} source_gate_sha256={} manifest_identity_sha256={}",
                    record.dispatch_id,
                    record.vc_sha256,
                    record.origin_sha256,
                    record.assumption_digest,
                    record.query_semantics,
                    record.replay,
                    record.selected_image_identity.sha256,
                    record.source_backpropagation_gate_sha256,
                    record.manifest_identity_sha256
                )
                .expect("write to string");
            }
        }
        if !production.diagnostics.is_empty() {
            writeln!(out, "checked certificate production diagnostics:").expect("write to string");
            for diagnostic in &production.diagnostics {
                writeln!(out, "  - {diagnostic}").expect("write to string");
            }
        }
    }
    if !proof_gate.rejections.is_empty() {
        writeln!(out, "proof-grade rejections:").expect("write to string");
        for rejection in &proof_gate.rejections {
            writeln!(out, "  - {rejection}").expect("write to string");
        }
    }

    if !report.vc_counts.is_empty() {
        writeln!(out, "vc counts:").expect("write to string");
        for count in &report.vc_counts {
            writeln!(out, "  - {}: {}", count.kind, count.count).expect("write to string");
        }
    }

    if !report.functions.is_empty() {
        writeln!(out, "functions:").expect("write to string");
        for function in &report.functions {
            writeln!(
                out,
                "  - {} @ {}: blocks={} statements={} vcs={}",
                function.name,
                function.entry.as_deref().unwrap_or("unknown"),
                function.blocks,
                function.statements,
                function.vcs
            )
            .expect("write to string");

            for count in &function.vc_counts {
                writeln!(out, "    - {}: {}", count.kind, count.count).expect("write to string");
            }
        }
    }

    if !report.solver_result_items.is_empty() {
        writeln!(out, "solver result items:").expect("write to string");
        for item in &report.solver_result_items {
            let location = item.location.as_deref().unwrap_or("unknown");
            let mut notes = Vec::new();
            if let Some(detail) = item.detail.as_deref() {
                notes.push(detail.to_string());
            }
            if let Some(replay_status) = item.replay_status.as_deref() {
                let replay_note = match item.replay_detail.as_deref() {
                    Some(replay_detail) => format!("replay={replay_status}: {replay_detail}"),
                    None => format!("replay={replay_status}"),
                };
                notes.push(replay_note);
            }
            if !item.replay_capability_evidence.is_empty() {
                notes.push(replay_capability_evidence_note(
                    &item.replay_capability_evidence,
                    item.replay_capability_evidence_matched,
                ));
            }
            if notes.is_empty() {
                writeln!(
                    out,
                    "  - {} {} @ {}: {} via {}",
                    item.function, item.vc_kind, location, item.status, item.solver
                )
                .expect("write to string");
            } else {
                writeln!(
                    out,
                    "  - {} {} @ {}: {} via {} ({})",
                    item.function,
                    item.vc_kind,
                    location,
                    item.status,
                    item.solver,
                    notes.join("; ")
                )
                .expect("write to string");
            }
        }
    }

    if !report.unsupported_items.is_empty() {
        writeln!(out, "unsupported items:").expect("write to string");
        for item in &report.unsupported_items {
            writeln!(out, "  - {item}").expect("write to string");
        }
    }

    if !report.failure_items.is_empty() {
        writeln!(out, "failures:").expect("write to string");
        for item in &report.failure_items {
            writeln!(out, "  - {item}").expect("write to string");
        }
    }

    out
}

fn write_source_backpropagation_gate_terminal(
    out: &mut String,
    gate: &SourceBackpropagationGateReport,
) {
    use std::fmt::Write as _;

    writeln!(out, "source backpropagation gate: {}", gate.status).expect("write to string");
    writeln!(
        out,
        "source backpropagation detail: source_provenance={} binary_verification={} reconstruction={} checked_certificate_source_backpropagation_gate={}",
        gate.source_provenance,
        gate.binary_verification_evidence,
        gate.reconstruction_evidence,
        gate.checked_certificate_source_backpropagation_gate
    )
    .expect("write to string");
    if !gate.blockers.is_empty() {
        writeln!(out, "source backpropagation blockers:").expect("write to string");
        for blocker in &gate.blockers {
            writeln!(out, "  - {}: {}", blocker.code, blocker.detail).expect("write to string");
        }
    }
}

fn replay_capability_evidence_note(
    evidence: &[trust_symex::BinaryMachineReplayCapabilityEvidence],
    matched: Option<bool>,
) -> String {
    let entries = evidence
        .iter()
        .map(|record| format!("{}@0x{:x}", record.capability, record.instruction_address))
        .collect::<Vec<_>>()
        .join(",");
    format!(
        "replay_capability_evidence matched={} entries={}",
        matched.map(|value| value.to_string()).unwrap_or_else(|| "unknown".to_string()),
        entries
    )
}

#[cfg(test)]
fn render_decompile_terminal(report: &DecompileReport) -> String {
    render_decompile_terminal_with_command("decompile", report)
}

#[cfg(test)]
fn render_convert_terminal(report: &DecompileReport) -> String {
    render_convert_terminal_with_checked_certificate_loader(
        report,
        convert_checked_certificate_loader_not_requested(),
    )
}

fn render_convert_terminal_with_checked_certificate_loader(
    report: &DecompileReport,
    checked_certificate_loader: ConvertCheckedCertificateLoaderReport,
) -> String {
    render_decompile_terminal_with_command_and_loader(
        "convert",
        report,
        Some(checked_certificate_loader),
    )
}

#[cfg(test)]
fn render_decompile_terminal_with_command(command: &str, report: &DecompileReport) -> String {
    render_decompile_terminal_with_command_and_loader(command, report, None)
}

fn render_decompile_terminal_with_command_and_loader(
    command: &str,
    report: &DecompileReport,
    checked_certificate_loader: Option<ConvertCheckedCertificateLoaderReport>,
) -> String {
    use std::fmt::Write as _;

    let mut out = String::new();
    writeln!(out, "targo trust {command} report").expect("write to string");
    writeln!(out, "binary: {}", report.binary).expect("write to string");
    writeln!(out, "format: {}", report.format.as_deref().unwrap_or("unknown"))
        .expect("write to string");
    writeln!(out, "architecture: {}", report.architecture.as_deref().unwrap_or("unknown"))
        .expect("write to string");
    writeln!(out, "selection: {}", report.selection).expect("write to string");
    writeln!(out, "entry: {}", report.entry.as_deref().unwrap_or("default"))
        .expect("write to string");
    writeln!(out, "binary entry: {}", report.binary_entry.as_deref().unwrap_or("unknown"))
        .expect("write to string");
    writeln!(
        out,
        "source provenance: status={} exact_mappings={} ambiguous_mappings={} source_backpropagation={}",
        report.source_provenance.status,
        report.source_provenance.exact_mapping_count,
        report.source_provenance.ambiguous_mapping_count,
        if report.source_provenance.effective_source_backpropagation_allowed() {
            "allowed"
        } else {
            "rejected"
        }
    )
    .expect("write to string");
    for diagnostic in report.source_provenance.typed_diagnostics() {
        writeln!(
            out,
            "source provenance diagnostic: {}: {}",
            diagnostic.kind.label(),
            diagnostic.message
        )
        .expect("write to string");
    }
    let source_backpropagation_gate = checked_certificate_loader
        .as_ref()
        .map(|loader| {
            let checked_certificate_source_backpropagation_gate =
                checked_certificate_source_backpropagation_gate_status_for_convert_loader(loader);
            build_decompile_source_backpropagation_gate_with_checked_certificate_status(
                report,
                "targo-trust::binary-source-backprop",
                checked_certificate_source_backpropagation_gate.as_str(),
            )
        })
        .unwrap_or_else(|| {
            build_decompile_source_backpropagation_gate(
                report,
                "targo-trust::binary-source-backprop",
            )
        });
    write_source_backpropagation_gate_terminal(&mut out, &source_backpropagation_gate);
    writeln!(out, "strict: {}", report.strict).expect("write to string");
    writeln!(out, "target: {}", report.target.label()).expect("write to string");
    writeln!(out, "output kind: {}", report.output_kind.as_deref().unwrap_or("none"))
        .expect("write to string");
    writeln!(out, "output trust: {}", report.output_trust_level).expect("write to string");
    writeln!(out, "output validation: {}", report.output_validation).expect("write to string");
    writeln!(out, "note: {}", report.validation_note).expect("write to string");
    writeln!(out, "functions decompiled: {}", report.functions_decompiled)
        .expect("write to string");
    writeln!(out, "blocks: {}", report.blocks).expect("write to string");
    writeln!(out, "instructions: {}", report.instructions).expect("write to string");
    writeln!(out, "statements: {}", report.statements).expect("write to string");
    writeln!(out, "memory facts: {}", report.memory_facts).expect("write to string");
    writeln!(out, "unsupported: {}", report.unsupported).expect("write to string");
    writeln!(out, "failures: {}", report.failures).expect("write to string");
    writeln!(out, "status: {}", report.status.label()).expect("write to string");
    writeln!(
        out,
        "binary evidence: verification_status={} trust_level={} replay={} proof_certificate={} dispatches={} checked_certificates={} unsupported_ledger={} release_gate={}",
        report.binary_evidence.verification_status,
        report.binary_evidence.verification_trust_level,
        report.binary_evidence.replay_status,
        report.binary_evidence.proof_certificate.status,
        report.binary_evidence.solver_dispatches.len(),
        report.binary_evidence.checked_certificate_dispatches,
        report.binary_evidence.unsupported_ledger.total_records,
        report.binary_evidence.release_gate.status
    )
    .expect("write to string");
    if !report.binary_evidence.release_gate.blockers.is_empty() {
        writeln!(out, "binary evidence blockers:").expect("write to string");
        for blocker in &report.binary_evidence.release_gate.blockers {
            writeln!(out, "  - {}: {}", blocker.code, blocker.detail).expect("write to string");
        }
    }

    if let Some(production) =
        checked_certificate_loader.as_ref().and_then(|loader| loader.production_export.as_ref())
    {
        writeln!(
            out,
            "checked certificate production export: status={} export_dir={} checker_selection={} candidates={} canonical_bindings={} proof_exports={} exported={} rejected={}",
            production.status,
            production.export_dir,
            production.checker_selection,
            production.candidate_dispatches,
            production.canonical_binding_candidates,
            production.proof_export_candidates,
            production.exported_artifacts,
            production.rejected_dispatches
        )
        .expect("write to string");
        if !production.artifact_paths.is_empty() {
            writeln!(out, "checked certificate production artifacts:").expect("write to string");
            for path in &production.artifact_paths {
                writeln!(out, "  - {path}").expect("write to string");
            }
        }
        if !production.blockers.is_empty() {
            writeln!(out, "checked certificate production blockers:").expect("write to string");
            for blocker in &production.blockers {
                writeln!(out, "  - {}: {}", blocker.code, blocker.detail).expect("write to string");
            }
        }
    }

    if command == "convert" {
        let gate = build_convert_cli_gate_with_loader(
            report,
            checked_certificate_loader
                .unwrap_or_else(convert_checked_certificate_loader_not_requested),
        );
        writeln!(out, "conversion gate: {}", gate.status).expect("write to string");
        writeln!(
            out,
            "conversion gate detail: target={} proof_grade_artifact={} validation={}",
            gate.target, gate.proof_grade_artifact, gate.validation
        )
        .expect("write to string");
        writeln!(
            out,
            "conversion checked-certificate evidence: status={} required={} proof_grade_release_accepted={} normalized_exports={} checker_successes={} checked_certificates={} raw_solver_proof_bytes_sufficient={}",
            gate.checked_certificate_evidence.status,
            gate.checked_certificate_evidence.required,
            gate.checked_certificate_evidence.proof_grade_release_accepted,
            gate.checked_certificate_evidence.normalized_solver_proof_exports,
            gate.checked_certificate_evidence.checker_successes,
            gate.checked_certificate_evidence.checked_certificates,
            gate.checked_certificate_evidence.raw_solver_proof_bytes_sufficient
        )
        .expect("write to string");
        let inventory = &gate.checked_certificate_evidence.production_positive_golden_inventory;
        if inventory.required {
            writeln!(
                out,
                "production-positive golden inventory: status={} target={} missing={}",
                inventory.status,
                inventory.target,
                inventory.missing_artifacts.len()
            )
            .expect("write to string");
            if !inventory.missing_artifacts.is_empty() {
                writeln!(out, "production-positive missing artifacts:").expect("write to string");
                for artifact in &inventory.missing_artifacts {
                    writeln!(out, "  - {}: {}", artifact.artifact, artifact.detail)
                        .expect("write to string");
                }
            }
        }
        if !gate.checked_certificate_evidence.blockers.is_empty() {
            writeln!(out, "conversion checked-certificate blockers:").expect("write to string");
            for blocker in &gate.checked_certificate_evidence.blockers {
                writeln!(out, "  - {}: {}", blocker.code, blocker.detail).expect("write to string");
            }
        }
        if !gate.blockers.is_empty() {
            writeln!(out, "conversion gate blockers:").expect("write to string");
            for blocker in &gate.blockers {
                writeln!(out, "  - {blocker}").expect("write to string");
            }
        }
        if !gate.validation_blockers.is_empty() {
            writeln!(out, "conversion validation blockers:").expect("write to string");
            for blocker in &gate.validation_blockers {
                writeln!(out, "  - {blocker}").expect("write to string");
            }
        }
    }

    if !report.functions.is_empty() {
        writeln!(out, "functions:").expect("write to string");
        for function in &report.functions {
            writeln!(
                out,
                "  - {} @ {}: blocks={} instructions={} statements={} memory_facts={} unsupported={}",
                function.name,
                function.entry,
                function.blocks,
                function.instructions,
                function.statements,
                function.memory_facts,
                function.unsupported
            )
            .expect("write to string");
        }
    }

    if !report.unsupported_items.is_empty() {
        writeln!(out, "unsupported items:").expect("write to string");
        for item in &report.unsupported_items {
            writeln!(out, "  - {item}").expect("write to string");
        }
    }

    if !report.failure_items.is_empty() {
        writeln!(out, "failures:").expect("write to string");
        for item in &report.failure_items {
            writeln!(out, "  - {item}").expect("write to string");
        }
    }

    if !report.target_validation_blockers.is_empty() {
        writeln!(out, "target validation blockers:").expect("write to string");
        for blocker in &report.target_validation_blockers {
            writeln!(out, "  - {}", format_target_validation_blocker(blocker))
                .expect("write to string");
        }
    }

    if !report.preserved_symbolic_formulas.is_empty() {
        writeln!(out, "preserved symbolic formulas:").expect("write to string");
        for formula in &report.preserved_symbolic_formulas {
            writeln!(out, "  - {}", format_preserved_symbolic_formula(formula))
                .expect("write to string");
        }
    }

    out
}

fn render_exploit_find_terminal(report: &ExploitFindReport) -> String {
    use std::fmt::Write as _;

    let mut out = String::new();
    writeln!(out, "targo trust exploit-find report").expect("write to string");
    writeln!(out, "input: {}", report.input).expect("write to string");
    writeln!(out, "target: {}", report.target.label()).expect("write to string");
    writeln!(out, "status: {}", report.status.label()).expect("write to string");
    writeln!(out, "exploit_found: {}", report.exploit_found).expect("write to string");
    writeln!(out, "binary status: {}", report.binary_status.label()).expect("write to string");
    writeln!(out, "verification status: {}", report.verification_status).expect("write to string");
    writeln!(out, "functions analyzed: {}", report.functions_analyzed).expect("write to string");
    writeln!(out, "vcs generated: {}", report.vcs).expect("write to string");
    writeln!(out, "unsupported: {}", report.unsupported).expect("write to string");
    writeln!(out, "failures: {}", report.failures).expect("write to string");
    writeln!(out, "solver results: {}", report.solver_results.status).expect("write to string");
    writeln!(
        out,
        "solver counts: total={} proved={} failed={} unknown={} timeout={}",
        report.solver_results.total,
        report.solver_results.proved,
        report.solver_results.failed,
        report.solver_results.unknown,
        report.solver_results.timeout
    )
    .expect("write to string");
    if !report.vc_counts.is_empty() {
        writeln!(out, "vc counts:").expect("write to string");
        for count in &report.vc_counts {
            writeln!(out, "  - {}: {}", count.kind, count.count).expect("write to string");
        }
    }
    writeln!(out, "synthesis: {}", report.synthesis_status.label()).expect("write to string");
    writeln!(out, "synthesis note: {}", report.synthesis_note).expect("write to string");
    writeln!(out, "replay: {}", report.replay_status.label()).expect("write to string");
    writeln!(out, "replay note: {}", report.replay_note).expect("write to string");
    writeln!(out, "independent refutation: {}", report.independent_refutation_status.label())
        .expect("write to string");
    writeln!(out, "independent refutation note: {}", report.independent_refutation_note)
        .expect("write to string");
    writeln!(out, "reducer: {}", report.reducer_status.label()).expect("write to string");
    writeln!(out, "reducer note: {}", report.reducer_note).expect("write to string");
    writeln!(out, "reason: {}", report.reason).expect("write to string");
    let evidence_gate = build_exploit_evidence_gate(report);
    writeln!(out, "evidence gate: {}", evidence_gate.status).expect("write to string");
    writeln!(
        out,
        "evidence gate detail: proof_grade_complete={} unsupported_evidence_blocks_completion={} claim_capture={} replay={} independent_refutation={} reduction={} attribution={} regression_emission={} exploit_found={}",
        evidence_gate.proof_grade_complete,
        evidence_gate.unsupported_evidence_blocks_completion,
        evidence_gate.claim_capture,
        evidence_gate.replay,
        evidence_gate.independent_refutation,
        evidence_gate.reduction,
        evidence_gate.attribution,
        evidence_gate.regression_emission,
        evidence_gate.exploit_found
    )
    .expect("write to string");
    if !evidence_gate.blockers.is_empty() {
        writeln!(out, "evidence gate blockers:").expect("write to string");
        for blocker in &evidence_gate.blockers {
            writeln!(out, "  - {blocker}").expect("write to string");
        }
    }

    let stage_records = exploit_analyzer_stage_records(report.target, &report.binary_report);
    if !stage_records.is_empty() {
        writeln!(out, "analyzer stage records:").expect("write to string");
        for record in &stage_records {
            writeln!(
                out,
                "  - {}: status={} target={} evidence_required={} evidence_present={} blocks_exploit_confirmation={} claim_ids={}",
                record.stage,
                record.status,
                record.target,
                record.evidence_required.join(","),
                record.evidence_present,
                record.blocks_exploit_confirmation,
                record.claim_ids.join(",")
            )
            .expect("write to string");
            writeln!(out, "    diagnostic: {}", record.diagnostic).expect("write to string");
        }
    }

    let claim_records = exploit_claim_capture_records(report.target, &report.binary_report);
    if !claim_records.is_empty() {
        writeln!(out, "claim capture records:").expect("write to string");
        for record in &claim_records {
            writeln!(
                out,
                "  - {}: status={} source={} function={} vc_kind={} location={} solver={} replay_required={} independent_refutation_required={}",
                record.claim_id,
                record.status,
                record.source,
                record.function,
                record.vc_kind,
                record.location.as_deref().unwrap_or("unknown"),
                record.solver,
                record.replay_required,
                record.independent_refutation_required
            )
            .expect("write to string");
            writeln!(out, "    diagnostic: {}", record.diagnostic).expect("write to string");
        }
    }

    let (phase_notes, non_phase_notes): (Vec<_>, Vec<_>) =
        report.notes.iter().partition(|note| note.starts_with("phase."));
    let (claim_record_notes, notes): (Vec<_>, Vec<_>) =
        non_phase_notes.into_iter().partition(|note| note.starts_with("claim_capture_record."));

    if !phase_notes.is_empty() {
        writeln!(out, "phase diagnostics:").expect("write to string");
        for note in phase_notes {
            writeln!(out, "  - {note}").expect("write to string");
        }
    }

    if !claim_record_notes.is_empty() {
        writeln!(out, "claim capture diagnostics:").expect("write to string");
        for note in claim_record_notes {
            writeln!(out, "  - {note}").expect("write to string");
        }
    }

    if !notes.is_empty() {
        writeln!(out, "notes:").expect("write to string");
        for note in notes {
            writeln!(out, "  - {note}").expect("write to string");
        }
    }

    out
}

fn hex_addr(address: u64) -> String {
    format!("0x{address:x}")
}

/// True when help was requested from this wrapper rather than forwarded to a
/// child command after `--`.
fn wrapper_help_requested(args: &[String]) -> bool {
    args.iter()
        .take_while(|argument| argument.as_str() != "--")
        .any(|argument| matches!(argument.as_str(), "--help" | "-h"))
}

fn focused_check_request_error(
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
) -> Option<&'static str> {
    sub_args.focused_function.as_ref()?;

    if subcommand != Subcommand::Check {
        return Some("--function is only supported by `targo trust check` and `report-query`");
    }
    if sub_args.rewrite {
        return Some("--function cannot be combined with --rewrite");
    }
    if sub_args.standalone {
        return Some(
            "--function requires canonical compiler-backed proof reports; remove --standalone",
        );
    }
    if matches!(sub_args.format, OutputFormat::Html) {
        return Some("--function supports terminal or json output, not html");
    }

    None
}

fn rewrite_request_error(
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
) -> Option<&'static str> {
    if sub_args.rewrite
        && !matches!(subcommand, Subcommand::Check | Subcommand::Build | Subcommand::Loop)
    {
        return Some("--rewrite is only supported by `targo trust check`, `build`, and `loop`");
    }
    None
}

fn is_exact_unsafe_memory_report_command(subcommand: Subcommand, args: &[String]) -> bool {
    subcommand == Subcommand::Report
        && args.len() == 1
        && args.first().is_some_and(|arg| arg == "--unsafe-memory")
}

fn default_unsafe_memory_report_dir(crate_root: &Path) -> String {
    crate_root.join("reports").join("proof").display().to_string()
}

/// A Cargo profile that disables a build-time safety check.
///
/// Strict/full verification overrides these settings with canonical `-C ...=yes`
/// flags before Cargo invokes trustc. Advisory and survey lanes deliberately
/// preserve the Cargo profile for artifact fidelity and therefore surface a
/// warning instead of claiming strict coverage.
#[derive(Debug, Clone, PartialEq, Eq)]
struct SafetyCheckBypass {
    /// Manifest the bypass was declared in.
    manifest: PathBuf,
    /// Profile label, e.g. `release` or `release.package.foo` / `dev.build-override`.
    profile: String,
    /// `"overflow-checks"` or `"debug-assertions"`.
    check: &'static str,
}

/// The two profile keys whose `false` value disables a soundness-relevant check.
const SAFETY_CHECK_KEYS: [&str; 2] = ["overflow-checks", "debug-assertions"];

/// Scan the crate manifest and every ANCESTOR manifest for `[profile.*]` tables
/// that request a disabled safety check. Cargo honors `[profile.*]` only at the
/// workspace root, but a crate may BE that root and the root may be any ancestor,
/// so the whole chain is scanned. Order is deterministic (crate → filesystem
/// root) for stable output. Every manifest is read as one bounded, stable
/// snapshot; an unreadable or malformed candidate is a setup error rather than
/// silently disappearing from this safety-policy audit.
fn detect_safety_check_bypasses(crate_root: &Path) -> Result<Vec<SafetyCheckBypass>, String> {
    let mut found = Vec::new();
    let mut seen: Vec<PathBuf> = Vec::new();
    let mut dir = Some(crate_root);
    while let Some(d) = dir {
        let manifest = d.join("Cargo.toml");
        if manifest.is_file() && !seen.contains(&manifest) {
            let text = input_limits::read_bounded_utf8_file(
                &manifest,
                input_limits::MAX_RELEASE_METADATA_BYTES,
            )
            .map_err(|error| {
                format!("could not inspect safety-check profile {}: {error}", manifest.display())
            })?;
            parse_safety_check_bypasses(&text, &manifest, &mut found)?;
            seen.push(manifest);
        }
        dir = d.parent();
    }
    Ok(found)
}

/// Pure manifest parse (kept separate from filesystem I/O so it is unit-testable
/// from a TOML string). Appends every safety-check bypass in `manifest_text` —
/// including nested `[profile.x.package.*]` and `[profile.x.build-override]`
/// sub-profiles, each of which can independently disable a check.
fn parse_safety_check_bypasses(
    manifest_text: &str,
    manifest: &Path,
    out: &mut Vec<SafetyCheckBypass>,
) -> Result<(), String> {
    let value = manifest_text.parse::<toml::Value>().map_err(|error| {
        format!("could not parse safety-check profile {}: {error}", manifest.display())
    })?;
    let Some(profiles) = value.get("profile").and_then(toml::Value::as_table) else {
        return Ok(());
    };
    for (profile_name, profile) in profiles {
        collect_profile_safety_bypasses(profile, profile_name, manifest, out);
    }
    Ok(())
}

fn collect_profile_safety_bypasses(
    profile: &toml::Value,
    label: &str,
    manifest: &Path,
    out: &mut Vec<SafetyCheckBypass>,
) {
    let Some(table) = profile.as_table() else {
        return;
    };
    for &check in &SAFETY_CHECK_KEYS {
        if table.get(check).and_then(toml::Value::as_bool) == Some(false) {
            out.push(SafetyCheckBypass {
                manifest: manifest.to_path_buf(),
                profile: label.to_string(),
                check,
            });
        }
    }
    // `[profile.<name>.package.<pkg>]` per-package overrides.
    if let Some(packages) = table.get("package").and_then(toml::Value::as_table) {
        for (pkg, sub) in packages {
            collect_profile_safety_bypasses(sub, &format!("{label}.package.{pkg}"), manifest, out);
        }
    }
    // `[profile.<name>.build-override]`.
    if let Some(build_override) = table.get("build-override") {
        collect_profile_safety_bypasses(
            build_override,
            &format!("{label}.build-override"),
            manifest,
            out,
        );
    }
}

fn safety_check_profile_diagnostic(bypass: &SafetyCheckBypass, strict: bool) -> String {
    if strict {
        format!(
            "\n\
targo trust: ============================================================\n\
targo trust:  NOTICE: PROFILE SAFETY-CHECK OPT-OUT in [profile.{profile}]\n\
targo trust:    {check} = false\n\
targo trust:    {manifest}\n\
targo trust: ------------------------------------------------------------\n\
targo trust:  Strict/full verification overrides this profile setting with\n\
targo trust:  `-C {check}=yes`; the proof covers the safety-checked artifact.\n\
targo trust:  That artifact may differ from an ordinary Cargo build using this\n\
targo trust:  profile. Remove the opt-out for build/proof parity, or choose an\n\
targo trust:  explicit advisory lane when profile fidelity is intentional.\n\
targo trust: ============================================================\n",
            profile = bypass.profile,
            check = bypass.check,
            manifest = bypass.manifest.display(),
        )
    } else {
        format!(
            "\n\
targo trust: ============================================================\n\
targo trust:  WARNING: SAFETY CHECK DISABLED in [profile.{profile}]\n\
targo trust:    {check} = false\n\
targo trust:    {manifest}\n\
targo trust: ------------------------------------------------------------\n\
targo trust:  This advisory/survey lane preserves the Cargo profile, so the\n\
targo trust:  generated artifact omits this safety check and strict proof is\n\
targo trust:  not claimed. Remove the opt-out or use strict/full verification\n\
targo trust:  to compile and prove with `-C {check}=yes`.\n\
targo trust: ============================================================\n",
            profile = bypass.profile,
            check = bypass.check,
            manifest = bypass.manifest.display(),
        )
    }
}

/// Print an actionable mode-specific diagnostic for each profile opt-out.
fn warn_safety_check_bypasses(bypasses: &[SafetyCheckBypass], strict: bool) {
    for b in bypasses {
        eprint!("{}", safety_check_profile_diagnostic(b, strict));
    }
}

fn source_subcommand_compiles_for_safety_diagnostics(subcommand: Subcommand) -> bool {
    matches!(
        subcommand,
        Subcommand::Check
            | Subcommand::Build
            | Subcommand::Test
            | Subcommand::Report
            | Subcommand::Loop
    )
}

fn run_subcommand(subcommand: Subcommand, args: &[String]) -> ExitCode {
    run_subcommand_with_live_report(subcommand, args, None, true)
}

pub(crate) fn run_subcommand_with_live_report(
    subcommand: Subcommand,
    args: &[String],
    mut live_report_consumer: Option<
        &mut dyn FnMut(&report::LiveCanonicalReport) -> Result<(), String>,
    >,
    render_output: bool,
) -> ExitCode {
    if wrapper_help_requested(args) {
        print_usage_stdout();
        return ExitCode::SUCCESS;
    }
    let exact_unsafe_memory_report_command =
        is_exact_unsafe_memory_report_command(subcommand, args);
    let mut sub_args = match parse_subcommand_args(args) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("targo trust: {e}");
            return ExitCode::from(2);
        }
    };
    restore_cargo_all_alias(subcommand, &mut sub_args);

    if subcommand == Subcommand::Test && sub_args.is_single_file {
        eprintln!(
            "targo trust: `test` requires a Cargo crate; single-file test execution is not supported"
        );
        return ExitCode::from(2);
    }

    if let Some(error) = focused_check_request_error(subcommand, &sub_args) {
        eprintln!("targo trust: {error}");
        return ExitCode::from(2);
    }
    if let Some(error) = rewrite_request_error(subcommand, &sub_args) {
        eprintln!("targo trust: {error}");
        return ExitCode::from(2);
    }

    // Handle `diff` subcommand separately -- it compares reports, not runs.
    if subcommand == Subcommand::Diff {
        return diff_report::run_diff(&sub_args, &resolve_project_root(&sub_args).root);
    }

    // Handle `solvers` subcommand -- detect and report solver status.
    if subcommand == Subcommand::Solvers {
        return run_solvers(&sub_args);
    }

    if let Some(diagnostic) =
        trust_verify_disable_diagnostic(&sub_args.passthrough, sub_args.is_single_file)
    {
        eprintln!("targo trust: error: verifier policy cannot be overridden through targo trust");
        eprintln!("  {diagnostic}");
        return ExitCode::from(2);
    }

    // Trust policy is anchored to the project root, not the launch directory.
    let resolved_project_root = resolve_project_root(&sub_args);
    let crate_root = resolved_project_root.root.clone();
    // Surface profile opt-outs before compilation. Strict/full runs override
    // them in canonical child flags; advisory/survey runs preserve them and
    // warn that strict coverage is not being claimed.
    if source_subcommand_compiles_for_safety_diagnostics(subcommand) {
        let bypasses = match detect_safety_check_bypasses(&crate_root) {
            Ok(bypasses) => bypasses,
            Err(error) => {
                eprintln!("targo trust: error: {error}");
                eprintln!(
                    "  safety-profile discovery requires bounded, readable regular Cargo manifests"
                );
                return ExitCode::from(2);
            }
        };
        warn_safety_check_bypasses(&bypasses, sub_args.strict_artifact_policy());
    }
    let unsafe_memory_report_request = if exact_unsafe_memory_report_command {
        if sub_args.report_dir.is_none() {
            sub_args.report_dir = Some(default_unsafe_memory_report_dir(&crate_root));
        }
        Some(UnsafeMemoryReportRequest::new(crate_root.clone()))
    } else {
        None
    };
    let config = match TrustConfig::load_for_verification(
        &crate_root,
        resolved_project_root.manifest_path.as_deref(),
    ) {
        Ok(config) => config,
        Err(error) => {
            eprintln!("targo trust: error: {error}");
            eprintln!(
                "  verifier entrypoints require a readable, valid `[{}]` table, or none at all",
                config::TRUST_TABLE
            );
            return ExitCode::from(2);
        }
    };
    apply_configured_trust_profile(&mut sub_args, &config);
    // Evidence-grade invocations always pin a backend. Leaving this unset lets
    // ambient rustflags or a project-controlled custom target select an
    // in-process backend that can forge compiler transport.
    let selected_codegen_backend = Some(
        sub_args
            .backend
            .as_deref()
            .or(config.codegen_backend.as_deref())
            .unwrap_or(DEFAULT_CODEGEN_BACKEND),
    );
    if sub_args.hardened {
        let profile = sub_args.trust_profile.as_deref().unwrap_or(DEFAULT_TRUST_PROFILE);
        eprintln!("targo trust: hardened profile `{profile}` enabled");
    }
    if !config.enabled {
        if sub_args.focused_function.is_some() {
            eprintln!(
                "targo trust: --function requires `enabled` to be unset or true in [{}]",
                config::TRUST_TABLE
            );
            return ExitCode::from(2);
        }
        eprintln!(
            "targo trust: error: verification disabled by `enabled = false` in the project configuration"
        );
        eprintln!(
            "  targo trust verifier entrypoints are fail-closed; remove `enabled = false` before requesting proof evidence"
        );
        return ExitCode::from(2);
    }

    // Only accept solver requests that are actually routed by
    // compiler-backed source verification. Detection can know about more tools,
    // but accepting them here would imply native routing that does not exist.
    let mut selected_ay_path = None;
    if let Some(ref solver_name) = sub_args.solver {
        if !is_source_solver_routed(solver_name) {
            eprintln!(
                "targo trust: solver `{solver_name}` is not wired for compiler-backed source verification"
            );
            eprintln!(
                "  Supported compiler-backed --solver values: {}",
                supported_source_solver_names()
            );
            eprintln!(
                "  Use `targo trust solvers --solver {solver_name}` to inspect detection only."
            );
            return ExitCode::from(2);
        }

        let info = solver_detect::detect_solver(solver_name);
        if !info.available {
            eprintln!("targo trust: requested solver `{solver_name}` is unavailable");
            if let Some(diagnostic) = &info.diagnostic {
                eprintln!("  {diagnostic}");
            }
            eprintln!("  Install it or set AY_PATH before using `--solver {solver_name}`.");
            return ExitCode::from(2);
        } else if let Some(ref path) = info.path {
            eprintln!("targo trust: requesting solver `{solver_name}` at {}", path.display());
            if solver_name == "ay" {
                selected_ay_path = Some(path.clone());
            }
        }
        if solver_name == "ay" && selected_ay_path.is_none() {
            eprintln!("targo trust: requested solver `ay` has no executable path");
            return ExitCode::from(2);
        }
    }

    if sub_args.standalone {
        // (The former `--full-verifier` + `--standalone` conflict is gone: there is
        // no `--full-verifier` flag under the batteries-on doctrine.)
        if matches!(subcommand, Subcommand::Check | Subcommand::Report) {
            return run_standalone_check(&sub_args, &crate_root);
        }
        eprintln!("targo trust: --standalone is only supported for check/report");
        return ExitCode::from(2);
    }

    // Standalone mode is explicit only. Defaults must use the Trust compiler.
    let native_rustc = discover_native_rustc_checked();
    let native_capabilities =
        native_rustc.as_ref().map(|discovery| detect_native_rustc_capabilities(&discovery.rustc));

    if let (Some(discovery), Some(capabilities)) = (native_rustc, native_capabilities) {
        let rustc = discovery.rustc;
        if !capabilities.trust_verify {
            eprintln!(
                "targo trust: error: discovered compiler does not support Trust verification: {}",
                rustc.display()
            );
            eprintln!(
                "Use canonical `trustc` from this checkout; --standalone is only a non-proof source audit."
            );
            return ExitCode::from(2);
        }

        if !capabilities.json_transport {
            eprintln!(
                "targo trust: error: native source verification requires structured Trust JSON transport (-Z trust-verify-output=json)"
            );
            eprintln!("  Discovered compiler: {} ({})", rustc.display(), discovery.source.label());
            eprintln!(
                "  Human-readable Trust diagnostics are not accepted for default native verification."
            );
            eprintln!(
                "  Use canonical `trustc` with JSON transport support; --standalone is only a non-proof source audit."
            );
            return ExitCode::from(2);
        }

        if sub_args.strict_artifact_policy() && !capabilities.authenticated_coverage {
            eprintln!(
                "targo trust: error: strict native verification requires authenticated, session-bound coverage transport"
            );
            eprintln!("  Discovered compiler: {} ({})", rustc.display(), discovery.source.label());
            eprintln!(
                "  This compiler supports generic Trust JSON, but did not prove the current coverage authentication protocol."
            );
            eprintln!(
                "  Use the canonical current trustc, or select an explicit advisory lane for legacy JSON compatibility without coverage credit."
            );
            return ExitCode::from(2);
        }

        eprintln!(
            "targo trust: using native compiler at {} ({})",
            rustc.display(),
            discovery.source.label()
        );
        if let Some(backend) = selected_codegen_backend {
            eprintln!("targo trust: using codegen backend `{backend}`");
        } else {
            eprintln!("targo trust: using default codegen backend `{DEFAULT_CODEGEN_BACKEND}`");
        }

        // `loop` subcommand always runs the rewrite loop.
        if subcommand == Subcommand::Loop || sub_args.rewrite {
            return run_rewrite_loop(
                &rustc,
                if subcommand == Subcommand::Loop { Subcommand::Check } else { subcommand },
                &sub_args,
                &config,
                selected_codegen_backend,
                capabilities.json_transport,
                selected_ay_path.as_deref(),
            );
        }

        // `report` runs check + renders in the requested format.
        let compile_cmd = match subcommand {
            Subcommand::Report => Subcommand::Check,
            other => other,
        };
        let focused_function = sub_args.focused_function.clone();
        let render_format =
            if focused_function.is_some() { OutputFormat::Terminal } else { sub_args.format };

        let compile_args = match build_native_command_with_json_transport(
            &rustc,
            compile_cmd,
            &sub_args,
            &config,
            selected_codegen_backend,
            capabilities.json_transport,
        ) {
            Ok(args) => args,
            Err(error) => {
                eprintln!("targo trust: error: {error}");
                return ExitCode::from(2);
            }
        };
        let mut focused_exit = None;
        let focused_format = sub_args.format;
        let has_live_consumer = focused_function.is_some() || live_report_consumer.is_some();
        let mut dispatch_live_report = |live: &report::LiveCanonicalReport| {
            if let Some(function) = focused_function.as_deref() {
                focused_exit = Some(report_query::run_live_focused_check_query(
                    live,
                    function,
                    focused_format,
                ));
            }
            if let Some(consumer) = live_report_consumer.as_mut() {
                consumer(live)?;
            }
            Ok(())
        };
        let live_report_consumer = has_live_consumer.then_some(
            &mut dispatch_live_report
                as &mut dyn FnMut(&report::LiveCanonicalReport) -> Result<(), String>,
        );
        let exit_code = run_compiler(CompilerRun {
            cmd_args: &compile_args,
            rustc_path: &rustc,
            config: &config,
            selected_codegen_backend,
            supports_json_transport: capabilities.json_transport,
            strict_artifact_policy: sub_args.strict_artifact_policy(),
            strict_result_gate: sub_args.strict_result_gate(),
            certify_gate: sub_args.certify_lane(),
            allow_l0_gaps: sub_args.allow_l0_gaps_lane(),
            memory_safe_policy: sub_args.memory_safe && !sub_args.survey,
            survey: sub_args.survey,
            hardened: sub_args.hardened,
            trust_profile: sub_args.trust_profile.as_deref(),
            ay_path: selected_ay_path.as_deref(),
            format: render_format,
            report_dir: sub_args.report_dir.as_deref(),
            unsafe_memory_report: unsafe_memory_report_request.as_ref(),
            live_report_consumer,
            render_output,
            ephemeral_single_file_output: sub_args.is_single_file
                && !matches!(compile_cmd, Subcommand::Build | Subcommand::Test)
                && !has_output_path_flag(&sub_args.passthrough),
        });
        drop(dispatch_live_report);
        if let Some(function) = focused_function.as_deref() {
            if exit_code != ExitCode::SUCCESS && exit_code != ExitCode::FAILURE {
                if exit_code == ExitCode::from(2) {
                    eprintln!(
                        "targo trust: focused function `{function}` skipped because compiler setup or report evidence failed"
                    );
                } else {
                    eprintln!(
                        "targo trust: focused function `{function}` cannot override an abnormal compiler termination"
                    );
                }
                return exit_code;
            }
            let Some(focused_exit) = focused_exit else {
                eprintln!(
                    "targo trust: focused function `{function}` had no live sealed compiler report"
                );
                return ExitCode::from(2);
            };
            if focused_exit == 0 {
                eprintln!(
                    "targo trust: focused function `{function}` satisfied --require proved; non-focused rows do not affect this focused exit code"
                );
            }
            return ExitCode::from(focused_exit);
        }
        return exit_code;
    }

    eprintln!("targo trust: error: Trust compiler not found");
    eprintln!();
    eprintln!("Discovery order:");
    eprintln!("  1. sibling trustc next to the running targo-trust");
    eprintln!("  2. repo-local build/host/stage2/bin/trustc");
    eprintln!(
        "  3. repo-local build/<host>/stage2/bin/trustc (scanned as build/*/stage2/bin/trustc)"
    );
    eprintln!("  4. repo-local build/host/stage3/bin/trustc or build/<host>/stage3/bin/trustc");
    eprintln!();
    eprintln!(
        "Install or build a Trust toolchain so targo trust can find canonical trustc automatically."
    );
    eprintln!(
        "For local stage2 gating, run `python3 scripts/recreate_bootstrap.py --stage 2` or `./x.py build --stage 2 compiler/rustc`, then verify build/<host>/stage2/bin/trustc exists."
    );
    eprintln!("Stage0 trustc is intentionally not accepted for release proof evidence.");
    eprintln!(
        "Use --standalone only for a non-proof source audit; it never performs compiler verification."
    );
    ExitCode::from(2)
}

/// The generic wrapper parser also uses `--all` for binary lifting. In a
/// crate-mode source command, however, it is Cargo's historical spelling of
/// `--workspace` and must reach the child frontend. Normalize it here, where
/// the subcommand context is known, rather than making binary commands inherit
/// a stray Cargo flag.
fn restore_cargo_all_alias(subcommand: Subcommand, sub_args: &mut SubcommandArgs) {
    if !sub_args.is_single_file
        && sub_args.all_functions
        && matches!(
            subcommand,
            Subcommand::Check
                | Subcommand::Build
                | Subcommand::Test
                | Subcommand::Report
                | Subcommand::Loop
        )
        && !sub_args.passthrough.iter().any(|arg| arg == "--workspace" || arg == "--all")
    {
        sub_args.passthrough.push("--workspace".to_string());
    }
}

fn run_doctor_subcommand(args: &[String]) -> ExitCode {
    if wrapper_help_requested(args) {
        print_usage_stdout();
        return ExitCode::SUCCESS;
    }
    let sub_args = match parse_subcommand_args(args) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("targo trust: {e}");
            return ExitCode::from(2);
        }
    };

    if matches!(sub_args.format, OutputFormat::Html) {
        eprintln!("targo trust doctor: HTML output is not implemented; use terminal or json");
        return ExitCode::from(2);
    }

    let report = build_doctor_report(&sub_args);

    match sub_args.format {
        OutputFormat::Json => match serde_json::to_string_pretty(&report) {
            Ok(json) => println!("{json}"),
            Err(error) => {
                eprintln!("targo trust: failed to serialize doctor report: {error}");
                return ExitCode::from(2);
            }
        },
        OutputFormat::Terminal => print_doctor_terminal(&report),
        OutputFormat::Html => unreachable!("HTML rejected before doctor rendering"),
    }

    if report.ready { ExitCode::SUCCESS } else { ExitCode::FAILURE }
}

// ---------------------------------------------------------------------------
// Solver detection subcommand
// ---------------------------------------------------------------------------

/// Run the `solvers` subcommand: detect all known solver binaries and
/// report their status.
fn run_solvers(sub_args: &SubcommandArgs) -> ExitCode {
    if matches!(sub_args.format, OutputFormat::Html) {
        eprintln!("targo trust solvers: HTML output is not implemented; use terminal or json");
        return ExitCode::from(2);
    }
    // Keep the legacy renderer referenced while terminal output is owned here
    // so routing/readiness wording can stay aligned with implemented behavior.
    let _legacy_renderer: fn(&[solver_detect::SolverInfo]) = solver_detect::render_solvers_terminal;
    let _legacy_json_renderer: fn(&[solver_detect::SolverInfo]) =
        solver_detect::render_solvers_json;
    let verifier_suites = verifier_suite_statuses();
    let mut solvers = if let Some(ref name) = sub_args.solver {
        vec![solver_detect::detect_solver(name)]
    } else {
        solver_detect::detect_all_solvers()
    };
    let external_available = solvers.iter().filter(|solver| solver.available).count();
    mark_doctor_in_process_solver_routes(&mut solvers, &verifier_suites);
    let native_suite_available =
        verifier_suites.iter().filter(|suite| doctor_suite_has_native_source_route(suite)).count();
    let available = solvers.iter().filter(|solver| solver.available).count();
    let routed_available = solvers
        .iter()
        .filter(|solver| {
            solver.available
                && (is_source_solver_routed(&solver.name)
                    || doctor_solver_has_native_source_route(&solver.name, &verifier_suites))
        })
        .count();

    match sub_args.format {
        OutputFormat::Json => {
            #[derive(Serialize)]
            struct SolverCommandReport {
                solvers: Vec<solver_detect::SolverInfo>,
                available: usize,
                total: usize,
                external_available: usize,
                native_suite_available: usize,
                routed_available: usize,
            }

            let report = SolverCommandReport {
                solvers: solvers.clone(),
                available,
                total: solvers.len(),
                external_available,
                native_suite_available,
                routed_available,
            };
            match serde_json::to_string_pretty(&report) {
                Ok(json) => println!("{json}"),
                Err(error) => {
                    eprintln!("targo trust: failed to serialize solver report: {error}");
                    return ExitCode::from(2);
                }
            }
        }
        OutputFormat::Terminal => {
            print_solvers_terminal(&solvers, &verifier_suites);
        }
        OutputFormat::Html => unreachable!("HTML rejected before solver rendering"),
    }

    if available > 0 { ExitCode::SUCCESS } else { ExitCode::FAILURE }
}

// ---------------------------------------------------------------------------
// Init subcommand
// ---------------------------------------------------------------------------

/// Run the `init` subcommand: scaffold verification annotations.
fn run_init_subcommand(args: &[String]) -> ExitCode {
    if wrapper_help_requested(args) {
        print_usage_stdout();
        return ExitCode::SUCCESS;
    }
    let sub_args = match parse_subcommand_args(args) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("targo trust: {e}");
            return ExitCode::from(2);
        }
    };

    if !matches!(sub_args.format, OutputFormat::Terminal) {
        eprintln!("targo trust init: structured output is not implemented; use terminal format");
        return ExitCode::from(2);
    }

    let resolved_root = resolve_project_root(&sub_args);
    let crate_root = resolved_root.root;

    let summary = if sub_args.is_single_file {
        let file = resolved_root.single_file_path.unwrap_or_else(|| {
            PathBuf::from(
                sub_args.single_file_path().expect("single-file mode should have a file path"),
            )
        });
        if !file.exists() {
            eprintln!("targo trust: error: file not found: {}", file.display());
            return ExitCode::from(2);
        }
        eprintln!("targo trust: scanning {} for annotation scaffolding", file.display());
        init::scaffold_file(&file)
    } else {
        eprintln!(
            "targo trust: scanning crate at {} for annotation scaffolding",
            crate_root.display()
        );
        init::scaffold_crate(&crate_root)
    };

    // Scaffold the policy table into the manifest the project already has.
    match config::discover_manifest(&crate_root) {
        Some(manifest_path) => match config::read_trust_table(&manifest_path) {
            Ok(Some(_)) => {
                eprintln!(
                    "targo trust: {} already declares [{}], skipping",
                    manifest_path.display(),
                    config::TRUST_TABLE
                );
            }
            Ok(None) => match init::append_trust_table(&manifest_path) {
                Ok(()) => {
                    eprintln!(
                        "targo trust: added [{}] to {}",
                        config::TRUST_TABLE,
                        manifest_path.display()
                    );
                }
                Err(e) => {
                    eprintln!(
                        "targo trust: warning: failed to write {}: {e}",
                        manifest_path.display()
                    );
                }
            },
            Err(error) => {
                eprintln!("targo trust: warning: {error}");
            }
        },
        None => {
            eprintln!(
                "targo trust: warning: no manifest at {}; nowhere to declare [{}]",
                crate_root.display(),
                config::TRUST_TABLE
            );
        }
    }

    // Output annotations
    if sub_args.inline {
        if summary.annotations.is_empty() {
            eprintln!("targo trust: no annotations to write");
        } else {
            match init::write_inline_annotations(&summary.annotations) {
                Ok(count) => {
                    eprintln!("targo trust: wrote annotations for {count} functions inline");
                }
                Err(e) => {
                    eprintln!("targo trust: error writing inline annotations: {e}");
                    return ExitCode::FAILURE;
                }
            }
        }
    } else {
        init::render_annotations_stdout(&summary.annotations);
    }

    init::render_summary(&summary);

    ExitCode::SUCCESS
}

#[cfg(test)]
mod main_tests {
    use super::*;

    #[test]
    fn terminal_and_git_identity_transports_reject_ambiguous_bytes() {
        assert_eq!(escape_terminal_controls("ok\u{1b}[31m\u{7}"), "ok\\u{1b}[31m\\u{7}");

        let commit = "a".repeat(40);
        assert_eq!(
            parse_canonical_git_commit_output(format!("{commit}\n").into_bytes()),
            Some(commit.clone())
        );
        assert_eq!(
            parse_canonical_git_commit_output(format!("{commit}\r\n").into_bytes()),
            Some(commit.clone())
        );
        assert!(
            parse_canonical_git_commit_output(format!("{commit}\n{commit}\n").into_bytes())
                .is_none()
        );
        assert!(parse_canonical_git_commit_output(vec![0xff]).is_none());
    }

    #[test]
    fn test_main_help_strings_use_targo_trust() {
        for usage in [
            lift_usage_text(),
            verify_binary_usage_text(),
            decompile_usage_text(),
            convert_usage_text(),
            exploit_find_usage_text(),
        ] {
            assert!(usage.contains("targo trust"));
            assert!(!usage.lines().any(|line| line.trim_start().starts_with("cargo trust ")));
        }
    }

    #[test]
    fn test_version_text_reports_stable_trust_identity() {
        let text = version_text();

        assert!(text.starts_with("targo-trust "));
        assert!(text.contains("trust.identity=targo trust"));
        assert!(text.contains("trust.command=targo trust"));
        assert!(text.contains("trust.package=targo-trust"));
        assert!(text.contains("trust.source_package=targo-trust"));
        assert!(text.contains("trust.version="));
        assert_eq!(
            text.lines()
                .filter_map(|line| line.strip_prefix("trust-repo-commit-hash: "))
                .collect::<Vec<_>>(),
            [embedded_trust_repo_commit_hash(option_env!("CFG_VER_HASH"))]
        );
    }

    #[test]
    fn embedded_trust_repo_commit_is_exact_or_explicitly_unbound() {
        let commit = "0123456789abcdef0123456789abcdef01234567";
        assert_eq!(embedded_trust_repo_commit_hash(Some(commit)), commit);
        for invalid in [
            None,
            Some(""),
            Some("0123456789abcdef0123456789abcdef0123456"),
            Some("0123456789ABCDEF0123456789ABCDEF01234567"),
            Some("g123456789abcdef0123456789abcdef01234567"),
        ] {
            assert_eq!(embedded_trust_repo_commit_hash(invalid), UNBOUND_TRUST_REPO_COMMIT);
        }
    }

    #[test]
    fn crate_mode_all_alias_reaches_cargo_as_workspace_selection() {
        let mut parsed = parse_subcommand_args(&["--all".to_string()]).expect("parse --all");
        assert!(parsed.passthrough.is_empty(), "generic parser owns binary --all");
        restore_cargo_all_alias(Subcommand::Build, &mut parsed);
        assert_eq!(parsed.passthrough, ["--workspace"]);

        let mut binary = parse_subcommand_args(&["--all".to_string()]).expect("parse --all");
        restore_cargo_all_alias(Subcommand::Diff, &mut binary);
        assert!(binary.passthrough.is_empty(), "non-compile command must not inherit Cargo flags");
    }

    #[test]
    fn prove_args_reject_missing_values_and_unknown_options() {
        for args in [
            vec!["--dump-dir".to_string()],
            vec!["--source".to_string()],
            vec!["--require-axioms".to_string()],
            vec!["--require-axioms=three".to_string()],
            vec!["--budget-secs".to_string()],
            vec!["--budget-secs=0".to_string()],
            vec!["--budget-secs=forever".to_string()],
            vec!["--format".to_string()],
            vec!["--format=xml".to_string()],
            vec!["--unknown".to_string()],
        ] {
            assert!(parse_prove_args(&args).is_err(), "must reject {args:?}");
        }
    }

    #[test]
    fn prove_args_parse_owned_input_and_axiom_limit() {
        let args = [
            "--self".to_string(),
            "--kernel".to_string(),
            "--require-axioms=3".to_string(),
            "--budget-secs=45".to_string(),
            "--format=json".to_string(),
            "--source".to_string(),
            "example.rs".to_string(),
        ];
        let parsed = parse_prove_args(&args).expect("valid prove arguments");

        assert!(parsed.self_mode);
        assert_eq!(parsed.require_axioms, Some(3));
        assert_eq!(parsed.budget_secs, Some(45));
        assert!(parsed.json);
        assert_eq!(parsed.source.as_deref(), Some(Path::new("example.rs")));
        assert_eq!(parsed.dump_dir, None);
    }

    #[test]
    fn prove_args_separator_preserves_a_dash_prefixed_source() {
        let parsed = parse_prove_args(&["--".to_string(), "-generated.rs".to_string()])
            .expect("separator should make the remaining argument positional");
        assert_eq!(parsed.source, Some(PathBuf::from("-generated.rs")));
    }

    #[test]
    fn prove_args_reject_ambiguous_or_duplicate_inputs() {
        let source_and_dump = ["--source=a.rs".to_string(), "--dump-dir=dumps".to_string()];
        assert!(parse_prove_args(&source_and_dump).is_err());

        let duplicate_source = ["a.rs".to_string(), "b.rs".to_string()];
        assert!(parse_prove_args(&duplicate_source).is_err());

        let duplicate_budget = ["--budget-secs=1".to_string(), "--budget-secs=2".to_string()];
        assert!(parse_prove_args(&duplicate_budget).is_err());
    }

    #[test]
    fn prove_dump_resolution_never_falls_back_to_unrelated_fixtures() {
        let nonexistent_self_dump = Path::new("target/definitely-absent-trust-proof-dump");
        assert_eq!(resolve_prove_dump_dir(None, false, nonexistent_self_dump), None);
        assert_eq!(
            resolve_prove_dump_dir(Some(PathBuf::from("explicit")), false, nonexistent_self_dump,),
            Some(PathBuf::from("explicit"))
        );
    }

    #[test]
    fn prove_rejects_an_empty_dump_instead_of_succeeding_vacuously() {
        let dump = tempfile::Builder::new()
            .prefix("targo-trust-empty-proof-")
            .tempdir()
            .expect("create empty proof directory");
        let args = ["--dump-dir".to_string(), dump.path().to_string_lossy().into_owned()];

        assert_ne!(run_prove_subcommand(&args), ExitCode::SUCCESS);
    }

    #[test]
    fn proof_dump_coverage_preserves_body_counts_and_skips() {
        let coverage = parse_proof_dump_coverage(
            "noise\n\
             TRUST_COVERAGE: demo::f => analyzed:2\n\
             TRUST_COVERAGE: demo::f => zero-obligation\n\
             TRUST_COVERAGE: demo::g => skipped:UserOptOut\n",
        );

        assert_eq!(coverage.analyzed.get("demo::f"), Some(&2));
        assert_eq!(coverage.skipped, ["demo::g (skipped:UserOptOut)"]);
    }

    #[test]
    fn reflect_clean_args_reject_missing_invalid_duplicate_and_unknown_options() {
        for args in [
            vec!["--require-axioms".to_string()],
            vec!["--require-axioms=three".to_string()],
            vec!["--require-axioms=3".to_string(), "--require-axioms=4".to_string()],
            vec!["--unknown".to_string()],
        ] {
            assert!(parse_reflect_clean_args(&args).is_err(), "must reject {args:?}");
        }
    }

    #[test]
    fn reflect_clean_args_support_separator_and_axiom_upper_bounds() {
        let parsed = parse_reflect_clean_args(&[
            "--kernel".to_string(),
            "--require-axioms=4".to_string(),
            "--".to_string(),
            "-generated.rs".to_string(),
        ])
        .expect("valid reflect arguments");

        assert!(parsed.kernel);
        assert_eq!(parsed.require_axioms, Some(4));
        assert_eq!(parsed.paths, [PathBuf::from("-generated.rs")]);
    }

    #[test]
    fn reflect_clean_contract_scan_distinguishes_duplicate_function_names() {
        let source = "\
#[cfg(feature = \"requires\")]\n\
#[core::contracts::requires(\n\
    x > 0\n\
)]\n\
fn same(x: i32) -> i32 { x }\n\
mod nested {\n\
    fn same(x: i32) -> i32\n\
        ensures result >= 0\n\
    { x }\n\
}\n";
        let functions = crate::source_analysis::extract_functions_from_source(
            source,
            Path::new("duplicate.rs"),
        );
        assert_eq!(functions.len(), 2);

        let first =
            scan_contract_exprs(source, functions[0].line.saturating_sub(1), &functions[0].name)
                .unwrap();
        let second =
            scan_contract_exprs(source, functions[1].line.saturating_sub(1), &functions[1].name)
                .unwrap();
        assert_eq!(first, (vec!["x > 0".to_string()], Vec::new()));
        assert_eq!(second, (Vec::new(), vec!["result >= 0".to_string()]));
    }

    #[test]
    fn reflect_clean_ingests_only_explicit_upstream_compatibility_attributes() {
        let source = "\
#[requires(x > 0)]\n\
#[core::contracts::requires(x < 100)]\n\
#[core::contracts::ensures(|ret| ret > x)]\n\
fn bounded(x: i32) -> i32 { x + 1 }\n";
        let contracts = scan_contract_exprs(source, 3, "bounded").unwrap();
        assert_eq!(contracts.0, ["x < 100"]);
        assert_eq!(contracts.1, ["result > x"]);
    }

    #[test]
    fn reflect_clean_scans_multiline_native_clauses_at_signature_position() {
        let source = "fn choose(\n    x: i32,\n    y: i32,\n) -> i32\n    requires x >= 0 &&\n        y >= 0\n    ensures match result {\n        value => value >= x,\n    }\n{ x.max(y) }\n";
        let contracts = scan_contract_exprs(source, 0, "choose").unwrap();
        assert_eq!(contracts.0, ["x >= 0 &&\n        y >= 0"]);
        assert_eq!(contracts.1, ["match result {\n        value => value >= x,\n    }"]);
    }

    #[test]
    fn reflect_clean_rejects_a_function_free_input_vacuously() {
        let dir = tempfile::Builder::new()
            .prefix("targo-trust-empty-reflect-")
            .tempdir()
            .expect("create reflect directory");
        let source = dir.path().join("empty.rs");
        std::fs::write(&source, "// deliberately contains no function\n")
            .expect("write empty source");

        assert_ne!(
            run_reflect_clean_subcommand(&[source.to_string_lossy().into_owned()]),
            ExitCode::SUCCESS
        );
    }

    #[test]
    fn unsupported_output_formats_fail_instead_of_falling_back_to_terminal() {
        let html_args = ["--format=html".to_string()];
        assert_eq!(run_doctor_subcommand(&html_args), ExitCode::from(2));

        let parsed_html = parse_subcommand_args(&html_args).expect("parse HTML format");
        assert_eq!(run_solvers(&parsed_html), ExitCode::from(2));
        assert_eq!(diff_report::run_diff(&parsed_html, Path::new(".")), ExitCode::from(2));
        assert_eq!(run_standalone_check(&parsed_html, Path::new(".")), ExitCode::from(2));

        let json_args = ["--format=json".to_string()];
        assert_eq!(run_init_subcommand(&json_args), ExitCode::from(2));
    }

    #[test]
    fn wrapper_help_only_matches_before_child_separator() {
        assert!(wrapper_help_requested(&["--help".to_string()]));
        // Top-level `targo trust help` is dispatched before this helper. A bare
        // child argument named `help` must remain available to Cargo/rustc.
        assert!(!wrapper_help_requested(&["help".to_string()]));
        assert!(!wrapper_help_requested(&[
            "source.rs".to_string(),
            "--".to_string(),
            "--help".to_string(),
        ]));
    }

    #[test]
    fn safety_bypass_detects_overflow_checks_and_debug_assertions() {
        let manifest = r#"
[profile.release]
overflow-checks = false

[profile.dev]
debug-assertions = false
"#;
        let mut out = Vec::new();
        parse_safety_check_bypasses(manifest, Path::new("/x/Cargo.toml"), &mut out)
            .expect("valid manifest");
        assert_eq!(out.len(), 2, "{out:?}");
        assert!(out.iter().any(|b| b.profile == "release" && b.check == "overflow-checks"));
        assert!(out.iter().any(|b| b.profile == "dev" && b.check == "debug-assertions"));
    }

    #[test]
    fn safety_profile_diagnostic_describes_the_effective_lane() {
        let bypass = SafetyCheckBypass {
            manifest: PathBuf::from("/workspace/Cargo.toml"),
            profile: "release".to_string(),
            check: "overflow-checks",
        };

        let strict = safety_check_profile_diagnostic(&bypass, true);
        assert!(strict.contains("Strict/full verification overrides"), "{strict}");
        assert!(strict.contains("-C overflow-checks=yes"), "{strict}");
        assert!(strict.contains("proof covers the safety-checked artifact"), "{strict}");
        assert!(!strict.contains("pass SILENTLY"), "{strict}");

        let advisory = safety_check_profile_diagnostic(&bypass, false);
        assert!(advisory.contains("advisory/survey lane preserves"), "{advisory}");
        assert!(advisory.contains("strict proof is"), "{advisory}");
        assert!(advisory.contains("not claimed"), "{advisory}");
    }

    #[test]
    fn safety_profile_diagnostics_cover_every_source_compilation_front_door() {
        for subcommand in
            [Subcommand::Check, Subcommand::Build, Subcommand::Report, Subcommand::Loop]
        {
            assert!(source_subcommand_compiles_for_safety_diagnostics(subcommand));
        }
        for subcommand in [Subcommand::Diff, Subcommand::Solvers, Subcommand::Init] {
            assert!(!source_subcommand_compiles_for_safety_diagnostics(subcommand));
        }
    }

    #[test]
    fn safety_bypass_detects_nested_package_and_build_override() {
        let manifest = r#"
[profile.release.package.foo]
overflow-checks = false

[profile.release.build-override]
debug-assertions = false
"#;
        let mut out = Vec::new();
        parse_safety_check_bypasses(manifest, Path::new("/x/Cargo.toml"), &mut out)
            .expect("valid manifest");
        assert!(
            out.iter().any(|b| b.profile == "release.package.foo" && b.check == "overflow-checks"),
            "{out:?}"
        );
        assert!(
            out.iter()
                .any(|b| b.profile == "release.build-override" && b.check == "debug-assertions"),
            "{out:?}"
        );
    }

    #[test]
    fn safety_bypass_ignores_enabled_checks_and_unrelated_keys() {
        let manifest = r#"
[package]
name = "demo"

[profile.release]
overflow-checks = true
debug-assertions = true
opt-level = 3
lto = true
"#;
        let mut out = Vec::new();
        parse_safety_check_bypasses(manifest, Path::new("/x/Cargo.toml"), &mut out)
            .expect("valid manifest");
        assert!(out.is_empty(), "no bypass expected, got {out:?}");
    }

    #[test]
    fn safety_bypass_rejects_malformed_manifest() {
        let mut out = Vec::new();
        let error = parse_safety_check_bypasses(
            "not = valid = toml [[[",
            Path::new("/x/Cargo.toml"),
            &mut out,
        )
        .expect_err("malformed safety policy must fail closed");
        assert!(out.is_empty());
        assert!(error.contains("could not parse safety-check profile"), "{error}");
    }
}
