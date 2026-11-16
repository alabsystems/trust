// targo trust self-improve — the Trust-on-Trust improvement loop (Slice 1).
//
// Closes the self-hosting loop described in docs/trust-refinement-compiler.tex:
// verify Trust's own crates to capture the proof frontier, surface repair
// targets as proposals (nothing is applied), and — when a prior frontier is
// supplied as a baseline — measure the frontier delta across runs. The
// north-star metric is the Trust-on-Trust convergence score (proved /
// obligations), which should improve monotonically across releases.
//
// The frontier route remains read-only. Native execution refuses before any
// project work until the original graph, agent and publication owners exist.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use trust_backprop::{RepairPromptContext, build_ai_repair_command, build_ai_repair_prompt};
use trust_types::{CrateSummary, FunctionVerdict, JsonProofReport, ObligationOutcome};

use crate::intent::{ResolvedIntent, resolve_intent};
use crate::script_cli::resolve_repo_file;

mod native;

const USAGE: &str = "\
Usage: targo trust self-improve [options]

Run the Trust-on-Trust improvement loop over Trust's own crates: verify each
crate, aggregate the proof frontier, and surface repair targets as proposals.
Nothing is applied — this slice is read-only and proposal-only.

Options:
  --crate NAME         Restrict to the named crate (repeatable). Default: all
                       crates under `crates/`.
  --baseline PATH      Compare against a complete v2 frontier with at least one
                       obligation, written by a prior run (--out) for the same
                       selected crates.
  --require-no-regression
                       Require --baseline and fail if total proved obligations
                       decrease. Additional obligations alone do not fail.
  --out NEW_PATH       Write a new frontier JSON; existing files refuse. Use a
                       complete run with obligations as the next --baseline
                       without replacing it.
  --capture-dir NEW_DIR Retain each crate's full report and typed verifier
                        inputs from the same live run in a fresh directory.
                        Captures are audit data, never proof authority.
  --intent PATH        Design doc / chat that guides repair (authority: below a
                       formal contract, above code-abduced guesses). When set,
                       each repair target gets an intent-guided AI repair prompt.
  --json               Emit the consolidated frontier report as JSON.
  --native             Request the native measured repair loop. Currently exits
                       3 before project work: original graph/SDK, authenticated
                       agent and development publication owners are unavailable.
  -h, --help           Show this help.

Every selected crate remains in JSON and --out, including failed measurements.
Incomplete measurement exits 3 (COULD NOT RUN); convergence is unavailable for
incomplete coverage or zero obligations. Baselines require obligations and
consistent inventories and totals; legacy or partial baselines refuse.
With --require-no-regression, a proved-count decrease exits 1, and incomplete
or empty current measurements exit 3. A saved baseline grants no proof authority.

Examples:
  targo trust self-improve --crate trust-vcgen --crate trust-router
  targo trust self-improve --out target/trust-frontier.json
  targo trust self-improve --baseline target/trust-frontier.json
  targo trust self-improve --baseline reports/trust-frontier-baseline.json --require-no-regression
  targo trust self-improve --intent docs/trust-intent.md --crate trust-vcgen
";

/// One crate's contribution to the proof frontier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CrateFrontier {
    pub(crate) crate_name: String,
    pub(crate) obligations: usize,
    pub(crate) proved: usize,
    pub(crate) runtime_checked: usize,
    pub(crate) failed: usize,
    pub(crate) unknown: usize,
}

impl CrateFrontier {
    fn from_summary(crate_name: &str, summary: &CrateSummary) -> Self {
        Self {
            crate_name: crate_name.to_string(),
            obligations: summary.total_obligations,
            proved: summary.total_proved,
            runtime_checked: summary.total_runtime_checked,
            failed: summary.total_failed + summary.total_unattributed_failed,
            unknown: summary.total_unknown + summary.total_unattributed_unknown,
        }
    }

    /// Obligations that are neither proved nor discharged at runtime — the
    /// candidates for spec inference and repair in later slices.
    fn unproved(&self) -> usize {
        self.failed + self.unknown
    }
}

/// A function needing static proofs, including runtime checks — a proposal target.
/// We do not generate or apply rewrites here; we only name where repair would aim and
/// (when an intent document is supplied) render the intent-guided repair prompt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RepairTarget {
    pub(crate) crate_name: String,
    pub(crate) function: String,
    pub(crate) failed: usize,
    pub(crate) unknown: usize,
    pub(crate) runtime_checked: usize,
    /// VC kind of the lead unproved obligation (e.g. `arithmetic_overflow`).
    pub(crate) vc_kind: String,
    /// Solver that produced the lead unproved result.
    pub(crate) solver: String,
    /// Outcome label of the lead unproved obligation (`FAILED` / `UNKNOWN`; a
    /// failed row nothing refuted reads `FAILED (unproved, no counterexample;
    /// failed closed)`).
    pub(crate) outcome: String,
    /// Source file of the lead unproved obligation, when known.
    pub(crate) source_file: Option<String>,
}

impl RepairTarget {
    /// Render the intent-guided AI repair prompt for this target.
    fn repair_prompt(&self, intent: Option<&str>) -> String {
        let ctx = RepairPromptContext {
            function: &self.function,
            source_file: self.source_file.as_deref(),
            signature: None,
            params: &[],
            return_type: None,
            vc_kind: &self.vc_kind,
            pattern: "unproved_obligation",
            solver: &self.solver,
            outcome: &self.outcome,
            solver_reason: None,
            counterexample: None,
            location: None,
            intent,
        };
        build_ai_repair_prompt(&ctx)
    }
}

/// The aggregated Trust-on-Trust proof frontier.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct TrustOnTrustFrontier {
    pub(crate) crates: Vec<CrateFrontier>,
}

impl TrustOnTrustFrontier {
    fn push(&mut self, frontier: CrateFrontier) {
        self.crates.push(frontier);
    }

    fn total_obligations(&self) -> usize {
        self.crates.iter().map(|c| c.obligations).sum()
    }

    fn total_proved(&self) -> usize {
        self.crates.iter().map(|c| c.proved).sum()
    }

    fn total_runtime_checked(&self) -> usize {
        self.crates.iter().map(|c| c.runtime_checked).sum()
    }

    fn total_unproved(&self) -> usize {
        self.crates.iter().map(CrateFrontier::unproved).sum()
    }

    /// Internal proved/obligations ratio. The empty-set fixed-point convention
    /// is not measurement evidence: renderers expose no convergence score for
    /// zero obligations or incomplete selected-crate coverage.
    fn convergence_score(&self) -> f64 {
        let obligations = self.total_obligations();
        if obligations == 0 {
            return 1.0;
        }
        self.total_proved() as f64 / obligations as f64
    }
}

/// Selection and failed measurements stay beside the measured frontier. A
/// missing compiler report contributes no proof and cannot shrink the selected
/// population or become a convergence baseline.
#[derive(Debug, Clone, PartialEq, Eq)]
struct MeasurementCoverage {
    selected_crates: Vec<String>,
    failures: Vec<(String, String)>,
}

impl MeasurementCoverage {
    fn complete(&self, frontier: &TrustOnTrustFrontier) -> bool {
        !self.selected_crates.is_empty()
            && self.failures.is_empty()
            && self.selected_crates.len() == frontier.crates.len()
            && self.selected_crates.iter().collect::<BTreeSet<_>>().len()
                == self.selected_crates.len()
            && frontier.crates.iter().map(|row| &row.crate_name).collect::<BTreeSet<_>>().len()
                == frontier.crates.len()
            && self.selected_crates.iter().collect::<BTreeSet<_>>()
                == frontier.crates.iter().map(|row| &row.crate_name).collect::<BTreeSet<_>>()
    }

    fn exit_code(&self, frontier: &TrustOnTrustFrontier) -> u8 {
        if self.complete(frontier) { 0 } else { 3 }
    }
}

/// The change in convergence between a baseline frontier and the current one.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct FrontierDelta {
    pub(crate) baseline_score: f64,
    pub(crate) current_score: f64,
    pub(crate) proved_delta: i64,
    pub(crate) unproved_delta: i64,
}

impl FrontierDelta {
    fn between(baseline: &TrustOnTrustFrontier, current: &TrustOnTrustFrontier) -> Self {
        Self {
            baseline_score: baseline.convergence_score(),
            current_score: current.convergence_score(),
            proved_delta: current.total_proved() as i64 - baseline.total_proved() as i64,
            unproved_delta: current.total_unproved() as i64 - baseline.total_unproved() as i64,
        }
    }
}

/// Collect functions that still need static proofs, including runtime checks.
fn repair_targets(report: &JsonProofReport) -> Vec<RepairTarget> {
    report
        .functions
        .iter()
        .filter(|function| {
            matches!(
                function.summary.verdict,
                FunctionVerdict::HasViolations
                    | FunctionVerdict::Inconclusive
                    | FunctionVerdict::RuntimeChecked
            ) || function.summary.failed > 0
                || function.summary.unknown > 0
                || function.summary.runtime_checked > 0
                || function.summary.unattributed_failed > 0
                || function.summary.unattributed_unknown > 0
        })
        .map(|function| {
            let summary = &function.summary;
            let has_unresolved = summary.failed > 0
                || summary.unknown > 0
                || summary.unattributed_failed > 0
                || summary.unattributed_unknown > 0;
            // Keep failed and unresolved rows ahead of runtime checks, even
            // when the runtime-checked row occurs first in source order.
            let lead = function
                .obligations
                .iter()
                .find(|obligation| {
                    matches!(
                        obligation.outcome,
                        ObligationOutcome::Failed { .. }
                            | ObligationOutcome::Unknown { .. }
                            | ObligationOutcome::Timeout { .. }
                    )
                })
                .or_else(|| {
                    if has_unresolved {
                        // A missing atomic row must not hide unresolved
                        // summary results behind a runtime-check prompt.
                        return None;
                    }
                    function.obligations.iter().find(|obligation| {
                        matches!(obligation.outcome, ObligationOutcome::RuntimeChecked { .. })
                    })
                });
            let (vc_kind, solver, outcome, source_file) = match lead {
                Some(obligation) => (
                    obligation.kind.clone(),
                    obligation.solver.clone(),
                    outcome_label(&obligation.outcome),
                    obligation.location.as_ref().map(|span| span.file.clone()),
                ),
                None => (
                    "unproved_obligation".to_string(),
                    "verifier".to_string(),
                    "UNKNOWN".to_string(),
                    None,
                ),
            };
            RepairTarget {
                crate_name: report.crate_name.clone(),
                function: function.function.clone(),
                failed: function.summary.failed + function.summary.unattributed_failed,
                unknown: function.summary.unknown + function.summary.unattributed_unknown,
                runtime_checked: function.summary.runtime_checked,
                vc_kind,
                solver,
                outcome,
                source_file,
            }
        })
        .collect()
}

fn outcome_label(outcome: &ObligationOutcome) -> String {
    match outcome {
        // Nothing refuted a fail-closed row; a repair target must not present
        // it as a found violation.
        ObligationOutcome::Failed { basis, .. } if !basis.is_refuted() => {
            return format!("FAILED ({})", basis.human_label());
        }
        ObligationOutcome::Failed { .. } => "FAILED",
        ObligationOutcome::Unknown { .. } => "UNKNOWN",
        ObligationOutcome::Timeout { .. } => "TIMEOUT",
        ObligationOutcome::Proved { .. } => "PROVED",
        ObligationOutcome::RuntimeChecked { .. } => "RUNTIME_CHECKED",
        _ => "UNKNOWN",
    }
    .to_string()
}

#[derive(Debug, Clone)]
struct Options {
    crates: Vec<String>,
    baseline: Option<PathBuf>,
    require_no_regression: bool,
    out: Option<PathBuf>,
    capture_dir: Option<PathBuf>,
    intent: Option<String>,
    json: bool,
    native: bool,
}

fn parse_options(args: &[String]) -> Result<Option<Options>, String> {
    let mut options = Options {
        crates: Vec::new(),
        baseline: None,
        require_no_regression: false,
        out: None,
        capture_dir: None,
        intent: None,
        json: false,
        native: false,
    };
    let mut index = 0;
    while index < args.len() {
        match args[index].as_str() {
            "-h" | "--help" => return Ok(None),
            "--json" => {
                options.json = true;
                index += 1;
            }
            "--native" => {
                if options.native {
                    return Err("--native may be supplied only once".into());
                }
                options.native = true;
                index += 1;
            }
            "--require-no-regression" => {
                if options.require_no_regression {
                    return Err("--require-no-regression may be supplied only once".into());
                }
                options.require_no_regression = true;
                index += 1;
            }
            "--intent" => {
                let value = args.get(index + 1).ok_or("--intent requires a path")?;
                options.intent = Some(value.clone());
                index += 2;
            }
            "--crate" => {
                let value = args.get(index + 1).ok_or("--crate requires a crate name")?;
                options.crates.push(value.clone());
                index += 2;
            }
            "--baseline" => {
                let value = args.get(index + 1).ok_or("--baseline requires a path")?;
                options.baseline = Some(PathBuf::from(value));
                index += 2;
            }
            "--out" => {
                let value = args.get(index + 1).ok_or("--out requires a path")?;
                options.out = Some(PathBuf::from(value));
                index += 2;
            }
            "--capture-dir" => {
                if options.capture_dir.is_some() {
                    return Err("--capture-dir may be supplied only once".to_string());
                }
                let value = args
                    .get(index + 1)
                    .filter(|value| !value.is_empty() && !value.starts_with('-'))
                    .ok_or("--capture-dir requires a new directory path")?;
                options.capture_dir = Some(PathBuf::from(value));
                index += 2;
            }
            other => return Err(format!("unknown option `{other}`")),
        }
    }
    if options.require_no_regression && options.baseline.is_none() {
        return Err("--require-no-regression requires --baseline".into());
    }
    Ok(Some(options))
}

pub(crate) fn run_self_improve_subcommand(args: &[String]) -> ExitCode {
    let options = match parse_options(args) {
        Ok(Some(options)) => options,
        Ok(None) => {
            print!("{USAGE}");
            return ExitCode::SUCCESS;
        }
        Err(message) => {
            eprintln!("targo trust self-improve: {message}");
            eprint!("{USAGE}");
            return ExitCode::from(2);
        }
    };

    if options.native {
        return native::run(options.json);
    }

    let intent = match resolve_intent(options.intent.as_deref(), None, None) {
        Ok(intent) => intent,
        Err(message) => {
            eprintln!("targo trust self-improve: {message}");
            return ExitCode::from(2);
        }
    };

    let Some((repo_root, _)) = resolve_repo_file("crates/trust-types/Cargo.toml") else {
        eprintln!(
            "targo trust self-improve: could not locate the Trust product sources (crates/trust-types/Cargo.toml)"
        );
        eprintln!("  Run from a Trust checkout or set TRUST_REPO_ROOT=/path/to/trust.");
        return ExitCode::from(2);
    };
    let crates_dir = repo_root.join("crates");

    let manifests = match select_crate_manifests(&crates_dir, &options.crates) {
        Ok(manifests) => manifests,
        Err(message) => {
            eprintln!("targo trust self-improve: {message}");
            return ExitCode::from(2);
        }
    };
    if manifests.is_empty() {
        eprintln!("targo trust self-improve: no Trust-owned crates selected");
        return ExitCode::from(2);
    }

    let mut frontier = TrustOnTrustFrontier::default();
    let mut targets: Vec<RepairTarget> = Vec::new();
    let mut coverage = MeasurementCoverage {
        selected_crates: manifests.iter().map(|(name, _)| name.clone()).collect(),
        failures: Vec::new(),
    };

    let baseline = match options
        .baseline
        .as_deref()
        .map(|path| load_selected_baseline(path, &coverage.selected_crates))
    {
        Some(Ok(baseline)) => Some(baseline),
        Some(Err(message)) => {
            eprintln!("targo trust self-improve: failed to read baseline: {message}");
            return ExitCode::from(2);
        }
        None => None,
    };

    let capture_root = match options
        .capture_dir
        .as_deref()
        .map(crate::self_verify_cli::create_private_report_directory)
        .transpose()
    {
        Ok(root) => root,
        Err(message) => {
            eprintln!("targo trust self-improve: {message}");
            return ExitCode::from(2);
        }
    };

    #[cfg(unix)]
    let mut timings =
        trust_qualification::improvement::Measurements::new(&coverage.selected_crates)
            .expect("selected crate names were validated as unique and nonempty");
    for (crate_name, manifest) in &manifests {
        #[cfg(unix)]
        let timed = timings.start(crate_name).expect("each selected crate is attempted once");
        let measured = verify_crate(crate_name, manifest, capture_root.as_deref());
        #[cfg(unix)]
        timed.finish(measured.is_ok());
        match measured {
            Ok(measurement) => {
                frontier.push(measurement.frontier);
                targets.extend(measurement.targets);
            }
            Err(message) => coverage.failures.push((crate_name.clone(), message)),
        }
    }
    #[cfg(unix)]
    let timing_report = native::timing_report(timings);

    let delta = baseline.as_ref().and_then(|baseline| {
        (coverage.complete(&frontier) && frontier.total_obligations() > 0)
            .then(|| FrontierDelta::between(baseline, &frontier))
    });

    if let Some(out) = options.out.as_deref() {
        if let Err(message) = write_frontier_json(out, &frontier, &coverage) {
            eprintln!("targo trust self-improve: failed to write --out: {message}");
            return ExitCode::from(1);
        }
    }

    if options.json {
        let rendered = render_json(&frontier, &targets, delta.as_ref(), &coverage, intent.as_ref());
        #[cfg(unix)]
        let rendered = {
            let mut value: serde_json::Value =
                serde_json::from_str(&rendered).expect("render_json produced a JSON object");
            value["verification_timing"] = timing_report.clone();
            format!("{value}\n")
        };
        print!("{rendered}");
    } else {
        print!("{}", render_text(&frontier, &targets, delta.as_ref(), &coverage, intent.as_ref()));
        #[cfg(unix)]
        eprintln!("verification timing: {timing_report}");
    }

    // When an intent document is supplied, render an intent-guided AI repair
    // prompt per target. These are proposals only — nothing is applied.
    if let Some(intent) = intent.as_ref() {
        let excerpt = intent.excerpt(2000);
        print_repair_prompts(&targets, &excerpt);
    }

    let code = measurement_exit_code(
        &frontier,
        &coverage,
        baseline.as_ref(),
        options.require_no_regression,
    );
    if options.require_no_regression {
        if delta.is_some() {
            for current in &frontier.crates {
                if let Some(previous) = baseline
                    .as_ref()
                    .and_then(|baseline| {
                        baseline.crates.iter().find(|row| row.crate_name == current.crate_name)
                    })
                    .filter(|previous| current.proved < previous.proved)
                {
                    eprintln!(
                        "targo trust self-improve: {} regressed: proved {} -> {}",
                        current.crate_name, previous.proved, current.proved,
                    );
                }
            }
        }
        match code {
            0 => eprintln!("targo trust self-improve: frontier floor preserved"),
            1 => eprintln!(
                "targo trust self-improve: frontier regressed by {} proved obligations",
                baseline
                    .as_ref()
                    .expect("a regression requires a complete baseline")
                    .total_proved()
                    - frontier.total_proved(),
            ),
            _ => eprintln!(
                "targo trust self-improve: frontier floor unavailable; current measurement is incomplete or has no obligations"
            ),
        }
    }
    ExitCode::from(code)
}

/// The floor compares statistical counts only after the live reduction has
/// accounted for every selected crate. Missing work cannot become improvement.
fn measurement_exit_code(
    frontier: &TrustOnTrustFrontier,
    coverage: &MeasurementCoverage,
    baseline: Option<&TrustOnTrustFrontier>,
    require_no_regression: bool,
) -> u8 {
    let code = coverage.exit_code(frontier);
    if code != 0 || !require_no_regression {
        return code;
    }
    if frontier.total_obligations() == 0 {
        return 3;
    }
    match baseline {
        Some(baseline) if frontier.total_proved() < baseline.total_proved() => 1,
        Some(_) => 0,
        None => 3,
    }
}

fn load_selected_baseline(
    path: &Path,
    selected: &[String],
) -> Result<TrustOnTrustFrontier, String> {
    let baseline = load_frontier_json(path)?;
    let names: BTreeSet<_> = baseline.crates.iter().map(|row| &row.crate_name).collect();
    if names != selected.iter().collect() {
        return Err("baseline selects a different crate population".into());
    }
    Ok(baseline)
}

/// Emit the intent-guided repair prompt for each target to stderr, paired with
/// a ready-to-run assistant invocation. Proposal-only — nothing is applied.
fn print_repair_prompts(targets: &[RepairTarget], intent_excerpt: &str) {
    if targets.is_empty() {
        return;
    }
    eprintln!();
    eprintln!("=== Intent-guided repair prompts ({} target(s)) ===", targets.len());
    for target in targets {
        let body = target.repair_prompt(Some(intent_excerpt));
        let command = build_ai_repair_command(&body);
        eprintln!();
        eprintln!("--- repair prompt for `{}::{}` ---", target.crate_name, target.function);
        eprint!("{body}");
        eprintln!("--- run with: ---");
        eprint!("{command}");
    }
    eprintln!("--- end intent-guided repair prompts ---");
}

/// Discover the crate manifests to verify. Without `--crate`, every immediate
/// subdirectory of `crates/` containing a `Cargo.toml` is selected.
fn select_crate_manifests(
    crates_dir: &Path,
    requested: &[String],
) -> Result<Vec<(String, PathBuf)>, String> {
    if !requested.is_empty() {
        let mut manifests = Vec::new();
        let mut seen = BTreeSet::new();
        for name in requested {
            let mut components = Path::new(name).components();
            if !matches!(components.next(), Some(std::path::Component::Normal(part)) if part == std::ffi::OsStr::new(name))
                || components.next().is_some()
            {
                return Err(format!("crate `{name}` must be one directory name under crates/"));
            }
            if !seen.insert(name) {
                return Err(format!("crate `{name}` was selected more than once"));
            }
            let manifest = crates_dir.join(name).join("Cargo.toml");
            if !manifest.is_file() {
                return Err(format!("crate `{name}` not found under {}", crates_dir.display()));
            }
            manifests.push((name.clone(), manifest));
        }
        return Ok(manifests);
    }

    let entries = fs::read_dir(crates_dir)
        .map_err(|error| format!("reading {}: {error}", crates_dir.display()))?;
    let mut manifests = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|error| format!("reading {}: {error}", crates_dir.display()))?;
        let path = entry.path();
        if !path.is_dir() {
            continue;
        }
        let manifest = path.join("Cargo.toml");
        if manifest.is_file() {
            if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
                manifests.push((name.to_string(), manifest));
            }
        }
    }
    manifests.sort();
    Ok(manifests)
}

pub(crate) struct CrateMeasurement {
    frontier: CrateFrontier,
    targets: Vec<RepairTarget>,
}

/// Verify one crate in this process and reduce the canonical report while its
/// opaque publication capability is still live. Retaining or reloading a JSON
/// DTO would discard that authority and turn every genuine proof into Unknown.
fn verify_crate(
    crate_name: &str,
    manifest: &Path,
    capture_root: Option<&Path>,
) -> Result<CrateMeasurement, String> {
    let capture_dir = capture_root
        .map(|root| crate::self_verify_cli::create_private_report_directory(&root.join(crate_name)))
        .transpose()?;
    let args = verification_args(manifest, capture_dir.as_deref());
    let mut measurement = None;
    let mut diagnostics = crate::pipeline::run::CompilerRunDiagnostics::default();
    let exit = {
        let mut consume = |live: &crate::report::LiveCanonicalReport| {
            measurement = Some(measure_live_report(crate_name, live));
            Ok(())
        };
        let mut observe =
            |batch: &crate::pipeline::run::CompilerRunDiagnostics| diagnostics.extend(batch);
        crate::run_subcommand_with_diagnostics(
            crate::types::Subcommand::Check,
            &args,
            Some(&mut consume),
            Some(&mut observe),
            if capture_dir.is_some() {
                crate::pipeline::run::ReportRendering::ArtifactsOnly
            } else {
                crate::pipeline::run::ReportRendering::Suppressed
            },
        )
    };
    finish_measurement(measurement, exit, &diagnostics, capture_dir.is_some())
}

pub(crate) fn measure_live_report(
    crate_name: &str,
    live: &crate::report::LiveCanonicalReport,
) -> CrateMeasurement {
    let report = live.for_self_improve_reduction();
    CrateMeasurement {
        frontier: CrateFrontier::from_summary(crate_name, &report.summary),
        targets: repair_targets(report),
    }
}

pub(crate) fn finish_measurement(
    measurement: Option<CrateMeasurement>,
    exit: ExitCode,
    diagnostics: &crate::pipeline::run::CompilerRunDiagnostics,
    capture_requested: bool,
) -> Result<CrateMeasurement, String> {
    if capture_requested && diagnostics.artifact_failed {
        return Err(format!(
            "requested capture failed after verification (exit {exit:?}); {}",
            diagnostics
                .errors
                .iter()
                .map(|error| error.message.as_str())
                .collect::<Vec<_>>()
                .join("; ")
        ));
    }
    measurement.ok_or_else(|| failed_measurement_reason(exit, diagnostics))
}

fn verification_args(manifest: &Path, capture_dir: Option<&Path>) -> Vec<String> {
    let mut args = vec!["--manifest-path".to_string(), manifest.display().to_string()];
    if let Some(capture_dir) = capture_dir {
        args.extend([
            "--report-dir".to_string(),
            capture_dir.join("report").display().to_string(),
            "--dump-verifier-inputs".to_string(),
            capture_dir.join("verifier-inputs").display().to_string(),
        ]);
    }
    args
}

fn failed_measurement_reason(
    exit: ExitCode,
    diagnostics: &crate::pipeline::run::CompilerRunDiagnostics,
) -> String {
    let mut reason =
        format!("in-process check produced no live sealed compiler report (exit {exit:?})");
    if !diagnostics.errors.is_empty() {
        reason.push_str("; compiler/setup errors: ");
        reason.push_str(
            &diagnostics.errors.iter().map(|d| d.message.as_str()).collect::<Vec<_>>().join("; "),
        );
        if diagnostics.truncated {
            reason.push_str("; additional diagnostic text omitted");
        }
    }
    reason
}

fn load_frontier_json(path: &Path) -> Result<TrustOnTrustFrontier, String> {
    let bytes = crate::input_limits::read_bounded_file(
        path,
        crate::input_limits::MAX_SAVED_PROOF_REPORT_BYTES,
    )
    .map_err(|error| format!("reading {}: {error}", path.display()))?;
    let value: serde_json::Value = serde_json::from_slice(&bytes)
        .map_err(|error| format!("parsing {}: {error}", path.display()))?;
    if value.get("schema").and_then(|v| v.as_str()) != Some("trust.self-improve.frontier.v2")
        || value.get("measurement_complete").and_then(|v| v.as_bool()) != Some(true)
    {
        return Err("baseline requires a complete v2 measurement; legacy and partial frontiers cannot establish convergence".to_string());
    }
    let selected: Vec<String> = serde_json::from_value(
        value.get("selected_crates").cloned().ok_or("baseline lacks selected_crates")?,
    )
    .map_err(|error| format!("invalid selected_crates: {error}"))?;
    let crates =
        value.get("crates").and_then(|c| c.as_array()).ok_or("baseline lacks crates array")?;
    let mut frontier = TrustOnTrustFrontier::default();
    let mut names = BTreeSet::new();
    for entry in crates {
        let name = entry
            .get("crate")
            .and_then(|v| v.as_str())
            .filter(|name| !name.is_empty())
            .ok_or("baseline crate name is missing or invalid")?;
        if !names.insert(name.to_string()) {
            return Err(format!("baseline repeats crate `{name}`"));
        }
        let count = |key: &str| -> Result<usize, String> {
            entry
                .get(key)
                .and_then(|value| value.as_u64())
                .and_then(|value| usize::try_from(value).ok())
                .ok_or_else(|| format!("baseline crate `{name}` has missing or invalid `{key}`"))
        };
        let row = CrateFrontier {
            crate_name: name.to_string(),
            obligations: count("obligations")?,
            proved: count("proved")?,
            runtime_checked: count("runtime_checked")?,
            failed: count("failed")?,
            unknown: count("unknown")?,
        };
        if row.proved > row.obligations {
            return Err(format!(
                "baseline crate `{name}` proves more than its obligation population"
            ));
        }
        frontier.push(row);
    }
    let counters: [fn(&CrateFrontier) -> usize; 5] = [
        |row| row.obligations,
        |row| row.proved,
        |row| row.runtime_checked,
        |row| row.failed,
        |row| row.unknown,
    ];
    for count in counters {
        frontier
            .crates
            .iter()
            .try_fold(0_usize, |sum, row| sum.checked_add(count(row)))
            .and_then(|total| i64::try_from(total).ok())
            .ok_or("baseline counts exceed the supported comparison range")?;
    }
    frontier
        .crates
        .iter()
        .try_fold(0_usize, |sum, row| {
            row.failed.checked_add(row.unknown).and_then(|count| sum.checked_add(count))
        })
        .and_then(|total| i64::try_from(total).ok())
        .ok_or("baseline unproved counts exceed the supported comparison range")?;
    let coverage = MeasurementCoverage { selected_crates: selected, failures: Vec::new() };
    if !coverage.complete(&frontier)
        || coverage.selected_crates.iter().collect::<BTreeSet<_>>().len()
            != coverage.selected_crates.len()
        || frontier.total_obligations() == 0
        || value
            .get("measurement_failures")
            .and_then(|v| v.as_array())
            .is_none_or(|v| !v.is_empty())
    {
        return Err("baseline must account for every unique selected crate, without failed measurements, and contain obligations".to_string());
    }
    // A saved baseline is a statistical comparison, never proof authority, but
    // its explicit coverage and aggregate fields must still agree with its
    // rows. Otherwise an incomplete measurement can relabel itself complete.
    let measured: Vec<String> = serde_json::from_value(
        value.get("measured_crates").cloned().ok_or("baseline lacks measured_crates")?,
    )
    .map_err(|error| format!("invalid measured_crates: {error}"))?;
    if measured.len() != frontier.crates.len()
        || measured.iter().collect::<BTreeSet<_>>()
            != frontier.crates.iter().map(|row| &row.crate_name).collect::<BTreeSet<_>>()
        || value.get("unmeasured_crates").and_then(|v| v.as_array()).is_none_or(|v| !v.is_empty())
    {
        return Err("baseline measured/unmeasured inventories contradict its complete crate rows"
            .to_string());
    }
    for (key, expected) in [
        ("total_obligations", frontier.total_obligations()),
        ("total_proved", frontier.total_proved()),
        ("total_runtime_checked", frontier.total_runtime_checked()),
        ("total_unproved", frontier.total_unproved()),
    ] {
        if value
            .get(key)
            .and_then(|value| value.as_u64())
            .and_then(|value| usize::try_from(value).ok())
            != Some(expected)
        {
            return Err(format!(
                "baseline `{key}` is missing, invalid or contradicts its crate rows"
            ));
        }
    }
    if value.get("convergence_score").and_then(|v| v.as_f64()).is_none_or(|score| {
        !score.is_finite() || (score - frontier.convergence_score()).abs() > 4.0 * f64::EPSILON
    }) {
        return Err("baseline convergence_score is missing, invalid or contradicts its crate rows"
            .to_string());
    }
    Ok(frontier)
}

fn write_frontier_json(
    path: &Path,
    frontier: &TrustOnTrustFrontier,
    coverage: &MeasurementCoverage,
) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent)
                .map_err(|error| format!("creating {}: {error}", parent.display()))?;
        }
    }
    let serialized = frontier_json_value(frontier, coverage).to_string();
    fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .and_then(|mut file| file.write_all(serialized.as_bytes()))
        .map_err(|error| format!("writing new frontier {}: {error}", path.display()))
}

fn frontier_json_value(
    frontier: &TrustOnTrustFrontier,
    coverage: &MeasurementCoverage,
) -> serde_json::Value {
    let crates: Vec<serde_json::Value> = frontier
        .crates
        .iter()
        .map(|c| {
            serde_json::json!({
                "crate": c.crate_name,
                "obligations": c.obligations,
                "proved": c.proved,
                "runtime_checked": c.runtime_checked,
                "failed": c.failed,
                "unknown": c.unknown,
            })
        })
        .collect();
    serde_json::json!({
        "schema": "trust.self-improve.frontier.v2",
        "selected_crates": coverage.selected_crates,
        "measured_crates": frontier.crates.iter().map(|row| &row.crate_name).collect::<Vec<_>>(),
        "measurement_complete": coverage.complete(frontier),
        "measurement_failures": coverage.failures.iter().map(|(name, reason)| {
            serde_json::json!({"crate": name, "reason": reason})
        }).collect::<Vec<_>>(),
        "unmeasured_crates": coverage.selected_crates.iter().filter(|name| {
            !frontier.crates.iter().any(|row| &row.crate_name == *name)
        }).collect::<Vec<_>>(),
        "convergence_score": (coverage.complete(frontier) && frontier.total_obligations() > 0)
            .then(|| frontier.convergence_score()),
        "total_obligations": frontier.total_obligations(),
        "total_proved": frontier.total_proved(),
        "total_runtime_checked": frontier.total_runtime_checked(),
        "total_unproved": frontier.total_unproved(),
        "crates": crates,
    })
}

fn render_json(
    frontier: &TrustOnTrustFrontier,
    targets: &[RepairTarget],
    delta: Option<&FrontierDelta>,
    coverage: &MeasurementCoverage,
    intent: Option<&ResolvedIntent>,
) -> String {
    let mut value = frontier_json_value(frontier, coverage);
    let object = value.as_object_mut().expect("frontier json is an object");
    if let Some(intent) = intent {
        object.insert(
            "intent".to_string(),
            serde_json::json!({
                "source": intent.source.label(),
                "path": intent.path.display().to_string(),
                "bytes": intent.text.len(),
            }),
        );
    }
    object.insert(
        "repair_targets".to_string(),
        serde_json::Value::Array(
            targets
                .iter()
                .map(|t| {
                    serde_json::json!({
                        "crate": t.crate_name,
                        "function": t.function,
                        "failed": t.failed,
                        "unknown": t.unknown,
                        "runtime_checked": t.runtime_checked,
                        "vc_kind": t.vc_kind,
                        "solver": t.solver,
                        "outcome": t.outcome,
                        "intent_guided": intent.is_some(),
                    })
                })
                .collect(),
        ),
    );
    if let Some(delta) = delta {
        object.insert(
            "delta".to_string(),
            serde_json::json!({
                "baseline_score": delta.baseline_score,
                "current_score": delta.current_score,
                "proved_delta": delta.proved_delta,
                "unproved_delta": delta.unproved_delta,
            }),
        );
    }
    format!("{value}\n")
}

fn render_text(
    frontier: &TrustOnTrustFrontier,
    targets: &[RepairTarget],
    delta: Option<&FrontierDelta>,
    coverage: &MeasurementCoverage,
    intent: Option<&ResolvedIntent>,
) -> String {
    let mut out = String::new();
    out.push_str("Trust-on-Trust proof frontier\n");
    if let Some(intent) = intent {
        out.push_str(&format!(
            "  intent: {} ({} bytes) — repair prompts are intent-guided\n",
            intent.source.label(),
            intent.text.len(),
        ));
    }
    out.push_str(&format!(
        "  measured crates: {} / {} selected\n",
        frontier.crates.len(),
        coverage.selected_crates.len()
    ));
    if coverage.complete(frontier) && frontier.total_obligations() > 0 {
        out.push_str(&format!(
            "  convergence: {:.4}  (proved {} / obligations {})\n",
            frontier.convergence_score(),
            frontier.total_proved(),
            frontier.total_obligations(),
        ));
    } else {
        out.push_str("  convergence: unavailable (incomplete measurement or zero obligations)\n");
    }
    out.push_str(&format!(
        "  runtime-checked: {}   unproved: {}\n",
        frontier.total_runtime_checked(),
        frontier.total_unproved(),
    ));

    if let Some(delta) = delta {
        let arrow = if delta.current_score >= delta.baseline_score { "+" } else { "" };
        out.push_str(&format!(
            "  delta vs baseline: {:.4} -> {:.4} ({arrow}{:.4}), proved {:+}, unproved {:+}\n",
            delta.baseline_score,
            delta.current_score,
            delta.current_score - delta.baseline_score,
            delta.proved_delta,
            delta.unproved_delta,
        ));
    }

    out.push_str("\nPer-crate frontier:\n");
    for c in &frontier.crates {
        out.push_str(&format!(
            "  {:<28} proved {:>5} / {:<5}  runtime {:>4}  unproved {:>4}\n",
            c.crate_name,
            c.proved,
            c.obligations,
            c.runtime_checked,
            c.unproved(),
        ));
    }

    if targets.is_empty() {
        if !coverage.complete(frontier) || frontier.total_obligations() == 0 {
            out.push_str("\nNo repair targets recovered; this is not evidence of convergence.\n");
        } else if frontier.total_unproved() > 0 {
            out.push_str("\nNo function-level repair targets recovered; unresolved crate-level results remain.\n");
        } else if frontier.total_runtime_checked() > 0 {
            out.push_str("\nNo function-level repair targets recovered; runtime checks still need static proofs.\n");
        } else if frontier.total_proved().checked_add(frontier.total_runtime_checked())
            != Some(frontier.total_obligations())
        {
            out.push_str("\nNo function-level repair targets recovered; remaining obligations are not proved or runtime-checked.\n");
        } else {
            out.push_str("\nNo repair targets — every obligation is proved.\n");
        }
    } else {
        out.push_str(&format!(
            "\nRepair targets (proposal-only, nothing applied) — {} function(s):\n",
            targets.len(),
        ));
        for t in targets {
            out.push_str(&format!(
                "  {}::{}  ({}, failed {}, unknown {}, runtime-checked {})\n",
                t.crate_name, t.function, t.vc_kind, t.failed, t.unknown, t.runtime_checked,
            ));
        }
        if intent.is_some() {
            out.push_str(
                "\nIntent-guided AI repair prompts for these targets follow on stderr (proposal-only).\n",
            );
        } else {
            out.push_str(
                "\nThese are where spec inference and AI-in-the-loop repair would aim. Pass --intent <doc> to emit intent-guided repair prompts.\n",
            );
        }
    }

    if !coverage.failures.is_empty() {
        out.push_str(&format!("\n{} crate(s) could not be measured:\n", coverage.failures.len()));
        for (name, reason) in &coverage.failures {
            out.push_str(&format!("  {name}: {reason}\n"));
        }
        out.push_str(
            "  The selected-crate inventory is incomplete; this run is not convergence evidence.\n",
        );
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn capture_relative_directory_is_created_in_an_owned_subprocess_cwd() {
        const CHILD: &str = "TRUST_SELF_IMPROVE_CAPTURE_RELATIVE_CHILD";
        if std::env::var_os(CHILD).is_some() {
            let path =
                crate::self_verify_cli::create_private_report_directory(Path::new("captures"))
                    .expect("relative leaf must sync its current-directory parent");
            assert_eq!(path, std::env::current_dir().unwrap().join("captures"));
            assert!(path.is_dir());
            return;
        }
        let root = tempfile::tempdir().unwrap();
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "self_improve::tests::capture_relative_directory_is_created_in_an_owned_subprocess_cwd",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .current_dir(root.path())
            .output()
            .unwrap();
        assert!(output.status.success(), "{output:?}");
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(
            stdout.lines().any(|line| line.starts_with("test result: ok. 1 passed;")),
            "the isolated child must execute its exact test: {stdout}"
        );
        assert!(root.path().join("captures").is_dir());
    }

    #[test]
    fn capture_option_is_explicit_and_rejects_missing_or_repeated_paths() {
        let default = parse_options(&[]).unwrap().unwrap();
        assert!(default.capture_dir.is_none());
        let options = parse_options(&[
            "--capture-dir".into(),
            "artifacts with spaces".into(),
            "--crate".into(),
            "trust-budget".into(),
        ])
        .unwrap()
        .unwrap();
        assert_eq!(options.capture_dir, Some(PathBuf::from("artifacts with spaces")));
        assert_eq!(options.crates, ["trust-budget"]);
        for args in [
            vec!["--capture-dir".into()],
            vec!["--capture-dir".into(), "--json".into()],
            vec!["--capture-dir".into(), "".into()],
            vec!["--capture-dir".into(), "a".into(), "--capture-dir".into(), "b".into()],
        ] {
            assert!(parse_options(&args).is_err());
        }
    }

    #[test]
    fn capture_arguments_forward_existing_outputs_without_changing_default_run() {
        let manifest = Path::new("crates/trust-budget/Cargo.toml");
        assert_eq!(
            verification_args(manifest, None),
            ["--manifest-path", "crates/trust-budget/Cargo.toml"]
        );
        let capture = Path::new("audit dir/trust-budget");
        assert_eq!(
            verification_args(manifest, Some(capture)),
            [
                "--manifest-path".to_string(),
                manifest.display().to_string(),
                "--report-dir".to_string(),
                capture.join("report").display().to_string(),
                "--dump-verifier-inputs".to_string(),
                capture.join("verifier-inputs").display().to_string(),
            ]
        );
    }

    #[test]
    fn capture_directory_is_fresh_private_and_keeps_each_crate_separate() {
        let temp = tempfile::tempdir().unwrap();
        let root =
            crate::self_verify_cli::create_private_report_directory(&temp.path().join("capture"))
                .unwrap();
        for name in ["trust-budget", "trust-intbound"] {
            let dir =
                crate::self_verify_cli::create_private_report_directory(&root.join(name)).unwrap();
            assert_eq!(dir, root.join(name));
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt as _;
                assert_eq!(fs::metadata(&dir).unwrap().permissions().mode() & 0o777, 0o700);
            }
        }
        let retained = root.join("trust-budget/retained-proof");
        fs::write(&retained, b"original evidence").unwrap();
        assert!(crate::self_verify_cli::create_private_report_directory(&root).is_err());
        assert!(
            crate::self_verify_cli::create_private_report_directory(&root.join("trust-budget"))
                .is_err()
        );
        assert_eq!(fs::read(retained).unwrap(), b"original evidence");
    }

    #[test]
    fn capture_setup_error_is_a_failed_measurement_before_compiler_dispatch() {
        let temp = tempfile::tempdir().unwrap();
        fs::write(temp.path().join("trust-budget"), b"keep this file").unwrap();
        let error = verify_crate(
            "trust-budget",
            &temp.path().join("missing-manifest.toml"),
            Some(temp.path()),
        )
        .err()
        .expect("capture collision refuses before dispatch");
        assert!(error.contains("refusing non-fresh report directory"), "{error}");
        assert_eq!(fs::read(temp.path().join("trust-budget")).unwrap(), b"keep this file");
        let coverage = MeasurementCoverage {
            selected_crates: vec!["trust-budget".into()],
            failures: vec![("trust-budget".into(), error)],
        };
        let frontier = TrustOnTrustFrontier::default();
        assert_eq!(coverage.exit_code(&frontier), 3);
        let value = frontier_json_value(&frontier, &coverage);
        assert_eq!(value["selected_crates"], serde_json::json!(["trust-budget"]));
        assert_eq!(value["unmeasured_crates"], serde_json::json!(["trust-budget"]));
        assert_eq!(value["total_proved"], 0);
        assert!(value["convergence_score"].is_null());
    }

    #[test]
    fn capture_export_setup_refusals_reach_the_failed_measurement() {
        use crate::pipeline::run::{
            CompilerRun, CompilerRunDiagnostics, ReportRendering, run_compiler,
        };

        let root = tempfile::tempdir().unwrap();
        let compiler_root = tempfile::tempdir().unwrap();
        let compiler = compiler_root.path().join("bin/trustc");
        let capture = root.path().join("occupied");
        fs::write(&capture, b"retained capture bytes").unwrap();
        for (args, expected) in [
            (vec!["targo".to_string(), "build".to_string()], "requires a normal Cargo check"),
            (
                vec!["targo".to_string(), "check".to_string()],
                "could not create fresh verifier input export",
            ),
        ] {
            let mut diagnostics = CompilerRunDiagnostics::default();
            let mut called = false;
            let exit = {
                let mut observe = |batch: &CompilerRunDiagnostics| diagnostics.extend(batch);
                let mut consume = |_report: &crate::report::LiveCanonicalReport| {
                    called = true;
                    Ok(())
                };
                run_compiler(CompilerRun {
                    cmd_args: &args,
                    rustc_path: &compiler,
                    config: &crate::config::TrustConfig::default(),
                    selected_codegen_backend: None,
                    supports_json_transport: true,
                    strict_artifact_policy: false,
                    strict_result_gate: true,
                    certify_gate: false,
                    allow_l0_gaps: false,
                    memory_safe_policy: false,
                    survey: false,
                    hardened: false,
                    trust_profile: None,
                    spec_emit_dir: None,
                    dump_verifier_inputs: Some(&capture),
                    format: crate::types::OutputFormat::Json,
                    report_dir: None,
                    unsafe_memory_report: None,
                    live_report_consumer: Some(&mut consume),
                    diagnostic_observer: Some(&mut observe),
                    render_output: ReportRendering::ArtifactsOnly,
                    ephemeral_single_file_output: false,
                    test_target_panics: crate::test_target_panics::TestTargetPanicPolicy::Strict,
                    agent_delta: None,
                })
            };
            assert_eq!(exit, ExitCode::from(2));
            assert!(!called);
            let reason = finish_measurement(None, exit, &diagnostics, true).err().unwrap();
            assert!(reason.contains(expected), "{reason}");
            let frontier = TrustOnTrustFrontier::default();
            let coverage = MeasurementCoverage {
                selected_crates: vec!["fixture".into()],
                failures: vec![("fixture".into(), reason)],
            };
            let json = frontier_json_value(&frontier, &coverage);
            assert_eq!(json["measurement_complete"], false);
            assert_eq!(json["measured_crates"], serde_json::json!([]));
            assert_eq!(json["total_proved"], 0);
            assert_eq!(json["total_runtime_checked"], 0);
            assert!(json["convergence_score"].is_null());
        }
        assert_eq!(fs::read(capture).unwrap(), b"retained capture bytes");
    }
    #[test]
    #[cfg(unix)]
    fn capture_refuses_symlink_roots_parents_and_crate_directories() {
        use std::os::unix::fs::symlink;
        let temp = tempfile::tempdir().unwrap();
        let target = temp.path().join("retained");
        fs::create_dir(&target).unwrap();
        fs::write(target.join("proof"), b"original evidence").unwrap();
        let alias = temp.path().join("alias");
        symlink(&target, &alias).unwrap();
        assert!(crate::self_verify_cli::create_private_report_directory(&alias).is_err());
        assert!(
            crate::self_verify_cli::create_private_report_directory(&alias.join("run")).is_err()
        );
        let root =
            crate::self_verify_cli::create_private_report_directory(&temp.path().join("capture"))
                .unwrap();
        symlink(&target, root.join("trust-budget")).unwrap();
        let error = verify_crate("trust-budget", Path::new("unused"), Some(&root))
            .err()
            .expect("symlink capture refuses before dispatch");
        assert!(error.contains("refusing non-fresh report directory"), "{error}");
        assert_eq!(fs::read(target.join("proof")).unwrap(), b"original evidence");
        assert!(!target.join("run").exists());
    }

    #[test]
    fn outcome_label_does_not_present_a_fail_closed_row_as_a_found_bug() {
        let fail_closed = ObligationOutcome::failed_from_backend(
            trust_types::UNSAFE_DEMAND_FAIL_CLOSED_SOLVER,
            None,
        );
        assert_eq!(
            outcome_label(&fail_closed),
            "FAILED (unproved, no counterexample; failed closed)"
        );
        // CONTROLS: a refuted row and a definite structural finding keep `FAILED`.
        assert_eq!(outcome_label(&ObligationOutcome::failed_from_backend("ay", None)), "FAILED");
        assert_eq!(
            outcome_label(&ObligationOutcome::failed_from_backend(
                trust_types::UNSAFE_DEMAND_DEFINITE_SOLVER,
                None
            )),
            "FAILED"
        );
    }

    fn crate_frontier(name: &str, proved: usize, obligations: usize) -> CrateFrontier {
        CrateFrontier {
            crate_name: name.to_string(),
            obligations,
            proved,
            runtime_checked: 0,
            failed: obligations - proved,
            unknown: 0,
        }
    }

    #[test]
    fn regression_floor_requires_an_explicit_baseline() {
        assert!(!parse_options(&[]).unwrap().unwrap().require_no_regression);
        assert!(parse_options(&["--require-no-regression".into()]).is_err());
        let options = parse_options(&[
            "--require-no-regression".into(),
            "--baseline".into(),
            "recorded frontier.json".into(),
        ])
        .unwrap()
        .unwrap();
        assert!(options.require_no_regression);
        assert_eq!(options.baseline, Some(PathBuf::from("recorded frontier.json")));
        assert!(
            parse_options(&[
                "--baseline".into(),
                "baseline.json".into(),
                "--require-no-regression".into(),
                "--require-no-regression".into(),
            ])
            .is_err()
        );
    }

    #[test]
    fn regression_floor_rejects_a_real_drop_but_allows_unchanged_or_added_obligations() {
        let baseline = TrustOnTrustFrontier { crates: vec![crate_frontier("demo", 10, 12)] };
        let coverage =
            MeasurementCoverage { selected_crates: vec!["demo".into()], failures: Vec::new() };
        for (proved, obligations, expected) in [(7, 12, 1), (10, 12, 0), (10, 50, 0), (11, 50, 0)] {
            let current =
                TrustOnTrustFrontier { crates: vec![crate_frontier("demo", proved, obligations)] };
            assert_eq!(measurement_exit_code(&current, &coverage, Some(&baseline), true), expected);
            assert_eq!(
                measurement_exit_code(&current, &coverage, Some(&baseline), false),
                0,
                "comparison without the explicit floor retains its measurement-only behavior"
            );
        }
    }

    #[test]
    fn regression_floor_preserves_the_total_proved_policy_across_crates() {
        let baseline = TrustOnTrustFrontier {
            crates: vec![crate_frontier("a", 5, 10), crate_frontier("b", 5, 10)],
        };
        let current = TrustOnTrustFrontier {
            crates: vec![crate_frontier("a", 4, 10), crate_frontier("b", 6, 10)],
        };
        let coverage = MeasurementCoverage {
            selected_crates: vec!["a".into(), "b".into()],
            failures: Vec::new(),
        };
        let delta = FrontierDelta::between(&baseline, &current);
        assert_eq!(delta.proved_delta, 0);
        assert_eq!(measurement_exit_code(&current, &coverage, Some(&baseline), true), 0);
    }

    #[test]
    fn regression_floor_cannot_pass_incomplete_or_empty_current_measurements() {
        let current = TrustOnTrustFrontier { crates: vec![crate_frontier("measured", 10, 10)] };
        let incomplete = MeasurementCoverage {
            selected_crates: vec!["measured".into(), "missing".into()],
            failures: vec![("missing".into(), "compiler did not run".into())],
        };
        // A favorable numeric delta never repairs a missing selected measurement.
        assert_eq!(measurement_exit_code(&current, &incomplete, Some(&current), true), 3);
        let empty = TrustOnTrustFrontier { crates: vec![crate_frontier("empty", 0, 0)] };
        let coverage =
            MeasurementCoverage { selected_crates: vec!["empty".into()], failures: Vec::new() };
        assert_eq!(measurement_exit_code(&empty, &coverage, None, true), 3);
        let complete =
            MeasurementCoverage { selected_crates: vec!["measured".into()], failures: Vec::new() };
        assert_eq!(
            measurement_exit_code(&current, &complete, None, true),
            3,
            "absence of a complete baseline is not a passing floor"
        );
    }

    #[test]
    fn regression_floor_baseline_refuses_missing_partial_or_different_populations() {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("baseline.json");
        assert!(load_selected_baseline(&path, &["demo".into()]).is_err());
        let frontier = TrustOnTrustFrontier { crates: vec![crate_frontier("demo", 10, 12)] };
        let coverage =
            MeasurementCoverage { selected_crates: vec!["demo".into()], failures: Vec::new() };
        write_frontier_json(&path, &frontier, &coverage).unwrap();
        assert!(load_selected_baseline(&path, &["demo".into()]).is_ok());
        assert!(load_selected_baseline(&path, &["other".into()]).is_err());
        assert!(load_selected_baseline(&path, &["demo".into(), "missing".into()]).is_err());
        let partial = root.path().join("partial.json");
        let incomplete = MeasurementCoverage {
            selected_crates: vec!["demo".into(), "missing".into()],
            failures: vec![("missing".into(), "compiler refused".into())],
        };
        write_frontier_json(&partial, &frontier, &incomplete).unwrap();
        assert!(load_selected_baseline(&partial, &incomplete.selected_crates).is_err());
        assert!(
            write_frontier_json(&path, &frontier, &coverage).is_err(),
            "baseline updates retain the existing fresh-output refusal"
        );
        assert_eq!(load_selected_baseline(&path, &["demo".into()]).unwrap(), frontier);
    }

    #[test]
    fn empty_frontier_is_fully_converged() {
        let frontier = TrustOnTrustFrontier::default();
        assert_eq!(frontier.convergence_score(), 1.0);
        assert_eq!(frontier.total_obligations(), 0);
    }

    #[test]
    fn convergence_score_aggregates_across_crates() {
        let mut frontier = TrustOnTrustFrontier::default();
        frontier.push(crate_frontier("a", 8, 10));
        frontier.push(crate_frontier("b", 2, 10));
        assert_eq!(frontier.total_obligations(), 20);
        assert_eq!(frontier.total_proved(), 10);
        assert_eq!(frontier.total_unproved(), 10);
        assert!((frontier.convergence_score() - 0.5).abs() < 1e-9);
    }

    #[test]
    fn unproved_counts_failed_and_unknown() {
        let frontier = CrateFrontier {
            crate_name: "c".to_string(),
            obligations: 10,
            proved: 4,
            runtime_checked: 2,
            failed: 1,
            unknown: 3,
        };
        assert_eq!(frontier.unproved(), 4);
    }

    #[test]
    fn delta_tracks_improvement() {
        let mut baseline = TrustOnTrustFrontier::default();
        baseline.push(crate_frontier("a", 5, 10));
        let mut current = TrustOnTrustFrontier::default();
        current.push(crate_frontier("a", 8, 10));

        let delta = FrontierDelta::between(&baseline, &current);
        assert!((delta.baseline_score - 0.5).abs() < 1e-9);
        assert!((delta.current_score - 0.8).abs() < 1e-9);
        assert_eq!(delta.proved_delta, 3);
        assert_eq!(delta.unproved_delta, -3);
    }

    #[test]
    fn from_summary_folds_unattributed_into_unproved() {
        let summary = CrateSummary {
            functions_analyzed: 1,
            functions_verified: 0,
            functions_runtime_checked: 0,
            functions_with_violations: 1,
            functions_inconclusive: 0,
            total_obligations: 10,
            total_proved: 6,
            total_runtime_checked: 1,
            total_failed: 1,
            total_unknown: 1,
            total_timed_out: 0,
            total_design_requirements: 0,
            total_failed_unproved: 0,
            total_unattributed_failed: 1,
            total_unattributed_unknown: 1,
            total_unattributed_proved: 0,
            proof_grade_engine_statuses: Vec::new(),
            verdict: trust_types::CrateVerdict::HasViolations,
        };
        let frontier = CrateFrontier::from_summary("x", &summary);
        assert_eq!(frontier.proved, 6);
        assert_eq!(frontier.failed, 2);
        assert_eq!(frontier.unknown, 2);
        assert_eq!(frontier.unproved(), 4);
    }

    fn sample_target() -> RepairTarget {
        RepairTarget {
            crate_name: "trust-vcgen".to_string(),
            function: "vcgen::overflow_check".to_string(),
            failed: 1,
            unknown: 0,
            runtime_checked: 0,
            vc_kind: "arithmetic_overflow".to_string(),
            solver: "trust-wp".to_string(),
            outcome: "FAILED".to_string(),
            source_file: Some("crates/trust-vcgen/src/lib.rs".to_string()),
        }
    }

    // These DTOs exercise observational target selection only. They never
    // enter live publication or stand in for proof/monitor authority.
    fn target_selection_report(outcomes: Vec<ObligationOutcome>) -> JsonProofReport {
        let count = |predicate: fn(&ObligationOutcome) -> bool| {
            outcomes.iter().filter(|outcome| predicate(outcome)).count()
        };
        let proved = count(|outcome| matches!(outcome, ObligationOutcome::Proved { .. }));
        let runtime_checked =
            count(|outcome| matches!(outcome, ObligationOutcome::RuntimeChecked { .. }));
        let failed = count(|outcome| matches!(outcome, ObligationOutcome::Failed { .. }));
        let unknown = count(|outcome| {
            matches!(outcome, ObligationOutcome::Unknown { .. } | ObligationOutcome::Timeout { .. })
        });
        let timed_out = count(|outcome| matches!(outcome, ObligationOutcome::Timeout { .. }));
        let design_requirements =
            count(|outcome| matches!(outcome, ObligationOutcome::DesignRequirement { .. }));
        let verdict = FunctionVerdict::from_counts(trust_types::ScopeVerdictCounts {
            total: outcomes.len(),
            proved,
            runtime_checked,
            failed,
            unknown,
            ..Default::default()
        });
        let mut report = trust_report::build_json_report("fixture", &[]);
        report.summary.functions_analyzed = 1;
        report.summary.total_obligations = outcomes.len();
        report.summary.total_proved = proved;
        report.summary.total_runtime_checked = runtime_checked;
        report.summary.total_failed = failed;
        report.summary.total_unknown = unknown;
        report.summary.total_timed_out = timed_out;
        report.summary.total_design_requirements = design_requirements;
        report.summary.verdict = verdict;
        report.functions.push(trust_types::FunctionProofReport {
            function: "fixture::subject".into(),
            summary: trust_types::FunctionSummary {
                total_obligations: outcomes.len(),
                proved,
                runtime_checked,
                failed,
                failed_unproved: 0,
                unknown,
                timed_out,
                design_requirements,
                unattributed_failed: 0,
                unattributed_unknown: 0,
                unattributed_proved: 0,
                total_time_ms: 0,
                max_proof_level: None,
                verdict,
            },
            obligations: outcomes
                .into_iter()
                .enumerate()
                .map(|(index, outcome)| trust_types::ObligationReport {
                    obligation_id: Some(format!("row-{index}")),
                    description: "target selection fixture".into(),
                    kind: format!("kind-{index}"),
                    proof_level: trust_types::ProofLevel::L0Safety,
                    location: None,
                    outcome,
                    solver: format!("solver-{index}"),
                    time_ms: 0,
                    evidence: None,
                    proof_evidence: None,
                    transport_evidence: None,
                    assumes: Vec::new(),
                })
                .collect(),
        });
        report
    }

    #[test]
    fn runtime_only_function_remains_a_repair_target_without_proof_credit() {
        let report =
            target_selection_report(vec![ObligationOutcome::RuntimeChecked { note: None }]);
        let targets = repair_targets(&report);
        assert_eq!(targets.len(), 1);
        assert_eq!(targets[0].runtime_checked, 1);
        assert_eq!(targets[0].failed, 0);
        assert_eq!(targets[0].unknown, 0);
        assert_eq!(targets[0].outcome, "RUNTIME_CHECKED");
        assert_eq!(targets[0].vc_kind, "kind-0");
        let prompt = targets[0].repair_prompt(None);
        assert!(prompt.contains("RUNTIME_CHECKED"));
        assert!(!prompt.contains("Failed VC"));
        assert!(!prompt.contains("failed verification condition"));
        let frontier = TrustOnTrustFrontier {
            crates: vec![CrateFrontier::from_summary("fixture", &report.summary)],
        };
        let coverage =
            MeasurementCoverage { selected_crates: vec!["fixture".into()], failures: vec![] };
        let json: serde_json::Value =
            serde_json::from_str(&render_json(&frontier, &targets, None, &coverage, None)).unwrap();
        assert_eq!(json["repair_targets"][0]["runtime_checked"], 1);
        assert_eq!(json["total_runtime_checked"], 1);
        assert_eq!(json["total_proved"], 0);
        assert_eq!(json["total_unproved"], 0);
        assert_eq!(json["convergence_score"], 0.0);
        assert!(
            render_text(&frontier, &targets, None, &coverage, None).contains("runtime-checked 1")
        );
        let missing = render_text(&frontier, &[], None, &coverage, None);
        assert!(missing.contains("runtime checks still need static proofs"));
        assert!(!missing.contains("No repair targets — every obligation is proved"));
    }

    #[test]
    fn unresolved_rows_stay_ahead_of_runtime_rows_in_repair_targets() {
        for (outcome, expected) in [
            (ObligationOutcome::Unknown { reason: "unsupported".into() }, "UNKNOWN"),
            (ObligationOutcome::Timeout { timeout_ms: 1 }, "TIMEOUT"),
            (ObligationOutcome::failed_from_backend("ay", None), "FAILED"),
        ] {
            let report = target_selection_report(vec![
                ObligationOutcome::RuntimeChecked { note: None },
                outcome,
            ]);
            let targets = repair_targets(&report);
            assert_eq!(targets.len(), 1);
            assert_eq!(targets[0].runtime_checked, 1);
            assert_eq!(targets[0].outcome, expected);
            assert_eq!(targets[0].vc_kind, "kind-1");
        }
        let complete = target_selection_report(vec![ObligationOutcome::Proved {
            strength: trust_types::ProofStrength::deductive(),
        }]);
        assert!(repair_targets(&complete).is_empty());
        let design = target_selection_report(vec![ObligationOutcome::DesignRequirement {
            detail: "not a proof obligation".into(),
        }]);
        // Preserve the existing inconclusive fallback for design-only reports.
        assert_eq!(design.functions[0].summary.verdict, FunctionVerdict::Inconclusive);
        assert_eq!(repair_targets(&design)[0].outcome, "UNKNOWN");
    }

    #[test]
    fn unattributed_unresolved_rows_remain_targets_without_an_atomic_lead() {
        for failed in [false, true] {
            for runtime in [false, true] {
                let mut report = target_selection_report(if runtime {
                    vec![ObligationOutcome::RuntimeChecked { note: None }]
                } else {
                    vec![]
                });
                let summary = &mut report.functions[0].summary;
                if failed {
                    summary.unattributed_failed = 1;
                } else {
                    summary.unattributed_unknown = 1;
                }
                summary.verdict = FunctionVerdict::from_counts((&*summary).into());
                let targets = repair_targets(&report);
                assert_eq!(targets.len(), 1);
                assert_eq!(targets[0].failed, usize::from(failed));
                assert_eq!(targets[0].unknown, usize::from(!failed));
                assert_eq!(targets[0].runtime_checked, usize::from(runtime));
                assert_eq!(targets[0].outcome, "UNKNOWN");
                assert_eq!(targets[0].vc_kind, "unproved_obligation");
            }
        }
    }

    #[test]
    fn repair_prompt_is_intent_guided_when_intent_present() {
        let target = sample_target();
        let prompt = target.repair_prompt(Some("Overflow must be impossible by construction."));
        assert!(prompt.contains("vcgen::overflow_check"));
        assert!(prompt.contains("arithmetic_overflow"));
        assert!(prompt.contains("Author intent"));
        assert!(prompt.contains("Overflow must be impossible"));
        assert!(prompt.contains("Align the spec with the author's stated intent"));
    }

    #[test]
    fn repair_prompt_omits_intent_block_without_intent() {
        let target = sample_target();
        let prompt = target.repair_prompt(None);
        assert!(prompt.contains("vcgen::overflow_check"));
        assert!(!prompt.contains("Author intent"));
    }

    #[test]
    fn frontier_json_round_trips() {
        let mut frontier = TrustOnTrustFrontier::default();
        frontier.push(crate_frontier("a", 8, 10));
        frontier.push(crate_frontier("b", 3, 4));

        let dir = tempfile::tempdir().expect("frontier fixture");
        let path = dir.path().join("frontier.json");
        let coverage = MeasurementCoverage {
            selected_crates: vec!["a".to_string(), "b".to_string()],
            failures: Vec::new(),
        };
        write_frontier_json(&path, &frontier, &coverage).expect("write frontier");
        let loaded = load_frontier_json(&path).expect("load frontier");

        assert_eq!(loaded, frontier);
        let _ = fs::remove_file(&path);
    }

    #[test]
    fn missing_diagnostics_keep_the_existing_failure_fallback() {
        let reason = failed_measurement_reason(ExitCode::from(2), &Default::default());
        assert!(reason.contains("no live sealed compiler report"));
        assert!(!reason.contains("compiler/setup errors"));
    }

    #[test]
    fn diagnostic_errors_are_bounded_without_splitting_utf8_or_retaining_warnings() {
        use crate::pipeline::run::CompilerRunDiagnostics;
        use crate::report::CompilerDiagnostic;
        let mut diagnostics = CompilerRunDiagnostics::default();
        diagnostics.extend(&CompilerRunDiagnostics {
            errors: std::iter::once(CompilerDiagnostic {
                level: "warning".into(),
                message: "not a failure".into(),
            })
            .chain((0..20).map(|i| CompilerDiagnostic {
                level: "error".into(),
                message: format!("{i}:{}", "é".repeat(3000)),
            }))
            .collect(),
            truncated: false,
            artifact_failed: false,
        });
        assert_eq!(diagnostics.errors.len(), 8);
        assert!(diagnostics.truncated);
        assert!(diagnostics.errors.iter().all(|d| d.level == "error"
            && d.message.len() <= 2048
            && d.message.ends_with(" [truncated]")));
    }

    #[test]
    fn argument_setup_failure_reaches_diagnostics_without_a_live_report() {
        let mut diagnostics = crate::pipeline::run::CompilerRunDiagnostics::default();
        let mut observe =
            |batch: &crate::pipeline::run::CompilerRunDiagnostics| diagnostics.extend(batch);
        let exit = crate::run_subcommand_with_diagnostics(
            crate::types::Subcommand::Check,
            &["--solver".into(), "not-a-solver".into()],
            None,
            Some(&mut observe),
            false,
        );
        assert_eq!(exit, ExitCode::from(2));
        let reason = failed_measurement_reason(exit, &diagnostics);
        assert!(reason.contains("unknown solver `not-a-solver`"), "{reason}");
    }

    #[test]
    #[cfg(unix)]
    fn compiler_setup_diagnostic_reaches_incomplete_frontier_without_proof_credit() {
        use std::os::unix::fs::PermissionsExt;

        use crate::pipeline::run::{CompilerRun, CompilerRunDiagnostics, run_compiler};
        let root = tempfile::tempdir().unwrap();
        let compiler = root.path().join("trustc");
        std::fs::write(&compiler, "#!/bin/sh\nprintf '%s\\n' 'error: verified Targo refuses unaudited proc-macro dependencies [serde_derive, thiserror_impl]' >&2\nexit 101\n").unwrap();
        std::fs::set_permissions(&compiler, std::fs::Permissions::from_mode(0o755)).unwrap();
        let source = root.path().join("subject.rs");
        std::fs::write(&source, "fn main() {}\n").unwrap();
        let args = vec![compiler.display().to_string(), source.display().to_string()];
        let mut diagnostics = CompilerRunDiagnostics::default();
        let mut live_called = false;
        let exit = {
            let mut observe = |batch: &CompilerRunDiagnostics| diagnostics.extend(batch);
            let mut consume = |_report: &crate::report::LiveCanonicalReport| {
                live_called = true;
                Ok(())
            };
            run_compiler(CompilerRun {
                cmd_args: &args,
                rustc_path: &compiler,
                config: &crate::config::TrustConfig::default(),
                selected_codegen_backend: None,
                supports_json_transport: true,
                strict_artifact_policy: false,
                strict_result_gate: true,
                certify_gate: false,
                allow_l0_gaps: false,
                memory_safe_policy: false,
                survey: false,
                hardened: false,
                trust_profile: None,
                spec_emit_dir: None,
                dump_verifier_inputs: None,
                format: crate::types::OutputFormat::Json,
                report_dir: None,
                unsafe_memory_report: None,
                live_report_consumer: Some(&mut consume),
                diagnostic_observer: Some(&mut observe),
                render_output: false.into(),
                ephemeral_single_file_output: false,
                test_target_panics: crate::test_target_panics::TestTargetPanicPolicy::Strict,
                agent_delta: None,
            })
        };
        assert_ne!(exit, ExitCode::SUCCESS);
        assert!(!live_called, "diagnostics must not bypass live report admission");
        let reason = failed_measurement_reason(exit, &diagnostics);
        assert!(
            reason.contains("unaudited proc-macro dependencies [serde_derive, thiserror_impl]"),
            "{reason}"
        );
        let frontier = TrustOnTrustFrontier::default();
        let coverage = MeasurementCoverage {
            selected_crates: vec!["subject".into()],
            failures: vec![("subject".into(), reason)],
        };
        let value = frontier_json_value(&frontier, &coverage);
        assert_eq!(value["measurement_complete"], false);
        assert_eq!(value["measured_crates"], serde_json::json!([]));
        assert_eq!(value["total_proved"], 0);
        assert_eq!(value["total_runtime_checked"], 0);
        assert!(value["convergence_score"].is_null());
        assert!(
            value["measurement_failures"][0]["reason"].as_str().unwrap().contains("serde_derive")
        );
        assert!(render_text(&frontier, &[], None, &coverage, None).contains("thiserror_impl"));
        let path = root.path().join("frontier.json");
        write_frontier_json(&path, &frontier, &coverage).unwrap();
        assert!(load_frontier_json(&path).is_err());
    }

    #[test]
    fn an_unmeasured_selected_crate_cannot_improve_the_frontier() {
        let mut frontier = TrustOnTrustFrontier::default();
        frontier.push(crate_frontier("measured", 10, 10));
        let coverage = MeasurementCoverage {
            selected_crates: vec!["measured".to_string(), "missing".to_string()],
            failures: vec![("missing".to_string(), "no live compiler report".to_string())],
        };
        assert_eq!(coverage.exit_code(&frontier), 3);
        let value = frontier_json_value(&frontier, &coverage);
        assert_eq!(value["selected_crates"], serde_json::json!(["measured", "missing"]));
        assert_eq!(value["measured_crates"], serde_json::json!(["measured"]));
        assert_eq!(value["unmeasured_crates"], serde_json::json!(["missing"]));
        assert_eq!(value["measurement_complete"], false);
        assert!(value["convergence_score"].is_null());
        assert_eq!(value["measurement_failures"][0]["crate"], "missing");
        let text = render_text(&frontier, &[], None, &coverage, None);
        assert!(text.contains("measured crates: 1 / 2 selected"));
        assert!(text.contains("convergence: unavailable"));
        assert!(!text.contains("every obligation is proved"));
        let root = tempfile::tempdir().expect("frontier fixture");
        let path = root.path().join("partial.json");
        write_frontier_json(&path, &frontier, &coverage).expect("retain partial evidence");
        assert!(load_frontier_json(&path).is_err());
    }

    #[test]
    fn empty_and_zero_obligation_measurements_do_not_claim_convergence() {
        let empty = TrustOnTrustFrontier::default();
        let missing = MeasurementCoverage {
            selected_crates: vec!["missing".to_string()],
            failures: vec![("missing".to_string(), "admission refused".to_string())],
        };
        assert_eq!(missing.exit_code(&empty), 3);
        assert!(frontier_json_value(&empty, &missing)["convergence_score"].is_null());
        let mut measured = TrustOnTrustFrontier::default();
        measured.push(crate_frontier("empty", 0, 0));
        let complete = MeasurementCoverage {
            selected_crates: vec!["empty".to_string()],
            failures: Vec::new(),
        };
        assert_eq!(complete.exit_code(&measured), 0);
        assert!(frontier_json_value(&measured, &complete)["convergence_score"].is_null());
    }

    #[test]
    fn baseline_cannot_hide_selection_failure_missing_counts_or_duplicate_crates() {
        let mut frontier = TrustOnTrustFrontier::default();
        frontier.push(crate_frontier("a", 8, 10));
        let coverage =
            MeasurementCoverage { selected_crates: vec!["a".to_string()], failures: Vec::new() };
        let valid = frontier_json_value(&frontier, &coverage);
        let mut mutations = Vec::new();
        let mut legacy = valid.clone();
        legacy["schema"] = "trust.self-improve.frontier.v1".into();
        mutations.push(legacy);
        let mut partial = valid.clone();
        partial["measurement_complete"] = false.into();
        mutations.push(partial);
        let mut missing = valid.clone();
        missing["crates"][0].as_object_mut().unwrap().remove("unknown");
        mutations.push(missing);
        let mut negative = valid.clone();
        negative["crates"][0]["unknown"] = (-1).into();
        mutations.push(negative);
        let mut duplicate = valid.clone();
        duplicate["crates"].as_array_mut().unwrap().push(valid["crates"][0].clone());
        mutations.push(duplicate);
        let mut selected_twice = valid.clone();
        selected_twice["selected_crates"] = serde_json::json!(["a", "a"]);
        mutations.push(selected_twice);
        let mut omitted = valid.clone();
        omitted["selected_crates"] = serde_json::json!(["a", "unmeasured"]);
        mutations.push(omitted);
        let mut failed = valid.clone();
        failed["measurement_failures"] = serde_json::json!([{"crate":"a", "reason":"refused"}]);
        mutations.push(failed);
        let mut impossible = valid.clone();
        impossible["crates"][0]["proved"] = 11.into();
        mutations.push(impossible);
        let mut unmeasured = valid.clone();
        unmeasured["measured_crates"] = serde_json::json!([]);
        unmeasured["unmeasured_crates"] = serde_json::json!(["a"]);
        mutations.push(unmeasured);
        let mut repeated_measurement = valid.clone();
        repeated_measurement["measured_crates"] = serde_json::json!(["a", "a"]);
        mutations.push(repeated_measurement);
        let mut missing_inventory = valid.clone();
        missing_inventory.as_object_mut().unwrap().remove("unmeasured_crates");
        mutations.push(missing_inventory);
        for key in ["total_obligations", "total_proved", "total_runtime_checked", "total_unproved"]
        {
            let mut inconsistent = valid.clone();
            inconsistent[key] = 123.into();
            mutations.push(inconsistent);
            let mut missing = valid.clone();
            missing.as_object_mut().unwrap().remove(key);
            mutations.push(missing);
        }
        let mut wrong_score = valid.clone();
        wrong_score["convergence_score"] = 1.0.into();
        mutations.push(wrong_score);
        let root = tempfile::tempdir().expect("baseline fixture");
        let path = root.path().join("baseline.json");
        fs::write(&path, valid.to_string()).expect("valid baseline");
        assert_eq!(load_frontier_json(&path).expect("complete baseline"), frontier);
        for (index, mutation) in mutations.iter().enumerate() {
            fs::write(&path, mutation.to_string()).expect("write mutation");
            assert!(load_frontier_json(&path).is_err(), "mutation {index} admitted: {mutation}");
        }
    }

    #[test]
    fn crate_selection_refuses_duplicate_and_escaping_directory_names() {
        let root = tempfile::tempdir().expect("selection fixture");
        fs::create_dir(root.path().join("a")).expect("crate directory");
        fs::write(root.path().join("a/Cargo.toml"), "").expect("manifest");
        assert_eq!(select_crate_manifests(root.path(), &["a".to_string()]).unwrap().len(), 1);
        for names in [vec!["a", "a"], vec!["../a"], vec!["./a"], vec!["a/"]] {
            assert!(
                select_crate_manifests(
                    root.path(),
                    &names.iter().map(|name| name.to_string()).collect::<Vec<_>>()
                )
                .is_err(),
                "{names:?}"
            );
        }
    }

    #[test]
    fn partial_output_cannot_replace_an_existing_baseline() {
        let root = tempfile::tempdir().expect("frontier fixture");
        let path = root.path().join("baseline.json");
        let original = b"retained baseline bytes";
        fs::write(&path, original).expect("existing baseline");
        let frontier = TrustOnTrustFrontier::default();
        let coverage = MeasurementCoverage {
            selected_crates: vec!["missing".to_string()],
            failures: vec![("missing".to_string(), "admission refused".to_string())],
        };
        assert!(write_frontier_json(&path, &frontier, &coverage).is_err());
        assert_eq!(fs::read(&path).expect("preserved baseline"), original);
    }

    #[test]
    fn no_function_targets_cannot_hide_crate_residuals_or_other_outcomes() {
        let coverage =
            MeasurementCoverage { selected_crates: vec!["a".to_string()], failures: Vec::new() };
        let mut frontier = TrustOnTrustFrontier::default();
        frontier.push(crate_frontier("a", 0, 1));
        let residual = render_text(&frontier, &[], None, &coverage, None);
        assert!(residual.contains("unresolved crate-level results remain"));
        assert!(!residual.contains("every obligation is proved"));
        // A design requirement is an obligation without a proof/runtime
        // outcome. It is not a function repair target or a proved obligation.
        frontier.crates[0].failed = 0;
        let design = render_text(&frontier, &[], None, &coverage, None);
        assert!(design.contains("remaining obligations are not proved or runtime-checked"));
        assert!(!design.contains("every obligation is proved"));
        // The fully accounted positive control retains its useful message.
        frontier.crates[0].proved = 1;
        assert!(
            render_text(&frontier, &[], None, &coverage, None)
                .contains("every obligation is proved")
        );
    }

    #[test]
    fn frontier_json_rejects_oversized_input_before_deserialization() {
        let root = tempfile::tempdir().expect("frontier fixture");
        let path = root.path().join("frontier.json");
        let file = fs::File::create(&path).expect("create sparse frontier");
        file.set_len(crate::input_limits::MAX_SAVED_PROOF_REPORT_BYTES as u64 + 1)
            .expect("oversize frontier");
        let error = load_frontier_json(&path).expect_err("oversized frontier must fail closed");
        assert!(error.contains("safety limit"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn frontier_json_rejects_leaf_symlink() {
        use std::os::unix::fs::symlink;

        let root = tempfile::tempdir().expect("frontier fixture");
        let target = root.path().join("target.json");
        let linked = root.path().join("frontier.json");
        fs::write(&target, "{\"crates\":[]}").expect("write target");
        symlink(&target, &linked).expect("link frontier");
        let error = load_frontier_json(&linked).expect_err("symlink frontier must fail closed");
        assert!(error.contains("not a regular file"), "{error}");
    }
}
