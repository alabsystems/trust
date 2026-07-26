// targo trust self-improve — the Trust-on-Trust improvement loop (Slice 1).
//
// Closes the self-hosting loop described in docs/trust-refinement-compiler.tex:
// verify Trust's own crates to capture the proof frontier, surface repair
// targets as proposals (nothing is applied), and — when a prior frontier is
// supplied as a baseline — measure the frontier delta across runs. The
// north-star metric is the Trust-on-Trust convergence score (proved /
// obligations), which should improve monotonically across releases.
//
// This slice is read-only and proposal-only. AI-in-the-loop repair
// (trust-backprop) and intent input (design-doc / chat) land in later slices;
// the refinement floor remains the recoverable baseline throughout.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#[cfg(test)]
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use trust_backprop::{RepairPromptContext, build_ai_repair_command, build_ai_repair_prompt};
use trust_types::{CrateSummary, FunctionVerdict, JsonProofReport, ObligationOutcome};

use crate::intent::{ResolvedIntent, resolve_intent};
use crate::script_cli::resolve_repo_file;

const USAGE: &str = "\
Usage: targo trust self-improve [options]

Run the Trust-on-Trust improvement loop over Trust's own crates: verify each
crate, aggregate the proof frontier, and surface repair targets as proposals.
Nothing is applied — this slice is read-only and proposal-only.

Options:
  --crate NAME         Restrict to the named crate (repeatable). Default: all
                       crates under `crates/`.
  --baseline PATH      Compare against a frontier JSON written by a prior run
                       (--out) and report the convergence delta.
  --out PATH           Write the resulting frontier as JSON (use as the next
                       run's --baseline to track the proof frontier over time).
  --intent PATH        Design doc / chat that guides repair (authority: below a
                       formal contract, above code-abduced guesses). When set,
                       each repair target gets an intent-guided AI repair prompt.
  --json               Emit the consolidated frontier report as JSON.
  -h, --help           Show this help.

Examples:
  targo trust self-improve --crate trust-vcgen --crate trust-router
  targo trust self-improve --out target/trust-frontier.json
  targo trust self-improve --baseline target/trust-frontier.json
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

/// A single function carrying unproved obligations — a proposal target. We do
/// not generate or apply rewrites here; we only name where repair would aim and
/// (when an intent document is supplied) render the intent-guided repair prompt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RepairTarget {
    pub(crate) crate_name: String,
    pub(crate) function: String,
    pub(crate) failed: usize,
    pub(crate) unknown: usize,
    /// VC kind of the lead unproved obligation (e.g. `arithmetic_overflow`).
    pub(crate) vc_kind: String,
    /// Solver that produced the lead unproved result.
    pub(crate) solver: String,
    /// Outcome label of the lead unproved obligation (`FAILED` / `UNKNOWN`).
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

    /// proved / obligations, in [0, 1]. An empty frontier scores 1.0 (nothing
    /// left to prove), matching the fixed-point definition in the design note.
    fn convergence_score(&self) -> f64 {
        let obligations = self.total_obligations();
        if obligations == 0 {
            return 1.0;
        }
        self.total_proved() as f64 / obligations as f64
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

/// Collect the functions in a report that still carry unproved obligations.
fn repair_targets(report: &JsonProofReport) -> Vec<RepairTarget> {
    report
        .functions
        .iter()
        .filter(|function| {
            matches!(
                function.summary.verdict,
                FunctionVerdict::HasViolations | FunctionVerdict::Inconclusive
            ) || function.summary.failed + function.summary.unknown > 0
        })
        .map(|function| {
            let lead = function.obligations.iter().find(|obligation| {
                matches!(
                    obligation.outcome,
                    ObligationOutcome::Failed { .. }
                        | ObligationOutcome::Unknown { .. }
                        | ObligationOutcome::Timeout { .. }
                )
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
    out: Option<PathBuf>,
    intent: Option<String>,
    json: bool,
}

fn parse_options(args: &[String]) -> Result<Option<Options>, String> {
    let mut options =
        Options { crates: Vec::new(), baseline: None, out: None, intent: None, json: false };
    let mut index = 0;
    while index < args.len() {
        match args[index].as_str() {
            "-h" | "--help" => return Ok(None),
            "--json" => {
                options.json = true;
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
            other => return Err(format!("unknown option `{other}`")),
        }
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

    let intent = match resolve_intent(options.intent.as_deref(), None, None) {
        Ok(intent) => intent,
        Err(message) => {
            eprintln!("targo trust self-improve: {message}");
            return ExitCode::from(2);
        }
    };

    let Some((repo_root, _)) = resolve_repo_file("crates/Cargo.toml") else {
        eprintln!(
            "targo trust self-improve: could not locate the Trust crates workspace (crates/Cargo.toml)"
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
    let mut failures: Vec<String> = Vec::new();

    for (crate_name, manifest) in &manifests {
        match verify_crate(crate_name, manifest) {
            Ok(measurement) => {
                frontier.push(measurement.frontier);
                targets.extend(measurement.targets);
            }
            Err(message) => failures.push(format!("{crate_name}: {message}")),
        }
    }

    let baseline = match options.baseline.as_deref().map(load_frontier_json) {
        Some(Ok(baseline)) => Some(baseline),
        Some(Err(message)) => {
            eprintln!("targo trust self-improve: failed to read baseline: {message}");
            return ExitCode::from(2);
        }
        None => None,
    };
    let delta = baseline.as_ref().map(|b| FrontierDelta::between(b, &frontier));

    if let Some(out) = options.out.as_deref() {
        if let Err(message) = write_frontier_json(out, &frontier) {
            eprintln!("targo trust self-improve: failed to write --out: {message}");
            return ExitCode::from(1);
        }
    }

    if options.json {
        print!("{}", render_json(&frontier, &targets, delta.as_ref(), intent.as_ref()));
    } else {
        print!("{}", render_text(&frontier, &targets, delta.as_ref(), &failures, intent.as_ref()));
    }

    // When an intent document is supplied, render an intent-guided AI repair
    // prompt per target. These are proposals only — nothing is applied.
    if let Some(intent) = intent.as_ref() {
        let excerpt = intent.excerpt(2000);
        print_repair_prompts(&targets, &excerpt);
    }

    if !failures.is_empty() && frontier.crates.is_empty() {
        // Every crate failed to verify — nothing was measured.
        return ExitCode::from(1);
    }
    ExitCode::SUCCESS
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
        for name in requested {
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
    for entry in entries.flatten() {
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

struct CrateMeasurement {
    frontier: CrateFrontier,
    targets: Vec<RepairTarget>,
}

/// Verify one crate in this process and reduce the canonical report while its
/// opaque publication capability is still live. Retaining or reloading a JSON
/// DTO would discard that authority and turn every genuine proof into Unknown.
fn verify_crate(crate_name: &str, manifest: &Path) -> Result<CrateMeasurement, String> {
    let args = vec!["--manifest-path".to_string(), manifest.display().to_string()];
    let mut measurement = None;
    let mut consume = |live: &crate::report::LiveCanonicalReport| {
        let report = live.for_self_improve_reduction();
        measurement = Some(CrateMeasurement {
            frontier: CrateFrontier::from_summary(crate_name, &report.summary),
            targets: repair_targets(report),
        });
        Ok(())
    };
    let exit = crate::run_subcommand_with_live_report(
        crate::types::Subcommand::Check,
        &args,
        Some(&mut consume),
        false,
    );
    drop(consume);
    measurement.ok_or_else(|| {
        format!("in-process check produced no live sealed compiler report (exit {exit:?})")
    })
}

fn load_frontier_json(path: &Path) -> Result<TrustOnTrustFrontier, String> {
    let bytes = crate::input_limits::read_bounded_file(
        path,
        crate::input_limits::MAX_SAVED_PROOF_REPORT_BYTES,
    )
    .map_err(|error| format!("reading {}: {error}", path.display()))?;
    let value: serde_json::Value = serde_json::from_slice(&bytes)
        .map_err(|error| format!("parsing {}: {error}", path.display()))?;
    let crates = value
        .get("crates")
        .and_then(|c| c.as_array())
        .ok_or_else(|| format!("{}: missing `crates` array", path.display()))?;
    let mut frontier = TrustOnTrustFrontier::default();
    for entry in crates {
        frontier.push(CrateFrontier {
            crate_name: json_str(entry, "crate"),
            obligations: json_usize(entry, "obligations"),
            proved: json_usize(entry, "proved"),
            runtime_checked: json_usize(entry, "runtime_checked"),
            failed: json_usize(entry, "failed"),
            unknown: json_usize(entry, "unknown"),
        });
    }
    Ok(frontier)
}

fn json_str(value: &serde_json::Value, key: &str) -> String {
    value.get(key).and_then(|v| v.as_str()).unwrap_or_default().to_string()
}

fn json_usize(value: &serde_json::Value, key: &str) -> usize {
    value.get(key).and_then(|v| v.as_u64()).unwrap_or_default() as usize
}

fn write_frontier_json(path: &Path, frontier: &TrustOnTrustFrontier) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent)
                .map_err(|error| format!("creating {}: {error}", parent.display()))?;
        }
    }
    fs::write(path, frontier_json_value(frontier).to_string())
        .map_err(|error| format!("writing {}: {error}", path.display()))
}

fn frontier_json_value(frontier: &TrustOnTrustFrontier) -> serde_json::Value {
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
        "schema": "trust.self-improve.frontier.v1",
        "convergence_score": frontier.convergence_score(),
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
    intent: Option<&ResolvedIntent>,
) -> String {
    let mut value = frontier_json_value(frontier);
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
    failures: &[String],
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
        "  convergence: {:.4}  (proved {} / obligations {})\n",
        frontier.convergence_score(),
        frontier.total_proved(),
        frontier.total_obligations(),
    ));
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
        out.push_str("\nNo repair targets — every obligation is proved or runtime-checked.\n");
    } else {
        out.push_str(&format!(
            "\nRepair targets (proposal-only, nothing applied) — {} function(s):\n",
            targets.len(),
        ));
        for t in targets {
            out.push_str(&format!(
                "  {}::{}  ({}, failed {}, unknown {})\n",
                t.crate_name, t.function, t.vc_kind, t.failed, t.unknown,
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

    if !failures.is_empty() {
        out.push_str(&format!("\n{} crate(s) could not be verified:\n", failures.len()));
        for failure in failures {
            out.push_str(&format!("  {failure}\n"));
        }
        out.push_str("  (A built stage-2 trustc is required to run the loop end to end.)\n");
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;

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
            vc_kind: "arithmetic_overflow".to_string(),
            solver: "trust-wp".to_string(),
            outcome: "FAILED".to_string(),
            source_file: Some("crates/trust-vcgen/src/lib.rs".to_string()),
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

        let dir = env::temp_dir().join("trust-self-improve-test-roundtrip");
        fs::create_dir_all(&dir).expect("create temp dir");
        let path = dir.join("frontier.json");
        write_frontier_json(&path, &frontier).expect("write frontier");
        let loaded = load_frontier_json(&path).expect("load frontier");

        assert_eq!(loaded, frontier);
        let _ = fs::remove_file(&path);
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
