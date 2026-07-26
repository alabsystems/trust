use std::env;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use crate::source_analysis::{self, SourceAnalysisOptions, StandaloneOutcome};

mod claims;
mod evaluate;
mod report;
mod terminal;
mod validate;
mod validate_additional;
mod walkthrough;

use evaluate::{evaluate_claims, is_hardened_kind};
use report::{LabReport, LabSummary, SCHEMA_VERSION};
use terminal::{display_path, print_terminal_report, print_usage};
use walkthrough::run_walkthroughs;

#[cfg(test)]
mod tests;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OutputFormat {
    Terminal,
    Json,
}

#[derive(Debug)]
struct LabArgs {
    manifest_path: Option<PathBuf>,
    format: OutputFormat,
    show_vcs: bool,
}

pub(crate) fn run_hardened_lab_subcommand(args: &[String]) -> ExitCode {
    let args = match parse_args(args) {
        Ok(Some(args)) => args,
        Ok(None) => {
            print_usage();
            return ExitCode::SUCCESS;
        }
        Err(error) => {
            eprintln!("{error}");
            eprintln!();
            print_usage();
            return ExitCode::from(2);
        }
    };

    let manifest_path = match resolve_manifest_path(args.manifest_path.as_deref()) {
        Ok(path) => path,
        Err(error) => {
            eprintln!("{error}");
            return ExitCode::from(2);
        }
    };

    let summary = source_analysis::analyze_crate_with_options(
        &manifest_path,
        SourceAnalysisOptions { hardened: true },
    );
    if summary.files_analyzed == 0 {
        eprintln!(
            "targo trust hardened-lab: no Rust sources were discovered from {}",
            manifest_path.display()
        );
        return ExitCode::from(2);
    }

    let walkthroughs = match run_walkthroughs(&manifest_path) {
        Ok(walkthroughs) => walkthroughs,
        Err(error) => {
            eprintln!("{error}");
            return ExitCode::from(2);
        }
    };
    let walkthroughs_passed =
        !walkthroughs.is_empty() && walkthroughs.iter().all(|walkthrough| walkthrough.success);
    let claims = evaluate_claims(&summary.vcs, &walkthroughs);
    let claims_passed = claims.iter().all(|claim| claim.passed);

    let lab_summary = LabSummary {
        files_analyzed: summary.files_analyzed,
        functions_found: summary.functions_found,
        total_vcs: summary.total_audit_rows,
        failed: summary.failed,
        hardened_vcs: summary
            .vcs
            .iter()
            .filter(|vc| vc.outcome == StandaloneOutcome::Failed && is_hardened_kind(vc.kind))
            .count(),
        claims_total: claims.len(),
        claims_passed: claims.iter().filter(|claim| claim.passed).count(),
        claims_failed: claims.iter().filter(|claim| !claim.passed).count(),
        walkthroughs_total: walkthroughs.len(),
        walkthroughs_passed: walkthroughs.iter().filter(|walkthrough| walkthrough.success).count(),
        walkthroughs_failed: walkthroughs.iter().filter(|walkthrough| !walkthrough.success).count(),
    };

    let report = LabReport {
        schema_version: SCHEMA_VERSION,
        analyzer: "targo-trust source_analysis hardened mode",
        manifest_path: display_path(&manifest_path),
        raw_analyzer_command: format!(
            "targo trust check --standalone --hardened --format json --manifest-path {}",
            manifest_path.display()
        ),
        summary: lab_summary,
        claims_passed,
        claims,
        walkthroughs_passed,
        walkthroughs,
        vcs: args.show_vcs.then(|| summary.vcs.clone()),
    };

    match args.format {
        OutputFormat::Json => {
            if let Err(error) = serde_json::to_writer_pretty(std::io::stdout(), &report) {
                eprintln!("targo trust hardened-lab: failed to write JSON: {error}");
                return ExitCode::from(2);
            }
            println!();
        }
        OutputFormat::Terminal => print_terminal_report(&report),
    }

    if claims_passed && walkthroughs_passed { ExitCode::SUCCESS } else { ExitCode::from(1) }
}

fn parse_args(args: &[String]) -> Result<Option<LabArgs>, String> {
    let mut parsed =
        LabArgs { manifest_path: None, format: OutputFormat::Terminal, show_vcs: false };

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--help" | "-h" => return Ok(None),
            "--json" => parsed.format = OutputFormat::Json,
            "--show-vcs" => parsed.show_vcs = true,
            "--manifest-path" => {
                i += 1;
                let value = args.get(i).ok_or_else(|| {
                    "targo trust hardened-lab: --manifest-path requires a value".to_string()
                })?;
                parsed.manifest_path = Some(PathBuf::from(value));
            }
            "--format" => {
                i += 1;
                let value = args.get(i).ok_or_else(|| {
                    "targo trust hardened-lab: --format requires a value".to_string()
                })?;
                parsed.format = parse_format(value)?;
            }
            value if value.starts_with("--manifest-path=") => {
                let value = value.strip_prefix("--manifest-path=").expect("prefix checked");
                parsed.manifest_path = Some(PathBuf::from(value));
            }
            value if value.starts_with("--format=") => {
                let value = value.strip_prefix("--format=").expect("prefix checked");
                parsed.format = parse_format(value)?;
            }
            other => {
                return Err(format!("targo trust hardened-lab: unknown argument `{other}`"));
            }
        }
        i += 1;
    }

    Ok(Some(parsed))
}

fn parse_format(value: &str) -> Result<OutputFormat, String> {
    match value {
        "terminal" | "text" => Ok(OutputFormat::Terminal),
        "json" => Ok(OutputFormat::Json),
        other => Err(format!(
            "targo trust hardened-lab: unsupported --format `{other}`; expected terminal or json"
        )),
    }
}

fn resolve_manifest_path(explicit: Option<&Path>) -> Result<PathBuf, String> {
    let manifest_path = if let Some(path) = explicit {
        path.to_path_buf()
    } else {
        default_hardened_manifest().ok_or_else(|| {
            "targo trust hardened-lab: could not find examples/hardened/Cargo.toml; pass --manifest-path".to_string()
        })?
    };

    if !manifest_path.is_file() {
        return Err(format!(
            "targo trust hardened-lab: manifest not found: {}",
            manifest_path.display()
        ));
    }

    std::fs::canonicalize(&manifest_path).map_err(|error| {
        format!(
            "targo trust hardened-lab: could not canonicalize {}: {error}",
            manifest_path.display()
        )
    })
}

fn default_hardened_manifest() -> Option<PathBuf> {
    if let Ok(cwd) = env::current_dir() {
        for ancestor in cwd.ancestors() {
            let candidate = ancestor.join("examples/hardened/Cargo.toml");
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }

    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let candidate = manifest_dir.join("../examples/hardened/Cargo.toml");
    candidate.is_file().then_some(candidate)
}
