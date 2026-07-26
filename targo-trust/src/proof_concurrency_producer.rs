use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Duration;
use std::time::{SystemTime, UNIX_EPOCH};
use std::{env, fs};

use serde::Serialize;

use crate::controlled_git;

const REPORT_SCHEMA: &str = "trust.proof-concurrency.producer-audit.v1";
const DEFAULT_ARTIFACT_DIR: &str = "reports/proof/concurrency-artifacts";
const EXPECTED_SOLVER: &str = "trust-concurrency-prover-release-v1";
const MATERIALIZER_COMMAND: &str = "targo trust proof-concurrency --materialize-input-manifest --solver trust-concurrency-prover-release-v1";
const REPORT_COMMAND: &str =
    "not implemented: Trust-owned authenticated concurrency validation/replay report producer";
const MAX_GIT_STREAM_BYTES: usize = 64 * 1024 * 1024;
const GIT_TIMEOUT: Duration = Duration::from_secs(120);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OutputFormat {
    Terminal,
    Json,
}

#[derive(Debug)]
struct Args {
    format: OutputFormat,
    repo_root: Option<PathBuf>,
    artifact_dir: Option<PathBuf>,
}

#[derive(Debug, Serialize)]
struct ProducerAuditReport {
    schema: &'static str,
    generated_at: String,
    status: &'static str,
    repo: RepoReport,
    producer: MissingProducerReport,
    artifact_dir: String,
    required_artifacts: Vec<RequiredArtifactReport>,
    audited_modules: Vec<AuditedModuleReport>,
    next_required_interface: NextRequiredInterfaceReport,
}

#[derive(Debug, Serialize)]
struct RepoReport {
    root: String,
    head: String,
    dirty: bool,
}

#[derive(Debug, Serialize)]
struct MissingProducerReport {
    expected_solver: &'static str,
    expected_command: &'static str,
    implemented: bool,
    blocker_code: &'static str,
    blocker: &'static str,
}

#[derive(Debug, Serialize)]
struct RequiredArtifactReport {
    id: &'static str,
    kind: &'static str,
    files: Vec<ArtifactFileReport>,
}

#[derive(Debug, Serialize)]
struct ArtifactFileReport {
    role: &'static str,
    path: String,
    status: &'static str,
}

#[derive(Debug, Clone, Copy, Serialize)]
struct AuditedModuleReport {
    path: &'static str,
    finding: &'static str,
}

#[derive(Debug, Serialize)]
struct NextRequiredInterfaceReport {
    producer_command: &'static str,
    materializer_command: &'static str,
    report_command: &'static str,
    required_output_contract: &'static str,
}

#[derive(Debug, Clone, Copy)]
struct RequiredObligation {
    id: &'static str,
    kind: &'static str,
}

const REQUIRED_OBLIGATIONS: &[RequiredObligation] = &[
    RequiredObligation { id: "race_free_arc_mutex", kind: "data_race_free" },
    RequiredObligation { id: "atomic_release_acquire", kind: "atomic_ordering" },
    RequiredObligation { id: "channel_happens_before", kind: "happens_before" },
];

const ARTIFACT_ROLES: &[(&str, &str)] = &[
    ("source", "source.rs"),
    ("proof", "proof"),
    ("certificate", "cert"),
    ("dispatch", "dispatch"),
];

const AUDITED_MODULES: &[AuditedModuleReport] = &[
    AuditedModuleReport {
        path: "targo-trust/src/proof_concurrency.rs",
        finding: "non-proof artifact auditing and manifest materialization only; no validator, replay engine, or proof-report generator",
    },
    AuditedModuleReport {
        path: "crates/trust-types/src/concurrency.rs",
        finding: "concurrency model and TLA rendering types; no release source/proof/cert/dispatch writer",
    },
    AuditedModuleReport {
        path: "crates/trust-integration-tests/tests/concurrency_e2e.rs",
        finding: "test-only data-race, ordering, and happens-before scenarios; no release producer",
    },
    AuditedModuleReport {
        path: "crates/trust-proof-cert/src/generate.rs",
        finding: "generic certificate generation for proved VCs; not wired to concurrency release artifacts",
    },
    AuditedModuleReport {
        path: "crates/trust-certify/src/lib.rs",
        finding: "CleanCic certification for supported formula fragments; no concurrency release bundle driver",
    },
];

pub(crate) fn run_subcommand(args: &[String]) -> ExitCode {
    match parse_args(args) {
        Ok(ParseResult::Help) => {
            print_usage();
            ExitCode::SUCCESS
        }
        Ok(ParseResult::Run(args)) => run(args),
        Err(error) => {
            eprintln!("targo trust proof-concurrency-producer: {error}");
            eprintln!("Run `targo trust proof-concurrency-producer --help` for usage.");
            ExitCode::from(2)
        }
    }
}

fn run(args: Args) -> ExitCode {
    let report = match build_report(&args) {
        Ok(report) => report,
        Err(error) => {
            eprintln!("targo trust proof-concurrency-producer: {error}");
            return ExitCode::from(2);
        }
    };

    match args.format {
        OutputFormat::Json => match serde_json::to_string_pretty(&report) {
            Ok(json) => println!("{json}"),
            Err(error) => {
                eprintln!(
                    "targo trust proof-concurrency-producer: failed to serialize JSON: {error}"
                );
                return ExitCode::from(1);
            }
        },
        OutputFormat::Terminal => {
            println!(
                "proof-concurrency-producer: schema={} status={} missing_producer={} artifact_dir={}",
                report.schema, report.status, report.producer.expected_solver, report.artifact_dir
            );
            println!("next: {}", report.next_required_interface.producer_command);
        }
    }

    ExitCode::from(2)
}

#[derive(Debug)]
enum ParseResult {
    Help,
    Run(Args),
}

fn parse_args(args: &[String]) -> Result<ParseResult, String> {
    let mut parsed = Args { format: OutputFormat::Terminal, repo_root: None, artifact_dir: None };
    let mut audit_seen = false;
    let mut i = 0;

    while i < args.len() {
        let arg = args[i].as_str();
        match arg {
            "--help" | "-h" => return Ok(ParseResult::Help),
            "audit" => {
                if audit_seen {
                    return Err("`audit` may be specified only once".to_string());
                }
                audit_seen = true;
                i += 1;
            }
            "produce-release-artifacts" => {
                return Err("`produce-release-artifacts` was removed: no Trust-owned concurrency \
                     producer exists yet, so accepting the mode falsely implied artifacts \
                     could be created; use `audit` to inspect the explicit blocker"
                    .to_string());
            }
            "--format" => {
                let value = args.get(i + 1).ok_or("--format requires json or terminal")?;
                parsed.format = parse_format(value)?;
                i += 2;
            }
            value if value.starts_with("--format=") => {
                let value = value.strip_prefix("--format=").expect("prefix checked");
                parsed.format = parse_format(value)?;
                i += 1;
            }
            "--json" => {
                parsed.format = OutputFormat::Json;
                i += 1;
            }
            "--repo-root" => {
                let value = args.get(i + 1).ok_or("--repo-root requires a path")?;
                if value.trim().is_empty() {
                    return Err("--repo-root requires a path".to_string());
                }
                parsed.repo_root = Some(PathBuf::from(value));
                i += 2;
            }
            value if value.starts_with("--repo-root=") => {
                let value = value.strip_prefix("--repo-root=").expect("prefix checked");
                if value.trim().is_empty() {
                    return Err("--repo-root requires a path".to_string());
                }
                parsed.repo_root = Some(PathBuf::from(value));
                i += 1;
            }
            "--artifact-dir" => {
                let value = args.get(i + 1).ok_or("--artifact-dir requires a path")?;
                if value.trim().is_empty() {
                    return Err("--artifact-dir requires a path".to_string());
                }
                parsed.artifact_dir = Some(PathBuf::from(value));
                i += 2;
            }
            value if value.starts_with("--artifact-dir=") => {
                let value = value.strip_prefix("--artifact-dir=").expect("prefix checked");
                if value.trim().is_empty() {
                    return Err("--artifact-dir requires a path".to_string());
                }
                parsed.artifact_dir = Some(PathBuf::from(value));
                i += 1;
            }
            other => return Err(format!("unknown argument `{other}`")),
        }
    }

    Ok(ParseResult::Run(parsed))
}

fn parse_format(value: &str) -> Result<OutputFormat, String> {
    match value {
        "json" => Ok(OutputFormat::Json),
        "terminal" => Ok(OutputFormat::Terminal),
        other => Err(format!("unsupported --format `{other}`; expected json or terminal")),
    }
}

fn print_usage() {
    println!(
        "\
Usage:
  targo trust proof-concurrency-producer audit [--format json] [--repo-root <path>] [--artifact-dir <path>]

Audit the Trust-owned producer path for release concurrency proof artifacts.

This command is fail-closed until a real Trust-owned producer implements
trust-concurrency-prover-release-v1. It never creates source/proof/cert/dispatch
artifacts by fixture or manual pass.

Options:
  --format json        Emit trust.proof-concurrency.producer-audit.v1 JSON
  --json               Alias for --format json
  --repo-root <path>   Repository root to inspect
  --artifact-dir <dir> Required artifact output directory
                       (default: reports/proof/concurrency-artifacts)
  --help               Show this help
"
    );
}

fn build_report(args: &Args) -> Result<ProducerAuditReport, String> {
    let repo_root = resolve_repo_root(args.repo_root.as_deref())?;
    let artifact_dir = repo_contained_path(
        &repo_root,
        args.artifact_dir.as_deref().unwrap_or_else(|| Path::new(DEFAULT_ARTIFACT_DIR)),
    )?;
    let head = controlled_git::canonical_head(
        &repo_root,
        "proof-concurrency producer HEAD probe",
        MAX_GIT_STREAM_BYTES,
        GIT_TIMEOUT,
    )?;
    let dirty = !controlled_git::exact_status_porcelain_v1(
        &repo_root,
        "proof-concurrency producer cleanliness probe",
        MAX_GIT_STREAM_BYTES,
        GIT_TIMEOUT,
    )?
    .is_empty();
    let repo = RepoReport { root: repo_root.display().to_string(), head, dirty };

    Ok(ProducerAuditReport {
        schema: REPORT_SCHEMA,
        generated_at: generated_at(),
        status: "blocked",
        repo,
        producer: MissingProducerReport {
            expected_solver: EXPECTED_SOLVER,
            expected_command: "targo trust proof-concurrency-producer audit",
            implemented: false,
            blocker_code: "missing_trust_concurrency_release_producer",
            blocker: "No Trust-owned release producer currently generates the required concurrency source/proof/certificate/dispatch artifact quartet.",
        },
        artifact_dir: display_repo_path(&repo_root, &artifact_dir),
        required_artifacts: required_artifacts(&repo_root, &artifact_dir),
        audited_modules: AUDITED_MODULES.to_vec(),
        next_required_interface: NextRequiredInterfaceReport {
            producer_command: "not implemented: trust-concurrency-prover-release-v1",
            materializer_command: MATERIALIZER_COMMAND,
            report_command: REPORT_COMMAND,
            required_output_contract: "For each obligation, a future producer must emit authenticated validator inputs plus independently replayable validation records. Presence-only source/proof/certificate/dispatch files remain non-proof and can only feed trust.proof-concurrency.artifact-audit.v1.",
        },
    })
}

fn required_artifacts(repo_root: &Path, artifact_dir: &Path) -> Vec<RequiredArtifactReport> {
    REQUIRED_OBLIGATIONS
        .iter()
        .map(|obligation| {
            let files = ARTIFACT_ROLES
                .iter()
                .map(|(role, suffix)| {
                    let path = artifact_dir.join(format!("{}.{}", obligation.id, suffix));
                    ArtifactFileReport {
                        role: *role,
                        path: display_repo_path(repo_root, &path),
                        status: artifact_status(&path),
                    }
                })
                .collect();
            RequiredArtifactReport { id: obligation.id, kind: obligation.kind, files }
        })
        .collect()
}

fn artifact_status(path: &Path) -> &'static str {
    match fs::symlink_metadata(path) {
        Ok(metadata) if metadata.file_type().is_symlink() => "rejected_symlink",
        Ok(metadata) if metadata.is_file() && metadata.len() > 0 => "present_unvalidated",
        Ok(metadata) if metadata.is_file() => "empty_file",
        Ok(_) => "not_regular_file",
        Err(_) => "missing",
    }
}

fn repo_contained_path(repo_root: &Path, path: &Path) -> Result<PathBuf, String> {
    let path = if path.is_absolute() { path.to_path_buf() } else { repo_root.join(path) };
    if !path.starts_with(repo_root)
        || path.strip_prefix(repo_root).ok().is_none_or(|relative| {
            relative.as_os_str().is_empty()
                || !relative
                    .components()
                    .all(|component| matches!(component, std::path::Component::Normal(_)))
        })
    {
        return Err(format!(
            "artifact directory {} must be a canonical path contained by repository root {}",
            path.display(),
            repo_root.display()
        ));
    }
    Ok(path)
}

fn display_repo_path(repo_root: &Path, path: &Path) -> String {
    path.strip_prefix(repo_root).unwrap_or(path).display().to_string()
}

fn resolve_repo_root(repo_root: Option<&Path>) -> Result<PathBuf, String> {
    let requested = if let Some(path) = repo_root {
        if path.is_absolute() {
            path.to_path_buf()
        } else {
            env::current_dir().map_err(|error| error.to_string())?.join(path)
        }
    } else {
        env::current_dir().map_err(|error| error.to_string())?
    };
    let requested = requested.canonicalize().map_err(|error| {
        format!("failed to resolve repository path {}: {error}", requested.display())
    })?;
    let discovered = controlled_git::resolve_repo_root(&requested)?;
    if repo_root.is_some() && requested != discovered {
        return Err(format!(
            "--repo-root must name the repository top level exactly; {} resolves inside {}",
            requested.display(),
            discovered.display()
        ));
    }
    Ok(discovered)
}

fn generated_at() -> String {
    let seconds = SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_secs();
    format!("unix-seconds:{seconds}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_audit_json_repo_root_and_artifact_dir() {
        let args = vec![
            "audit".to_string(),
            "--json".to_string(),
            "--repo-root=.".to_string(),
            "--artifact-dir".to_string(),
            "out/concurrency".to_string(),
        ];

        let ParseResult::Run(parsed) = parse_args(&args).expect("args should parse") else {
            panic!("expected run args");
        };

        assert_eq!(parsed.format, OutputFormat::Json);
        assert_eq!(parsed.repo_root.as_deref(), Some(Path::new(".")));
        assert_eq!(parsed.artifact_dir.as_deref(), Some(Path::new("out/concurrency")));
    }

    #[test]
    fn rejects_removed_fake_producer_mode() {
        let error = parse_args(&["produce-release-artifacts".to_string()])
            .expect_err("a mode that never produced artifacts must not parse");
        assert!(error.contains("was removed"));
        assert!(error.contains("use `audit`"));
    }
}
