use std::collections::BTreeSet;
use std::path::{Component, Path, PathBuf};
use std::process::ExitCode;
use std::time::Duration;
use std::time::{SystemTime, UNIX_EPOCH};
use std::{env, fs};

use serde::{Deserialize, Serialize};

use crate::controlled_git;
use crate::durable_io;
use crate::input_limits::{MAX_RELEASE_METADATA_BYTES, read_bounded_file};

/// This command currently has no Trust-owned concurrency validator.  Its two
/// report modes are therefore deliberately outside the proof-report namespace.
const ARTIFACT_AUDIT_SCHEMA: &str = "trust.proof-concurrency.artifact-audit.v1";
const DEMO_AUDIT_SCHEMA: &str = "trust.proof-concurrency.demo-audit.v1";
const INPUT_SCHEMA: &str = "trust.proof-concurrency.inputs.v1";
const MATERIALIZE_SCHEMA: &str = "trust.proof-concurrency.input-materialization.v1";
const DEFAULT_INPUT_MANIFEST: &str = "reports/proof/concurrency-inputs.json";
const DEFAULT_INPUT_ARTIFACT_DIR: &str = "reports/proof/concurrency-artifacts";
const DEFAULT_MEMORY_MODEL: &str = "rust-abstract-machine+llvm-atomics";
const REQUIRED_OBLIGATION_KINDS: &[&str] = &["data_race_free", "atomic_ordering", "happens_before"];
const MAX_ARTIFACT_BYTES: usize = 128 * 1024 * 1024;
const MAX_GIT_STREAM_BYTES: usize = 64 * 1024 * 1024;
const GIT_TIMEOUT: Duration = Duration::from_secs(120);
const MAX_ID_BYTES: usize = 256;
const MAX_LABEL_BYTES: usize = 4096;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OutputFormat {
    Terminal,
    Json,
}

#[derive(Debug)]
struct Args {
    format: OutputFormat,
    repo_root: Option<PathBuf>,
    demo_audit: bool,
    manifest: Option<PathBuf>,
    materialize_manifest: bool,
    artifact_dir: Option<PathBuf>,
    manifest_out: Option<PathBuf>,
    solver: Option<String>,
    memory_model: Option<String>,
}

#[derive(Debug, Serialize)]
struct ProofConcurrencyAuditReport {
    schema: &'static str,
    mode: &'static str,
    proof_authority: &'static str,
    proof_pass: bool,
    validator_available: bool,
    validation_performed: bool,
    replay_performed: bool,
    blocker_code: &'static str,
    blocker: &'static str,
    generated_at: String,
    repo_head: String,
    repo_dirty: bool,
    repo_dirty_metadata: DirtyMetadata,
    runner: Runner,
    summary: AuditSummary,
    obligations: Vec<AuditObligation>,
}

#[derive(Debug, Serialize)]
struct DirtyMetadata {
    available: bool,
    dirty: bool,
    porcelain_v1: Vec<String>,
    untracked_files: &'static str,
    ignore_submodules: &'static str,
}

#[derive(Debug, Serialize)]
struct Runner {
    implementation: &'static str,
    language: &'static str,
    runtime: &'static str,
    entrypoint: &'static str,
    command: String,
    argv: Vec<String>,
    tool: &'static str,
    version: &'static str,
    python_used: bool,
    mode: &'static str,
    audit_kind: &'static str,
}

#[derive(Debug, Serialize)]
struct AuditSummary {
    total_obligations: u64,
    artifact_sets_present: u64,
    artifact_sets_hash_bound: u64,
    authenticated_validations: u64,
    replays_performed: u64,
}

#[derive(Debug, Serialize)]
struct AuditObligation {
    id: String,
    kind: String,
    status: &'static str,
    source: String,
    memory_model: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    artifacts: Option<ArtifactInventory>,
}

#[derive(Debug, Serialize)]
struct ArtifactInventory {
    declared_solver: String,
    source_sha256: String,
    certificate_sha256: String,
    transcript_sha256: String,
    dispatch_sha256: String,
    validation_status: &'static str,
    replay_status: &'static str,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct InputManifest {
    schema: String,
    solver: String,
    memory_model: String,
    obligations: Vec<InputObligation>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct InputObligation {
    id: String,
    kind: InputObligationKind,
    source: Option<String>,
    source_artifact: PathBuf,
    proof_artifact: PathBuf,
    certificate_artifact: PathBuf,
    dispatch_artifact: PathBuf,
    source_sha256: String,
    proof_sha256: String,
    certificate_sha256: String,
    dispatch_sha256: String,
    solver: Option<String>,
    memory_model: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
enum InputObligationKind {
    DataRaceFree,
    AtomicOrdering,
    HappensBefore,
}

impl InputObligationKind {
    fn as_str(self) -> &'static str {
        match self {
            Self::DataRaceFree => "data_race_free",
            Self::AtomicOrdering => "atomic_ordering",
            Self::HappensBefore => "happens_before",
        }
    }
}

#[derive(Debug)]
struct ArtifactBinding {
    canonical_path: PathBuf,
    sha256: String,
}

#[derive(Debug, Serialize)]
struct MaterializationResult {
    schema: &'static str,
    status: &'static str,
    proof_authority: &'static str,
    proof_pass: bool,
    validation_performed: bool,
    manifest_path: String,
    artifact_dir: String,
    solver: String,
    memory_model: String,
    obligations: u64,
}

#[derive(Debug, Clone, Copy)]
struct ReleaseObligationSpec {
    id: &'static str,
    kind: InputObligationKind,
}

#[derive(Debug)]
struct RepoProvenance {
    head: String,
    dirty_metadata: DirtyMetadata,
}

const RELEASE_INPUT_OBLIGATIONS: &[ReleaseObligationSpec] = &[
    ReleaseObligationSpec { id: "race_free_arc_mutex", kind: InputObligationKind::DataRaceFree },
    ReleaseObligationSpec {
        id: "atomic_release_acquire",
        kind: InputObligationKind::AtomicOrdering,
    },
    ReleaseObligationSpec {
        id: "channel_happens_before",
        kind: InputObligationKind::HappensBefore,
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
            eprintln!("targo trust proof-concurrency: {error}");
            eprintln!("Run `targo trust proof-concurrency --help` for usage.");
            ExitCode::from(2)
        }
    }
}

fn run(args: Args) -> ExitCode {
    if args.materialize_manifest {
        return run_materialize_input_manifest(args);
    }
    if args.artifact_dir.is_some()
        || args.manifest_out.is_some()
        || args.solver.is_some()
        || args.memory_model.is_some()
    {
        eprintln!(
            "targo trust proof-concurrency: --artifact-dir, --manifest-out, --solver, and --memory-model require --materialize-input-manifest"
        );
        return ExitCode::from(2);
    }

    let report = match (&args.manifest, args.demo_audit) {
        (Some(_), true) => Err(
            "choose either --manifest for artifact auditing or --demo-audit for demo mode, not both"
                .to_string(),
        ),
        (Some(manifest), false) => {
            build_artifact_audit(args.repo_root.as_deref(), manifest, ManifestSelection::Explicit)
        }
        (None, true) => build_demo_audit(args.repo_root.as_deref()),
        (None, false) => build_default_artifact_audit(args.repo_root.as_deref()),
    };
    let report = match report {
        Ok(report) => report,
        Err(error) => {
            eprintln!("targo trust proof-concurrency: {error}");
            return ExitCode::from(2);
        }
    };

    match args.format {
        OutputFormat::Json => match serde_json::to_string_pretty(&report) {
            Ok(json) => {
                println!("{json}");
                ExitCode::SUCCESS
            }
            Err(error) => {
                eprintln!("targo trust proof-concurrency: failed to serialize JSON: {error}");
                ExitCode::from(1)
            }
        },
        OutputFormat::Terminal => {
            println!(
                "proof-concurrency audit: schema={} mode={} proof_authority={} proof_pass={} repo_head={} obligations={}",
                report.schema,
                report.mode,
                report.proof_authority,
                report.proof_pass,
                report.repo_head,
                report.summary.total_obligations,
            );
            ExitCode::SUCCESS
        }
    }
}

enum ParseResult {
    Help,
    Run(Args),
}

fn parse_args(args: &[String]) -> Result<ParseResult, String> {
    let mut parsed = Args {
        format: OutputFormat::Terminal,
        repo_root: None,
        demo_audit: false,
        manifest: None,
        materialize_manifest: false,
        artifact_dir: None,
        manifest_out: None,
        solver: None,
        memory_model: None,
    };
    let mut i = 0;

    while i < args.len() {
        let arg = args[i].as_str();
        match arg {
            "--help" | "-h" => return Ok(ParseResult::Help),
            "--json" => {
                parsed.format = OutputFormat::Json;
                i += 1;
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
            "--repo-root" => {
                let value = args.get(i + 1).ok_or("--repo-root requires a path")?;
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
            "--manifest" => {
                let value = args.get(i + 1).ok_or("--manifest requires a path")?;
                if value.trim().is_empty() {
                    return Err("--manifest requires a path".to_string());
                }
                parsed.manifest = Some(PathBuf::from(value));
                i += 2;
            }
            value if value.starts_with("--manifest=") => {
                let value = value.strip_prefix("--manifest=").expect("prefix checked");
                if value.trim().is_empty() {
                    return Err("--manifest requires a path".to_string());
                }
                parsed.manifest = Some(PathBuf::from(value));
                i += 1;
            }
            "--demo-audit" | "--stub-proved" => {
                parsed.demo_audit = true;
                i += 1;
            }
            "--materialize-input-manifest" => {
                parsed.materialize_manifest = true;
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
            "--manifest-out" => {
                let value = args.get(i + 1).ok_or("--manifest-out requires a path")?;
                if value.trim().is_empty() {
                    return Err("--manifest-out requires a path".to_string());
                }
                parsed.manifest_out = Some(PathBuf::from(value));
                i += 2;
            }
            value if value.starts_with("--manifest-out=") => {
                let value = value.strip_prefix("--manifest-out=").expect("prefix checked");
                if value.trim().is_empty() {
                    return Err("--manifest-out requires a path".to_string());
                }
                parsed.manifest_out = Some(PathBuf::from(value));
                i += 1;
            }
            "--solver" => {
                let value = args.get(i + 1).ok_or("--solver requires an identity")?;
                if value.trim().is_empty() {
                    return Err("--solver requires an identity".to_string());
                }
                parsed.solver = Some(value.to_string());
                i += 2;
            }
            value if value.starts_with("--solver=") => {
                let value = value.strip_prefix("--solver=").expect("prefix checked");
                if value.trim().is_empty() {
                    return Err("--solver requires an identity".to_string());
                }
                parsed.solver = Some(value.to_string());
                i += 1;
            }
            "--memory-model" => {
                let value = args.get(i + 1).ok_or("--memory-model requires a value")?;
                if value.trim().is_empty() {
                    return Err("--memory-model requires a value".to_string());
                }
                parsed.memory_model = Some(value.to_string());
                i += 2;
            }
            value if value.starts_with("--memory-model=") => {
                let value = value.strip_prefix("--memory-model=").expect("prefix checked");
                if value.trim().is_empty() {
                    return Err("--memory-model requires a value".to_string());
                }
                parsed.memory_model = Some(value.to_string());
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
  targo trust proof-concurrency --format json [--repo-root <path>]
  targo trust proof-concurrency --format json --manifest <path> [--repo-root <path>]
  targo trust proof-concurrency --format json --demo-audit [--repo-root <path>]
  targo trust proof-concurrency --materialize-input-manifest --solver <identity> [--artifact-dir <path>] [--manifest-out <path>] [--repo-root <path>]

Inventory concurrency artifacts without claiming proof authority.

No Trust-owned authenticated concurrency validator/replayer is implemented.
Consequently this command cannot emit a domination-admissible proof report.

Options:
  --format json        Emit a non-proof artifact/demo audit JSON document
  --json               Alias for --format json
  --manifest <path>    trust.proof-concurrency.inputs.v1 artifact manifest with source,
                       proof transcript, certificate, and dispatch artifact paths
                       (default: reports/proof/concurrency-inputs.json)
  --demo-audit         Emit trust.proof-concurrency.demo-audit.v1 with authority none
  --stub-proved        Deprecated alias for --demo-audit; never emits proved status
  --materialize-input-manifest
                       Write trust.proof-concurrency.inputs.v1 from a complete
                       artifact set; inventory only, never proof evidence
  --artifact-dir <path>
                       Directory containing <id>.source.rs, <id>.proof,
                       <id>.cert, and <id>.dispatch files for each release
                       obligation (default: reports/proof/concurrency-artifacts)
  --manifest-out <path>
                       Manifest path to write (default: reports/proof/concurrency-inputs.json)
  --solver <identity>  Concrete non-manual solver identity for materialized inputs
  --memory-model <id>  Memory-model label for materialized inputs
                       (default: rust-abstract-machine+llvm-atomics)
  --repo-root <path>   Git repository root to bind in provenance
  --help               Show this help
"
    );
}

fn run_materialize_input_manifest(args: Args) -> ExitCode {
    let manifest = match materialize_input_manifest(&args) {
        Ok(result) => result,
        Err(error) => {
            eprintln!("targo trust proof-concurrency: {error}");
            return ExitCode::from(2);
        }
    };

    match args.format {
        OutputFormat::Json => match serde_json::to_string_pretty(&manifest) {
            Ok(json) => {
                println!("{json}");
                ExitCode::SUCCESS
            }
            Err(error) => {
                eprintln!(
                    "targo trust proof-concurrency: failed to serialize materialization JSON: {error}"
                );
                ExitCode::from(1)
            }
        },
        OutputFormat::Terminal => {
            println!(
                "proof-concurrency inputs: schema={} status={} proof_authority={} proof_pass={} manifest_path={} obligations={}",
                manifest.schema,
                manifest.status,
                manifest.proof_authority,
                manifest.proof_pass,
                manifest.manifest_path,
                manifest.obligations
            );
            ExitCode::SUCCESS
        }
    }
}

fn materialize_input_manifest(args: &Args) -> Result<MaterializationResult, String> {
    if args.demo_audit {
        return Err(
            "--materialize-input-manifest cannot be combined with --demo-audit/--stub-proved"
                .to_string(),
        );
    }
    if args.manifest.is_some() {
        return Err(
            "--materialize-input-manifest writes --manifest-out, not --manifest".to_string()
        );
    }

    let repo_root = resolve_repo_root(args.repo_root.as_deref())?;
    let solver = args
        .solver
        .as_deref()
        .ok_or("--materialize-input-manifest requires --solver <identity>")?;
    let solver = concrete_solver_identity("materialize-input-manifest", solver)?;
    let memory_model =
        args.memory_model.as_deref().unwrap_or(DEFAULT_MEMORY_MODEL).trim().to_string();
    if memory_model.is_empty() {
        return Err("--memory-model must be nonempty".to_string());
    }
    validate_label("memory_model", &memory_model, MAX_LABEL_BYTES)?;

    let artifact_dir = resolve_output_path_within_repo(
        &repo_root,
        args.artifact_dir.as_deref().unwrap_or_else(|| Path::new(DEFAULT_INPUT_ARTIFACT_DIR)),
        "artifact directory",
    )?;
    let manifest_path = resolve_output_path_within_repo(
        &repo_root,
        args.manifest_out.as_deref().unwrap_or_else(|| Path::new(DEFAULT_INPUT_MANIFEST)),
        "manifest output",
    )?;
    let manifest_dir = manifest_path.parent().ok_or_else(|| {
        format!("manifest output path {} has no parent directory", manifest_path.display())
    })?;
    if !artifact_dir.starts_with(manifest_dir) {
        return Err(format!(
            "artifact directory {} must be inside manifest directory {} so every serialized artifact path stays contained and relative",
            artifact_dir.display(),
            manifest_dir.display()
        ));
    }

    let mut obligations = Vec::with_capacity(RELEASE_INPUT_OBLIGATIONS.len());
    let mut missing = Vec::new();
    for spec in RELEASE_INPUT_OBLIGATIONS {
        match materialize_obligation(spec, &repo_root, &artifact_dir, manifest_dir) {
            Ok(obligation) => obligations.push(obligation),
            Err(errors) => missing.extend(errors),
        }
    }
    if !missing.is_empty() {
        return Err(format!(
            "cannot materialize `{DEFAULT_INPUT_MANIFEST}`; missing or invalid release artifacts:\n{}",
            missing.join("\n")
        ));
    }

    let manifest = InputManifest {
        schema: INPUT_SCHEMA.to_string(),
        solver: solver.clone(),
        memory_model: memory_model.clone(),
        obligations,
    };
    let bytes = serde_json::to_vec_pretty(&manifest)
        .map_err(|error| format!("failed to serialize input manifest: {error}"))?;
    durable_io::atomic_write_private(&manifest_path, &bytes).map_err(|error| {
        format!("failed to publish input manifest {} safely: {error}", manifest_path.display())
    })?;

    Ok(MaterializationResult {
        schema: MATERIALIZE_SCHEMA,
        status: "artifact_inventory_materialized",
        proof_authority: "none",
        proof_pass: false,
        validation_performed: false,
        manifest_path: display_repo_path(&repo_root, &manifest_path),
        artifact_dir: display_repo_path(&repo_root, &artifact_dir),
        solver,
        memory_model,
        obligations: RELEASE_INPUT_OBLIGATIONS.len() as u64,
    })
}

fn materialize_obligation(
    spec: &ReleaseObligationSpec,
    repo_root: &Path,
    artifact_dir: &Path,
    manifest_dir: &Path,
) -> Result<InputObligation, Vec<String>> {
    let source_artifact = artifact_dir.join(format!("{}.source.rs", spec.id));
    let proof_artifact = artifact_dir.join(format!("{}.proof", spec.id));
    let certificate_artifact = artifact_dir.join(format!("{}.cert", spec.id));
    let dispatch_artifact = artifact_dir.join(format!("{}.dispatch", spec.id));
    let mut errors = Vec::new();

    let source_sha256 =
        materialize_artifact_sha256(repo_root, spec.id, "source_artifact", &source_artifact)
            .unwrap_or_else(|error| {
                errors.push(error);
                String::new()
            });
    let proof_sha256 =
        materialize_artifact_sha256(repo_root, spec.id, "proof_artifact", &proof_artifact)
            .unwrap_or_else(|error| {
                errors.push(error);
                String::new()
            });
    let certificate_sha256 = materialize_artifact_sha256(
        repo_root,
        spec.id,
        "certificate_artifact",
        &certificate_artifact,
    )
    .unwrap_or_else(|error| {
        errors.push(error);
        String::new()
    });
    let dispatch_sha256 =
        materialize_artifact_sha256(repo_root, spec.id, "dispatch_artifact", &dispatch_artifact)
            .unwrap_or_else(|error| {
                errors.push(error);
                String::new()
            });
    if !errors.is_empty() {
        return Err(errors);
    }

    Ok(InputObligation {
        id: spec.id.to_string(),
        kind: spec.kind,
        source: Some(display_manifest_artifact_path(&source_artifact, manifest_dir)),
        source_artifact: manifest_artifact_path(&source_artifact, manifest_dir),
        proof_artifact: manifest_artifact_path(&proof_artifact, manifest_dir),
        certificate_artifact: manifest_artifact_path(&certificate_artifact, manifest_dir),
        dispatch_artifact: manifest_artifact_path(&dispatch_artifact, manifest_dir),
        source_sha256,
        proof_sha256,
        certificate_sha256,
        dispatch_sha256,
        solver: None,
        memory_model: None,
    })
}

fn materialize_artifact_sha256(
    repo_root: &Path,
    obligation_id: &str,
    field: &str,
    path: &Path,
) -> Result<String, String> {
    let path = resolve_existing_path_within_repo(repo_root, path, field)
        .map_err(|error| format!("{obligation_id}: {error}"))?;
    let bytes = read_bounded_file(&path, MAX_ARTIFACT_BYTES).map_err(|error| {
        format!("{obligation_id}: {field} {} could not be read safely: {error}", path.display())
    })?;
    if bytes.is_empty() {
        return Err(format!("{obligation_id}: {field} {} must be nonempty", path.display()));
    }
    if field == "source_artifact" {
        validate_source_artifact(obligation_id, &path, &bytes)?;
    }
    Ok(trust_types::digest::stable_sha256_hex(&bytes))
}

fn manifest_artifact_path(path: &Path, manifest_dir: &Path) -> PathBuf {
    path.strip_prefix(manifest_dir).unwrap_or(path).to_path_buf()
}

fn display_manifest_artifact_path(path: &Path, manifest_dir: &Path) -> String {
    manifest_artifact_path(path, manifest_dir).display().to_string()
}

fn display_repo_path(repo_root: &Path, path: &Path) -> String {
    path.strip_prefix(repo_root).unwrap_or(path).display().to_string()
}

fn build_demo_audit(repo_root: Option<&Path>) -> Result<ProofConcurrencyAuditReport, String> {
    let provenance = collect_clean_repo_provenance(repo_root)?;
    let obligations = demo_obligations();
    let summary = AuditSummary {
        total_obligations: obligations.len() as u64,
        artifact_sets_present: 0,
        artifact_sets_hash_bound: 0,
        authenticated_validations: 0,
        replays_performed: 0,
    };

    Ok(ProofConcurrencyAuditReport {
        schema: DEMO_AUDIT_SCHEMA,
        mode: "synthetic_demo_audit",
        proof_authority: "none",
        proof_pass: false,
        validator_available: false,
        validation_performed: false,
        replay_performed: false,
        blocker_code: "missing_trust_concurrency_authenticated_validator",
        blocker: "Synthetic demo rows are not proof artifacts, and no Trust-owned authenticated concurrency validator/replayer is implemented.",
        generated_at: generated_at(),
        repo_head: provenance.head,
        repo_dirty: false,
        repo_dirty_metadata: provenance.dirty_metadata,
        runner: Runner {
            implementation: "rust",
            language: "rust",
            runtime: "native",
            entrypoint: "targo trust proof-concurrency",
            command: "targo trust proof-concurrency --format json --demo-audit".to_string(),
            argv: vec![
                "targo".to_string(),
                "trust".to_string(),
                "proof-concurrency".to_string(),
                "--format".to_string(),
                "json".to_string(),
                "--demo-audit".to_string(),
            ],
            tool: "targo-trust",
            version: env!("CARGO_PKG_VERSION"),
            python_used: false,
            mode: "synthetic_demo_audit",
            audit_kind: "nonproof_contract_shape_only",
        },
        summary,
        obligations,
    })
}

fn build_artifact_audit(
    repo_root: Option<&Path>,
    manifest_path: &Path,
    manifest_selection: ManifestSelection,
) -> Result<ProofConcurrencyAuditReport, String> {
    let repo_root = resolve_repo_root(repo_root)?;
    let provenance = collect_clean_repo_provenance(Some(&repo_root))?;
    let manifest_path = resolve_existing_path_within_repo(&repo_root, manifest_path, "manifest")?;
    let manifest = read_input_manifest(&manifest_path)?;
    let manifest_dir = manifest_path.parent().ok_or_else(|| {
        format!("manifest path {} has no parent directory", manifest_path.display())
    })?;
    let obligations = build_artifact_obligations(&manifest, manifest_dir, &repo_root)?;
    let summary = AuditSummary {
        total_obligations: obligations.len() as u64,
        artifact_sets_present: obligations.len() as u64,
        artifact_sets_hash_bound: obligations.len() as u64,
        authenticated_validations: 0,
        replays_performed: 0,
    };
    let manifest_arg = manifest_path.display().to_string();
    let (command, argv) = match manifest_selection {
        ManifestSelection::Default => (
            "targo trust proof-concurrency --format json".to_string(),
            vec![
                "targo".to_string(),
                "trust".to_string(),
                "proof-concurrency".to_string(),
                "--format".to_string(),
                "json".to_string(),
            ],
        ),
        ManifestSelection::Explicit => (
            format!("targo trust proof-concurrency --format json --manifest {manifest_arg}"),
            vec![
                "targo".to_string(),
                "trust".to_string(),
                "proof-concurrency".to_string(),
                "--format".to_string(),
                "json".to_string(),
                "--manifest".to_string(),
                manifest_arg,
            ],
        ),
    };

    Ok(ProofConcurrencyAuditReport {
        schema: ARTIFACT_AUDIT_SCHEMA,
        mode: "artifact_inventory_audit",
        proof_authority: "none",
        proof_pass: false,
        validator_available: false,
        validation_performed: false,
        replay_performed: false,
        blocker_code: "missing_trust_concurrency_authenticated_validator",
        blocker: "Artifact presence and hash binding do not validate a certificate or replay a proof; no Trust-owned authenticated concurrency validator/replayer is implemented.",
        generated_at: generated_at(),
        repo_head: provenance.head,
        repo_dirty: false,
        repo_dirty_metadata: provenance.dirty_metadata,
        runner: Runner {
            implementation: "rust",
            language: "rust",
            runtime: "native",
            entrypoint: "targo trust proof-concurrency",
            command,
            argv,
            tool: "targo-trust",
            version: env!("CARGO_PKG_VERSION"),
            python_used: false,
            mode: "artifact_inventory_audit",
            audit_kind: "presence_and_digest_only",
        },
        summary,
        obligations,
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ManifestSelection {
    Default,
    Explicit,
}

fn build_default_artifact_audit(
    repo_root: Option<&Path>,
) -> Result<ProofConcurrencyAuditReport, String> {
    let manifest_path = default_input_manifest_path(repo_root)?;
    if !manifest_path.is_file() {
        return Err(format!(
            "artifact auditing requires `{DEFAULT_INPUT_MANIFEST}` or --manifest <path>; use --demo-audit only for the synthetic non-proof demo; no validated proof-report producer is implemented"
        ));
    }
    build_artifact_audit(repo_root, &manifest_path, ManifestSelection::Default)
}

fn default_input_manifest_path(repo_root: Option<&Path>) -> Result<PathBuf, String> {
    Ok(resolve_repo_root(repo_root)?.join(DEFAULT_INPUT_MANIFEST))
}

fn collect_clean_repo_provenance(repo_root: Option<&Path>) -> Result<RepoProvenance, String> {
    let repo_root = resolve_repo_root(repo_root)?;
    let repo_head = controlled_git::canonical_head(
        &repo_root,
        "proof-concurrency repository HEAD probe",
        MAX_GIT_STREAM_BYTES,
        GIT_TIMEOUT,
    )?;

    let porcelain = git_status_porcelain_lines(&repo_root)?;
    if !porcelain.is_empty() {
        return Err(format!(
            "repo must be clean before emitting a commit-bound proof-concurrency audit; git status has {} entries",
            porcelain.len()
        ));
    }

    Ok(RepoProvenance {
        head: repo_head,
        dirty_metadata: DirtyMetadata {
            available: true,
            dirty: false,
            porcelain_v1: porcelain,
            untracked_files: "all",
            ignore_submodules: "none",
        },
    })
}

fn read_input_manifest(path: &Path) -> Result<InputManifest, String> {
    let bytes = read_bounded_file(path, MAX_RELEASE_METADATA_BYTES).map_err(|error| {
        format!("failed to read proof-concurrency manifest {}: {error}", path.display())
    })?;
    let manifest: InputManifest = serde_json::from_slice(&bytes).map_err(|error| {
        format!(
            "failed to parse proof-concurrency manifest {} with schema {}: {error}",
            path.display(),
            INPUT_SCHEMA
        )
    })?;
    if manifest.schema != INPUT_SCHEMA {
        return Err(format!(
            "proof-concurrency manifest {} has schema `{}`, expected `{}`",
            path.display(),
            manifest.schema,
            INPUT_SCHEMA
        ));
    }
    if manifest.obligations.is_empty() {
        return Err("proof-concurrency manifest obligations array must be nonempty".to_string());
    }
    Ok(manifest)
}

fn build_artifact_obligations(
    manifest: &InputManifest,
    manifest_dir: &Path,
    repo_root: &Path,
) -> Result<Vec<AuditObligation>, String> {
    let mut ids = BTreeSet::new();
    let mut kinds = BTreeSet::new();
    let mut obligations = Vec::with_capacity(manifest.obligations.len());

    for input in &manifest.obligations {
        let id = input.id.trim();
        validate_label("obligation id", id, MAX_ID_BYTES)?;
        if !ids.insert(id.to_string()) {
            return Err(format!("proof-concurrency manifest has duplicate obligation id `{id}`"));
        }

        let kind = input.kind.as_str();
        kinds.insert(kind);
        let solver = input.solver.as_deref().unwrap_or(&manifest.solver);
        let solver = concrete_solver_identity(id, solver)?;
        let memory_model = input.memory_model.as_deref().unwrap_or(&manifest.memory_model).trim();
        if memory_model.is_empty() {
            return Err(format!("{id}: memory_model must be nonempty"));
        }
        validate_label("memory_model", memory_model, MAX_LABEL_BYTES)?;

        let source_binding = bind_artifact(
            repo_root,
            manifest_dir,
            id,
            "source_artifact",
            &input.source_artifact,
            Some(input.source_sha256.as_str()),
        )?;
        let proof_binding = bind_artifact(
            repo_root,
            manifest_dir,
            id,
            "proof_artifact",
            &input.proof_artifact,
            Some(input.proof_sha256.as_str()),
        )?;
        let certificate_binding = bind_artifact(
            repo_root,
            manifest_dir,
            id,
            "certificate_artifact",
            &input.certificate_artifact,
            Some(input.certificate_sha256.as_str()),
        )?;
        let dispatch_binding = bind_artifact(
            repo_root,
            manifest_dir,
            id,
            "dispatch_artifact",
            &input.dispatch_artifact,
            Some(input.dispatch_sha256.as_str()),
        )?;
        let source = input
            .source
            .as_deref()
            .map(str::trim)
            .filter(|source| !source.is_empty())
            .map(str::to_string)
            .unwrap_or_else(|| display_repo_path(repo_root, &source_binding.canonical_path));
        validate_repo_source_label(&source)?;

        obligations.push(AuditObligation {
            id: id.to_string(),
            kind: kind.to_string(),
            status: "present_unvalidated",
            source,
            memory_model: memory_model.to_string(),
            artifacts: Some(ArtifactInventory {
                declared_solver: solver,
                source_sha256: source_binding.sha256,
                certificate_sha256: certificate_binding.sha256,
                transcript_sha256: proof_binding.sha256,
                dispatch_sha256: dispatch_binding.sha256,
                validation_status: "not_performed",
                replay_status: "not_performed",
            }),
        });
    }

    for required in REQUIRED_OBLIGATION_KINDS {
        if !kinds.contains(required) {
            return Err(format!("proof-concurrency manifest must include a {required} obligation"));
        }
    }

    Ok(obligations)
}

fn bind_artifact(
    repo_root: &Path,
    manifest_dir: &Path,
    obligation_id: &str,
    field: &str,
    path: &Path,
    expected_sha256: Option<&str>,
) -> Result<ArtifactBinding, String> {
    if path.as_os_str().is_empty() {
        return Err(format!("{obligation_id}: {field} requires a path"));
    }
    validate_manifest_artifact_path(path, obligation_id, field)?;
    let resolved = manifest_dir.join(path);
    let canonical_path = resolve_existing_path_within_repo(repo_root, &resolved, field)
        .map_err(|error| format!("{obligation_id}: {error}"))?;
    let bytes = read_bounded_file(&canonical_path, MAX_ARTIFACT_BYTES).map_err(|error| {
        format!(
            "{obligation_id}: {field} {} could not be read safely: {error}",
            canonical_path.display()
        )
    })?;
    if bytes.is_empty() {
        return Err(format!(
            "{obligation_id}: {field} {} must be nonempty",
            canonical_path.display()
        ));
    }
    if field == "source_artifact" {
        validate_source_artifact(obligation_id, &canonical_path, &bytes)?;
    }
    let actual_sha256 = trust_types::digest::stable_sha256_hex(&bytes);
    if let Some(expected_sha256) = expected_sha256 {
        let expected_sha256 = canonical_expected_sha256(obligation_id, field, expected_sha256)?;
        if expected_sha256 != actual_sha256 {
            return Err(format!(
                "{obligation_id}: {field} {} hash mismatch; expected {expected_sha256}, actual {actual_sha256}",
                canonical_path.display()
            ));
        }
    }

    Ok(ArtifactBinding { canonical_path, sha256: actual_sha256 })
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
    if repo_root.is_some() && discovered != requested {
        return Err(format!(
            "--repo-root must name the repository top level exactly; {} resolves inside {}",
            requested.display(),
            discovered.display()
        ));
    }
    Ok(discovered)
}

fn git_status_porcelain_lines(repo_root: &Path) -> Result<Vec<String>, String> {
    controlled_git::exact_status_porcelain_v1(
        repo_root,
        "proof-concurrency repository cleanliness probe",
        MAX_GIT_STREAM_BYTES,
        GIT_TIMEOUT,
    )
}

fn resolve_existing_path_within_repo(
    repo_root: &Path,
    path: &Path,
    role: &str,
) -> Result<PathBuf, String> {
    let candidate = path_within_repo(repo_root, path, role)?;
    ensure_no_symlink_components(repo_root, &candidate, role, true)?;
    let canonical = candidate.canonicalize().map_err(|error| {
        format!("{role} {} is missing or cannot be resolved: {error}", candidate.display())
    })?;
    if !canonical.starts_with(repo_root) {
        return Err(format!(
            "{role} {} escapes repository root {}",
            canonical.display(),
            repo_root.display()
        ));
    }
    Ok(canonical)
}

fn resolve_output_path_within_repo(
    repo_root: &Path,
    path: &Path,
    role: &str,
) -> Result<PathBuf, String> {
    let candidate = path_within_repo(repo_root, path, role)?;
    ensure_no_symlink_components(repo_root, &candidate, role, false)?;
    Ok(candidate)
}

fn path_within_repo(repo_root: &Path, path: &Path, role: &str) -> Result<PathBuf, String> {
    let candidate = if path.is_absolute() { path.to_path_buf() } else { repo_root.join(path) };
    if candidate
        .components()
        .any(|component| matches!(component, Component::ParentDir | Component::CurDir))
    {
        return Err(format!(
            "{role} {} must not contain `.` or `..` components",
            candidate.display()
        ));
    }
    // macOS exposes /var through /private/var. Canonicalize only the nearest
    // existing parent so platform aliases normalize without following the leaf
    // file (which must still be rejected when it is a symlink).
    let candidate = canonicalize_existing_parent(&candidate, role)?;
    let relative = candidate.strip_prefix(repo_root).map_err(|_| {
        format!(
            "{role} {} must be contained by repository root {}",
            candidate.display(),
            repo_root.display()
        )
    })?;
    if relative.as_os_str().is_empty()
        || !relative.components().all(|component| matches!(component, Component::Normal(_)))
    {
        return Err(format!(
            "{role} {} must be a canonical contained path without `.` or `..` components",
            candidate.display()
        ));
    }
    Ok(candidate)
}

fn canonicalize_existing_parent(candidate: &Path, role: &str) -> Result<PathBuf, String> {
    let leaf = candidate
        .file_name()
        .ok_or_else(|| format!("{role} {} has no final path component", candidate.display()))?;
    let mut ancestor = candidate
        .parent()
        .ok_or_else(|| format!("{role} {} has no parent directory", candidate.display()))?;
    let mut suffix = vec![leaf.to_os_string()];
    while fs::symlink_metadata(ancestor).is_err() {
        let name = ancestor
            .file_name()
            .ok_or_else(|| format!("{role} {} has no existing ancestor", candidate.display()))?;
        suffix.push(name.to_os_string());
        ancestor = ancestor
            .parent()
            .ok_or_else(|| format!("{role} {} has no existing ancestor", candidate.display()))?;
    }
    let mut normalized = ancestor.canonicalize().map_err(|error| {
        format!("{role} parent {} cannot be resolved: {error}", ancestor.display())
    })?;
    for component in suffix.into_iter().rev() {
        normalized.push(component);
    }
    Ok(normalized)
}

fn ensure_no_symlink_components(
    repo_root: &Path,
    candidate: &Path,
    role: &str,
    require_all: bool,
) -> Result<(), String> {
    let relative = candidate
        .strip_prefix(repo_root)
        .map_err(|_| format!("{role} {} is outside repository root", candidate.display()))?;
    let mut current = repo_root.to_path_buf();
    for component in relative.components() {
        let Component::Normal(component) = component else {
            return Err(format!("{role} contains a non-canonical path component"));
        };
        current.push(component);
        match fs::symlink_metadata(&current) {
            Ok(metadata) if metadata.file_type().is_symlink() => {
                return Err(format!("{role} {} traverses a symbolic link", current.display()));
            }
            Ok(_) => {}
            Err(error) if !require_all && error.kind() == std::io::ErrorKind::NotFound => break,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                return Err(format!(
                    "{role} {} is missing or cannot be resolved: {error}",
                    candidate.display()
                ));
            }
            Err(error) => {
                return Err(format!(
                    "{role} {} cannot be inspected safely: {error}",
                    current.display()
                ));
            }
        }
    }
    Ok(())
}

fn validate_manifest_artifact_path(
    path: &Path,
    obligation_id: &str,
    field: &str,
) -> Result<(), String> {
    if !is_canonical_relative_path(path) {
        return Err(format!(
            "{obligation_id}: {field} must be a canonical manifest-relative contained path"
        ));
    }
    Ok(())
}

fn validate_source_artifact(obligation_id: &str, path: &Path, bytes: &[u8]) -> Result<(), String> {
    let source = std::str::from_utf8(bytes).map_err(|error| {
        format!("{obligation_id}: source artifact {} is not UTF-8: {error}", path.display())
    })?;
    if source.chars().any(|ch| ch.is_control() && !matches!(ch, '\n' | '\r' | '\t')) {
        return Err(format!(
            "{obligation_id}: source artifact {} contains an unexpected control character",
            path.display()
        ));
    }
    Ok(())
}

fn validate_label(kind: &str, value: &str, max_bytes: usize) -> Result<(), String> {
    if value.is_empty() || value.len() > max_bytes || value.chars().any(char::is_control) {
        return Err(format!(
            "{kind} must be nonempty, control-free, and at most {max_bytes} bytes"
        ));
    }
    Ok(())
}

fn validate_repo_source_label(source: &str) -> Result<(), String> {
    validate_label("source", source, MAX_LABEL_BYTES)?;
    let path = Path::new(source);
    if source.contains("://")
        || source.to_ascii_lowercase().starts_with("urn:")
        || !is_canonical_relative_path(path)
    {
        return Err("source must be a canonical repository-relative path, not a URI".to_string());
    }
    Ok(())
}

fn is_canonical_relative_path(path: &Path) -> bool {
    if path.is_absolute() || path.as_os_str().is_empty() {
        return false;
    }
    let mut normalized = PathBuf::new();
    for component in path.components() {
        let Component::Normal(component) = component else {
            return false;
        };
        normalized.push(component);
    }
    normalized.as_os_str() == path.as_os_str()
}

fn demo_obligations() -> Vec<AuditObligation> {
    [
        ("race_free_arc_mutex", "data_race_free"),
        ("atomic_release_acquire", "atomic_ordering"),
        ("channel_happens_before", "happens_before"),
    ]
    .into_iter()
    .map(|(id, kind)| AuditObligation {
        id: id.to_string(),
        kind: kind.to_string(),
        status: "synthetic_demo_only",
        source: "not-generated".to_string(),
        memory_model: DEFAULT_MEMORY_MODEL.to_string(),
        artifacts: None,
    })
    .collect()
}

fn generated_at() -> String {
    let seconds = SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_secs();
    format!("unix-seconds:{seconds}")
}

fn canonical_expected_sha256(
    obligation_id: &str,
    field: &str,
    value: &str,
) -> Result<String, String> {
    let value = value.trim();
    if trust_types::digest::is_stable_sha256_hex(value) {
        Ok(value.to_string())
    } else {
        Err(format!("{obligation_id}: {field} expected SHA-256 must be canonical lowercase hex"))
    }
}


fn concrete_solver_identity(obligation_id: &str, value: &str) -> Result<String, String> {
    let value = value.trim();
    let lowered = value.to_ascii_lowercase();
    if value.is_empty()
        || value.len() > MAX_LABEL_BYTES
        || ["unknown", "manual", "none", "n/a", "stub", "demo", "fixture", "mock"]
            .iter()
            .any(|marker| lowered.contains(marker))
        || lowered.contains("://")
        || lowered.starts_with("urn:")
        || value.chars().any(|ch| {
            !(ch.is_ascii_alphanumeric() || matches!(ch, '-' | '_' | '.' | '/' | ':' | '+'))
        })
    {
        return Err(format!(
            "{obligation_id}: solver must be a concrete non-manual solver identity; stub/demo/fixture/mock and URI identities are forbidden"
        ));
    }
    Ok(value.to_string())
}



#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parser_accepts_json_demo_alias_and_repo_root() {
        let args = vec![
            "--format=json".to_string(),
            "--stub-proved".to_string(),
            "--repo-root=.".to_string(),
        ];

        let ParseResult::Run(parsed) = parse_args(&args).expect("args should parse") else {
            panic!("expected run args");
        };

        assert_eq!(parsed.format, OutputFormat::Json);
        assert!(parsed.demo_audit);
        assert!(parsed.manifest.is_none());
        assert_eq!(parsed.repo_root.as_deref(), Some(Path::new(".")));
    }

    #[test]
    fn parser_accepts_json_manifest_and_repo_root() {
        let args = vec![
            "--json".to_string(),
            "--manifest".to_string(),
            "proofs/concurrency/manifest.json".to_string(),
            "--repo-root=.".to_string(),
        ];

        let ParseResult::Run(parsed) = parse_args(&args).expect("args should parse") else {
            panic!("expected run args");
        };

        assert_eq!(parsed.format, OutputFormat::Json);
        assert!(!parsed.demo_audit);
        assert_eq!(parsed.manifest.as_deref(), Some(Path::new("proofs/concurrency/manifest.json")));
        assert_eq!(parsed.repo_root.as_deref(), Some(Path::new(".")));
    }

    #[test]
    fn demo_obligations_are_explicitly_nonproof() {
        let obligations = demo_obligations();
        let kinds =
            obligations.iter().map(|obligation| obligation.kind.as_str()).collect::<Vec<_>>();

        assert_eq!(kinds, vec!["data_race_free", "atomic_ordering", "happens_before"]);
        for obligation in obligations {
            assert_eq!(obligation.status, "synthetic_demo_only");
            assert!(obligation.artifacts.is_none());
        }
    }

    #[test]
    fn rejects_stub_and_uri_solver_identities() {
        for solver in [
            "trust-proof-concurrency-stub-v1",
            "fixture-solver",
            "https://solver.example/proof",
            "urn:trust:solver",
        ] {
            assert!(
                concrete_solver_identity("race_free", solver).is_err(),
                "{solver} must not be admitted as a concrete solver"
            );
        }
        assert_eq!(
            concrete_solver_identity("race_free", "trust-concurrency-prover-v1")
                .expect("concrete local identity"),
            "trust-concurrency-prover-v1"
        );
    }

    #[test]
    fn manifest_artifact_paths_are_relative_and_contained() {
        for path in ["../escape.cert", "/tmp/escape.cert", "./alias.cert"] {
            assert!(
                validate_manifest_artifact_path(Path::new(path), "race_free", "certificate")
                    .is_err(),
                "{path} must be rejected"
            );
        }
        validate_manifest_artifact_path(
            Path::new("artifacts/race_free.cert"),
            "race_free",
            "certificate",
        )
        .expect("canonical contained relative path");
    }
}
