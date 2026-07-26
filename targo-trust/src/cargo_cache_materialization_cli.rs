use std::collections::{BTreeMap, BTreeSet};
use std::io::Read as _;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use std::{env, fs, io};

use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use crate::pipeline::{
    LinkedTrustCargoSurfaceKind, LinkedTrustCargoSurfaceStatus, LinkedTrustSurfaceToolStatusKind,
    LinkedTrustToolchainStatus, LinkedTrustToolchainStatusKind, detect_linked_trust_cargo_surface,
};
use crate::stage2_tools::discover_unique_repo_stage2_tool;
use crate::{bounded_process, durable_io};

const MATERIALIZATION_SCHEMA: &str = "trust.full-verify.cargo-cache-materialization.v1";
const CACHE_HIT_MISS_SCHEMA: &str = "trust.full-verify.cargo-cache-hit-miss.v1";
const FETCH_PLAN_SCHEMA: &str = "trust.full-verify.cargo-cache-fetch-plan.v1";
const MATERIALIZATION_PROOF: &str = ".trust-full-verify-cargo-cache-materialization.json";
const MAX_CARGO_LOCKFILE_BYTES: usize = 64 * 1024 * 1024;
const MAX_REGISTRY_ARCHIVE_BYTES: u64 = 1024 * 1024 * 1024;

const USAGE: &str = "\
Usage: targo trust verify cargo-cache --repo-root <path> --cargo-home <path> [--json-output <path>]

Materialize a dedicated registry-only Cargo seed cache for release full-verification.

Options:
  --repo-root <path>     Trust checkout root containing build/<host>/stage2
  --cargo-home <path>    Dedicated seed CARGO_HOME to materialize
  --json-output <path>   Also write the materialization report to this path
  -h, --help             Show this help
";

const FULL_VERIFY_LOCKFILES: &[&str] = &[
    "Cargo.lock",
    "targo-trust/Cargo.lock",
    "crates/Cargo.lock",
    "library/Cargo.lock",
    "library/backtrace/Cargo.lock",
    "library/compiler-builtins/Cargo.lock",
    "library/portable-simd/Cargo.lock",
    "library/stdarch/Cargo.lock",
    "src/bootstrap/Cargo.lock",
    "src/tools/rust-analyzer/Cargo.lock",
    "src/tools/rustbook/Cargo.lock",
    // src/tools/trustfmt is a ROOT-workspace member (root Cargo.toml `members`),
    // so the root "Cargo.lock" above already governs and covers its resolution.
    // Its standalone Cargo.lock was a dead vestige of the upstream-rustfmt
    // rename (no build resolved against it) and was removed: auditing it here
    // demanded cache evidence for ~98 stale package pins nothing ever fetches.
    // rust-analyzer and rustbook stay listed because each declares its OWN
    // [workspace] and really does resolve against its standalone lock.
];

#[derive(Debug)]
struct Args {
    repo_root: PathBuf,
    cargo_home: PathBuf,
    json_output: Option<PathBuf>,
}

#[derive(Debug)]
struct TrustToolchain {
    surface: LinkedTrustCargoSurfaceStatus,
    sysroot: PathBuf,
    bin_dir: PathBuf,
    trustc: PathBuf,
    targo: PathBuf,
}

#[derive(Debug, Default)]
struct RequiredToolIdentityAudit {
    errors: Vec<String>,
    identities: BTreeMap<String, Value>,
    captured: Vec<CapturedToolIdentity>,
}

#[derive(Debug, Clone)]
struct CapturedToolIdentity {
    name: &'static str,
    path: PathBuf,
    version_args: &'static [&'static str],
    sha256: String,
}

#[derive(Debug)]
struct FetchRecord {
    manifest_index: usize,
    plan_position: usize,
    manifest: PathBuf,
    lockfile: PathBuf,
    command: Vec<String>,
    status: String,
    fetch_executed: bool,
    skip_reason: Option<String>,
    covered_by_manifest: Option<PathBuf>,
    exit_code: Option<i32>,
    stdout: String,
    stderr: String,
    cache_initial: ManifestCacheEvidence,
    cache_before: ManifestCacheEvidence,
    cache_after: ManifestCacheEvidence,
}

#[derive(Debug)]
struct ManifestJob {
    manifest_index: usize,
    manifest: PathBuf,
    lockfile: PathBuf,
    cache_initial: ManifestCacheEvidence,
    package_keys: BTreeSet<String>,
}

#[derive(Debug, Clone)]
struct LockedRegistryPackage {
    source: String,
    name: String,
    version: String,
    checksum: String,
}

#[derive(Debug, Clone)]
struct PackageCacheEvidence {
    package: LockedRegistryPackage,
    candidate_count: usize,
    cache_path: Option<PathBuf>,
    computed_checksum: Option<String>,
    status: String,
}

#[derive(Debug, Clone)]
struct ManifestCacheEvidence {
    status: String,
    fetch_required: bool,
    lockfile_sha256: Option<String>,
    locked_registry_package_count: usize,
    cache_hit_count: usize,
    cache_miss_count: usize,
    packages: Vec<PackageCacheEvidence>,
    errors: Vec<String>,
}

pub(crate) fn run(args: &[String]) -> ExitCode {
    if args.first().is_some_and(|arg| is_help_arg(arg)) {
        print!("{USAGE}");
        return ExitCode::SUCCESS;
    }

    let args = match parse_args(args) {
        Ok(args) => args,
        Err(message) => {
            eprintln!("targo trust verify cargo-cache: {message}");
            eprint!("{USAGE}");
            return ExitCode::from(2);
        }
    };

    match run_inner(&args) {
        Ok(report) => {
            let status =
                report.get("status").and_then(Value::as_str).unwrap_or("failed").to_string();
            if let Err(error) = write_reports(&args, &report) {
                eprintln!("targo trust verify cargo-cache: failed to write report: {error}");
                return ExitCode::from(2);
            }
            if status == "passed" {
                println!(
                    "targo trust verify cargo-cache: materialized registry-only seed at {}",
                    args.cargo_home.display()
                );
                ExitCode::SUCCESS
            } else {
                eprintln!("targo trust verify cargo-cache: materialization failed");
                if let Some(errors) = report.get("errors").and_then(Value::as_array) {
                    for error in errors.iter().filter_map(Value::as_str) {
                        eprintln!("  - {error}");
                    }
                }
                ExitCode::FAILURE
            }
        }
        Err(error) => {
            eprintln!("targo trust verify cargo-cache: {error}");
            ExitCode::from(2)
        }
    }
}

fn parse_args(args: &[String]) -> Result<Args, String> {
    let mut repo_root = None;
    let mut cargo_home = None;
    let mut json_output = None;
    let mut index = 0;
    while index < args.len() {
        match args[index].as_str() {
            "-h" | "--help" | "help" => {
                return Err("help must be the first argument".to_string());
            }
            "--repo-root" => {
                let Some(value) = args.get(index + 1) else {
                    return Err("--repo-root requires a path".to_string());
                };
                repo_root = Some(PathBuf::from(value));
                index += 2;
            }
            "--cargo-home" => {
                let Some(value) = args.get(index + 1) else {
                    return Err("--cargo-home requires a path".to_string());
                };
                cargo_home = Some(PathBuf::from(value));
                index += 2;
            }
            "--json-output" => {
                let Some(value) = args.get(index + 1) else {
                    return Err("--json-output requires a path".to_string());
                };
                json_output = Some(PathBuf::from(value));
                index += 2;
            }
            value if value.starts_with("--repo-root=") => {
                repo_root = Some(PathBuf::from(value.trim_start_matches("--repo-root=")));
                index += 1;
            }
            value if value.starts_with("--cargo-home=") => {
                cargo_home = Some(PathBuf::from(value.trim_start_matches("--cargo-home=")));
                index += 1;
            }
            value if value.starts_with("--json-output=") => {
                json_output = Some(PathBuf::from(value.trim_start_matches("--json-output=")));
                index += 1;
            }
            other => return Err(format!("unknown argument `{other}`")),
        }
    }

    let current = env::current_dir().map_err(|error| format!("failed to read cwd: {error}"))?;
    let repo_root = repo_root.unwrap_or_else(|| current.clone());
    let repo_root = resolve_path(&repo_root, &current);
    let cargo_home = cargo_home.ok_or_else(|| "--cargo-home is required".to_string())?;
    let cargo_home = resolve_path(&cargo_home, &repo_root);
    let json_output = json_output.map(|path| resolve_path(&path, &repo_root));

    Ok(Args { repo_root, cargo_home, json_output })
}

fn run_inner(args: &Args) -> Result<Value, String> {
    let repo_root = canonicalize_existing_dir(&args.repo_root, "repo root")?;
    validate_cargo_home(&repo_root, &args.cargo_home)?;
    fs::create_dir_all(&args.cargo_home).map_err(|error| {
        format!("failed to create cargo home {}: {error}", args.cargo_home.display())
    })?;
    let cargo_home = canonicalize_existing_dir(&args.cargo_home, "cargo home")?;

    let mut errors = Vec::new();
    let toolchain = match detect_stage2_toolchain(&repo_root) {
        Ok(toolchain) => toolchain,
        Err(error) => {
            errors.push(error);
            return Ok(report_json(
                &repo_root,
                &cargo_home,
                None,
                &[],
                &errors,
                &RequiredToolIdentityAudit::default(),
            ));
        }
    };
    let mut tool_identity_audit = required_tool_identities(&toolchain);
    errors.extend(tool_identity_audit.errors.iter().cloned());
    if !tool_identity_audit.errors.is_empty() {
        return Ok(report_json(
            &repo_root,
            &cargo_home,
            Some(&toolchain),
            &[],
            &errors,
            &tool_identity_audit,
        ));
    }

    let manifest_jobs = full_verify_manifests(&repo_root)
        .into_iter()
        .enumerate()
        .map(|(manifest_index, (lockfile, manifest))| {
            let cache_initial = cache_evidence_for_lockfile(&cargo_home, &lockfile);
            let package_keys = package_keys_for_evidence(&cache_initial);
            ManifestJob { manifest_index, manifest, lockfile, cache_initial, package_keys }
        })
        .collect::<Vec<_>>();
    if manifest_jobs.is_empty() {
        errors.push("no full-verify lockfile manifests were found".to_string());
    }

    let mut fetch_records = Vec::new();
    let mut successful_fetches = Vec::<(PathBuf, BTreeSet<String>)>::new();
    for (plan_position, job_index) in plan_fetch_order(&manifest_jobs).into_iter().enumerate() {
        let job = &manifest_jobs[job_index];
        let cache_before = cache_evidence_for_lockfile(&cargo_home, &job.lockfile);
        let covered_by_manifest =
            if job.cache_initial.fetch_required && !cache_before.fetch_required {
                covering_manifest(&successful_fetches, &job.package_keys)
            } else {
                None
            };
        let record = if cache_before.fetch_required {
            let targo_identity = tool_identity_audit
                .captured
                .iter()
                .find(|tool| tool.name == "targo")
                .expect("successful required-tool audit captured targo");
            run_fetch(
                &toolchain,
                targo_identity,
                &cargo_home,
                &repo_root,
                job,
                plan_position,
                cache_before,
            )
        } else {
            let skip_reason = if !job.cache_initial.fetch_required {
                "initial-cache-hit"
            } else if covered_by_manifest.is_some() {
                "planned-prior-fetch-cache-hit"
            } else {
                "current-cache-hit"
            };
            skipped_fetch_record(
                &toolchain,
                job,
                plan_position,
                cache_before,
                skip_reason,
                covered_by_manifest,
            )
        };
        if record.status != "passed" {
            errors.push(format!(
                "cargo cache fetch failed for {}",
                repo_relative(&job.manifest, &repo_root)
            ));
        } else if record.cache_after.fetch_required {
            errors.push(format!(
                "cargo cache fetch did not produce machine-checkable cache-hit evidence for {}",
                repo_relative(&job.manifest, &repo_root)
            ));
        }
        if record.fetch_executed && record.status == "passed" && !record.cache_after.fetch_required
        {
            successful_fetches
                .push((record.manifest.clone(), package_keys_for_evidence(&record.cache_after)));
        }
        fetch_records.push(record);
    }
    fetch_records.sort_by_key(|record| record.manifest_index);

    if !cargo_home.join("registry/index").is_dir() {
        errors.push(format!(
            "materialized cargo home is missing registry/index: {}",
            cargo_home.join("registry/index").display()
        ));
    }
    if !cargo_home.join("registry/cache").is_dir() {
        errors.push(format!(
            "materialized cargo home is missing registry/cache: {}",
            cargo_home.join("registry/cache").display()
        ));
    }
    if cargo_home.join("git").exists() {
        errors.push(format!(
            "materialized cargo home contains Cargo git checkout/cache state: {}",
            cargo_home.join("git").display()
        ));
    }
    errors.extend(revalidate_captured_tool_identities(&mut tool_identity_audit));

    Ok(report_json(
        &repo_root,
        &cargo_home,
        Some(&toolchain),
        &fetch_records,
        &errors,
        &tool_identity_audit,
    ))
}

fn validate_cargo_home(repo_root: &Path, cargo_home: &Path) -> Result<(), String> {
    if same_path(repo_root, cargo_home) {
        return Err("cargo home must not be the repository root".to_string());
    }
    if let Some(home) = env::var_os("HOME") {
        let shared = PathBuf::from(home).join(".cargo");
        if same_path(&shared, cargo_home) {
            return Err(format!(
                "cargo home must be a dedicated seed, not the shared user Cargo cache: {}",
                cargo_home.display()
            ));
        }
    }
    if cargo_home.exists() && !cargo_home.is_dir() {
        return Err(format!("cargo home is not a directory: {}", cargo_home.display()));
    }
    if cargo_home.join("git").exists() {
        return Err(format!(
            "cargo home must be registry-only and must not contain git cache state: {}",
            cargo_home.join("git").display()
        ));
    }
    Ok(())
}

fn detect_stage2_toolchain(repo_root: &Path) -> Result<TrustToolchain, String> {
    let trustc = discover_unique_repo_stage2_tool(repo_root, "trustc")?.ok_or_else(|| {
        format!(
            "could not find executable canonical stage2 trustc under {}/build/*/stage2/bin",
            repo_root.display()
        )
    })?;
    let linked = LinkedTrustToolchainStatus {
        status: LinkedTrustToolchainStatusKind::Visible,
        rustc: Some(trustc.clone()),
        detail: None,
    };
    let surface = detect_linked_trust_cargo_surface(&linked);
    if !surface.ready || !matches!(surface.kind, LinkedTrustCargoSurfaceKind::Stage2Ready) {
        return Err(format!(
            "stage2 Trust cargo surface is not release-ready: {}",
            surface.detail.as_deref().unwrap_or_else(|| surface.kind.label())
        ));
    }
    let sysroot = surface
        .sysroot
        .clone()
        .ok_or_else(|| "stage2 Trust cargo surface did not report a sysroot".to_string())?;
    let bin_dir = surface
        .bin_dir
        .clone()
        .ok_or_else(|| "stage2 Trust cargo surface did not report a bin directory".to_string())?;
    let targo = surface
        .targo
        .clone()
        .ok_or_else(|| "stage2 Trust cargo surface did not report canonical targo".to_string())?;
    Ok(TrustToolchain { surface, sysroot, bin_dir, trustc, targo })
}

fn full_verify_manifests(repo_root: &Path) -> Vec<(PathBuf, PathBuf)> {
    FULL_VERIFY_LOCKFILES
        .iter()
        .filter_map(|relative| {
            let lockfile = repo_root.join(relative);
            if !lockfile.is_file() {
                return None;
            }
            let manifest = lockfile.parent()?.join("Cargo.toml");
            manifest.is_file().then_some((lockfile, manifest))
        })
        .collect()
}

fn plan_fetch_order(jobs: &[ManifestJob]) -> Vec<usize> {
    let mut remaining = (0..jobs.len()).collect::<BTreeSet<_>>();
    let mut planned_present = BTreeSet::new();
    for job in jobs {
        for package in job.cache_initial.packages.iter().filter(|package| package.status == "hit") {
            planned_present.insert(package_key(&package.package));
        }
    }

    let mut order = Vec::with_capacity(jobs.len());
    while let Some(index) = next_fetch_plan_index(jobs, &remaining, &planned_present) {
        remaining.remove(&index);
        for key in &jobs[index].package_keys {
            planned_present.insert(key.clone());
        }
        order.push(index);
    }
    order
}

fn next_fetch_plan_index(
    jobs: &[ManifestJob],
    remaining: &BTreeSet<usize>,
    planned_present: &BTreeSet<String>,
) -> Option<usize> {
    let mut best = None;
    for index in remaining {
        let missing_count = jobs[*index].package_keys.difference(planned_present).count();
        let candidate = (*index, missing_count, jobs[*index].manifest_index);
        best = match best {
            None => Some(candidate),
            Some((_, best_missing, best_manifest_index))
                if missing_count > best_missing
                    || (missing_count == best_missing
                        && jobs[*index].manifest_index < best_manifest_index) =>
            {
                Some(candidate)
            }
            Some(best) => Some(best),
        };
    }
    best.map(|(index, _, _)| index)
}

fn package_keys_for_evidence(evidence: &ManifestCacheEvidence) -> BTreeSet<String> {
    evidence.packages.iter().map(|package| package_key(&package.package)).collect()
}

fn package_key(package: &LockedRegistryPackage) -> String {
    format!("{}\t{}\t{}\t{}", package.source, package.name, package.version, package.checksum)
}

fn covering_manifest(
    successful_fetches: &[(PathBuf, BTreeSet<String>)],
    package_keys: &BTreeSet<String>,
) -> Option<PathBuf> {
    successful_fetches
        .iter()
        .find(|(_, fetched_keys)| package_keys.is_subset(fetched_keys))
        .map(|(manifest, _)| manifest.clone())
}

fn run_fetch(
    toolchain: &TrustToolchain,
    targo_identity: &CapturedToolIdentity,
    cargo_home: &Path,
    repo_root: &Path,
    job: &ManifestJob,
    plan_position: usize,
    cache_before: ManifestCacheEvidence,
) -> FetchRecord {
    let command = fetch_command(toolchain, &job.manifest);
    let mut executed = false;
    let output = verify_captured_tool_identity(targo_identity, "before fetch").and_then(|()| {
        let mut child = Command::new(&toolchain.targo);
        child
            .arg("fetch")
            .arg("--manifest-path")
            .arg(&job.manifest)
            .arg("--locked")
            .current_dir(repo_root)
            .env("CARGO_HOME", cargo_home)
            .env("RUSTC", &toolchain.trustc)
            .env("RUSTDOC", tool_path(&toolchain.surface, "trustdoc").unwrap_or_default());
        executed = true;
        let command_result = bounded_process::output(
            &mut child,
            "stage2 targo fetch",
            64 * 1024 * 1024,
            Duration::from_secs(10 * 60),
        );
        let post_identity = verify_captured_tool_identity(targo_identity, "after fetch");
        match (command_result, post_identity) {
            (Ok(output), Ok(())) => Ok(output),
            (Err(command_error), Ok(())) => Err(command_error),
            (Ok(_), Err(identity_error)) => Err(identity_error),
            (Err(command_error), Err(identity_error)) => {
                Err(format!("{command_error}; {identity_error}"))
            }
        }
    });
    let cache_after = cache_evidence_for_lockfile(cargo_home, &job.lockfile);
    match output {
        Ok(output) => FetchRecord {
            manifest_index: job.manifest_index,
            plan_position,
            manifest: job.manifest.clone(),
            lockfile: job.lockfile.clone(),
            command,
            status: if output.status.success() { "passed" } else { "failed" }.to_string(),
            fetch_executed: executed,
            skip_reason: None,
            covered_by_manifest: None,
            exit_code: output.status.code(),
            stdout: String::from_utf8_lossy(&output.stdout).trim().to_string(),
            stderr: String::from_utf8_lossy(&output.stderr).trim().to_string(),
            cache_initial: job.cache_initial.clone(),
            cache_before,
            cache_after,
        },
        Err(error) => FetchRecord {
            manifest_index: job.manifest_index,
            plan_position,
            manifest: job.manifest.clone(),
            lockfile: job.lockfile.clone(),
            command,
            status: "failed".to_string(),
            fetch_executed: executed,
            skip_reason: None,
            covered_by_manifest: None,
            exit_code: None,
            stdout: String::new(),
            stderr: format!("failed to run authenticated stage2 targo fetch: {error}"),
            cache_initial: job.cache_initial.clone(),
            cache_before,
            cache_after,
        },
    }
}

fn skipped_fetch_record(
    toolchain: &TrustToolchain,
    job: &ManifestJob,
    plan_position: usize,
    cache_before: ManifestCacheEvidence,
    skip_reason: &str,
    covered_by_manifest: Option<PathBuf>,
) -> FetchRecord {
    FetchRecord {
        manifest_index: job.manifest_index,
        plan_position,
        manifest: job.manifest.clone(),
        lockfile: job.lockfile.clone(),
        command: fetch_command(toolchain, &job.manifest),
        status: "passed".to_string(),
        fetch_executed: false,
        skip_reason: Some(skip_reason.to_string()),
        covered_by_manifest,
        exit_code: Some(0),
        stdout: format!(
            "stage2 targo fetch skipped: locked registry crates already present in seed cache ({skip_reason})"
        ),
        stderr: String::new(),
        cache_initial: job.cache_initial.clone(),
        cache_after: cache_before.clone(),
        cache_before,
    }
}

fn fetch_command(toolchain: &TrustToolchain, manifest: &Path) -> Vec<String> {
    vec![
        toolchain.targo.display().to_string(),
        "fetch".to_string(),
        "--manifest-path".to_string(),
        manifest.display().to_string(),
        "--locked".to_string(),
    ]
}

fn cache_evidence_for_lockfile(cargo_home: &Path, lockfile: &Path) -> ManifestCacheEvidence {
    let lockfile_bytes =
        match crate::input_limits::read_bounded_file(lockfile, MAX_CARGO_LOCKFILE_BYTES) {
            Ok(bytes) => bytes,
            Err(error) => {
                return ManifestCacheEvidence {
                    status: "undetermined".to_string(),
                    fetch_required: true,
                    lockfile_sha256: None,
                    locked_registry_package_count: 0,
                    cache_hit_count: 0,
                    cache_miss_count: 0,
                    packages: Vec::new(),
                    errors: vec![format!(
                        "failed to read bounded lockfile {}: {error}",
                        lockfile.display()
                    )],
                };
            }
        };
    let lockfile_sha256 = Some(trust_types::digest::stable_sha256_hex(&lockfile_bytes));
    let lockfile_text = match std::str::from_utf8(&lockfile_bytes) {
        Ok(text) => text,
        Err(error) => {
            return ManifestCacheEvidence {
                status: "undetermined".to_string(),
                fetch_required: true,
                lockfile_sha256,
                locked_registry_package_count: 0,
                cache_hit_count: 0,
                cache_miss_count: 0,
                packages: Vec::new(),
                errors: vec![format!(
                    "lockfile {} is not valid UTF-8: {error}",
                    lockfile.display()
                )],
            };
        }
    };
    let packages = match locked_registry_packages(lockfile, lockfile_text) {
        Ok(packages) => packages,
        Err(error) => {
            return ManifestCacheEvidence {
                status: "undetermined".to_string(),
                fetch_required: true,
                lockfile_sha256,
                locked_registry_package_count: 0,
                cache_hit_count: 0,
                cache_miss_count: 0,
                packages: Vec::new(),
                errors: vec![error],
            };
        }
    };

    let mut package_evidence = Vec::with_capacity(packages.len());
    let mut hit_count = 0usize;
    let mut miss_count = 0usize;
    for package in packages {
        let evidence = package_cache_evidence(cargo_home, package);
        if evidence.status == "hit" {
            hit_count += 1;
        } else {
            miss_count += 1;
        }
        package_evidence.push(evidence);
    }

    let registry_dirs_present =
        cargo_home.join("registry/index").is_dir() && cargo_home.join("registry/cache").is_dir();
    let locked_registry_package_count = package_evidence.len();
    let status = if locked_registry_package_count == 0 {
        "not-required"
    } else if miss_count == 0 {
        "hit"
    } else {
        "miss"
    }
    .to_string();
    let fetch_required = match status.as_str() {
        "hit" => !registry_dirs_present,
        "not-required" => !registry_dirs_present,
        _ => true,
    };

    ManifestCacheEvidence {
        status,
        fetch_required,
        lockfile_sha256,
        locked_registry_package_count,
        cache_hit_count: hit_count,
        cache_miss_count: miss_count,
        packages: package_evidence,
        errors: Vec::new(),
    }
}

fn locked_registry_packages(
    lockfile: &Path,
    text: &str,
) -> Result<Vec<LockedRegistryPackage>, String> {
    let document = toml::from_str::<toml::Value>(text)
        .map_err(|error| format!("failed to parse lockfile {}: {error}", lockfile.display()))?;
    let Some(packages) = document.get("package").and_then(toml::Value::as_array) else {
        return Ok(Vec::new());
    };

    let mut locked = Vec::new();
    for package in packages {
        let Some(source) = package.get("source").and_then(toml::Value::as_str) else {
            continue;
        };
        if !source.starts_with("registry+") {
            continue;
        }
        let name = package
            .get("name")
            .and_then(toml::Value::as_str)
            .ok_or_else(|| format!("registry package in {} is missing name", lockfile.display()))?;
        let version = package.get("version").and_then(toml::Value::as_str).ok_or_else(|| {
            format!("registry package `{name}` in {} is missing version", lockfile.display())
        })?;
        let checksum = package.get("checksum").and_then(toml::Value::as_str).ok_or_else(|| {
            format!(
                "registry package `{name}` v{version} in {} is missing checksum",
                lockfile.display()
            )
        })?;
        locked.push(LockedRegistryPackage {
            source: source.to_string(),
            name: name.to_string(),
            version: version.to_string(),
            checksum: checksum.to_ascii_lowercase(),
        });
    }
    Ok(locked)
}

fn package_cache_evidence(
    cargo_home: &Path,
    package: LockedRegistryPackage,
) -> PackageCacheEvidence {
    let candidates = registry_cache_candidates(cargo_home, &package.name, &package.version);
    let mut cache_path = None;
    let mut computed_checksum = None;
    for candidate in &candidates {
        let Ok(digest) = bounded_sha256_file(candidate, MAX_REGISTRY_ARCHIVE_BYTES) else {
            continue;
        };
        if digest == package.checksum {
            cache_path = Some(candidate.clone());
            computed_checksum = Some(digest);
            break;
        }
    }
    let status = if cache_path.is_some() { "hit" } else { "miss" }.to_string();
    PackageCacheEvidence {
        package,
        candidate_count: candidates.len(),
        cache_path,
        computed_checksum,
        status,
    }
}

fn registry_cache_candidates(cargo_home: &Path, name: &str, version: &str) -> Vec<PathBuf> {
    let mut candidates = Vec::new();
    let archive_name = format!("{name}-{version}.crate");
    if let Ok(entries) = fs::read_dir(cargo_home.join("registry/cache")) {
        for entry in entries.flatten() {
            let candidate = entry.path().join(&archive_name);
            if candidate.is_file() {
                candidates.push(candidate);
            }
        }
    }
    candidates.sort();
    candidates
}

fn report_json(
    repo_root: &Path,
    cargo_home: &Path,
    toolchain: Option<&TrustToolchain>,
    fetch_records: &[FetchRecord],
    errors: &[String],
    tool_identity_audit: &RequiredToolIdentityAudit,
) -> Value {
    let status = if errors.is_empty() { "passed" } else { "failed" };
    json!({
        "schema": MATERIALIZATION_SCHEMA,
        "status": status,
        "generated_at_unix_ms": unix_ms(),
        "repo_root": repo_root.display().to_string(),
        "cargo_home": cargo_home.display().to_string(),
        "uses_upstream_cargo": false,
        "toolchain": toolchain.map(|toolchain| toolchain_json(toolchain, tool_identity_audit)).unwrap_or_else(|| {
            json!({
                "status": "failed",
                "uses_upstream_cargo": false,
            })
        }),
        "cache_evidence": cache_evidence_summary(fetch_records),
        "manifests": fetch_records.iter().map(|record| fetch_record_json(record, repo_root)).collect::<Vec<_>>(),
        "errors": errors,
    })
}

fn toolchain_json(
    toolchain: &TrustToolchain,
    tool_identity_audit: &RequiredToolIdentityAudit,
) -> Value {
    json!({
        "status": if toolchain.surface.ready && tool_identity_audit.errors.is_empty() {
            "passed"
        } else {
            "failed"
        },
        "uses_upstream_cargo": false,
        "sysroot": toolchain.sysroot.display().to_string(),
        "trustc_for_fetch": toolchain.trustc.display().to_string(),
        "targo": audited_tool_identity(tool_identity_audit, "targo"),
        "trustc": audited_tool_identity(tool_identity_audit, "trustc"),
        "trustdoc": audited_tool_identity(tool_identity_audit, "trustdoc"),
        "targo_trust": audited_tool_identity(tool_identity_audit, "targo-trust"),
        "trustd": audited_tool_identity(tool_identity_audit, "trustd"),
        "trustfmt": audited_tool_identity(tool_identity_audit, "trustfmt"),
        "targo_fmt": audited_tool_identity(tool_identity_audit, "targo-fmt"),
        "tippy": audited_tool_identity(tool_identity_audit, "tippy"),
        "targo_tippy": audited_tool_identity(tool_identity_audit, "targo-tippy"),
        "tippy_driver": audited_tool_identity(tool_identity_audit, "tippy-driver"),
        "trust_analyzer": audited_tool_identity(tool_identity_audit, "trust-analyzer"),
        "required_compatibility_aliases": required_aliases_json(&toolchain.bin_dir),
    })
}

fn audited_tool_identity(audit: &RequiredToolIdentityAudit, name: &str) -> Value {
    audit.identities.get(name).cloned().unwrap_or_else(|| {
        json!({
            "name": name,
            "path": null,
            "status": "failed",
            "diagnostic": "required identity evidence was not captured",
        })
    })
}

fn required_tool_identities(toolchain: &TrustToolchain) -> RequiredToolIdentityAudit {
    let required: Vec<(&'static str, Option<PathBuf>, &'static [&'static str])> = vec![
        ("targo", Some(toolchain.targo.clone()), &["--version"]),
        ("trustc", Some(toolchain.trustc.clone()), &["-Vv"]),
        ("trustdoc", tool_path(&toolchain.surface, "trustdoc"), &["--version"]),
        ("targo-trust", tool_path(&toolchain.surface, "targo-trust"), &["--version"]),
        ("trustd", tool_path(&toolchain.surface, "trustd"), &["--version"]),
        ("trustfmt", tool_path(&toolchain.surface, "trustfmt"), &["--version"]),
        ("targo-fmt", tool_path(&toolchain.surface, "targo-fmt"), &["--version"]),
        ("tippy", tool_path(&toolchain.surface, "tippy"), &["--version"]),
        ("targo-tippy", tool_path(&toolchain.surface, "targo-tippy"), &["--version"]),
        ("tippy-driver", tool_path(&toolchain.surface, "tippy-driver"), &["--version"]),
        ("trust-analyzer", tool_path(&toolchain.surface, "trust-analyzer"), &["--version"]),
    ];
    let mut audit = RequiredToolIdentityAudit::default();
    let mut captured = Vec::new();

    // Phase one is read-only: reject any missing, redirected, non-regular, or
    // unreadable leaf before executing even a version probe from this surface.
    for (name, path, version_args) in required {
        let Some(path) = path else {
            let error =
                format!("required tool identity `{name}` is missing from the stage2 surface");
            audit.errors.push(error.clone());
            audit.identities.insert(
                name.to_string(),
                json!({"name": name, "path": null, "status": "failed", "diagnostic": error}),
            );
            continue;
        };
        if !path_is_executable(&path) {
            let error = format!(
                "required tool identity `{name}` is not an exact regular executable: {}",
                path.display()
            );
            audit.errors.push(error.clone());
            audit.identities.insert(
                name.to_string(),
                json!({
                    "name": name,
                    "path": path.display().to_string(),
                    "status": "failed",
                    "diagnostic": error,
                }),
            );
            continue;
        }
        let Some(sha256) = exact_tool_sha256(&path) else {
            let error = format!(
                "required tool identity `{name}` has no stable exact-file sha256: {}",
                path.display()
            );
            audit.errors.push(error.clone());
            audit.identities.insert(
                name.to_string(),
                json!({
                    "name": name,
                    "path": path.display().to_string(),
                    "status": "failed",
                    "diagnostic": error,
                }),
            );
            continue;
        };
        captured.push(CapturedToolIdentity { name, path, version_args, sha256 });
    }

    if !audit.errors.is_empty() {
        for tool in &captured {
            audit.identities.insert(
                tool.name.to_string(),
                json!({
                    "name": tool.name,
                    "path": tool.path.display().to_string(),
                    "status": "not-probed",
                    "sha256": tool.sha256,
                    "version_probe_skipped": true,
                    "diagnostic": "version probe skipped because another required exact-file identity was invalid",
                }),
            );
        }
        audit.captured = captured;
        return audit;
    }

    // Phase two runs each version probe exactly once, then proves that the
    // exact executable bytes persisted across that probe.
    for tool in &captured {
        let mut command = Command::new(&tool.path);
        command.args(tool.version_args);
        let output = bounded_process::output(
            &mut command,
            &format!("required stage2 {} version probe", tool.name),
            64 * 1024,
            Duration::from_secs(10),
        );
        let post_sha256 = exact_tool_sha256(&tool.path);
        let unchanged = post_sha256.as_deref() == Some(tool.sha256.as_str());
        let (returncode, stdout, stderr, utf8_valid) = match output {
            Ok(output) => {
                let returncode = output.status.code();
                match (String::from_utf8(output.stdout), String::from_utf8(output.stderr)) {
                    (Ok(stdout), Ok(stderr)) => {
                        (returncode, stdout.trim().to_string(), stderr.trim().to_string(), true)
                    }
                    _ => (
                        returncode,
                        String::new(),
                        "required tool version output was not valid UTF-8".to_string(),
                        false,
                    ),
                }
            }
            Err(error) => (None, String::new(), error, false),
        };
        let passed = returncode == Some(0) && unchanged && utf8_valid;
        if returncode != Some(0) {
            audit.errors.push(format!(
                "required tool identity `{}` version probe failed with {:?}: {}",
                tool.name, returncode, stderr
            ));
        }
        if !unchanged {
            audit.errors.push(format!(
                "required tool identity `{}` changed during its version probe (expected sha256 {}, observed {:?})",
                tool.name, tool.sha256, post_sha256
            ));
        }
        if returncode.is_some() && !utf8_valid {
            audit.errors.push(format!(
                "required tool identity `{}` version output was not valid UTF-8",
                tool.name
            ));
        }
        audit.identities.insert(
            tool.name.to_string(),
            json!({
                "name": tool.name,
                "path": tool.path.display().to_string(),
                "status": if passed { "passed" } else { "failed" },
                "sha256": if unchanged { Some(tool.sha256.as_str()) } else { None },
                "version_returncode": returncode,
                "version_stdout": stdout,
                "version_stderr": stderr,
                "post_version_sha256_verified": unchanged,
                "version_output_utf8_valid": utf8_valid,
            }),
        );
    }
    audit.captured = captured;
    audit
}

fn verify_captured_tool_identity(tool: &CapturedToolIdentity, phase: &str) -> Result<(), String> {
    let observed = exact_tool_sha256(&tool.path).ok_or_else(|| {
        format!(
            "required tool `{}` could not be re-hashed {phase}: {}",
            tool.name,
            tool.path.display()
        )
    })?;
    if observed != tool.sha256 {
        return Err(format!(
            "required tool `{}` changed {phase} (expected sha256 {}, observed {observed})",
            tool.name, tool.sha256
        ));
    }
    Ok(())
}

fn revalidate_captured_tool_identities(audit: &mut RequiredToolIdentityAudit) -> Vec<String> {
    let outcomes = audit
        .captured
        .iter()
        .map(|tool| (tool.name, verify_captured_tool_identity(tool, "after cache materialization")))
        .collect::<Vec<_>>();
    let mut errors = Vec::new();
    for (name, outcome) in outcomes {
        let identity = audit.identities.entry(name.to_string()).or_insert_with(|| {
            json!({
                "name": name,
                "status": "failed",
                "diagnostic": "required identity evidence was not captured",
            })
        });
        let Some(identity) = identity.as_object_mut() else {
            let error = format!("required tool identity `{name}` report evidence is malformed");
            *identity = json!({
                "name": name,
                "status": "failed",
                "post_materialization_sha256_verified": false,
                "diagnostic": error,
            });
            errors.push(error);
            continue;
        };
        match outcome {
            Ok(()) => {
                identity.insert("post_materialization_sha256_verified".to_string(), json!(true));
            }
            Err(error) => {
                identity.insert("status".to_string(), json!("failed"));
                identity.insert("post_materialization_sha256_verified".to_string(), json!(false));
                identity.insert("diagnostic".to_string(), json!(&error));
                errors.push(error);
            }
        }
    }
    audit.errors.extend(errors.iter().cloned());
    errors
}

fn required_aliases_json(bin_dir: &Path) -> Value {
    // Only these two same-sysroot aliases are part of the Trust toolchain
    // contract. Every secondary tool is intentionally Trust-named only and
    // retired upstream leaves are rejected by linked-surface discovery.
    let aliases = [("cargo", "targo"), ("rustc", "trustc")];
    let mut map = BTreeMap::new();
    for (alias, canonical) in aliases {
        let path = bin_dir.join(host_executable_name(alias));
        let canonical_path = bin_dir.join(host_executable_name(canonical));
        let bound = compatibility_alias_binds(&path, &canonical_path);
        map.insert(
            alias,
            json!({
                "path": path.display().to_string(),
                "canonical_tool": canonical_path.display().to_string(),
                "identity_bound": bound,
                "status": if bound { "passed" } else { "failed" },
            }),
        );
    }
    json!(map)
}

fn compatibility_alias_binds(alias: &Path, canonical: &Path) -> bool {
    if !path_is_executable_target(alias) || !path_is_executable(canonical) {
        return false;
    }
    let Some(alias) = fs::canonicalize(alias).ok() else {
        return false;
    };
    let Some(canonical) = fs::canonicalize(canonical).ok() else {
        return false;
    };
    if alias == canonical {
        return true;
    }
    exact_tool_sha256(&alias)
        .zip(exact_tool_sha256(&canonical))
        .is_some_and(|(alias, canonical)| alias == canonical)
}

fn fetch_record_json(record: &FetchRecord, repo_root: &Path) -> Value {
    json!({
        "manifest_index": record.manifest_index,
        "plan_position": record.plan_position,
        "manifest": repo_relative(&record.manifest, repo_root),
        "lockfile": repo_relative(&record.lockfile, repo_root),
        "command": &record.command,
        "status": &record.status,
        "fetch_executed": record.fetch_executed,
        "initial_fetch_required": record.cache_initial.fetch_required,
        "skip_reason": &record.skip_reason,
        "covered_by_manifest": record.covered_by_manifest.as_ref().map(|path| repo_relative(path, repo_root)),
        "exit_code": record.exit_code,
        "stdout": &record.stdout,
        "stderr": &record.stderr,
        "cache_status": &record.cache_after.status,
        "cache_initial": manifest_cache_evidence_json(&record.cache_initial),
        "cache_before": manifest_cache_evidence_json(&record.cache_before),
        "cache_after": manifest_cache_evidence_json(&record.cache_after),
    })
}

fn cache_evidence_summary(fetch_records: &[FetchRecord]) -> Value {
    let fetches_executed = fetch_records.iter().filter(|record| record.fetch_executed).count();
    let fetches_skipped = fetch_records.len().saturating_sub(fetches_executed);
    let initial_fetches_required =
        fetch_records.iter().filter(|record| record.cache_initial.fetch_required).count();
    let planned_fetches_avoided = fetch_records
        .iter()
        .filter(|record| {
            record.cache_initial.fetch_required
                && !record.fetch_executed
                && !record.cache_after.fetch_required
        })
        .count();
    let manifest_hits_before =
        fetch_records.iter().filter(|record| record.cache_initial.status == "hit").count();
    let manifest_misses_before =
        fetch_records.iter().filter(|record| record.cache_initial.status == "miss").count();
    let manifest_hits_after =
        fetch_records.iter().filter(|record| record.cache_after.status == "hit").count();
    let manifest_misses_after =
        fetch_records.iter().filter(|record| record.cache_after.status == "miss").count();
    let locked_registry_packages = fetch_records
        .iter()
        .map(|record| record.cache_after.locked_registry_package_count)
        .sum::<usize>();
    let package_hits_after =
        fetch_records.iter().map(|record| record.cache_after.cache_hit_count).sum::<usize>();
    let package_misses_after =
        fetch_records.iter().map(|record| record.cache_after.cache_miss_count).sum::<usize>();
    json!({
        "schema": CACHE_HIT_MISS_SCHEMA,
        "machine_checkable": fetch_records.iter().all(|record| !record.cache_after.fetch_required),
        "fetch_plan": {
            "schema": FETCH_PLAN_SCHEMA,
            "strategy": "largest-currently-missing-registry-set-first",
            "reordered": fetch_records.iter().any(|record| record.plan_position != record.manifest_index),
            "initial_fetches_required": initial_fetches_required,
            "planned_fetches_avoided": planned_fetches_avoided,
        },
        "initial_fetches_required": initial_fetches_required,
        "planned_fetches_avoided": planned_fetches_avoided,
        "fetches_executed": fetches_executed,
        "fetches_skipped": fetches_skipped,
        "manifest_hits_before": manifest_hits_before,
        "manifest_misses_before": manifest_misses_before,
        "manifest_hits_after": manifest_hits_after,
        "manifest_misses_after": manifest_misses_after,
        "locked_registry_packages": locked_registry_packages,
        "package_hits_after": package_hits_after,
        "package_misses_after": package_misses_after,
    })
}

fn manifest_cache_evidence_json(evidence: &ManifestCacheEvidence) -> Value {
    json!({
        "status": &evidence.status,
        "fetch_required": evidence.fetch_required,
        "lockfile_sha256": &evidence.lockfile_sha256,
        "locked_registry_package_count": evidence.locked_registry_package_count,
        "cache_hit_count": evidence.cache_hit_count,
        "cache_miss_count": evidence.cache_miss_count,
        "packages": evidence.packages.iter().map(package_cache_evidence_json).collect::<Vec<_>>(),
        "errors": &evidence.errors,
    })
}

fn package_cache_evidence_json(evidence: &PackageCacheEvidence) -> Value {
    json!({
        "name": &evidence.package.name,
        "version": &evidence.package.version,
        "source": &evidence.package.source,
        "checksum": &evidence.package.checksum,
        "candidate_count": evidence.candidate_count,
        "cache_path": evidence.cache_path.as_ref().map(|path| path.display().to_string()),
        "computed_checksum": &evidence.computed_checksum,
        "status": &evidence.status,
    })
}

fn write_reports(args: &Args, report: &Value) -> io::Result<()> {
    fs::create_dir_all(&args.cargo_home)?;
    let proof_path = args.cargo_home.join(MATERIALIZATION_PROOF);
    write_json(&proof_path, report)?;
    if let Some(path) = &args.json_output {
        write_json(path, report)?;
    }
    Ok(())
}

fn write_json(path: &Path, report: &Value) -> io::Result<()> {
    let mut text = serde_json::to_string_pretty(report)?;
    text.push('\n');
    durable_io::atomic_write_private(path, text.as_bytes())
}

fn tool_path(surface: &LinkedTrustCargoSurfaceStatus, name: &str) -> Option<PathBuf> {
    surface
        .required_tools
        .iter()
        .chain(surface.optional_tools.iter())
        .find(|tool| tool.name == name)
        .and_then(|tool| {
            (tool.status == LinkedTrustSurfaceToolStatusKind::Present)
                .then(|| tool.path.clone())
                .flatten()
        })
}

fn canonicalize_existing_dir(path: &Path, label: &str) -> Result<PathBuf, String> {
    let path = fs::canonicalize(path)
        .map_err(|error| format!("failed to canonicalize {label} {}: {error}", path.display()))?;
    if !path.is_dir() {
        return Err(format!("{label} is not a directory: {}", path.display()));
    }
    Ok(path)
}

fn resolve_path(path: &Path, base: &Path) -> PathBuf {
    if path.is_absolute() { path.to_path_buf() } else { base.join(path) }
}

fn same_path(left: &Path, right: &Path) -> bool {
    let left = fs::canonicalize(left).unwrap_or_else(|_| left.to_path_buf());
    let right = fs::canonicalize(right).unwrap_or_else(|_| right.to_path_buf());
    left == right
}

fn repo_relative(path: &Path, repo_root: &Path) -> String {
    path.strip_prefix(repo_root).unwrap_or(path).display().to_string()
}

fn bounded_sha256_file(path: &Path, max_bytes: u64) -> io::Result<String> {
    let before = fs::symlink_metadata(path)?;
    if before.file_type().is_symlink() || !before.file_type().is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "digest input is not an exact regular file",
        ));
    }
    if before.len() > max_bytes {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("digest input exceeds the {max_bytes}-byte safety limit"),
        ));
    }
    let mut file = fs::File::open(path)?;
    let opened = file.metadata()?;
    if !opened.file_type().is_file() || !same_file_identity(&before, &opened) {
        return Err(io::Error::other("digest input changed while it was opened"));
    }
    let mut hasher = Sha256::new();
    let copied = io::copy(&mut (&mut file).take(before.len().saturating_add(1)), &mut hasher)?;
    if copied != before.len() {
        return Err(io::Error::other("digest input length changed while it was hashed"));
    }
    let after = fs::symlink_metadata(path)?;
    if after.file_type().is_symlink()
        || !after.file_type().is_file()
        || !same_file_identity(&before, &after)
        || after.len() != before.len()
    {
        return Err(io::Error::other("digest input changed while it was hashed"));
    }
    Ok(format!("{:x}", hasher.finalize()))
}


fn exact_tool_sha256(path: &Path) -> Option<String> {
    const MAX_TOOL_BYTES: u64 = 1024 * 1024 * 1024;
    let before = fs::symlink_metadata(path).ok()?;
    if before.file_type().is_symlink()
        || !before.file_type().is_file()
        || before.len() == 0
        || before.len() > MAX_TOOL_BYTES
    {
        return None;
    }
    let mut file = fs::File::open(path).ok()?;
    let opened = file.metadata().ok()?;
    if !opened.file_type().is_file() || !same_file_identity(&before, &opened) {
        return None;
    }
    let mut hasher = Sha256::new();
    let copied = io::copy(&mut (&mut file).take(before.len().checked_add(1)?), &mut hasher).ok()?;
    if copied != before.len() {
        return None;
    }
    let after = fs::symlink_metadata(path).ok()?;
    if after.file_type().is_symlink()
        || !after.file_type().is_file()
        || !same_file_identity(&before, &after)
        || after.len() != before.len()
    {
        return None;
    }
    Some(format!("{:x}", hasher.finalize()))
}

#[cfg(unix)]
fn same_file_identity(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    use std::os::unix::fs::MetadataExt;

    left.dev() == right.dev() && left.ino() == right.ino()
}

#[cfg(not(unix))]
fn same_file_identity(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    left.is_file() && right.is_file() && left.len() == right.len()
}

fn unix_ms() -> u128 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_millis())
        .unwrap_or_default()
}

fn is_help_arg(arg: &str) -> bool {
    matches!(arg, "help" | "-h" | "--help")
}

fn host_executable_name(stem: &str) -> String {
    if cfg!(windows) { format!("{stem}.exe") } else { stem.to_string() }
}

fn path_is_executable(path: &Path) -> bool {
    let Ok(metadata) = fs::symlink_metadata(path) else {
        return false;
    };
    if metadata.file_type().is_symlink() || !metadata.file_type().is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        metadata.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        true
    }
}

fn path_is_executable_target(path: &Path) -> bool {
    let Ok(metadata) = fs::metadata(path) else {
        return false;
    };
    if !metadata.file_type().is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        metadata.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    #[test]
    fn materializes_registry_only_seed_with_stage2_targo() {
        let temp =
            tempfile::Builder::new().prefix("targo-trust-cargo-cache-").tempdir().expect("tempdir");
        let repo = temp.path().join("repo");
        let bin = repo.join("build/host/stage2/bin");
        fs::create_dir_all(&bin).expect("stage2 bin");
        fs::write(
            repo.join("Cargo.toml"),
            "[package]\nname='demo'\nversion='0.0.0'\nedition='2021'\n",
        )
        .expect("manifest");
        let crate_payload = "demo dep crate\n";
        let crate_checksum = trust_types::digest::stable_sha256_hex(crate_payload.as_bytes());
        fs::write(
            repo.join("Cargo.lock"),
            format!(
                r#"# This file is automatically @generated by Cargo.
version = 3

[[package]]
name = "demo-dep"
version = "1.0.0"
source = "registry+https://github.com/rust-lang/crates.io-index"
checksum = "{crate_checksum}"
"#
            ),
        )
        .expect("lock");
        write_fake_stage2_tools(&bin);

        let cargo_home = temp.path().join("seed-home");
        let json_output = temp.path().join("report.json");
        let status = run(&[
            "--repo-root".to_string(),
            repo.display().to_string(),
            "--cargo-home".to_string(),
            cargo_home.display().to_string(),
            "--json-output".to_string(),
            json_output.display().to_string(),
        ]);

        assert_eq!(status, ExitCode::SUCCESS);
        let proof_path = cargo_home.join(MATERIALIZATION_PROOF);
        assert!(proof_path.is_file());
        assert!(json_output.is_file());
        let proof: Value =
            serde_json::from_str(&fs::read_to_string(proof_path).expect("proof text"))
                .expect("proof json");
        assert_eq!(proof["schema"], MATERIALIZATION_SCHEMA);
        assert_eq!(proof["status"], "passed");
        assert_eq!(proof["uses_upstream_cargo"], false);
        assert_eq!(proof["toolchain"]["status"], "passed");
        assert_eq!(proof["toolchain"]["uses_upstream_cargo"], false);
        assert_eq!(proof["toolchain"]["targo_fmt"]["status"], "passed");
        assert_eq!(proof["toolchain"]["tippy_driver"]["status"], "passed");
        assert_eq!(
            proof["toolchain"]["required_compatibility_aliases"]["cargo"]["status"],
            "passed"
        );
        assert_eq!(
            proof["toolchain"]["required_compatibility_aliases"]["rustc"]["status"],
            "passed"
        );
        assert_eq!(
            proof["toolchain"]["required_compatibility_aliases"]
                .as_object()
                .expect("compatibility alias object")
                .len(),
            2
        );
        assert_eq!(proof["cache_evidence"]["schema"], CACHE_HIT_MISS_SCHEMA);
        assert_eq!(proof["cache_evidence"]["machine_checkable"], true);
        assert_eq!(proof["cache_evidence"]["fetches_executed"], 1);
        assert_eq!(proof["cache_evidence"]["fetches_skipped"], 0);
        assert_eq!(proof["cache_evidence"]["package_hits_after"], 1);
        assert_eq!(proof["cache_evidence"]["package_misses_after"], 0);
        assert_eq!(proof["manifests"][0]["fetch_executed"], true);
        assert_eq!(proof["manifests"][0]["cache_before"]["status"], "miss");
        assert_eq!(proof["manifests"][0]["cache_after"]["status"], "hit");
        let command = proof["manifests"][0]["command"].as_array().expect("command");
        let expected_targo = fs::canonicalize(bin.join("targo")).expect("canonical targo");
        assert_eq!(
            command[0].as_str().expect("targo command"),
            expected_targo.display().to_string()
        );

        let second_status = run(&[
            "--repo-root".to_string(),
            repo.display().to_string(),
            "--cargo-home".to_string(),
            cargo_home.display().to_string(),
            "--json-output".to_string(),
            json_output.display().to_string(),
        ]);
        assert_eq!(second_status, ExitCode::SUCCESS);
        let second: Value =
            serde_json::from_str(&fs::read_to_string(json_output).expect("second report text"))
                .expect("second report json");
        assert_eq!(second["cache_evidence"]["machine_checkable"], true);
        assert_eq!(second["cache_evidence"]["fetches_executed"], 0);
        assert_eq!(second["cache_evidence"]["fetches_skipped"], 1);
        assert_eq!(second["manifests"][0]["fetch_executed"], false);
        assert_eq!(second["manifests"][0]["cache_before"]["status"], "hit");
        assert_eq!(second["manifests"][0]["cache_after"]["status"], "hit");
        assert_eq!(
            fs::read_to_string(cargo_home.join("fetch-count")).expect("fetch count").trim(),
            "1",
            "second materialization should reuse the existing verified seed cache"
        );
    }

    #[cfg(unix)]
    #[test]
    fn required_tool_version_probe_failure_blocks_materialization_proof() {
        let temp = tempfile::Builder::new()
            .prefix("targo-trust-cargo-cache-tool-id-")
            .tempdir()
            .expect("tempdir");
        let repo = temp.path().join("repo");
        let bin = repo.join("build/host/stage2/bin");
        fs::create_dir_all(&bin).expect("stage2 bin");
        fs::write(
            repo.join("Cargo.toml"),
            "[package]\nname='demo'\nversion='0.0.0'\nedition='2021'\n",
        )
        .expect("manifest");
        let crate_payload = "demo dep crate\n";
        let crate_checksum = trust_types::digest::stable_sha256_hex(crate_payload.as_bytes());
        fs::write(
            repo.join("Cargo.lock"),
            lockfile_text(&[("demo-dep", "1.0.0", &crate_checksum)]),
        )
        .expect("lock");
        write_fake_stage2_tools(&bin);
        write_fake_version_failure_tool(&bin.join("trustfmt"));

        let cargo_home = temp.path().join("seed-home");
        let json_output = temp.path().join("report.json");
        let status = run(&[
            "--repo-root".to_string(),
            repo.display().to_string(),
            "--cargo-home".to_string(),
            cargo_home.display().to_string(),
            "--json-output".to_string(),
            json_output.display().to_string(),
        ]);

        assert_eq!(status, ExitCode::FAILURE);
        let proof: Value =
            serde_json::from_str(&fs::read_to_string(json_output).expect("report text"))
                .expect("report json");
        assert_eq!(proof["status"], "failed");
        assert_eq!(proof["toolchain"]["status"], "failed");
        assert_eq!(proof["toolchain"]["trustfmt"]["status"], "failed");
        assert_eq!(proof["cache_evidence"]["fetches_executed"], 0);
        assert!(
            !cargo_home.join("fetch-count").exists(),
            "identity failure must stop before targo fetch"
        );
        assert!(
            proof["errors"]
                .as_array()
                .expect("errors")
                .iter()
                .filter_map(Value::as_str)
                .any(|error| error
                    .contains("required tool identity `trustfmt` version probe failed"))
        );
    }

    #[cfg(unix)]
    #[test]
    fn failed_fetch_still_runs_post_identity_check_and_poisoned_toolchain_report() {
        let temp = tempfile::Builder::new()
            .prefix("targo-trust-cargo-cache-fetch-swap-")
            .tempdir()
            .expect("tempdir");
        let repo = temp.path().join("repo");
        let bin = repo.join("build/host/stage2/bin");
        fs::create_dir_all(&bin).expect("stage2 bin");
        fs::write(
            repo.join("Cargo.toml"),
            "[package]\nname='demo'\nversion='0.0.0'\nedition='2021'\n",
        )
        .expect("manifest");
        let crate_checksum = trust_types::digest::stable_sha256_hex(b"demo dep crate\n");
        fs::write(
            repo.join("Cargo.lock"),
            lockfile_text(&[("demo-dep", "1.0.0", &crate_checksum)]),
        )
        .expect("lock");
        write_fake_stage2_tools(&bin);
        write_self_replacing_fetch_tool(&bin.join("targo"));
        fs::copy(bin.join("targo"), bin.join("cargo")).expect("rebind cargo compatibility copy");

        let cargo_home = temp.path().join("seed-home");
        let json_output = temp.path().join("report.json");
        let status = run(&[
            "--repo-root".to_string(),
            repo.display().to_string(),
            "--cargo-home".to_string(),
            cargo_home.display().to_string(),
            "--json-output".to_string(),
            json_output.display().to_string(),
        ]);

        assert_eq!(status, ExitCode::FAILURE);
        let proof: Value =
            serde_json::from_str(&fs::read_to_string(json_output).expect("report text"))
                .expect("report json");
        assert_eq!(proof["status"], "failed");
        assert_eq!(proof["manifests"][0]["fetch_executed"], true);
        assert_eq!(proof["manifests"][0]["status"], "failed");
        assert!(
            proof["manifests"][0]["stderr"]
                .as_str()
                .is_some_and(|stderr| stderr.contains("changed after fetch")),
            "{}",
            proof["manifests"][0]["stderr"]
        );
        assert_eq!(proof["toolchain"]["status"], "failed");
        assert_eq!(proof["toolchain"]["targo"]["status"], "failed");
        assert_eq!(proof["toolchain"]["targo"]["post_materialization_sha256_verified"], false);
    }

    #[cfg(unix)]
    #[test]
    fn static_identity_defect_runs_neither_targo_nor_trustc_probe() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::Builder::new()
            .prefix("targo-trust-cargo-cache-static-id-")
            .tempdir()
            .expect("tempdir");
        let repo = temp.path().join("repo");
        let bin = repo.join("build/host/stage2/bin");
        fs::create_dir_all(&bin).expect("stage2 bin");
        write_fake_stage2_tools(&bin);
        let targo_marker = temp.path().join("targo-ran");
        let trustc_marker = temp.path().join("trustc-ran");
        write_marker_version_tool(&bin.join("targo"), &targo_marker);
        write_marker_version_tool(&bin.join("trustc"), &trustc_marker);
        fs::copy(bin.join("targo"), bin.join("cargo")).expect("rebind cargo compatibility copy");
        fs::copy(bin.join("trustc"), bin.join("rustc")).expect("rebind rustc compatibility copy");

        // Resolve the exact stage2 surface first, then model a same-user path
        // replacement before identity capture.
        let toolchain = detect_stage2_toolchain(&repo).expect("stage2 toolchain");
        let trustfmt = bin.join("trustfmt");
        fs::remove_file(&trustfmt).expect("remove trustfmt");
        symlink("tippy", &trustfmt).expect("redirect trustfmt leaf");

        let audit = required_tool_identities(&toolchain);
        assert!(!audit.errors.is_empty());
        assert!(
            audit
                .errors
                .iter()
                .any(|error| error.contains("trustfmt") && error.contains("exact regular")),
            "{:?}",
            audit.errors
        );
        assert!(!targo_marker.exists(), "targo version probe ran before static audit completed");
        assert!(!trustc_marker.exists(), "trustc version probe ran before static audit completed");
        assert_eq!(audit.identities["targo"]["status"], "not-probed");
        assert_eq!(audit.identities["trustc"]["status"], "not-probed");
    }

    #[cfg(unix)]
    #[test]
    fn persistent_tool_replacement_after_capture_fails_final_identity_gate() {
        let temp = tempfile::Builder::new()
            .prefix("targo-trust-cargo-cache-post-id-")
            .tempdir()
            .expect("tempdir");
        let repo = temp.path().join("repo");
        let bin = repo.join("build/host/stage2/bin");
        fs::create_dir_all(&bin).expect("stage2 bin");
        write_fake_stage2_tools(&bin);

        let toolchain = detect_stage2_toolchain(&repo).expect("stage2 toolchain");
        let mut audit = required_tool_identities(&toolchain);
        assert!(audit.errors.is_empty(), "{:?}", audit.errors);

        write_fake_version_failure_tool(&bin.join("targo"));
        let errors = revalidate_captured_tool_identities(&mut audit);
        assert!(
            errors.iter().any(|error| error.contains("targo") && error.contains("changed")),
            "{errors:?}"
        );
        assert_eq!(audit.identities["targo"]["status"], "failed");
        assert_eq!(audit.identities["targo"]["post_materialization_sha256_verified"], false);
        assert!(!audit.errors.is_empty());
    }

    #[cfg(unix)]
    #[test]
    fn fixed_materialization_report_symlink_cannot_clobber_target() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().expect("report symlink fixture");
        let cargo_home = temp.path().join("cargo-home");
        fs::create_dir(&cargo_home).expect("cargo home");
        let victim = temp.path().join("victim");
        fs::write(&victim, b"safe").expect("victim");
        symlink(&victim, cargo_home.join(MATERIALIZATION_PROOF)).expect("proof symlink");
        let args = Args { repo_root: temp.path().to_path_buf(), cargo_home, json_output: None };

        let error = write_reports(&args, &json!({"status": "failed"}))
            .expect_err("symlinked fixed proof must fail closed");
        assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
        assert_eq!(fs::read(&victim).expect("victim contents"), b"safe");
    }

    #[cfg(unix)]
    #[test]
    fn toolchain_json_keeps_prior_identity_blockers_fail_closed() {
        let temp = tempfile::Builder::new()
            .prefix("targo-trust-cargo-cache-toolchain-json-")
            .tempdir()
            .expect("tempdir");
        let repo = temp.path().join("repo");
        let bin = repo.join("build/host/stage2/bin");
        fs::create_dir_all(&bin).expect("stage2 bin");
        write_fake_stage2_tools(&bin);

        let toolchain = detect_stage2_toolchain(&repo).expect("stage2 toolchain");
        let mut audit = required_tool_identities(&toolchain);
        audit.errors.push("required tool identity `trustfmt` version probe failed".to_string());
        let value = toolchain_json(&toolchain, &audit);

        assert_eq!(value["status"], "failed");
        assert_eq!(value["trustfmt"]["status"], "passed");
    }

    #[cfg(unix)]
    #[test]
    fn plans_superset_lockfile_fetch_before_subset_to_avoid_redundant_fetch() {
        let temp = tempfile::Builder::new()
            .prefix("targo-trust-cargo-cache-plan-")
            .tempdir()
            .expect("tempdir");
        let repo = temp.path().join("repo");
        let bin = repo.join("build/host/stage2/bin");
        fs::create_dir_all(repo.join("targo-trust")).expect("targo-trust dir");
        fs::create_dir_all(&bin).expect("stage2 bin");
        fs::write(
            repo.join("Cargo.toml"),
            "[package]\nname='root-demo'\nversion='0.0.0'\nedition='2021'\n",
        )
        .expect("root manifest");
        fs::write(
            repo.join("targo-trust/Cargo.toml"),
            "[package]\nname='targo-demo'\nversion='0.0.0'\nedition='2021'\n",
        )
        .expect("targo manifest");
        let demo_checksum = trust_types::digest::stable_sha256_hex(b"demo dep crate\n");
        let extra_checksum = trust_types::digest::stable_sha256_hex(b"extra dep crate\n");
        fs::write(repo.join("Cargo.lock"), lockfile_text(&[("demo-dep", "1.0.0", &demo_checksum)]))
            .expect("root lock");
        fs::write(
            repo.join("targo-trust/Cargo.lock"),
            lockfile_text(&[
                ("demo-dep", "1.0.0", &demo_checksum),
                ("extra-dep", "2.0.0", &extra_checksum),
            ]),
        )
        .expect("targo lock");
        write_fake_stage2_tools(&bin);

        let cargo_home = temp.path().join("seed-home");
        let json_output = temp.path().join("report.json");
        let status = run(&[
            "--repo-root".to_string(),
            repo.display().to_string(),
            "--cargo-home".to_string(),
            cargo_home.display().to_string(),
            "--json-output".to_string(),
            json_output.display().to_string(),
        ]);

        assert_eq!(status, ExitCode::SUCCESS);
        let proof: Value =
            serde_json::from_str(&fs::read_to_string(json_output).expect("report text"))
                .expect("report json");
        assert_eq!(proof["cache_evidence"]["fetch_plan"]["schema"], FETCH_PLAN_SCHEMA);
        assert_eq!(proof["cache_evidence"]["fetch_plan"]["reordered"], true);
        assert_eq!(proof["cache_evidence"]["initial_fetches_required"], 2);
        assert_eq!(proof["cache_evidence"]["fetches_executed"], 1);
        assert_eq!(proof["cache_evidence"]["fetches_skipped"], 1);
        assert_eq!(proof["cache_evidence"]["planned_fetches_avoided"], 1);
        assert_eq!(
            fs::read_to_string(cargo_home.join("fetch-count")).expect("fetch count").trim(),
            "1",
            "planned superset fetch should cover the subset manifest"
        );

        let root_manifest = &proof["manifests"][0];
        assert_eq!(root_manifest["manifest"], "Cargo.toml");
        assert_eq!(root_manifest["manifest_index"], 0);
        assert_eq!(root_manifest["plan_position"], 1);
        assert_eq!(root_manifest["initial_fetch_required"], true);
        assert_eq!(root_manifest["fetch_executed"], false);
        assert_eq!(root_manifest["skip_reason"], "planned-prior-fetch-cache-hit");
        assert_eq!(root_manifest["covered_by_manifest"], "targo-trust/Cargo.toml");
        assert_eq!(root_manifest["cache_initial"]["status"], "miss");
        assert_eq!(root_manifest["cache_before"]["status"], "hit");
        assert_eq!(root_manifest["cache_after"]["status"], "hit");

        let superset_manifest = &proof["manifests"][1];
        assert_eq!(superset_manifest["manifest"], "targo-trust/Cargo.toml");
        assert_eq!(superset_manifest["manifest_index"], 1);
        assert_eq!(superset_manifest["plan_position"], 0);
        assert_eq!(superset_manifest["fetch_executed"], true);
        assert_eq!(superset_manifest["cache_initial"]["status"], "miss");
        assert_eq!(superset_manifest["cache_after"]["status"], "hit");
    }

    #[test]
    fn cache_evidence_rejects_oversized_sparse_inputs_without_reading_them() {
        let temp = tempfile::tempdir().expect("bounded cache fixture");
        let lockfile = temp.path().join("Cargo.lock");
        let lock = fs::File::create(&lockfile).expect("create sparse lockfile");
        lock.set_len(MAX_CARGO_LOCKFILE_BYTES as u64 + 1).expect("size sparse lockfile");
        let evidence = cache_evidence_for_lockfile(temp.path(), &lockfile);
        assert_eq!(evidence.status, "undetermined");
        assert!(evidence.fetch_required);
        assert!(
            evidence.errors.iter().any(|error| error.contains("safety limit")),
            "{:?}",
            evidence.errors
        );

        let cache_dir = temp.path().join("registry/cache/fake");
        fs::create_dir_all(&cache_dir).expect("cache directory");
        let archive = cache_dir.join("huge-1.0.0.crate");
        let archive_file = fs::File::create(&archive).expect("create sparse archive");
        archive_file.set_len(MAX_REGISTRY_ARCHIVE_BYTES + 1).expect("size sparse archive");
        let package = LockedRegistryPackage {
            source: "registry+https://example.invalid/index".to_string(),
            name: "huge".to_string(),
            version: "1.0.0".to_string(),
            checksum: "00".repeat(32),
        };
        let archive_evidence = package_cache_evidence(temp.path(), package);
        assert_eq!(archive_evidence.candidate_count, 1);
        assert_eq!(archive_evidence.status, "miss");
        assert_eq!(archive_evidence.computed_checksum, None);
    }

    fn lockfile_text(packages: &[(&str, &str, &str)]) -> String {
        let mut text =
            "# This file is automatically @generated by Cargo.\nversion = 3\n\n".to_string();
        for (name, version, checksum) in packages {
            text.push_str(&format!(
                r#"[[package]]
name = "{name}"
version = "{version}"
source = "registry+https://github.com/rust-lang/crates.io-index"
checksum = "{checksum}"

"#
            ));
        }
        text
    }

    #[cfg(unix)]
    fn write_fake_stage2_tools(bin: &Path) {
        for tool in [
            "trustc",
            "rustc",
            "targo",
            "cargo",
            "targo-trust",
            "trustd",
            "trustdoc",
            "trustfmt",
            "targo-fmt",
            "tippy",
            "targo-tippy",
            "tippy-driver",
            "trust-analyzer",
        ] {
            write_fake_stage2_tool(&bin.join(tool));
        }
    }

    #[cfg(unix)]
    fn write_fake_stage2_tool(path: &Path) {
        use std::os::unix::fs::PermissionsExt;

        let script = r#"#!/bin/sh
name="$(basename "$0")"
if [ "$name" = "targo" ] && [ "${1:-}" = "fetch" ]; then
    mkdir -p "$CARGO_HOME/registry/index/fake" "$CARGO_HOME/registry/cache/fake"
    manifest=""
    if [ "${2:-}" = "--manifest-path" ]; then
        manifest="${3:-}"
    fi
    printf 'demo dep crate\n' > "$CARGO_HOME/registry/cache/fake/demo-dep-1.0.0.crate"
    case "$manifest" in
        */targo-trust/Cargo.toml)
            printf 'extra dep crate\n' > "$CARGO_HOME/registry/cache/fake/extra-dep-2.0.0.crate"
            ;;
    esac
    count_file="$CARGO_HOME/fetch-count"
    count=0
    if [ -f "$count_file" ]; then
        count="$(cat "$count_file")"
    fi
    count=$((count + 1))
    printf '%s\n' "$count" > "$count_file"
    echo "fetch ok"
    exit 0
fi
case "$1" in
    --version|-Vv)
        echo "$name fake stage2"
        exit 0
        ;;
    *)
        echo "unexpected $name invocation: $*" >&2
        exit 3
        ;;
esac
"#;
        fs::write(path, script).expect("write fake tool");
        let mut permissions = fs::metadata(path).expect("fake metadata").permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(path, permissions).expect("chmod fake");
    }

    #[cfg(unix)]
    fn write_fake_version_failure_tool(path: &Path) {
        use std::os::unix::fs::PermissionsExt;

        let script = r#"#!/bin/sh
case "$1" in
    --version|-Vv)
        echo "version probe failed" >&2
        exit 17
        ;;
    *)
        echo "unexpected invocation: $*" >&2
        exit 3
        ;;
esac
"#;
        fs::write(path, script).expect("write failing fake tool");
        let mut permissions = fs::metadata(path).expect("fake metadata").permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(path, permissions).expect("chmod fake");
    }

    #[cfg(unix)]
    fn write_self_replacing_fetch_tool(path: &Path) {
        use std::os::unix::fs::PermissionsExt;

        let script = r#"#!/bin/sh
if [ "${1:-}" = "fetch" ]; then
    replacement="${0}.replacement"
    printf '#!/bin/sh\nexit 91\n' > "$replacement"
    chmod 755 "$replacement"
    mv "$replacement" "$0"
    echo 'fetch failed after replacing targo' >&2
    exit 17
fi
case "${1:-}" in
    --version|-Vv)
        echo "$(basename "$0") fake stage2"
        exit 0
        ;;
    *)
        exit 3
        ;;
esac
"#;
        fs::write(path, script).expect("write self-replacing fetch tool");
        fs::set_permissions(path, fs::Permissions::from_mode(0o755))
            .expect("chmod self-replacing fetch tool");
    }

    #[cfg(unix)]
    fn write_marker_version_tool(path: &Path, marker: &Path) {
        use std::os::unix::fs::PermissionsExt;

        let script = format!(
            "#!/bin/sh\nprintf ran > \"{}\"\nprintf '%s\\n' \"$(basename \"$0\") marker\"\n",
            marker.display()
        );
        fs::write(path, script).expect("write marker tool");
        let mut permissions = fs::metadata(path).expect("marker metadata").permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(path, permissions).expect("chmod marker tool");
    }
}
