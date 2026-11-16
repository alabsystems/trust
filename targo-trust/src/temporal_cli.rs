// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
//! `targo trust temporal` — inspect the canonical temporal engine dependency and
//! linkable-target boundary, or explicitly elaborate a bounded TLA+ invariant-safety
//! input into a zero-authority canonical Lean/Clean proposition image.
//!
//! The former generated-harness/embedded-ty execution route — and the automatic
//! link-time model inventory it consumed — are DELETED
//! (no deprecation limbo: a retired route is deleted, not kept as a fallback): a project-linked executable cannot
//! authenticate the source bytes rustc read or the prior/final build artifact,
//! so no such route may exist until trustc emits an authenticated manifest.
//!
//! New models use a Clean `Trust.Temporal.FiniteModel.ScalarModel` plus an
//! explicit `trust_spec_temporal::certify_clean_scalar_model_with_ty` call; the
//! caller owns the definition list it certifies. Project-authored
//! `examples/trust_models.rs` programs are also rejected because code supplying
//! its own verdict protocol is not independent evidence. The separate `ingest`
//! command is compilation only: it never supplies a proof verdict to this gate.

use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::time::Duration;

pub(crate) const UNBOUND_TEMPORAL_EVIDENCE: &str = "unbound build evidence: the canonical compiler does not yet emit an authenticated input/output manifest binding the generated temporal harness source, resolved dependency graph, ty identity, and executable bytes; automatic temporal results are non-evidentiary and cannot pass";

const TEMPORAL_HELP: &str = "\
targo trust temporal [path]
targo trust temporal ingest <spec.tla> --config <spec.cfg> [--out <image.json>]

Inspect the canonical temporal-engine dependency/linkable-target boundary in the
crate at <path> (default `.`) and enforce the fail-closed temporal evidence
boundary. This command does not generate or execute a model-check harness while
compiler-authenticated semantic-input/output binding is unavailable.

`temporal ingest` invokes a fresh selected-Trust-compiler sibling `ty`; its
executable-path identity is snapshotted and revalidated before and after the
bounded run. Ty elaborates the bounded invariant-safety TLA+ fragment into one
deterministic canonical Lean/Clean proposition image. This wrapper validates the
closed envelope, exact input bindings, basis structure, and digests; it does not
independently re-elaborate the Clean terms. Exit 0 means ELABORATED, not proved:
the image is fixed to `authority: none` and `verdict: ungraded`, and is never
accepted as build or proof evidence. Inherited `TY_*` evaluator controls are
removed by clearing the fresh child's environment and restoring only the
selected toolchain's required runtime-library path. The embedded Clean
environment identity is only its canonical public declaration projection plus
admission ledger; the separate executable endpoint check remains external.
Without `--out`, the validated image is written to stdout.

A canonical `trust-spec-temporal` dependency plus a linkable library is only an
opt-in signal; it is not proof that any model declaration was compiled.

Exit code 2 denotes usage, setup, or intentionally rejected unbound evidence.
Automatic temporal analysis cannot return proof-bearing success until trustc
emits an authenticated semantic input/output binding. Locked Cargo-compatible
inspection is routed through canonical sibling `targo`; ambient `cargo` is
never evidence.
";

/// Whether the crate ships the legacy, project-authored model harness. This is
/// detected only so it can be rejected with a migration diagnostic: accepting
/// verdict text from code under verification would let that code forge proof.
pub(crate) fn crate_has_retired_project_harness(path: &str) -> bool {
    Path::new(path).join("examples").join("trust_models.rs").is_file()
}

#[derive(Debug, serde::Deserialize)]
struct TemporalCargoMetadata {
    packages: Vec<TemporalMetadataPackage>,
    resolve: Option<TemporalMetadataResolve>,
}

#[derive(Debug, serde::Deserialize)]
struct TemporalMetadataPackage {
    id: String,
    name: String,
    manifest_path: PathBuf,
    #[serde(default)]
    targets: Vec<TemporalMetadataTarget>,
}

#[derive(Debug, serde::Deserialize)]
struct TemporalMetadataTarget {
    name: String,
    #[serde(default)]
    kind: Vec<String>,
    #[serde(default)]
    crate_types: Vec<String>,
}

#[derive(Debug, serde::Deserialize)]
struct TemporalMetadataResolve {
    nodes: Vec<TemporalMetadataNode>,
}

#[derive(Debug, serde::Deserialize)]
struct TemporalMetadataNode {
    id: String,
    #[serde(default)]
    deps: Vec<TemporalMetadataDependency>,
}

#[derive(Debug, serde::Deserialize)]
struct TemporalMetadataDependency {
    pkg: String,
    #[serde(default)]
    dep_kinds: Vec<TemporalMetadataDependencyKind>,
}

#[derive(Debug, serde::Deserialize)]
struct TemporalMetadataDependencyKind {
    kind: Option<String>,
}

/// Ask canonical Targo for the resolved dependency graph under the exact
/// feature/platform/config context. Raw TOML declarations are insufficient:
/// disabled optional and nonmatching target-specific dependencies are not
/// active proof inputs.
fn resolved_temporal_gate_target(
    root: &Path,
    metadata_context: &[String],
) -> Result<TemporalGateTarget, String> {
    let (rustc, targo) = crate::pipeline::discovery::discover_native_trust_toolchain_checked()?;
    let mut context = metadata_context.to_vec();
    if !context.iter().any(|arg| arg == "--filter-platform") {
        let platforms = match crate::pipeline::configured_cargo_build_target()? {
            Some(targets) => targets
                .split(',')
                .map(str::trim)
                .filter(|target| !target.is_empty())
                .map(ToOwned::to_owned)
                .collect::<Vec<_>>(),
            None => vec![crate::pipeline::selected_trustc_host_triple()?],
        };
        for platform in platforms {
            context.extend(["--filter-platform".to_string(), platform]);
        }
    }
    let mut command = temporal_metadata_command(&targo, &rustc, root, &context)?;
    let output = crate::bounded_process::output(
        &mut command,
        &format!("canonical temporal metadata query at {}", targo.display()),
        64 * 1024 * 1024,
        Duration::from_secs(5 * 60),
    )?;
    if !output.status.success() {
        return Err(format!(
            "canonical temporal metadata query failed with {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let metadata = serde_json::from_slice::<TemporalCargoMetadata>(&output.stdout)
        .map_err(|error| format!("canonical temporal metadata was invalid: {error}"))?;
    temporal_gate_target_from_metadata(root, &metadata)
}

/// The temporal gate's canonical `targo metadata` query for the package at
/// `root`, with `context` (feature, config and `--filter-platform` flags).
///
/// Built by `cargo_selection::selection_probe_command`, like package
/// selection: the authenticated trustc pinned, no rustc wrapper, and the
/// `[host]` rustflags refusal first. S9 re-review: this query used to inherit
/// ambient `RUSTFLAGS` and a config-file `build.rustc`, so an external
/// `-Zcodegen-backend` loaded the trust-mc dylib into trustc's target-info
/// query after every successful `targo trust build`. `--filter-platform`
/// evaluates target cfgs, so the query resolves the project's rustflags as
/// the build does (T14a: the environment, else the matching configured
/// tables), with the probe's empty lane, which keeps any external backend out
/// of its compiler: a `--cfg` that activates the temporal engine edge in the
/// build must activate it here, or the gate would pass that build as having
/// no temporal opt-in. The build's trust-cg codegen contract and strict safety
/// checks are not replayed, because this gate does not see the build's lane;
/// the query inherited neither before this change either.
pub(crate) fn temporal_metadata_command(
    targo: &Path,
    rustc: &Path,
    root: &Path,
    context: &[String],
) -> Result<Command, String> {
    let mut command =
        crate::pipeline::cargo_selection::selection_probe_command(targo, rustc, context)?;
    command.args(["metadata", "--format-version", "1", "--manifest-path"]);
    command.arg(root.join("Cargo.toml"));
    command.args(context);
    Ok(command)
}

fn canonical_temporal_engine_manifest() -> Result<PathBuf, String> {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .ok_or_else(|| "targo-trust manifest has no repository parent".to_string())?
        .join("crates/trust-spec-temporal/Cargo.toml")
        .canonicalize()
        .map_err(|error| {
            format!("repository-owned trust-spec-temporal manifest is unavailable: {error}")
        })
}

/// The pure pass-through/override decision of the build gate, factored out so the
/// fail-closed contract is unit-testable without a subprocess, ty, or toolchain.
///
/// - `build_code`: the build step's own exit code.
/// - `gate`: `None` if the gate did not run (crate not temporal); `Some(code)`
///   from the model-check harness.
///
/// Contract: a failed build is returned immediately without running a gate. If
/// the build passed, a gate that did not run or passed preserves success, while
/// a failed gate returns a nonzero code clamped into `1..=255`.
///
/// `gate_build` mirrors this exact decision over the opaque `ExitCode`; this pure
/// form exists so the fail-closed contract is unit-tested deterministically.
// Reference impl of the gate decision; exercised by unit tests below.
#[cfg(test)]
fn gate_outcome(build_code: i32, gate: Option<i32>) -> i32 {
    if build_code != 0 {
        return build_code;
    }
    match gate {
        None | Some(0) => 0,
        Some(c) => c.clamp(1, 255),
    }
}

pub(crate) fn run_temporal_subcommand(args: &[String]) -> ExitCode {
    let separator = args.iter().position(|arg| arg == "--").unwrap_or(args.len());
    if args[..separator].iter().any(|arg| arg == "--help" || arg == "-h") {
        print!("{TEMPORAL_HELP}");
        return ExitCode::SUCCESS;
    }
    if args.first().is_some_and(|arg| arg == "ingest") {
        return run_tla_clean_ingest(&args[1..]);
    }
    let (path, passthrough) = match parse_temporal_invocation(args) {
        Ok(parsed) => parsed,
        Err(error) => {
            eprintln!("targo trust temporal: {error}");
            return ExitCode::from(2);
        }
    };
    if !passthrough.is_empty() {
        eprintln!(
            "targo trust temporal: forwarded harness arguments are unavailable because the \
             unattested automatic execution route is retired"
        );
        return ExitCode::from(2);
    }

    eprintln!(
        "targo trust temporal: inspecting the resolved temporal engine dependency/linkable-target \
         boundary in `{path}` (no proof harness will be executed)..."
    );

    // Neither a generated project-linked harness nor a project-authored executable
    // can authenticate the source bytes rustc read or the final build artifact.
    let metadata_context = ["--locked".to_string()];
    match temporal_gate_target(Path::new(path), &metadata_context) {
        Ok(TemporalGateTarget::Explicit) => {
            eprintln!(
                "targo trust temporal: `{path}/examples/trust_models.rs` is a legacy, \
                 project-authored proof harness and is not accepted as proof evidence; migrate \
                 each model to a Clean `Trust.Temporal.FiniteModel.ScalarModel` and explicitly \
                 call `trust_spec_temporal::certify_clean_scalar_model_with_ty`"
            );
            ExitCode::from(2)
        }
        Ok(TemporalGateTarget::Automatic { package_id, library_crate_name }) => {
            let _ = (package_id, library_crate_name);
            // The automatic route is unconditionally non-evidentiary. Do not
            // make its deterministic rejection depend on whether a ty binary
            // happens to have been built or installed: no checker is executed,
            // and tool discovery cannot strengthen the missing build binding.
            eprintln!("targo trust temporal: {UNBOUND_TEMPORAL_EVIDENCE}");
            ExitCode::from(2)
        }
        Ok(TemporalGateTarget::None) => {
            eprintln!(
                "targo trust temporal: `{path}` has no active canonical `trust-spec-temporal` \
                 dependency with a linkable library target; temporal declarations were not \
                 inspected, and absence of an opt-in edge is absence of proof."
            );
            ExitCode::from(2)
        }
        Err(error) => {
            eprintln!("targo trust temporal: could not inspect `{path}`: {error}");
            ExitCode::from(2)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TlaCleanIngestInvocation {
    spec: PathBuf,
    config: PathBuf,
    out: Option<PathBuf>,
}

const TLA_CLEAN_SCHEMA: &str = "trust.tla-clean-compat/v1";
const TLA_CLEAN_AUTHORITY: &str = "none";
const TLA_CLEAN_INGESTION_AUTHORITY: &str = "zero-authority";
const TLA_CLEAN_VERDICT: &str = "ungraded";
const TLA_CLEAN_PROPOSITION_DESTINATION: &str = "lean:canonical-temporal-term";
const TLA_CLEAN_BASIS_ORDER: &str = "lexicographic-u64-tuples/v1";
const TLA_CLEAN_PROPOSITION_BASIS_SCHEMA: &str = "trust.tla-clean-proposition-basis/v1";
const TLA_CLEAN_TLA_ENVIRONMENT_SCHEMA: &str = "trust.tla-builtin-environment/v1";
const TLA_CLEAN_TLA_ENVIRONMENT_VERSION: u32 = 1;
const TLA_CLEAN_ADMITTED_BUILTIN_MODULES: &[&str] = &["Naturals"];
const TLA_CLEAN_KERNEL_ENVIRONMENT_SCHEMA: &str = "trust.clean-reflect-environment-identity/v1";
const TLA_CLEAN_KERNEL_ENVIRONMENT_VERSION: u32 = 1;
const TLA_CLEAN_KERNEL_ENVIRONMENT_CONTENT_ENCODING: &str =
    "clean.reflect-environment-content.compact-json/v1";
const TLA_CLEAN_TERM_ENCODING: &str = "clean.expr.compact-json/v1";
const TLA_CLEAN_PROPOSITION_ORDER: &str =
    "r-subset-safety_then_init-subset-r_then_r-closed-under-next/v1";
const TLA_CLEAN_SOURCE_MAX_BYTES: usize = 1024 * 1024;
const TLA_CLEAN_CONFIG_MAX_BYTES: usize = 256 * 1024;
const TLA_CLEAN_IMAGE_MAX_BYTES: usize = 64 * 1024 * 1024;
const TLA_CLEAN_TERM_MAX_BYTES: usize = 16 * 1024 * 1024;
const TLA_CLEAN_VARIABLE_CAP: usize = 64;
const TLA_CLEAN_STATE_CAP: u64 = 256;
const TLA_CLEAN_OBLIGATION_LEG_CAP: u64 = 4096;

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TlaCleanImage {
    schema: String,
    authority: String,
    ingestion_authority: String,
    verdict: String,
    proposition_destination: String,
    computational_destinations: Vec<String>,
    source: TlaCleanInput,
    config: TlaCleanInput,
    operators: TlaCleanOperators,
    variables: Vec<String>,
    sorts: Vec<TlaCleanSort>,
    basis: TlaCleanBasis,
    proposition_basis_sha256: String,
    tla_environment: TlaCleanTlaEnvironment,
    kernel_environment: TlaCleanKernelEnvironment,
    terms: TlaCleanTerms,
    artifact_sha256: String,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TlaCleanInput {
    utf8: String,
    sha256: String,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TlaCleanOperators {
    init: String,
    next: String,
    invariants: Vec<String>,
    effective_init: String,
    effective_next: String,
    effective_invariants: Vec<String>,
    constants: Vec<TlaCleanConstant>,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TlaCleanConstant {
    name: String,
    canonical_value: String,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TlaCleanTlaEnvironment {
    schema: String,
    version: u32,
    admitted_builtin_modules: Vec<String>,
    used_builtin_modules: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
enum TlaCleanKernelAdmission {
    Inductive,
    CheckedDefinition,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TlaCleanKernelLedgerEntry {
    name: String,
    admission: TlaCleanKernelAdmission,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TlaCleanKernelEnvironment {
    schema: String,
    version: u32,
    clean_kernel_version: String,
    tla_check_version: String,
    environment_schema_fingerprint: String,
    ledger: Vec<TlaCleanKernelLedgerEntry>,
    content_encoding: String,
    environment_content_sha256: String,
    identity_sha256: String,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum TlaCleanSort {
    Int,
    Enum { labels: Vec<String>, atom_kind: String },
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TlaCleanBasis {
    order: String,
    state_cap: u64,
    max_obligation_legs: u64,
    reachable_count: u64,
    init_domain_count: u64,
    next_domain_count: u64,
    obligation_leg_count: u64,
    max_r: Vec<u64>,
    reachable: Vec<Vec<u64>>,
    init_domain: Vec<Vec<u64>>,
    next_domain: Vec<Vec<u64>>,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TlaCleanTerms {
    encoding: String,
    proposition_order: String,
    init: TlaCleanTerm,
    next: TlaCleanTerm,
    safety: TlaCleanTerm,
    proposition: TlaCleanTerm,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TlaCleanTerm {
    bytes_hex: String,
    sha256: String,
}

fn parse_tla_clean_ingest_invocation(args: &[String]) -> Result<TlaCleanIngestInvocation, String> {
    let mut spec = None;
    let mut config = None;
    let mut out = None;
    let mut index = 0;
    while index < args.len() {
        match args[index].as_str() {
            "--config" => {
                index += 1;
                let value = args.get(index).ok_or("--config requires a path")?;
                if config.replace(PathBuf::from(value)).is_some() {
                    return Err("--config may be supplied only once".to_string());
                }
            }
            "--out" => {
                index += 1;
                let value = args.get(index).ok_or("--out requires a path")?;
                if out.replace(PathBuf::from(value)).is_some() {
                    return Err("--out may be supplied only once".to_string());
                }
            }
            "--" => {
                return Err(
                    "`temporal ingest` does not accept forwarded or positional arguments after `--`"
                        .to_string(),
                );
            }
            option if option.starts_with('-') => {
                return Err(format!("unknown ingest option `{option}`"));
            }
            operand => {
                if spec.replace(PathBuf::from(operand)).is_some() {
                    return Err(format!("unexpected extra TLA+ source `{operand}`"));
                }
            }
        }
        index += 1;
    }
    let spec = spec.ok_or("`temporal ingest` requires one <spec.tla> operand")?;
    let config = config.ok_or("`temporal ingest` requires --config <spec.cfg>")?;
    if spec.extension().and_then(|extension| extension.to_str()) != Some("tla") {
        return Err(format!("TLA+ source must have a `.tla` extension: {}", spec.display()));
    }
    if config.extension().and_then(|extension| extension.to_str()) != Some("cfg") {
        return Err(format!(
            "TLA+ configuration must have a `.cfg` extension: {}",
            config.display()
        ));
    }
    Ok(TlaCleanIngestInvocation { spec, config, out })
}

fn run_tla_clean_ingest(args: &[String]) -> ExitCode {
    let invocation = match parse_tla_clean_ingest_invocation(args) {
        Ok(invocation) => invocation,
        Err(error) => {
            eprintln!("targo trust temporal ingest: {error}");
            return ExitCode::from(2);
        }
    };
    if let Err(error) = reject_tla_clean_output_alias(&invocation) {
        eprintln!("targo trust temporal ingest: {error}");
        return ExitCode::from(2);
    }
    match elaborate_tla_clean_image(&invocation) {
        Ok(bytes) => {
            if let Some(path) = &invocation.out {
                if let Err(error) = crate::durable_io::atomic_write_private(path, &bytes) {
                    eprintln!(
                        "targo trust temporal ingest: could not publish {}: {error}",
                        path.display()
                    );
                    return ExitCode::from(2);
                }
                eprintln!(
                    "targo trust temporal ingest: elaborated zero-authority image at {} \
                     (authority=none, verdict=ungraded; this is not proof evidence)",
                    path.display()
                );
            } else {
                use std::io::Write as _;
                if let Err(error) = std::io::stdout().write_all(&bytes) {
                    eprintln!("targo trust temporal ingest: could not write image: {error}");
                    return ExitCode::from(2);
                }
                if !bytes.ends_with(b"\n") {
                    println!();
                }
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("targo trust temporal ingest: {error}");
            ExitCode::from(2)
        }
    }
}

fn reject_tla_clean_output_alias(invocation: &TlaCleanIngestInvocation) -> Result<(), String> {
    let Some(out) = invocation.out.as_deref() else {
        return Ok(());
    };
    for (label, input) in
        [("source", invocation.spec.as_path()), ("configuration", invocation.config.as_path())]
    {
        if paths_equivalent(out, input) {
            return Err(format!(
                "output {} aliases the TLA+ {label} {}; refusing to overwrite an input",
                out.display(),
                input.display()
            ));
        }
    }
    Ok(())
}

fn elaborate_tla_clean_image(invocation: &TlaCleanIngestInvocation) -> Result<Vec<u8>, String> {
    let source_bytes =
        crate::input_limits::read_bounded_file(&invocation.spec, TLA_CLEAN_SOURCE_MAX_BYTES)
            .map_err(|error| {
                format!(
                    "could not read bounded regular TLA+ source {}: {error}",
                    invocation.spec.display()
                )
            })?;
    let config_bytes =
        crate::input_limits::read_bounded_file(&invocation.config, TLA_CLEAN_CONFIG_MAX_BYTES)
            .map_err(|error| {
                format!(
                    "could not read bounded regular TLA+ configuration {}: {error}",
                    invocation.config.display()
                )
            })?;
    std::str::from_utf8(&source_bytes)
        .map_err(|error| format!("TLA+ source is not UTF-8: {error}"))?;
    std::str::from_utf8(&config_bytes)
        .map_err(|error| format!("TLA+ configuration is not UTF-8: {error}"))?;

    let scratch = tempfile::Builder::new()
        .prefix("targo-trust-tla-clean-ingest-")
        .tempdir()
        .map_err(|error| format!("could not create a private ingestion directory: {error}"))?;
    let source_snapshot = scratch.path().join("input.tla");
    let config_snapshot = scratch.path().join("input.cfg");
    let image_path = scratch.path().join("image.json");
    crate::durable_io::atomic_write_private(&source_snapshot, &source_bytes)
        .map_err(|error| format!("could not stage the exact TLA+ source bytes: {error}"))?;
    crate::durable_io::atomic_write_private(&config_snapshot, &config_bytes)
        .map_err(|error| format!("could not stage the exact TLA+ configuration bytes: {error}"))?;

    let discovery = crate::pipeline::discover_native_rustc_checked().ok_or_else(|| {
        "no canonical Trust compiler is available to anchor the sibling `ty` elaborator \
         (run `./x.py build` first)"
            .to_string()
    })?;
    let bin_dir = discovery.rustc.parent().ok_or_else(|| {
        format!(
            "selected Trust compiler has no containing directory: {}",
            discovery.rustc.display()
        )
    })?;
    let ty = bin_dir.join(crate::stage2_tools::host_executable_name("ty"));
    let ty_identity = crate::stage2_tools::snapshot_exact_executable(
        &ty,
        "TLA+ compatibility ingress",
        "sibling ty elaborator",
    )?;

    let mut command = Command::new(&ty);
    command.env_clear();
    crate::pipeline::apply_native_runtime_env(&mut command, &discovery.rustc);
    scrub_tla_clean_elaborator_env(&mut command);
    command
        .current_dir(scratch.path())
        .arg("tla-clean-ingest")
        .arg(&source_snapshot)
        .arg("--config")
        .arg(&config_snapshot)
        .arg("--out")
        .arg(&image_path);
    let run = crate::bounded_process::output(
        &mut command,
        &format!("bounded TLA+ compatibility elaboration with {}", ty.display()),
        8 * 1024 * 1024,
        Duration::from_secs(10 * 60),
    );
    crate::stage2_tools::revalidate_exact_executable(
        &ty_identity,
        "TLA+ compatibility ingress",
        "sibling ty elaborator",
    )?;
    let run = run?;
    if !run.status.success() {
        let stderr = String::from_utf8_lossy(&run.stderr);
        let stdout = String::from_utf8_lossy(&run.stdout);
        let detail = if stderr.trim().is_empty() { stdout.trim() } else { stderr.trim() };
        return Err(format!("sibling ty elaborator failed with {}: {detail}", run.status));
    }
    if !run.stdout.is_empty() {
        return Err("sibling ty elaborator wrote unexpected stdout beside its output image".into());
    }
    if !run.stderr.is_empty() {
        return Err(
            "sibling ty elaborator wrote unexpected stderr on successful elaboration".into()
        );
    }

    let image_bytes =
        crate::input_limits::read_bounded_file(&image_path, TLA_CLEAN_IMAGE_MAX_BYTES).map_err(
            |error| format!("could not read the bounded ty compatibility image: {error}"),
        )?;
    validate_tla_clean_image(&image_bytes, &source_bytes, &config_bytes)?;
    Ok(image_bytes)
}

fn scrub_tla_clean_elaborator_env(command: &mut Command) {
    let keys = std::env::vars_os()
        .map(|(key, _)| key)
        .chain(command.get_envs().map(|(key, _)| key.to_os_string()))
        .filter(|key| is_ty_control_environment_key(key))
        .collect::<Vec<_>>();
    for key in keys {
        command.env_remove(key);
    }
}

fn is_ty_control_environment_key(key: &OsStr) -> bool {
    key.to_string_lossy()
        .as_bytes()
        .get(..3)
        .is_some_and(|prefix| prefix.eq_ignore_ascii_case(b"TY_"))
}

fn validate_tla_clean_image(
    image_bytes: &[u8],
    source_bytes: &[u8],
    config_bytes: &[u8],
) -> Result<(), String> {
    if image_bytes.len() > TLA_CLEAN_IMAGE_MAX_BYTES {
        return Err(format!(
            "compatibility image exceeds the {TLA_CLEAN_IMAGE_MAX_BYTES}-byte safety limit"
        ));
    }
    let image: TlaCleanImage = serde_json::from_slice(image_bytes)
        .map_err(|error| format!("ty compatibility image violates its closed schema: {error}"))?;

    require_tla_image_tag("schema", &image.schema, TLA_CLEAN_SCHEMA)?;
    require_tla_image_tag("authority", &image.authority, TLA_CLEAN_AUTHORITY)?;
    require_tla_image_tag(
        "ingestion_authority",
        &image.ingestion_authority,
        TLA_CLEAN_INGESTION_AUTHORITY,
    )?;
    require_tla_image_tag("verdict", &image.verdict, TLA_CLEAN_VERDICT)?;
    require_tla_image_tag(
        "proposition_destination",
        &image.proposition_destination,
        TLA_CLEAN_PROPOSITION_DESTINATION,
    )?;
    if !image.computational_destinations.is_empty() {
        return Err("zero-authority TLA+ ingestion cannot name a computational destination".into());
    }
    validate_tla_clean_input("source", &image.source, source_bytes)?;
    validate_tla_clean_input("config", &image.config, config_bytes)?;
    validate_tla_clean_operators(&image.operators)?;
    validate_tla_clean_basis(&image.variables, &image.sorts, &image.basis)?;
    validate_tla_clean_proposition_basis(
        &image.variables,
        &image.sorts,
        &image.basis,
        &image.proposition_basis_sha256,
    )?;
    validate_tla_clean_tla_environment(&image.tla_environment)?;
    validate_tla_clean_kernel_environment(&image.kernel_environment)?;
    validate_tla_clean_terms(&image.terms)?;

    validate_sha256("artifact_sha256", &image.artifact_sha256)?;
    let mut unsigned = image.clone();
    unsigned.artifact_sha256.clear();
    let unsigned_bytes = serde_json::to_vec(&unsigned)
        .map_err(|error| format!("could not reproduce compatibility image identity: {error}"))?;
    let expected_artifact_sha256 = tla_clean_sha256(&unsigned_bytes);
    if image.artifact_sha256 != expected_artifact_sha256 {
        return Err(format!(
            "compatibility image identity mismatch: declared {}, recomputed {expected_artifact_sha256}",
            image.artifact_sha256
        ));
    }

    let mut canonical_bytes = serde_json::to_vec_pretty(&image)
        .map_err(|error| format!("could not reproduce canonical compatibility image: {error}"))?;
    canonical_bytes.push(b'\n');
    if image_bytes != canonical_bytes {
        return Err(
            "ty compatibility image is not the unique pretty-JSON encoding with one trailing newline"
                .into(),
        );
    }
    Ok(())
}

fn require_tla_image_tag(field: &str, observed: &str, expected: &str) -> Result<(), String> {
    if observed == expected {
        Ok(())
    } else {
        Err(format!(
            "ty compatibility image has invalid {field} `{observed}`; expected `{expected}`"
        ))
    }
}

fn validate_tla_clean_input(
    label: &str,
    input: &TlaCleanInput,
    expected_bytes: &[u8],
) -> Result<(), String> {
    if input.utf8.as_bytes() != expected_bytes {
        return Err(format!("compatibility image {label} bytes do not match the requested input"));
    }
    validate_sha256(&format!("{label}.sha256"), &input.sha256)?;
    let observed = tla_clean_sha256(expected_bytes);
    if input.sha256 != observed {
        return Err(format!(
            "compatibility image {label} digest mismatch: declared {}, recomputed {observed}",
            input.sha256
        ));
    }
    Ok(())
}

fn validate_tla_clean_operators(operators: &TlaCleanOperators) -> Result<(), String> {
    if operators.init.is_empty()
        || operators.next.is_empty()
        || operators.invariants.is_empty()
        || operators.effective_init.is_empty()
        || operators.effective_next.is_empty()
        || operators.effective_invariants.is_empty()
    {
        return Err(
            "compatibility image requires named configured and effective Init, Next, and invariants"
                .into(),
        );
    }
    validate_nonempty_unique_strings("invariant", &operators.invariants)?;
    validate_nonempty_unique_strings("effective invariant", &operators.effective_invariants)?;
    let constant_names = operators.constants.iter().map(|constant| constant.name.as_str());
    validate_strictly_increasing_nonempty("constant", constant_names)?;
    if operators.constants.iter().any(|constant| constant.canonical_value.is_empty()) {
        return Err("compatibility image contains an empty canonical constant value".into());
    }
    Ok(())
}

fn validate_tla_clean_proposition_basis(
    variables: &[String],
    sorts: &[TlaCleanSort],
    basis: &TlaCleanBasis,
    declared_sha256: &str,
) -> Result<(), String> {
    validate_sha256("proposition_basis_sha256", declared_sha256)?;
    let expected = tla_clean_proposition_basis_sha256(variables, sorts, basis)?;
    if declared_sha256 != expected {
        return Err(format!(
            "compatibility image proposition-basis identity mismatch: declared \
             {declared_sha256}, recomputed {expected}"
        ));
    }
    Ok(())
}

fn tla_clean_proposition_basis_sha256(
    variables: &[String],
    sorts: &[TlaCleanSort],
    basis: &TlaCleanBasis,
) -> Result<String, String> {
    #[derive(serde::Serialize)]
    struct PropositionBasis<'a> {
        schema: &'static str,
        variables: &'a [String],
        sorts: &'a [TlaCleanSort],
        basis: &'a TlaCleanBasis,
    }

    let bytes = serde_json::to_vec(&PropositionBasis {
        schema: TLA_CLEAN_PROPOSITION_BASIS_SCHEMA,
        variables,
        sorts,
        basis,
    })
    .map_err(|error| format!("could not reproduce proposition-basis identity: {error}"))?;
    Ok(tla_clean_sha256(&bytes))
}

fn validate_tla_clean_tla_environment(environment: &TlaCleanTlaEnvironment) -> Result<(), String> {
    require_tla_image_tag(
        "tla_environment.schema",
        &environment.schema,
        TLA_CLEAN_TLA_ENVIRONMENT_SCHEMA,
    )?;
    if environment.version != TLA_CLEAN_TLA_ENVIRONMENT_VERSION {
        return Err(format!(
            "compatibility image has invalid tla_environment.version {}; expected {}",
            environment.version, TLA_CLEAN_TLA_ENVIRONMENT_VERSION
        ));
    }
    let admitted = TLA_CLEAN_ADMITTED_BUILTIN_MODULES
        .iter()
        .map(|module| (*module).to_string())
        .collect::<Vec<_>>();
    if environment.admitted_builtin_modules != admitted {
        return Err("compatibility image changes the fixed TLA+ built-in allowlist".into());
    }
    if environment.used_builtin_modules != admitted {
        return Err("compatibility image must record the exact v1 TLA+ built-in environment".into());
    }
    Ok(())
}

fn validate_tla_clean_kernel_environment(
    environment: &TlaCleanKernelEnvironment,
) -> Result<(), String> {
    require_tla_image_tag(
        "kernel_environment.schema",
        &environment.schema,
        TLA_CLEAN_KERNEL_ENVIRONMENT_SCHEMA,
    )?;
    if environment.version != TLA_CLEAN_KERNEL_ENVIRONMENT_VERSION {
        return Err(format!(
            "compatibility image has invalid kernel_environment.version {}; expected {}",
            environment.version, TLA_CLEAN_KERNEL_ENVIRONMENT_VERSION
        ));
    }
    require_tla_image_tag(
        "kernel_environment.content_encoding",
        &environment.content_encoding,
        TLA_CLEAN_KERNEL_ENVIRONMENT_CONTENT_ENCODING,
    )?;
    for (label, value) in [
        ("clean_kernel_version", environment.clean_kernel_version.as_str()),
        ("tla_check_version", environment.tla_check_version.as_str()),
        ("environment_schema_fingerprint", environment.environment_schema_fingerprint.as_str()),
    ] {
        if value.is_empty()
            || value.len() > 128
            || !value.bytes().all(|byte| byte.is_ascii_graphic())
        {
            return Err(format!(
                "compatibility image kernel_environment.{label} is not a bounded printable identity"
            ));
        }
    }
    if environment.ledger.is_empty() || environment.ledger.len() > 128 {
        return Err(
            "compatibility image Clean declaration-environment ledger has an invalid size".into()
        );
    }
    let ledger_names =
        environment.ledger.iter().map(|entry| entry.name.clone()).collect::<Vec<_>>();
    validate_nonempty_unique_strings("Clean declaration-environment ledger", &ledger_names)?;
    validate_sha256(
        "kernel_environment.environment_content_sha256",
        &environment.environment_content_sha256,
    )?;
    validate_sha256("kernel_environment.identity_sha256", &environment.identity_sha256)?;
    let expected = tla_clean_kernel_environment_sha256(environment)?;
    if environment.identity_sha256 != expected {
        return Err(format!(
            "compatibility image Clean declaration-environment identity mismatch: declared {}, recomputed {expected}",
            environment.identity_sha256
        ));
    }
    Ok(())
}

fn tla_clean_kernel_environment_sha256(
    environment: &TlaCleanKernelEnvironment,
) -> Result<String, String> {
    let mut unsigned = environment.clone();
    unsigned.identity_sha256.clear();
    let bytes = serde_json::to_vec(&unsigned).map_err(|error| {
        format!("could not reproduce Clean declaration-environment identity: {error}")
    })?;
    Ok(tla_clean_sha256(&bytes))
}

fn validate_tla_clean_basis(
    variables: &[String],
    sorts: &[TlaCleanSort],
    basis: &TlaCleanBasis,
) -> Result<(), String> {
    validate_nonempty_unique_strings("variable", variables)?;
    if variables.len() > TLA_CLEAN_VARIABLE_CAP {
        return Err(format!(
            "compatibility image exceeds the {TLA_CLEAN_VARIABLE_CAP}-variable cap"
        ));
    }
    if sorts.len() != variables.len() || basis.max_r.len() != variables.len() {
        return Err(
            "compatibility image variable, sort, and reachable-maximum widths disagree".into()
        );
    }
    for sort in sorts {
        if let TlaCleanSort::Enum { labels, atom_kind } = sort {
            if atom_kind != "model" && atom_kind != "str" {
                return Err(format!(
                    "compatibility image has invalid enum atom_kind `{atom_kind}`"
                ));
            }
            validate_nonempty_unique_strings("enum label", labels)?;
            if labels.windows(2).any(|pair| pair[0] >= pair[1]) {
                return Err("compatibility image enum labels are not strictly sorted".into());
            }
        }
    }
    require_tla_image_tag("basis.order", &basis.order, TLA_CLEAN_BASIS_ORDER)?;
    if basis.state_cap != TLA_CLEAN_STATE_CAP
        || basis.max_obligation_legs != TLA_CLEAN_OBLIGATION_LEG_CAP
    {
        return Err(format!(
            "compatibility image must bind the fixed {TLA_CLEAN_STATE_CAP}-state and \
             {TLA_CLEAN_OBLIGATION_LEG_CAP}-leg caps"
        ));
    }

    let reachable_count = u64::try_from(basis.reachable.len())
        .map_err(|_| "reachable-state count does not fit u64")?;
    let init_domain_count =
        u64::try_from(basis.init_domain.len()).map_err(|_| "Init-domain count does not fit u64")?;
    let next_domain_count =
        u64::try_from(basis.next_domain.len()).map_err(|_| "Next-domain count does not fit u64")?;
    if basis.reachable_count != reachable_count
        || basis.init_domain_count != init_domain_count
        || basis.next_domain_count != next_domain_count
    {
        return Err("compatibility image basis counts do not match their rows".into());
    }
    if reachable_count == 0
        || reachable_count > TLA_CLEAN_STATE_CAP
        || init_domain_count == 0
        || init_domain_count > TLA_CLEAN_STATE_CAP
        || next_domain_count == 0
        || next_domain_count > TLA_CLEAN_STATE_CAP
    {
        return Err("compatibility image basis is empty or exceeds its fixed state cap".into());
    }
    let expected_legs = reachable_count
        .checked_add(init_domain_count)
        .and_then(|count| {
            reachable_count
                .checked_mul(next_domain_count)
                .and_then(|closure| count.checked_add(closure))
        })
        .ok_or("compatibility image obligation-leg count overflowed")?;
    if basis.obligation_leg_count != expected_legs || expected_legs > TLA_CLEAN_OBLIGATION_LEG_CAP {
        return Err(format!(
            "compatibility image obligation-leg count is invalid: declared {}, expected {expected_legs}",
            basis.obligation_leg_count
        ));
    }

    for (label, rows) in [
        ("reachable", &basis.reachable),
        ("Init domain", &basis.init_domain),
        ("Next domain", &basis.next_domain),
    ] {
        if rows.iter().any(|row| row.len() != variables.len()) {
            return Err(format!("compatibility image {label} row has the wrong tuple width"));
        }
        if rows.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(format!("compatibility image {label} rows are not strictly lexicographic"));
        }
        for row in rows {
            for (column, value) in row.iter().copied().enumerate() {
                if let TlaCleanSort::Enum { labels, .. } = &sorts[column] {
                    if usize::try_from(value).map_or(true, |index| index >= labels.len()) {
                        return Err(format!(
                            "compatibility image {label} row has an out-of-range enum code in column {column}"
                        ));
                    }
                }
            }
        }
    }
    validate_dense_tla_clean_domain("Init", &basis.init_domain, variables.len())?;
    validate_dense_tla_clean_domain("Next", &basis.next_domain, variables.len())?;
    let expected_max_r = (0..variables.len())
        .map(|column| basis.reachable.iter().map(|row| row[column]).max().unwrap_or(0))
        .collect::<Vec<_>>();
    if basis.max_r != expected_max_r {
        return Err("compatibility image max_r does not match the reachable rows".into());
    }
    Ok(())
}

fn validate_dense_tla_clean_domain(
    label: &str,
    rows: &[Vec<u64>],
    width: usize,
) -> Result<(), String> {
    let maxima = (0..width)
        .map(|column| rows.iter().map(|row| row[column]).max().unwrap_or(0))
        .collect::<Vec<_>>();
    let expected_count = maxima.iter().try_fold(1_u64, |count, maximum| {
        maximum
            .checked_add(1)
            .and_then(|axis| count.checked_mul(axis))
            .ok_or_else(|| format!("compatibility image {label} domain cardinality overflowed"))
    })?;
    let observed_count = u64::try_from(rows.len())
        .map_err(|_| format!("compatibility image {label} domain count does not fit u64"))?;
    if observed_count != expected_count {
        return Err(format!(
            "compatibility image {label} domain is not the complete dense Cartesian product: \
             observed {observed_count} row(s), expected {expected_count} from column maxima {maxima:?}"
        ));
    }
    Ok(())
}

fn validate_tla_clean_terms(terms: &TlaCleanTerms) -> Result<(), String> {
    require_tla_image_tag("terms.encoding", &terms.encoding, TLA_CLEAN_TERM_ENCODING)?;
    require_tla_image_tag(
        "terms.proposition_order",
        &terms.proposition_order,
        TLA_CLEAN_PROPOSITION_ORDER,
    )?;
    for (label, term) in [
        ("init", &terms.init),
        ("next", &terms.next),
        ("safety", &terms.safety),
        ("proposition", &terms.proposition),
    ] {
        validate_sha256(&format!("terms.{label}.sha256"), &term.sha256)?;
        let bytes = decode_lower_hex(&format!("terms.{label}.bytes_hex"), &term.bytes_hex)?;
        if bytes.is_empty() || bytes.len() > TLA_CLEAN_TERM_MAX_BYTES {
            return Err(format!(
                "compatibility image terms.{label} is empty or exceeds the \
                 {TLA_CLEAN_TERM_MAX_BYTES}-byte term limit"
            ));
        }
        let observed = tla_clean_sha256(&bytes);
        if term.sha256 != observed {
            return Err(format!(
                "compatibility image terms.{label} digest mismatch: declared {}, recomputed {observed}",
                term.sha256
            ));
        }
    }
    Ok(())
}

fn validate_nonempty_unique_strings(label: &str, values: &[String]) -> Result<(), String> {
    if values.is_empty() || values.iter().any(String::is_empty) {
        return Err(format!("compatibility image requires nonempty {label} names"));
    }
    let mut sorted = values.iter().map(String::as_str).collect::<Vec<_>>();
    sorted.sort_unstable();
    if sorted.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(format!("compatibility image contains duplicate {label} names"));
    }
    Ok(())
}

fn validate_strictly_increasing_nonempty<'a>(
    label: &str,
    values: impl IntoIterator<Item = &'a str>,
) -> Result<(), String> {
    let values = values.into_iter().collect::<Vec<_>>();
    if values.iter().any(|value| value.is_empty())
        || values.windows(2).any(|pair| pair[0] >= pair[1])
    {
        return Err(format!(
            "compatibility image {label} names must be nonempty, unique, and sorted"
        ));
    }
    Ok(())
}

fn validate_sha256(label: &str, digest: &str) -> Result<(), String> {
    if digest.len() == 64
        && digest.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        Ok(())
    } else {
        Err(format!("compatibility image {label} is not lowercase SHA-256 hex"))
    }
}

fn decode_lower_hex(label: &str, hex: &str) -> Result<Vec<u8>, String> {
    if !hex.len().is_multiple_of(2) || hex.len() > TLA_CLEAN_TERM_MAX_BYTES.saturating_mul(2) {
        return Err(format!("compatibility image {label} has an invalid encoded length"));
    }
    hex.as_bytes()
        .as_chunks::<2>().0.iter()
        .map(|pair| {
            let high = lower_hex_nibble(pair[0])
                .ok_or_else(|| format!("compatibility image {label} is not lowercase hex"))?;
            let low = lower_hex_nibble(pair[1])
                .ok_or_else(|| format!("compatibility image {label} is not lowercase hex"))?;
            Ok((high << 4) | low)
        })
        .collect()
}

fn lower_hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

fn tla_clean_sha256(bytes: &[u8]) -> String {
    use sha2::{Digest as _, Sha256};

    format!("{:x}", Sha256::digest(bytes))
}

fn parse_temporal_invocation(args: &[String]) -> Result<(&str, Vec<&String>), String> {
    let separator = args.iter().position(|arg| arg == "--").unwrap_or(args.len());
    let mut path = None;
    for arg in &args[..separator] {
        if arg.starts_with('-') {
            return Err(format!("unknown option `{arg}`"));
        }
        if path.replace(arg.as_str()).is_some() {
            return Err(format!("unexpected extra crate path `{arg}`"));
        }
    }
    let passthrough =
        if separator < args.len() { args[separator + 1..].iter().collect() } else { Vec::new() };
    Ok((path.unwrap_or("."), passthrough))
}

/// Build-time temporal evidence boundary.
///
/// A project-linked executable cannot authenticate the source bytes rustc read,
/// and a second post-build compilation cannot certify the first compilation's
/// artifact. Until trustc emits an authenticated semantic-input/output manifest,
/// selected temporal packages therefore fail with `unbound build evidence`.
/// Crates without an active temporal engine edge remain a no-op pass-through.
///
/// `build_result` is the build's own ExitCode, passed through unchanged when the
/// gate passes (or when the crate is not opted in). Once a crate opts in, ambient
/// process state cannot disable the gate. A help-only `build` compiled nothing,
/// so it is passed through too (see `pipeline::run_was_help_only`).
pub(crate) fn gate_build(build_result: ExitCode, args: &[String]) -> ExitCode {
    if build_result != ExitCode::SUCCESS || crate::pipeline::run_was_help_only(args) {
        return build_result;
    }
    let context = match crate::pipeline::post_build_cargo_context(args) {
        Ok(Some(context)) => context,
        Ok(None) => return build_result,
        Err(error) => {
            eprintln!(
                "targo trust build: temporal gate could not reconstruct build context: {error}"
            );
            return ExitCode::from(2);
        }
    };
    let roots = match crate::pipeline::resolve_cargo_gate_package_roots(args) {
        Ok(Some(roots)) => roots,
        Ok(None) => return build_result,
        Err(error) => {
            eprintln!(
                "targo trust build: temporal gate could not resolve selected packages: {error}"
            );
            return ExitCode::from(2);
        }
    };

    for root in roots {
        let path = root.to_string_lossy();
        let target = match temporal_gate_target(&root, context.metadata_args()) {
            Ok(target) => target,
            Err(error) => {
                eprintln!("targo trust build: temporal gate could not inspect `{path}`: {error}");
                return ExitCode::from(2);
            }
        };
        let gate_code = match target {
            TemporalGateTarget::Explicit => {
                eprintln!(
                    "targo trust build: `{path}/examples/trust_models.rs` is a project-authored \
                     legacy proof harness and cannot be trusted as independent evidence; migrate \
                     each model to a Clean `Trust.Temporal.FiniteModel.ScalarModel` and explicitly \
                     call `trust_spec_temporal::certify_clean_scalar_model_with_ty`"
                );
                2
            }
            TemporalGateTarget::Automatic { package_id, library_crate_name } => {
                let _ = (package_id, library_crate_name, context.temporal_args());
                eprintln!(
                    "targo trust build: temporal model gate for `{path}` rejected: \
                     {UNBOUND_TEMPORAL_EVIDENCE}"
                );
                2
            }
            TemporalGateTarget::None => continue,
        };
        if gate_code != 0 {
            eprintln!(
                "targo trust build: temporal evidence for `{path}` is unavailable or rejected; \
                 failing the build without claiming that the checker ran."
            );
            return ExitCode::from(gate_code.clamp(1, 255) as u8);
        }
    }

    build_result
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TemporalGateTarget {
    Explicit,
    Automatic { package_id: String, library_crate_name: String },
    None,
}

fn temporal_gate_target(
    root: &Path,
    metadata_context: &[String],
) -> Result<TemporalGateTarget, String> {
    let path = root.to_string_lossy();
    if crate_has_retired_project_harness(&path) {
        Ok(TemporalGateTarget::Explicit)
    } else {
        resolved_temporal_gate_target(root, metadata_context)
    }
}

fn temporal_gate_target_from_metadata(
    root: &Path,
    metadata: &TemporalCargoMetadata,
) -> Result<TemporalGateTarget, String> {
    temporal_gate_target_from_metadata_with_engine(
        root,
        metadata,
        canonical_temporal_engine_manifest,
    )
}

/// `expected_engine_manifest` is resolved only when the package has an active
/// normal edge to a package named `trust-spec-temporal`. A delivered toolchain
/// has no repository checkout at its build path, so resolving it up front made
/// every `targo trust build` fail after a passing verification, temporal or not.
fn temporal_gate_target_from_metadata_with_engine(
    root: &Path,
    metadata: &TemporalCargoMetadata,
    expected_engine_manifest: impl FnOnce() -> Result<PathBuf, String>,
) -> Result<TemporalGateTarget, String> {
    let manifest = root.join("Cargo.toml");
    let package = metadata
        .packages
        .iter()
        .find(|package| paths_equivalent(&package.manifest_path, &manifest))
        .ok_or_else(|| {
            format!(
                "canonical metadata did not contain selected package manifest {}",
                manifest.display()
            )
        })?;
    let resolve = metadata.resolve.as_ref().ok_or_else(|| {
        "canonical temporal metadata omitted the dependency resolve graph".to_string()
    })?;
    let node = resolve
        .nodes
        .iter()
        .find(|node| node.id == package.id)
        .ok_or_else(|| format!("canonical metadata omitted resolve node `{}`", package.id))?;
    let named_engines = metadata
        .packages
        .iter()
        .filter(|package| package.name == "trust-spec-temporal")
        .collect::<Vec<_>>();
    let mut active = false;
    let mut resolve_expected = Some(expected_engine_manifest);
    let mut expected_engine_manifest: Option<PathBuf> = None;
    for dependency in &node.deps {
        let Some(engine) = named_engines.iter().find(|engine| engine.id == dependency.pkg) else {
            continue;
        };
        let active_normal = dependency
            .dep_kinds
            .iter()
            .any(|kind| kind.kind.as_deref().is_none_or(|kind| kind == "normal"));
        if !active_normal {
            continue;
        }
        if let Some(resolve) = resolve_expected.take() {
            expected_engine_manifest = Some(resolve()?);
        }
        let expected_engine_manifest = expected_engine_manifest
            .as_deref()
            .expect("resolved before the first active engine edge");
        if !paths_equivalent(&engine.manifest_path, expected_engine_manifest) {
            return Err(format!(
                "package `{}` resolves trust-spec-temporal to untrusted shadow package `{}` at {}; proof-bearing temporal dependencies must use repository-owned {}",
                package.name,
                engine.id,
                engine.manifest_path.display(),
                expected_engine_manifest.display()
            ));
        }
        active = true;
    }
    if !active {
        return Ok(TemporalGateTarget::None);
    }
    let library = package
        .targets
        .iter()
        .find(|target| {
            target.kind.iter().any(|kind| kind == "lib" || kind == "rlib")
                && target
                    .crate_types
                    .iter()
                    .any(|crate_type| crate_type == "lib" || crate_type == "rlib")
        })
        .ok_or_else(|| {
            format!(
                "package `{}` has an active trust-spec-temporal dependency but no linkable \
                 Rust library target; the automatic temporal route cannot prove a binary-only crate",
                package.name
            )
        })?;
    Ok(TemporalGateTarget::Automatic {
        package_id: package.id.clone(),
        library_crate_name: library.name.clone(),
    })
}

fn paths_equivalent(left: &Path, right: &Path) -> bool {
    left == right
        || left
            .canonicalize()
            .ok()
            .zip(right.canonicalize().ok())
            .is_some_and(|(left, right)| left == right)
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::process::ExitCode;

    use super::{
        TLA_CLEAN_AUTHORITY, TLA_CLEAN_BASIS_ORDER, TLA_CLEAN_INGESTION_AUTHORITY,
        TLA_CLEAN_KERNEL_ENVIRONMENT_CONTENT_ENCODING, TLA_CLEAN_KERNEL_ENVIRONMENT_SCHEMA,
        TLA_CLEAN_KERNEL_ENVIRONMENT_VERSION, TLA_CLEAN_OBLIGATION_LEG_CAP,
        TLA_CLEAN_PROPOSITION_DESTINATION, TLA_CLEAN_PROPOSITION_ORDER, TLA_CLEAN_SCHEMA,
        TLA_CLEAN_STATE_CAP, TLA_CLEAN_TERM_ENCODING, TLA_CLEAN_TLA_ENVIRONMENT_SCHEMA,
        TLA_CLEAN_TLA_ENVIRONMENT_VERSION, TLA_CLEAN_VERDICT, TemporalCargoMetadata,
        TemporalGateTarget, TemporalMetadataDependency, TemporalMetadataDependencyKind,
        TemporalMetadataNode, TemporalMetadataPackage, TemporalMetadataResolve,
        TemporalMetadataTarget, TlaCleanBasis, TlaCleanConstant, TlaCleanImage,
        TlaCleanIngestInvocation, TlaCleanInput, TlaCleanKernelAdmission,
        TlaCleanKernelEnvironment, TlaCleanKernelLedgerEntry, TlaCleanOperators, TlaCleanSort,
        TlaCleanTerm, TlaCleanTerms, TlaCleanTlaEnvironment, gate_outcome,
        is_ty_control_environment_key, parse_temporal_invocation,
        parse_tla_clean_ingest_invocation, reject_tla_clean_output_alias, temporal_gate_target,
        temporal_gate_target_from_metadata, tla_clean_kernel_environment_sha256,
        tla_clean_proposition_basis_sha256, tla_clean_sha256, validate_tla_clean_image,
    };

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(ToString::to_string).collect()
    }

    fn tla_clean_term(label: &str) -> TlaCleanTerm {
        let bytes = format!("{{\"fixture\":\"{label}\"}}").into_bytes();
        TlaCleanTerm {
            bytes_hex: bytes.iter().map(|byte| format!("{byte:02x}")).collect(),
            sha256: tla_clean_sha256(&bytes),
        }
    }

    fn tla_clean_fixture(source: &str, config: &str) -> TlaCleanImage {
        let variables = vec!["x".to_string()];
        let sorts = vec![TlaCleanSort::Int];
        let basis = TlaCleanBasis {
            order: TLA_CLEAN_BASIS_ORDER.to_string(),
            state_cap: TLA_CLEAN_STATE_CAP,
            max_obligation_legs: TLA_CLEAN_OBLIGATION_LEG_CAP,
            reachable_count: 2,
            init_domain_count: 1,
            next_domain_count: 2,
            obligation_leg_count: 7,
            max_r: vec![1],
            reachable: vec![vec![0], vec![1]],
            init_domain: vec![vec![0]],
            next_domain: vec![vec![0], vec![1]],
        };
        let proposition_basis_sha256 =
            tla_clean_proposition_basis_sha256(&variables, &sorts, &basis)
                .expect("seal proposition basis");
        let mut kernel_environment = TlaCleanKernelEnvironment {
            schema: TLA_CLEAN_KERNEL_ENVIRONMENT_SCHEMA.to_string(),
            version: TLA_CLEAN_KERNEL_ENVIRONMENT_VERSION,
            clean_kernel_version: "0.14.0".to_string(),
            tla_check_version: "0.14.0".to_string(),
            environment_schema_fingerprint: "clean-env-bincode-v1".to_string(),
            ledger: vec![TlaCleanKernelLedgerEntry {
                name: "TyReflectPExp".to_string(),
                admission: TlaCleanKernelAdmission::Inductive,
            }],
            content_encoding: TLA_CLEAN_KERNEL_ENVIRONMENT_CONTENT_ENCODING.to_string(),
            environment_content_sha256: tla_clean_sha256(b"fixture environment"),
            identity_sha256: String::new(),
        };
        kernel_environment.identity_sha256 =
            tla_clean_kernel_environment_sha256(&kernel_environment)
                .expect("seal kernel environment");
        TlaCleanImage {
            schema: TLA_CLEAN_SCHEMA.to_string(),
            authority: TLA_CLEAN_AUTHORITY.to_string(),
            ingestion_authority: TLA_CLEAN_INGESTION_AUTHORITY.to_string(),
            verdict: TLA_CLEAN_VERDICT.to_string(),
            proposition_destination: TLA_CLEAN_PROPOSITION_DESTINATION.to_string(),
            computational_destinations: Vec::new(),
            source: TlaCleanInput {
                utf8: source.to_string(),
                sha256: tla_clean_sha256(source.as_bytes()),
            },
            config: TlaCleanInput {
                utf8: config.to_string(),
                sha256: tla_clean_sha256(config.as_bytes()),
            },
            operators: TlaCleanOperators {
                init: "Init".to_string(),
                next: "Next".to_string(),
                invariants: vec!["Safe".to_string()],
                effective_init: "Init".to_string(),
                effective_next: "Next".to_string(),
                effective_invariants: vec!["Safe".to_string()],
                constants: vec![TlaCleanConstant {
                    name: "Limit".to_string(),
                    canonical_value: "value:1".to_string(),
                }],
            },
            variables,
            sorts,
            basis,
            proposition_basis_sha256,
            tla_environment: TlaCleanTlaEnvironment {
                schema: TLA_CLEAN_TLA_ENVIRONMENT_SCHEMA.to_string(),
                version: TLA_CLEAN_TLA_ENVIRONMENT_VERSION,
                admitted_builtin_modules: vec!["Naturals".to_string()],
                used_builtin_modules: vec!["Naturals".to_string()],
            },
            kernel_environment,
            terms: TlaCleanTerms {
                encoding: TLA_CLEAN_TERM_ENCODING.to_string(),
                proposition_order: TLA_CLEAN_PROPOSITION_ORDER.to_string(),
                init: tla_clean_term("init"),
                next: tla_clean_term("next"),
                safety: tla_clean_term("safety"),
                proposition: tla_clean_term("proposition"),
            },
            artifact_sha256: String::new(),
        }
    }

    fn seal_tla_clean_fixture(mut image: TlaCleanImage) -> Vec<u8> {
        image.artifact_sha256.clear();
        image.artifact_sha256 =
            tla_clean_sha256(&serde_json::to_vec(&image).expect("serialize unsigned image"));
        let mut bytes = serde_json::to_vec_pretty(&image).expect("serialize image");
        bytes.push(b'\n');
        bytes
    }

    fn metadata(
        root: &std::path::Path,
        active: bool,
        linkable_library: bool,
    ) -> TemporalCargoMetadata {
        let package_id = "path+file:///fixture#package@0.1.0".to_string();
        let engine_id = "path+file:///fixture/engine#trust-spec-temporal@0.1.0".to_string();
        TemporalCargoMetadata {
            packages: vec![
                TemporalMetadataPackage {
                    id: package_id.clone(),
                    name: "package".to_string(),
                    manifest_path: root.join("Cargo.toml"),
                    targets: linkable_library
                        .then(|| TemporalMetadataTarget {
                            name: "actual_lib".to_string(),
                            kind: vec!["lib".to_string()],
                            crate_types: vec!["lib".to_string()],
                        })
                        .into_iter()
                        .collect(),
                },
                TemporalMetadataPackage {
                    id: engine_id.clone(),
                    name: "trust-spec-temporal".to_string(),
                    manifest_path: super::canonical_temporal_engine_manifest()
                        .expect("canonical temporal engine fixture"),
                    targets: vec![],
                },
            ],
            resolve: Some(TemporalMetadataResolve {
                nodes: vec![TemporalMetadataNode {
                    id: package_id,
                    deps: active
                        .then(|| TemporalMetadataDependency {
                            pkg: engine_id,
                            dep_kinds: vec![TemporalMetadataDependencyKind { kind: None }],
                        })
                        .into_iter()
                        .collect(),
                }],
            }),
        }
    }

    #[test]
    fn temporal_cli_keeps_forwarded_positionals_out_of_the_crate_path() {
        let args = strings(&["models", "--", "forwarded", "--help"]);
        let (path, forwarded) = parse_temporal_invocation(&args).expect("parse temporal args");
        assert_eq!(path, "models");
        assert_eq!(
            forwarded.iter().map(|arg| arg.as_str()).collect::<Vec<_>>(),
            ["forwarded", "--help"]
        );

        let args = strings(&["--", "forwarded"]);
        let (path, forwarded) = parse_temporal_invocation(&args).expect("parse temporal args");
        assert_eq!(path, ".");
        assert_eq!(forwarded.iter().map(|arg| arg.as_str()).collect::<Vec<_>>(), ["forwarded"]);
    }
    #[test]
    fn temporal_cli_rejects_unknown_options_and_extra_paths() {
        assert!(parse_temporal_invocation(&strings(&["--unknown"])).is_err());
        assert!(parse_temporal_invocation(&strings(&["one", "two"])).is_err());
    }

    #[test]
    fn temporal_ingest_parser_keeps_source_config_and_output_roles_exact() {
        let parsed = parse_tla_clean_ingest_invocation(&strings(&[
            "Counter.tla",
            "--config",
            "Counter.cfg",
            "--out",
            "counter.clean.json",
        ]))
        .expect("parse bounded TLA+ ingestion");
        assert_eq!(parsed.spec, std::path::Path::new("Counter.tla"));
        assert_eq!(parsed.config, std::path::Path::new("Counter.cfg"));
        assert_eq!(parsed.out.as_deref(), Some(std::path::Path::new("counter.clean.json")));

        let stdout = parse_tla_clean_ingest_invocation(&strings(&[
            "Counter.tla",
            "--config",
            "Counter.cfg",
        ]))
        .expect("stdout is the default destination");
        assert!(stdout.out.is_none());
    }

    #[test]
    fn temporal_ingest_parser_rejects_ambiguous_or_mistyped_roles() {
        for args in [
            vec!["Counter.tla"],
            vec!["Counter.cfg", "--config", "Counter.cfg"],
            vec!["Counter.tla", "--config", "Counter.tla"],
            vec!["Counter.tla", "Other.tla", "--config", "Counter.cfg"],
            vec!["Counter.tla", "--config", "Counter.cfg", "--config", "Other.cfg"],
            vec!["Counter.tla", "--config", "Counter.cfg", "--out"],
            vec!["Counter.tla", "--config", "Counter.cfg", "--", "extra"],
            vec!["Counter.tla", "--config", "Counter.cfg", "--authority", "proof"],
        ] {
            assert!(
                parse_tla_clean_ingest_invocation(&strings(&args)).is_err(),
                "must reject {args:?}"
            );
        }
    }

    #[test]
    fn temporal_ingest_scrubs_all_ty_control_environment_keys() {
        assert!(is_ty_control_environment_key(std::ffi::OsStr::new("TY_NO_STDLIB_OVERRIDE")));
        assert!(is_ty_control_environment_key(std::ffi::OsStr::new("TY_VM_FORCE_FALLBACK")));
        assert!(is_ty_control_environment_key(std::ffi::OsStr::new("ty_vm_force_fallback")));
        assert!(!is_ty_control_environment_key(std::ffi::OsStr::new("RUST_LOG")));
        assert!(!is_ty_control_environment_key(std::ffi::OsStr::new("TRUST_TY_PATH")));

        let mut command = std::process::Command::new("unused-test-program");
        command.env("Ty_Vm_Force_Fallback", "1");
        command.env("RUST_LOG", "debug");
        super::scrub_tla_clean_elaborator_env(&mut command);
        assert!(command.get_envs().any(|(name, value)| {
            name == std::ffi::OsStr::new("Ty_Vm_Force_Fallback") && value.is_none()
        }));
        assert!(command.get_envs().any(|(name, value)| {
            name == std::ffi::OsStr::new("RUST_LOG") && value == Some(std::ffi::OsStr::new("debug"))
        }));
    }

    #[test]
    fn temporal_ingest_rejects_output_aliases_before_elaboration() {
        let temp = tempfile::tempdir().expect("create alias fixture");
        let source = temp.path().join("Counter.tla");
        let config = temp.path().join("Counter.cfg");
        fs::write(&source, "---- MODULE Counter ----\n====\n").expect("write source");
        fs::write(&config, "INIT Init\nNEXT Next\nINVARIANT Safe\n").expect("write config");

        let direct = TlaCleanIngestInvocation {
            spec: source.clone(),
            config: config.clone(),
            out: Some(source.clone()),
        };
        assert!(reject_tla_clean_output_alias(&direct).is_err());

        let lexical_alias = TlaCleanIngestInvocation {
            spec: source.clone(),
            config,
            out: Some(temp.path().join("nested").join("..").join("Counter.tla")),
        };
        fs::create_dir(temp.path().join("nested")).expect("create alias path component");
        assert!(reject_tla_clean_output_alias(&lexical_alias).is_err());
    }

    #[test]
    fn temporal_ingest_image_accepts_only_the_canonical_zero_authority_envelope() {
        let source = "---- MODULE Counter ----\nVARIABLE x\n====\n";
        let config = "INIT Init\nNEXT Next\nINVARIANT Safe\n";
        let bytes = seal_tla_clean_fixture(tla_clean_fixture(source, config));
        validate_tla_clean_image(&bytes, source.as_bytes(), config.as_bytes())
            .expect("canonical zero-authority image");

        let mut noncanonical = bytes.clone();
        noncanonical.extend_from_slice(b"\n");
        let error = validate_tla_clean_image(&noncanonical, source.as_bytes(), config.as_bytes())
            .expect_err("noncanonical whitespace must fail");
        assert!(error.contains("unique pretty-JSON"), "{error}");

        let mut unknown: serde_json::Value =
            serde_json::from_slice(&bytes).expect("decode fixture as JSON");
        unknown["proof"] = serde_json::json!(true);
        let unknown = serde_json::to_vec_pretty(&unknown).expect("encode unknown field");
        let error = validate_tla_clean_image(&unknown, source.as_bytes(), config.as_bytes())
            .expect_err("closed schema must reject authority injection");
        assert!(error.contains("closed schema"), "{error}");
    }

    #[test]
    fn temporal_ingest_image_rejects_resealed_authority_or_input_substitution() {
        let source = "---- MODULE Counter ----\nVARIABLE x\n====\n";
        let config = "INIT Init\nNEXT Next\nINVARIANT Safe\n";

        let mut authority = tla_clean_fixture(source, config);
        authority.authority = "proof".to_string();
        let error = validate_tla_clean_image(
            &seal_tla_clean_fixture(authority),
            source.as_bytes(),
            config.as_bytes(),
        )
        .expect_err("a resealed producer cannot grant proof authority");
        assert!(error.contains("invalid authority"), "{error}");

        let mut substituted = tla_clean_fixture(source, config);
        substituted.source.utf8.push_str("\\* substituted\n");
        substituted.source.sha256 = tla_clean_sha256(substituted.source.utf8.as_bytes());
        let error = validate_tla_clean_image(
            &seal_tla_clean_fixture(substituted),
            source.as_bytes(),
            config.as_bytes(),
        )
        .expect_err("a resealed image must remain bound to requested bytes");
        assert!(error.contains("source bytes"), "{error}");
    }

    #[test]
    fn temporal_ingest_image_rejects_term_and_basis_corruption() {
        let source = "---- MODULE Counter ----\nVARIABLE x\n====\n";
        let config = "INIT Init\nNEXT Next\nINVARIANT Safe\n";

        let mut term = tla_clean_fixture(source, config);
        term.terms.proposition.bytes_hex.push_str("00");
        let error = validate_tla_clean_image(
            &seal_tla_clean_fixture(term),
            source.as_bytes(),
            config.as_bytes(),
        )
        .expect_err("term bytes must be bound by their digest");
        assert!(error.contains("proposition digest mismatch"), "{error}");

        let mut counts = tla_clean_fixture(source, config);
        counts.basis.obligation_leg_count += 1;
        let error = validate_tla_clean_image(
            &seal_tla_clean_fixture(counts),
            source.as_bytes(),
            config.as_bytes(),
        )
        .expect_err("basis counts must be independently recomputed");
        assert!(error.contains("obligation-leg count"), "{error}");

        let mut order = tla_clean_fixture(source, config);
        order.basis.reachable.swap(0, 1);
        let error = validate_tla_clean_image(
            &seal_tla_clean_fixture(order),
            source.as_bytes(),
            config.as_bytes(),
        )
        .expect_err("basis order must be canonical");
        assert!(error.contains("strictly lexicographic"), "{error}");

        let mut gap = tla_clean_fixture(source, config);
        gap.basis.next_domain = vec![vec![0], vec![2]];
        gap.basis.max_r = vec![1];
        let error = validate_tla_clean_image(
            &seal_tla_clean_fixture(gap),
            source.as_bytes(),
            config.as_bytes(),
        )
        .expect_err("domain rows must cover the dense Cartesian product");
        assert!(error.contains("complete dense Cartesian product"), "{error}");
    }

    #[test]
    fn temporal_ingest_image_rejects_identity_and_environment_corruption() {
        let source = "---- MODULE Counter ----\nVARIABLE x\n====\n";
        let config = "INIT Init\nNEXT Next\nINVARIANT Safe\n";

        let mut basis_identity = tla_clean_fixture(source, config);
        basis_identity.proposition_basis_sha256.replace_range(0..1, "0");
        if basis_identity.proposition_basis_sha256
            == tla_clean_proposition_basis_sha256(
                &basis_identity.variables,
                &basis_identity.sorts,
                &basis_identity.basis,
            )
            .expect("recompute proposition basis")
        {
            basis_identity.proposition_basis_sha256.replace_range(0..1, "1");
        }
        let error = validate_tla_clean_image(
            &seal_tla_clean_fixture(basis_identity),
            source.as_bytes(),
            config.as_bytes(),
        )
        .expect_err("proposition basis digest mutation must fail");
        assert!(error.contains("proposition-basis identity mismatch"), "{error}");

        let mut tla_environment = tla_clean_fixture(source, config);
        tla_environment.tla_environment.admitted_builtin_modules.push("Sequences".to_string());
        let error = validate_tla_clean_image(
            &seal_tla_clean_fixture(tla_environment),
            source.as_bytes(),
            config.as_bytes(),
        )
        .expect_err("expanded TLA+ dependency authority must fail");
        assert!(error.contains("fixed TLA+ built-in allowlist"), "{error}");

        let mut kernel_environment = tla_clean_fixture(source, config);
        kernel_environment.kernel_environment.environment_content_sha256 =
            tla_clean_sha256(b"substituted environment");
        let error = validate_tla_clean_image(
            &seal_tla_clean_fixture(kernel_environment),
            source.as_bytes(),
            config.as_bytes(),
        )
        .expect_err("environment content substitution under a stale identity must fail");
        assert!(error.contains("Clean declaration-environment identity mismatch"), "{error}");

        let mut effective = tla_clean_fixture(source, config);
        effective.operators.effective_init.clear();
        let error = validate_tla_clean_image(
            &seal_tla_clean_fixture(effective),
            source.as_bytes(),
            config.as_bytes(),
        )
        .expect_err("missing effective operator binding must fail");
        assert!(error.contains("configured and effective Init"), "{error}");
    }

    #[test]
    fn gate_passes_through_when_not_temporal() {
        // Gate did not run -> the build's own code stands, success or failure.
        assert_eq!(gate_outcome(0, None), 0);
        assert_eq!(gate_outcome(2, None), 2);
    }

    #[test]
    fn gate_pass_preserves_build_result() {
        // Gate ran and passed after a green build.
        assert_eq!(gate_outcome(0, Some(0)), 0); // green build + gate pass -> 0
    }

    #[test]
    fn gate_failure_fails_closed_only_after_a_successful_build() {
        assert_eq!(gate_outcome(0, Some(1)), 1); // green build but model violated -> FAIL
        assert!(gate_outcome(0, Some(255)) >= 1);
        assert_eq!(gate_outcome(2, Some(1)), 2); // preserve base failure; gate is not run
    }

    #[test]
    fn temporal_gate_classifies_every_selected_package_root() {
        let temp = tempfile::tempdir().expect("create temporal gate fixture");
        let explicit = temp.path().join("explicit");
        let automatic = temp.path().join("automatic");
        let plain = temp.path().join("plain");
        std::fs::create_dir_all(explicit.join("examples")).expect("create explicit examples");
        std::fs::create_dir_all(&automatic).expect("create automatic package");
        std::fs::create_dir_all(&plain).expect("create plain package");
        std::fs::write(explicit.join("examples/trust_models.rs"), "fn main() {}\n")
            .expect("write explicit registry");
        std::fs::write(
            automatic.join("Cargo.toml"),
            "[package]\nname='automatic'\nversion='0.1.0'\n[dependencies]\ntrust-spec-temporal='0.1'\n",
        )
        .expect("write automatic manifest");
        std::fs::write(plain.join("Cargo.toml"), "[package]\nname='plain'\nversion='0.1.0'\n")
            .expect("write plain manifest");

        assert_eq!(temporal_gate_target(&explicit, &[]).unwrap(), TemporalGateTarget::Explicit);
        assert_eq!(
            temporal_gate_target_from_metadata(&automatic, &metadata(&automatic, true, true))
                .unwrap(),
            TemporalGateTarget::Automatic {
                package_id: "path+file:///fixture#package@0.1.0".to_string(),
                library_crate_name: "actual_lib".to_string(),
            }
        );
        assert_eq!(
            temporal_gate_target_from_metadata(&plain, &metadata(&plain, false, true)).unwrap(),
            TemporalGateTarget::None
        );
    }

    #[test]
    fn temporal_dependency_requires_an_active_resolved_normal_edge() {
        let temp = tempfile::tempdir().expect("create temporal dependency fixture");
        assert_eq!(
            temporal_gate_target_from_metadata(temp.path(), &metadata(temp.path(), false, true))
                .unwrap(),
            TemporalGateTarget::None,
            "disabled optional/nonmatching target dependencies must be a no-op"
        );
        assert!(matches!(
            temporal_gate_target_from_metadata(temp.path(), &metadata(temp.path(), true, true))
                .unwrap(),
            TemporalGateTarget::Automatic { .. }
        ));
    }

    #[test]
    fn unavailable_engine_manifest_matters_only_with_an_engine_edge() {
        // A delivered toolchain has no checkout at its build path, so the engine
        // manifest cannot be resolved there. A crate with no trust-spec-temporal
        // edge must not depend on it; a crate with one must still fail closed.
        let temp = tempfile::tempdir().expect("create delivered-toolchain fixture");
        let unavailable = || -> Result<std::path::PathBuf, String> {
            Err("repository-owned trust-spec-temporal manifest is unavailable".to_string())
        };
        let no_edge = metadata(temp.path(), false, true);
        assert_eq!(
            super::temporal_gate_target_from_metadata_with_engine(
                temp.path(),
                &no_edge,
                || -> Result<std::path::PathBuf, String> {
                    panic!("no engine edge: the engine manifest must not be resolved")
                },
            )
            .unwrap(),
            TemporalGateTarget::None
        );
        assert_eq!(
            super::temporal_gate_target_from_metadata_with_engine(
                temp.path(),
                &no_edge,
                unavailable
            )
            .unwrap(),
            TemporalGateTarget::None
        );
        let error = super::temporal_gate_target_from_metadata_with_engine(
            temp.path(),
            &metadata(temp.path(), true, true),
            unavailable,
        )
        .expect_err("an engine edge with no resolvable engine must fail closed");
        assert!(error.contains("manifest is unavailable"), "{error}");
    }

    #[test]
    fn temporal_dependency_rejects_same_named_shadow_package() {
        let temp = tempfile::tempdir().expect("create temporal shadow fixture");
        let mut shadow = metadata(temp.path(), true, true);
        shadow
            .packages
            .iter_mut()
            .find(|package| package.name == "trust-spec-temporal")
            .expect("engine package")
            .manifest_path = temp.path().join("shadow/trust-spec-temporal/Cargo.toml");
        let error = temporal_gate_target_from_metadata(temp.path(), &shadow)
            .expect_err("same-named path/patch shadow must not become the trusted engine");
        assert!(error.contains("untrusted shadow package"), "{error}");
    }

    #[test]
    fn automatic_route_fails_closed_without_a_linkable_library() {
        let temp = tempfile::tempdir().expect("create binary-only temporal fixture");
        fs::write(
            temp.path().join("Cargo.toml"),
            "[package]\nname='binary-only'\nversion='0.1.0'\n\
             [dependencies]\ntrust-spec-temporal='0.1'\n",
        )
        .expect("write binary-only manifest");
        fs::create_dir_all(temp.path().join("src")).expect("create src");
        fs::write(temp.path().join("src/main.rs"), "fn main() {}\n").expect("write binary");

        let error =
            temporal_gate_target_from_metadata(temp.path(), &metadata(temp.path(), true, false))
                .expect_err("binary-only crate must fail closed");
        assert!(error.contains("no linkable Rust library target"), "{error}");
        assert!(!temp.path().join("examples").exists());
    }

    #[test]
    fn temporal_gate_preserves_a_failed_build_without_resolving_packages() {
        assert_eq!(
            super::gate_build(ExitCode::from(7), &["-p".to_string(), "missing".to_string()]),
            ExitCode::from(7)
        );
    }
}
