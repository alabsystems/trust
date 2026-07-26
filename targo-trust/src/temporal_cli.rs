// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
//! `targo trust temporal` — inspect the canonical temporal engine dependency and
//! linkable-target boundary, then fail closed with unbound evidence.
//!
//! The former generated-harness/embedded-ty execution route — and the automatic
//! link-time model inventory it consumed — are DELETED (owner ruling
//! 2026-07-20, "no deprecation limbo"): a project-linked executable cannot
//! authenticate the source bytes rustc read or the prior/final build artifact,
//! so no such route may exist until trustc emits an authenticated manifest.
//!
//! New models use a Clean `Trust.Temporal.FiniteModel.ScalarModel` plus an
//! explicit `trust_spec_temporal::certify_clean_scalar_model_with_ty` call; the
//! caller owns the definition list it certifies. Project-authored
//! `examples/trust_models.rs` programs are also rejected because code supplying
//! its own verdict protocol is not independent evidence.

use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::time::Duration;

pub(crate) const UNBOUND_TEMPORAL_EVIDENCE: &str = "unbound build evidence: the canonical compiler does not yet emit an authenticated input/output manifest binding the generated temporal harness source, resolved dependency graph, ty identity, and executable bytes; automatic temporal results are non-evidentiary and cannot pass";

const TEMPORAL_HELP: &str = "\
targo trust temporal [path]

Inspect the canonical temporal-engine dependency/linkable-target boundary in the
crate at <path> (default `.`) and enforce the fail-closed temporal evidence
boundary. This command does not generate or execute a model-check harness while
compiler-authenticated semantic-input/output binding is unavailable.

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
pub(crate) fn crate_has_models(path: &str) -> bool {
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
    let targo = crate::pipeline::discover_native_trust_cargo_checked()?;
    let mut command = Command::new(&targo);
    command.args(["metadata", "--format-version", "1", "--manifest-path"]);
    command.arg(root.join("Cargo.toml"));
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
    command.args(&context);
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
/// process state cannot disable the gate.
pub(crate) fn gate_build(build_result: ExitCode, args: &[String]) -> ExitCode {
    if build_result != ExitCode::SUCCESS {
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
    if crate_has_models(&path) {
        Ok(TemporalGateTarget::Explicit)
    } else {
        resolved_temporal_gate_target(root, metadata_context)
    }
}

fn temporal_gate_target_from_metadata(
    root: &Path,
    metadata: &TemporalCargoMetadata,
) -> Result<TemporalGateTarget, String> {
    let expected_engine_manifest = canonical_temporal_engine_manifest()?;
    temporal_gate_target_from_metadata_with_engine(root, metadata, &expected_engine_manifest)
}

fn temporal_gate_target_from_metadata_with_engine(
    root: &Path,
    metadata: &TemporalCargoMetadata,
    expected_engine_manifest: &Path,
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
        TemporalCargoMetadata, TemporalGateTarget, TemporalMetadataDependency,
        TemporalMetadataDependencyKind, TemporalMetadataNode, TemporalMetadataPackage,
        TemporalMetadataResolve, TemporalMetadataTarget, gate_outcome, parse_temporal_invocation,
        temporal_gate_target, temporal_gate_target_from_metadata,
    };

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(ToString::to_string).collect()
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
