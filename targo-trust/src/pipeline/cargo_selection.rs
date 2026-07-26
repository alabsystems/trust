// Cargo package selection shared by post-build proof gates.
//
// The compiler pipeline and every post-build gate must agree about which
// packages Cargo selected.  Guessing from the first positional
// argument is unsound: values for `-p`, `--manifest-path`, and unrelated
// wrapper options are not crate directories, and a workspace invocation may
// select more than one package.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use serde::Deserialize;

use super::discovery::discover_native_trust_cargo_checked;
use crate::bounded_process;
use crate::cli::parse_subcommand_args;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CargoSelectionArgs {
    packages: Vec<String>,
    excludes: Vec<String>,
    workspace: bool,
    package_flag_seen: bool,
    manifest_path: Option<PathBuf>,
    target_triples: BTreeSet<String>,
    global_context_args: Vec<String>,
    metadata_feature_args: Vec<String>,
}

impl CargoSelectionArgs {
    /// Parse Cargo's package-selection flags without interpreting positionals.
    ///
    /// Unknown flags are left to Cargo. Known flags that consume a value are
    /// skipped so a value that happens to begin with `-p` cannot become a
    /// package selection. A literal `--` ends Cargo-option parsing.
    pub(crate) fn parse(args: &[String]) -> Result<Self, String> {
        let mut parsed = Self::default();
        let mut index = 0;
        while index < args.len() {
            let arg = args[index].as_str();
            if arg == "--" {
                break;
            }
            match arg {
                "-p" | "--package" => {
                    parsed.package_flag_seen = true;
                    if let Some(value) = optional_value(args, &mut index) {
                        parsed.packages.push(value);
                    }
                }
                "--exclude" => {
                    parsed.excludes.push(required_value(args, &mut index, arg)?);
                }
                "--manifest-path" => {
                    let value = required_value(args, &mut index, arg)?;
                    set_manifest_path(&mut parsed.manifest_path, value)?;
                }
                "--workspace" | "--all" => parsed.workspace = true,
                // These Cargo compile options consume the next token. Keep the
                // list explicit: package-selection parsing must never guess
                // that their values are crate paths or `-p...` selectors.
                "--target" => {
                    let value = required_value(args, &mut index, arg)?;
                    parsed.target_triples.insert(value);
                }
                "--bin" | "--example" | "--test" | "--bench" => {
                    let _ = optional_value(args, &mut index);
                }
                "--features" | "-F" => {
                    let value = required_value(args, &mut index, arg)?;
                    parsed.metadata_feature_args.push("--features".to_string());
                    parsed.metadata_feature_args.push(value);
                }
                "--config" | "-Z" => {
                    let value = required_value(args, &mut index, arg)?;
                    parsed.global_context_args.push(arg.to_string());
                    parsed.global_context_args.push(value);
                }
                "--all-features" | "--no-default-features" => {
                    parsed.metadata_feature_args.push(arg.to_string());
                }
                "--locked" | "--offline" | "--frozen" => {
                    parsed.global_context_args.push(arg.to_string());
                }
                "--release" | "-r" => {}
                "--target-dir" | "--profile" => {
                    let _ = required_value(args, &mut index, arg)?;
                }
                "--artifact-dir" | "--jobs" | "-j" | "--message-format" | "--color"
                | "--crate-type" | "--lockfile-path" => {
                    let _ = required_value(args, &mut index, arg)?;
                }
                _ => {
                    if let Some(value) = arg.strip_prefix("--package=") {
                        parsed.package_flag_seen = true;
                        push_nonempty(&mut parsed.packages, value, "--package")?;
                    } else if let Some(value) = arg.strip_prefix("--exclude=") {
                        push_nonempty(&mut parsed.excludes, value, "--exclude")?;
                    } else if let Some(value) = arg.strip_prefix("--manifest-path=") {
                        if value.is_empty() {
                            return Err("--manifest-path requires a nonempty path".to_string());
                        }
                        set_manifest_path(&mut parsed.manifest_path, value.to_string())?;
                    } else if let Some(value) = arg.strip_prefix("--target=") {
                        require_joined_value(value, "--target")?;
                        parsed.target_triples.insert(value.to_string());
                    } else if let Some(value) = arg.strip_prefix("--target-dir=") {
                        require_joined_value(value, "--target-dir")?;
                    } else if let Some(value) = arg.strip_prefix("--profile=") {
                        require_joined_value(value, "--profile")?;
                    } else if let Some(value) = arg.strip_prefix("-p=") {
                        parsed.package_flag_seen = true;
                        push_nonempty(&mut parsed.packages, value, "-p")?;
                    } else if let Some(value) = arg.strip_prefix("-p").filter(|v| !v.is_empty()) {
                        parsed.package_flag_seen = true;
                        push_nonempty(&mut parsed.packages, value, "-p")?;
                    } else if let Some(value) = arg.strip_prefix("--features=") {
                        push_feature_arg(&mut parsed.metadata_feature_args, value, "--features")?;
                    } else if let Some(value) = arg.strip_prefix("-F=") {
                        push_feature_arg(&mut parsed.metadata_feature_args, value, "-F")?;
                    } else if let Some(value) = arg.strip_prefix("-F").filter(|v| !v.is_empty()) {
                        push_feature_arg(&mut parsed.metadata_feature_args, value, "-F")?;
                    } else if let Some(value) = arg.strip_prefix("--config=") {
                        push_context_arg(&mut parsed.global_context_args, "--config", value)?;
                    } else if let Some(value) = arg.strip_prefix("-Z=") {
                        push_context_arg(&mut parsed.global_context_args, "-Z", value)?;
                    } else if let Some(value) = arg.strip_prefix("-Z").filter(|v| !v.is_empty()) {
                        push_context_arg(&mut parsed.global_context_args, "-Z", value)?;
                    }
                }
            }
            index += 1;
        }

        if !parsed.excludes.is_empty() && !parsed.workspace {
            return Err("--exclude can only be used together with --workspace/--all".to_string());
        }
        if parsed.package_flag_seen && parsed.packages.is_empty() {
            return Err("--package/-p requires a package specification (the build would not run)"
                .to_string());
        }
        if parsed.target_triples.len() > 1 {
            return Err(format!(
                "evidence-grade Targo requires one effective compile target per invocation; split the requested targets into independent proof reports: {}",
                parsed.target_triples.iter().cloned().collect::<Vec<_>>().join(", ")
            ));
        }
        Ok(parsed)
    }

    pub(crate) fn manifest_path(&self) -> Option<&Path> {
        self.manifest_path.as_deref()
    }

    fn explicit_target_triple(&self) -> Option<&str> {
        self.target_triples.iter().next().map(String::as_str)
    }
}

fn push_feature_arg(values: &mut Vec<String>, value: &str, option: &str) -> Result<(), String> {
    if value.is_empty() {
        return Err(format!("{option} requires a nonempty value"));
    }
    values.push("--features".to_string());
    values.push(value.to_string());
    Ok(())
}

fn push_context_arg(values: &mut Vec<String>, option: &str, value: &str) -> Result<(), String> {
    if value.is_empty() {
        return Err(format!("{option} requires a nonempty value"));
    }
    values.push(option.to_string());
    values.push(value.to_string());
    Ok(())
}

fn require_joined_value(value: &str, option: &str) -> Result<(), String> {
    if value.is_empty() {
        return Err(format!("{option} requires a nonempty value"));
    }
    Ok(())
}

fn required_value(args: &[String], index: &mut usize, option: &str) -> Result<String, String> {
    *index += 1;
    let value = args
        .get(*index)
        .filter(|value| !value.is_empty() && value.as_str() != "--")
        .ok_or_else(|| format!("{option} requires a nonempty value"))?;
    Ok(value.clone())
}

fn optional_value(args: &[String], index: &mut usize) -> Option<String> {
    let next = args.get(*index + 1)?;
    if next == "--" || next.starts_with('-') {
        return None;
    }
    *index += 1;
    Some(next.clone())
}

fn push_nonempty(values: &mut Vec<String>, value: &str, option: &str) -> Result<(), String> {
    if value.is_empty() {
        return Err(format!("{option} requires a nonempty value"));
    }
    values.push(value.to_string());
    Ok(())
}

fn set_manifest_path(slot: &mut Option<PathBuf>, value: String) -> Result<(), String> {
    let path = PathBuf::from(value);
    if let Some(previous) = slot {
        if previous != &path {
            return Err(format!(
                "conflicting --manifest-path values `{}` and `{}`",
                previous.display(),
                path.display()
            ));
        }
    } else {
        *slot = Some(path);
    }
    Ok(())
}

#[derive(Debug, Deserialize)]
struct CargoMetadata {
    packages: Vec<MetadataPackage>,
    workspace_members: Vec<String>,
    workspace_default_members: Vec<String>,
    target_directory: PathBuf,
}

#[derive(Debug, Deserialize)]
struct MetadataPackage {
    id: String,
    name: String,
    version: String,
    manifest_path: PathBuf,
}

/// Exact identity for a package selected by canonical Targo/Cargo semantics.
/// Consumers must use `id` (not the raw CLI spec or possibly-ambiguous name)
/// when addressing the package back to Targo.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResolvedCargoPackage {
    pub(crate) id: String,
    pub(crate) name: String,
    pub(crate) root: PathBuf,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResolvedCargoSelection {
    pub(crate) packages: Vec<ResolvedCargoPackage>,
    /// Cargo's authoritative effective target directory from the same
    /// authenticated metadata invocation used for package selection.
    pub(crate) target_directory: PathBuf,
}

/// One resolved dependency: a package in the graph that is not a workspace
/// member, with the directory its `.trust/proof.cert` would live in.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResolvedDependency {
    pub(crate) name: String,
    pub(crate) version: String,
    pub(crate) root: PathBuf,
}

/// Every non-member package the resolved graph pulls in.
///
/// Workspace members are excluded because a project's own crates are what the
/// run in progress is verifying; the dependency-evidence policy is about the
/// code the project did NOT verify. Resolution goes through the canonical
/// sibling `targo`, the same authenticated path package selection uses — a PATH
/// cargo could resolve a different graph than the one being built.
pub(crate) fn resolve_dependencies(args: &[String]) -> Result<Vec<ResolvedDependency>, String> {
    let targo = discover_native_trust_cargo_checked()?;
    let (metadata, _, _) = resolve_cargo_selection_and_metadata_with_targo(args, &targo)?;
    let members: BTreeSet<&str> = metadata.workspace_members.iter().map(String::as_str).collect();
    let mut deps: Vec<ResolvedDependency> = metadata
        .packages
        .iter()
        .filter(|package| !members.contains(package.id.as_str()))
        .filter_map(|package| {
            package.manifest_path.parent().map(|root| ResolvedDependency {
                name: package.name.clone(),
                version: package.version.clone(),
                root: root.to_path_buf(),
            })
        })
        .collect();
    deps.sort_by(|a, b| (&a.name, &a.version).cmp(&(&b.name, &b.version)));
    deps.dedup();
    Ok(deps)
}

/// Resolve a child-facing Cargo argv to every selected package.
/// Metadata is always obtained through the canonical sibling `targo` belonging
/// to the selected Trust compiler; PATH Cargo is never proof evidence.
pub(crate) fn resolve_cargo_selection(args: &[String]) -> Result<ResolvedCargoSelection, String> {
    let targo = discover_native_trust_cargo_checked()?;
    resolve_cargo_selection_with_targo(args, &targo)
}

/// Resolve selection with the exact Targo executable already authenticated by
/// the caller. Compiler execution and metadata selection must use the same
/// frontend bytes/path; independently rediscovering Targo here can select a
/// different installation between the two operations.
pub(crate) fn resolve_cargo_selection_with_targo(
    args: &[String],
    targo: &Path,
) -> Result<ResolvedCargoSelection, String> {
    resolve_cargo_selection_and_metadata_with_targo(args, targo).map(|(_, _, selection)| selection)
}

fn resolve_cargo_selection_and_metadata_with_targo(
    args: &[String],
    targo: &Path,
) -> Result<(CargoMetadata, CargoSelectionArgs, ResolvedCargoSelection), String> {
    let selection = CargoSelectionArgs::parse(args)?;
    let mut command = Command::new(targo);
    command.args(&selection.global_context_args);
    command.args(["metadata", "--format-version", "1"]);
    if let Some(manifest_path) = &selection.manifest_path {
        command.arg("--manifest-path").arg(manifest_path);
    }
    command.args(&selection.metadata_feature_args);
    let output = bounded_process::output(
        &mut command,
        &format!("canonical sibling `targo metadata` at {}", targo.display()),
        64 * 1024 * 1024,
        Duration::from_secs(5 * 60),
    )?;
    if !output.status.success() {
        let stderr = String::from_utf8(output.stderr).map_err(|error| {
            format!("canonical sibling `targo metadata` stderr was not UTF-8: {error}")
        })?;
        let detail = stderr.trim();
        return Err(if detail.is_empty() {
            format!("canonical sibling `targo metadata` at {} failed", targo.display())
        } else {
            format!("canonical sibling `targo metadata` at {} failed: {detail}", targo.display())
        });
    }
    let metadata = serde_json::from_slice::<CargoMetadata>(&output.stdout)
        .map_err(|error| format!("could not parse canonical `targo metadata` output: {error}"))?;
    let exact_resolutions = resolve_exact_package_specs(targo, &metadata, &selection)?;
    let packages = select_packages(&metadata, &selection, &exact_resolutions)?;
    let target_directory = validated_metadata_target_directory(&metadata.target_directory)?;
    Ok((metadata, selection, ResolvedCargoSelection { packages, target_directory }))
}

fn validated_metadata_target_directory(path: &Path) -> Result<PathBuf, String> {
    if path.as_os_str().is_empty()
        || !path.is_absolute()
        || path.components().any(|component| {
            matches!(component, std::path::Component::CurDir | std::path::Component::ParentDir)
        })
    {
        return Err(format!(
            "canonical `targo metadata` returned a non-canonical target_directory: {}",
            path.display()
        ));
    }
    Ok(path.to_path_buf())
}

#[derive(Debug, Deserialize)]
struct CargoUnitGraph {
    version: u32,
    units: Vec<CargoUnitGraphUnit>,
    roots: Vec<usize>,
}

#[derive(Debug, Deserialize)]
struct CargoUnitGraphUnit {
    pkg_id: String,
    target: CargoUnitGraphTarget,
    mode: String,
    platform: Option<String>,
}

#[derive(Debug, Deserialize)]
struct CargoUnitGraphTarget {
    name: String,
    kind: Vec<String>,
    crate_types: Vec<String>,
}

fn unit_graph_target_is_trust_cg_rlib(target: &CargoUnitGraphTarget) -> bool {
    !target.kind.iter().any(|kind| kind == "proc-macro")
        && target.kind.iter().any(|kind| matches!(kind.as_str(), "lib" | "rlib"))
        && !target.crate_types.is_empty()
        && target.crate_types.iter().all(|kind| matches!(kind.as_str(), "lib" | "rlib"))
}

fn validate_trust_cg_unit_graph(graph: &CargoUnitGraph) -> Result<(), String> {
    if graph.version != 1 {
        return Err(format!(
            "canonical Targo returned unsupported unit-graph version {}; expected 1",
            graph.version
        ));
    }
    if graph.roots.is_empty() {
        return Err("canonical Targo unit graph selected no primary build targets".to_string());
    }

    let mut unsupported_roots = Vec::new();
    for &index in &graph.roots {
        let unit = graph.units.get(index).ok_or_else(|| {
            format!(
                "canonical Targo unit graph root index {index} is outside its {}-unit inventory",
                graph.units.len()
            )
        })?;
        if !unit_graph_target_is_trust_cg_rlib(&unit.target) {
            unsupported_roots.push(format!(
                "{}::{} (kind={}, crate-types={}, mode={})",
                unit.pkg_id,
                unit.target.name,
                unit.target.kind.join("+"),
                unit.target.crate_types.join("+"),
                unit.mode,
            ));
        } else if unit.platform.is_none() {
            return Err(format!(
                "canonical Targo did not place selected target {}::{} behind an explicit target boundary; refusing to expose host build scripts/proc macros to trust-cg RUSTFLAGS",
                unit.pkg_id, unit.target.name
            ));
        }
    }
    if !unsupported_roots.is_empty() {
        unsupported_roots.sort();
        return Err(format!(
            "trust-cg can currently link only selected rlib library targets; unsupported primary Cargo target(s): {}. Use `--lib` for an rlib package or select the LLVM backend",
            unsupported_roots.join(", ")
        ));
    }

    // Cargo may select target-side artifact dependencies in addition to the
    // roots. They receive the same trust-cg RUSTFLAGS, so reject an unsupported
    // target-side build unit now instead of letting rustc fail after some units
    // have already produced artifacts. Host-only units have platform=null and
    // are deliberately compiled with LLVM by verified Targo. A custom-build
    // run unit is not a compiler invocation.
    let mut unsupported_target_units = graph
        .units
        .iter()
        .filter(|unit| unit.platform.is_some() && unit.mode == "build")
        .filter(|unit| !unit_graph_target_is_trust_cg_rlib(&unit.target))
        .map(|unit| {
            format!(
                "{}::{} (kind={}, crate-types={})",
                unit.pkg_id,
                unit.target.name,
                unit.target.kind.join("+"),
                unit.target.crate_types.join("+")
            )
        })
        .collect::<Vec<_>>();
    unsupported_target_units.sort();
    unsupported_target_units.dedup();
    if !unsupported_target_units.is_empty() {
        return Err(format!(
            "trust-cg cannot compile selected target-side Cargo unit(s): {}",
            unsupported_target_units.join(", ")
        ));
    }
    Ok(())
}

/// Ask canonical Targo for its exact dry unit graph before spawning the real
/// build. This delegates default-target, auto-target, required-feature,
/// workspace, and optional selector semantics to Cargo itself rather than
/// maintaining a second approximate selector implementation. `--unit-graph`
/// resolves the graph but does not compile units or execute build scripts.
pub(crate) fn preflight_trust_cg_cargo_targets_with_targo(
    args: &[String],
    targo: &Path,
    rustc: &Path,
) -> Result<(), String> {
    if args
        .iter()
        .take_while(|arg| arg.as_str() != "--")
        .any(|arg| arg == "--unit-graph" || arg.starts_with("--unit-graph="))
    {
        return Err("--unit-graph is reserved for targo-trust's target preflight".to_string());
    }
    let mut dry_args = args.to_vec();
    let separator = dry_args.iter().position(|arg| arg == "--").unwrap_or(dry_args.len());
    dry_args.insert(separator, "--unit-graph".to_string());

    let mut command = Command::new(targo);
    command
        .args(["--unverified", "-Z", "unstable-options", "build"])
        .args(&dry_args)
        // The real build pins the authenticated compiler and rejects wrappers.
        // Do the same for graph resolution: branded Targo otherwise falls back
        // to a PATH-resolved `trustc`, so preflight could inspect a different
        // toolchain (or fail even though the selected compiler is usable).
        .env("RUSTC", rustc)
        .env("CARGO_BUILD_RUSTC", rustc)
        .env("RUSTC_WRAPPER", "")
        .env("RUSTC_WORKSPACE_WRAPPER", "")
        .env("CARGO_BUILD_RUSTC_WRAPPER", "")
        .env("CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "")
        // This process resolves Cargo's selection only; it must not enter the
        // verified-child protocol without the real build's fresh session nonce
        // and complete policy. Canonical Targo therefore uses its explicit
        // `-Ztrust-verify=off` dry lane against the authenticated Trust compiler.
        .env_remove("TRUST_TARGO_VERIFY")
        .env_remove("TRUST_TARGO_TEST_EXECUTE_FRESH_SESSION")
        .env_remove("TRUST_TARGO_TEST_EXECUTION_MANIFEST")
        .env_remove("TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256")
        .env_remove("TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION")
        .env_remove("TRUST_TARGO_TEST_MONITOR_SESSION")
        // Ambient flags are sanitized and reassembled for the real build.
        // They must not affect this earlier selection-only compiler query.
        // TRUSTFLAGS overrides deliberately do not reach this preflight
        // either: verifier policy is inert in the `-Ztrust-verify=off` dry
        // lane, and forwarding it would only widen the surface that could
        // enter the verified-child protocol without the real build's fresh
        // session nonce (the probe/preflight session stripping is the fix for
        // the v24 early-exit regression — keep probes minimal).
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .env("CARGO_INCREMENTAL", "0")
        .env("TRUST_NO_MIGRATE_WARN", "1");
    let output = bounded_process::output(
        &mut command,
        &format!("canonical Targo unit-graph preflight at {}", targo.display()),
        64 * 1024 * 1024,
        Duration::from_secs(2 * 60),
    )?;
    if !output.status.success() {
        let stderr = String::from_utf8(output.stderr).map_err(|error| {
            format!("canonical Targo unit-graph preflight stderr was not UTF-8: {error}")
        })?;
        return Err(format!(
            "canonical Targo unit-graph preflight failed with {}: {}",
            output.status,
            stderr.trim()
        ));
    }
    let graph = serde_json::from_slice::<CargoUnitGraph>(&output.stdout)
        .map_err(|error| format!("canonical Targo returned an invalid unit graph: {error}"))?;
    validate_trust_cg_unit_graph(&graph)
}

/// Resolve whether Cargo already has an effective target boundary. An explicit
/// target keeps host build scripts/proc macros out of target RUSTFLAGS even
/// when it names the host triple. Trust-CG command construction injects the
/// exact trustc host only when CLI, environment, and Cargo config are all
/// silent, so it never overwrites a user's cross-target selection.
pub(crate) fn effective_cargo_target_with_targo(
    args: &[String],
    targo: &Path,
) -> Result<Option<String>, String> {
    let selection = CargoSelectionArgs::parse(args)?;
    if let Some(target) = selection.explicit_target_triple() {
        return Ok(Some(target.to_string()));
    }
    if let Some(target) = parse_cargo_build_target(std::env::var_os("CARGO_BUILD_TARGET"))? {
        return Ok(Some(target));
    }

    let mut command = Command::new(targo);
    command.args(&selection.global_context_args);
    command.args([
        "-Z",
        "unstable-options",
        "config",
        "get",
        "build.target",
        "--format",
        "json-value",
    ]);
    let output = bounded_process::output(
        &mut command,
        &format!("canonical Targo build.target probe at {}", targo.display()),
        1024 * 1024,
        Duration::from_secs(30),
    )?;
    if !output.status.success() {
        let stderr = String::from_utf8(output.stderr).map_err(|error| {
            format!("canonical Targo build.target probe stderr was not UTF-8: {error}")
        })?;
        if stderr.contains("config value `build.target` is not set") {
            return Ok(None);
        }
        return Err(format!(
            "canonical sibling `targo config get build.target` at {} failed with {}: {}",
            targo.display(),
            output.status,
            stderr.trim()
        ));
    }

    let configured: serde_json::Value =
        serde_json::from_slice(&output.stdout).map_err(|error| {
            format!("canonical `targo config get build.target` returned invalid JSON: {error}")
        })?;
    match configured {
        serde_json::Value::String(target) if !target.is_empty() => Ok(Some(target)),
        serde_json::Value::Array(mut targets) if targets.len() == 1 => targets
            .pop()
            .and_then(|target| target.as_str().map(str::to_string))
            .filter(|target| !target.is_empty())
            .map(Some)
            .ok_or_else(|| {
                "canonical Targo build.target array must contain one non-empty string".to_string()
            }),
        serde_json::Value::Null => Ok(None),
        serde_json::Value::Array(targets) => Err(format!(
            "evidence-grade trust-cg requires one effective Cargo target, but build.target contains {} entries",
            targets.len()
        )),
        other => Err(format!(
            "canonical `targo config get build.target` returned unexpected value {other}"
        )),
    }
}

fn parse_cargo_build_target(value: Option<OsString>) -> Result<Option<String>, String> {
    let Some(value) = value.filter(|value| !value.is_empty()) else {
        return Ok(None);
    };
    let target =
        value.into_string().map_err(|_| "CARGO_BUILD_TARGET is not valid Unicode".to_string())?;
    if target.trim() != target || target.is_empty() {
        return Err("CARGO_BUILD_TARGET must contain one non-empty, trimmed target".to_string());
    }
    Ok(Some(target))
}

/// Trust-CG emits machine objects only for this bridge-owned, audited target
/// matrix. Rustc itself recognizes many more triples; accepting one merely
/// because Cargo can resolve its target specification defers failure until
/// codegen and can misrepresent an unaudited cross-target request as a valid
/// proof build. Custom JSON targets are also rejected because a familiar
/// `llvm-target` string does not authenticate the rest of their data-layout,
/// ABI, atomics, or object-format semantics.
pub(crate) fn validate_trust_cg_effective_target(target: &str) -> Result<(), String> {
    const AUDITED: &[&str] = &[
        "aarch64-apple-darwin",
        "aarch64-unknown-linux-gnu",
        "aarch64-unknown-linux-musl",
        "x86_64-apple-darwin",
        "x86_64-pc-windows-gnu",
        "x86_64-pc-windows-gnullvm",
        "x86_64-pc-windows-msvc",
        "x86_64-unknown-linux-gnu",
        "x86_64-unknown-linux-musl",
    ];
    if AUDITED.contains(&target) {
        return Ok(());
    }
    let detail = if target.ends_with(".json") || Path::new(target).components().count() > 1 {
        "custom target specifications are not authenticated by Trust-CG's audited ABI/object-format matrix"
    } else {
        "the requested triple is outside Trust-CG's audited architecture/OS/ABI matrix"
    };
    Err(format!(
        "unsupported Trust-CG compile target `{target}`: {detail}; audited targets: {}",
        AUDITED.join(", ")
    ))
}

/// Canonical `targo pkgid` is the authority for exact Cargo package specs.
/// Reimplementing PackageIdSpec here drifted on partial versions, source URLs,
/// and non-workspace dependency packages. Patterns remain workspace-only in
/// Cargo and are handled below with Cargo's own `glob` crate.
fn resolve_exact_package_specs(
    targo: &Path,
    metadata: &CargoMetadata,
    selection: &CargoSelectionArgs,
) -> Result<BTreeMap<String, Vec<String>>, String> {
    let mut resolved = BTreeMap::new();

    // Cargo validates every explicit -p/--package spec even when --workspace
    // makes the eventual selection workspace-wide. Resolve it before spawning
    // the build so invalid invocations have no build-script or artifact effects.
    for spec in &selection.packages {
        if is_package_pattern(spec) || resolved.contains_key(spec) {
            continue;
        }
        let ids =
            constrain_pkgid_to_workspace(metadata, spec, canonical_pkgid(targo, selection, spec))?;
        resolved.insert(spec.clone(), ids);
    }

    if selection.workspace {
        for spec in &selection.excludes {
            if is_package_pattern(spec) || resolved.contains_key(spec) {
                continue;
            }
            let ids = match canonical_pkgid(targo, selection, spec) {
                Ok(id) => vec![id],
                Err(detail) => {
                    // Unmatched excludes are warning-only in Cargo. If pkgid
                    // was ambiguous across the full dependency graph, its
                    // canonical suggestions identify any matching workspace
                    // members that Cargo's workspace-scoped exclusion removes.
                    workspace_ids_suggested_by_pkgid(metadata, &detail)
                }
            };
            resolved.insert(spec.clone(), ids);
        }
    }

    Ok(resolved)
}

/// Cargo compile package specs are workspace-scoped, while `cargo pkgid`
/// searches the full resolved graph.  Constrain its canonical resolution back
/// to workspace members.  If a dependency makes a short spec globally
/// ambiguous, Cargo's diagnostic candidates can still identify one unambiguous
/// workspace member; selecting a dependency is always rejected.
fn constrain_pkgid_to_workspace(
    metadata: &CargoMetadata,
    spec: &str,
    resolution: Result<String, String>,
) -> Result<Vec<String>, String> {
    let members = metadata.workspace_members.iter().map(String::as_str).collect::<BTreeSet<_>>();
    match resolution {
        Ok(id) if members.contains(id.as_str()) => Ok(vec![id]),
        Ok(id) => Err(format!(
            "Cargo package selection `{spec}` resolved to non-workspace dependency `{id}`; -p/--package only selects workspace members"
        )),
        Err(detail) => {
            let candidates = workspace_ids_suggested_by_pkgid(metadata, &detail);
            match candidates.as_slice() {
                [id] => Ok(vec![id.clone()]),
                [] => Err(format!("canonical sibling `targo pkgid {spec}` failed: {detail}")),
                _ => Err(format!(
                    "Cargo package selection `{spec}` is ambiguous among workspace members: {}",
                    candidates.join(", ")
                )),
            }
        }
    }
}

fn canonical_pkgid(
    targo: &Path,
    selection: &CargoSelectionArgs,
    spec: &str,
) -> Result<String, String> {
    let mut command = Command::new(targo);
    command.arg("--color=never");
    command.args(&selection.global_context_args);
    command.arg("pkgid");
    if let Some(manifest_path) = &selection.manifest_path {
        command.arg("--manifest-path").arg(manifest_path);
    }
    command.arg(spec);
    let output = bounded_process::output(
        &mut command,
        &format!("canonical Targo pkgid probe at {}", targo.display()),
        1024 * 1024,
        Duration::from_secs(60),
    )?;
    if !output.status.success() {
        let stderr = String::from_utf8(output.stderr).map_err(|error| {
            format!("canonical Targo pkgid probe stderr was not UTF-8: {error}")
        })?;
        let detail = stderr.trim();
        return Err(if detail.is_empty() {
            format!("{} exited with {}", targo.display(), output.status)
        } else {
            detail.to_string()
        });
    }

    let stdout = String::from_utf8(output.stdout)
        .map_err(|error| format!("canonical `targo pkgid` output was not UTF-8: {error}"))?;
    let id = stdout.trim();
    if id.is_empty() || id.lines().count() != 1 {
        return Err(format!("canonical `targo pkgid` returned an invalid package ID: `{id}`"));
    }
    Ok(id.to_string())
}

fn workspace_ids_suggested_by_pkgid(metadata: &CargoMetadata, detail: &str) -> Vec<String> {
    if !detail.lines().any(|line| line.contains(" is ambiguous")) {
        return Vec::new();
    }
    let suggestions = detail.lines().map(str::trim).collect::<BTreeSet<_>>();
    metadata
        .packages
        .iter()
        .filter(|package| metadata.workspace_members.contains(&package.id))
        .filter(|package| {
            suggestions.contains(package.id.as_str())
                || suggestions.contains(format!("{}@{}", package.name, package.version).as_str())
        })
        .map(|package| package.id.clone())
        .collect()
}

/// Resolve wrapper arguments used by `targo trust build`. `None` is the
/// intentional single-file lane, which has no Cargo package gate.
pub(crate) fn resolve_cargo_gate_package_roots(
    wrapper_args: &[String],
) -> Result<Option<Vec<PathBuf>>, String> {
    resolve_cargo_gate_selection(wrapper_args)
        .map(|selection| selection.map(|selection| package_roots(selection.packages)))
}

fn resolve_cargo_gate_selection(
    wrapper_args: &[String],
) -> Result<Option<ResolvedCargoSelection>, String> {
    let parsed = parse_subcommand_args(wrapper_args).map_err(|error| {
        format!("could not parse build arguments for post-build gates: {error}")
    })?;
    if parsed.is_single_file {
        return Ok(None);
    }

    resolve_cargo_selection(&parsed.crate_mode_cargo_args()).map(Some)
}

fn select_packages(
    metadata: &CargoMetadata,
    selection: &CargoSelectionArgs,
    exact_resolutions: &BTreeMap<String, Vec<String>>,
) -> Result<Vec<ResolvedCargoPackage>, String> {
    let by_id = metadata
        .packages
        .iter()
        .map(|package| (package.id.as_str(), package))
        .collect::<BTreeMap<_, _>>();
    let members = metadata
        .workspace_members
        .iter()
        .map(|id| {
            by_id
                .get(id.as_str())
                .copied()
                .ok_or_else(|| format!("targo metadata omitted workspace member `{id}`"))
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Validate opt-in selectors independently of the eventual --workspace
    // selection. Exact specs were resolved by canonical `targo pkgid`; glob
    // specs use Cargo's workspace-only name matching. An unmatched include is
    // an error, unlike an unmatched --exclude (which Cargo warns about).
    for spec in &selection.packages {
        if is_package_pattern(spec) {
            if packages_matching_pattern(&members, spec)?.is_empty() {
                return Err(format!(
                    "Cargo package selection pattern `{spec}` matched no packages"
                ));
            }
        } else {
            let ids = exact_resolutions.get(spec).ok_or_else(|| {
                format!("missing canonical resolution for package selection `{spec}`")
            })?;
            if ids.is_empty() {
                return Err(format!("Cargo package selection `{spec}` matched no packages"));
            }
            for id in ids {
                if !metadata.workspace_members.contains(id) {
                    return Err(format!(
                        "Cargo package selection `{spec}` resolved to non-workspace dependency `{id}`; -p/--package only selects workspace members"
                    ));
                }
            }
        }
    }

    let selected = if selection.workspace {
        if selection.excludes.is_empty() {
            // Cargo accepts `--workspace -p SPEC` but still builds the whole
            // workspace. Every SPEC was validated above before any clean.
            members
        } else {
            let mut excluded = BTreeSet::new();
            for spec in &selection.excludes {
                if is_package_pattern(spec) {
                    for package in packages_matching_pattern(&members, spec)? {
                        excluded.insert(package.id.as_str());
                    }
                } else {
                    let ids = exact_resolutions.get(spec).ok_or_else(|| {
                        format!("missing canonical resolution for package exclusion `{spec}`")
                    })?;
                    excluded.extend(ids.iter().map(String::as_str));
                }
            }
            members.into_iter().filter(|package| !excluded.contains(package.id.as_str())).collect()
        }
    } else if !selection.packages.is_empty() {
        let mut ids = BTreeSet::new();
        let mut packages = Vec::new();
        for spec in &selection.packages {
            let matches = if is_package_pattern(spec) {
                packages_matching_pattern(&members, spec)?
            } else {
                exact_resolutions
                    .get(spec)
                    .ok_or_else(|| {
                        format!("missing canonical resolution for package selection `{spec}`")
                    })?
                    .iter()
                    .map(|id| {
                        by_id.get(id.as_str()).copied().ok_or_else(|| {
                            format!(
                                "canonical package selection `{spec}` resolved to `{id}`, which targo metadata omitted"
                            )
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?
            };
            for package in matches {
                if !metadata.workspace_members.contains(&package.id) {
                    return Err(format!(
                        "Cargo package selection resolved to non-workspace dependency `{}`; -p/--package only selects workspace members",
                        package.id
                    ));
                }
                if ids.insert(package.id.as_str()) {
                    packages.push(package);
                }
            }
        }
        packages
    } else {
        metadata
            .workspace_default_members
            .iter()
            .map(|id| {
                by_id.get(id.as_str()).copied().ok_or_else(|| {
                    format!("targo metadata omitted default workspace member `{id}`")
                })
            })
            .collect::<Result<Vec<_>, _>>()?
    };

    if selected.is_empty() {
        return Err("Cargo package selection resolved to no packages".to_string());
    }

    let mut packages = selected
        .into_iter()
        .map(|package| {
            let root = package.manifest_path.parent().map(Path::to_path_buf).ok_or_else(|| {
                format!("package `{}` has a manifest path without a parent", package.name)
            })?;
            Ok(ResolvedCargoPackage { id: package.id.clone(), name: package.name.clone(), root })
        })
        .collect::<Result<Vec<_>, String>>()?;
    packages.sort_by(|left, right| left.root.cmp(&right.root).then(left.id.cmp(&right.id)));
    packages.dedup_by(|left, right| left.id == right.id);
    Ok(packages)
}

fn package_roots(packages: Vec<ResolvedCargoPackage>) -> Vec<PathBuf> {
    let mut roots = packages.into_iter().map(|package| package.root).collect::<Vec<_>>();
    roots.sort();
    roots.dedup();
    roots
}

#[cfg(test)]
fn select_package_roots(
    metadata: &CargoMetadata,
    selection: &CargoSelectionArgs,
    exact_resolutions: &BTreeMap<String, Vec<String>>,
) -> Result<Vec<PathBuf>, String> {
    select_packages(metadata, selection, exact_resolutions).map(package_roots)
}

fn is_package_pattern(spec: &str) -> bool {
    // Cargo attempts PackageIdSpec parsing before falling back to glob syntax.
    // A source URL can legitimately contain brackets (for example an IPv6
    // host), so URL-shaped specs must go through canonical `targo pkgid`.
    !spec.contains("://") && spec.contains(['*', '?', '[', ']'])
}

fn packages_matching_pattern<'a>(
    members: &[&'a MetadataPackage],
    spec: &str,
) -> Result<Vec<&'a MetadataPackage>, String> {
    if spec.is_empty() {
        return Err("empty Cargo package specification".to_string());
    }
    let pattern = glob::Pattern::new(spec)
        .map_err(|error| format!("cannot build glob pattern from `{spec}`: {error}"))?;
    let matches = members
        .iter()
        .copied()
        .filter(|package| pattern.matches(&package.name))
        .collect::<Vec<_>>();
    if matches.is_empty() {
        // Cargo treats an unmatched `--exclude` pattern as a warning. The
        // caller does not need a separate mode: an empty match set naturally
        // excludes nothing, while an explicit opt-in is rejected below.
        return Ok(matches);
    }
    Ok(matches)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(ToString::to_string).collect()
    }

    fn exact(entries: &[(&str, &str)]) -> BTreeMap<String, Vec<String>> {
        entries.iter().map(|(spec, id)| ((*spec).to_string(), vec![(*id).to_string()])).collect()
    }

    #[test]
    fn pkgid_resolution_is_constrained_to_workspace_members() {
        let metadata = metadata();
        let dependency_id = "registry+https://example.invalid/index#dep@4.5.6";
        let error = constrain_pkgid_to_workspace(&metadata, "dep", Ok(dependency_id.to_string()))
            .expect_err("dependency package cannot be selected with -p");
        assert!(error.contains("non-workspace dependency"));

        let workspace_id = "path+file:///ws/a#a@1.0.0";
        let ambiguity = format!(
            "package ID specification `a` is ambiguous\n  {workspace_id}\n  registry+https://example.invalid/index#a@9.0.0"
        );
        assert_eq!(
            constrain_pkgid_to_workspace(&metadata, "a", Err(ambiguity))
                .expect("dependency ambiguity must not hide one workspace match"),
            [workspace_id]
        );
    }

    fn metadata() -> CargoMetadata {
        CargoMetadata {
            packages: vec![
                MetadataPackage {
                    id: "path+file:///ws/a#a@1.0.0".to_string(),
                    name: "a".to_string(),
                    version: "1.0.0".to_string(),
                    manifest_path: PathBuf::from("/ws/a/Cargo.toml"),
                },
                MetadataPackage {
                    id: "path+file:///ws/b#b@2.0.0".to_string(),
                    name: "b".to_string(),
                    version: "2.0.0".to_string(),
                    manifest_path: PathBuf::from("/ws/b/Cargo.toml"),
                },
                MetadataPackage {
                    id: "path+file:///ws/c#cat@3.0.0".to_string(),
                    name: "cat".to_string(),
                    version: "3.0.0".to_string(),
                    manifest_path: PathBuf::from("/ws/c/Cargo.toml"),
                },
                MetadataPackage {
                    id: "registry+https://example.invalid/index#dep@4.5.6".to_string(),
                    name: "dep".to_string(),
                    version: "4.5.6".to_string(),
                    manifest_path: PathBuf::from("/registry/dep/Cargo.toml"),
                },
            ],
            workspace_members: vec![
                "path+file:///ws/a#a@1.0.0".to_string(),
                "path+file:///ws/b#b@2.0.0".to_string(),
                "path+file:///ws/c#cat@3.0.0".to_string(),
            ],
            workspace_default_members: vec!["path+file:///ws/b#b@2.0.0".to_string()],
            target_directory: PathBuf::from("/ws/target"),
        }
    }

    #[test]
    fn metadata_target_directory_must_be_absolute_and_lexically_normal() {
        let target = std::env::temp_dir().join("targo-trust-metadata-target");
        assert_eq!(validated_metadata_target_directory(&target).unwrap(), target);
        assert!(validated_metadata_target_directory(Path::new("target")).is_err());
        assert!(validated_metadata_target_directory(&target.join("..").join("other")).is_err());
    }

    fn unit(
        name: &str,
        kind: &str,
        crate_types: &[&str],
        platform: Option<&str>,
    ) -> CargoUnitGraphUnit {
        CargoUnitGraphUnit {
            pkg_id: format!("path+file:///ws/{name}#{name}@1.0.0"),
            target: CargoUnitGraphTarget {
                name: name.to_string(),
                kind: vec![kind.to_string()],
                crate_types: crate_types.iter().map(|value| (*value).to_string()).collect(),
            },
            mode: "build".to_string(),
            platform: platform.map(str::to_string),
        }
    }

    #[test]
    fn trust_cg_target_preflight_matches_exact_audited_matrix() {
        for target in [
            "aarch64-apple-darwin",
            "aarch64-unknown-linux-gnu",
            "aarch64-unknown-linux-musl",
            "x86_64-apple-darwin",
            "x86_64-pc-windows-gnu",
            "x86_64-pc-windows-gnullvm",
            "x86_64-pc-windows-msvc",
            "x86_64-unknown-linux-gnu",
            "x86_64-unknown-linux-musl",
        ] {
            validate_trust_cg_effective_target(target)
                .unwrap_or_else(|error| panic!("audited target {target} was rejected: {error}"));
        }
        for unsupported in [
            "wasm32-unknown-unknown",
            "aarch64-pc-windows-msvc",
            "i686-unknown-linux-gnu",
            "targets/lookalike.json",
            "/tmp/x86_64-unknown-linux-gnu.json",
            " x86_64-unknown-linux-gnu",
        ] {
            let error = validate_trust_cg_effective_target(unsupported)
                .expect_err("unaudited cross/custom target must fail before Cargo");
            assert!(error.contains("unsupported Trust-CG compile target"), "{error}");
            assert!(error.contains(unsupported), "{error}");
        }
    }

    #[test]
    fn cargo_build_target_parser_rejects_noncanonical_text() {
        assert_eq!(
            parse_cargo_build_target(Some(OsString::from("x86_64-unknown-linux-gnu"))).unwrap(),
            Some("x86_64-unknown-linux-gnu".to_string())
        );
        assert_eq!(parse_cargo_build_target(Some(OsString::new())).unwrap(), None);
        for invalid in [" x86_64-unknown-linux-gnu", "x86_64-unknown-linux-gnu "] {
            assert!(
                parse_cargo_build_target(Some(OsString::from(invalid)))
                    .expect_err("whitespace target must reject")
                    .contains("trimmed")
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn cargo_build_target_parser_rejects_non_unicode_bytes() {
        use std::os::unix::ffi::OsStringExt as _;

        let error =
            parse_cargo_build_target(Some(OsString::from_vec(vec![b'x', b'8', b'6', b'_', 0xff])))
                .expect_err("lossy target conversion would change compiler semantics");
        assert!(error.contains("not valid Unicode"), "{error}");
    }

    #[test]
    fn trust_cg_unit_graph_accepts_target_rlibs_and_ignores_host_build_units() {
        let mut build_script = unit("build-script-build", "custom-build", &["bin"], None);
        build_script.mode = "build".to_string();
        let graph = CargoUnitGraph {
            version: 1,
            units: vec![
                unit("pkg", "lib", &["lib"], Some("x86_64-unknown-linux-gnu")),
                build_script,
                unit("proc_mac", "proc-macro", &["proc-macro"], None),
            ],
            roots: vec![0],
        };
        validate_trust_cg_unit_graph(&graph)
            .expect("target rlib plus LLVM-isolated host units should be admitted");
    }

    #[test]
    fn trust_cg_unit_graph_rejects_every_unadvertised_primary_artifact_class() {
        for (kind, crate_type) in [
            ("bin", "bin"),
            ("example", "bin"),
            ("test", "bin"),
            ("bench", "bin"),
            ("proc-macro", "proc-macro"),
            ("lib", "dylib"),
            ("lib", "cdylib"),
            ("lib", "staticlib"),
        ] {
            let graph = CargoUnitGraph {
                version: 1,
                units: vec![unit(
                    "unsupported",
                    kind,
                    &[crate_type],
                    Some("x86_64-unknown-linux-gnu"),
                )],
                roots: vec![0],
            };
            let error = validate_trust_cg_unit_graph(&graph)
                .expect_err("unadvertised target must fail before Cargo build");
            assert!(error.contains("unsupported"), "{kind}/{crate_type}: {error}");
        }
    }

    #[test]
    fn trust_cg_unit_graph_rejects_unsupported_target_side_dependency() {
        let graph = CargoUnitGraph {
            version: 1,
            units: vec![
                unit("root", "lib", &["rlib"], Some("x86_64-unknown-linux-gnu")),
                unit("artifact", "bin", &["bin"], Some("x86_64-unknown-linux-gnu")),
            ],
            roots: vec![0],
        };
        let error = validate_trust_cg_unit_graph(&graph)
            .expect_err("target-side binary dependency receives trust-cg and must reject");
        assert!(error.contains("target-side Cargo unit"), "{error}");
    }

    #[test]
    fn trust_cg_unit_graph_requires_valid_roots_and_explicit_target_boundary() {
        let no_boundary = CargoUnitGraph {
            version: 1,
            units: vec![unit("root", "lib", &["rlib"], None)],
            roots: vec![0],
        };
        assert!(
            validate_trust_cg_unit_graph(&no_boundary)
                .expect_err("host/target boundary is mandatory")
                .contains("explicit target boundary")
        );

        let invalid_root = CargoUnitGraph { version: 1, units: Vec::new(), roots: vec![7] };
        assert!(
            validate_trust_cg_unit_graph(&invalid_root)
                .expect_err("out-of-range root must fail closed")
                .contains("outside")
        );
    }

    #[test]
    fn parser_handles_repeated_packages_workspace_excludes_and_manifest_forms() {
        let parsed = CargoSelectionArgs::parse(&strings(&[
            "build",
            "-pa",
            "--package=b@2.0.0",
            "--workspace",
            "--exclude",
            "cat",
            "--manifest-path=/ws/Cargo.toml",
        ]))
        .expect("parse selection");
        assert_eq!(parsed.packages, ["a", "b@2.0.0"]);
        assert_eq!(parsed.excludes, ["cat"]);
        assert!(parsed.workspace);
        assert_eq!(parsed.manifest_path, Some(PathBuf::from("/ws/Cargo.toml")));

        let split = CargoSelectionArgs::parse(&strings(&["--manifest-path", "/other/Cargo.toml"]))
            .expect("split manifest path");
        assert_eq!(split.manifest_path, Some(PathBuf::from("/other/Cargo.toml")));
    }

    #[test]
    fn parser_does_not_treat_option_values_or_post_separator_args_as_selection() {
        let parsed = CargoSelectionArgs::parse(&strings(&[
            "--config",
            "-pnot-a-package",
            "--target",
            "wasm32-unknown-unknown",
            "--",
            "-p",
            "also-not-a-package",
        ]))
        .expect("parse opaque values");
        assert!(parsed.packages.is_empty());
        assert!(!parsed.workspace);

        let bare_package =
            CargoSelectionArgs::parse(&strings(&["-p", "--bin", "--target", "--workspace"]));
        assert!(bare_package.is_err(), "Cargo rejects --package without a SPEC");

        let artifact = CargoSelectionArgs::parse(&strings(&[
            "--artifact-dir",
            "-pnot-a-package",
            "-j-2",
            "--package=real-package",
        ]))
        .expect("parse artifact and joined job values");
        assert_eq!(artifact.packages, ["real-package"]);
    }

    #[test]
    fn parser_forwards_resolution_context_and_features_to_metadata() {
        let parsed = CargoSelectionArgs::parse(&strings(&[
            "--locked",
            "--config=net.retry=3",
            "-Zunstable-options",
            "--features",
            "one,two",
            "-Fthree",
            "--all-features",
            "--no-default-features",
            "--manifest-path=crates/app/Cargo.toml",
            "--target",
            "wasm32-unknown-unknown",
            "--target=wasm32-unknown-unknown",
            "--target-dir=out",
            "--profile",
            "production",
        ]))
        .expect("parse context");
        assert_eq!(
            parsed.global_context_args,
            ["--locked", "--config", "net.retry=3", "-Z", "unstable-options"]
        );
        assert_eq!(
            parsed.metadata_feature_args,
            [
                "--features",
                "one,two",
                "--features",
                "three",
                "--all-features",
                "--no-default-features"
            ]
        );
        assert_eq!(parsed.manifest_path(), Some(Path::new("crates/app/Cargo.toml")));
        CargoSelectionArgs::parse(&strings(&["-r"])).expect("release is a valueless flag");
        assert!(CargoSelectionArgs::parse(&strings(&["--target"])).is_err());
        assert!(CargoSelectionArgs::parse(&strings(&["--target-dir="])).is_err());
    }

    #[test]
    fn selector_returns_every_explicit_and_workspace_package_root() {
        let explicit = CargoSelectionArgs::parse(&strings(&["-p", "a", "-p=b@2.0.0"]))
            .expect("explicit packages");
        let explicit_ids =
            exact(&[("a", "path+file:///ws/a#a@1.0.0"), ("b@2.0.0", "path+file:///ws/b#b@2.0.0")]);
        assert_eq!(
            select_package_roots(&metadata(), &explicit, &explicit_ids)
                .expect("select explicit packages"),
            [PathBuf::from("/ws/a"), PathBuf::from("/ws/b")]
        );

        let workspace = CargoSelectionArgs::parse(&strings(&["--workspace", "--exclude=c*"]))
            .expect("workspace packages");
        assert_eq!(
            select_package_roots(&metadata(), &workspace, &BTreeMap::new())
                .expect("select workspace packages"),
            [PathBuf::from("/ws/a"), PathBuf::from("/ws/b")]
        );

        let all_with_validation = CargoSelectionArgs::parse(&strings(&["--workspace", "-p", "a"]))
            .expect("workspace plus package validation");
        assert_eq!(
            select_package_roots(
                &metadata(),
                &all_with_validation,
                &exact(&[("a", "path+file:///ws/a#a@1.0.0")]),
            )
            .expect("workspace still selects every member"),
            [PathBuf::from("/ws/a"), PathBuf::from("/ws/b"), PathBuf::from("/ws/c")]
        );

        let opt_out_validates_opt_in =
            CargoSelectionArgs::parse(&strings(&["--workspace", "-p", "a", "--exclude", "b"]))
                .expect("workspace opt-out selection");
        let selected_and_excluded =
            exact(&[("a", "path+file:///ws/a#a@1.0.0"), ("b", "path+file:///ws/b#b@2.0.0")]);
        assert_eq!(
            select_package_roots(&metadata(), &opt_out_validates_opt_in, &selected_and_excluded)
                .expect("exclude mode follows Cargo's opt-out semantics"),
            [PathBuf::from("/ws/a"), PathBuf::from("/ws/c")]
        );

        let invalid_workspace_spec =
            CargoSelectionArgs::parse(&strings(&["--workspace", "-p", "missing"]))
                .expect("parse invalid workspace package");
        assert!(
            select_package_roots(&metadata(), &invalid_workspace_spec, &BTreeMap::new()).is_err(),
            "workspace-wide selection must still validate every -p before cleaning"
        );

        assert!(CargoSelectionArgs::parse(&strings(&["--exclude", "a"])).is_err());
    }

    #[test]
    fn selector_rejects_canonical_dependency_resolutions() {
        let selection = CargoSelectionArgs::parse(&strings(&[
            "-p",
            "dep@4",
            "-p",
            "https://example.invalid/index#dep@4.5",
        ]))
        .expect("parse exact dependency specs");
        let dep_id = "registry+https://example.invalid/index#dep@4.5.6";
        let resolved =
            exact(&[("dep@4", dep_id), ("https://example.invalid/index#dep@4.5", dep_id)]);
        assert!(
            select_packages(&metadata(), &selection, &resolved)
                .expect_err("-p must never select a dependency")
                .contains("non-workspace dependency")
        );
    }

    #[test]
    fn distinct_compile_targets_fail_before_ambiguous_evidence_is_built() {
        let error = CargoSelectionArgs::parse(&strings(&[
            "--target",
            "wasm32-unknown-unknown",
            "--target=aarch64-unknown-linux-gnu",
        ]))
        .expect_err("one proof report must bind one compile target");
        assert!(error.contains("requires one effective compile target"), "{error}");
        assert!(error.contains("aarch64-unknown-linux-gnu"), "{error}");
        assert!(error.contains("wasm32-unknown-unknown"), "{error}");

        CargoSelectionArgs::parse(&strings(&[
            "--target",
            "wasm32-unknown-unknown",
            "--target=wasm32-unknown-unknown",
        ]))
        .expect("duplicate spelling of the same target remains a single Cargo unit domain");
    }

    #[test]
    fn selector_treats_unmatched_workspace_excludes_as_warning_only() {
        let exact_missing =
            CargoSelectionArgs::parse(&strings(&["--workspace", "--exclude=missing"]))
                .expect("parse exact exclusion");
        let mut unmatched = BTreeMap::new();
        unmatched.insert("missing".to_string(), Vec::new());
        assert_eq!(
            select_package_roots(&metadata(), &exact_missing, &unmatched)
                .expect("unmatched exact exclusion excludes nothing"),
            [PathBuf::from("/ws/a"), PathBuf::from("/ws/b"), PathBuf::from("/ws/c")]
        );

        let glob_missing = CargoSelectionArgs::parse(&strings(&["--workspace", "--exclude=z*"]))
            .expect("parse glob exclusion");
        assert_eq!(
            select_package_roots(&metadata(), &glob_missing, &BTreeMap::new())
                .expect("unmatched glob exclusion excludes nothing"),
            [PathBuf::from("/ws/a"), PathBuf::from("/ws/b"), PathBuf::from("/ws/c")]
        );
    }

    #[test]
    fn pkgid_ambiguity_suggestions_recover_workspace_matches() {
        let detail = "error: specification `a` is ambiguous\n\
                      help: re-run this command with one of the following specifications\n\
                        a@1.0.0\n\
                        registry+https://example.invalid/index#a@9.0.0";
        assert_eq!(
            workspace_ids_suggested_by_pkgid(&metadata(), detail),
            ["path+file:///ws/a#a@1.0.0"]
        );

        let merely_similar = "error: package ID specification `a@9` did not match any packages\n\
                              help: there are similar package ID specifications:\n\
                                a@1.0.0";
        assert!(workspace_ids_suggested_by_pkgid(&metadata(), merely_similar).is_empty());
    }

    #[test]
    fn selector_uses_metadata_default_members_and_fails_closed_on_bad_specs() {
        assert_eq!(
            select_package_roots(&metadata(), &CargoSelectionArgs::default(), &BTreeMap::new(),)
                .expect("select defaults"),
            [PathBuf::from("/ws/b")]
        );
        let missing =
            CargoSelectionArgs::parse(&strings(&["-p", "missing"])).expect("parse missing package");
        assert!(select_package_roots(&metadata(), &missing, &BTreeMap::new()).is_err());
    }

    #[test]
    fn selector_honors_root_versus_member_default_metadata() {
        // Canonical Targo computes `workspace_default_members` from its
        // current manifest: a root invocation uses configured/default
        // workspace members, while a member invocation uses that package.
        let mut root_metadata = metadata();
        root_metadata.workspace_default_members =
            vec!["path+file:///ws/a#a@1.0.0".to_string(), "path+file:///ws/b#b@2.0.0".to_string()];
        assert_eq!(
            select_package_roots(&root_metadata, &CargoSelectionArgs::default(), &BTreeMap::new(),)
                .expect("root defaults"),
            [PathBuf::from("/ws/a"), PathBuf::from("/ws/b")]
        );

        let mut member_metadata = metadata();
        member_metadata.workspace_default_members = vec!["path+file:///ws/c#cat@3.0.0".to_string()];
        assert_eq!(
            select_package_roots(
                &member_metadata,
                &CargoSelectionArgs::default(),
                &BTreeMap::new(),
            )
            .expect("member default"),
            [PathBuf::from("/ws/c")]
        );
    }

    #[test]
    fn selector_matches_cargo_glob_ranges_and_rejects_invalid_patterns() {
        let range =
            CargoSelectionArgs::parse(&strings(&["-p", "[a-b]"])).expect("parse range pattern");
        assert_eq!(
            select_package_roots(&metadata(), &range, &BTreeMap::new()).expect("select range"),
            [PathBuf::from("/ws/a"), PathBuf::from("/ws/b")]
        );

        let invalid = CargoSelectionArgs::parse(&strings(&["-p", "[a-b"]))
            .expect("selection parser leaves glob validation to selector");
        assert!(select_package_roots(&metadata(), &invalid, &BTreeMap::new()).is_err());
    }
}
