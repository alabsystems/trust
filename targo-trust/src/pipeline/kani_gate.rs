// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
//! Build-time Kani-manifest disclosure boundary.
//!
//! A package that declares a `kani` dependency is opting into a Kani harness
//! surface (`#[kani::proof]` / `#[kani::proof_for_contract]`).
//!
//! **Amended 2026-07-26 (two-language design v5, §3.2 MIGRATE).** Kani is now a
//! *zero-authority ingestion lane* on the TLA+ terms: its attributes may be read
//! as sugar and elaborated into Clean, and may never assert a proposition,
//! introduce an assumption, or acquire proof authority. This gate previously
//! rejected the build outright, on the premise that "Trust does not import that
//! legacy attribute surface". That premise is what the amendment changed, and
//! the rejection had become self-defeating: tippy machine-applicably rewrites
//! `#[kani::proof]` to `#[kani::harness]`, which is provided by the very crate
//! this gate refused — the autofix pointed at a door the build gate held shut.
//!
//! The other half of the original rationale still stands: trustc does not yet
//! publish the authenticated semantic-input/output manifest that would let a
//! post-build re-run certify the artifact just built. So the harnesses really
//! are unexamined by Trust. The false-green risk was never the *dependency*; it
//! was the word "silently". This gate therefore keeps the detection and
//! replaces the rejection with an unmissable disclosure: the build proceeds, and
//! the operator is told plainly that the Kani surface carried no authority and
//! was not examined. A gate keyed on the mere presence of a dependency was
//! testing the wrong thing; authority is what must be withheld, and it is
//! withheld structurally — nothing kani-derived can mint proof authority.
//!
//! **Why allowing the dependency is not fail-open** (verified 2026-07-26;
//! premises 1 and 2 re-worded 2026-09-12 for the T1 dylib lane, step S9). Each
//! premise is pinned by a `premise_*` test in this module: a pin that starts
//! failing means the gate must go back to rejecting.
//!
//! 1. **trustc registers no `kanitool` tool by default.** `#[kani::proof]` /
//!    `#[kani::harness]` expand to `#[kanitool::proof]`
//!    (`first-party/trust-mc/library/kani_macros`). The predefined tool list in
//!    `compiler/rustc_resolve/src/macros.rs` does not name it, so without an
//!    explicit `register_tool(kanitool)` the path is E0433, and nothing in
//!    `compiler/` names `kanitool`, so even a registered Kani tool attribute is
//!    inert to trustc. An inert attribute cannot mint an obligation or a
//!    verdict.
//! 2. **trust-mc engine code reaches trustc only as an explicitly selected
//!    external `-Zcodegen-backend`.** librustc_driver links none of
//!    `trust_mc_compiler`, `trust_mc_engine`, `codegen_ay` or `kani_middle`: in
//!    the compiler workspace's resolved graph no non-dev path leads from
//!    `rustc_driver` to the `trust-mc-engine` rlib, the `trust-mc-backend`
//!    cdylib (`librustc_codegen_trust_mc`), or `trust-mc-compiler` built with a
//!    feature that enables the engine; `crates/trust-bmc` reaches only
//!    trust-mc-driver, trust-mc-core and, at most, trust-mc-compiler's
//!    rustc-free facade. And `targo trust check`/`build` select `llvm` or
//!    `trust-cg` themselves (never trust-mc) and hand Cargo a lane in
//!    `TRUST_TARGO_LANE_RUSTFLAGS` (re-worded 2026-10-11 for T14a: the
//!    project's configured rustflags now reach the build, with the lane
//!    appended, where before the exported rustflags made Cargo ignore them);
//!    whenever a lane is present the sibling Targo drops every project
//!    `-Zcodegen-backend`, `-Zllvm-plugins` and `-Cllvm-args`, configured or
//!    inherited, naming each (`extra_args` in its `target_info.rs`). Every
//!    package-selection probe (`targo metadata`/`pkgid`/`config get`, the
//!    trust-cg unit-graph preflight, the post-build temporal metadata query)
//!    carries a lane too, with the authenticated trustc pinned and no rustc
//!    wrapper (`cargo_selection::selection_probe_command`). targo trust also
//!    refuses external code in `[host]` rustflags in any config file,
//!    `include` chain or variable (and any Cargo config it cannot examine),
//!    before any Cargo process starts, and prints an `UNEXAMINED_KANI_SURFACE`
//!    disclosure when a rustflags channel carried an external backend or
//!    `register_tool(kanitool)`, so a strict PASS is never a silent stand-in
//!    for a Kani verdict.
//! 3. `ProofObligationSource::KaniProofAttribute` exists only under
//!    `trust-mc-driver/src/list/` — the harness *listing* surface. It enumerates
//!    for display; it is not a verdict path and the compiler does not call it.
//!
//! So in a `targo trust check` or `build` the Kani surface is inert: there is no verdict to
//! soften and no authority to withhold that is not already structurally absent.
//!
//! Fail-closed is preserved where it still means something: a manifest that
//! cannot be inspected is a setup error, not a pass.
//!
//! This boundary was previously provided by `kani_cli::gate_build`; the
//! `targo trust kani` Route-2 shim around it is deleted (R2 deletion D-A).
//! Both `check` and `build` run it, through
//! `pipeline::disclose_zero_authority_ingestion_lanes` (TRUST-26).

use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::io;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use super::backend::{canonical_rustc_option_name, split_encoded_rustflags, split_plain_rustflags};
use crate::project_root::lexically_normalized;

const UNEXAMINED_KANI_SURFACE: &str = "its Kani harnesses were NOT examined and carry NO proof authority. Kani is a zero-authority ingestion lane (two-language design v5, §3.2): its attributes may be read as sugar and elaborated into Clean, but may never assert a proposition or certify a build.";

/// What `build` adds after [`UNEXAMINED_KANI_SURFACE`].
const UNEXAMINED_KANI_SURFACE_BUILD_TAIL: &str = "trustc does not yet emit the authenticated semantic-input digest and output-artifact binding that a post-build re-run would need, so nothing here certifies the current source identity or the artifact just built. Do not read a successful build as a discharged Kani proof; run `targo trust check` for the verdicts Trust actually stands behind";

/// What `check` adds after [`UNEXAMINED_KANI_SURFACE`].
const UNEXAMINED_KANI_SURFACE_CHECK_TAIL: &str = "A PASS from this check covers only the obligations trustc itself verified; it is not a Kani verdict";

/// The per-package Kani dependency disclosure for `verb`.
fn kani_dependency_disclosure(verb: super::CompileVerb, root: &Path) -> String {
    let tail = match verb {
        super::CompileVerb::Check => UNEXAMINED_KANI_SURFACE_CHECK_TAIL,
        super::CompileVerb::Build => UNEXAMINED_KANI_SURFACE_BUILD_TAIL,
    };
    format!(
        "targo trust {}: warning: {} declares a `kani` dependency — {UNEXAMINED_KANI_SURFACE} {tail}",
        verb.as_str(),
        root.display()
    )
}

/// Grep-stable tag on the disclosure `targo trust check`/`build` print when an
/// inherited rustflags channel carries a Kani surface that targo strips.
pub(crate) const UNEXAMINED_KANI_SURFACE_TAG: &str = "UNEXAMINED_KANI_SURFACE";

/// The codegen backends linked into librustc_driver (`builtin_codegen_backend`
/// in `compiler/rustc_interface/src/util.rs`). Every other `-Zcodegen-backend`
/// value, a sysroot backend name or a path, loads an external dylib: the only
/// way trust-mc engine code reaches trustc.
pub(crate) const TRUSTC_BUILTIN_CODEGEN_BACKENDS: &[&str] =
    &["dummy", "llvm", "trust-cg", "trust_cg"];

const UNEXAMINED_KANI_SURFACE_IN_SESSION: &str = "targo trust's lane drops every project codegen backend, LLVM plugin and LLVM argument, configured or inherited, from the build and from every package-selection probe (each run with the authenticated trustc pinned), and targo trust refuses an external backend in `[host]` rustflags (and any Cargo config it cannot examine), so no external codegen backend, and no trust-mc engine, ran in this session: its Kani harnesses were NOT examined and carry NO proof authority. Kani is a zero-authority ingestion lane (two-language design v5, §3.2): Kani text never asserts a proposition, never introduces an assumption and never certifies a build. A PASS from this run covers only the obligations trustc itself verified; it is not a Kani verdict";

/// One inherited rustflags channel and the arguments it carries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RustflagsSource {
    pub(crate) origin: String,
    pub(crate) args: Vec<String>,
    /// `[host]` rustflags: Cargo gives them to host artifacts and its host
    /// target-info query under `-Zhost-config`, and `targo trust` cannot
    /// override them (see `host_rustflags_external_code_refusal`).
    pub(crate) host_artifacts: bool,
    /// Why this Cargo config (a file or an `include` entry) could not be
    /// examined, or `None` when its flags were read. An unexamined config could
    /// carry `[host]` rustflags, so it refuses the run
    /// (`host_rustflags_external_code_refusal`).
    pub(crate) unexamined: Option<String>,
}

fn registers_kanitool(attribute: &str) -> bool {
    let compact = attribute.chars().filter(|c| !c.is_whitespace()).collect::<String>();
    compact
        .strip_prefix("register_tool(")
        .and_then(|tools| tools.strip_suffix(')'))
        .is_some_and(|tools| tools.split(',').any(|tool| tool == "kanitool"))
}

/// What one `-Z` flag would put into trustc.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TrustcSurface {
    /// A non-builtin `-Zcodegen-backend`: an external dylib, the only way
    /// trust-mc engine code reaches trustc.
    ExternalCodegenBackend,
    /// A non-empty `-Zllvm-plugins`: LLVM plugin dylibs loaded into trustc.
    LlvmPlugins,
    /// `-Zcrate-attr=register_tool(kanitool)`: inert to trustc (premise 1).
    KanitoolRegistration,
}

/// Every `-Z` flag in `args`, in either spelling, that loads external code
/// into trustc or registers the Kani tool, with what it does.
fn trustc_surface_flags(args: &[String]) -> Vec<(String, TrustcSurface)> {
    let mut found = Vec::new();
    let mut index = 0;
    while index < args.len() {
        let split = args[index] == "-Z";
        let option = if split {
            args.get(index + 1).map(String::as_str)
        } else {
            args[index].strip_prefix("-Z").filter(|option| !option.is_empty())
        };
        if let Some((name, value)) = option.and_then(|option| option.split_once('=')) {
            let surface = match canonical_rustc_option_name(name).as_ref() {
                "codegen-backend" if !TRUSTC_BUILTIN_CODEGEN_BACKENDS.contains(&value) => {
                    Some(TrustcSurface::ExternalCodegenBackend)
                }
                "llvm-plugins" if !value.trim().is_empty() => Some(TrustcSurface::LlvmPlugins),
                "crate-attr" if registers_kanitool(value) => {
                    Some(TrustcSurface::KanitoolRegistration)
                }
                _ => None,
            };
            if let Some(surface) = surface {
                let flag = if split {
                    format!("-Z {}", option.unwrap_or_default())
                } else {
                    args[index].clone()
                };
                found.push((flag, surface));
            }
        }
        index += if split { 2 } else { 1 };
    }
    found
}

/// The flags in `args` that would put a Kani surface into trustc: a
/// non-builtin `-Zcodegen-backend` (an external backend such as the trust-mc
/// dylib) or `-Zcrate-attr=register_tool(kanitool)`, in either `-Z` spelling.
pub(crate) fn kani_surface_flags(args: &[String]) -> Vec<String> {
    trustc_surface_flags(args)
        .into_iter()
        .filter(|(_, surface)| *surface != TrustcSurface::LlvmPlugins)
        .map(|(flag, _)| flag)
        .collect()
}

fn whitespace_rustflags(flags: &str) -> Vec<String> {
    flags.split_whitespace().map(str::to_string).collect()
}

fn toml_rustflags(value: &toml::Value) -> Option<Vec<String>> {
    match value {
        toml::Value::String(flags) => Some(whitespace_rustflags(flags)),
        toml::Value::Array(flags) => {
            Some(flags.iter().filter_map(toml::Value::as_str).map(str::to_string).collect())
        }
        _ => None,
    }
}

fn push_config_rustflags(origin: &str, config: &toml::Value, sources: &mut Vec<RustflagsSource>) {
    if let Some(args) =
        config.get("build").and_then(|build| build.get("rustflags")).and_then(toml_rustflags)
    {
        sources.push(RustflagsSource {
            origin: format!("{origin} build.rustflags"),
            args,
            host_artifacts: false,
            unexamined: None,
        });
    }
    if let Some(targets) = config.get("target").and_then(toml::Value::as_table) {
        for (target, table) in targets {
            if let Some(args) = table.get("rustflags").and_then(toml_rustflags) {
                sources.push(RustflagsSource {
                    origin: format!("{origin} target.{target}.rustflags"),
                    args,
                    host_artifacts: false,
                    unexamined: None,
                });
            }
        }
    }
    // `[host] rustflags` and `[host.<triple>] rustflags` (`-Zhost-config`).
    if let Some(host) = config.get("host").and_then(toml::Value::as_table) {
        for (key, value) in host {
            let (key, args) = if key == "rustflags" {
                ("host.rustflags".to_string(), toml_rustflags(value))
            } else {
                (format!("host.{key}.rustflags"), value.get("rustflags").and_then(toml_rustflags))
            };
            if let Some(args) = args {
                sources.push(RustflagsSource {
                    origin: format!("{origin} {key}"),
                    args,
                    host_artifacts: true,
                    unexamined: None,
                });
            }
        }
    }
}

fn read_cargo_config_file(path: &Path) -> Result<toml::Value, String> {
    crate::input_limits::read_bounded_utf8_file(
        path,
        crate::input_limits::MAX_RELEASE_METADATA_BYTES,
    )
    .map_err(|error| format!("unreadable: {error}"))?
    .parse::<toml::Value>()
    .map_err(|error| {
        format!("not valid TOML: {}", error.to_string().lines().next().unwrap_or_default())
    })
}

/// A Cargo config that could not be examined: a `[host]` source that refuses
/// the run.
fn unexamined_config(origin: String, reason: &str) -> RustflagsSource {
    RustflagsSource {
        origin,
        args: Vec::new(),
        host_artifacts: true,
        unexamined: Some(reason.to_string()),
    }
}

/// The rustflags sources of one Cargo config file and of its `include` chain.
/// `loaded` holds every file already reached from the same top-level config:
/// Cargo rejects reaching one twice as an include cycle.
fn push_config_file_rustflags(
    path: &Path,
    loaded: &mut BTreeSet<PathBuf>,
    sources: &mut Vec<RustflagsSource>,
) {
    let origin = path.display().to_string();
    if !loaded.insert(path.to_path_buf()) {
        sources.push(unexamined_config(origin, "Cargo rejects this config `include` cycle"));
        return;
    }
    match read_cargo_config_file(path) {
        Ok(config) => push_config_value_rustflags(&origin, &config, path.parent(), loaded, sources),
        Err(reason) => sources.push(unexamined_config(origin, &reason)),
    }
}

/// Every rustflags source in one Cargo config value and, recursively, in the
/// files its `include` key pulls in (stable since Cargo 1.93).
///
/// Cargo resolves each `include` path against `include_base`: the including
/// file's directory, or the working directory for an inline `--config` value.
/// It normalizes the path lexically, skips a missing `optional = true` entry,
/// and rejects everything else it cannot load: a missing file, a cycle, an
/// `include` that is not an array, an entry that is not a string or a
/// `{ path, optional }` table, or a path that does not end in `.toml` or holds
/// glob or template characters (measured on targo 45dc60873, 2026-09-12). Each
/// of those becomes an unexamined source instead of being skipped: it could
/// carry `[host]` rustflags, and Cargo rejects the config anyway, so refusing
/// loses no working run. Merge order does not matter here, because every table
/// in the chain is reported.
fn push_config_value_rustflags(
    origin: &str,
    config: &toml::Value,
    include_base: Option<&Path>,
    loaded: &mut BTreeSet<PathBuf>,
    sources: &mut Vec<RustflagsSource>,
) {
    if let Some(include) = config.get("include") {
        let include_origin = format!("{origin} include");
        let Some(entries) = include.as_array() else {
            sources.push(unexamined_config(
                include_origin,
                "Cargo requires `include` to be an array of paths or `{ path, optional }` tables",
            ));
            push_config_rustflags(origin, config, sources);
            return;
        };
        for entry in entries {
            let (path, optional) = match entry {
                toml::Value::String(path) => (path.as_str(), false),
                toml::Value::Table(table) => {
                    let Some(path) = table.get("path").and_then(toml::Value::as_str) else {
                        sources.push(unexamined_config(
                            include_origin.clone(),
                            "an `include` table needs a string `path`",
                        ));
                        continue;
                    };
                    match table.get("optional") {
                        None => (path, false),
                        Some(toml::Value::Boolean(optional)) => (path, *optional),
                        Some(_) => {
                            sources.push(unexamined_config(
                                format!("{include_origin} `{path}`"),
                                "an `include` table's `optional` must be a boolean",
                            ));
                            continue;
                        }
                    }
                }
                _ => {
                    sources.push(unexamined_config(
                        include_origin.clone(),
                        "an `include` entry must be a string or a `{ path, optional }` table",
                    ));
                    continue;
                }
            };
            if Path::new(path).extension() != Some(OsStr::new("toml"))
                || path.contains(&['*', '?', '[', ']', '{', '}'][..])
            {
                sources.push(unexamined_config(
                    format!("{include_origin} `{path}`"),
                    "Cargo includes only `.toml` paths without glob or template characters",
                ));
                continue;
            }
            let Some(base) = include_base else {
                sources.push(unexamined_config(
                    format!("{include_origin} `{path}`"),
                    "no working directory to resolve it against",
                ));
                continue;
            };
            let resolved = lexically_normalized(&base.join(path));
            if optional && !resolved.exists() {
                continue;
            }
            push_config_file_rustflags(&resolved, loaded, sources);
        }
    }
    push_config_rustflags(origin, config, sources);
}

/// `--config` values in Cargo's own arguments (before `--`).
fn cargo_cli_config_values(cargo_args: &[String]) -> Vec<&str> {
    let mut values = Vec::new();
    let mut index = 0;
    while index < cargo_args.len() {
        let argument = cargo_args[index].as_str();
        if argument == "--" {
            break;
        }
        if argument == "--config" {
            values.extend(cargo_args.get(index + 1).map(String::as_str));
            index += 2;
            continue;
        }
        values.extend(argument.strip_prefix("--config="));
        index += 1;
    }
    values
}

/// Every rustflags channel a plain Cargo build would have read: `RUSTFLAGS`,
/// `CARGO_ENCODED_RUSTFLAGS`, `CARGO_BUILD_RUSTFLAGS`,
/// `CARGO_TARGET_<triple>_RUSTFLAGS`, `CARGO_HOST_RUSTFLAGS` /
/// `CARGO_HOST_<triple>_RUSTFLAGS`, Cargo `--config` values (inline TOML or a
/// file), and `build.rustflags` / `target.<triple-or-cfg>.rustflags` /
/// `host.rustflags` / `host.<triple>.rustflags` in every `.cargo/config[.toml]`
/// from `cwd` upward and in `cargo_home`, and in every file those `include`.
/// Under `targo trust`'s lane the sibling
/// Targo drops an external backend, LLVM plugins and LLVM arguments from every
/// channel (T14a), and targo trust refuses `[host]` outright when it carries
/// external code. Rustdoc flags (`RUSTDOCFLAGS`, `build.rustdocflags`, ...) are
/// deliberately not read: `targo trust check`/`build` never run rustdoc, and
/// `targo trust test` compiles `--no-run` and fails `--doc` closed, so no
/// rustdoc codegen runs in which a backend could load. Cargo `include` chains
/// are followed from every config file and `--config` value
/// (`push_config_value_rustflags`). A config file or `include` entry that
/// cannot be read, parsed or resolved becomes an unexamined `[host]` source,
/// which refuses the run: it could carry `[host]` rustflags, and Cargo rejects
/// such a config itself, so refusing loses no working run.
pub(crate) fn inherited_rustflags_sources(
    cwd: Option<&Path>,
    cargo_home: Option<&Path>,
    cargo_args: &[String],
    environment: &[(String, String)],
) -> Vec<RustflagsSource> {
    let mut sources = Vec::new();
    for (key, value) in environment {
        let (args, host_artifacts) = match key.as_str() {
            "RUSTFLAGS" => {
                (split_plain_rustflags(value).into_iter().map(str::to_string).collect(), false)
            }
            "CARGO_ENCODED_RUSTFLAGS" => {
                (split_encoded_rustflags(value).into_iter().map(str::to_string).collect(), false)
            }
            "CARGO_BUILD_RUSTFLAGS" => (whitespace_rustflags(value), false),
            _ if key.starts_with("CARGO_TARGET_") && key.ends_with("_RUSTFLAGS") => {
                (whitespace_rustflags(value), false)
            }
            _ if key.starts_with("CARGO_HOST_") && key.ends_with("_RUSTFLAGS") => {
                (whitespace_rustflags(value), true)
            }
            _ => continue,
        };
        sources.push(RustflagsSource {
            origin: key.clone(),
            args,
            host_artifacts,
            unexamined: None,
        });
    }

    for value in cargo_cli_config_values(cargo_args) {
        // Cargo's own rule: a `--config` value naming an existing path is a
        // config file, whose `include` paths resolve against its directory;
        // anything else is inline TOML, whose `include` paths resolve against
        // the working directory.
        let path = match cwd {
            Some(cwd) => cwd.join(value),
            None => PathBuf::from(value),
        };
        if !value.is_empty() && path.exists() {
            push_config_file_rustflags(&path, &mut BTreeSet::new(), &mut sources);
        } else if let Ok(config) = value.parse::<toml::Value>() {
            push_config_value_rustflags(
                "--config",
                &config,
                cwd,
                &mut BTreeSet::new(),
                &mut sources,
            );
        }
    }

    let mut config_files = Vec::new();
    for directory in cwd.into_iter().flat_map(Path::ancestors) {
        config_files.push(directory.join(".cargo").join("config.toml"));
        config_files.push(directory.join(".cargo").join("config"));
    }
    if let Some(cargo_home) = cargo_home {
        config_files.push(cargo_home.join("config.toml"));
        config_files.push(cargo_home.join("config"));
    }
    let mut seen = BTreeSet::new();
    for path in config_files {
        if !seen.insert(path.clone()) || !path.is_file() {
            continue;
        }
        push_config_file_rustflags(&path, &mut BTreeSet::new(), &mut sources);
    }
    sources
}

/// The `UNEXAMINED_KANI_SURFACE` disclosure for `sources`, or `None` when no
/// channel carries a Kani surface.
pub(crate) fn unexamined_kani_surface_disclosure(sources: &[RustflagsSource]) -> Option<String> {
    let findings = sources
        .iter()
        .filter_map(|source| {
            let flags = kani_surface_flags(&source.args);
            (!flags.is_empty()).then(|| format!("`{}` carries {}", source.origin, flags.join(" ")))
        })
        .collect::<Vec<_>>();
    if findings.is_empty() {
        return None;
    }
    Some(format!(
        "warning: {UNEXAMINED_KANI_SURFACE_TAG}: {}. {UNEXAMINED_KANI_SURFACE_IN_SESSION}",
        findings.join("; ")
    ))
}

/// Every rustflags channel of this process: its environment, working
/// directory, Cargo home and the Cargo arguments of the run.
fn process_rustflags_sources(cargo_args: &[String]) -> Vec<RustflagsSource> {
    let cwd = std::env::current_dir().ok();
    let cargo_home = std::env::var_os("CARGO_HOME")
        .filter(|home| !home.is_empty())
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".cargo")));
    let environment = std::env::vars_os()
        .filter_map(|(key, value)| Some((key.into_string().ok()?, value.into_string().ok()?)))
        .collect::<Vec<_>>();
    inherited_rustflags_sources(cwd.as_deref(), cargo_home.as_deref(), cargo_args, &environment)
}

/// The disclosure for this process: its environment, working directory, Cargo
/// home and the Cargo arguments of the run.
pub(crate) fn inherited_kani_surface_disclosure(cargo_args: &[String]) -> Option<String> {
    unexamined_kani_surface_disclosure(&process_rustflags_sources(cargo_args))
}

/// Grep-stable tag on the refusal for external code in `[host]` rustflags.
pub(crate) const HOST_RUSTFLAGS_EXTERNAL_CODE_TAG: &str = "HOST_RUSTFLAGS_EXTERNAL_CODE";

/// The refusal for `sources` whose `[host]` rustflags would load external code
/// into trustc (a non-builtin `-Zcodegen-backend`, such as the trust-mc dylib,
/// or `-Zllvm-plugins`), or `None`.
///
/// `[host]` rustflags are the one rustflags channel `targo trust` cannot
/// override. Under `-Zhost-config` (a `-Z` flag, an `[unstable]` config table
/// or `CARGO_UNSTABLE_HOST_CONFIG`) Cargo hands host artifacts (build scripts,
/// proc macros) and its host target-info query ONLY those flags, ignoring the
/// exported `RUSTFLAGS` and even an empty `CARGO_ENCODED_RUSTFLAGS`, and
/// verified Targo layers its policy on top without rejecting a non-builtin
/// backend. Measured 2026-09-12 on targo 45dc60873: with
/// `CARGO_ENCODED_RUSTFLAGS=""`, `targo -Zhost-config -Ztarget-applies-to-host
/// metadata` still handed trustc a `host.rustflags` backend, and so did
/// `[host.<triple>]`, `CARGO_HOST_RUSTFLAGS`, and a config-file `[unstable]`
/// table. Whether host-config is on is spread over too many channels to decide
/// soundly here, so such flags refuse the run either way: fail closed.
///
/// `sources` cover every Cargo `include` chain, and a config file or `include`
/// entry `inherited_rustflags_sources` could not examine refuses the run as
/// well, since it could carry exactly such flags (S9 re-review, measured on
/// targo 45dc60873: a `[host.<triple>]` backend one `include` away reached
/// trustc's host target-info query past this refusal).
pub(crate) fn host_rustflags_external_code_refusal(sources: &[RustflagsSource]) -> Option<String> {
    let findings = sources
        .iter()
        .filter(|source| source.host_artifacts)
        .filter_map(|source| {
            if let Some(reason) = &source.unexamined {
                return Some(format!("`{}` could not be examined ({reason})", source.origin));
            }
            let flags = trustc_surface_flags(&source.args)
                .into_iter()
                .filter(|(_, surface)| *surface != TrustcSurface::KanitoolRegistration)
                .map(|(flag, _)| flag)
                .collect::<Vec<_>>();
            (!flags.is_empty()).then(|| format!("`{}` carries {}", source.origin, flags.join(" ")))
        })
        .collect::<Vec<_>>();
    if findings.is_empty() {
        return None;
    }
    Some(format!(
        "{HOST_RUSTFLAGS_EXTERNAL_CODE_TAG}: {}. `[host]` rustflags are the one rustflags channel targo trust cannot strip: under -Zhost-config Cargo hands them to host artifacts and to its host target-info query regardless of the rustflags targo sets, so that code would load into trustc during this run, package selection included, and a Cargo config (or `include`) targo trust cannot examine could carry exactly that. This is refused even when -Zhost-config is off and Cargo would ignore `[host]`: delete the stanza or variable (or repair the config) rather than looking for a host-config switch. targo trust selects `llvm` or `trust-cg` itself, and the trust-mc engine is never its codegen backend",
        findings.join("; ")
    ))
}

/// The `[host]` rustflags refusal for this process (see
/// `host_rustflags_external_code_refusal`).
pub(crate) fn inherited_host_rustflags_refusal(cargo_args: &[String]) -> Option<String> {
    host_rustflags_external_code_refusal(&process_rustflags_sources(cargo_args))
}

/// What a `-Ztrust-verify=off` unit prints when its codegen ran in an external
/// backend (the trust-mc dylib): trustc's own zero-obligation note, then the
/// backend's Kani text. None of it is Trust proof evidence.
#[cfg(test)]
pub(crate) const EXTERNAL_BACKEND_VERIFY_OFF_STDERR: &str = "\
note: compiled WITHOUT Trust verification \u{2014} 0 obligations checked
[AY:COMPILER_ROUTE route=trustc backend=/abs/librustc_codegen_trust_mc.dylib]
Checking harness check_add...
VERIFICATION:- SUCCESSFUL
Verification Time: 0.01s
Complete - 1 successfully verified harnesses, 0 failures, 1 total.
";

/// The same unit when the compiler also emits a terminal crate summary with
/// zero counts: still no function row and nothing verified.
#[cfg(test)]
pub(crate) const EXTERNAL_BACKEND_VERIFY_OFF_STDERR_WITH_ZERO_SUMMARY: &str = "\
note: compiled WITHOUT Trust verification \u{2014} 0 obligations checked
VERIFICATION:- SUCCESSFUL
TRUST_JSON:{\"type\":\"crate_summary\",\"crate_name\":\"harness\",\"package_name\":\"harness\",\"primary_package\":true,\"functions_analyzed\":0,\"functions_verified\":0,\"total_proved\":0,\"total_failed\":0,\"total_unknown\":0,\"total_timed_out\":0,\"total_skipped\":0,\"total_runtime_checked\":0,\"total_obligations\":0}
";

/// Post-compile disclosure gate run by both `targo trust check` and
/// `targo trust build` (via `pipeline::disclose_zero_authority_ingestion_lanes`).
///
/// A failed run is returned immediately without resolving packages. On a
/// successful run, every selected package manifest is inspected; a package
/// that declares a `kani` dependency (directly, renamed via `package = "kani"`,
/// in a target-specific section, or through a workspace-inherited alias) gets a
/// prominent disclosure on stderr and the run is allowed to proceed.
///
/// This does not weaken any proof claim, because a Kani harness never had one:
/// the ingestion lane forbids kani-derived text from acquiring proof authority,
/// so there is no verdict here to soften. What changed is that the operator is
/// now told, rather than the build being refused for spelling its sugar.
pub(crate) fn disclose_after_compile(
    verb: super::CompileVerb,
    result: ExitCode,
    args: &[String],
) -> ExitCode {
    if result != ExitCode::SUCCESS {
        return result;
    }
    let verb_name = verb.as_str();

    let package_roots = match super::resolve_cargo_gate_package_roots(args) {
        Ok(Some(roots)) => roots,
        Ok(None) => return result,
        Err(error) => {
            eprintln!(
                "targo trust {verb_name}: Kani gate could not resolve selected packages: {error}"
            );
            return ExitCode::from(2);
        }
    };

    for root in package_roots {
        match manifest_declares_kani_dependency(&root) {
            Ok(false) => {}
            Ok(true) => eprintln!("{}", kani_dependency_disclosure(verb, &root)),
            Err(error) => {
                eprintln!(
                    "targo trust {verb_name}: Kani gate could not inspect {} before applying the \
                     authenticated-input boundary: {error}",
                    root.display()
                );
                return ExitCode::from(2);
            }
        }
    }
    result
}

fn dependency_table_declares_kani(value: &toml::Value) -> bool {
    let Some(table) = value.as_table() else {
        return false;
    };
    table.iter().any(|(name, dependency)| {
        name == "kani"
            || dependency
                .as_table()
                .and_then(|detail| detail.get("package"))
                .and_then(toml::Value::as_str)
                == Some("kani")
    })
}

fn dependency_table_workspace_aliases(value: &toml::Value, aliases: &mut BTreeSet<String>) {
    let Some(table) = value.as_table() else {
        return;
    };
    for (name, dependency) in table {
        if dependency
            .as_table()
            .and_then(|detail| detail.get("workspace"))
            .and_then(toml::Value::as_bool)
            == Some(true)
        {
            aliases.insert(name.clone());
        }
    }
}

fn workspace_manifest_for_package(
    manifest_dir: &Path,
    package_manifest: &toml::Value,
) -> Result<Option<PathBuf>, String> {
    if let Some(workspace) = package_manifest
        .get("package")
        .and_then(toml::Value::as_table)
        .and_then(|package| package.get("workspace"))
        .and_then(toml::Value::as_str)
    {
        let path = manifest_dir.join(workspace).join("Cargo.toml");
        return path
            .canonicalize()
            .map(Some)
            .map_err(|error| format!("could not resolve inherited workspace manifest: {error}"));
    }

    for ancestor in manifest_dir.ancestors() {
        let candidate = ancestor.join("Cargo.toml");
        let text = match crate::input_limits::read_bounded_utf8_file(
            &candidate,
            crate::input_limits::MAX_RELEASE_METADATA_BYTES,
        ) {
            Ok(text) => text,
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(error) => {
                return Err(format!(
                    "could not inspect ancestor manifest {}: {error}",
                    candidate.display()
                ));
            }
        };
        let value = text.parse::<toml::Value>().map_err(|error| {
            format!("could not parse ancestor manifest {}: {error}", candidate.display())
        })?;
        if value.get("workspace").and_then(toml::Value::as_table).is_some() {
            return Ok(Some(candidate.canonicalize().map_err(|error| {
                format!(
                    "could not canonicalize workspace manifest {}: {error}",
                    candidate.display()
                )
            })?));
        }
    }
    Ok(None)
}

fn manifest_declares_kani_dependency(manifest_dir: &Path) -> Result<bool, String> {
    let manifest_path = manifest_dir.join("Cargo.toml");
    let text = crate::input_limits::read_bounded_utf8_file(
        &manifest_path,
        crate::input_limits::MAX_RELEASE_METADATA_BYTES,
    )
    .map_err(|error| format!("could not read {}: {error}", manifest_path.display()))?;
    let manifest = text
        .parse::<toml::Value>()
        .map_err(|error| format!("could not parse {}: {error}", manifest_path.display()))?;
    let Some(root) = manifest.as_table() else {
        return Err(format!("{} is not a TOML table", manifest_path.display()));
    };

    const DEPENDENCY_SECTIONS: [&str; 3] =
        ["dependencies", "dev-dependencies", "build-dependencies"];
    let mut tables =
        DEPENDENCY_SECTIONS.iter().filter_map(|section| root.get(*section)).collect::<Vec<_>>();

    if let Some(targets) = root.get("target").and_then(toml::Value::as_table) {
        for target in targets.values().filter_map(toml::Value::as_table) {
            tables.extend(DEPENDENCY_SECTIONS.iter().filter_map(|section| target.get(*section)));
        }
    }
    if tables.iter().copied().any(dependency_table_declares_kani) {
        return Ok(true);
    }

    let mut inherited_aliases = BTreeSet::new();
    for table in tables {
        dependency_table_workspace_aliases(table, &mut inherited_aliases);
    }
    if inherited_aliases.is_empty() {
        return Ok(false);
    }
    let workspace_manifest =
        workspace_manifest_for_package(manifest_dir, &manifest)?.ok_or_else(|| {
            format!(
                "{} inherits workspace dependencies {:?}, but no workspace manifest was found",
                manifest_path.display(),
                inherited_aliases
            )
        })?;
    let workspace_text = crate::input_limits::read_bounded_utf8_file(
        &workspace_manifest,
        crate::input_limits::MAX_RELEASE_METADATA_BYTES,
    )
    .map_err(|error| format!("could not read {}: {error}", workspace_manifest.display()))?;
    let workspace = workspace_text
        .parse::<toml::Value>()
        .map_err(|error| format!("could not parse {}: {error}", workspace_manifest.display()))?;
    let workspace_dependencies = workspace
        .get("workspace")
        .and_then(toml::Value::as_table)
        .and_then(|workspace| workspace.get("dependencies"))
        .and_then(toml::Value::as_table)
        .ok_or_else(|| {
            format!(
                "{} has no [workspace.dependencies] table for inherited aliases {:?}",
                workspace_manifest.display(),
                inherited_aliases
            )
        })?;
    Ok(inherited_aliases.into_iter().any(|alias| {
        workspace_dependencies.get(&alias).is_some_and(|dependency| {
            alias == "kani"
                || dependency
                    .as_table()
                    .and_then(|detail| detail.get("package"))
                    .and_then(toml::Value::as_str)
                    == Some("kani")
        })
    }))
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, VecDeque};
    use std::fs;
    use std::process::{Command, Stdio};

    use serde_json::{Value, json};

    use super::*;

    #[test]
    fn kani_dependency_detection_covers_aliases_and_target_sections() {
        for manifest in [
            "[package]\nname='p'\nversion='0.1.0'\n[dev-dependencies]\nkani='1'\n",
            "[package]\nname='p'\nversion='0.1.0'\n[dependencies.mc]\npackage='kani'\nversion='1'\n",
            "[package]\nname='p'\nversion='0.1.0'\n[target.'cfg(unix)'.dependencies]\nkani={ workspace=true }\n",
        ] {
            let temp = tempfile::tempdir().expect("temp package");
            fs::write(temp.path().join("Cargo.toml"), manifest).expect("write manifest");
            assert!(
                manifest_declares_kani_dependency(temp.path()).expect("inspect manifest"),
                "missed Kani declaration in {manifest}"
            );
        }

        let temp = tempfile::tempdir().expect("temp package");
        fs::write(
            temp.path().join("Cargo.toml"),
            "[package]\nname='p'\nversion='0.1.0'\n[dependencies]\nserde='1'\n",
        )
        .expect("write manifest");
        assert!(!manifest_declares_kani_dependency(temp.path()).expect("inspect manifest"));
    }

    #[test]
    fn kani_dependency_detection_resolves_workspace_inherited_aliases() {
        let temp = tempfile::tempdir().expect("workspace fixture");
        let member = temp.path().join("member");
        fs::create_dir_all(&member).expect("member directory");
        fs::write(
            temp.path().join("Cargo.toml"),
            "[workspace]\nmembers=['member']\n[workspace.dependencies]\nmc={ package='kani', version='1' }\n",
        )
        .expect("workspace manifest");
        fs::write(
            member.join("Cargo.toml"),
            "[package]\nname='p'\nversion='0.1.0'\n[target.'cfg(unix)'.dev-dependencies]\nmc={ workspace=true }\n",
        )
        .expect("member manifest");
        assert!(manifest_declares_kani_dependency(&member).expect("resolve inherited alias"));
    }

    #[test]
    fn kani_gate_preserves_a_failed_build_without_resolving_packages() {
        assert_eq!(
            disclose_after_compile(
                super::super::CompileVerb::Build,
                ExitCode::from(9),
                &["-p".to_string(), "missing".to_string()]
            ),
            ExitCode::from(9)
        );
        assert_eq!(
            disclose_after_compile(
                super::super::CompileVerb::Check,
                ExitCode::from(9),
                &["-p".to_string(), "missing".to_string()]
            ),
            ExitCode::from(9)
        );
    }

    /// TRUST-26: each verb names itself and keeps the shared lane statement;
    /// only `build` carries the artifact-binding advice.
    #[test]
    fn kani_dependency_disclosure_names_the_verb_that_ran() {
        let root = Path::new("/pkg");
        let check = kani_dependency_disclosure(super::super::CompileVerb::Check, root);
        let build = kani_dependency_disclosure(super::super::CompileVerb::Build, root);
        for (disclosure, verb) in [(&check, "check"), (&build, "build")] {
            assert!(
                disclosure.starts_with(&format!("targo trust {verb}: warning: /pkg declares")),
                "{disclosure}"
            );
            assert!(disclosure.contains(UNEXAMINED_KANI_SURFACE), "{disclosure}");
        }
        assert!(build.contains("artifact just built"), "{build}");
        assert!(!check.contains("artifact just built"), "{check}");
        assert!(check.contains("not a Kani verdict"), "{check}");
    }

    /// A `kani` dependency DISCLOSES, it does not reject (two-language design
    /// v5, §3.2 MIGRATE: kani is a zero-authority ingestion lane).
    ///
    /// This pins the amended boundary. It is not a weakened proof claim: the
    /// Kani surface is inert in a trustc build — trustc registers no `kanitool`
    /// tool by default, and trust-mc engine code reaches trustc only as an
    /// explicitly selected external `-Zcodegen-backend` that `targo trust` never
    /// inherits. The `premise_*` tests below pin the three checks in the module
    /// docs; if any of them stops holding, it fails on purpose and the gate
    /// should go back to rejecting.
    #[test]
    fn kani_dependency_discloses_rather_than_rejecting_the_build() {
        let temp = tempfile::tempdir().expect("package fixture");
        fs::write(
            temp.path().join("Cargo.toml"),
            "[package]\nname='p'\nversion='0.1.0'\n[dependencies]\nkani='1'\n",
        )
        .expect("write manifest");
        assert!(
            manifest_declares_kani_dependency(temp.path()).expect("inspect manifest"),
            "detection must survive the amendment — the disclosure depends on it"
        );
    }

    // ----------------------------------------------------------------------
    // S9 (T1): doctrine pins for the dylib lane. Kani text carries no proof
    // authority in Trust; trust-mc engine code reaches trustc only as an
    // explicitly selected external `-Zcodegen-backend`; `targo trust
    // check`/`build` never inherit such a backend silently.
    // ----------------------------------------------------------------------

    const TRUST_MC_BACKEND_DYLIB: &str = "/abs/librustc_codegen_trust_mc.dylib";

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(|arg| (*arg).to_string()).collect()
    }

    fn environment(pairs: &[(&str, &str)]) -> Vec<(String, String)> {
        pairs.iter().map(|(key, value)| ((*key).to_string(), (*value).to_string())).collect()
    }

    fn trust_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("targo-trust lives directly under the trust checkout")
            .to_path_buf()
    }

    fn read_source(path: &Path) -> String {
        fs::read_to_string(path)
            .unwrap_or_else(|error| panic!("could not read {}: {error}", path.display()))
    }

    fn rust_sources_under(root: &Path, files: &mut Vec<PathBuf>) {
        let entries = fs::read_dir(root)
            .unwrap_or_else(|error| panic!("could not read {}: {error}", root.display()));
        for entry in entries {
            let entry = entry.expect("directory entry");
            let file_type = entry.file_type().expect("directory entry type");
            let path = entry.path();
            if file_type.is_dir() {
                if !matches!(entry.file_name().to_str(), Some("target" | ".git")) {
                    rust_sources_under(&path, files);
                }
            } else if file_type.is_file() && path.extension().is_some_and(|ext| ext == "rs") {
                files.push(path);
            }
        }
    }

    fn sources_naming(files: &[PathBuf], needle: &str) -> Vec<PathBuf> {
        files
            .iter()
            .filter(|path| {
                String::from_utf8_lossy(&fs::read(path).expect("read Rust source")).contains(needle)
            })
            .cloned()
            .collect()
    }

    /// The `sym::` names in the compiler's shared `PREDEFINED_TOOLS` initializer.
    fn predefined_tool_names(macros_rs: &str) -> Option<Vec<String>> {
        let tokens: Vec<_> = trust_types::obligation_identity::tokens(macros_rs)
            .into_iter()
            .map(|(start, end)| &macros_rs[start..end])
            .collect();
        let mut declarations = tokens
            .windows(2)
            .enumerate()
            .filter_map(|(index, pair)| (pair == ["const", "PREDEFINED_TOOLS"]).then_some(index));
        let start = declarations.next()?;
        if declarations.next().is_some() {
            return None;
        }
        // A declaration inside a function or macro is not the shared compiler constant.
        let mut groups = Vec::new();
        for token in &tokens[..start] {
            match *token {
                "(" => groups.push(")"),
                "[" => groups.push("]"),
                "{" => groups.push("}"),
                ")" | "]" | "}" if groups.pop() != Some(*token) => return None,
                _ => {}
            }
        }
        if !groups.is_empty() {
            return None;
        }
        let mut rest =
            tokens[start + 2..].strip_prefix(&[":", "&", "[", "Symbol", "]", "=", "&", "["])?;
        let mut tools = Vec::new();
        loop {
            if let Some(tail) = rest.strip_prefix(&["]"]) {
                // Trust: a missing tool registry requires a fresh premise audit.
                return (tail.first() == Some(&";") && !tools.is_empty()).then_some(tools);
            }
            let ["sym", ":", ":", name, tail @ ..] = rest else { return None };
            let mut bytes = name.bytes();
            if !bytes.next().is_some_and(|c| c.is_ascii_alphabetic() || c == b'_')
                || !bytes.all(|c| c.is_ascii_alphanumeric() || c == b'_')
            {
                return None;
            }
            tools.push(name.to_string());
            rest = match tail {
                [",", tail @ ..] => tail,
                ["]", ..] => tail,
                _ => return None,
            };
        }
    }

    #[test]
    fn predefined_tool_audit_exposes_a_kani_tool() {
        let tools = predefined_tool_names(
            "const PREDEFINED_TOOLS: &[Symbol] = &[sym::clippy, sym::kanitool];",
        )
        .expect("literal symbol array");
        assert!(tools.iter().any(|tool| tool.contains("kani")));
    }

    #[test]
    fn predefined_tool_audit_reads_the_initializer_not_its_slice_type() {
        assert_eq!(
            predefined_tool_names(
                "const PREDEFINED_TOOLS: &[Symbol] =\n &[sym::clippy, sym::trust,];"
            ),
            Some(vec!["clippy".to_string(), "trust".to_string()])
        );
    }

    #[test]
    fn predefined_tool_audit_refuses_unknown_or_incomplete_source() {
        for source in [
            "let predefined_tools = [sym::clippy];",
            "const PREDEFINED_TOOLS: &[Symbol] = computed_tools();",
            "const PREDEFINED_TOOLS: &[Symbol] = &[sym::clippy].chain(other_tools);",
            "const PREDEFINED_TOOLS: &[Symbol] = &[sym::clippy, computed_tool()];",
            "const PREDEFINED_TOOLS: &[Symbol] = &[sym::clippy]",
            "const PREDEFINED_TOOLS: &[Symbol] = &[];",
            "const PREDEFINED_TOOLS: &[Symbol] = &[sym::clippy,,];",
            "const PREDEFINED_TOOLS: &[Symbol] = &[sym::clippy];\n\
             const PREDEFINED_TOOLS: &[Symbol] = &[sym::kanitool];",
        ] {
            assert_eq!(predefined_tool_names(source), None, "audit must refuse {source}");
        }
    }

    #[test]
    fn predefined_tool_names_reads_typed_const_initializer_without_decoys() {
        let source = r#"
const BEFORE: &[Symbol] = &[sym::kanitool];
const PREDEFINED_TOOLS: &[Symbol] = &[
    sym::clippy,
    sym::trust,
];
const AFTER: &[Symbol] = &[sym::kani];
"#;
        assert_eq!(
            predefined_tool_names(source),
            Some(vec!["clippy".to_string(), "trust".to_string()])
        );
    }

    #[test]
    fn predefined_tool_names_does_not_hide_kani_behind_comments_or_literals() {
        for decoy in [
            "// const PREDEFINED_TOOLS: &[Symbol] = &[sym::clippy];",
            "/* outer /* nested */ const PREDEFINED_TOOLS: &[Symbol] = &[sym::clippy]; */",
            r#"const TEXT: &str = "const PREDEFINED_TOOLS: &[Symbol] = &[sym::clippy];";"#,
            r##"const TEXT: &str = r#"const PREDEFINED_TOOLS: &[Symbol] = &[sym::clippy];"#;"##,
            r###"const TEXT: &[u8] = br##"const PREDEFINED_TOOLS: &[Symbol] = &[sym::clippy];"##;"###,
        ] {
            assert!(predefined_tool_names(decoy).is_none(), "accepted decoy: {decoy}");
            let source = format!("{decoy}\nconst PREDEFINED_TOOLS: &[Symbol] = &[sym::kani];");
            assert_eq!(predefined_tool_names(&source), Some(vec!["kani".to_string()]));
        }
        let source = r#"const QUOTE: char = '"';
const PREDEFINED_TOOLS: &[Symbol] = &[sym::clippy, sym::kanitool];"#;
        let tools = predefined_tool_names(source).expect("parse the actual initializer");
        assert!(tools.iter().any(|tool| tool.contains("kani")));
    }

    #[test]
    fn predefined_tool_names_refuses_unexpected_or_ambiguous_initializers() {
        for source in [
            "let predefined_tools = [sym::clippy];",
            "const PREDEFINED_TOOLS: &[Symbol]; const DECOY: &[Symbol] = &[sym::clippy];",
            "const PREDEFINED_TOOLS: &[Symbol] = build_tools();",
            "const PREDEFINED_TOOLS: &[Symbol] = &[sym::clippy, alias];",
            "const PREDEFINED_TOOLS: &[Symbol] = &[sym::clippy]",
            "const PREDEFINED_TOOLS: &[Symbol] = &[];",
            "const PREDEFINED_TOOLS: &[Symbol] = &[sym::clippy] + &[sym::kani];",
            "const PREDEFINED_TOOLS: &[Symbol] = &[sym::clippy]; \
             const PREDEFINED_TOOLS: &[Symbol] = &[sym::kani];",
            "fn decoy() { const PREDEFINED_TOOLS: &[Symbol] = &[sym::clippy]; }",
            "macro_rules! decoy { () => { const PREDEFINED_TOOLS: &[Symbol] = &[sym::clippy]; } }",
        ] {
            assert!(predefined_tool_names(source).is_none(), "accepted {source}");
        }
    }

    /// Premise 1: trustc registers no `kanitool` tool by default, so a
    /// `#[kanitool::…]` path resolves only in a crate that opts in with
    /// `register_tool(kanitool)`. The dynamic half (`trustc --cfg=kani` on a
    /// `#[kanitool::proof]` file without `register_tool` gives E0433) is a UI
    /// test that needs a stage build; this pins the source it follows from.
    #[test]
    fn premise_one_trustc_registers_no_kanitool_tool_by_default() {
        let path = trust_root().join("compiler/rustc_resolve/src/macros.rs");
        let source = read_source(&path);
        let tools = predefined_tool_names(&source).unwrap_or_else(|| {
            panic!(
                "`const PREDEFINED_TOOLS: &[Symbol] = &[...]` changed in {}; re-derive premise 1",
                path.display()
            )
        });
        // Rust 1.101 split attribute and lint tools; both registration paths
        // must still extend the exact shared array audited above.
        for function in ["registered_attr_tools", "registered_lint_tools_ast"] {
            let (_, body) = source
                .split_once(&format!("fn {function}("))
                .unwrap_or_else(|| panic!("{function} moved; re-derive premise 1"));
            let (body, _) = body
                .split_once("\n}")
                .unwrap_or_else(|| panic!("{function} changed shape; re-derive premise 1"));
            assert!(
                body.contains(
                    "registered_tools.extend(PREDEFINED_TOOLS.iter().cloned().map(Ident::with_dummy_span));"
                ),
                "{function} no longer registers the audited PREDEFINED_TOOLS; re-derive premise 1"
            );
        }
        assert!(
            tools.iter().any(|tool| tool == "clippy"),
            "parsed the wrong array in {}: {tools:?}",
            path.display()
        );
        assert!(
            !tools.iter().any(|tool| tool.contains("kani")),
            "trustc predefines a Kani tool, so `#[kanitool::…]` no longer needs an explicit \
             register_tool: {tools:?}"
        );
    }

    /// Premise 1, second half: nothing in rustc proper names `kanitool`, so even
    /// a registered Kani tool attribute is inert to trustc.
    #[test]
    fn premise_one_no_compiler_source_names_kanitool() {
        let compiler = trust_root().join("compiler");
        let mut files = Vec::new();
        rust_sources_under(&compiler, &mut files);
        assert!(
            files.len() > 1000,
            "expected the rustc source tree under {}, found {} .rs files",
            compiler.display(),
            files.len()
        );
        let hits = sources_naming(&files, "kanitool");
        assert!(hits.is_empty(), "compiler source names `kanitool`; re-derive premise 1: {hits:?}");
    }

    const TRUSTC_DRIVER_ROOTS: [&str; 2] = ["rustc_driver", "rustc_driver_impl"];
    const TRUST_MC_ENGINE_PACKAGES: [&str; 2] = ["trust-mc-engine", "trust-mc-backend"];
    const TRUST_MC_FACADE_PACKAGE: &str = "trust-mc-compiler";

    #[derive(Debug, Default)]
    struct EngineGraphAudit {
        reachable: BTreeSet<String>,
        violations: Vec<String>,
    }

    /// Whether enabling `feature` (transitively) enables the trust-mc engine
    /// dependency. A weak `trust-mc-engine?/…` entry does not.
    fn feature_enables_engine(
        declared: &serde_json::Map<String, Value>,
        feature: &str,
        seen: &mut BTreeSet<String>,
    ) -> bool {
        if !seen.insert(feature.to_string()) {
            return false;
        }
        declared
            .get(feature)
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .any(|entry| {
                entry == "dep:trust-mc-engine"
                    || entry == "trust-mc-engine"
                    || entry.starts_with("trust-mc-engine/")
                    || feature_enables_engine(declared, entry, seen)
            })
    }

    /// Walk every non-dev edge from `rustc_driver` / `rustc_driver_impl` in a
    /// `cargo metadata` resolve graph and report each path to trust-mc engine
    /// code: the `trust-mc-engine` rlib, the `trust-mc-backend` cdylib, or
    /// `trust-mc-compiler` built with a feature that enables the engine (its
    /// binary target requires `driver`). `trust-mc-compiler`'s rustc-free
    /// library facade is admitted; a `trust-mc-compiler` with no feature gating
    /// the engine predates the split, so its library is the engine.
    fn audit_trust_mc_engine_reachability(metadata: &Value) -> Result<EngineGraphAudit, String> {
        let packages = metadata["packages"].as_array().ok_or("cargo metadata has no `packages`")?;
        let package_by_id = packages
            .iter()
            .filter_map(|package| Some((package["id"].as_str()?, package)))
            .collect::<BTreeMap<_, _>>();
        let nodes = metadata["resolve"]["nodes"]
            .as_array()
            .ok_or("cargo metadata has no resolve graph; was --no-deps passed?")?;
        let node_by_id = nodes
            .iter()
            .filter_map(|node| Some((node["id"].as_str()?, node)))
            .collect::<BTreeMap<_, _>>();
        let name_of = |id: &str| {
            package_by_id
                .get(id)
                .and_then(|package| package["name"].as_str())
                .unwrap_or(id)
                .to_string()
        };

        let mut routes = BTreeMap::<&str, Vec<String>>::new();
        let mut queue = VecDeque::new();
        for (id, package) in &package_by_id {
            if TRUSTC_DRIVER_ROOTS.contains(&package["name"].as_str().unwrap_or_default()) {
                routes.insert(*id, vec![name_of(id)]);
                queue.push_back(*id);
            }
        }
        if queue.is_empty() {
            return Err(format!(
                "no {TRUSTC_DRIVER_ROOTS:?} package in the metadata; this is not the trust \
                 compiler workspace"
            ));
        }
        while let Some(id) = queue.pop_front() {
            let node =
                node_by_id.get(id).ok_or_else(|| format!("resolve graph has no node for {id}"))?;
            for dependency in node["deps"].as_array().into_iter().flatten() {
                let kinds =
                    dependency["dep_kinds"].as_array().map(Vec::as_slice).unwrap_or_default();
                // A dev-dependency is never linked into the dependent's library.
                if !kinds.is_empty()
                    && kinds.iter().all(|kind| kind["kind"].as_str() == Some("dev"))
                {
                    continue;
                }
                let dependency_id = dependency["pkg"]
                    .as_str()
                    .ok_or_else(|| format!("a dependency of {id} has no package id"))?;
                if routes.contains_key(dependency_id) {
                    continue;
                }
                let mut route = routes[id].clone();
                route.push(name_of(dependency_id));
                routes.insert(dependency_id, route);
                queue.push_back(dependency_id);
            }
        }

        let no_features = serde_json::Map::new();
        let mut audit = EngineGraphAudit::default();
        for (id, route) in &routes {
            let name = name_of(id);
            let route = route.join(" -> ");
            audit.reachable.insert(name.clone());
            if TRUST_MC_ENGINE_PACKAGES.contains(&name.as_str()) {
                audit.violations.push(format!("{route}: `{name}` is trust-mc engine code"));
                continue;
            }
            if name != TRUST_MC_FACADE_PACKAGE {
                continue;
            }
            let declared = package_by_id
                .get(*id)
                .and_then(|package| package["features"].as_object())
                .unwrap_or(&no_features);
            if !declared
                .keys()
                .any(|feature| feature_enables_engine(declared, feature, &mut BTreeSet::new()))
            {
                audit.violations.push(format!(
                    "{route}: `{name}` has no feature gating trust-mc-engine, so its library is \
                     the engine itself (pre-split layout)"
                ));
                continue;
            }
            let engine_features = node_by_id
                .get(*id)
                .and_then(|node| node["features"].as_array())
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .filter(|feature| feature_enables_engine(declared, feature, &mut BTreeSet::new()))
                .collect::<Vec<_>>();
            if !engine_features.is_empty() {
                audit.violations.push(format!(
                    "{route}: `{name}` is resolved with engine feature(s) {engine_features:?}; \
                     only its rustc-free facade (default-features = false, no `driver`) may be \
                     linked"
                ));
            }
        }
        Ok(audit)
    }

    fn facade_features() -> Value {
        json!({
            "default": ["ay", "driver"],
            "ay": ["trust-mc-core", "trust-mc-engine?/ay"],
            "driver": ["dep:trust-mc-engine"],
            "compiler-corpus-tests": ["trust-mc-engine?/compiler-corpus-tests"],
        })
    }

    fn metadata_fixture(
        packages: &[(&str, Value)],
        edges: &[(&str, &str, Option<&str>)],
        resolved: &[(&str, &[&str])],
    ) -> Value {
        let nodes = packages
            .iter()
            .map(|(name, _)| {
                let deps = edges
                    .iter()
                    .filter(|(from, _, _)| from == name)
                    .map(|(_, to, kind)| {
                        json!({
                            "name": to.replace('-', "_"),
                            "pkg": to,
                            "dep_kinds": [{ "kind": kind, "target": null }],
                        })
                    })
                    .collect::<Vec<_>>();
                let features = resolved
                    .iter()
                    .find(|(package, _)| package == name)
                    .map(|(_, features)| features.to_vec())
                    .unwrap_or_default();
                json!({ "id": name, "deps": deps, "features": features })
            })
            .collect::<Vec<_>>();
        let packages = packages
            .iter()
            .map(|(name, features)| json!({ "id": name, "name": name, "features": features }))
            .collect::<Vec<_>>();
        json!({ "packages": packages, "resolve": { "nodes": nodes, "root": null } })
    }

    fn driver_graph_packages(extra: &[(&'static str, Value)]) -> Vec<(&'static str, Value)> {
        let mut packages = vec![
            ("rustc_driver", json!({})),
            ("rustc_driver_impl", json!({})),
            ("rustc_interface", json!({})),
            ("trust-bmc", json!({})),
        ];
        packages.extend(extra.iter().cloned());
        packages
    }

    const DRIVER_TO_BMC: [(&str, &str, Option<&str>); 3] = [
        ("rustc_driver", "rustc_driver_impl", None),
        ("rustc_driver_impl", "rustc_interface", None),
        ("rustc_interface", "trust-bmc", None),
    ];

    #[test]
    fn engine_graph_audit_admits_the_rustc_free_facade() {
        let packages = driver_graph_packages(&[
            ("trust-mc-compiler", facade_features()),
            ("trust-mc-core", json!({})),
        ]);
        let mut edges = DRIVER_TO_BMC.to_vec();
        edges.push(("trust-bmc", "trust-mc-compiler", None));
        edges.push(("trust-mc-compiler", "trust-mc-core", None));
        let audit = audit_trust_mc_engine_reachability(&metadata_fixture(
            &packages,
            &edges,
            &[("trust-mc-compiler", &["ay"])],
        ))
        .expect("audit fixture graph");
        assert!(audit.violations.is_empty(), "{:?}", audit.violations);
        assert!(audit.reachable.contains("trust-mc-compiler"), "{:?}", audit.reachable);
    }

    #[test]
    fn engine_graph_audit_rejects_engine_features_on_the_facade() {
        for resolved in [&["default", "ay", "driver"][..], &["driver"][..], &["default"][..]] {
            let packages = driver_graph_packages(&[
                ("trust-mc-compiler", facade_features()),
                ("trust-mc-engine", json!({})),
            ]);
            let mut edges = DRIVER_TO_BMC.to_vec();
            edges.push(("trust-bmc", "trust-mc-compiler", None));
            edges.push(("trust-mc-compiler", "trust-mc-engine", None));
            let audit = audit_trust_mc_engine_reachability(&metadata_fixture(
                &packages,
                &edges,
                &[("trust-mc-compiler", resolved)],
            ))
            .expect("audit fixture graph");
            assert!(
                audit.violations.iter().any(|violation| violation.contains("engine feature")),
                "facade features {resolved:?} were admitted: {:?}",
                audit.violations
            );
            assert!(
                audit.violations.iter().any(
                    |violation| violation.contains("`trust-mc-engine` is trust-mc engine code")
                ),
                "{:?}",
                audit.violations
            );
        }
    }

    #[test]
    fn engine_graph_audit_rejects_engine_and_backend_packages() {
        let packages = driver_graph_packages(&[
            ("trust-mc-engine", json!({})),
            ("trust-mc-backend", json!({})),
        ]);
        let mut edges = DRIVER_TO_BMC.to_vec();
        edges.push(("rustc_driver_impl", "trust-mc-engine", None));
        edges.push(("trust-bmc", "trust-mc-backend", Some("build")));
        let audit = audit_trust_mc_engine_reachability(&metadata_fixture(&packages, &edges, &[]))
            .expect("audit fixture graph");
        assert_eq!(audit.violations.len(), 2, "{:?}", audit.violations);
        assert!(
            audit.violations.iter().any(|violation| violation.starts_with(
                "rustc_driver_impl -> rustc_interface -> trust-bmc -> trust-mc-backend:"
            )),
            "{:?}",
            audit.violations
        );
    }

    #[test]
    fn engine_graph_audit_rejects_a_pre_split_trust_mc_compiler() {
        let packages = driver_graph_packages(&[(
            "trust-mc-compiler",
            json!({ "default": ["ay"], "ay": ["ay_bindings", "trust-mc-core"] }),
        )]);
        let mut edges = DRIVER_TO_BMC.to_vec();
        edges.push(("trust-bmc", "trust-mc-compiler", None));
        let audit = audit_trust_mc_engine_reachability(&metadata_fixture(&packages, &edges, &[]))
            .expect("audit fixture graph");
        assert!(
            audit.violations.iter().any(|violation| violation.contains("pre-split")),
            "{:?}",
            audit.violations
        );
    }

    #[test]
    fn engine_graph_audit_ignores_dev_edges_and_fails_closed_without_driver_roots() {
        let packages = driver_graph_packages(&[("trust-mc-engine", json!({}))]);
        let mut edges = DRIVER_TO_BMC.to_vec();
        edges.push(("rustc_interface", "trust-mc-engine", Some("dev")));
        let audit = audit_trust_mc_engine_reachability(&metadata_fixture(&packages, &edges, &[]))
            .expect("audit fixture graph");
        assert!(audit.violations.is_empty(), "{:?}", audit.violations);
        assert!(!audit.reachable.contains("trust-mc-engine"));

        let rootless = metadata_fixture(&[("trust-mc-engine", json!({}))], &[], &[]);
        assert!(audit_trust_mc_engine_reachability(&rootless).is_err());
    }

    /// Premise 2, live: over the trust compiler workspace's own resolved graph
    /// (`targo metadata`, no build), librustc_driver reaches no trust-mc engine
    /// code. crates/trust-bmc may still reach trust-mc-driver and trust-mc-core,
    /// and may reach trust-mc-compiler's rustc-free facade.
    #[test]
    fn premise_two_trustc_driver_graph_reaches_no_trust_mc_engine() {
        let root = trust_root();
        // `$CARGO` is targo under `targo --unverified test`; outside targo, the
        // Trust tool by name (`metadata` takes no lane), never a bare `cargo`.
        let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "targo".into());
        let output = Command::new(&cargo)
            .args(["metadata", "--format-version", "1", "--locked", "--manifest-path"])
            .arg(root.join("Cargo.toml"))
            .current_dir(&root)
            .stdin(Stdio::null())
            .output()
            .unwrap_or_else(|error| panic!("could not run {cargo:?} metadata: {error}"));
        assert!(
            output.status.success(),
            "`{} metadata` over {} failed ({}):\n{}",
            Path::new(&cargo).display(),
            root.display(),
            output.status,
            String::from_utf8_lossy(&output.stderr)
        );
        let metadata: Value =
            serde_json::from_slice(&output.stdout).expect("cargo metadata emits JSON");
        let audit =
            audit_trust_mc_engine_reachability(&metadata).unwrap_or_else(|error| panic!("{error}"));
        assert!(
            audit.reachable.contains("rustc_interface"),
            "the audit did not walk the compiler graph: {:?}",
            audit.reachable
        );
        assert!(
            audit.violations.is_empty(),
            "librustc_driver reaches trust-mc engine code:\n{}",
            audit.violations.join("\n")
        );
    }

    /// Premise 3: `ProofObligationSource::KaniProofAttribute` is referenced only
    /// by trust-mc-driver's harness listing surface, never by a verdict path.
    #[test]
    fn premise_three_kani_proof_attribute_is_referenced_only_by_the_listing_surface() {
        let trust_mc = trust_root().join("first-party/trust-mc");
        let listing = trust_mc.join("trust-mc-driver/src/list");
        assert!(
            listing.is_dir(),
            "{} is missing; initialise the first-party/trust-mc submodule",
            listing.display()
        );
        let mut files = Vec::new();
        rust_sources_under(&trust_mc, &mut files);
        let referencing = sources_naming(&files, "KaniProofAttribute");
        assert!(
            !referencing.is_empty(),
            "no KaniProofAttribute reference found; re-derive premise 3"
        );
        let outside =
            referencing.iter().filter(|path| !path.starts_with(&listing)).collect::<Vec<_>>();
        assert!(outside.is_empty(), "KaniProofAttribute escaped the listing surface: {outside:?}");
    }

    #[test]
    fn trustc_builtin_codegen_backends_match_the_linked_backend_table() {
        let path = trust_root().join("compiler/rustc_interface/src/util.rs");
        let source = read_source(&path);
        let start = source
            .find("fn builtin_codegen_backend(")
            .unwrap_or_else(|| panic!("builtin_codegen_backend moved out of {}", path.display()));
        let body = &source[start..];
        let body = &body[..body.find("\n}\n").expect("end of builtin_codegen_backend")];
        let linked = body
            .lines()
            .map(str::trim)
            .filter(|line| !line.starts_with("//"))
            .filter_map(|line| line.split_once("=>"))
            .flat_map(|(patterns, _)| patterns.split('|'))
            .filter_map(|pattern| pattern.trim().strip_prefix('"')?.strip_suffix('"'))
            .map(str::to_string)
            .collect::<BTreeSet<_>>();
        let pinned = TRUSTC_BUILTIN_CODEGEN_BACKENDS
            .iter()
            .map(|name| (*name).to_string())
            .collect::<BTreeSet<_>>();
        assert!(
            linked.contains("llvm"),
            "parsed the wrong function in {}: {linked:?}",
            path.display()
        );
        assert_eq!(
            pinned, linked,
            "the builtin backend list drifted from trustc; every other name loads an external dylib"
        );
    }

    #[test]
    fn kani_surface_flags_cover_external_backends_and_kanitool_registration() {
        let compact = format!("-Zcodegen-backend={TRUST_MC_BACKEND_DYLIB}");
        let split = format!("codegen-backend={TRUST_MC_BACKEND_DYLIB}");
        let args = vec![
            compact.clone(),
            "-Z".to_string(),
            split.clone(),
            "-Zcodegen_backend=trust_mc".to_string(),
            "--cfg=kani".to_string(),
            "-Zcrate-attr=feature(register_tool)".to_string(),
            "-Zcrate-attr=register_tool(kanitool)".to_string(),
            "-Z".to_string(),
            "crate_attr=register_tool(other, kanitool)".to_string(),
            "-Copt-level=2".to_string(),
        ];
        assert_eq!(
            kani_surface_flags(&args),
            vec![
                compact,
                format!("-Z {split}"),
                "-Zcodegen_backend=trust_mc".to_string(),
                "-Zcrate-attr=register_tool(kanitool)".to_string(),
                "-Z crate_attr=register_tool(other, kanitool)".to_string(),
            ]
        );
        for builtin in ["dummy", "llvm", "trust-cg", "trust_cg"] {
            assert!(
                kani_surface_flags(&[format!("-Zcodegen-backend={builtin}")]).is_empty(),
                "builtin backend {builtin} is not an external surface"
            );
        }
        assert!(
            kani_surface_flags(&strings(&[
                "--cfg",
                "kani",
                "-Zcrate-attr=feature(register_tool)",
                "-Zcrate-attr=register_tool(tippy)",
                "-C",
                "metadata=register_tool(kanitool)",
            ]))
            .is_empty()
        );
    }

    #[test]
    fn unexamined_kani_surface_disclosure_names_every_inherited_rustflags_channel() {
        let temp = tempfile::tempdir().expect("disclosure fixture");
        let project = temp.path().join("harness");
        fs::create_dir_all(project.join(".cargo")).expect("project config dir");
        let project_config = project.join(".cargo").join("config.toml");
        fs::write(
            &project_config,
            format!(
                "[build]\nrustflags = [\"-Zcodegen-backend={TRUST_MC_BACKEND_DYLIB}\", \"--cfg=kani\"]\n\n\
                 [target.'cfg(all())']\nrustflags = \"-Zcrate-attr=feature(register_tool) -Zcrate-attr=register_tool(kanitool)\"\n\n\
                 [host]\nrustflags = [\"-Zcrate-attr=register_tool(kanitool)\"]\n\n\
                 [host.aarch64-apple-darwin]\nrustflags = [\"-Zcodegen-backend={TRUST_MC_BACKEND_DYLIB}\"]\n"
            ),
        )
        .expect("project config");
        let cargo_home = temp.path().join("cargo-home");
        fs::create_dir_all(&cargo_home).expect("cargo home");
        let home_config = cargo_home.join("config.toml");
        fs::write(
            &home_config,
            "[target.aarch64-apple-darwin]\nrustflags = [\"-Zcodegen-backend=trust_mc\"]\n",
        )
        .expect("home config");
        let config_file = temp.path().join("extra-config.toml");
        fs::write(&config_file, "[build]\nrustflags = [\"-Zcodegen-backend=trust-mc\"]\n")
            .expect("--config file");

        let plain = format!("-Zcodegen-backend={TRUST_MC_BACKEND_DYLIB} --cfg=kani");
        let encoded = format!("-Z\x1fcodegen-backend={TRUST_MC_BACKEND_DYLIB}");
        let inherited = environment(&[
            ("RUSTFLAGS", plain.as_str()),
            ("CARGO_ENCODED_RUSTFLAGS", encoded.as_str()),
            ("CARGO_BUILD_RUSTFLAGS", "-Zcrate-attr=register_tool(kanitool)"),
            ("CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS", "-Zcodegen-backend=trust-mc"),
            ("CARGO_HOST_RUSTFLAGS", "-Zcodegen-backend=trust_mc"),
            ("CARGO_HOST_AARCH64_APPLE_DARWIN_RUSTFLAGS", "-Zcrate-attr=register_tool(kanitool)"),
            ("PATH", "/usr/bin:/bin"),
        ]);
        let cargo_args = vec![
            "check".to_string(),
            "--config".to_string(),
            "build.rustflags=['-Zcodegen-backend=trust_mc']".to_string(),
            "--config=host.rustflags=['-Zcodegen-backend=trust-mc']".to_string(),
            format!("--config={}", config_file.display()),
            "--".to_string(),
            "--config".to_string(),
            "build.rustflags=['-Zcodegen-backend=after-separator']".to_string(),
        ];

        let sources =
            inherited_rustflags_sources(Some(&project), Some(&cargo_home), &cargo_args, &inherited);
        let disclosure = unexamined_kani_surface_disclosure(&sources)
            .expect("an inherited Kani surface must be disclosed");
        assert!(disclosure.contains(UNEXAMINED_KANI_SURFACE_TAG), "{disclosure}");
        assert!(disclosure.contains("NOT examined"), "{disclosure}");
        assert!(disclosure.contains("NO proof authority"), "{disclosure}");
        for origin in [
            "`RUSTFLAGS`".to_string(),
            "`CARGO_ENCODED_RUSTFLAGS`".to_string(),
            "`CARGO_BUILD_RUSTFLAGS`".to_string(),
            "`CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS`".to_string(),
            "`CARGO_HOST_RUSTFLAGS`".to_string(),
            "`CARGO_HOST_AARCH64_APPLE_DARWIN_RUSTFLAGS`".to_string(),
            "`--config build.rustflags`".to_string(),
            "`--config host.rustflags`".to_string(),
            format!("`{} host.rustflags`", project_config.display()),
            format!("`{} host.aarch64-apple-darwin.rustflags`", project_config.display()),
            format!("`{} build.rustflags`", project_config.display()),
            format!("`{} target.cfg(all()).rustflags`", project_config.display()),
            format!("`{} target.aarch64-apple-darwin.rustflags`", home_config.display()),
            format!("`{} build.rustflags`", config_file.display()),
        ] {
            assert!(
                disclosure.contains(&origin),
                "disclosure does not name {origin}: {disclosure}"
            );
        }
        assert!(
            !disclosure.contains("after-separator"),
            "arguments after `--` are not Cargo configuration: {disclosure}"
        );
    }

    #[test]
    fn unexamined_kani_surface_disclosure_is_silent_without_a_kani_surface() {
        let temp = tempfile::tempdir().expect("disclosure fixture");
        let project = temp.path().join("plain");
        fs::create_dir_all(project.join(".cargo")).expect("project config dir");
        fs::write(
            project.join(".cargo").join("config.toml"),
            "[build]\nrustflags = [\"-Zcodegen-backend=trust-cg\", \"--cfg=kani\"]\n",
        )
        .expect("project config");
        let inherited = environment(&[
            ("RUSTFLAGS", "-C opt-level=2 --cfg=kani -Zcodegen-backend=llvm"),
            ("CARGO_ENCODED_RUSTFLAGS", "-Z\x1fcodegen-backend=trust_cg"),
        ]);
        let sources = inherited_rustflags_sources(Some(&project), None, &[], &inherited);
        assert_eq!(sources.len(), 3, "every channel must still be read: {sources:?}");
        assert_eq!(unexamined_kani_surface_disclosure(&sources), None);
    }

    #[test]
    fn host_rustflags_external_code_refuses_the_run_in_every_host_channel() {
        let temp = tempfile::tempdir().expect("host refusal fixture");
        let project = temp.path().join("harness");
        fs::create_dir_all(project.join(".cargo")).expect("project config dir");
        let project_config = project.join(".cargo").join("config.toml");
        fs::write(
            &project_config,
            format!(
                "[unstable]\nhost-config = true\ntarget-applies-to-host = true\n\n\
                 [host.aarch64-apple-darwin]\nrustflags = [\"-Z\", \"codegen_backend={TRUST_MC_BACKEND_DYLIB}\"]\n"
            ),
        )
        .expect("project config");
        let target_backend = format!("-Zcodegen-backend={TRUST_MC_BACKEND_DYLIB}");
        let inherited = environment(&[
            ("CARGO_HOST_RUSTFLAGS", "-Zllvm-plugins=/abs/libforge.dylib"),
            // Stripped by the verified merge and silenced in selection probes:
            // disclosed, never refused.
            ("RUSTFLAGS", target_backend.as_str()),
        ]);
        let cargo_args =
            strings(&["check", "--config", "host.rustflags=['-Zcodegen-backend=trust-mc']"]);

        let sources = inherited_rustflags_sources(Some(&project), None, &cargo_args, &inherited);
        let refusal = host_rustflags_external_code_refusal(&sources)
            .expect("external code in [host] rustflags must refuse the run");
        assert!(refusal.starts_with(HOST_RUSTFLAGS_EXTERNAL_CODE_TAG), "{refusal}");
        assert!(
            refusal.contains("even when -Zhost-config is off"),
            "an inert [host] table is refused too, and the text must say so: {refusal}"
        );
        for finding in [
            "`CARGO_HOST_RUSTFLAGS` carries -Zllvm-plugins=/abs/libforge.dylib".to_string(),
            "`--config host.rustflags` carries -Zcodegen-backend=trust-mc".to_string(),
            format!(
                "`{} host.aarch64-apple-darwin.rustflags` carries -Z codegen_backend={TRUST_MC_BACKEND_DYLIB}",
                project_config.display()
            ),
        ] {
            assert!(refusal.contains(&finding), "refusal does not name {finding}: {refusal}");
        }
        assert!(!refusal.contains("`RUSTFLAGS`"), "target-side flags are stripped: {refusal}");
    }

    #[test]
    fn host_rustflags_refusal_admits_builtin_backends_and_inert_kanitool_registration() {
        let temp = tempfile::tempdir().expect("host refusal fixture");
        let project = temp.path().join("plain");
        fs::create_dir_all(project.join(".cargo")).expect("project config dir");
        fs::write(
            project.join(".cargo").join("config.toml"),
            "[host]\nrustflags = [\"-Zcodegen-backend=llvm\", \"-Zcrate-attr=register_tool(kanitool)\"]\n\n\
             [host.aarch64-apple-darwin]\nrustflags = \"-Z codegen-backend=trust_cg --cfg=kani\"\n",
        )
        .expect("project config");
        let target_backend = format!("-Zcodegen-backend={TRUST_MC_BACKEND_DYLIB}");
        let inherited = environment(&[
            ("RUSTFLAGS", target_backend.as_str()),
            ("CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS", target_backend.as_str()),
            ("CARGO_HOST_RUSTFLAGS", "-Zllvm-plugins="),
        ]);
        let cargo_args = strings(&["--config", "build.rustflags=['-Zcodegen-backend=trust_mc']"]);

        let sources = inherited_rustflags_sources(Some(&project), None, &cargo_args, &inherited);
        assert_eq!(
            sources.iter().filter(|source| source.host_artifacts).count(),
            3,
            "every [host] channel must be read: {sources:?}"
        );
        assert_eq!(host_rustflags_external_code_refusal(&sources), None);
        let disclosure = unexamined_kani_surface_disclosure(&sources)
            .expect("the target-side backend and [host] kanitool registration are disclosed");
        assert!(
            disclosure.contains("host.rustflags` carries -Zcrate-attr=register_tool(kanitool)"),
            "{disclosure}"
        );
        assert!(!disclosure.contains("llvm-plugins"), "{disclosure}");
    }
    /// Cargo's `include` key (stable since 1.93) pulls whole config tables in
    /// from other files: relative to the including file's directory, to the
    /// working directory for an inline `--config`, and recursively. A `[host]`
    /// backend in an included file walked around the refusal (S9 re-review,
    /// measured on targo 45dc60873), so every table in an include chain is a
    /// rustflags source exactly like the file that includes it.
    #[test]
    fn inherited_rustflags_sources_follow_cargo_config_include_chains() {
        let temp = tempfile::tempdir().expect("include fixture");
        let project = temp.path().join("harness");
        let cargo_dir = project.join(".cargo");
        fs::create_dir_all(cargo_dir.join("nested")).expect("nested config dir");
        fs::create_dir_all(project.join("shared")).expect("shared config dir");
        let project_config = cargo_dir.join("config.toml");
        fs::write(
            &project_config,
            "include = [\"nested/host.toml\", { path = \"absent.toml\", optional = true }]\n\n\
             [build]\nrustflags = [\"--cfg=kani\"]\n",
        )
        .expect("project config");
        let nested = cargo_dir.join("nested").join("host.toml");
        fs::write(
            &nested,
            format!(
                "include = [{{ path = \"../../shared/build.toml\" }}]\n\n\
                 [host.aarch64-apple-darwin]\nrustflags = [\"-Zcodegen-backend={TRUST_MC_BACKEND_DYLIB}\"]\n"
            ),
        )
        .expect("included host config");
        let shared = project.join("shared").join("build.toml");
        fs::write(
            &shared,
            "[build]\nrustflags = [\"-Zcodegen-backend=trust_mc\"]\n\n\
             [target.'cfg(all())']\nrustflags = [\"-Zcrate-attr=register_tool(kanitool)\"]\n",
        )
        .expect("transitively included build config");
        let inline_include = project.join("cli-host.toml");
        fs::write(
            &inline_include,
            "[host]\nrustflags = [\"-Zllvm-plugins=/abs/libforge.dylib\"]\n",
        )
        .expect("inline --config include");
        let cli_dir = temp.path().join("cli");
        fs::create_dir_all(&cli_dir).expect("--config file dir");
        let cli_file = cli_dir.join("extra.toml");
        fs::write(&cli_file, "include = [\"sibling.toml\"]\n").expect("--config file");
        let cli_sibling = cli_dir.join("sibling.toml");
        fs::write(&cli_sibling, "[host]\nrustflags = [\"-Z\", \"codegen-backend=trust-mc\"]\n")
            .expect("--config file include");
        let cargo_args = vec![
            "check".to_string(),
            "--config".to_string(),
            "include=['cli-host.toml']".to_string(),
            format!("--config={}", cli_file.display()),
        ];

        let sources = inherited_rustflags_sources(Some(&project), None, &cargo_args, &[]);
        let refusal = host_rustflags_external_code_refusal(&sources)
            .expect("a [host] backend in an included config must refuse the run");
        for finding in [
            format!(
                "`{} host.aarch64-apple-darwin.rustflags` carries -Zcodegen-backend={TRUST_MC_BACKEND_DYLIB}",
                nested.display()
            ),
            format!(
                "`{} host.rustflags` carries -Zllvm-plugins=/abs/libforge.dylib",
                inline_include.display()
            ),
            format!(
                "`{} host.rustflags` carries -Z codegen-backend=trust-mc",
                cli_sibling.display()
            ),
        ] {
            assert!(refusal.contains(&finding), "refusal does not name {finding}: {refusal}");
        }
        let disclosure = unexamined_kani_surface_disclosure(&sources)
            .expect("an included target-side Kani surface must be disclosed");
        for finding in [
            format!("`{} build.rustflags` carries -Zcodegen-backend=trust_mc", shared.display()),
            format!(
                "`{} target.cfg(all()).rustflags` carries -Zcrate-attr=register_tool(kanitool)",
                shared.display()
            ),
        ] {
            assert!(
                disclosure.contains(&finding),
                "disclosure does not name {finding}: {disclosure}"
            );
        }
        assert!(
            sources
                .iter()
                .any(|source| source.origin
                    == format!("{} build.rustflags", project_config.display())),
            "the including file's own tables are still read: {sources:?}"
        );
    }

    /// A config file or include chain targo trust cannot fully examine could
    /// carry exactly the `[host]` backend the refusal exists for, so it refuses
    /// the run. Cargo rejects every one of these configs itself, so no run that
    /// would otherwise succeed is lost; an optional include of a missing file
    /// is skipped, as Cargo skips it.
    #[test]
    fn host_rustflags_refusal_fails_closed_on_cargo_config_it_cannot_examine() {
        let temp = tempfile::tempdir().expect("unexamined config fixture");
        let no_extra: &[(&str, &str)] = &[];
        for (label, config, extra) in [
            (
                "cycle",
                "include = [\"loop.toml\"]\n",
                &[("loop.toml", "include = [\"config.toml\"]\n")][..],
            ),
            ("missing", "include = [\"missing.toml\"]\n", no_extra),
            (
                "extension",
                "include = [\"host.cfg\"]\n",
                &[("host.cfg", "[host]\nrustflags = []\n")][..],
            ),
            (
                "string",
                "include = \"host.toml\"\n",
                &[("host.toml", "[host]\nrustflags = []\n")][..],
            ),
            ("no-path", "include = [{ optional = true }]\n", no_extra),
            ("glob", "include = [\"*.toml\"]\n", no_extra),
            (
                "unparseable-include",
                "include = [\"bad.toml\"]\n",
                &[("bad.toml", "[host\nrustflags = [\n")][..],
            ),
            ("unparseable", "[host\n", no_extra),
        ] {
            let project = temp.path().join(label);
            let cargo_dir = project.join(".cargo");
            fs::create_dir_all(&cargo_dir).expect("config dir");
            fs::write(cargo_dir.join("config.toml"), config).expect("config");
            for (name, contents) in extra {
                fs::write(cargo_dir.join(name), contents).expect("included config");
            }
            let sources = inherited_rustflags_sources(Some(&project), None, &[], &[]);
            let refusal = host_rustflags_external_code_refusal(&sources)
                .unwrap_or_else(|| panic!("`{label}` config must refuse the run: {sources:?}"));
            assert!(refusal.starts_with(HOST_RUSTFLAGS_EXTERNAL_CODE_TAG), "{label}: {refusal}");
            assert!(refusal.contains("could not be examined"), "{label}: {refusal}");
            assert!(refusal.contains(&cargo_dir.display().to_string()), "{label}: {refusal}");
        }

        let project = temp.path().join("optional");
        let cargo_dir = project.join(".cargo");
        fs::create_dir_all(&cargo_dir).expect("config dir");
        fs::write(
            cargo_dir.join("config.toml"),
            "include = [{ path = \"absent.toml\", optional = true }, \"plain.toml\"]\n",
        )
        .expect("config");
        fs::write(cargo_dir.join("plain.toml"), "[host]\nrustflags = [\"--cfg=kani\"]\n")
            .expect("included config");
        let sources = inherited_rustflags_sources(Some(&project), None, &[], &[]);
        assert_eq!(host_rustflags_external_code_refusal(&sources), None, "{sources:?}");
        assert!(
            sources.iter().any(|source| source.origin.ends_with("plain.toml host.rustflags")),
            "{sources:?}"
        );
    }
}
