//! Trust: classify source readiness in the native parser's actual invocation.
//!
//! The actual Flags parser selects one shared preparation scope before any
//! standalone writer. A full request checks the complete recipe envelope with
//! the existing complete checker on every host; on Darwin each of its fetches
//! runs under the helper's per-fetch retirement custodian
//! (docs/DECISION_QUEUE.md DARWIN-DEPENDENCY-FETCH-CUSTODIAN-1) until the
//! original managed Root path is qualified
//! (docs/OPEN_ISSUES.md BOOTSTRAP-DEPENDENCY-CUSTODY-1).
//! Selected developer requests retain their actual frozen Cargo producers.
//! Classification DATA never supplies availability or source/child custody.

use std::collections::BTreeSet;
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use crate::core::builder::Kind;
use crate::core::config::flags::Flags;
use crate::core::config::{Config, DryRun};
use crate::core::session::Session;
use crate::utils::exec::{BootstrapCommand, command};
use crate::utils::helpers;

/// Native request classification DATA, never readiness, custody or completion.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreparationScope {
    NotProducer,
    RequestSources,
    FullEnvelope,
}

impl PreparationScope {
    fn selection(kind: Kind, stage: Option<u32>, paths: bool, defaults: bool) -> Self {
        match kind {
            Kind::Build
            | Kind::Check
            | Kind::Clippy
            | Kind::Fix
            | Kind::Doc
            | Kind::Test
            | Kind::Miri
            | Kind::Bench
            | Kind::Run => {
                if stage.is_some_and(|stage| stage <= 1) && paths && !defaults {
                    Self::RequestSources
                } else {
                    Self::FullEnvelope
                }
            }
            Kind::Dist | Kind::Install | Kind::MiriSetup | Kind::MiriTest => Self::FullEnvelope,
            Kind::Clean | Kind::Format | Kind::Setup | Kind::Vendor => Self::NotProducer,
        }
    }
    pub(crate) fn for_flags(flags: &Flags) -> Self {
        Self::selection(
            flags.cmd.kind(),
            flags.stage,
            !flags.paths.is_empty(),
            flags.include_default_paths,
        )
    }
    pub(crate) fn for_config(config: &Config) -> Self {
        Self::selection(
            config.cmd.kind(),
            config.explicit_stage_from_cli.then_some(config.stage),
            !config.paths.is_empty(),
            config.include_default_paths,
        )
    }
}

pub(crate) fn ensure(
    config: &Config,
    initial_rustc: &Path,
    initial_cargo: &Path,
) -> Result<(), String> {
    ensure_bound(config, initial_rustc, initial_cargo, std::env::var_os("BOOTSTRAP_PYTHON"))
}

// Trust: SelfCheck has already walked the SAME selected native Step graph.
// Fetching this separate workspace, unlike startup metadata --no-deps, checks
// its transitive index and source/archive inputs without compiling anything.
// Full requests already check the entire recipe envelope. Explicit dry runs
// and tools whose graph never requests std keep their existing fast paths.
pub(crate) fn check_selected_std_sources(sess: &Session, requested: bool) -> Result<(), String> {
    if !requested {
        return Ok(());
    }
    check_selected_manifest_sources(sess, Path::new("library/Cargo.toml"), "std")
}

pub(crate) fn check_selected_tool_sources(
    sess: &Session,
    manifests: &BTreeSet<PathBuf>,
) -> Result<(), String> {
    for manifest in manifests {
        check_selected_manifest_sources(sess, manifest, "tool")?;
    }
    Ok(())
}

fn check_selected_manifest_sources(
    sess: &Session,
    relative_manifest: &Path,
    role: &str,
) -> Result<(), String> {
    if !matches!(sess.config.get_dry_run(), DryRun::SelfCheck)
        || PreparationScope::for_config(&sess.config) != PreparationScope::RequestSources
    {
        return Ok(());
    }
    let manifest = sess.src.join(relative_manifest);
    eprintln!("Trust source readiness: checking selected {role} inputs ({})", manifest.display());
    let mut command = selected_manifest_check_command(
        &sess.initial_cargo,
        &sess.initial_rustc,
        &sess.src,
        relative_manifest,
    );
    if !command.run(sess) {
        return Err(format!(
            "selected {role} locked offline inputs unavailable: {}; prepare with the same Cargo home: {} fetch --locked --manifest-path {}",
            manifest.display(),
            sess.initial_cargo.display(),
            manifest.display(),
        ));
    }
    Ok(())
}

#[cfg(test)]
fn selected_std_check_command(cargo: &Path, rustc: &Path, source: &Path) -> BootstrapCommand {
    selected_manifest_check_command(cargo, rustc, source, Path::new("library/Cargo.toml"))
}

fn selected_manifest_check_command(
    cargo: &Path,
    rustc: &Path,
    source: &Path,
    relative_manifest: &Path,
) -> BootstrapCommand {
    let mut command = command(cargo).allow_failure();
    // Reuse the original scheduler/child transport and Cargo's normal cache
    // exclusion. No saved availability seal or new source/SDK owner is made.
    command.metadata_scheduler();
    command
        .run_in_dry_run()
        .env("RUSTC", rustc)
        .env("RUSTC_BOOTSTRAP", "1")
        .env_remove("CARGO_BUILD_TARGET")
        .args(["fetch", "--frozen", "--manifest-path"])
        .arg(source.join(relative_manifest))
        // Match Builder::bare_cargo's config lookup and relative tool binding.
        .current_dir(source);
    command
}

/// `ensure` with x.py's bound interpreter passed in, not read from the
/// process environment, so a test can name the checker's interpreter.
fn ensure_bound(
    config: &Config,
    initial_rustc: &Path,
    initial_cargo: &Path,
    bound_python: Option<OsString>,
) -> Result<(), String> {
    let scope = PreparationScope::for_config(config);
    if config.dry_run() || scope == PreparationScope::NotProducer {
        return Ok(());
    }
    if scope == PreparationScope::RequestSources {
        eprintln!("Trust source readiness: selected request (native frozen Cargo)");
        return Ok(());
    }

    // x.py binds the interpreter that materialized this native metatool. A
    // direct native full request must select one explicitly, rather than guess
    // another Python through PATH (the generic sanity fallback allows Python2).
    let python = bound_python
        .or_else(|| config.python.as_ref().map(|path| path.as_os_str().to_owned()))
        .ok_or("full source readiness needs BOOTSTRAP_PYTHON or build.python; run through x.py or select a supported Python interpreter")?;
    let mut command = full_check_command(config, initial_rustc, initial_cargo, &python)?;
    eprintln!("Trust source readiness: checking complete locked offline recipe envelope");
    run_full_check(&mut command)?;
    eprintln!("Trust source readiness: complete recipe envelope checked");
    Ok(())
}

fn full_check_command(
    config: &Config,
    initial_rustc: &Path,
    initial_cargo: &Path,
    python: &OsStr,
) -> Result<Command, String> {
    let invocation_dir = std::env::current_dir()
        .map_err(|error| format!("cannot bind source-readiness tool paths: {error}"))?;
    let python = anchored_program(Path::new(python), &invocation_dir)?;
    let initial_rustc = anchored_program(initial_rustc, &invocation_dir)?;
    let initial_cargo = anchored_program(initial_cargo, &invocation_dir)?;
    let mut command = Command::new(python);
    command
        .args(["-I", "-S", "-B"])
        .arg(config.src.join("scripts/bootstrap_dependency_closure.py"))
        .arg("check")
        .arg("--repo-root")
        .arg(&config.src)
        .arg("--targo")
        // Preserve the actual configured compatibility name and path spelling.
        .arg(initial_cargo)
        .current_dir(&config.src)
        .env("RUSTC", initial_rustc)
        .env("RUSTC_BOOTSTRAP", "1")
        .env_remove("CARGO_BUILD_TARGET")
        // Progress/refusals remain visible. The helper's JSON is an observation,
        // not a portable seal or an input to the native admission decision.
        .stdout(Stdio::null())
        .stderr(Stdio::inherit());
    // Do not leak a Unix host loader directory into stage0 probes. On Windows
    // and Cygwin this variable is PATH, which must retain tool search semantics.
    if helpers::dylib_path_var() != "PATH" {
        command.env_remove(helpers::dylib_path_var());
    }
    // Inherit the operator's Cargo home, warning-policy presence/value and
    // network/credential environment. Do not inject producer deny-warnings,
    // features or flags through Builder::cargo. The helper's check mode always
    // adds --locked --offline under one original deadline.
    Ok(command)
}

fn anchored_program(path: &Path, invocation_dir: &Path) -> Result<PathBuf, String> {
    if path.is_absolute() {
        return Ok(path.to_owned());
    }
    // Changing cwd must not change a relative tool's selection. Keep symlink
    // and compatibility-name spelling: canonicalization can rename cargo/targo.
    if path.parent().is_some_and(|parent| !parent.as_os_str().is_empty()) {
        let bound = invocation_dir.join(path);
        if bound.is_absolute() {
            return Ok(bound);
        }
    }
    Err("full source readiness needs explicit executable paths (absolute or directory-relative); bare PATH names do not bind the selected driver".into())
}

fn run_full_check(command: &mut Command) -> Result<(), String> {
    crate::utils::exec::require_standalone_process("full source-readiness command")
        .map_err(|error| error.to_string())?;
    let status = command
        .status()
        .map_err(|error| format!("cannot execute full source-readiness check: {error}"))?;
    if !status.success() {
        return Err(format!("complete locked offline recipe envelope refused ({status})"));
    }
    Ok(())
}

#[cfg(test)]
mod tests;
