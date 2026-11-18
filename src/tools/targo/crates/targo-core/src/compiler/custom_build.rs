//! How to execute a build script and parse its output.
//!
//! ## Preparing a build script run
//!
//! A [build script] is an optional Rust script Cargo will run before building
//! your package. As of this writing, two kinds of special [`Unit`]s will be
//! constructed when there is a build script in a package.
//!
//! * Build script compilation --- This unit is generally the same as units
//!   that would compile other Cargo targets. It will recursively creates units
//!   of its dependencies. One biggest difference is that the [`Unit`] of
//!   compiling a build script is flagged as [`TargetKind::CustomBuild`].
//! * Build script execution --- During the construction of the [`UnitGraph`],
//!   Cargo inserts a [`Unit`] with [`CompileMode::RunCustomBuild`]. This unit
//!   depends on the unit of compiling the associated build script, to ensure
//!   the executable is available before running. The [`Work`] of running the
//!   build script is prepared in the function [`prepare`].
//!
//! ## Running a build script
//!
//! When running a build script, Cargo is aware of the progress and the result
//! of a build script. Standard output is the chosen interprocess communication
//! between Cargo and build script processes. A set of strings is defined for
//! that purpose. These strings, a.k.a. instructions, are interpreted by
//! [`BuildOutput::parse`] and stored in [`BuildRunner::build_script_outputs`].
//! The entire execution work is constructed by [`build_work`].
//!
//! [build script]: https://doc.rust-lang.org/nightly/cargo/reference/build-scripts.html
//! [`TargetKind::CustomBuild`]: crate::workspace::manifest::TargetKind::CustomBuild
//! [`UnitGraph`]: super::unit_graph::UnitGraph
//! [`CompileMode::RunCustomBuild`]: crate::compiler::CompileMode::RunCustomBuild
//! [instructions]: https://doc.rust-lang.org/cargo/reference/build-scripts.html#outputs-of-the-build-script

use super::{
    BuildRunner, Job, TRUST_VERIFY_OFF_OPTION, Unit, Work, fingerprint, get_dynamic_search_path,
};
use crate::compiler::CompileMode;
use crate::compiler::artifact;
use crate::compiler::build_runner::UnitHash;
// Trust: cached directives are data from an original successful process, not
// whatever a later pathname read happens to return.
use crate::compiler::fingerprint::build_script_output::{CachedOutput, ReceiptKey, write_atomic};
use crate::compiler::job_queue::JobState;
use crate::util::data_structures::HashMap;
use crate::util::data_structures::HashSet;
use crate::util::errors::CargoResult;
use crate::util::internal;
use crate::util::machine_message::{self, Message};
use crate::util::process_authority::{
    NativePairingInputRole, is_compiler_flag_environment, prepare_native_pairing_input,
};
// Trust: EW-9 re-rooting of cached output recorded in another tree.
use crate::util::relocation_roots::OutputRelocation;
use crate::util::rustc_options::rustc_option_parts;
use crate::workspace::{PackageId, Target, profiles::ProfileRoot};
use anyhow::{Context as _, bail};
use cargo_platform::Cfg;
use cargo_util::{ProcessBuilder, paths};
use cargo_util_schemas::manifest::RustVersion;
use std::collections::BTreeSet;
use std::collections::hash_map::Entry;
use std::path::{Path, PathBuf};
use std::str;
use std::sync::{Arc, Mutex};

/// A build script instruction that tells Cargo to display an error after the
/// build script has finished running. Read [the doc] for more.
///
/// [the doc]: https://doc.rust-lang.org/nightly/cargo/reference/build-scripts.html#cargo-error
const CARGO_ERROR_SYNTAX: &str = "cargo::error=";
/// Deprecated: A build script instruction that tells Cargo to display a warning after the
/// build script has finished running. Read [the doc] for more.
///
/// [the doc]: https://doc.rust-lang.org/nightly/cargo/reference/build-scripts.html#cargo-warning
const OLD_CARGO_WARNING_SYNTAX: &str = "cargo:warning=";
/// A build script instruction that tells Cargo to display a warning after the
/// build script has finished running. Read [the doc] for more.
///
/// [the doc]: https://doc.rust-lang.org/nightly/cargo/reference/build-scripts.html#cargo-warning
const NEW_CARGO_WARNING_SYNTAX: &str = "cargo::warning=";

// Trust: configured build-output identity includes diagnostic severity.
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, serde::Serialize)]
pub enum Severity {
    Error,
    Warning,
}

pub type LogMessage = (Severity, String);

/// Represents a path added to the library search path.
///
/// We need to keep track of requests to add search paths within the cargo build directory
/// separately from paths outside of Cargo. The reason is that we want to give precedence to linking
/// against libraries within the Cargo build directory even if a similar library exists in the
/// system (e.g. crate A adds `/usr/lib` to the search path and then a later build of crate B adds
/// `target/debug/...` to satisfy its request to link against the library B that it built, but B is
/// also found in `/usr/lib`).
///
/// There's some nuance here because we want to preserve relative order of paths of the same type.
/// For example, if the build process would in declaration order emit the following linker line:
/// ```bash
/// -L/usr/lib -Ltarget/debug/build/crate1/libs -L/lib -Ltarget/debug/build/crate2/libs)
/// ```
///
/// we want the linker to actually receive:
/// ```bash
/// -Ltarget/debug/build/crate1/libs -Ltarget/debug/build/crate2/libs) -L/usr/lib -L/lib
/// ```
///
/// so that the library search paths within the crate artifacts directory come first but retain
/// relative ordering while the system library paths come after while still retaining relative
/// ordering among them; ordering is the order they are emitted within the build process,
/// not lexicographic order.
///
/// WARNING: Even though this type implements PartialOrd + Ord, this is a lexicographic ordering.
/// The linker line will require an explicit sorting algorithm. PartialOrd + Ord is derived because
/// BuildOutput requires it but that ordering is different from the one for the linker search path,
/// at least today. It may be worth reconsidering & perhaps it's ok if BuildOutput doesn't have
/// a lexicographic ordering for the library_paths? I'm not sure the consequence of that.
// Trust: canonical unit evidence includes configured build-script overrides.
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, serde::Serialize)]
pub enum LibraryPath {
    /// The path is pointing within the output folder of the crate and takes priority over
    /// external paths when passed to the linker.
    CargoArtifact(PathBuf),
    /// The path is pointing outside of the crate's build location. The linker will always
    /// receive such paths after `CargoArtifact`.
    External(PathBuf),
}

impl LibraryPath {
    fn new(p: PathBuf, script_out_dir: &Path) -> Self {
        let search_path = get_dynamic_search_path(&p);
        if search_path.starts_with(script_out_dir) {
            Self::CargoArtifact(p)
        } else {
            Self::External(p)
        }
    }

    pub fn into_path_buf(self) -> PathBuf {
        match self {
            LibraryPath::CargoArtifact(p) | LibraryPath::External(p) => p,
        }
    }
}

impl AsRef<PathBuf> for LibraryPath {
    fn as_ref(&self) -> &PathBuf {
        match self {
            LibraryPath::CargoArtifact(p) | LibraryPath::External(p) => p,
        }
    }
}

/// Contains the parsed output of a custom build script.
// Trust: serialize values, never their process-local allocation identities.
#[derive(Clone, Debug, Hash, Default, PartialEq, Eq, PartialOrd, Ord, serde::Serialize)]
pub struct BuildOutput {
    /// Paths to pass to rustc with the `-L` flag.
    pub library_paths: Vec<LibraryPath>,
    /// Names and link kinds of libraries, suitable for the `-l` flag.
    pub library_links: Vec<String>,
    /// Linker arguments suitable to be passed to `-C link-arg=<args>`
    pub linker_args: Vec<(LinkArgTarget, String)>,
    /// Various `--cfg` flags to pass to the compiler.
    pub cfgs: Vec<String>,
    /// Various `--check-cfg` flags to pass to the compiler.
    pub check_cfgs: Vec<String>,
    /// Additional environment variables to run the compiler with.
    pub env: Vec<(String, String)>,
    /// Metadata to pass to the immediate dependencies.
    pub metadata: Vec<(String, String)>,
    /// Paths to trigger a rerun of this build script.
    /// May be absolute or relative paths (relative to package root).
    pub rerun_if_changed: Vec<PathBuf>,
    /// Environment variables which, when changed, will cause a rebuild.
    pub rerun_if_env_changed: Vec<String>,
    /// Errors and warnings generated by this build.
    ///
    /// These are only displayed if this is a "local" package, `-vv` is used, or
    /// there is a build error for any target in this package. Note that any log
    /// message of severity `Error` will by itself cause a build error, and will
    /// cause all log messages to be displayed.
    pub log_messages: Vec<LogMessage>,
}

/// Map of packages to build script output.
///
/// This initially starts out as empty. Overridden build scripts get
/// inserted during `build_map`. The rest of the entries are added
/// immediately after each build script runs.
///
/// The [`UnitHash`] is the unique metadata hash for the `RunCustomBuild` Unit of
/// the package. It needs a unique key, since the build script can be run
/// multiple times with different profiles or features. We can't embed a
/// `Unit` because this structure needs to be shareable between threads.
#[derive(Default)]
pub struct BuildScriptOutputs {
    outputs: HashMap<UnitHash, BuildOutput>,
}

/// Linking information for a `Unit`.
///
/// See [`build_map`] for more details.
#[derive(Default)]
pub struct BuildScripts {
    /// List of build script outputs this Unit needs to include for linking. Each
    /// element is an index into `BuildScriptOutputs`.
    ///
    /// Cargo will use this `to_link` vector to add `-L` flags to compiles as we
    /// propagate them upwards towards the final build. Note, however, that we
    /// need to preserve the ordering of `to_link` to be topologically sorted.
    /// This will ensure that build scripts which print their paths properly will
    /// correctly pick up the files they generated (if there are duplicates
    /// elsewhere).
    ///
    /// To preserve this ordering, the (id, metadata) is stored in two places, once
    /// in the `Vec` and once in `seen_to_link` for a fast lookup. We maintain
    /// this as we're building interactively below to ensure that the memory
    /// usage here doesn't blow up too much.
    ///
    /// For more information, see #2354.
    pub to_link: Vec<(PackageId, UnitHash)>,
    /// This is only used while constructing `to_link` to avoid duplicates.
    seen_to_link: HashSet<(PackageId, UnitHash)>,
    /// Host-only dependencies that have build scripts. Each element is an
    /// index into `BuildScriptOutputs`.
    ///
    /// This is the set of transitive dependencies that are host-only
    /// (proc-macro, plugin, build-dependency) that contain a build script.
    /// Any `BuildOutput::library_paths` path relative to `target` will be
    /// added to `LD_LIBRARY_PATH` so that the compiler can find any dynamic
    /// libraries a build script may have generated.
    pub plugins: BTreeSet<(PackageId, UnitHash)>,
}

/// Dependency information as declared by a build script that might trigger
/// a recompile of itself.
#[derive(Debug)]
pub struct BuildDeps {
    /// Absolute path to the file in the target directory that stores the
    /// output of the build script.
    pub build_script_output: PathBuf,
    /// Files that trigger a rebuild if they change.
    pub rerun_if_changed: Vec<PathBuf>,
    /// Environment variables that trigger a rebuild if they change.
    pub rerun_if_env_changed: Vec<String>,
    /// Trust: exact original controls used for this invocation's planning.
    pub(super) cached_receipt: Option<ReceiptKey>,
    /// Trust: exact ordered late manifest values from those same parsed
    /// controls. None means unavailable, not a known empty overlay. Native
    /// freshness may use these only with the original planning receipt.
    pub(super) manifest_env_overrides: Option<Vec<(String, String)>>,
    /// Trust: original cfg/check-cfg operands from those same parsed controls.
    /// None means unavailable; these are never expanded or read as paths.
    compiler_cfg_args: Option<Vec<String>>,
    /// Trust: the complete output parsed from the SAME bounded planning
    /// controls. This is not inserted into the live execution-output map.
    command_output: Option<BuildOutput>,
    /// Trust: EW-9. The previous output was recorded under other
    /// `-Ztrust-relocation-roots` and could not be re-rooted, so it must not
    /// be replayed: the script runs again.
    pub(super) relocation_refused: bool,
}

/// Represents one of the instructions from `cargo::rustc-link-arg-*` build
/// script instruction family.
///
/// In other words, indicates targets that custom linker arguments applies to.
///
/// See the [build script documentation][1] for more.
///
/// [1]: https://doc.rust-lang.org/nightly/cargo/reference/build-scripts.html#cargorustc-link-argflag
// Trust: preserve the target distinction in canonical build-output evidence.
#[derive(Clone, Hash, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize)]
pub enum LinkArgTarget {
    /// Represents `cargo::rustc-link-arg=FLAG`.
    All,
    /// Represents `cargo::rustc-cdylib-link-arg=FLAG`.
    Cdylib,
    /// Represents `cargo::rustc-link-arg-bins=FLAG`.
    Bin,
    /// Represents `cargo::rustc-link-arg-bin=BIN=FLAG`.
    SingleBin(String),
    /// Represents `cargo::rustc-link-arg-tests=FLAG`.
    Test,
    /// Represents `cargo::rustc-link-arg-benches=FLAG`.
    Bench,
    /// Represents `cargo::rustc-link-arg-examples=FLAG`.
    Example,
}

impl LinkArgTarget {
    /// Checks if this link type applies to a given [`Target`].
    pub fn applies_to(&self, target: &Target, mode: CompileMode) -> bool {
        let is_test = mode.is_any_test();
        match self {
            LinkArgTarget::All => true,
            LinkArgTarget::Cdylib => !is_test && target.is_cdylib(),
            LinkArgTarget::Bin => target.is_bin(),
            LinkArgTarget::SingleBin(name) => target.is_bin() && target.name() == name,
            LinkArgTarget::Test => target.is_test(),
            LinkArgTarget::Bench => target.is_bench(),
            LinkArgTarget::Example => target.is_exe_example(),
        }
    }
}

/// Prepares a `Work` that executes the target as a custom build script.
#[tracing::instrument(skip_all)]
pub fn prepare(build_runner: &mut BuildRunner<'_, '_>, unit: &Unit) -> CargoResult<Job> {
    let metadata = build_runner.get_run_build_script_metadata(unit);
    if build_runner
        .build_script_outputs
        .lock()
        .unwrap()
        .contains_key(metadata)
    {
        // The output is already set, thus the build script is overridden.
        fingerprint::prepare_target(build_runner, unit, false)
    } else {
        build_work(build_runner, unit)
    }
}

/// Emits the output of a build script as a [`machine_message::BuildScript`]
/// JSON string to standard output.
fn emit_build_output(
    state: &JobState<'_, '_>,
    output: &BuildOutput,
    out_dir: &Path,
    package_id: PackageId,
) -> CargoResult<()> {
    let library_paths = output
        .library_paths
        .iter()
        .map(|l| l.as_ref().display().to_string())
        .collect::<Vec<_>>();

    let msg = machine_message::BuildScript {
        package_id: package_id.to_spec(),
        linked_libs: &output.library_links,
        linked_paths: &library_paths,
        cfgs: &output.cfgs,
        env: &output.env,
        out_dir,
    }
    .to_json_string();
    state.stdout(msg)?;
    Ok(())
}

// Trust: from here to `build_work` is Trust-authored. A build script is
// arbitrary code that Cargo runs with the same environment the frontend holds,
// which for a verified run includes the proof session, the artifact root, and
// every raw compiler-flag channel. None of that is input a build script needs,
// and all of it is authority it could otherwise re-emit or redirect. The scrub
// is explicit-list *plus* a `TRUST_` prefix rule so a control added later fails
// closed instead of silently inheriting.
#[cfg(test)]
const TRUST_PROOF_ARTIFACT_ROOT_OPTION: &str = "trust-proof-artifact-root";

const TRUST_TARGO_INTERNAL_BUILD_SCRIPT_ENV: &[&str] = &[
    super::TRUST_TARGO_LANE_RUSTFLAGS_ENV,
    "TRUST_TARGO_PREPARED_TESTS_EXPORT",
    "TRUST_TARGO_PREPARED_TESTS_SESSION",
    "TRUST_TARGO_PREPARED_TEST_SESSION",
    "TRUST_TARGO_TEST_EXECUTION_MANIFEST",
    "TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256",
    "TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION",
    "TRUST_TARGO_TEST_MONITOR_SESSION",
    "TRUST_TARGO_VERIFY",
    "TRUST_TARGO_FRONTEND",
];

/// Trust: remove Targo's private protocol and every raw compiler-flag channel
/// before executing untrusted build-script code. The explicit list documents
/// the current protocol, while the `TRUST_` prefix rule fails closed for future
/// controls that have not yet been added to it.
fn scrub_verified_build_script_authority_env(cmd: &mut ProcessBuilder) {
    for name in TRUST_TARGO_INTERNAL_BUILD_SCRIPT_ENV {
        cmd.env_remove(name);
    }

    let explicitly_configured = cmd.get_envs().keys().cloned().collect::<Vec<_>>();
    for name in explicitly_configured {
        if name.starts_with("TRUST_") || is_compiler_flag_environment(&name) {
            cmd.env_remove(&name);
        }
    }

    // `host_process` inherits Targo's environment. Remove every rustc and
    // rustdoc flag spelling, including target-specific Cargo variables and
    // Bootstrap's private variables. Iterate the raw environment so
    // non-Unicode values cannot evade the boundary.
    #[allow(clippy::disallowed_methods)]
    let inherited_environment = std::env::vars_os();
    for (name, _) in inherited_environment {
        if let Some(name) = name.to_str()
            && (name.starts_with("TRUST_") || is_compiler_flag_environment(name))
        {
            cmd.env_remove(name);
        }
    }
}

/// The flag vector exposed to an executed build script: the unit's flags with
/// every Targo-owned Trust control removed, then exactly one canonical
/// verification off-switch (`-Z` `TRUST_VERIFY_OFF_OPTION`).
///
/// The unit itself keeps the original flags, so Cargo's own rustc invocations
/// (including the host compilation of the build script) still receive the
/// complete verified policy. `CARGO_ENCODED_RUSTFLAGS`, however, is part of a
/// build script's untrusted runtime environment. Exposing the session, proof
/// root, package/role metadata, or any other current/future `trust-*` control
/// lets package code replay authority, forge a compiler scope, or mutate the
/// proof store. A verified invocation therefore requires exactly one canonical
/// session/root pair and withholds every Trust control the unit carries from
/// the build-script runtime copy, its own off-switch or `on` included.
///
/// Trust (B5 step A, 2026-10-01): the copy then ends in Targo's own off-switch,
/// whatever the unit's role. The only compilations that read this variable
/// are the ones the script itself starts: a compiler probe (anyhow, thiserror,
/// proc-macro2, rustix, autocfg) runs `$RUSTC` with it and emits a cfg when the
/// probe compiles. With no switch the probe ran trustc's verifying default,
/// the strict default refuted probe code (`a / b`, measured on trustc
/// 321aaeda7), and the cfg went missing with no error, so a verified build
/// compiled other code than `targo --unverified`, whose scripts see the
/// switch. Handing the switch over grants no authority, so "no Targo
/// authority reaches the build script" still holds:
///   * it only turns verification off in compilations the script starts.
///     Those carry no session (withheld above), so they can mint no
///     session-bound evidence, and what a script makes of them reaches the
///     build only as its own output, which the report already rows as the
///     `build-execution-scope` premise;
///   * any script can already type it: trustc honors `-Z trust-verify=off`
///     with every `TRUST_*` variable removed (measured, same trustc);
///   * nothing the unit carries is copied: the switch is Targo's constant,
///     appended after the strip, never the unit's own value.
/// A probe that ignores this variable gets trustc's verifying default in
/// `targo --unverified` too, whose switch also travels only here (measured:
/// exit 1 on `a / b` with that lane's environment and no flags), so the two
/// lanes agree; neither matches stock rustc for such a probe. None of the 5
/// compiler probes among the 39 build scripts of trust-ir's `--workspace`
/// graph ignores it (census, 2026-10-01).
fn build_script_rustflags_without_targo_authority(
    rustflags: &[String],
    verified_targo: bool,
) -> CargoResult<Vec<String>> {
    if !verified_targo {
        return Ok(rustflags.to_vec());
    }

    let mut sanitized = Vec::with_capacity(rustflags.len());
    let mut roots_removed = 0usize;
    let mut sessions_removed = 0usize;
    let mut index = 0usize;
    while index < rustflags.len() {
        let (option, split) = if rustflags[index] == "-Z" {
            let option = rustflags.get(index + 1).ok_or_else(|| {
                anyhow::anyhow!(
                    "verified Targo build-script RUSTFLAGS end with an incomplete `-Z` option"
                )
            })?;
            (Some(option.as_str()), true)
        } else {
            (
                rustflags[index]
                    .strip_prefix("-Z")
                    .filter(|option| !option.is_empty()),
                false,
            )
        };

        let option_parts = option.map(rustc_option_parts);
        let is_targo_authority = option_parts
            .as_ref()
            .is_some_and(|(name, _)| name == "trust_verify" || name.starts_with("trust_"));
        if is_targo_authority {
            let (option_name, value) = option_parts.expect("checked above");
            match option_name.as_ref() {
                "trust_proof_artifact_root" => {
                    let root = value.ok_or_else(|| {
                            anyhow::anyhow!(
                                "verified Targo build-script policy requires -Ztrust-proof-artifact-root=<absolute-path>"
                            )
                        })?;
                    if root.is_empty() || root.trim() != root || !Path::new(root).is_absolute() {
                        bail!(
                            "verified Targo build-script policy requires one non-empty, trimmed absolute proof artifact root"
                        );
                    }
                    roots_removed += 1;
                    if roots_removed > 1 {
                        bail!(
                            "verified Targo build-script policy contains duplicate -Ztrust-proof-artifact-root options"
                        );
                    }
                }
                "trust_verify_session" => {
                    let session = value.ok_or_else(|| {
                            anyhow::anyhow!(
                                "verified Targo build-script policy requires -Ztrust-verify-session=<nonce>"
                            )
                        })?;
                    if session.is_empty() || session.trim() != session {
                        bail!(
                            "verified Targo build-script policy requires one non-empty, trimmed verification session"
                        );
                    }
                    sessions_removed += 1;
                    if sessions_removed > 1 {
                        bail!(
                            "verified Targo build-script policy contains duplicate -Ztrust-verify-session options"
                        );
                    }
                }
                _ => {}
            }
            index += if split { 2 } else { 1 };
            continue;
        }

        sanitized.push(rustflags[index].clone());
        if split {
            sanitized.push(rustflags[index + 1].clone());
        }
        index += if split { 2 } else { 1 };
    }

    if roots_removed != 1 || sessions_removed != 1 {
        bail!(
            "verified Targo refuses to execute a build script without exactly one private verification session and proof artifact root to withhold"
        );
    }
    sanitized.extend(["-Z".to_string(), TRUST_VERIFY_OFF_OPTION.to_string()]);
    Ok(sanitized)
}

fn scrub_compiler_flag_environment(
    cmd: &mut ProcessBuilder,
    inherited_names: impl IntoIterator<Item = String>,
) {
    const CANONICAL_ENCODED_RUSTFLAGS: &str = "CARGO_ENCODED_RUSTFLAGS";

    let replaced_by_canonical_rustflags =
        |name: &str| cfg!(windows) && name.eq_ignore_ascii_case(CANONICAL_ENCODED_RUSTFLAGS);
    // `host_process` has already materialized project `[env]` values as
    // explicit ProcessBuilder entries. Scrubbing only the parent process would
    // therefore allow those entries to reinstall a private flag channel.
    let explicit_names = cmd
        .get_envs()
        .keys()
        .filter(|name| is_compiler_flag_environment(name))
        .cloned()
        .collect::<Vec<_>>();
    for name in explicit_names {
        if replaced_by_canonical_rustflags(&name) {
            // On Windows, retaining both a differently-cased tombstone and
            // the canonical sanitized value makes BTreeMap iteration order
            // decide which case-insensitive child variable survives.
            cmd.env_clear_override(&name);
        } else {
            cmd.env_remove(&name);
        }
    }
    for name in inherited_names
        .into_iter()
        .filter(|name| is_compiler_flag_environment(name))
    {
        if !replaced_by_canonical_rustflags(&name) {
            cmd.env_remove(&name);
        }
    }
}

// Trust: the normal command and native queue capture select the SAME actual
// compiled dependency/UnitOutput. This is compiler graph selection, never a
// path supplied by a saved report or another process.
pub(super) fn compiled_script_executable(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
) -> CargoResult<(Unit, PathBuf)> {
    anyhow::ensure!(
        unit.mode.is_run_custom_build(),
        "native script selection requires a RunCustomBuild unit"
    );
    let compiled = build_runner
        .unit_deps(unit)
        .iter()
        .find(|dep| !dep.unit.mode.is_run_custom_build() && dep.unit.target.is_custom_build())
        .map(|dep| dep.unit.clone())
        .ok_or_else(|| anyhow::anyhow!("script has no actual compiled build-script dependency"))?;
    let directory = build_runner.files().build_script_dir(&compiled);
    let bin_name = if build_runner.bcx.gctx.cli_unstable().build_dir_new_layout {
        unit.target.crate_name()
    } else {
        unit.target.name().to_string()
    };
    Ok((compiled, directory.join(bin_name)))
}

/// Constructs the unit of work of running a build script.
///
/// The construction includes:
///
/// * Set environment variables for the build script run.
/// * Create the output dir (`OUT_DIR`) for the build script output.
/// * Determine if the build script needs a re-run.
/// * Run the build script and store its output.
fn build_work(build_runner: &mut BuildRunner<'_, '_>, unit: &Unit) -> CargoResult<Job> {
    assert!(unit.mode.is_run_custom_build());
    let bcx = &build_runner.bcx;
    let dependencies = build_runner.unit_deps(unit);
    let (build_script_unit, to_exec) = compiled_script_executable(build_runner, unit)?;
    let script_dir = build_runner.files().build_script_dir(&build_script_unit);

    let script_out_dir = script_out_dir(build_runner, unit);

    if let Some(deps) = unit.pkg.manifest().metabuild() {
        prepare_metabuild(build_runner, &build_script_unit, deps)?;
    }

    // Start preparing the process to execute, starting out with some
    // environment variables. Note that the profile-related environment
    // variables are not set with this the build script's profile but rather the
    // package's library profile.
    // NOTE: if you add any profile flags, be sure to update
    // `Profiles::get_profile_run_custom_build` so that those flags get
    // carried over.
    let to_exec = to_exec.into_os_string();
    let mut cmd = build_runner.compilation.host_process(to_exec, &unit.pkg)?;
    let debug = unit.profile.debuginfo.is_turned_on();
    cmd.env("OUT_DIR", &script_out_dir)
        .env("CARGO_MANIFEST_DIR", unit.pkg.root())
        .env("CARGO_MANIFEST_PATH", unit.pkg.manifest_path())
        .env("NUM_JOBS", &bcx.jobs().to_string())
        .env("TARGET", bcx.target_data.short_name(&unit.kind))
        .env("DEBUG", debug.to_string())
        .env("OPT_LEVEL", &unit.profile.opt_level)
        .env(
            "PROFILE",
            match unit.profile.root {
                ProfileRoot::Release => "release",
                ProfileRoot::Debug => "debug",
            },
        )
        .env("HOST", &bcx.host_triple())
        .env("RUSTC", &bcx.rustc().path)
        .env("RUSTDOC", &*bcx.gctx.rustdoc()?)
        .inherit_jobserver(&build_runner.jobserver);

    // Find all artifact dependencies and make their file and containing directory discoverable using environment variables.
    for (var, value) in artifact::get_env(build_runner, unit, dependencies)? {
        cmd.env(&var, value);
    }

    if let Some(linker) = &build_runner.compilation.target_linker(unit.kind) {
        cmd.env("RUSTC_LINKER", linker);
    }

    if let Some(links) = unit.pkg.manifest().links() {
        cmd.env("CARGO_MANIFEST_LINKS", links);
    }

    let trim_paths = &unit.profile.trim_paths;
    cmd.env("CARGO_TRIM_PATHS_SCOPE", trim_paths.to_string());
    // Trust: keep the exposed build-script remap environment and its
    // fingerprint on the same scope decision as compiler command generation.
    let pairs = if super::trim_paths::remap_enabled(trim_paths, false) {
        super::trim_paths::trim_paths_remap(build_runner, unit)
    } else {
        Vec::new()
    };
    cmd.env(
        "CARGO_TRIM_PATHS_REMAP",
        paths::join_paths(&pairs, "CARGO_TRIM_PATHS_REMAP")?,
    );

    // Be sure to pass along all enabled features for this package, this is the
    // last piece of statically known information that we have.
    for feat in &unit.features {
        cmd.env(&format!("CARGO_FEATURE_{}", super::envify(feat)), "1");
    }

    let mut cfg_map = HashMap::default();
    cfg_map.insert(
        "feature",
        unit.features.iter().map(|s| s.as_str()).collect::<Vec<_>>(),
    );
    // Manually inject debug_assertions based on the profile setting.
    // The cfg query from rustc doesn't include profile settings and would always be true,
    // so we override it with the actual profile setting.
    if unit.profile.debug_assertions {
        cfg_map.insert("debug_assertions", Vec::new());
    }
    for cfg in bcx.target_data.cfg(unit.kind) {
        match *cfg {
            Cfg::Name(ref n) => {
                // Skip debug_assertions from rustc query; we use the profile setting instead
                if n.as_str() == "debug_assertions" {
                    continue;
                }
                cfg_map.insert(n.as_str(), Vec::new());
            }
            Cfg::KeyPair(ref k, ref v) => {
                let values = cfg_map.entry(k.as_str()).or_default();
                values.push(v.as_str());
            }
        }
    }
    for (k, v) in cfg_map {
        // FIXME: We should handle raw-idents somehow instead of pretending they
        // don't exist here
        let k = format!("CARGO_CFG_{}", super::envify(k));
        cmd.env(&k, v.join(","));
    }

    // Also inform the build script of the rustc compiler context.
    if let Some(wrapper) = bcx.rustc().wrapper.as_ref() {
        cmd.env("RUSTC_WRAPPER", wrapper);
    } else {
        cmd.env_remove("RUSTC_WRAPPER");
    }
    cmd.env_remove("RUSTC_WORKSPACE_WRAPPER");
    if build_runner.bcx.ws.is_member(&unit.pkg) {
        if let Some(wrapper) = bcx.rustc().workspace_wrapper.as_ref() {
            cmd.env("RUSTC_WORKSPACE_WRAPPER", wrapper);
        }
    }
    let verified_targo = super::verified_targo_protocol_active();
    let build_script_rustflags =
        build_script_rustflags_without_targo_authority(&unit.rustflags, verified_targo)?;
    if verified_targo {
        scrub_verified_build_script_authority_env(&mut cmd);
        // Trust: `host_process` inherits Targo's environment. Remove every rustc and
        // rustdoc flag spelling, including target-specific Cargo variables and
        // Bootstrap's private variables, before installing the sanitized
        // runtime view below. Otherwise the private root can leak through a
        // secondary flag channel even when CARGO_ENCODED_RUSTFLAGS is clean.
        // GlobalContext's normalized environment is insufficient here: this
        // boundary must remove raw target-specific and explicitly configured
        // spellings before a build script starts.
        #[allow(clippy::disallowed_methods)]
        let inherited_names = std::env::vars_os().filter_map(|(name, _)| name.into_string().ok());
        scrub_compiler_flag_environment(&mut cmd, inherited_names);
    }
    cmd.env(
        "CARGO_ENCODED_RUSTFLAGS",
        build_script_rustflags.join("\x1f"),
    );
    cmd.env_remove("RUSTFLAGS");
    // Trust: this compiler input is not build-script runtime data, on either
    // lane. Keep all original scheduling transport and the compiler's own
    // captured value; never ask untrusted script output to replay it.
    prepare_native_pairing_input(&mut cmd, NativePairingInputRole::BuildScript)?;

    if build_runner.bcx.ws.gctx().extra_verbose() {
        cmd.display_env_vars();
    }

    let any_build_script_metadata = bcx.gctx.cli_unstable().any_build_script_metadata;

    // Gather the set of native dependencies that this package has along with
    // some other variables to close over.
    //
    // This information will be used at build-time later on to figure out which
    // sorts of variables need to be discovered at that time.
    let lib_deps = dependencies
        .iter()
        .filter_map(|dep| {
            if dep.unit.mode.is_run_custom_build() {
                let dep_metadata = build_runner.get_run_build_script_metadata(&dep.unit);

                let dep_name = dep.dep_name.unwrap_or(dep.unit.pkg.name());

                Some((
                    dep_name,
                    dep.unit
                        .pkg
                        .manifest()
                        .links()
                        .map(|links| links.to_string()),
                    dep.unit.pkg.package_id(),
                    dep_metadata,
                ))
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    let library_name = unit.pkg.library().map(|t| t.crate_name());
    let pkg_descr = unit.pkg.to_string();
    let build_script_outputs = Arc::clone(&build_runner.build_script_outputs);
    let id = unit.pkg.package_id();
    let run_files = BuildScriptRunFiles::for_unit(build_runner, unit);
    let output_integrity = crate::is_targo_invocation().then(|| cached_output(build_runner, unit));
    let host_target_root = build_runner.files().host_dest().map(|v| v.to_path_buf());
    let all = (
        id,
        library_name.clone(),
        pkg_descr.clone(),
        Arc::clone(&build_script_outputs),
        run_files.stdout.clone(),
        script_out_dir.clone(),
        output_integrity.clone(),
        build_runner.build_explicit_deps[unit]
            .cached_receipt
            .clone(),
    );
    let build_scripts = build_runner.build_scripts.get(unit).cloned();
    let json_messages = bcx.build_config.emit_json();
    let extra_verbose = bcx.gctx.extra_verbose();
    let capture_rusage = bcx.capture_rusage();
    let expected_receipt = build_runner.build_explicit_deps[unit]
        .cached_receipt
        .clone();
    let (mut prev_output, prev_script_out_dir, observed_receipt, _) =
        prev_build_output(build_runner, unit);
    // Trust: EW-9. A run records the relocation roots it ran under beside
    // `root-output` (removing a stale record when the flag is absent); a
    // fresh replay re-roots from them exactly as `prev_build_output` does.
    let relocation_record = build_runner
        .bcx
        .gctx
        .cli_unstable()
        .trust_relocation_roots
        .as_ref()
        .map(|roots| roots.record());
    // An unusable record made the unit stale (`relocation_refused`), so the
    // script runs and nothing is replayed from it.
    let prev_relocation = output_integrity
        .is_none()
        .then(|| output_relocation(build_runner, &run_files))
        .and_then(|relocation| relocation.ok().flatten());
    if crate::is_targo_invocation() && observed_receipt != expected_receipt {
        prev_output = None;
    }
    let metadata_hash = build_runner.get_run_build_script_metadata(unit);

    paths::create_dir_all(&script_dir)?;
    if output_integrity.is_none() {
        paths::create_dir_all(&script_out_dir)?;
    }
    paths::create_dir_all(&run_files.root)?;

    let nightly_features_allowed = build_runner.bcx.gctx.nightly_features_allowed;
    let targets: Vec<Target> = unit.pkg.targets().to_vec();
    let msrv = unit.pkg.rust_version().cloned();
    // Need a separate copy for the fresh closure.
    let targets_fresh = targets.clone();
    let msrv_fresh = msrv.clone();

    let env_profile_name = unit.profile.name.to_uppercase();
    let built_with_debuginfo = build_runner
        .bcx
        .unit_graph
        .get(unit)
        .and_then(|deps| deps.iter().find(|dep| dep.unit.target == unit.target))
        .map(|dep| dep.unit.profile.debuginfo.is_turned_on())
        .unwrap_or(false);

    // Prepare the unit of "dirty work" which will actually run the custom build
    // command.
    //
    // Note that this has to do some extra work just before running the command
    // to determine extra environment variables and such.
    let dirty = Work::new(move |state| {
        // Trust: a failed or interrupted new execution cannot leave a previous
        // success receipt describing this run's cache leaves.
        let _retired_generation = if let Some(integrity) = &output_integrity {
            integrity.prepare()?
        } else {
            None
        };
        // Make sure that OUT_DIR exists.
        //
        // If we have an old build directory, then just move it into place,
        // otherwise create it!
        paths::create_dir_all(&script_out_dir)
            .context("failed to create script output directory for build command")?;

        // For all our native lib dependencies, pick up their metadata to pass
        // along to this custom build command. We're also careful to augment our
        // dynamic library search path in case the build script depended on any
        // native dynamic libraries.
        {
            let build_script_outputs = build_script_outputs.lock().unwrap();
            for (name, links, dep_id, dep_metadata) in lib_deps {
                let script_output = build_script_outputs.get(dep_metadata).ok_or_else(|| {
                    internal(format!(
                        "failed to locate build state for env vars: {}/{}",
                        dep_id, dep_metadata
                    ))
                })?;
                let data = &script_output.metadata;
                for (key, value) in data.iter() {
                    if let Some(ref links) = links {
                        cmd.env(
                            &format!("DEP_{}_{}", super::envify(&links), super::envify(key)),
                            value,
                        );
                    }
                    if any_build_script_metadata {
                        cmd.env(
                            &format!("CARGO_DEP_{}_{}", super::envify(&name), super::envify(key)),
                            value,
                        );
                    }
                }
            }
            if let Some(build_scripts) = build_scripts
                && let Some(ref host_target_root) = host_target_root
            {
                super::add_plugin_deps(
                    &mut cmd,
                    &build_script_outputs,
                    &build_scripts,
                    host_target_root,
                )?;
            }
        }

        // Install the admitted root after all build-script environment overlays.
        state.configure_resources(&mut cmd, false)?;
        // And now finally, run the build command itself!
        state.running(&cmd);
        let timestamp = paths::set_invocation_time(&run_files.root)?;
        let prefix = format!("[{} {}] ", id.name(), id.version());
        let mut log_messages_in_case_of_panic = Vec::new();
        let span = tracing::debug_span!("build_script", process = cmd.to_string());
        let (stats, output) = span.in_scope(|| {
            let (stats, result) = super::exec_with_targo_streaming_policy(
                &cmd,
                &mut |stdout| {
                    if let Some(error) = stdout.strip_prefix(CARGO_ERROR_SYNTAX) {
                        log_messages_in_case_of_panic.push((Severity::Error, error.to_owned()));
                    }
                    if let Some(warning) = stdout
                        .strip_prefix(OLD_CARGO_WARNING_SYNTAX)
                        .or(stdout.strip_prefix(NEW_CARGO_WARNING_SYNTAX))
                    {
                        log_messages_in_case_of_panic.push((Severity::Warning, warning.to_owned()));
                    }
                    if extra_verbose {
                        state.stdout(format!("{}{}", prefix, stdout))?;
                    }
                    Ok(())
                },
                &mut |stderr| {
                    if extra_verbose {
                        state.stderr(format!("{}{}", prefix, stderr))?;
                    }
                    Ok(())
                },
                true,
                capture_rusage,
            );
            let result = result.with_context(|| {
                let mut build_error_context =
                    format!("failed to run custom build command for `{}`", pkg_descr);

                // If we're opting into backtraces, mention that build dependencies' backtraces can
                // be improved by requesting debuginfo to be built, if we're not building with
                // debuginfo already.
                #[expect(clippy::disallowed_methods, reason = "consistency with rustc")]
                if let Ok(show_backtraces) = std::env::var("RUST_BACKTRACE") {
                    if !built_with_debuginfo && show_backtraces != "0" {
                        build_error_context.push_str(&format!(
                            "\n\
                            note: To improve backtraces for build dependencies, set the \
                            CARGO_PROFILE_{env_profile_name}_BUILD_OVERRIDE_DEBUG=true environment \
                            variable to enable debug information generation.",
                        ));
                    }
                }

                build_error_context
            });
            (stats, result)
        });

        if let Some(peak_memory) = stats.peak_rss {
            state.peak_memory(peak_memory);
        }
        if let Some(times) = stats.cpu_times {
            state.cpu_times(times);
        }

        // If the build failed
        if let Err(error) = output {
            insert_log_messages_in_build_outputs(
                build_script_outputs,
                id,
                metadata_hash,
                log_messages_in_case_of_panic,
            );
            return Err(error);
        }
        // ... or it logged any errors
        else if log_messages_in_case_of_panic
            .iter()
            .any(|(severity, _)| *severity == Severity::Error)
        {
            insert_log_messages_in_build_outputs(
                build_script_outputs,
                id,
                metadata_hash,
                log_messages_in_case_of_panic,
            );
            anyhow::bail!("build script logged errors");
        }

        let output = output.unwrap();

        // After the build command has finished running, we need to be sure to
        // remember all of its output so we can later discover precisely what it
        // was, even if we don't run the build command again (due to freshness).
        //
        // This is also the location where we provide feedback into the build
        // state informing what variables were discovered via our script as
        // well.
        if output_integrity.is_some() {
            write_atomic(&run_files.stdout, &output.stdout)?;
        } else {
            paths::write(&run_files.stdout, &output.stdout)?;
        }
        // This mtime shift allows Cargo to detect if a source file was
        // modified in the middle of the build.
        paths::set_file_time_no_err(&run_files.stdout, timestamp);
        let root_output = paths::path2bytes(&script_out_dir)?;
        if output_integrity.is_some() {
            write_atomic(&run_files.stderr, &output.stderr)?;
            write_atomic(&run_files.root_output, &root_output)?;
        } else {
            paths::write(&run_files.stderr, &output.stderr)?;
            paths::write(&run_files.root_output, &root_output)?;
            // Trust: EW-9, see `relocation_record`. Verified output is never
            // re-rooted, so it keeps no record.
            match &relocation_record {
                Some(record) => paths::write(&run_files.root_relocation, record)?,
                None if run_files.root_relocation.exists() => {
                    paths::remove_file(&run_files.root_relocation)?
                }
                None => {}
            }
        }
        let parsed_output = BuildOutput::parse(
            &output.stdout,
            library_name,
            &pkg_descr,
            &script_out_dir,
            &script_out_dir,
            nightly_features_allowed,
            &targets,
            &msrv,
        )?;
        // Trust: record original process bytes only after both execution and
        // directive parsing succeeded. Never hash a later disk replacement.
        if let Some(integrity) = &output_integrity {
            if let Err(error) = integrity.publish(&output.stdout, &root_output) {
                tracing::debug!(%error, "build-script output is not cacheable");
                integrity.invalidate()?;
            }
        }

        if json_messages {
            emit_build_output(state, &parsed_output, script_out_dir.as_path(), id)?;
        }
        build_script_outputs
            .lock()
            .unwrap()
            .insert(id, metadata_hash, parsed_output);
        Ok(())
    });

    // Now that we've prepared our work-to-do, we need to prepare the fresh work
    // itself to run when we actually end up just discarding what we calculated
    // above.
    let fresh = Work::new(move |state| {
        let (
            id,
            library_name,
            pkg_descr,
            build_script_outputs,
            output_file,
            script_out_dir,
            output_integrity,
            expected_receipt,
        ) = all;
        let output = match prev_output {
            Some(output) => output,
            None if output_integrity.is_some() => {
                let expected = expected_receipt
                    .as_ref()
                    .context("no verified build-script planning receipt")?;
                let (stdout, root_output) =
                    output_integrity.as_ref().unwrap().read_matching(expected)?;
                let generated_dir = paths::bytes2path(&root_output)?;
                BuildOutput::parse(
                    &stdout,
                    library_name,
                    &pkg_descr,
                    &generated_dir,
                    &script_out_dir,
                    nightly_features_allowed,
                    &targets_fresh,
                    &msrv_fresh,
                )?
            }
            None => BuildOutput::parse_file(
                &output_file,
                library_name,
                &pkg_descr,
                &prev_script_out_dir,
                &script_out_dir,
                nightly_features_allowed,
                &targets_fresh,
                &msrv_fresh,
                prev_relocation.as_ref(),
            )?,
        };

        if json_messages {
            emit_build_output(state, &output, script_out_dir.as_path(), id)?;
        }

        build_script_outputs
            .lock()
            .unwrap()
            .insert(id, metadata_hash, output);
        Ok(())
    });

    let mut job = fingerprint::prepare_build_script(build_runner, unit, dirty)?;
    if job.freshness().is_fresh() {
        job.before(fresh);
    }
    Ok(job)
}

/// When a build script run fails, store only log messages, and nuke other
/// outputs, as they are likely broken.
fn insert_log_messages_in_build_outputs(
    build_script_outputs: Arc<Mutex<BuildScriptOutputs>>,
    id: PackageId,
    metadata_hash: UnitHash,
    log_messages: Vec<LogMessage>,
) {
    let build_output_with_only_log_messages = BuildOutput {
        log_messages,
        ..BuildOutput::default()
    };
    build_script_outputs.lock().unwrap().insert(
        id,
        metadata_hash,
        build_output_with_only_log_messages,
    );
}

impl BuildOutput {
    /// Like [`BuildOutput::parse_relocated`] but from a file path.
    pub fn parse_file(
        path: &Path,
        library_name: Option<String>,
        pkg_descr: &str,
        script_out_dir_when_generated: &Path,
        script_out_dir: &Path,
        nightly_features_allowed: bool,
        targets: &[Target],
        msrv: &Option<RustVersion>,
        // Trust: EW-9 re-rooting of output recorded in another tree.
        relocation: Option<&OutputRelocation>,
    ) -> CargoResult<BuildOutput> {
        let contents = paths::read_bytes(path)?;
        BuildOutput::parse_relocated(
            &contents,
            library_name,
            pkg_descr,
            script_out_dir_when_generated,
            script_out_dir,
            nightly_features_allowed,
            targets,
            msrv,
            relocation,
        )
    }

    /// Parses the output instructions of a build script.
    ///
    /// * `pkg_descr` --- for error messages
    /// * `library_name` --- for determining if `RUSTC_BOOTSTRAP` should be allowed
    pub fn parse(
        input: &[u8],
        // Takes String instead of InternedString so passing `unit.pkg.name()` will give a compile error.
        library_name: Option<String>,
        pkg_descr: &str,
        script_out_dir_when_generated: &Path,
        script_out_dir: &Path,
        nightly_features_allowed: bool,
        targets: &[Target],
        msrv: &Option<RustVersion>,
    ) -> CargoResult<BuildOutput> {
        BuildOutput::parse_relocated(
            input,
            library_name,
            pkg_descr,
            script_out_dir_when_generated,
            script_out_dir,
            nightly_features_allowed,
            targets,
            msrv,
            None,
        )
    }

    /// [`BuildOutput::parse`] of output recorded in another tree.
    ///
    /// Trust: EW-9. With `relocation`, every directive value is re-rooted from
    /// the recording tree's `-Ztrust-relocation-roots` to the current ones, in
    /// the same pass that re-roots the old `OUT_DIR`; an old root that cannot
    /// be re-rooted fails the parse, so the output is not replayed. Without it
    /// this is exactly [`BuildOutput::parse`].
    pub fn parse_relocated(
        input: &[u8],
        library_name: Option<String>,
        pkg_descr: &str,
        script_out_dir_when_generated: &Path,
        script_out_dir: &Path,
        nightly_features_allowed: bool,
        targets: &[Target],
        msrv: &Option<RustVersion>,
        relocation: Option<&OutputRelocation>,
    ) -> CargoResult<BuildOutput> {
        let mut library_paths = Vec::new();
        let mut library_links = Vec::new();
        let mut linker_args = Vec::new();
        let mut cfgs = Vec::new();
        let mut check_cfgs = Vec::new();
        let mut env = Vec::new();
        let mut metadata = Vec::new();
        let mut rerun_if_changed = Vec::new();
        let mut rerun_if_env_changed = Vec::new();
        let mut log_messages = Vec::new();
        let whence = format!("build script of `{}`", pkg_descr);
        // Old syntax:
        //    cargo:rustc-flags=VALUE
        //    cargo:KEY=VALUE (for other unreserved keys)
        // New syntax:
        //    cargo::rustc-flags=VALUE
        //    cargo::metadata=KEY=VALUE (for other unreserved keys)
        // Due to backwards compatibility, no new keys can be added to this old format.
        const RESERVED_PREFIXES: &[&str] = &[
            "rustc-flags=",
            "rustc-link-lib=",
            "rustc-link-search=",
            "rustc-link-arg-cdylib=",
            "rustc-cdylib-link-arg=",
            "rustc-link-arg-bins=",
            "rustc-link-arg-bin=",
            "rustc-link-arg-tests=",
            "rustc-link-arg-benches=",
            "rustc-link-arg-examples=",
            "rustc-link-arg=",
            "rustc-cfg=",
            "rustc-check-cfg=",
            "rustc-env=",
            "warning=",
            "rerun-if-changed=",
            "rerun-if-env-changed=",
        ];
        const DOCS_LINK_SUGGESTION: &str = "See https://doc.rust-lang.org/cargo/reference/build-scripts.html#outputs-of-the-build-script \
                for more information about build script outputs.";

        fn has_reserved_prefix(flag: &str) -> bool {
            RESERVED_PREFIXES
                .iter()
                .any(|reserved_prefix| flag.starts_with(reserved_prefix))
        }

        fn check_minimum_supported_rust_version_for_new_syntax(
            pkg_descr: &str,
            msrv: &Option<RustVersion>,
            flag: &str,
        ) -> CargoResult<()> {
            if let Some(msrv) = msrv {
                let new_syntax_added_in = RustVersion::new(1, 77, 0);
                if !new_syntax_added_in.is_compatible_with(&msrv.to_partial()) {
                    let old_syntax_suggestion = if has_reserved_prefix(flag) {
                        format!(
                            "Switch to the old `cargo:{flag}` syntax (note the single colon).\n"
                        )
                    } else if flag.starts_with("metadata=") {
                        let old_format_flag = flag.strip_prefix("metadata=").unwrap();
                        format!(
                            "Switch to the old `cargo:{old_format_flag}` syntax instead of `cargo::{flag}` (note the single colon).\n"
                        )
                    } else {
                        String::new()
                    };

                    bail!(
                        "the `cargo::` syntax for build script output instructions was added in \
                        Rust 1.77.0, but the minimum supported Rust version of `{pkg_descr}` is {msrv}.\n\
                        {old_syntax_suggestion}\
                        {DOCS_LINK_SUGGESTION}"
                    );
                }
            }

            Ok(())
        }

        fn parse_directive<'a>(
            whence: &str,
            line: &str,
            data: &'a str,
            old_syntax: bool,
        ) -> CargoResult<(&'a str, &'a str)> {
            let mut iter = data.splitn(2, "=");
            let key = iter.next();
            let value = iter.next();
            match (key, value) {
                (Some(a), Some(b)) => Ok((a, b.trim_end())),
                _ => bail!(
                    "invalid output in {whence}: `{line}`\n\
                    Expected a line with `{syntax}KEY=VALUE` with an `=` character, \
                    but none was found.\n\
                    {DOCS_LINK_SUGGESTION}",
                    syntax = if old_syntax { "cargo:" } else { "cargo::" },
                ),
            }
        }

        fn parse_metadata<'a>(
            whence: &str,
            line: &str,
            data: &'a str,
            old_syntax: bool,
        ) -> CargoResult<(&'a str, &'a str)> {
            let mut iter = data.splitn(2, "=");
            let key = iter.next();
            let value = iter.next();
            match (key, value) {
                (Some(a), Some(b)) => Ok((a, b.trim_end())),
                _ => bail!(
                    "invalid output in {whence}: `{line}`\n\
                    Expected a line with `{syntax}KEY=VALUE` with an `=` character, \
                    but none was found.\n\
                    {DOCS_LINK_SUGGESTION}",
                    syntax = if old_syntax {
                        "cargo:"
                    } else {
                        "cargo::metadata="
                    },
                ),
            }
        }

        for line in input.split(|b| *b == b'\n') {
            let line = match str::from_utf8(line) {
                Ok(line) => line.trim(),
                Err(..) => continue,
            };
            let mut old_syntax = false;
            // Trust: accept the canonical `targo::`/`targo:` build-script
            // directive spelling as an exact synonym for `cargo::`/`cargo:`, so
            // Trust's own build scripts speak targo while foreign crates.io
            // build scripts keep emitting cargo:. Both parse identically.
            let (key, value) = if let Some(data) = line
                .strip_prefix("cargo::")
                .or_else(|| line.strip_prefix("targo::"))
            {
                check_minimum_supported_rust_version_for_new_syntax(pkg_descr, msrv, data)?;
                // For instance, `cargo::rustc-flags=foo` or `cargo::metadata=foo=bar`.
                parse_directive(whence.as_str(), line, data, old_syntax)?
            } else if let Some(data) = line
                .strip_prefix("cargo:")
                .or_else(|| line.strip_prefix("targo:"))
            {
                old_syntax = true;
                // For instance, `cargo:rustc-flags=foo`.
                if has_reserved_prefix(data) {
                    parse_directive(whence.as_str(), line, data, old_syntax)?
                } else {
                    // For instance, `cargo:foo=bar`.
                    ("metadata", data)
                }
            } else {
                // Skip lines outside the native or compatibility protocols.
                continue;
            };
            // This will rewrite paths if the target directory has been moved.
            let out_dir = (
                script_out_dir_when_generated.to_str().unwrap(),
                script_out_dir.to_str().unwrap(),
            );
            let value = match relocation {
                None => value.replace(out_dir.0, out_dir.1),
                // Trust: EW-9, see `parse_relocated`.
                Some(relocation) => relocation
                    .relocate(value, out_dir)
                    .with_context(|| format!("cannot replay the output of the {whence}"))?
                    .into_owned(),
            };

            let syntax_prefix = if old_syntax { "cargo:" } else { "cargo::" };
            macro_rules! check_and_add_target {
                ($target_kind: expr, $is_target_kind: expr, $link_type: expr) => {
                    if !targets.iter().any(|target| $is_target_kind(target)) {
                        bail!(
                            "invalid instruction `{}{}` from {}\n\
                                The package {} does not have a {} target.",
                            syntax_prefix,
                            key,
                            whence,
                            pkg_descr,
                            $target_kind
                        );
                    }
                    linker_args.push(($link_type, value));
                };
            }

            // Keep in sync with TargetConfig::parse_links_overrides.
            match key {
                "rustc-flags" => {
                    let (paths, links) = BuildOutput::parse_rustc_flags(&value, &whence)?;
                    library_links.extend(links.into_iter());
                    library_paths.extend(
                        paths
                            .into_iter()
                            .map(|p| LibraryPath::new(p, script_out_dir)),
                    );
                }
                "rustc-link-lib" => library_links.push(value.to_string()),
                "rustc-link-search" => {
                    library_paths.push(LibraryPath::new(PathBuf::from(value), script_out_dir))
                }
                "rustc-link-arg-cdylib" | "rustc-cdylib-link-arg" => {
                    if !targets.iter().any(|target| target.is_cdylib()) {
                        log_messages.push((
                            Severity::Warning,
                            format!(
                                "{}{} was specified in the build script of {}, \
                             but that package does not contain a cdylib target\n\
                             \n\
                             Allowing this was an unintended change in the 1.50 \
                             release, and may become an error in the future. \
                             For more information, see \
                             <https://github.com/rust-lang/cargo/issues/9562>.",
                                syntax_prefix, key, pkg_descr
                            ),
                        ));
                    }
                    linker_args.push((LinkArgTarget::Cdylib, value))
                }
                "rustc-link-arg-bins" => {
                    check_and_add_target!("bin", Target::is_bin, LinkArgTarget::Bin);
                }
                "rustc-link-arg-bin" => {
                    let (bin_name, arg) = value.split_once('=').ok_or_else(|| {
                        anyhow::format_err!(
                            "invalid instruction `{}{}={}` from {}\n\
                                The instruction should have the form {}{}=BIN=ARG",
                            syntax_prefix,
                            key,
                            value,
                            whence,
                            syntax_prefix,
                            key
                        )
                    })?;
                    if !targets
                        .iter()
                        .any(|target| target.is_bin() && target.name() == bin_name)
                    {
                        bail!(
                            "invalid instruction `{}{}` from {}\n\
                                The package {} does not have a bin target with the name `{}`.",
                            syntax_prefix,
                            key,
                            whence,
                            pkg_descr,
                            bin_name
                        );
                    }
                    linker_args.push((
                        LinkArgTarget::SingleBin(bin_name.to_owned()),
                        arg.to_string(),
                    ));
                }
                "rustc-link-arg-tests" => {
                    check_and_add_target!("test", Target::is_test, LinkArgTarget::Test);
                }
                "rustc-link-arg-benches" => {
                    check_and_add_target!("benchmark", Target::is_bench, LinkArgTarget::Bench);
                }
                "rustc-link-arg-examples" => {
                    check_and_add_target!("example", Target::is_example, LinkArgTarget::Example);
                }
                "rustc-link-arg" => {
                    linker_args.push((LinkArgTarget::All, value));
                }
                "rustc-cfg" => cfgs.push(value.to_string()),
                "rustc-check-cfg" => check_cfgs.push(value.to_string()),
                "rustc-env" => {
                    let (key, val) = BuildOutput::parse_rustc_env(&value, &whence)?;
                    // Build scripts aren't allowed to set RUSTC_BOOTSTRAP.
                    // See https://github.com/rust-lang/cargo/issues/7088.
                    if key == "RUSTC_BOOTSTRAP" {
                        // If RUSTC_BOOTSTRAP is already set, the user of Cargo knows about
                        // bootstrap and still wants to override the channel. Give them a way to do
                        // so, but still emit a warning that the current crate shouldn't be trying
                        // to set RUSTC_BOOTSTRAP.
                        // If this is a nightly build, setting RUSTC_BOOTSTRAP wouldn't affect the
                        // behavior, so still only give a warning.
                        // NOTE: cargo only allows nightly features on RUSTC_BOOTSTRAP=1, but we
                        // want setting any value of RUSTC_BOOTSTRAP to downgrade this to a warning
                        // (so that `RUSTC_BOOTSTRAP=library_name` will work)
                        let rustc_bootstrap_allows = |name: Option<&str>| {
                            let name = match name {
                                // as of 2021, no binaries on crates.io use RUSTC_BOOTSTRAP, so
                                // fine-grained opt-outs aren't needed. end-users can always use
                                // RUSTC_BOOTSTRAP=1 from the top-level if it's really a problem.
                                None => return false,
                                Some(n) => n,
                            };
                            #[expect(
                                clippy::disallowed_methods,
                                reason = "consistency with rustc, not specified behavior"
                            )]
                            std::env::var("RUSTC_BOOTSTRAP")
                                .map_or(false, |var| var.split(',').any(|s| s == name))
                        };
                        if nightly_features_allowed
                            || rustc_bootstrap_allows(library_name.as_deref())
                        {
                            log_messages.push((Severity::Warning, format!("cannot set `RUSTC_BOOTSTRAP={}` from {}.\n\
                                note: crates cannot set `RUSTC_BOOTSTRAP` themselves, as doing so would subvert the stability guarantees of Rust for your project.",
                                val, whence
                            )));
                        } else {
                            // Setting RUSTC_BOOTSTRAP would change the behavior of the crate.
                            // Abort with an error.
                            bail!(
                                "cannot set `RUSTC_BOOTSTRAP={}` from {}.\n\
                                note: crates cannot set `RUSTC_BOOTSTRAP` themselves, as doing so would subvert the stability guarantees of Rust for your project.\n\
                                help: If you're sure you want to do this in your project, set the environment variable `RUSTC_BOOTSTRAP={}` before running cargo instead.",
                                val,
                                whence,
                                library_name.as_deref().unwrap_or("1"),
                            );
                        }
                    } else {
                        env.push((key, val));
                    }
                }
                "error" => log_messages.push((Severity::Error, value.to_string())),
                "warning" => log_messages.push((Severity::Warning, value.to_string())),
                "rerun-if-changed" => rerun_if_changed.push(PathBuf::from(value)),
                "rerun-if-env-changed" => rerun_if_env_changed.push(value.to_string()),
                "metadata" => {
                    let (key, value) = parse_metadata(whence.as_str(), line, &value, old_syntax)?;
                    metadata.push((key.to_owned(), value.to_owned()));
                }
                _ => bail!(
                    "invalid output in {whence}: `{line}`\n\
                    Unknown key: `{key}`.\n\
                    {DOCS_LINK_SUGGESTION}",
                ),
            }
        }

        Ok(BuildOutput {
            library_paths,
            library_links,
            linker_args,
            cfgs,
            check_cfgs,
            env,
            metadata,
            rerun_if_changed,
            rerun_if_env_changed,
            log_messages,
        })
    }

    /// Parses [`cargo::rustc-flags`] instruction.
    ///
    /// [`cargo::rustc-flags`]: https://doc.rust-lang.org/nightly/cargo/reference/build-scripts.html#cargorustc-flagsflags
    pub fn parse_rustc_flags(
        value: &str,
        whence: &str,
    ) -> CargoResult<(Vec<PathBuf>, Vec<String>)> {
        let value = value.trim();
        let mut flags_iter = value
            .split(|c: char| c.is_whitespace())
            .filter(|w| w.chars().any(|c| !c.is_whitespace()));
        let (mut library_paths, mut library_links) = (Vec::new(), Vec::new());

        while let Some(flag) = flags_iter.next() {
            if flag.starts_with("-l") || flag.starts_with("-L") {
                // Check if this flag has no space before the value as is
                // common with tools like pkg-config
                // e.g. -L/some/dir/local/lib or -licui18n
                let (flag, mut value) = flag.split_at(2);
                if value.is_empty() {
                    value = match flags_iter.next() {
                        Some(v) => v,
                        None => bail! {
                            "flag in rustc-flags has no value in {}: {}",
                            whence,
                            value
                        },
                    }
                }

                match flag {
                    "-l" => library_links.push(value.to_string()),
                    "-L" => library_paths.push(PathBuf::from(value)),

                    // This was already checked above
                    _ => unreachable!(),
                };
            } else {
                bail!(
                    "only `-l` and `-L` flags are allowed in {}: `{}`",
                    whence,
                    value
                )
            }
        }
        Ok((library_paths, library_links))
    }

    /// Parses [`cargo::rustc-env`] instruction.
    ///
    /// [`cargo::rustc-env`]: https://doc.rust-lang.org/nightly/cargo/reference/build-scripts.html#rustc-env
    pub fn parse_rustc_env(value: &str, whence: &str) -> CargoResult<(String, String)> {
        match value.split_once('=') {
            Some((n, v)) => Ok((n.to_owned(), v.to_owned())),
            _ => bail!("Variable rustc-env has no value in {whence}: {value}"),
        }
    }
}

/// Prepares the Rust script for the unstable feature [metabuild].
///
/// [metabuild]: https://doc.rust-lang.org/nightly/cargo/reference/unstable.html#metabuild
fn prepare_metabuild(
    build_runner: &BuildRunner<'_, '_>,
    unit: &Unit,
    deps: &[String],
) -> CargoResult<()> {
    let mut output = Vec::new();
    let available_deps = build_runner.unit_deps(unit);
    // Filter out optional dependencies, and look up the actual lib name.
    let meta_deps: Vec<_> = deps
        .iter()
        .filter_map(|name| {
            available_deps
                .iter()
                .find(|d| d.unit.pkg.name().as_str() == name.as_str())
                .map(|d| d.unit.target.crate_name())
        })
        .collect();
    output.push("fn main() {\n".to_string());
    for dep in &meta_deps {
        output.push(format!("    {}::metabuild();\n", dep));
    }
    output.push("}\n".to_string());
    let output = output.join("");
    let path = unit
        .pkg
        .manifest()
        .metabuild_path(build_runner.bcx.ws.build_dir());
    paths::create_dir_all(path.parent().unwrap())?;
    paths::write_if_changed(path, &output)?;
    Ok(())
}

impl BuildDeps {
    /// Creates a build script dependency information from a previous
    /// build script output path and the content.
    pub fn new(output_file: &Path, output: Option<&BuildOutput>) -> BuildDeps {
        BuildDeps {
            build_script_output: output_file.to_path_buf(),
            rerun_if_changed: output
                .map(|p| &p.rerun_if_changed)
                .cloned()
                .unwrap_or_default(),
            rerun_if_env_changed: output
                .map(|p| &p.rerun_if_env_changed)
                .cloned()
                .unwrap_or_default(),
            cached_receipt: None,
            manifest_env_overrides: output.map(|output| {
                output
                    .env
                    .iter()
                    .filter(|(key, _)| crate::workspace::manifest::is_tracked_manifest_env(key))
                    .cloned()
                    .collect()
            }),
            compiler_cfg_args: output.map(|output| {
                output
                    .cfgs
                    .iter()
                    .chain(&output.check_cfgs)
                    .cloned()
                    .collect()
            }),
            command_output: output.cloned(),
            relocation_refused: false,
        }
    }

    /// Trust: freshness may inspect only the original receipt-bound operands.
    /// Missing controls still make the script dependency dirty; the compiler's
    /// exec-edge output guard handles a first run's newly discovered operands.
    pub(super) fn receipt_bound_cfg_args(&self) -> Option<&[String]> {
        if self.relocation_refused || self.cached_receipt.is_none() {
            return None;
        }
        self.compiler_cfg_args.as_deref()
    }
}

/// Computes several maps in [`BuildRunner`].
///
/// - [`build_scripts`]: A map that tracks which build scripts each package
///   depends on.
/// - [`build_explicit_deps`]: Dependency statements emitted by build scripts
///   from a previous run.
/// - [`build_script_outputs`]: Pre-populates this with any overridden build
///   scripts.
///
/// The important one here is [`build_scripts`], which for each `(package,
/// metadata)` stores a [`BuildScripts`] object which contains a list of
/// dependencies with build scripts that the unit should consider when linking.
/// For example this lists all dependencies' `-L` flags which need to be
/// propagated transitively.
///
/// The given set of units to this function is the initial set of
/// targets/profiles which are being built.
///
/// [`build_scripts`]: BuildRunner::build_scripts
/// [`build_explicit_deps`]: BuildRunner::build_explicit_deps
/// [`build_script_outputs`]: BuildRunner::build_script_outputs
pub fn build_map(build_runner: &mut BuildRunner<'_, '_>) -> CargoResult<()> {
    let mut ret = HashMap::default();
    for unit in &build_runner.bcx.roots {
        build(&mut ret, build_runner, unit)?;
    }
    build_runner
        .build_scripts
        .extend(ret.into_iter().map(|(k, v)| (k, Arc::new(v))));
    return Ok(());

    // Recursive function to build up the map we're constructing. This function
    // memoizes all of its return values as it goes along.
    fn build<'a>(
        out: &'a mut HashMap<Unit, BuildScripts>,
        build_runner: &mut BuildRunner<'_, '_>,
        unit: &Unit,
    ) -> CargoResult<&'a BuildScripts> {
        // Do a quick pre-flight check to see if we've already calculated the
        // set of dependencies.
        if out.contains_key(unit) {
            return Ok(&out[unit]);
        }

        // If there is a build script override, pre-fill the build output.
        if unit.mode.is_run_custom_build() {
            if let Some(links) = unit.pkg.manifest().links() {
                if let Some(output) = unit.links_overrides.get(links) {
                    let metadata = build_runner.get_run_build_script_metadata(unit);
                    build_runner.build_script_outputs.lock().unwrap().insert(
                        unit.pkg.package_id(),
                        metadata,
                        output.clone(),
                    );
                }
            }
        }

        let mut ret = BuildScripts::default();

        // If a package has a build script, add itself as something to inspect for linking.
        if !unit.target.is_custom_build() && unit.pkg.has_custom_build() {
            let script_metas = build_runner
                .find_build_script_metadatas(unit)
                .expect("has_custom_build should have RunCustomBuild");
            for script_meta in script_metas {
                add_to_link(&mut ret, unit.pkg.package_id(), script_meta);
            }
        }

        if unit.mode.is_run_custom_build() {
            parse_previous_explicit_deps(build_runner, unit);
        }

        // We want to invoke the compiler deterministically to be cache-friendly
        // to rustc invocation caching schemes, so be sure to generate the same
        // set of build script dependency orderings via sorting the targets that
        // come out of the `Context`.
        let mut dependencies: Vec<Unit> = build_runner
            .unit_deps(unit)
            .iter()
            .map(|d| d.unit.clone())
            .collect();
        dependencies.sort_by_key(|u| u.pkg.package_id());

        for dep_unit in dependencies.iter() {
            let dep_scripts = build(out, build_runner, dep_unit)?;

            if dep_unit.target.for_host() {
                ret.plugins.extend(dep_scripts.to_link.iter().cloned());
            } else if dep_unit.target.is_linkable() {
                for &(pkg, metadata) in dep_scripts.to_link.iter() {
                    add_to_link(&mut ret, pkg, metadata);
                }
            }
        }

        match out.entry(unit.clone()) {
            Entry::Vacant(entry) => Ok(entry.insert(ret)),
            Entry::Occupied(_) => panic!("cyclic dependencies in `build_map`"),
        }
    }

    // When adding an entry to 'to_link' we only actually push it on if the
    // script hasn't seen it yet (e.g., we don't push on duplicates).
    fn add_to_link(scripts: &mut BuildScripts, pkg: PackageId, metadata: UnitHash) {
        if scripts.seen_to_link.insert((pkg, metadata)) {
            scripts.to_link.push((pkg, metadata));
        }
    }

    /// Load any dependency declarations from a previous build script run.
    fn parse_previous_explicit_deps(build_runner: &mut BuildRunner<'_, '_>, unit: &Unit) {
        let run_files = BuildScriptRunFiles::for_unit(build_runner, unit);
        let (prev_output, _, receipt, relocation_refused) = prev_build_output(build_runner, unit);
        let mut deps = BuildDeps::new(&run_files.stdout, prev_output.as_ref());
        deps.cached_receipt = receipt;
        deps.relocation_refused = relocation_refused;
        build_runner.build_explicit_deps.insert(unit.clone(), deps);
    }
}

/// Returns the previous parsed `BuildOutput`, if any, from a previous
/// execution.
///
/// Also returns the directory containing the output, typically used later in
/// processing, and the exact receipt key used for dependency planning. Trust:
/// generated-file admission remains at the final fingerprint freshness gate.
/// The last element is true when output recorded under other EW-9 relocation
/// roots could not be re-rooted (see [`BuildDeps::relocation_refused`]).
fn prev_build_output(
    build_runner: &mut BuildRunner<'_, '_>,
    unit: &Unit,
) -> (Option<BuildOutput>, PathBuf, Option<ReceiptKey>, bool) {
    let script_out_dir = script_out_dir(build_runner, unit);
    let run_files = BuildScriptRunFiles::for_unit(build_runner, unit);

    // Trust: verify bounded bytes before parsing any cached directives or
    // relocation data. Parse those same buffers, without reopening a pathname.
    if crate::is_targo_invocation() {
        let parsed = (|| -> CargoResult<_> {
            let (stdout, root_output, key) = cached_output(build_runner, unit)
                .read_controls()?
                .into_parts();
            let generated_dir = paths::bytes2path(&root_output)?;
            let output = BuildOutput::parse(
                &stdout,
                unit.pkg.library().map(|target| target.crate_name()),
                &unit.pkg.to_string(),
                &generated_dir,
                &script_out_dir,
                build_runner.bcx.gctx.nightly_features_allowed,
                unit.pkg.targets(),
                &unit.pkg.rust_version().cloned(),
            )?;
            Ok((output, generated_dir, key))
        })();
        // Trust: verified output carries no EW-9 relocation record; it is
        // replayed as recorded.
        return match parsed {
            Ok((output, generated_dir, key)) => (Some(output), generated_dir, Some(key), false),
            Err(error) => {
                tracing::debug!(%error,"cached build-script output is unavailable");
                (None, script_out_dir, None, false)
            }
        };
    }

    let prev_script_out_dir = paths::read_bytes(&run_files.root_output)
        .and_then(|bytes| paths::bytes2path(&bytes))
        .unwrap_or_else(|_| script_out_dir.clone());
    let Ok(relocation) = output_relocation(build_runner, &run_files) else {
        tracing::debug!("build-script output beside an unusable relocation record");
        return (None, prev_script_out_dir, None, true);
    };

    let output = BuildOutput::parse_file(
        &run_files.stdout,
        unit.pkg.library().map(|t| t.crate_name()),
        &unit.pkg.to_string(),
        &prev_script_out_dir,
        &script_out_dir,
        build_runner.bcx.gctx.nightly_features_allowed,
        unit.pkg.targets(),
        &unit.pkg.rust_version().cloned(),
        relocation.as_ref(),
    );
    let relocation_refused = relocation.is_some() && output.is_err();
    if relocation_refused && let Err(error) = &output {
        tracing::debug!(%error, "relocated build-script output is not replayable");
    }
    (output.ok(), prev_script_out_dir, None, relocation_refused)
}

/// Trust: EW-9. How to replay a unit's cached output here: a relocation only
/// when `-Ztrust-relocation-roots` is in effect and the run that wrote the
/// output recorded a different set of the same number of roots beside it;
/// `Err` (the script runs again) when the record beside it is malformed or
/// names another number of roots. Without the flag or a record, the output
/// is replayed exactly as without the flag.
fn output_relocation(
    build_runner: &BuildRunner<'_, '_>,
    run_files: &BuildScriptRunFiles,
) -> Result<Option<OutputRelocation>, ()> {
    let Some(roots) = build_runner
        .bcx
        .gctx
        .cli_unstable()
        .trust_relocation_roots
        .as_ref()
    else {
        return Ok(None);
    };
    let Ok(record) = paths::read_bytes(&run_files.root_relocation) else {
        return Ok(None);
    };
    roots.relocation_from(&record)
}

impl BuildScriptOutputs {
    /// Inserts a new entry into the map.
    fn insert(&mut self, pkg_id: PackageId, metadata: UnitHash, parsed_output: BuildOutput) {
        match self.outputs.entry(metadata) {
            Entry::Vacant(entry) => {
                entry.insert(parsed_output);
            }
            Entry::Occupied(entry) => panic!(
                "build script output collision for {}/{}\n\
                old={:?}\nnew={:?}",
                pkg_id,
                metadata,
                entry.get(),
                parsed_output
            ),
        }
    }

    /// Returns `true` if the given key already exists.
    fn contains_key(&self, metadata: UnitHash) -> bool {
        self.outputs.contains_key(&metadata)
    }

    /// Gets the build output for the given key.
    pub fn get(&self, meta: UnitHash) -> Option<&BuildOutput> {
        self.outputs.get(&meta)
    }

    /// Returns an iterator over all entries.
    pub fn iter(&self) -> impl Iterator<Item = (&UnitHash, &BuildOutput)> {
        self.outputs.iter()
    }
}

/// Trust: reconstruct only the overlays required by one ordinary command.
/// Prefer the runner's actual current outputs (including explicit overrides).
/// Otherwise revalidate the exact planning receipt before using the originally
/// parsed data. Script input/dependency freshness remains a separate mandatory
/// gate; this snapshot cannot admit a stale script or update its runtime map.
pub(super) fn planning_command_outputs(
    build_runner: &BuildRunner<'_, '_>,
    required: &[UnitHash],
) -> CargoResult<BuildScriptOutputs> {
    let mut outputs = BuildScriptOutputs::default();
    {
        let live = build_runner.build_script_outputs.lock().unwrap();
        for &metadata in required {
            if let Some(output) = live.get(metadata) {
                outputs.outputs.insert(metadata, output.clone());
            }
        }
    }
    for &metadata in required {
        if outputs.contains_key(metadata) {
            continue;
        }
        let mut matches = build_runner.build_explicit_deps.iter().filter(|(unit, _)| {
            unit.mode.is_run_custom_build()
                && build_runner.get_run_build_script_metadata(unit) == metadata
        });
        let (unit, deps) = matches
            .next()
            .context("build-script planning output is missing")?;
        anyhow::ensure!(
            matches.next().is_none(),
            "ambiguous build-script planning output"
        );
        anyhow::ensure!(
            !deps.relocation_refused,
            "build-script relocation was refused"
        );
        let key = deps
            .cached_receipt
            .as_ref()
            .context("build-script planning receipt is missing")?;
        let output = deps
            .command_output
            .as_ref()
            .context("parsed build-script planning output is missing")?;
        cached_output(build_runner, unit).read_matching(key)?;
        outputs.outputs.insert(metadata, output.clone());
    }
    Ok(outputs)
}

/// Trust (DC-18c): the file that holds what a build-script run printed, its
/// directives, as Targo reads them for its dependents' commands.
pub(crate) fn script_stdout(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> PathBuf {
    BuildScriptRunFiles::for_unit(build_runner, unit).stdout
}

/// The `OUT_DIR` a run of a build script writes, in the build directory's
/// layout: what the script is told, what its outputs are cached from, and
/// what a shared member that runs it is keyed on (DC-18c).
pub(crate) fn script_out_dir(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> PathBuf {
    if build_runner.bcx.gctx.cli_unstable().build_dir_new_layout {
        build_runner.files().out_dir_new_layout(unit)
    } else {
        build_runner.files().build_script_out_dir(unit)
    }
}

/// Files with information about a running build script.
struct BuildScriptRunFiles {
    /// The directory containing files related to running a build script.
    root: PathBuf,
    /// The stdout produced by the build script
    stdout: PathBuf,
    /// The stderr produced by the build script
    stderr: PathBuf,
    /// A file that contains the path to the `out` dir of the build script.
    /// This is used for detect if the directory was moved since the previous run.
    root_output: PathBuf,
    /// Trust: EW-9. The `-Ztrust-relocation-roots` in effect when the build
    /// script last ran, so its output can be re-rooted in a relocated tree.
    root_relocation: PathBuf,
}

// Trust: the unit and inventory come from the compiler's actual build graph,
// never paths or keys supplied by a receipt being decoded.
pub(super) fn cached_output(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> CachedOutput {
    let files = BuildScriptRunFiles::for_unit(build_runner, unit);
    let generated = script_out_dir(build_runner, unit);
    CachedOutput::new(
        &files.root,
        build_runner.get_run_build_script_metadata(unit).to_string(),
        &files.stdout,
        &files.root_output,
        &generated,
    )
}

impl BuildScriptRunFiles {
    pub fn for_unit(build_runner: &BuildRunner<'_, '_>, unit: &Unit) -> Self {
        let root = build_runner.files().build_script_run_dir(unit);
        let stdout = if build_runner.bcx.gctx.cli_unstable().build_dir_new_layout {
            root.join("stdout")
        } else {
            root.join("output")
        };
        let stderr = root.join("stderr");
        let root_output = root.join("root-output");
        let root_relocation = root.join("root-relocation");
        Self {
            root,
            stdout,
            stderr,
            root_output,
            root_relocation,
        }
    }
}

// Trust: pins that the `targo:` directive spelling parses identically to
// `cargo:` and that neither prefix is privileged over the other, so a crate can
// be built by either frontend without changing its build script.
#[cfg(test)]
mod native_protocol_tests {
    use super::{BuildDeps, BuildOutput};

    #[test]
    fn compiler_cfg_planning_keeps_original_operands_bound_to_the_receipt() {
        let root = tempfile::tempdir().unwrap();
        let stdout_path = root.path().join("stdout");
        let root_output = root.path().join("root-output");
        let generated = root.path().join("out");
        std::fs::create_dir(&generated).unwrap();
        let stdout = b"cargo::rustc-cfg=literal=\"@embedded\"\n\
                       cargo::rustc-cfg=@missing-cfg.args\n\
                       cargo::rustc-check-cfg=@shell:missing-check.args\n\
                       cargo::rustc-env=PATH=/earlier/native\n\
                       cargo::rustc-env=PATH=/later/native\n";
        std::fs::write(&stdout_path, stdout).unwrap();
        std::fs::write(&root_output, b"original-root").unwrap();
        let output = BuildOutput::parse(
            stdout,
            None,
            "cfg-planning-fixture",
            &generated,
            &generated,
            false,
            &[],
            &None,
        )
        .unwrap();
        let planned = BuildDeps::new(&stdout_path, Some(&output));
        assert_eq!(planned.command_output.as_ref(), Some(&output));
        assert_eq!(
            planned.command_output.as_ref().unwrap().env,
            [
                ("PATH".into(), "/earlier/native".into()),
                ("PATH".into(), "/later/native".into())
            ]
        );
        assert!(BuildDeps::new(&stdout_path, None).command_output.is_none());
        let guard = super::CachedOutput::new(
            root.path(),
            "cfg-planning-fixture".into(),
            &stdout_path,
            &root_output,
            &generated,
        );
        guard.publish(stdout, b"original-root").unwrap();
        let (_, _, key) = guard.read_controls().unwrap().into_parts();

        assert!(
            BuildDeps::new(&stdout_path, None)
                .compiler_cfg_args
                .is_none()
        );
        assert_eq!(
            BuildDeps::new(&stdout_path, Some(&BuildOutput::default())).compiler_cfg_args,
            Some(Vec::new())
        );
        let mut deps = BuildDeps::new(&stdout_path, Some(&output));
        assert!(deps.receipt_bound_cfg_args().is_none());
        deps.cached_receipt = Some(key);
        assert_eq!(
            deps.receipt_bound_cfg_args().unwrap(),
            [
                "literal=\"@embedded\"",
                "@missing-cfg.args",
                "@shell:missing-check.args"
            ]
        );
        deps.relocation_refused = true;
        assert!(deps.receipt_bound_cfg_args().is_none());
    }

    #[test]
    fn manifest_environment_planning_preserves_unknown_empty_and_ordered_values() {
        let path = std::path::Path::new("output");
        assert!(BuildDeps::new(path, None).manifest_env_overrides.is_none());
        assert_eq!(
            BuildDeps::new(path, Some(&BuildOutput::default())).manifest_env_overrides,
            Some(Vec::new())
        );
        let env = vec![
            ("CARGO_MANIFEST_DIR".to_owned(), "first".to_owned()),
            ("UNRELATED".to_owned(), "ignored".to_owned()),
            ("CARGO_MANIFEST_DIR".to_owned(), "last".to_owned()),
            ("CARGO_MANIFEST_PATH".to_owned(), String::new()),
            ("CARGO_PKG_DESCRIPTION".to_owned(), "first".to_owned()),
            ("CARGO_PKG_DESCRIPTION".to_owned(), String::new()),
        ];
        let output = BuildOutput {
            env,
            ..BuildOutput::default()
        };
        assert_eq!(
            BuildDeps::new(path, Some(&output))
                .manifest_env_overrides
                .unwrap(),
            [
                output.env[0].clone(),
                output.env[2].clone(),
                output.env[3].clone(),
                output.env[4].clone(),
                output.env[5].clone()
            ]
        );
    }

    #[test]
    fn native_and_compat_build_script_directives_parse_identically() {
        let out_dir = tempfile::tempdir().unwrap();
        let output = BuildOutput::parse(
            b"targo::rustc-env=NATIVE_NEW=new\n\
              targo:rustc-env=NATIVE_OLD=old\n\
              cargo::rustc-env=COMPAT_NEW=compat-new\n\
              cargo:rustc-env=COMPAT_OLD=compat-old\n\
              not-a-directive=ignored\n",
            None,
            "native-protocol-fixture",
            out_dir.path(),
            out_dir.path(),
            false,
            &[],
            &None,
        )
        .unwrap();

        assert_eq!(
            output.env,
            [
                ("NATIVE_NEW".to_string(), "new".to_string()),
                ("NATIVE_OLD".to_string(), "old".to_string()),
                ("COMPAT_NEW".to_string(), "compat-new".to_string()),
                ("COMPAT_OLD".to_string(), "compat-old".to_string()),
            ]
        );
    }
}

#[cfg(test)]
mod trust_authority_tests {
    use super::*;
    use std::ffi::OsStr;

    fn flags(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| (*value).to_string()).collect()
    }

    /// `without_trust_controls` followed by Targo's one canonical off-switch,
    /// in the split spelling `trust_unit_protocol_args` uses.
    fn with_canonical_off_switch(mut without_trust_controls: Vec<String>) -> Vec<String> {
        without_trust_controls.extend(["-Z".to_string(), TRUST_VERIFY_OFF_OPTION.to_string()]);
        without_trust_controls
    }

    /// B5 step A. A build script's compiler probe runs `$RUSTC` (trustc in a
    /// verified session) with `CARGO_ENCODED_RUSTFLAGS`, and trustc's bare
    /// default verifies: measured on the installed trustc 321aaeda7, a probe
    /// `a / b` is refuted (exit 1) with the flags this view used to carry and
    /// compiles with `-Z trust-verify=off` appended. The view is therefore the
    /// unit's flags minus every Trust control, plus exactly one off-switch in
    /// Targo's own spelling, whatever the unit's role and whatever switch the
    /// unit's own flags carry: a primary unit (compiled with verification on,
    /// so no switch at all) and a dependency unit whose flags spell the switch
    /// both ways, in a non-canonical key spelling and with a later `on`.
    #[test]
    fn build_script_runtime_view_carries_one_canonical_off_switch() {
        let primary = flags(&[
            "--cfg",
            "fixture",
            "-Z",
            "trust-verify-session=session-1",
            "-Ztrust-proof-artifact-root=/tmp/private-proof-store",
            "-Ztrust-verify-crate-role=primary",
            "-Ztrust-policy=strict",
            "-Ztrust-verify-level=2",
            "-Copt-level=1",
        ]);
        let dependency = flags(&[
            "-Ztrust-verify-session=session-2",
            "-Z",
            "trust-proof-artifact-root=/tmp/private-proof-store",
            "-Ztrust-verify-crate-role=dependency",
            "-Ztrust_verify=off",
            "-Z",
            "trust-verify=on",
            "-Cpanic=abort",
        ]);
        for (role, original, without_trust_controls) in [
            (
                "primary",
                primary,
                flags(&["--cfg", "fixture", "-Copt-level=1"]),
            ),
            ("dependency", dependency, flags(&["-Cpanic=abort"])),
        ] {
            assert_eq!(
                build_script_rustflags_without_targo_authority(&original, true).unwrap(),
                with_canonical_off_switch(without_trust_controls),
                "{role} unit: the build-script runtime view"
            );
        }
    }

    #[test]
    fn verified_build_script_runtime_withholds_every_split_trust_control() {
        let original = flags(&[
            "--cfg",
            "fixture",
            "-Z",
            "trust-verify-session=session-1",
            "-Z",
            "trust-proof-artifact-root=/tmp/private-proof-store",
            "-Z",
            "trust-verify-package-name=fixture",
            "-Ztrust-verify-crate-role=primary",
            "-Ztrust-verify-level=2",
            "-Ztrust-verify=off",
            "-Copt-level=2",
        ]);
        let sanitized = build_script_rustflags_without_targo_authority(&original, true).unwrap();
        assert_eq!(
            sanitized,
            with_canonical_off_switch(flags(&["--cfg", "fixture", "-Copt-level=2"]))
        );
        assert!(
            original
                .iter()
                .any(|flag| flag.contains(TRUST_PROOF_ARTIFACT_ROOT_OPTION)),
            "the unit's compiler policy must remain intact"
        );
    }

    #[test]
    fn verified_build_script_runtime_withholds_attached_trust_controls() {
        let sanitized = build_script_rustflags_without_targo_authority(
            &flags(&[
                "-Ztrust-verify-session=session-1",
                "-Ztrust-proof-artifact-root=/tmp/private-proof-store",
                "-Ztrust-verify-level=1",
                "-Cpanic=abort",
            ]),
            true,
        )
        .unwrap();
        assert_eq!(
            sanitized,
            with_canonical_off_switch(flags(&["-Cpanic=abort"]))
        );
    }

    #[test]
    fn verified_build_script_runtime_withholds_rustc_equivalent_key_spellings() {
        let sanitized = build_script_rustflags_without_targo_authority(
            &flags(&[
                "-Ztrust_verify-session=session-1",
                "-Ztrust-proof_artifact_root=/tmp/private-proof-store",
                "-Ztrust_verify_level=1",
                "-Ztrust_verify=off",
                "-Cpanic=abort",
            ]),
            true,
        )
        .unwrap();
        assert_eq!(
            sanitized,
            with_canonical_off_switch(flags(&["-Cpanic=abort"]))
        );
    }

    #[test]
    fn verified_build_script_runtime_fails_closed_on_authority_policy_gaps() {
        for invalid in [
            flags(&["-Ztrust-verify-session=session-1"]),
            flags(&["-Ztrust-proof-artifact-root=/tmp/private"]),
            flags(&[
                "-Ztrust-verify-session=session-1",
                "-Ztrust-proof-artifact-root=relative",
            ]),
            flags(&[
                "-Ztrust-verify-session=session-1",
                "-Ztrust-proof-artifact-root=/tmp/one",
                "-Z",
                "trust-proof-artifact-root=/tmp/two",
            ]),
            flags(&[
                "-Ztrust-verify-session=session-1",
                "-Ztrust-verify-session=session-2",
                "-Ztrust-proof-artifact-root=/tmp/private",
            ]),
            flags(&[
                "-Z",
                "trust-verify-session=session-1",
                "-Z",
                "trust-proof-artifact-root",
            ]),
        ] {
            assert!(
                build_script_rustflags_without_targo_authority(&invalid, true).is_err(),
                "verified runtime accepted {invalid:?}"
            );
        }
    }

    #[test]
    fn ordinary_cargo_preserves_unknown_private_proof_flag() {
        let original = flags(&["-Ztrust-proof-artifact-root=/tmp/ordinary", "-Copt-level=1"]);
        assert_eq!(
            build_script_rustflags_without_targo_authority(&original, false).unwrap(),
            original
        );
    }

    #[test]
    fn verified_build_script_scrubs_all_inherited_compiler_flag_spellings() {
        for name in [
            "RUSTFLAGS",
            "CARGO_ENCODED_RUSTFLAGS",
            "RUSTDOCFLAGS",
            "CARGO_ENCODED_RUSTDOCFLAGS",
            "RUSTFLAGS_BOOTSTRAP",
            "RUSTFLAGS_NOT_BOOTSTRAP",
            "RUSTDOCFLAGS_BOOTSTRAP",
            "RUSTDOCFLAGS_NOT_BOOTSTRAP",
            "MAGIC_EXTRA_RUSTFLAGS",
            "CARGO_BUILD_RUSTFLAGS",
            "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS",
            "cargo_target_x86_64_unknown_linux_gnu_rustflags",
            "RuStDoCfLaGs_NoT_BoOtStRaP",
        ] {
            assert!(is_compiler_flag_environment(name), "{name}");
        }
        assert!(!is_compiler_flag_environment("TRUST_RUSTC_ARG_LOG"));
        assert!(!is_compiler_flag_environment("RUSTC"));
    }

    #[test]
    fn verified_build_script_scrubs_ambient_and_explicit_flag_channels() {
        let mut cmd = ProcessBuilder::new("build-script");
        cmd.env("cargo_encoded_rustflags", "project-controlled")
            .env("SAFE_EXPLICIT_ENV", "retained");

        scrub_compiler_flag_environment(
            &mut cmd,
            [
                "RuStDoCfLaGs_BoOtStRaP".to_string(),
                "CaRgO_EnCoDeD_RuStFlAgS".to_string(),
                "SAFE_AMBIENT_ENV".to_string(),
            ],
        );
        cmd.env("CARGO_ENCODED_RUSTFLAGS", "sanitized");

        if cfg!(windows) {
            assert!(!cmd.get_envs().contains_key("cargo_encoded_rustflags"));
            assert!(!cmd.get_envs().contains_key("CaRgO_EnCoDeD_RuStFlAgS"));
        } else {
            assert_eq!(cmd.get_envs().get("cargo_encoded_rustflags"), Some(&None));
            assert_eq!(cmd.get_envs().get("CaRgO_EnCoDeD_RuStFlAgS"), Some(&None));
        }
        assert_eq!(
            cmd.get_envs()
                .get("CARGO_ENCODED_RUSTFLAGS")
                .and_then(Option::as_deref),
            Some(std::ffi::OsStr::new("sanitized"))
        );
        assert_eq!(cmd.get_envs().get("RuStDoCfLaGs_BoOtStRaP"), Some(&None));
        assert_eq!(
            cmd.get_envs()
                .get("SAFE_EXPLICIT_ENV")
                .and_then(Option::as_deref),
            Some(std::ffi::OsStr::new("retained"))
        );
        assert!(!cmd.get_envs().contains_key("SAFE_AMBIENT_ENV"));
    }

    #[test]
    fn verified_build_script_process_scrubs_private_authority_and_flag_channels() {
        let mut command = ProcessBuilder::new("build-script");
        for name in TRUST_TARGO_INTERNAL_BUILD_SCRIPT_ENV {
            command.env(name, "secret");
        }
        command
            .env("TRUST_FUTURE_PRIVATE_CONTROL", "secret")
            .env("RUSTFLAGS", "-Ztrust-verify-session=forged")
            .env(
                "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS",
                "-Ztrust-proof-artifact-root=/tmp/forged",
            )
            .env("FIXTURE_MODE", "benign");

        scrub_verified_build_script_authority_env(&mut command);

        for name in TRUST_TARGO_INTERNAL_BUILD_SCRIPT_ENV {
            assert_eq!(command.get_env(name), None, "{name}");
        }
        for name in [
            "TRUST_FUTURE_PRIVATE_CONTROL",
            "RUSTFLAGS",
            "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS",
        ] {
            assert_eq!(command.get_env(name), None, "{name}");
        }
        assert_eq!(
            command.get_env("FIXTURE_MODE").as_deref(),
            Some(OsStr::new("benign"))
        );
    }
}
