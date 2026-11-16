//! Type definitions for the result of a compilation.

use crate::util::data_structures::HashMap;
use std::collections::BTreeSet;
use std::ffi::{OsStr, OsString};
use std::path::Path;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::Arc;

use anyhow::Context as _;
use cargo_platform::CfgExpr;
use cargo_util::{ProcessBuilder, paths};

use crate::compiler::BuildContext;
use crate::compiler::CompileTarget;
use crate::compiler::RustdocFingerprint;
use crate::compiler::apply_env_config;
use crate::compiler::{CompileKind, Unit, UnitHash};
use crate::util::process_authority::{
    configure_nested_unverified_targo_child, scrub_dynamic_loader_authority_env,
    verified_tool_runtime_library_paths,
};
use crate::util::{CargoResult, GlobalContext};
use crate::workspace::Package;

use super::fingerprint::VerifiedRustdocLauncherIdentity;

/// Trust: every tool process Cargo builds here inherits the ambient
/// environment. `RUST_TARGET_PATH` would reopen the unauthenticated named-target
/// search that `target_info` closes, so it is stripped at the one place all such
/// processes are constructed rather than at each call site.
fn scrub_verified_target_search_path(cmd: &mut ProcessBuilder, verified_targo: bool) {
    if verified_targo {
        cmd.env_remove("RUST_TARGET_PATH");
    }
}

/// Represents the kind of process we are creating.
#[derive(Debug)]
enum ToolKind {
    /// See [`Compilation::rustc_process`].
    Rustc,
    /// See [`Compilation::rustdoc_process`].
    Rustdoc,
    /// See [`Compilation::host_process`].
    HostProcess,
    /// See [`Compilation::target_process`].
    TargetProcess,
}

/// The source selected for a rustc command.
///
/// Keep this alongside [`Compilation::rustc_process`] so callers can enforce
/// role-specific protocol invariants without inferring authority from an
/// executable basename. In particular, a primary-unit override takes
/// precedence over the workspace wrapper.
///
/// Trust: upstream decides the same three cases inline and keeps only the
/// resulting command. Which of them was chosen is exactly what the verified
/// lane needs to know — a wrapper or proxy runs after argv validation — and it
/// cannot be recovered from the command afterwards.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RustcProcessRole {
    /// The configured compiler process, possibly behind the ordinary wrapper.
    Compiler,
    /// The process includes the configured workspace wrapper.
    WorkspaceWrapper,
    /// The primary-unit process override was selected. Cargo fix uses this
    /// process as a proxy and lets it invoke the workspace wrapper afterward.
    PrimaryOverride { downstream_workspace_wrapper: bool },
}

impl RustcProcessRole {
    pub(crate) fn uses_workspace_wrapper(self) -> bool {
        matches!(
            self,
            Self::WorkspaceWrapper
                | Self::PrimaryOverride {
                    downstream_workspace_wrapper: true
                }
        )
    }

    pub(crate) fn is_primary_override(self) -> bool {
        matches!(self, Self::PrimaryOverride { .. })
    }

    pub(crate) fn has_downstream_workspace_wrapper(self) -> bool {
        matches!(
            self,
            Self::PrimaryOverride {
                downstream_workspace_wrapper: true
            }
        )
    }
}

fn select_rustc_process_role(
    is_primary: bool,
    is_workspace: bool,
    has_primary_override: bool,
    has_workspace_wrapper: bool,
) -> RustcProcessRole {
    if is_primary && has_primary_override {
        RustcProcessRole::PrimaryOverride {
            downstream_workspace_wrapper: is_workspace && has_workspace_wrapper,
        }
    } else if is_workspace && has_workspace_wrapper {
        RustcProcessRole::WorkspaceWrapper
    } else {
        RustcProcessRole::Compiler
    }
}

impl ToolKind {
    fn is_rustc_tool(&self) -> bool {
        matches!(self, ToolKind::Rustc | ToolKind::Rustdoc)
    }
}

/// Structure with enough information to run `rustdoc --test`.
pub struct Doctest {
    /// What's being doctested
    pub unit: Unit,
    /// Arguments needed to pass to rustdoc to run this test.
    pub args: Vec<OsString>,
    /// Whether or not -Zunstable-options is needed.
    pub unstable_opts: bool,
    /// The -Clinker value to use.
    pub linker: Option<PathBuf>,
    /// The script metadata, if this unit's package has a build script.
    ///
    /// This is used for indexing [`Compilation::extra_env`].
    pub script_metas: Option<Vec<UnitHash>>,

    /// Environment variables to set in the rustdoc process.
    pub env: HashMap<String, OsString>,
}

/// Information about the output of a unit.
pub struct UnitOutput {
    /// The unit that generated this output.
    pub unit: Unit,
    /// Path to the unit's primary output (an executable or cdylib).
    pub path: PathBuf,
    /// The script metadata, if this unit's package has a build script.
    ///
    /// This is used for indexing [`Compilation::extra_env`].
    pub script_metas: Option<Vec<UnitHash>>,

    /// Environment variables to set in the unit's process.
    pub env: HashMap<String, OsString>,
}

/// A structure returning the result of a compilation.
pub struct Compilation<'gctx> {
    /// The unit queue's original selection; no scheduler is reconstructed here.
    pub(super) post_build_compiler: Option<super::post_build_compiler::Scheduler>,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    candidate_preparation: Option<Arc<super::candidate_commands::Preparation>>,
    /// Trust: actual test actions already run by the compilation's queue.
    pub(crate) test_execution: Option<crate::ops::cargo_test::graph::TestGraphRun>,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(crate) qualification: Option<super::qualification::Run>,
    /// An array of all tests created during this compilation.
    pub tests: Vec<UnitOutput>,

    /// An array of all binaries created.
    pub binaries: Vec<UnitOutput>,

    /// An array of all cdylibs created.
    pub cdylibs: Vec<UnitOutput>,

    /// The crate names of the root units specified on the command-line.
    pub root_crate_names: Vec<String>,

    /// All directories for the output of native build commands.
    ///
    /// This is currently used to drive some entries which are added to the
    /// `LD_LIBRARY_PATH` as appropriate.
    ///
    /// The order should be deterministic.
    pub native_dirs: BTreeSet<PathBuf>,

    /// Root output directory (for the local package's artifacts)
    pub root_output: HashMap<CompileKind, PathBuf>,

    /// Output directories for rust dependencies.
    /// May be for the host or for a specific target.
    pub deps_output: HashMap<CompileKind, BTreeSet<PathBuf>>,

    /// The path to libstd for each target
    sysroot_target_libdir: HashMap<CompileKind, PathBuf>,

    /// Extra environment variables that were passed to compilations and should
    /// be passed to future invocations of programs.
    ///
    /// The key is the build script metadata for uniquely identifying the
    /// `RunCustomBuild` unit that generated these env vars.
    pub extra_env: HashMap<UnitHash, Vec<(String, String)>>,

    /// Libraries to test with rustdoc.
    pub to_doc_test: Vec<Doctest>,

    /// Rustdoc fingerprint files to determine whether we need to run `rustdoc --read-doc-meta-dir`.
    ///
    /// See `-Zrustdoc-mergeable-info` for more.
    pub rustdoc_fingerprints: Option<HashMap<CompileKind, RustdocFingerprint>>,

    /// Verified-only `trustdoc` cache/integrity fingerprint carried across the
    /// build. It is not execution identity; verified doctests fail closed.
    verified_rustdoc_launcher: Option<Arc<VerifiedRustdocLauncherIdentity>>,

    /// Extra flags to pass to rustdoc for each host or target.
    pub rustdocflags: HashMap<CompileKind, Rc<[String]>>,

    /// The target host tuple.
    pub host: String,

    gctx: &'gctx GlobalContext,

    /// Rustc process to be used by default
    rustc_process: ProcessBuilder,
    /// Rustc process to be used for workspace crates instead of `rustc_process`
    rustc_workspace_wrapper_process: ProcessBuilder,
    /// Whether `rustc_workspace_wrapper_process` actually has a workspace
    /// wrapper rather than merely being an equivalent compiler process.
    has_rustc_workspace_wrapper: bool,
    /// Optional rustc process to be used for primary crates instead of either `rustc_process` or
    /// `rustc_workspace_wrapper_process`
    primary_rustc_process: Option<ProcessBuilder>,

    /// The runner to use for each host or target process.
    runners: HashMap<CompileKind, Option<(PathBuf, Vec<String>)>>,
    /// The linker to use for each host or target.
    linkers: HashMap<CompileKind, Option<PathBuf>>,

    /// The total number of lint warnings emitted by the compilation.
    pub lint_warning_count: usize,

    // Trust: preserve the actual configured width for the later run phase.
    // Ambient jobserver capacity does not describe this fixed admission.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fixed_gnu_ceiling: u32,
}

impl<'gctx> Compilation<'gctx> {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(super) fn for_candidate<'a>(
        bcx: &BuildContext<'a, 'gctx>,
        preparation: Arc<super::candidate_commands::Preparation>,
    ) -> CargoResult<Self> {
        preparation.require_context(bcx)?;
        let mut compilation = Self::new(bcx)?;
        compilation.candidate_preparation = Some(preparation);
        Ok(compilation)
    }
    /// Shared pure location bookkeeping. The returned directories are created
    /// only by the ordinary runner which owns their Layout leases.
    pub(super) fn record_output_paths<'a, L: std::borrow::Borrow<super::layout::LayoutPaths>>(
        &mut self,
        bcx: &BuildContext<'a, 'gctx>,
        files: &super::build_runner::CompilationFiles<'a, 'gctx, L>,
    ) -> Vec<PathBuf> {
        let mut directories = Vec::new();
        for &kind in &bcx.all_kinds {
            let layout = files.layout(kind);
            if let Some(artifact_dir) = layout.artifact_dir() {
                self.root_output
                    .insert(kind, artifact_dir.dest().to_path_buf());
            }
            if bcx.gctx.cli_unstable().build_dir_new_layout
                || bcx
                    .unit_graph
                    .keys()
                    .any(|unit| unit.kind == kind && files.private_unit(unit).is_some())
            {
                for unit in bcx.unit_graph.keys().filter(|unit| unit.kind == kind) {
                    let directory = files.deps_dir(unit);
                    if let Some(private) = files.private_unit(unit) {
                        directories.push(private.root().to_path_buf());
                        directories.push(private.incremental().to_path_buf());
                    }
                    directories.push(directory.clone());
                    if unit.target.is_dylib() {
                        self.deps_output.entry(kind).or_default().insert(directory);
                    }
                }
            } else {
                self.deps_output
                    .entry(kind)
                    .or_default()
                    .insert(layout.build_dir().legacy_deps().to_path_buf());
            }
        }
        directories
    }

    pub fn new<'a>(bcx: &BuildContext<'a, 'gctx>) -> CargoResult<Compilation<'gctx>> {
        let rustc_process = bcx.rustc().process();
        let primary_rustc_process = bcx.build_config.primary_unit_rustc.clone();
        let rustc_workspace_wrapper_process = bcx.rustc().workspace_process();
        let has_rustc_workspace_wrapper = bcx
            .rustc()
            .workspace_wrapper
            .as_deref()
            .is_some_and(|wrapper| !wrapper.as_os_str().is_empty());
        let host = bcx.host_triple().to_string();
        // Trust: capture the launcher once for the whole build. Capturing per
        // unit would compare each doc unit only against itself, which cannot
        // detect a swap that happens between two of them.
        let verified_rustdoc_launcher = if super::verified_targo_protocol_active()
            && !bcx.build_config.unit_graph
            && bcx.unit_graph.keys().any(|unit| {
                unit.mode.is_doc() || unit.mode.is_doc_scrape() || unit.mode.is_doc_test()
            }) {
            Some(Arc::new(
                VerifiedRustdocLauncherIdentity::capture_for_build(bcx.gctx, bcx.rustc())?,
            ))
        } else {
            None
        };
        let sysroot_target_libdir = get_sysroot_target_libdir(bcx)?;
        let rustdocflags = bcx
            .all_kinds
            .iter()
            .map(|&kind| (kind, bcx.target_data.info(kind).rustdocflags.clone()))
            .collect();

        // When `target-applies-to-host=false`, and without `--target`,
        // there will be only `CompileKind::Host` in requested_kinds.
        // Need to insert target config explicitly for target-applies-to-host=false
        // to find the correct configs.
        let insert_explicit_host_runner = !bcx.gctx.target_applies_to_host()?
            && bcx
                .build_config
                .requested_kinds
                .iter()
                .any(CompileKind::is_host);
        let mut runners = bcx
            .build_config
            .requested_kinds
            .iter()
            .chain(Some(&CompileKind::Host))
            .map(|kind| Ok((*kind, target_runner(bcx, *kind)?)))
            .collect::<CargoResult<HashMap<_, _>>>()?;
        if insert_explicit_host_runner {
            let kind = explicit_host_kind(&host);
            runners.insert(kind, target_runner(bcx, kind)?);
        }

        let mut linkers = bcx
            .build_config
            .requested_kinds
            .iter()
            .chain(Some(&CompileKind::Host))
            .map(|kind| Ok((*kind, target_linker(bcx, *kind)?)))
            .collect::<CargoResult<HashMap<_, _>>>()?;
        if insert_explicit_host_runner {
            let kind = explicit_host_kind(&host);
            linkers.insert(kind, target_linker(bcx, kind)?);
        }
        Ok(Compilation {
            post_build_compiler: None,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            candidate_preparation: None,
            native_dirs: BTreeSet::new(),
            test_execution: None,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            qualification: None,
            root_output: HashMap::default(),
            deps_output: HashMap::default(),
            sysroot_target_libdir,
            tests: Vec::new(),
            binaries: Vec::new(),
            cdylibs: Vec::new(),
            root_crate_names: Vec::new(),
            extra_env: HashMap::default(),
            to_doc_test: Vec::new(),
            rustdoc_fingerprints: None,
            verified_rustdoc_launcher,
            rustdocflags,
            gctx: bcx.gctx,
            host,
            rustc_process,
            rustc_workspace_wrapper_process,
            has_rustc_workspace_wrapper,
            primary_rustc_process,
            runners,
            linkers,
            lint_warning_count: 0,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            fixed_gnu_ceiling: bcx.jobs(),
        })
    }

    pub(in crate::compiler) fn verified_rustdoc_launcher(
        &self,
    ) -> Option<Arc<VerifiedRustdocLauncherIdentity>> {
        self.verified_rustdoc_launcher.clone()
    }

    /// Trust: revalidate the deferred doctest launcher's cache/integrity
    /// fingerprint. Doctests run after the compile phase has already reported,
    /// so their launcher check cannot ride along with a unit's. Verified
    /// doctest execution stays fail-closed until its nested process tree has a
    /// sealed handle-bound launcher.
    pub(crate) fn ensure_verified_rustdoc_launcher_current(&self) -> CargoResult<()> {
        if let Some(identity) = &self.verified_rustdoc_launcher {
            identity.ensure_current()?;
        }
        Ok(())
    }

    /// Trust: the authenticated compiler image — never a primary-rustc override
    /// or workspace wrapper, which are only transport processes. Both the
    /// verified runtime-library prefix `fill_env` builds and the one loader
    /// value the certified-monitor seal reinstalls are derived from THIS path,
    /// so the two cannot be judged against different toolchains.
    pub(crate) fn authenticated_compiler_program(&self) -> &Path {
        Path::new(self.rustc_process.get_program())
    }

    /// Returns a [`ProcessBuilder`] for running `rustc` and the process role
    /// that selected it.
    ///
    /// `is_primary` is true if this is a "primary package", which means it
    /// was selected by the user on the command-line (such as with a `-p`
    /// flag), see [`crate::compiler::BuildRunner::primary_packages`].
    ///
    /// `is_workspace` is true if this is a workspace member.
    pub(crate) fn rustc_process(
        &self,
        unit: &Unit,
        is_primary: bool,
        is_workspace: bool,
    ) -> CargoResult<(ProcessBuilder, RustcProcessRole)> {
        let role = select_rustc_process_role(
            is_primary,
            is_workspace,
            self.primary_rustc_process.is_some(),
            self.has_rustc_workspace_wrapper,
        );
        let mut rustc = match role {
            RustcProcessRole::PrimaryOverride { .. } => self
                .primary_rustc_process
                .clone()
                .expect("the selected primary override must be present"),
            RustcProcessRole::WorkspaceWrapper => self.rustc_workspace_wrapper_process.clone(),
            RustcProcessRole::Compiler => self.rustc_process.clone(),
        };
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(preparation) = &self.candidate_preparation {
            preparation.validate()?;
            rustc.environment_snapshot(preparation.environment().clone());
        }
        if self.gctx.extra_verbose() {
            rustc.display_env_vars();
        }
        let cmd = fill_rustc_tool_env(rustc, unit);
        let cmd = self.fill_env(cmd, &unit.pkg, None, unit.kind, ToolKind::Rustc)?;
        Ok((cmd, role))
    }

    /// Returns a [`ProcessBuilder`] for running `rustdoc`.
    pub fn rustdoc_process(
        &self,
        unit: &Unit,
        script_metas: Option<&Vec<UnitHash>>,
    ) -> CargoResult<ProcessBuilder> {
        let mut rustdoc = ProcessBuilder::new(&*self.gctx.rustdoc()?);
        // Trust (T14a): as every compiler process (`Rustc::process`): none of
        // Targo's private protocol (the lane, which carries the session and
        // proof root; the verified marker; the test-monitor session) reaches
        // trustdoc, its proc macros or its doctests. `fill_env` adds back
        // the frontend mark and, in the unverified lane, the broker address.
        crate::util::rustc::scrub_trust_targo_internal_env(&mut rustdoc);
        if self.gctx.extra_verbose() {
            rustdoc.display_env_vars();
        }
        let cmd = fill_rustc_tool_env(rustdoc, unit);
        let mut cmd = self.fill_env(cmd, &unit.pkg, script_metas, unit.kind, ToolKind::Rustdoc)?;
        cmd.retry_with_argfile(true);
        unit.target.edition().cmd_edition_arg(&mut cmd);

        for crate_type in unit.target.rustc_crate_types() {
            cmd.arg("--crate-type").arg(crate_type.as_str());
        }

        Ok(cmd)
    }

    /// Returns a [`ProcessBuilder`] appropriate for running a process for the
    /// host platform.
    ///
    /// This is currently only used for running build scripts. If you use this
    /// for anything else, please be extra careful on how environment
    /// variables are set!
    pub fn host_process<T: AsRef<OsStr>>(
        &self,
        cmd: T,
        pkg: &Package,
    ) -> CargoResult<ProcessBuilder> {
        // Only use host runner when -Zhost-config is enabled
        // to ensure `target.<host>.runner` does not wrap build scripts.
        let builder = if !self.gctx.target_applies_to_host()?
            && let Some((runner, args)) = self
                .runners
                .get(&CompileKind::Host)
                .and_then(|x| x.as_ref())
        {
            let mut builder = ProcessBuilder::new(runner);
            builder.args(args);
            builder.arg(cmd);
            builder
        } else {
            ProcessBuilder::new(cmd)
        };
        self.fill_env(builder, pkg, None, CompileKind::Host, ToolKind::HostProcess)
    }

    pub fn target_runner(&self, kind: CompileKind) -> Option<&(PathBuf, Vec<String>)> {
        let target_applies_to_host = self.gctx.target_applies_to_host().unwrap_or(true);
        let kind = if !target_applies_to_host && kind.is_host() {
            // Use explicit host target tuple when `target-applies-to-host=false`
            // This ensures `host.runner` won't be accidentally applied to `cargo run` / `cargo test`.
            explicit_host_kind(&self.host)
        } else {
            kind
        };
        self.runners.get(&kind).and_then(|x| x.as_ref())
    }

    /// Gets the `[host.linker]` for host build target (build scripts and proc macros).
    pub fn host_linker(&self) -> Option<&Path> {
        self.linkers
            .get(&CompileKind::Host)
            .and_then(|x| x.as_ref())
            .map(|x| x.as_path())
    }

    /// Gets the user-specified linker for a particular host or target.
    pub fn target_linker(&self, kind: CompileKind) -> Option<&Path> {
        let target_applies_to_host = self.gctx.target_applies_to_host().unwrap_or(true);
        let kind = if !target_applies_to_host && kind.is_host() {
            // Use explicit host target tuple when `target-applies-to-host=false`
            // This ensures `host.linker` won't be accidentally applied to normal builds
            explicit_host_kind(&self.host)
        } else {
            kind
        };
        self.linkers
            .get(&kind)
            .and_then(|x| x.as_ref())
            .map(|x| x.as_path())
    }

    /// Returns a [`ProcessBuilder`] appropriate for running a process for the
    /// target platform. This is typically used for `cargo run` and `cargo
    /// test`.
    ///
    /// `script_metas` is the metadata for the `RunCustomBuild` unit that this
    /// unit used for its build script. Use `None` if the package did not have
    /// a build script.
    pub fn target_process<T: AsRef<OsStr>>(
        &self,
        cmd: T,
        kind: CompileKind,
        pkg: &Package,
        script_metas: Option<&Vec<UnitHash>>,
    ) -> CargoResult<ProcessBuilder> {
        self.target_process_with_jobserver(
            cmd,
            kind,
            pkg,
            script_metas,
            self.gctx.jobserver_from_env()?,
        )
    }

    /// Trust: `run` may carry a narrower actual GNU owner than startup. The
    /// selected owner is retained by its caller through the target's wait.
    pub(crate) fn target_process_with_jobserver<T: AsRef<OsStr>>(
        &self,
        cmd: T,
        kind: CompileKind,
        pkg: &Package,
        script_metas: Option<&Vec<UnitHash>>,
        jobserver: Option<&cargo_util::Jobserver>,
    ) -> CargoResult<ProcessBuilder> {
        let builder = if let Some((runner, args)) = self.target_runner(kind) {
            let mut builder = ProcessBuilder::new(runner);
            builder.args(args);
            builder.arg(cmd);
            builder
        } else {
            ProcessBuilder::new(cmd)
        };
        let tool_kind = ToolKind::TargetProcess;
        let mut builder = self.fill_env(builder, pkg, script_metas, kind, tool_kind)?;

        if let Some(client) = jobserver {
            // Trust: the runner's scheduler clone does not update this early
            // capture. Retain a same-pool recovery owner on the run target too,
            // so a plain child spawn can recover the original pipe it closes.
            let selected = client
                .for_descendant()
                .context("failed to retain run-target scheduler")?;
            builder.inherit_jobserver(&selected);
        }

        Ok(builder)
    }

    /// Trust: construct only for actual post-compilation direct leaves. The
    /// managed action queue already owns its scheduler and never calls this.
    pub(crate) fn prepare_target_execution(
        &self,
        command: ProcessBuilder,
    ) -> CargoResult<super::target_execution::TargetExecution> {
        super::target_execution::TargetExecution::new(
            command,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            self.fixed_target_jobserver()?,
        )
    }

    /// Compiler work after the unit queue has joined still owes that queue's
    /// actual scheduler and native admission, unlike ordinary test executables.
    pub(crate) fn prepare_doc_test_execution(
        &self,
        command: ProcessBuilder,
    ) -> CargoResult<super::post_build_compiler::Execution> {
        let selected = self
            .post_build_compiler
            .as_ref()
            .context("doctest execution has no retained original compiler scheduler")?;
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let fixed = if matches!(selected, super::post_build_compiler::Scheduler::Fixed) {
            self.fixed_target_jobserver()?
        } else {
            None
        };
        selected.prepare(
            command,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            fixed,
        )
    }

    /// Trust: compilation has returned its actual GNU guards. A fixed `run`
    /// borrows supplementary credits from that SAME ancestor again, under the
    /// already checked configured ceiling; it cannot expose the wider pool.
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fn fixed_target_jobserver(
        &self,
    ) -> CargoResult<Option<super::resource_gnu_fixed::FixedTargetJobserver>> {
        let (Some(claim), Some(inherited)) = (
            self.gctx.fixed_admission()?,
            self.gctx.jobserver_from_env()?,
        ) else {
            return Ok(None);
        };
        Ok(Some(super::resource_gnu_fixed::FixedTargetJobserver::new(
            inherited,
            self.fixed_gnu_ceiling,
            Arc::clone(claim),
        )?))
    }

    /// Prepares a new process with an appropriate environment to run against
    /// the artifacts produced by the build process.
    ///
    /// The package argument is also used to configure environment variables as
    /// well as the working directory of the child process.
    fn fill_env(
        &self,
        mut cmd: ProcessBuilder,
        pkg: &Package,
        script_metas: Option<&Vec<UnitHash>>,
        kind: CompileKind,
        tool_kind: ToolKind,
    ) -> CargoResult<ProcessBuilder> {
        let verified_rustc_tool = crate::is_targo_invocation()
            && crate::trust_verified_targo()
            && tool_kind.is_rustc_tool();
        let mut search_path = Vec::new();
        if tool_kind.is_rustc_tool() {
            // Trust: a primary rustc override (notably cargo-fix's Targo proxy)
            // is only the transport process; the authenticated downstream image
            // remains `self.rustc_process`. Derive the verified toolchain
            // libdir from that compiler, never from an override executable —
            // otherwise the override chooses which libraries it is judged by.
            if verified_rustc_tool {
                let compiler = self.authenticated_compiler_program();
                if !compiler.is_absolute() {
                    anyhow::bail!(
                        "verified Targo selected non-absolute compiler path `{}` while constructing its runtime-library closure",
                        compiler.display()
                    );
                }
                search_path.extend(verified_tool_runtime_library_paths(compiler)?);
            } else {
                prepend_trust_compiler_libdir(&mut search_path, &cmd);
            }
            if matches!(tool_kind, ToolKind::Rustdoc) {
                // HACK: `rustdoc --test` not only compiles but executes doctests.
                // Ideally only execution phase should have search paths appended,
                // so the executions can find native libs just like other tests.
                // However, there is no way to separate these two phase, so this
                // hack is added for both phases.
                // TODO: handle doctest-xcompile
                search_path.extend(super::filter_dynamic_search_path(
                    self.native_dirs.iter(),
                    &self.root_output[&CompileKind::Host],
                ));
            }
            if let Some(paths) = self.deps_output.get(&CompileKind::Host) {
                search_path.extend(paths.clone());
            }
        } else {
            search_path.extend(self.target_runtime_search_paths(pkg, kind));
        }

        // Trust: a verified compiler or documentation launcher must not inherit
        // an ambient dynamic-library search list — code loaded into the
        // compiler is inside the proof TCB, and upstream's `dylib_path()` is
        // whatever the caller's environment says. The deterministic prefix above
        // contains the authenticated toolchain libdir plus Cargo-owned unit
        // dependency directories. Windows PATH is also executable discovery
        // authority required by downstream tool spawning, so its broader
        // closure remains a separately reported limitation.
        let preserve_ambient_search = !verified_rustc_tool || paths::dylib_path_envvar() == "PATH";
        let dylib_path = if preserve_ambient_search {
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            if let Some(preparation) = &self.candidate_preparation {
                preparation
                    .environment()
                    .get(OsStr::new(paths::dylib_path_envvar()))
                    .map(|value| std::env::split_paths(&value).collect())
                    .unwrap_or_default()
            } else {
                paths::dylib_path()
            }
            #[cfg(not(any(target_os = "linux", target_os = "macos")))]
            paths::dylib_path()
        } else {
            Vec::new()
        };
        let dylib_path_is_empty = dylib_path.is_empty();
        if dylib_path.starts_with(&search_path) {
            search_path = dylib_path;
        } else {
            search_path.extend(dylib_path.into_iter());
        }
        if cfg!(target_os = "macos") && dylib_path_is_empty {
            // These are the defaults when DYLD_FALLBACK_LIBRARY_PATH isn't
            // set or set to an empty string. Since Cargo is explicitly setting
            // the value, make sure the defaults still work.
            if !verified_rustc_tool {
                if let Some(home) = self.gctx.get_env_os("HOME") {
                    search_path.push(PathBuf::from(home).join("lib"));
                }
                search_path.push(PathBuf::from("/usr/local/lib"));
            }
            search_path.push(PathBuf::from("/usr/lib"));
        }
        let search_path = paths::join_paths(&search_path, paths::dylib_path_envvar())?;
        let verified_search_path = verified_rustc_tool.then(|| search_path.clone());

        cmd.env(paths::dylib_path_envvar(), &search_path);
        if verified_rustc_tool {
            scrub_dynamic_loader_authority_env(&mut cmd, Some(paths::dylib_path_envvar()));
        }
        if let Some(meta_vec) = script_metas {
            for meta in meta_vec {
                if let Some(env) = self.extra_env.get(meta) {
                    for (k, v) in env {
                        if k == "OUT_DIR" && !tool_kind.is_rustc_tool() {
                            continue;
                        }
                        cmd.env(k, v);
                    }
                }
            }
        }

        #[cfg(any(target_os = "linux", target_os = "macos"))]
        let cargo_exe = match &self.candidate_preparation {
            Some(preparation) => preparation.frontend()?,
            None => self.gctx.cargo_exe()?,
        };
        #[cfg(not(any(target_os = "linux", target_os = "macos")))]
        let cargo_exe = self.gctx.cargo_exe()?;
        cmd.env(crate::CARGO_ENV, cargo_exe);

        // When adding new environment variables depending on
        // crate properties which might require rebuild upon change
        // consider adding the corresponding properties to the hash
        // in BuildContext::target_metadata()
        // Trust: freshness resolves observed path variables from this same
        // package-owned value, never an inherited or configured lookalike.
        use crate::workspace::manifest::ManifestPathEnv;
        cmd.env("CARGO_MANIFEST_DIR", ManifestPathEnv::Dir.value(pkg))
            .env("CARGO_MANIFEST_PATH", ManifestPathEnv::Path.value(pkg))
            .env("CARGO_PKG_VERSION_MAJOR", &pkg.version().major.to_string())
            .env("CARGO_PKG_VERSION_MINOR", &pkg.version().minor.to_string())
            .env("CARGO_PKG_VERSION_PATCH", &pkg.version().patch.to_string())
            .env("CARGO_PKG_VERSION_PRE", pkg.version().pre.as_str())
            .env("CARGO_PKG_VERSION", &pkg.version().to_string())
            .env("CARGO_PKG_NAME", &*pkg.name());

        for (key, value) in pkg.manifest().metadata().env_vars() {
            cmd.env(key, value.as_ref());
        }

        cmd.cwd(pkg.root());

        apply_env_config(self.gctx, &mut cmd)?;

        // Trust: only the native frontend publishes native metadata twins.
        // The Cargo compatibility entrypoint keeps the upstream environment.
        if crate::is_targo_invocation() {
            mirror_cargo_env_as_targo(&mut cmd);
        }
        if crate::is_targo_invocation() && crate::trust_verified_targo() {
            // Trust: verified target tuples are admitted only from rustc's closed
            // built-in inventory; explicit JSON targets are path/content bound.
            // Scrub the ambient named-custom search path from every descendant,
            // including build scripts, so no later process layer can restore an
            // untracked target-spec origin.
            scrub_verified_target_search_path(&mut cmd, true);
        }
        // Trust: mark compiler/build-script descendants as originating from
        // the canonical targo frontend. This is distinct from verifier mode:
        // `TRUST_TARGO_VERIFY` only accompanies a proof-session nonce and
        // tracked verifier policy.
        if crate::is_targo_invocation() {
            cmd.env("TRUST_TARGO_FRONTEND", "1");
        }
        if verified_rustc_tool {
            // Trust: close any late explicit overlay installed by package/build/env
            // processing after the deterministic search path was selected.
            // Merely retaining the search variable would preserve an attacker
            // value installed by `.cargo/config.toml`; restore the authenticated
            // deterministic value before scrubbing every other loader channel.
            cmd.env(
                paths::dylib_path_envvar(),
                verified_search_path
                    .as_ref()
                    .expect("verified rustc tool must have a captured search path"),
            );
            scrub_dynamic_loader_authority_env(&mut cmd, Some(paths::dylib_path_envvar()));
        }

        // `$CARGO` is intentionally the exact branded Targo frontend. Preserve
        // an ancestor's explicit-unverified decision for nested Cargo
        // orchestration (for example trybuild) through a live broker exchange,
        // not ambient flags or a configuration marker.
        configure_nested_unverified_targo_child(&mut cmd)?;

        // Trust: std intentionally closes ambient descriptors. Carry only an
        // inert live-ancestor locator across build-script/test spawns; nested
        // Targo recovers the actual originals and repeats full domain checks.
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(original) = self.gctx.fixed_admission()? {
            cmd.env(
                jobserver_utils::FIXED_CLAIM_HANDOFF_ENV,
                original.descendant_advertisement()?,
            );
            // Old images must refuse rather than ignore the new courier and
            // proceed without a ceiling. New readers never parse this sentinel.
            cmd.env(
                trust_build_tree::admission::FIXED_HANDOFF_ENV,
                "requires-live-ancestor-v1",
            );
        }

        Ok(cmd)
    }

    /// The same deterministic normal target-process prefix used by execution
    /// and by retained native workload input capture. Ambient loader overlays
    /// remain a separate observed/refused input to the native owner.
    pub(crate) fn target_runtime_search_paths(
        &self,
        pkg: &Package,
        kind: CompileKind,
    ) -> Vec<PathBuf> {
        let mut paths = Vec::new();
        if let Some(root) = self.root_output.get(&kind) {
            paths.extend(super::filter_dynamic_search_path(
                self.native_dirs.iter(),
                root,
            ));
            paths.push(root.clone());
        }
        if let Some(dependencies) = self.deps_output.get(&kind) {
            paths.extend(dependencies.iter().cloned());
        }
        // Keep the ordinary build-std/proc-macro policy unchanged.
        if self.gctx.cli_unstable().build_std.is_none() || pkg.proc_macro() {
            paths.push(self.sysroot_target_libdir[&kind].clone());
        }
        paths
    }
}

/// Trust: expose each effective `CARGO_*` value to native Trust crates under
/// its canonical `TARGO_*` spelling while retaining the compatibility variable
/// for foreign crates. Deriving the native value here, from Cargo's own final
/// map, is what stops project config from giving the two spellings
/// contradictory meanings — the alternative is two independent sources.
fn mirror_cargo_env_as_targo(cmd: &mut ProcessBuilder) {
    let cargo_twins: Vec<(String, std::ffi::OsString)> = cmd
        .get_envs()
        .iter()
        .filter_map(|(key, value)| {
            let suffix = key.strip_prefix("CARGO_")?;
            Some((format!("TARGO_{suffix}"), value.as_ref()?.clone()))
        })
        .collect();
    for (key, value) in cargo_twins {
        cmd.env(&key, value);
    }
}

// Trust: pins the process-role selection and the environment derivations above,
// both of which are decided from state that is gone by the time the command is
// spawned and so cannot be asserted on from an integration test.
#[cfg(test)]
mod rustc_process_role_tests {
    use super::{
        RustcProcessRole, mirror_cargo_env_as_targo, scrub_verified_target_search_path,
        select_rustc_process_role,
    };
    use cargo_util::ProcessBuilder;
    use std::ffi::OsStr;

    #[test]
    fn native_targo_environment_is_an_exact_compatibility_twin() {
        let mut command = ProcessBuilder::new("trustc");
        command
            .env("CARGO_PKG_VERSION", "1.2.3")
            .env("CARGO_MANIFEST_DIR", "/workspace/package")
            .env("TARGO_PKG_VERSION", "project-forged")
            .env("UNRELATED", "preserved");
        command.env_remove("CARGO_REMOVED");

        mirror_cargo_env_as_targo(&mut command);

        assert_eq!(
            command.get_env("TARGO_PKG_VERSION").as_deref(),
            Some(OsStr::new("1.2.3"))
        );
        assert_eq!(
            command.get_env("TARGO_MANIFEST_DIR").as_deref(),
            Some(OsStr::new("/workspace/package"))
        );
        assert_eq!(command.get_env("TARGO_REMOVED"), None);
        assert_eq!(
            command.get_env("UNRELATED").as_deref(),
            Some(OsStr::new("preserved"))
        );
    }

    #[test]
    fn verified_descendants_scrub_named_custom_target_search_path() {
        let mut verified = ProcessBuilder::new("trustc");
        verified.env("RUST_TARGET_PATH", "/workspace/targets");
        scrub_verified_target_search_path(&mut verified, true);
        assert_eq!(verified.get_env("RUST_TARGET_PATH"), None);

        let mut ordinary = ProcessBuilder::new("rustc");
        ordinary.env("RUST_TARGET_PATH", "/workspace/targets");
        scrub_verified_target_search_path(&mut ordinary, false);
        assert_eq!(
            ordinary.get_env("RUST_TARGET_PATH"),
            Some("/workspace/targets".into())
        );
    }

    #[test]
    fn primary_override_precedes_workspace_wrapper() {
        assert_eq!(
            select_rustc_process_role(true, true, true, true),
            RustcProcessRole::PrimaryOverride {
                downstream_workspace_wrapper: true
            }
        );
        assert_eq!(
            select_rustc_process_role(true, true, true, false),
            RustcProcessRole::PrimaryOverride {
                downstream_workspace_wrapper: false
            }
        );
        assert_eq!(
            select_rustc_process_role(true, false, true, true),
            RustcProcessRole::PrimaryOverride {
                downstream_workspace_wrapper: false
            }
        );
        assert_eq!(
            select_rustc_process_role(true, true, false, true),
            RustcProcessRole::WorkspaceWrapper
        );
        assert_eq!(
            select_rustc_process_role(false, true, true, true),
            RustcProcessRole::WorkspaceWrapper
        );
        assert_eq!(
            select_rustc_process_role(false, true, false, false),
            RustcProcessRole::Compiler
        );
    }
}

fn prepend_trust_compiler_libdir(search_path: &mut Vec<PathBuf>, cmd: &ProcessBuilder) {
    let Ok(program) = paths::resolve_executable(Path::new(cmd.get_program())) else {
        return;
    };
    // Trust retains `rustc` as the compiler compatibility alias. A direct
    // invocation of the sibling `cargo` binary resolves that alias, so it needs
    // the same runtime libdir treatment as canonical `trustc`/`trustdoc`.
    // `rustdoc` is intentionally absent: Trust does not ship that stock alias.
    if !["trustc", "trustdoc", "rustc"].iter().any(|expected| {
        crate::util::tippy_arg_protocol::executable_path_matches(&program, expected)
    }) {
        return;
    }
    let Some(bin_dir) = program.parent() else {
        return;
    };
    let libdir = bin_dir.join("..").join("lib");
    if !libdir.is_dir() {
        return;
    }
    search_path.retain(|path| path != &libdir);
    search_path.insert(0, libdir);
}

/// Prepares a `rustc_tool` process with additional environment variables
/// that are only relevant in a context that has a unit
fn fill_rustc_tool_env(mut cmd: ProcessBuilder, unit: &Unit) -> ProcessBuilder {
    if unit.target.is_executable() {
        let name = unit
            .target
            .binary_filename()
            .unwrap_or(unit.target.name().to_string());

        cmd.env("CARGO_BIN_NAME", name);
    }
    cmd.env("CARGO_CRATE_NAME", unit.target.crate_name());
    cmd
}

fn get_sysroot_target_libdir(
    bcx: &BuildContext<'_, '_>,
) -> CargoResult<HashMap<CompileKind, PathBuf>> {
    bcx.all_kinds
        .iter()
        .map(|&kind| {
            let Some(info) = bcx.target_data.get_info(kind) else {
                let target = match kind {
                    CompileKind::Host => "host".to_owned(),
                    CompileKind::Target(s) => s.short_name().to_owned(),
                };

                let dependency = bcx
                    .unit_graph
                    .iter()
                    .find_map(|(u, _)| (u.kind == kind).then_some(u.pkg.summary().package_id()))
                    .unwrap();

                anyhow::bail!(
                    "could not find specification for target `{target}`.\n  \
                    Dependency `{dependency}` requires to build for target `{target}`."
                )
            };

            Ok((kind, info.sysroot_target_libdir.clone()))
        })
        .collect()
}

fn target_runner(
    bcx: &BuildContext<'_, '_>,
    kind: CompileKind,
) -> CargoResult<Option<(PathBuf, Vec<String>)>> {
    if let Some(runner) = bcx.target_data.target_config(kind).runner.as_ref() {
        let path = runner.val.path.clone().resolve_program(bcx.gctx);
        return Ok(Some((path, runner.val.args.clone())));
    }

    // With `target-applies-to-host = true`,
    // host artifacts must fall through to pick up from [target]
    // since this is the stable behavior
    if kind.is_host() && !bcx.gctx.target_applies_to_host()? {
        return Ok(None);
    }

    // try target.'cfg(...)'.runner
    let target_cfg = bcx.target_data.info(kind).cfg();
    let mut cfgs = bcx
        .gctx
        .target_cfgs()?
        .iter()
        .filter_map(|(key, cfg)| cfg.runner.as_ref().map(|runner| (key, runner)))
        .filter(|(key, _runner)| CfgExpr::matches_key(key, target_cfg));
    let matching_runner = cfgs.next();
    if let Some((key, runner)) = cfgs.next() {
        anyhow::bail!(
            "several matching instances of `target.'cfg(..)'.runner` in configurations\n\
             first match `{}` located in {}\n\
             second match `{}` located in {}",
            matching_runner.unwrap().0,
            matching_runner.unwrap().1.definition,
            key,
            runner.definition
        );
    }
    Ok(matching_runner.map(|(_k, runner)| {
        (
            runner.val.path.clone().resolve_program(bcx.gctx),
            runner.val.args.clone(),
        )
    }))
}

/// Gets the user-specified linker for a particular host or target from the configuration.
fn target_linker(bcx: &BuildContext<'_, '_>, kind: CompileKind) -> CargoResult<Option<PathBuf>> {
    // Try host.linker and target.{}.linker.
    if let Some(path) = bcx
        .target_data
        .target_config(kind)
        .linker
        .as_ref()
        .map(|l| l.val.clone().resolve_program(bcx.gctx))
    {
        return Ok(Some(path));
    }

    // With `target-applies-to-host = true`,
    // host artifacts must fall through to pick up from [target]
    // since this is the stable behavior
    if kind.is_host() && !bcx.gctx.target_applies_to_host()? {
        return Ok(None);
    }

    // Try target.'cfg(...)'.linker.
    let target_cfg = bcx.target_data.info(kind).cfg();
    let mut cfgs = bcx
        .gctx
        .target_cfgs()?
        .iter()
        .filter_map(|(key, cfg)| cfg.linker.as_ref().map(|linker| (key, linker)))
        .filter(|(key, _linker)| CfgExpr::matches_key(key, target_cfg));
    let matching_linker = cfgs.next();
    if let Some((key, linker)) = cfgs.next() {
        anyhow::bail!(
            "several matching instances of `target.'cfg(..)'.linker` in configurations\n\
             first match `{}` located in {}\n\
             second match `{}` located in {}",
            matching_linker.unwrap().0,
            matching_linker.unwrap().1.definition,
            key,
            linker.definition
        );
    }
    Ok(matching_linker.map(|(_k, linker)| linker.val.clone().resolve_program(bcx.gctx)))
}

fn explicit_host_kind(host: &str) -> CompileKind {
    let target = CompileTarget::new(host, false).expect("must be a host tuple");
    CompileKind::Target(target)
}
