//! [`BuildContext`] is a (mostly) static information about a build task.

use crate::compiler::BuildConfig;
use crate::compiler::CompileKind;
use crate::compiler::Unit;
use crate::compiler::UnitIndex;
use crate::compiler::unit_graph::UnitGraph;
use crate::context::{FingerprintMethod, GlobalContext};
use crate::util::Rustc;
use crate::util::data_structures::{HashMap, HashSet};
use crate::util::errors::CargoResult;
use crate::util::interning::InternedString;
use crate::util::logger::BuildLogger;
use crate::workspace::PackageSet;
use crate::workspace::Workspace;
use crate::workspace::dependency::DepKind;
use crate::workspace::profiles::Profiles;

// Trust: project requirements use the same Cargo resolver before verification sessions.
mod project_policy;
pub(crate) use project_policy::resolve_project_trust_policy;
mod target_info;
pub use self::target_info::FileFlavor;
pub use self::target_info::FileType;
pub use self::target_info::RustcTargetData;
pub use self::target_info::TargetInfo;

/// The build context, containing complete information needed for a build task
/// before it gets started.
///
/// It is intended that this is mostly static information. Stuff that mutates
/// during the build can be found in the parent [`BuildRunner`]. (I say mostly,
/// because this has internal caching, but nothing that should be observable
/// or require &mut.)
///
/// As a result, almost every field on `BuildContext` is public, including
///
/// * a resolved [`UnitGraph`] of your dependencies,
/// * a [`Profiles`] containing compiler flags presets,
/// * a [`RustcTargetData`] containing host and target platform information,
/// * and a [`PackageSet`] for further package downloads,
///
/// just to name a few. Learn more on each own documentation.
///
/// # How to use
///
/// To prepare a build task, you may not want to use [`BuildContext::new`] directly,
/// since it is often too lower-level.
/// Instead, [`ops::create_bcx`] is usually what you are looking for.
///
/// After a `BuildContext` is built, the next stage of building is handled in [`BuildRunner`].
///
/// [`BuildRunner`]: crate::compiler::BuildRunner
/// [`ops::create_bcx`]: crate::ops::create_bcx
pub struct BuildContext<'a, 'gctx> {
    /// The workspace the build is for.
    pub ws: &'a Workspace<'gctx>,

    /// The cargo context.
    pub gctx: &'gctx GlobalContext,

    /// Build logger for `-Zbuild-analysis`.
    pub logger: Option<&'a BuildLogger>,

    /// Trust: build-local diagnostic capture IDs, never freshness authority.
    pub input_work_capture_ids: std::sync::Arc<portable_atomic::AtomicU64>,

    /// This contains a collection of compiler flags presets.
    pub profiles: Profiles,

    /// Configuration information for a rustc build.
    pub build_config: &'a BuildConfig,

    /// Source freshness uses compiler-reported content when available. This
    /// does not change verification-session liveness or build-script inputs.
    pub source_fingerprint: FingerprintMethod,
    /// Trust: opt-in enforced action inputs, independent of proof authority.
    pub action_sandbox: bool,
    pub action_platform: Option<std::sync::Arc<cargo_util::PlatformInputs>>,
    pub action_environment: Option<cargo_util::EnvironmentInputs>,
    pub shared_dependency_root: Option<std::path::PathBuf>,
    pub shared_dependency_units: HashSet<Unit>,

    /// Associated [`DepKind`]s for root targets
    pub selected_dep_kinds: DepKindSet,

    /// Extra compiler args for either `rustc` or `rustdoc`.
    pub extra_compiler_args: HashMap<Unit, Vec<String>>,

    /// Package downloader.
    ///
    /// This holds ownership of the `Package` objects.
    pub packages: PackageSet<'gctx>,

    /// Information about rustc and the target platform.
    pub target_data: RustcTargetData<'gctx>,

    /// The root units of `unit_graph` (units requested on the command-line).
    pub roots: Vec<Unit>,

    /// Trust: under a test plan, the requests that selected each root, as
    /// indices into `ResolvedPlan::requests` (the requests of this run, after
    /// `--request` narrowing; not the plan file's order). Empty without a plan.
    pub trust_root_requests: HashMap<Unit, Vec<usize>>,

    /// The dependency graph of units to compile.
    pub unit_graph: UnitGraph,

    /// A map from unit to index.
    pub unit_to_index: HashMap<Unit, UnitIndex>,

    /// Reverse-dependencies of documented units, used by the `rustdoc --scrape-examples` flag.
    pub scrape_units: Vec<Unit>,

    /// The list of all kinds that are involved in this build
    pub all_kinds: HashSet<CompileKind>,
}

impl BuildContext<'_, '_> {
    /// Record the already selected policy without preparing or executing a job.
    pub(crate) fn log_shared_dependency_policy(&self) {
        crate::compiler::shared_dependencies::log_policy(self);
    }
}

impl<'a, 'gctx> BuildContext<'a, 'gctx> {
    pub fn new(
        ws: &'a Workspace<'gctx>,
        logger: Option<&'a BuildLogger>,
        packages: PackageSet<'gctx>,
        build_config: &'a BuildConfig,
        selected_dep_kinds: DepKindSet,
        profiles: Profiles,
        extra_compiler_args: HashMap<Unit, Vec<String>>,
        target_data: RustcTargetData<'gctx>,
        roots: Vec<Unit>,
        unit_graph: UnitGraph,
        unit_to_index: HashMap<Unit, UnitIndex>,
        scrape_units: Vec<Unit>,
    ) -> CargoResult<BuildContext<'a, 'gctx>> {
        let all_kinds = unit_graph
            .keys()
            .map(|u| u.kind)
            .chain(build_config.requested_kinds.iter().copied())
            .chain(std::iter::once(CompileKind::Host))
            .collect();

        let gctx = ws.gctx();
        let action_sandbox = gctx.build_config()?.action_sandbox.unwrap_or(false);
        let shared_dependencies = gctx
            .build_config()?
            .shared_dependency_cache
            .unwrap_or(false);
        if shared_dependencies
            && (!gctx.cli_unstable().fine_grain_locking
                || !gctx.cli_unstable().build_dir_new_layout
                || !crate::is_targo_invocation()
                || crate::trust_verified_targo()
                || !cfg!(target_os = "macos"))
        {
            anyhow::bail!(
                "build.shared-dependency-cache requires native unverified Targo on macOS with -Zfine-grain-locking and -Zbuild-dir-new-layout"
            );
        }
        let shared_dependency_units = if shared_dependencies {
            crate::compiler::shared_dependencies::eligible_units(&unit_graph, &roots, ws.root())
        } else {
            HashSet::default()
        };
        let shared_dependency_root = if shared_dependencies {
            Some(crate::compiler::shared_dependencies::storage_root(
                gctx.home().as_path_unlocked(),
            )?)
        } else {
            None
        };
        let has_confined_actions = action_sandbox || !shared_dependency_units.is_empty();
        if has_confined_actions
            && (target_data.rustc.wrapper.is_some()
                || target_data.rustc.workspace_wrapper.is_some()
                || target_data.rustc.host.to_string()
                    != format!("{}-apple-darwin", std::env::consts::ARCH))
        {
            anyhow::bail!(
                "confined dependency compilation requires the same native host architecture and no compiler wrappers"
            );
        }
        if action_sandbox {
            if !crate::is_targo_invocation()
                || crate::trust_verified_targo()
                || !cfg!(target_os = "macos")
            {
                anyhow::bail!(
                    "build.action-sandbox currently requires native unverified Targo on macOS"
                );
            }
            if !gctx.cli_unstable().build_dir_new_layout {
                anyhow::bail!(
                    "build.action-sandbox requires -Zbuild-dir-new-layout for isolated action outputs"
                );
            }
            if target_data.rustc.host.to_string()
                != format!("{}-apple-darwin", std::env::consts::ARCH)
            {
                anyhow::bail!(
                    "build.action-sandbox requires the compiler and Targo to use the same native host architecture"
                );
            }
            if target_data.rustc.wrapper.is_some() || target_data.rustc.workspace_wrapper.is_some()
            {
                anyhow::bail!("build.action-sandbox does not yet admit compiler wrappers");
            }
            for unit in unit_graph.keys() {
                let library = unit.target.is_lib()
                    && unit.target.rustc_crate_types().iter().all(|kind| {
                        matches!(
                            kind,
                            crate::compiler::CrateType::Lib | crate::compiler::CrateType::Rlib
                        )
                    });
                if unit.target.is_custom_build()
                    || unit.target.proc_macro()
                    || !(unit.mode.is_check()
                        || (unit.mode == crate::compiler::CompileMode::Build && library))
                {
                    anyhow::bail!(
                        "build.action-sandbox currently admits checks and Rust library compilation, without build scripts or proc macros: {}",
                        unit.pkg.package_id()
                    );
                }
            }
        }
        let action_platform = if has_confined_actions {
            Some(std::sync::Arc::new(cargo_util::PlatformInputs::capture()?))
        } else {
            None
        };
        let action_environment = if has_confined_actions {
            let mut environment = cargo_util::ProcessBuilder::new("__action_environment__");
            crate::compiler::apply_env_config(gctx, &mut environment)?;
            // env_config omits force=false entries supplied by the caller.
            // Keep their declarations, and capture the selected caller value.
            for name in gctx.get::<crate::context::EnvConfig>(["env"])?.keys() {
                if !environment.get_envs().contains_key(name)
                    && let Some(value) = gctx.get_env_os(name)
                {
                    environment.env(name, value);
                }
            }
            crate::util::rustc::scrub_trust_targo_internal_env(&mut environment);
            // Trust: preserve standard compiler/locale selection. Additional
            // environment inputs must be declared through Cargo's [env];
            // orchestration tags are not compiler inputs by inheritance.
            Some(cargo_util::EnvironmentInputs::capture_for(
                &environment,
                &[
                    "PATH",
                    "HOME",
                    "LANG",
                    "LC_ALL",
                    "LC_CTYPE",
                    "LC_MESSAGES",
                    "TZ",
                    "RUSTUP_HOME",
                    "RUSTUP_TOOLCHAIN",
                    "RUSTC_BOOTSTRAP",
                    "MACOSX_DEPLOYMENT_TARGET",
                    "IPHONEOS_DEPLOYMENT_TARGET",
                    "TVOS_DEPLOYMENT_TARGET",
                    "WATCHOS_DEPLOYMENT_TARGET",
                    "XROS_DEPLOYMENT_TARGET",
                    "SDKROOT",
                    "DEVELOPER_DIR",
                    cargo_util::paths::dylib_path_envvar(),
                ],
            )?)
        } else {
            None
        };
        let configured = gctx.build_config()?.fingerprint;
        let source_fingerprint = if gctx.cli_unstable().checksum_freshness {
            configured.unwrap_or_default()
        } else if crate::is_targo_invocation()
            && configured.is_none()
            && target_data.rustc.supports_checksum_depinfo(gctx)?
        {
            FingerprintMethod::Content
        } else {
            FingerprintMethod::Mtime
        };

        Ok(BuildContext {
            ws,
            gctx: ws.gctx(),
            logger,
            input_work_capture_ids: std::sync::Arc::new(portable_atomic::AtomicU64::new(0)),
            packages,
            build_config,
            source_fingerprint,
            action_sandbox,
            action_platform,
            action_environment,
            shared_dependency_root,
            shared_dependency_units,
            selected_dep_kinds,
            profiles,
            extra_compiler_args,
            target_data,
            roots,
            // Trust: `create_bcx` assigns it under a test plan.
            trust_root_requests: HashMap::default(),
            unit_graph,
            unit_to_index,
            scrape_units,
            all_kinds,
        })
    }

    /// Information of the `rustc` this build task will use.
    pub fn rustc(&self) -> &Rustc {
        &self.target_data.rustc
    }

    pub fn confines(&self, unit: &Unit) -> bool {
        self.action_sandbox || self.shared_dependency_units.contains(unit)
    }

    /// Gets the host architecture tuple.
    ///
    /// For example, `x86_64-unknown-linux-gnu`, would be
    /// - machine: `x86_64`,
    /// - hardware-platform: `unknown`,
    /// - operating system: `linux-gnu`.
    pub fn host_triple(&self) -> InternedString {
        self.target_data.rustc.host
    }

    /// Gets the number of jobs specified for this build.
    pub fn jobs(&self) -> u32 {
        self.build_config.jobs
    }

    /// Extra compiler args for either `rustc` or `rustdoc`.
    ///
    /// As of now, these flags come from the trailing args of either
    /// `cargo rustc` or `cargo rustdoc`.
    pub fn extra_args_for(&self, unit: &Unit) -> Option<&Vec<String>> {
        self.extra_compiler_args.get(unit)
    }

    /// Whether to measure the peak memory usage (rusage) of build unit processes.
    ///
    /// Only true when `-Zmem-stats` is enabled and the build logger is active.
    pub fn capture_rusage(&self) -> bool {
        self.gctx.cli_unstable().mem_stats && self.logger.is_some()
    }
}

#[derive(Copy, Clone, Default, Debug)]
pub struct DepKindSet {
    pub build: bool,
    pub normal: bool,
    pub dev: bool,
}

impl DepKindSet {
    pub fn contains(&self, kind: DepKind) -> bool {
        match kind {
            DepKind::Build => self.build,
            DepKind::Normal => self.normal,
            DepKind::Development => self.dev,
        }
    }
}
