//! Trust: produce the immutable current native installation consumed by repo::wp.
//! Component selection belongs to the existing dist owners. This transaction
//! neither qualifies WP nor grants proof, release or channel-promotion authority.

use std::path::{Component, Path, PathBuf};

use crate::core::build_steps::tool::RustcPrivateCompilers;
use crate::core::build_steps::{dist, repo, tool};
use crate::core::builder::{Builder, CommandLineStep, Kind, RunConfig, ShouldRun};
use crate::core::config::Config;
use crate::utils::tarball::GeneratedTarball;

const SELECTION: &str = "trust-wp-installation";

pub(crate) fn is_wp_installation(kind: Kind, paths: &[PathBuf]) -> bool {
    kind == Kind::Install && paths.iter().any(|path| path == Path::new(SELECTION))
}

pub(crate) fn validate_wp_installation(config: &Config) -> Result<(), String> {
    validate_with_environment(config, &std::env::vars_os().collect())
}

fn validate_with_environment(
    config: &Config,
    environment: &std::collections::BTreeMap<std::ffi::OsString, std::ffi::OsString>,
) -> Result<(), String> {
    if !cfg!(any(target_os = "macos", target_os = "linux")) {
        return Err("atomic native WP installation currently requires macOS or Linux".into());
    }
    if config.paths.as_slice() != [PathBuf::from(SELECTION)]
        || config.stage != 2
        || config.hosts.as_slice() != [config.host_target]
        || config.targets.as_slice() != [config.host_target]
        || config.download_rustc()
        || config.bypass_bootstrap_lock
        || !config.keep_stage.is_empty()
        || !config.keep_stage_std.is_empty()
        || !config.skip.is_empty()
        || config.include_default_paths
        || !config.free_args.is_empty()
        || config.compile_time_deps
        || !config.extended
        || config
            .target_config
            .get(&config.host_target)
            .is_some_and(|target| target.runner.is_some())
    {
        return Err("select only trust-wp-installation on one local extended stage-2 host/target, with ordinary locks and no downloaded/kept/skipped/default/extra targets or runner".into());
    }
    // Trust: dist::Rustc includes trustdoc only when its tool selector is enabled,
    // but the WP consumer always requires it. Refuse before building components.
    if config.tools.as_ref().is_some_and(|tools| {
        !tools.iter().any(|entry| tool::tool_config_entry_selects_user_tool(entry, "trustdoc"))
    }) {
        return Err(
            "WP installation requires trustdoc in build.tools (rustdoc is also an accepted selector)"
                .into(),
        );
    }
    // Trust: AY is installed when its source is present, independently of the
    // allowlist. The dist owner's required L2 backends do respect that list.
    for backend in dist::REQUIRED_L2_BACKENDS {
        if config.tools.as_ref().is_some_and(|tools| {
            !tools.iter().any(|entry| tool::tool_config_entry_selects_user_tool(entry, backend))
        }) {
            return Err(format!("WP installation requires {backend} in build.tools"));
        }
    }
    // Trust: the immutable native toolchain also serves formatter/linter consumers.
    // Reject an incomplete allowlist before starting any component build.
    for required in ["trustfmt", "tippy"] {
        if config.tools.as_ref().is_some_and(|tools| {
            !tools.iter().any(|entry| tool::tool_config_entry_selects_user_tool(entry, required))
        }) {
            return Err(format!("WP installation requires {required} in build.tools"));
        }
    }
    let prefix = config.prefix.as_deref().ok_or("set an explicit external install.prefix")?;
    if !prefix.is_absolute()
        || prefix.file_name().is_none()
        || prefix.components().any(|part| {
            !matches!(part, Component::RootDir | Component::Normal(_))
                || matches!(part, Component::Normal(name)
                    if name == "build" || name == "stage1" || name == "stage2"
                        || name == "rustc-private-sysroots")
        })
    {
        return Err(
            "install.prefix must be an absolute final installation path outside live build trees"
                .into(),
        );
    }
    if config.bindir != Path::new("bin")
        || config.libdir.as_deref().is_some_and(|dir| dir != Path::new("lib"))
        || config.sysconfdir.is_some()
        || config.datadir.is_some()
        || config.docdir.is_some()
        || config.mandir.is_some()
    {
        return Err(
            "WP installation requires the component owners' standard installed layout".into()
        );
    }
    repo::check_installation_environment(environment)?;
    if environment.contains_key(std::ffi::OsStr::new("DESTDIR")) {
        return Err("WP installation does not support DESTDIR".into());
    }
    if !config.dry_run() {
        let share = environment
            .get(std::ffi::OsStr::new("CARGO_BUILD_JOBS"))
            .and_then(|v| v.to_str())
            .and_then(|v| v.parse::<u32>().ok());
        if environment.get(std::ffi::OsStr::new("BUILD_SLOT_HELD")).map(|v| v.as_os_str())
            != Some(std::ffi::OsStr::new("1"))
            || share.is_none_or(|share| {
                share == 0 || config.jobs.is_none_or(|jobs| jobs == 0 || jobs > share)
            })
        {
            return Err(
                "WP installation requires build-slot admission and --jobs within its share".into(),
            );
        }
        let source = std::fs::canonicalize(&config.src).map_err(|e| e.to_string())?;
        let output = std::fs::canonicalize(&config.out).map_err(|e| e.to_string())?;
        if output == source || !output.starts_with(&source) {
            return Err(
                "WP installation build outputs must remain inside their own checkout".into()
            );
        }
        let parent = std::fs::canonicalize(prefix.parent().unwrap()).map_err(|e| e.to_string())?;
        if parent != prefix.parent().unwrap()
            || prefix.starts_with(&source)
            || prefix.starts_with(&output)
        {
            return Err("install.prefix must have an existing canonical parent outside source/build outputs".into());
        }
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct WpInstallation;

impl CommandLineStep for WpInstallation {
    type Output = ();
    const IS_HOST: bool = true;

    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {
        run.alias(SELECTION)
    }

    fn is_default_step(_builder: &Builder<'_>) -> bool {
        false
    }

    fn make_run(run: RunConfig<'_>) {
        run.builder.ensure(Self);
    }

    fn run(self, builder: &Builder<'_>) {
        validate_wp_installation(&builder.config)
            .unwrap_or_else(|error| panic!("native WP installation: {error}"));
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        transaction::run(builder).unwrap_or_else(|error| panic!("native WP installation: {error}"));
    }
}

fn components(builder: &Builder<'_>) -> [(&'static str, GeneratedTarball); 7] {
    let target = builder.host_target;
    let build_compiler = builder.compiler(1, target);
    // Trust: both private tools must link to the compiler installed in this transaction.
    let compilers = RustcPrivateCompilers::new(builder, 2, target);
    [
        ("trustc", builder.ensure(dist::Rustc { target_compiler: builder.compiler(2, target) })),
        (
            "trust-std",
            builder.ensure(dist::Std::new(builder, target)).expect("native std component"),
        ),
        (
            "trustc-dev",
            builder.ensure(dist::RustcDev::new(builder, target)).expect("native private component"),
        ),
        (
            "targo",
            builder.ensure(dist::Cargo { build_compiler, target }).expect("native Targo component"),
        ),
        // Trust: the compiler image contains backends, while the authenticated
        // frontend and its daemon belong to this dedicated component owner.
        (
            "targo-trust",
            builder
                .ensure(dist::TCargoTrust { build_compiler, target })
                .expect("native Targo verifier component"),
        ),
        (
            "trustfmt",
            builder.ensure(dist::Rustfmt { compilers, target }).expect("native Trustfmt component"),
        ),
        (
            "tippy",
            builder.ensure(dist::Clippy { compilers, target }).expect("native Tippy component"),
        ),
    ]
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
mod transaction;

#[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
mod tests;
