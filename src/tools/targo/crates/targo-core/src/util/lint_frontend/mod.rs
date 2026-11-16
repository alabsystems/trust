//! Native lint planning keeps the invoking Targo while the selected compiler
//! and its sibling driver remain one authenticated SDK. This grants no proof
//! authority: the child explicitly uses the unverified check/fix lane and the
//! existing driver enters the typed NoTrustEvidence route.

mod channels;
mod compiler_identity;
mod overlay;
mod path_identity;

use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};

use cargo_util::{ProcessBuilder, paths};

use crate::CargoResult;
use crate::util::GlobalContext;
use crate::util::tippy_arg_protocol;
use crate::util::tippy_frontend_args::FrontendArgs;
use compiler_identity::AuthenticatedCompiler;
use overlay::{ConfiguredOverlay, OverlayEnvironment};
use path_identity::{AuthenticatedDirectoryChain, AuthenticatedExecutable};

struct Inputs {
    compiler: AuthenticatedCompiler,
    planner: AuthenticatedExecutable,
    planner_directory: AuthenticatedDirectoryChain,
    driver: AuthenticatedExecutable,
    planner_path: PathBuf,
    driver_path: PathBuf,
}

impl Inputs {
    fn capture(gctx: &GlobalContext) -> Result<Self, String> {
        let planner = crate::authenticated_targo_path()
            .map_err(|error| format!("cannot authenticate the invoking native planner: {error}"))?
            .ok_or_else(|| "native lint requires the authenticated invoking Targo".to_owned())?;
        // Selection is deliberately before Rustc::new: that constructor can
        // execute version/sysroot probes through configured wrappers.
        let selected = gctx
            .selected_rustc_path()
            .map_err(|error| format!("{error:#}"))?;
        let selected =
            paths::resolve_executable(&selected).map_err(|error| format!("{error:#}"))?;
        let selected = if selected.is_absolute() {
            selected
        } else {
            gctx.cwd().join(selected)
        };
        Self::from_paths(planner.to_owned(), selected)
    }

    fn from_paths(planner_path: PathBuf, compiler_path: PathBuf) -> Result<Self, String> {
        if !compiler_path.is_absolute()
            || !tippy_arg_protocol::executable_path_matches(&compiler_path, "trustc")
        {
            return Err("native Tippy requires the selected original Trust compiler, not an unresolved proxy".into());
        }
        // Do not canonicalize the selection: that would erase the executable
        // symlink and original directory checks shared with public Tippy.
        let compiler = AuthenticatedCompiler::selected_trustc(compiler_path)?;
        let driver_path = compiler.path().with_file_name(if cfg!(windows) {
            "tippy-driver.exe"
        } else {
            "tippy-driver"
        });
        let planner_directory = AuthenticatedDirectoryChain::capture(
            planner_path
                .parent()
                .ok_or_else(|| "current planner has no original parent".to_owned())?,
        )?;
        let planner = AuthenticatedExecutable::capture(planner_path.clone(), "targo")?;
        let driver = AuthenticatedExecutable::capture(driver_path.clone(), "tippy-driver")?;
        let _ = planner_directory.revalidate()?;
        Ok(Self {
            compiler,
            planner,
            planner_directory,
            driver,
            planner_path,
            driver_path,
        })
    }

    fn guarded<T>(&self, operation: impl FnOnce() -> T) -> Result<T, String> {
        let original = self.planner_directory.revalidate()?;
        let result = self
            .compiler
            .run_guarded(|| {
                self.planner.run_guarded_for("Targo", || {
                    self.driver.run_guarded_for("Tippy driver", operation)
                })
            })
            .and_then(|result| result);
        self.planner_directory
            .confirm_stable_with_guard(&original)?;
        result.and_then(|result| result)
    }

    fn prepare(
        &self,
        args: FrontendArgs,
        context: &[std::ffi::OsString],
        environment: OverlayEnvironment,
    ) -> Result<Command, String> {
        let configured = if environment.is_configured() {
            let (commit, host) =
                self.guarded(|| overlay::query_compiler_identity(self.compiler.path()))??;
            ConfiguredOverlay::for_frontend(
                Some(self.compiler.path()),
                Some(&commit),
                environment.with_compiler_host(OsStr::new(&host)),
            )?
        } else {
            None
        };
        let mut command = compile_command(
            &self.planner_path,
            self.compiler.path(),
            &self.driver_path,
            &args,
            context,
        );
        if let Some(configured) = configured {
            configured.configure_command(&mut command);
        }
        Ok(command)
    }
}

fn compile_command(
    planner: &Path,
    compiler: &Path,
    driver: &Path,
    args: &FrontendArgs,
    context: &[std::ffi::OsString],
) -> Command {
    let mut command = Command::new(planner);
    overlay::clear_overlay_command_environment(&mut command);
    command
        .arg("--unverified")
        .arg(args.verb)
        .args(context)
        .args(&args.args)
        .env("CARGO", planner)
        .env("RUSTC", compiler)
        .env("RUSTC_WORKSPACE_WRAPPER", driver)
        .env("RUSTC_WRAPPER", "")
        .env("CARGO_BUILD_RUSTC_WRAPPER", "")
        .env("CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "")
        .env("TRUST_NO_MIGRATE_WARN", "1");
    for (key, value) in args.channels() {
        command.env(key, value);
    }
    for key in [
        "TRUST_TARGO_VERIFY",
        "TRUST_TARGO_LANE_RUSTFLAGS",
        "SYSROOT",
        "TRUST_BOOTSTRAP_SHIM_NO_VERIFY",
        "TRUST_BOOTSTRAP_SHIM_NO_VERIFY_TARGET_ONLY",
        "TRUST_BOOTSTRAP_NO_VERIFY",
        "TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY",
    ] {
        command.env_remove(key);
    }
    command
}

fn process(command: &Command, gctx: &GlobalContext) -> CargoResult<ProcessBuilder> {
    let mut process = ProcessBuilder::new(command.get_program());
    process.args(&command.get_args().collect::<Vec<_>>());
    for (name, value) in command.get_envs() {
        let name = name
            .to_str()
            .ok_or_else(|| anyhow::anyhow!("native lint environment key is not UTF-8"))?;
        match value {
            Some(value) => {
                process.env(name, value);
            }
            None => {
                process.env_remove(name);
            }
        }
    }
    if let Some(directory) = command.get_current_dir() {
        process.cwd(directory);
    }
    crate::withhold_unauthenticated_nested_unverified_endpoint(&mut process);
    // Configure after every overlay, retaining the SAME original scheduler in
    // the native ProcessBuilder through its synchronous owning wait.
    if let Some(original) = gctx.jobserver_from_env()? {
        process.inherit_jobserver(original);
    }
    Ok(process)
}

/// Execute the branded native command. The outer Result is executable/input
/// authentication; the inner result preserves actual spawn/status outcomes.
pub fn run(
    gctx: &GlobalContext,
    command: &str,
    args: &[&OsStr],
) -> Result<CargoResult<ExitStatus>, String> {
    let args = args.strip_prefix(&[OsStr::new(command)]).unwrap_or(args);
    let args = args
        .iter()
        .enumerate()
        .map(|(index, value)| {
            value
                .to_str()
                .map(str::to_owned)
                .ok_or_else(|| format!("Tippy argument {index} is not UTF-8"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let inputs = Inputs::capture(gctx)?;
    let controls = args.split(|arg| arg == "--").next().unwrap_or_default();
    if controls.iter().any(|arg| {
        matches!(
            arg.as_str(),
            "--help" | "-h" | "--version" | "-V" | "--explain"
        )
    }) {
        // These public controls never launch a planner. Keep the selected
        // SDK's help/version/lint documentation rather than invent a second
        // lint catalogue in Targo.
        let frontend_path = inputs.compiler.path().with_file_name(if cfg!(windows) {
            "targo-tippy.exe"
        } else {
            "targo-tippy"
        });
        let frontend = AuthenticatedExecutable::capture(frontend_path.clone(), "targo-tippy")?;
        let mut metadata = Command::new(frontend_path);
        metadata.arg(command).args(&args);
        let metadata = process(&metadata, gctx).map_err(|error| format!("{error:#}"))?;
        return inputs
            .guarded(|| frontend.run_guarded_for("Tippy frontend", || metadata.status()))
            .and_then(|result| result);
    }
    let args = FrontendArgs::parse(args);
    if args.compiler_args.iter().any(|arg| arg == "--no-deps") {
        // Preserve the public frontend's pre-dispatch rejection of malformed
        // legacy arguments. The actual selected driver parses its own option
        // grammar in a read-only version request, before any planner work.
        // Prefix the sole -vV inside the framed compiler arguments: an input
        // `--` must never hide the version operation or cause a source compile.
        // Repeating it in the physical argv makes rustc reject the merged query.
        let mut probe_args = args.compiler_args.clone();
        probe_args.insert(0, "-vV".into());
        let probe = FrontendArgs {
            verb: "check",
            args: Vec::new(),
            no_deps: args.no_deps,
            compiler_args: probe_args,
        };
        let mut probe_command = Command::new(&inputs.driver_path);
        probe_command.arg(inputs.compiler.path());
        let environment = compile_command(
            &inputs.planner_path,
            inputs.compiler.path(),
            &inputs.driver_path,
            &probe,
            &[],
        );
        for (name, value) in environment.get_envs() {
            match value {
                Some(value) => {
                    probe_command.env(name, value);
                }
                None => {
                    probe_command.env_remove(name);
                }
            }
        }
        let probe = process(&probe_command, gctx).map_err(|error| format!("{error:#}"))?;
        let output = inputs.guarded(|| probe.exec_with_output())?;
        if let Err(error) = output {
            return Ok(Err(error));
        }
    }
    let environment =
        OverlayEnvironment::capture_with(|name| gctx.get_env_os(name).map(OsStr::to_owned));
    let prepared = inputs.prepare(args, &gctx.native_lint_context_args(), environment)?;
    let child = process(&prepared, gctx).map_err(|error| format!("{error:#}"))?;
    inputs.guarded(|| child.status())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::tippy_arg_protocol::{NoDepsFlag, decode_args};

    #[test]
    fn native_lint_keeps_the_current_planner_and_selected_sdk_driver() {
        let args =
            FrontendArgs::parse(["--all-targets", "--", "-D", "warnings"].map(str::to_owned));
        let command = compile_command(
            Path::new("/current/targo"),
            Path::new("/sdk/bin/trustc"),
            Path::new("/sdk/bin/tippy-driver"),
            &args,
            &[],
        );
        assert_eq!(command.get_program(), "/current/targo");
        assert_eq!(
            command.get_args().collect::<Vec<_>>(),
            ["--unverified", "check", "--all-targets"]
        );
        let environment = command
            .get_envs()
            .collect::<std::collections::BTreeMap<_, _>>();
        assert_eq!(
            environment[OsStr::new("CARGO")],
            Some(OsStr::new("/current/targo"))
        );
        assert_eq!(
            environment[OsStr::new("RUSTC")],
            Some(OsStr::new("/sdk/bin/trustc"))
        );
        assert_eq!(
            environment[OsStr::new("RUSTC_WORKSPACE_WRAPPER")],
            Some(OsStr::new("/sdk/bin/tippy-driver"))
        );
        for key in [
            "TRUST_TARGO_VERIFY",
            "TRUST_TARGO_LANE_RUSTFLAGS",
            "SYSROOT",
        ] {
            assert_eq!(environment[OsStr::new(key)], None);
        }
        let decoded = decode_args(
            environment[OsStr::new("TIPPY_ENCODED_ARGS")]
                .unwrap()
                .to_str()
                .unwrap(),
        )
        .unwrap();
        assert_eq!(decoded.no_deps, NoDepsFlag::Explicit(false));
        assert_eq!(decoded.compiler_args, ["-D", "warnings"]);
    }

    #[test]
    fn current_planner_does_not_need_a_stale_sibling_planner_in_the_sdk() {
        let root = tempfile::tempdir().unwrap();
        let sdk = root.path().join("sdk/bin");
        std::fs::create_dir_all(&sdk).unwrap();
        let planner = root.path().join("targo");
        let compiler = sdk.join("trustc");
        let driver = sdk.join("tippy-driver");
        for path in [&planner, &compiler, &driver] {
            std::fs::write(path, b"original selected image").unwrap();
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            for path in [&planner, &compiler, &driver] {
                std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700)).unwrap();
            }
        }
        let inputs = Inputs::from_paths(planner.clone(), compiler).unwrap();
        assert_eq!(inputs.planner_path, planner);
        assert!(!sdk.join("targo").exists());
        inputs.guarded(|| ()).unwrap();
        #[cfg(unix)]
        {
            std::fs::rename(&driver, sdk.join("original-driver")).unwrap();
            std::fs::write(&driver, b"replacement selected image").unwrap();
            assert!(inputs.guarded(|| ()).is_err());
        }
        #[cfg(windows)]
        assert!(std::fs::rename(&driver, sdk.join("original-driver")).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn selected_compiler_symlink_is_not_normalized_into_sdk_authority() {
        use std::os::unix::fs::symlink;
        let root = tempfile::tempdir().unwrap();
        let bin = root.path().join("sdk/bin");
        std::fs::create_dir_all(&bin).unwrap();
        let original = bin.join("original-compiler");
        std::fs::write(&original, b"selected image").unwrap();
        symlink(&original, bin.join("trustc")).unwrap();
        let error = Inputs::from_paths(root.path().join("targo"), bin.join("trustc"))
            .err()
            .unwrap();
        assert!(error.contains("symlink"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn restored_planner_parent_cannot_hide_a_different_child_image() {
        use std::os::unix::fs::{MetadataExt as _, PermissionsExt as _};
        let root = tempfile::tempdir().unwrap();
        let sdk = root.path().join("sdk/bin");
        std::fs::create_dir_all(&sdk).unwrap();
        let directory = root.path().join("planner");
        std::fs::create_dir(&directory).unwrap();
        let planner = directory.join("targo");
        let compiler = sdk.join("trustc");
        let driver = sdk.join("tippy-driver");
        for path in [&planner, &compiler, &driver] {
            std::fs::write(path, b"original selected image").unwrap();
            std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700)).unwrap();
        }
        let before = planner.metadata().unwrap();
        let inputs = Inputs::from_paths(planner.clone(), compiler).unwrap();
        let saved = root.path().join("saved-planner");
        std::fs::rename(&directory, &saved).unwrap();
        std::fs::create_dir(&directory).unwrap();
        std::fs::write(directory.join("targo"), b"different intermediate image").unwrap();
        std::fs::remove_dir_all(&directory).unwrap();
        std::fs::rename(&saved, &directory).unwrap();
        let after = planner.metadata().unwrap();
        assert_eq!(
            (
                before.dev(),
                before.ino(),
                before.len(),
                before.ctime(),
                before.ctime_nsec()
            ),
            (
                after.dev(),
                after.ino(),
                after.len(),
                after.ctime(),
                after.ctime_nsec()
            )
        );
        assert!(inputs.guarded(|| ()).is_err());
    }

    #[test]
    fn parsed_caller_config_and_frozen_policy_survive_native_dispatch() {
        let root = tempfile::tempdir().unwrap();
        let home = root.path().join("home");
        std::fs::create_dir(&home).unwrap();
        let mut context = GlobalContext::new(
            cargo_util_terminal::Shell::new(),
            root.path().to_owned(),
            home,
        );
        let directory = root.path().join("target with spaces");
        let config = "build.build-dir='cache with spaces'".to_owned();
        context
            .configure(
                0,
                false,
                None,
                true,
                false,
                false,
                &Some(directory.clone()),
                &[],
                &[config.clone()],
            )
            .unwrap();
        let args = context.native_lint_context_args();
        assert_eq!(
            args.iter()
                .filter(|arg| arg.as_os_str() == OsStr::new("--frozen"))
                .count(),
            1
        );
        assert!(
            args.windows(2)
                .any(|pair| pair[0].as_os_str() == OsStr::new("--config")
                    && pair[1].as_os_str() == OsStr::new(&config))
        );
        assert!(
            args.windows(2)
                .any(|pair| pair[0].as_os_str() == OsStr::new("--target-dir")
                    && pair[1].as_os_str() == directory.as_os_str())
        );
    }

    /// The files Tippy compiles into its own binaries: by `#[path]` in
    /// src/tools/tippy/src/main.rs and driver.rs, and by `include!` in
    /// src/tools/tippy/src/arg_protocol.rs. Every module this file declares
    /// is one of them (`lint_frontend_submodules_are_all_shared_with_tippy`).
    const SHARED_WITH_TIPPY: [(&str, &str); 6] = [
        ("lint_frontend/channels.rs", include_str!("channels.rs")),
        (
            "lint_frontend/compiler_identity.rs",
            include_str!("compiler_identity.rs"),
        ),
        ("lint_frontend/overlay.rs", include_str!("overlay.rs")),
        (
            "lint_frontend/path_identity.rs",
            include_str!("path_identity.rs"),
        ),
        (
            "tippy_frontend_args.rs",
            include_str!("../tippy_frontend_args.rs"),
        ),
        (
            "tippy_arg_protocol.rs",
            include_str!("../tippy_arg_protocol.rs"),
        ),
    ];

    /// Every crate name targo-core's manifest declares, in any dependency
    /// table, as code spells it (`-` as `_`).
    fn targo_core_dependencies() -> std::collections::BTreeSet<String> {
        let mut names = std::collections::BTreeSet::new();
        let mut in_table = false;
        for line in include_str!("../../../Cargo.toml").lines().map(str::trim) {
            if let Some(header) = line.strip_prefix('[') {
                let header = header.trim_end_matches(']');
                // `[target.'cfg(windows)'.dependencies.windows-sys]` names one.
                if let Some((_, name)) = header.rsplit_once("dependencies.") {
                    names.insert(name.replace('-', "_"));
                    in_table = false;
                } else {
                    in_table = header.ends_with("dependencies");
                }
            } else if in_table && !line.is_empty() && !line.starts_with('#') {
                let name: String = line
                    .chars()
                    .take_while(|c| c.is_ascii_alphanumeric() || *c == '-' || *c == '_')
                    .collect();
                if !name.is_empty() {
                    names.insert(name.replace('-', "_"));
                }
            }
        }
        names
    }

    /// What `line` names that only targo-core binds: a `crate::` path (in
    /// Tippy that is Tippy's root), `extern crate`, or a path rooted at a
    /// targo-core dependency (Tippy has its own, and these files stay
    /// std-only: docs/DECISION-native-tippy-current-planner-2026-11-08.md).
    /// A lexical scan of one line; a comment is not code.
    fn targo_core_only_names(
        line: &str,
        dependencies: &std::collections::BTreeSet<String>,
    ) -> Vec<String> {
        let code = line.split("//").next().unwrap_or_default();
        let is_ident = |c: char| c.is_alphanumeric() || c == '_';
        let mut found = Vec::new();
        for root in std::iter::once("crate").chain(dependencies.iter().map(String::as_str)) {
            let needle = format!("{root}::");
            for (at, _) in code.match_indices(&needle) {
                let before = &code[..at];
                // Rooted unless it continues a path (`std::time::`, `x::crate::`)
                // or is `$crate::`; a leading `::` (`::portable_atomic::`) is a root.
                let rooted = match before.chars().next_back() {
                    None => true,
                    Some(':') => match before.strip_suffix("::") {
                        Some(rest) => !rest.ends_with(|c: char| is_ident(c) || c == '>'),
                        None => true,
                    },
                    Some(c) => !is_ident(c) && c != '$',
                };
                if rooted {
                    found.push(needle.clone());
                }
            }
        }
        let words: Vec<&str> = code.split_whitespace().collect();
        if words.windows(2).any(|pair| pair == ["extern", "crate"]) {
            found.push("extern crate".to_owned());
        }
        found
    }

    /// TIPPY-SHARED-TEST-MODULES-1: a `crate::util::` import in channels.rs's
    /// tests and a `portable_atomic` fixture counter compiled here and broke
    /// only Tippy's test targets, which this crate's lane never compiles. This
    /// catches that class where its author tests; a sibling the including
    /// module must bind (`super::FrontendArgs`) is beyond a lexical scan, and
    /// compiling Tippy's test targets (`x.py check src/tools/tippy
    /// --all-targets`) stays the authority.
    #[test]
    fn files_tippy_compiles_name_nothing_only_targo_core_binds() {
        let dependencies = targo_core_dependencies();
        // Positive controls: the manifest scan reads plain, inline-table and
        // dotted-table dependencies, and the line scan fires on each class
        // and the spellings that broke Tippy, and on nothing std-only.
        for name in [
            "portable_atomic",
            "cargo_util",
            "serde",
            "windows_sys",
            "snapbox",
        ] {
            assert!(dependencies.contains(name), "manifest scan missed `{name}`");
        }
        for (line, expected) in [
            (
                "    use crate::util::tippy_arg_protocol::{NoDepsFlag, decode_args};",
                "crate::",
            ),
            ("    use portable_atomic::AtomicU64;", "portable_atomic::"),
            (
                "static N: ::portable_atomic::AtomicU64 = new();",
                "portable_atomic::",
            ),
            (
                "let x:portable_atomic::AtomicU64 = new();",
                "portable_atomic::",
            ),
            ("    let p = crate::authenticated_targo_path();", "crate::"),
            ("extern crate libc;", "extern crate"),
        ] {
            assert_eq!(
                targo_core_only_names(line, &dependencies),
                [expected],
                "{line}"
            );
        }
        for line in [
            "pub(crate) fn capture() {}",
            "    use super::super::tippy_arg_protocol::{NoDepsFlag, decode_args};",
            "let now = std::time::SystemTime::now(); // crate::util is targo-core's",
            "macro_rules! m { () => { $crate::x } }",
            "use std::sync::Mutex;",
        ] {
            assert!(
                targo_core_only_names(line, &dependencies).is_empty(),
                "{line}"
            );
        }

        let mut violations = Vec::new();
        for (file, source) in SHARED_WITH_TIPPY {
            for (index, line) in source.lines().enumerate() {
                let names = targo_core_only_names(line, &dependencies);
                if !names.is_empty() {
                    violations.push(format!(
                        "src/util/{file}:{}: {} in `{}`",
                        index + 1,
                        names.join(", "),
                        line.trim()
                    ));
                }
            }
        }
        assert!(
            violations.is_empty(),
            "Tippy compiles these files too, where `crate::` is Tippy's root and \
             targo-core's dependencies do not exist: reach siblings through \
             `super::` and keep them std-only\n{}",
            violations.join("\n")
        );
    }

    /// Every module this file declares is one Tippy compiles today, so a new
    /// one joins SHARED_WITH_TIPPY and the scan above; one for targo-core
    /// alone would change this test, with its reason.
    #[test]
    fn lint_frontend_submodules_are_all_shared_with_tippy() {
        let declared: Vec<&str> = include_str!("mod.rs")
            .lines()
            .filter_map(|line| line.strip_prefix("mod ")?.strip_suffix(';'))
            .collect();
        assert!(
            declared.contains(&"channels"),
            "module scan found {declared:?}"
        );
        for module in declared {
            let file = format!("lint_frontend/{module}.rs");
            assert!(
                SHARED_WITH_TIPPY.iter().any(|(shared, _)| *shared == file),
                "{file} is not in SHARED_WITH_TIPPY, which \
                 files_tippy_compiles_name_nothing_only_targo_core_binds scans"
            );
        }
    }
}
