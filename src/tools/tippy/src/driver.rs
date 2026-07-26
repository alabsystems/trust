#![feature(rustc_private)]
// warn on lints, that are included in `rust-lang/rust`s bootstrap
#![warn(rust_2018_idioms, unused_lifetimes)]
// warn on rustc internal lints
#![warn(rustc::internal)]
// FIXME: switch to something more ergonomic here, once available.
// (Currently there is no way to opt into sysroot crates without `extern crate`.)
// Blessed env_mutation (2026-07-20): vendored upstream tool code, compiled by
// the Trust toolchain's extended tools build. These files mutate process-global
// env under their own discipline (rust-analyzer's EnvChange holds an env lock;
// compiletest/tidy/opt-dist run single-threaded harness setup). Upstream builds
// them under stock rustc, so unknown_lints keeps that path green too.
#![allow(unknown_lints)]
#![allow(env_mutation)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_session;
extern crate rustc_span;

mod arg_protocol;
mod frontend_args;
mod path_identity;
mod rustc_private_overlay;

/// See docs in <https://github.com/rust-lang/rust/blob/HEAD/compiler/rustc/src/main.rs>
/// and <https://github.com/rust-lang/rust/pull/146627> for why we need this.
///
/// FIXME(madsmtm): This is loaded from the sysroot that was built with the other `rustc` crates
/// above, instead of via Cargo as you'd normally do. This is currently needed for LTO due to
/// <https://github.com/rust-lang/cc-rs/issues/1613>.
#[cfg(feature = "jemalloc")]
extern crate tikv_jemalloc_sys as _;

use clippy_utils::sym;
use declare_clippy_lint::LintListBuilder;
use rustc_interface::interface;
use rustc_session::config::ErrorOutputType;
use rustc_session::{EarlyDiagCtxt, Session};
use rustc_span::symbol::Symbol;

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::{env, fs};

use arg_protocol::{
    CLIPPY_ARGS_ENV, DecodedTippyArgs, NoDepsFlag, TIPPY_ENCODED_ARGS_ENV, decode_args,
    executable_path_matches_with_windows_semantics,
};
use frontend_args::split_legacy_no_deps;
use path_identity::{AuthenticatedDirectoryChain, AuthenticatedExecutable, metadata_is_plain_file};
use rustc_private_overlay::{
    ConfiguredOverlay, HOST_DIR_ENV, OverlayEnvironment, PreparedCompilerArgs, TARGET_DIR_ENV, crate_uses_overlay,
    query_compiler_commit_hash,
};

fn is_compiler_wrapper_mode(args: &[String]) -> bool {
    is_compiler_wrapper_mode_with_windows_semantics(args, cfg!(windows))
}

fn is_compiler_wrapper_mode_with_windows_semantics(args: &[String], windows_semantics: bool) -> bool {
    let Some(path) = args.get(1).map(Path::new) else {
        return false;
    };
    compiler_path_is_valid(path, windows_semantics)
}

fn compiler_options() -> rustc_session::getopts::Options {
    let mut options = rustc_session::getopts::Options::new();
    for option in rustc_session::config::rustc_optgroups() {
        option.apply(&mut options);
    }
    options
}

fn compiler_matches(args: &[String]) -> Result<rustc_session::getopts::Matches, String> {
    compiler_options()
        .parse(args.get(1..).unwrap_or_default())
        .map_err(|error| format!("invalid compiler arguments: {error}"))
}

fn should_print_tippy_version(matches: &rustc_session::getopts::Matches, wrapper_mode: bool) -> bool {
    !wrapper_mode && matches.opt_present("version") && !matches.opt_present("verbose")
}

/// Expand response files exactly once and use the returned snapshot both for
/// policy decisions and for compilation. Inspecting one expansion but handing
/// rustc the original `@file` would create a time-of-check/time-of-use race if
/// a workspace rewrites the file or swaps a symlink between the two reads.
fn expanded_args_snapshot(early_dcx: &EarlyDiagCtxt, args: &[String]) -> Vec<String> {
    let Some(program) = args.first() else {
        return Vec::new();
    };
    let mut expanded = Vec::with_capacity(args.len());
    expanded.push(program.clone());
    expanded.extend(rustc_driver::args::arg_expand_all(
        early_dcx,
        args.get(1..).unwrap_or_default(),
    ));
    expanded
}

fn has_sysroot_arg(matches: &rustc_session::getopts::Matches) -> bool {
    matches.opt_present("sysroot")
}

fn branded_args_override_selected_sysroot(branded: bool, matches: &rustc_session::getopts::Matches) -> bool {
    branded && has_sysroot_arg(matches)
}

fn has_response_file_arg(args: &[String]) -> bool {
    args.iter().any(|arg| arg.starts_with('@'))
}

fn internal_tippy_args_override_toolchain(compiler_args: &[String]) -> Result<bool, String> {
    let mut args = Vec::with_capacity(compiler_args.len() + 1);
    args.push("tippy-internal-args".to_owned());
    args.extend_from_slice(compiler_args);
    compiler_matches(&args).map(|matches| has_sysroot_arg(&matches))
}

fn compiler_path_is_valid(path: &Path, windows_semantics: bool) -> bool {
    executable_path_matches_with_windows_semantics(path, "rustc", windows_semantics)
        || executable_path_matches_with_windows_semantics(path, "trustc", windows_semantics)
}

fn insert_compiler_args_after_program(args: &mut Vec<String>, compiler_args: impl IntoIterator<Item = String>) {
    let insertion = usize::from(!args.is_empty());
    args.splice(insertion..insertion, compiler_args);
}

/// Locate rustc's semantic `--` without duplicating getopts' option-arity
/// table. A literal `--` can itself be the required value of an option such as
/// `--crate-name`; parsing the prefix distinguishes that case from a true
/// separator. The complete argv is parsed first, so any prefix error other than
/// a missing required value is an internal inconsistency and fails closed.
fn compiler_semantic_separator(args: &[String]) -> Result<Option<usize>, String> {
    compiler_matches(args)?;
    for (index, arg) in args.iter().enumerate().skip(1) {
        if arg != "--" {
            continue;
        }
        match compiler_options().parse(&args[1..index]) {
            Ok(_) => return Ok(Some(index)),
            Err(rustc_session::getopts::Fail::ArgumentMissing(_)) => {},
            Err(error) => {
                return Err(format!(
                    "compiler arguments parsed as a whole but failed before candidate separator {index}: {error}"
                ));
            },
        }
    }
    Ok(None)
}

fn insert_lint_compiler_args(
    args: &mut Vec<String>,
    compiler_args: impl IntoIterator<Item = String>,
) -> Result<(), String> {
    let insertion = compiler_semantic_separator(args)?.unwrap_or(args.len());
    args.splice(insertion..insertion, compiler_args);
    Ok(())
}

/// Merge Tippy's decoded compiler arguments into the actual execution argv and
/// parse that same vector for callback policy. This keeps classification and
/// execution identical while preserving rustc's option precedence and `--`
/// ownership.
fn merge_and_match_internal_compiler_args(
    execution_args: &mut Vec<String>,
    internal_compiler_args: &[String],
) -> Result<rustc_session::getopts::Matches, String> {
    insert_lint_compiler_args(execution_args, internal_compiler_args.iter().cloned())?;
    compiler_matches(execution_args)
}

fn same_directory(left: &Path, right: &Path) -> bool {
    left == right
}

fn invocation_executable_path() -> Option<PathBuf> {
    let path = env::current_exe().ok()?;
    fs::symlink_metadata(&path)
        .is_ok_and(|metadata| metadata_is_plain_file(&metadata))
        .then_some(path)
}

fn validate_branded_compiler_executable(compiler: &Path) -> Result<(), String> {
    if !compiler_path_is_valid(compiler, cfg!(windows)) {
        return Err(format!(
            "branded Tippy compiler `{}` is not the required `rustc` or `trustc` sibling",
            compiler.display()
        ));
    }
    let metadata = fs::symlink_metadata(compiler).map_err(|error| {
        format!(
            "branded Tippy compiler `{}` is unavailable: {error}; repair or reinstall the selected toolchain",
            compiler.display()
        )
    })?;
    if !metadata_is_plain_file(&metadata) {
        return Err(format!(
            "branded Tippy compiler `{}` is not a plain regular file; repair or reinstall the selected toolchain",
            compiler.display()
        ));
    }
    if !metadata_is_executable(&metadata) {
        return Err(format!(
            "branded Tippy compiler `{}` is not executable; repair or reinstall the selected toolchain",
            compiler.display()
        ));
    }
    Ok(())
}

#[cfg(unix)]
fn metadata_is_executable(metadata: &fs::Metadata) -> bool {
    use std::os::unix::fs::PermissionsExt as _;

    metadata.permissions().mode() & 0o111 != 0
}

#[cfg(not(unix))]
fn metadata_is_executable(_metadata: &fs::Metadata) -> bool {
    true
}

fn recognized_driver_brand(executable: &Path) -> Option<bool> {
    driver_brand_from_path(executable, cfg!(windows))
}

fn driver_brand_from_path(executable: &Path, windows_semantics: bool) -> Option<bool> {
    let matches = |expected| executable_path_matches_with_windows_semantics(executable, expected, windows_semantics);
    if matches("tippy-driver") {
        Some(true)
    } else if matches("clippy-driver") {
        Some(false)
    } else {
        None
    }
}

/// Return the sysroot selected by the branded Tippy frontend or driver.
///
/// Public Tippy invokes the public `tippy-driver` as a workspace wrapper and
/// selects a `rustc`/`trustc` sibling in the same `bin` directory. A direct
/// public `tippy-driver` invocation has no compiler argument to authenticate,
/// so it derives the same sysroot from its own executable. Deriving the sysroot
/// from that closed toolchain prevents project Cargo configuration or an
/// inherited `SYSROOT` from replacing it. Development `clippy-driver`
/// invocations deliberately retain their upstream environment behavior.
fn branded_driver_sysroot(args: &[String], current_exe: Option<&Path>) -> Result<Option<String>, String> {
    let raw_argv0 = args.first().map(String::as_str);
    let raw_brand = raw_argv0.and_then(|arg| recognized_driver_brand(Path::new(arg)));
    let Some(current_exe) = current_exe else {
        return match raw_brand {
            Some(false) => Ok(None),
            Some(true) => Err(
                "cannot authenticate the running Tippy driver executable; repair or reinstall the selected toolchain"
                    .to_string(),
            ),
            None => Err(format!(
                "cannot authenticate Tippy driver invocation `{}` without a recognized running or `clippy-driver` development identity",
                raw_argv0.unwrap_or_default()
            )),
        };
    };
    let current_brand = recognized_driver_brand(current_exe);
    if raw_brand
        .zip(current_brand)
        .is_some_and(|(raw, current)| raw != current)
    {
        return Err(format!(
            "invocation name `{}` conflicts with the running Tippy driver `{}`; executable identity, not argv[0], selects the toolchain",
            raw_argv0.unwrap_or_default(),
            current_exe.display()
        ));
    }
    if raw_brand == Some(true) && current_brand.is_none() {
        return Err(format!(
            "cannot authenticate branded Tippy driver invocation `{}` against the running executable",
            raw_argv0.unwrap_or_default()
        ));
    }
    let Some(current_brand) = current_brand else {
        return Err(format!(
            "running Tippy driver executable `{}` has an unrecognized name; expected `tippy-driver` or `clippy-driver`",
            current_exe.display()
        ));
    };
    let driver = current_exe;
    if !current_brand {
        return Ok(None);
    }
    let Some(driver_bin) = driver.parent().filter(|parent| !parent.as_os_str().is_empty()) else {
        return Err(format!(
            "cannot derive the selected Trust sysroot from branded driver `{}`",
            driver.display()
        ));
    };

    if is_compiler_wrapper_mode(args) {
        let compiler = Path::new(&args[1]);
        if !compiler.is_absolute() {
            return Err("branded Tippy requires an absolute sibling compiler path".into());
        }
        let Some(compiler_bin) = compiler.parent().filter(|parent| !parent.as_os_str().is_empty()) else {
            return Err("branded Tippy requires an absolute sibling compiler path".into());
        };
        if !same_directory(driver_bin, compiler_bin) {
            return Err(format!(
                "branded Tippy compiler `{}` is not a sibling of driver `{}`",
                compiler.display(),
                driver.display()
            ));
        }
        validate_branded_compiler_executable(compiler)?;
    }

    let Some(sysroot) = driver_bin.parent().filter(|parent| !parent.as_os_str().is_empty()) else {
        return Err(format!(
            "cannot derive the selected Trust sysroot from branded driver `{}`",
            driver.display()
        ));
    };
    let Some(sysroot) = sysroot.to_str() else {
        return Err(format!(
            "the selected Trust sysroot `{}` is not valid UTF-8",
            sysroot.display()
        ));
    };
    Ok(Some(sysroot.to_owned()))
}

/// Outer identity boundary for the public `tippy-driver` process.
///
/// Direct branded invocations do not have the Tippy frontend's compiler and
/// sibling guards around them. Bind the running driver plus the complete
/// launch/canonical directory chain that supplies its `bin` and sysroot, plus
/// the selected sibling `trustc`, then hold fresh handles and revalidate around
/// the entire embedded rustc driver.
/// This remains pathname execution: a raced resource can perform side effects
/// before the post-check rejects the result.
#[derive(Debug)]
struct AuthenticatedDriverExecution {
    sysroot: PathBuf,
    sysroot_directories: AuthenticatedDirectoryChain,
    bin_directories: AuthenticatedDirectoryChain,
    compiler_path: PathBuf,
    driver_executable: AuthenticatedExecutable,
    compiler_executable: AuthenticatedExecutable,
}

impl AuthenticatedDriverExecution {
    fn capture(driver: PathBuf) -> Result<Self, String> {
        let bin = driver
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
            .ok_or_else(|| {
                format!(
                    "branded Tippy driver `{}` has no selected toolchain bin directory",
                    driver.display()
                )
            })?
            .to_owned();
        let sysroot = bin
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
            .ok_or_else(|| {
                format!(
                    "branded Tippy driver `{}` has no selected sysroot directory",
                    driver.display()
                )
            })?
            .to_owned();
        // Capture the resolved sysroot root explicitly, in addition to the bin
        // path. The bin chain already traverses this object, but recording the
        // semantic root separately binds the path later passed to rustc and
        // makes that authority check reviewable rather than incidental.
        let sysroot_directories = AuthenticatedDirectoryChain::capture(&sysroot)?;
        let bin_directories = AuthenticatedDirectoryChain::capture(&bin)?;
        let mut compiler_path = bin.join("trustc");
        if cfg!(windows) {
            compiler_path.set_extension("exe");
        }
        let driver_executable = AuthenticatedExecutable::capture(driver, "tippy-driver")?;
        let compiler_executable = AuthenticatedExecutable::capture(compiler_path.clone(), "trustc")?;
        // Ensure the executable selection occurred within one stable directory
        // epoch rather than after an ancestor was redirected.
        let _ = bin_directories.revalidate()?;
        let _ = sysroot_directories.revalidate()?;
        Ok(Self {
            sysroot,
            sysroot_directories,
            bin_directories,
            compiler_path,
            driver_executable,
            compiler_executable,
        })
    }

    fn sysroot(&self) -> &Path {
        &self.sysroot
    }

    fn compiler_commit_hash(&self) -> Result<String, String> {
        self.run_guarded(|| query_compiler_commit_hash(&self.compiler_path))
            .and_then(|result| result)
    }

    fn run_guarded<T>(&self, operation: impl FnOnce() -> T) -> Result<T, String> {
        // The root and every directory-entry boundary are protected. Rustc
        // still opens nested sysroot files by pathname; an in-place rewrite of
        // a descendant file that leaves every recorded directory unchanged is
        // outside this process-identity guard.
        self.sysroot_directories
            .run_guarded_for("embedded Tippy compiler", || {
                self.bin_directories.run_guarded_for("embedded Tippy compiler", || {
                    self.driver_executable.run_guarded_for("embedded Tippy compiler", || {
                        self.compiler_executable
                            .run_guarded_for("embedded Tippy compiler", operation)
                    })
                })
            })
            .and_then(|result| result)
            .and_then(|result| result)
            .and_then(|result| result)
    }
}

/// Select the top-level driver route before interpreting rustc arguments.
///
/// Cargo's wrapper protocol puts the selected compiler in `argv[1]`, followed
/// by project-controlled rustc arguments. The former direct `--trustc` escape
/// hatch bypassed every lint callback and restored batteries-on proof
/// publication. Reject it in the only position where it was ever a Tippy
/// control; every accepted invocation remains on the no-evidence lint path.
fn driver_wrapper_mode(args: &[String]) -> Result<bool, String> {
    let wrapper_mode = is_compiler_wrapper_mode(args);
    if !wrapper_mode && args.get(1).is_some_and(|arg| arg == "--trustc") {
        return Err(
            "Tippy no longer exposes raw `--trustc` passthrough; invoke `trustc` directly for compiler semantics"
                .to_string(),
        );
    }
    Ok(wrapper_mode)
}

#[test]
fn repeatable_option_matches_rustc_first_value_precedence() {
    let allow_then_warn = ["tippy-driver", "--cap-lints=allow", "--cap-lints", "warn"].map(String::from);
    assert_eq!(
        compiler_matches(&allow_then_warn)
            .unwrap()
            .opt_str("cap-lints")
            .as_deref(),
        Some("allow")
    );

    let warn_then_allow = ["tippy-driver", "--cap-lints", "warn", "--cap-lints=allow"].map(String::from);
    assert_eq!(
        compiler_matches(&warn_then_allow)
            .unwrap()
            .opt_str("cap-lints")
            .as_deref(),
        Some("warn")
    );

    let after_separator = ["tippy-driver", "--cap-lints=warn", "--", "--cap-lints=allow"].map(String::from);
    assert_eq!(
        compiler_matches(&after_separator)
            .unwrap()
            .opt_str("cap-lints")
            .as_deref(),
        Some("warn")
    );
}

#[test]
fn policy_matching_combines_outer_and_v2_compiler_arguments_semantically() {
    let mut outer = ["tippy-driver", "--cap-lints=allow", "input.rs"]
        .map(String::from)
        .to_vec();
    let internal = ["--force-warn=clippy::pedantic"].map(String::from);
    let matches = merge_and_match_internal_compiler_args(&mut outer, &internal).unwrap();
    assert_eq!(matches.opt_str("cap-lints").as_deref(), Some("allow"));
    assert_eq!(matches.opt_strs("force-warn"), ["clippy::pedantic"]);
    assert_eq!(
        outer
            .iter()
            .filter(|arg| *arg == "--force-warn=clippy::pedantic")
            .count(),
        1
    );

    let mut outer = ["tippy-driver", "input.rs"].map(String::from).to_vec();
    let internal = ["--cap-lints", "allow", "--print=cfg"].map(String::from);
    let matches = merge_and_match_internal_compiler_args(&mut outer, &internal).unwrap();
    assert_eq!(matches.opt_str("cap-lints").as_deref(), Some("allow"));
    assert_eq!(matches.opt_strs("print"), ["cfg"]);
    assert_eq!(
        outer,
        ["tippy-driver", "input.rs", "--cap-lints", "allow", "--print=cfg"]
    );
}

#[test]
fn combined_policy_matching_respects_outer_precedence_and_semantic_separator() {
    let mut outer = ["tippy-driver", "--cap-lints=warn", "--", "--cap-lints=allow"]
        .map(String::from)
        .to_vec();
    let internal = ["--cap-lints=allow", "--force-warn=clippy::all"].map(String::from);
    let matches = merge_and_match_internal_compiler_args(&mut outer, &internal).unwrap();
    assert_eq!(
        matches.opt_str("cap-lints").as_deref(),
        Some("warn"),
        "the first semantic cap-lints value remains authoritative"
    );
    assert_eq!(matches.opt_strs("force-warn"), ["clippy::all"]);
    assert!(matches.free.iter().any(|arg| arg == "--cap-lints=allow"));
    assert_eq!(
        outer,
        [
            "tippy-driver",
            "--cap-lints=warn",
            "--cap-lints=allow",
            "--force-warn=clippy::all",
            "--",
            "--cap-lints=allow",
        ]
    );
}

#[test]
fn product_and_compiler_version_queries_are_distinct() {
    for flag in ["--version", "-V"] {
        let args = ["tippy-driver", flag].map(String::from);
        assert!(should_print_tippy_version(&compiler_matches(&args).unwrap(), false));
    }
    for flag in ["-vV", "-Vv"] {
        let args = ["tippy-driver", flag].map(String::from);
        assert!(!should_print_tippy_version(&compiler_matches(&args).unwrap(), false));
    }
}

#[test]
fn driver_and_compiler_names_require_complete_platform_valid_names() {
    assert_eq!(driver_brand_from_path(Path::new("TIPPY-DRIVER.EXE"), true), Some(true));
    assert_eq!(
        driver_brand_from_path(Path::new("ClIpPy-DrIvEr.ExE"), true),
        Some(false)
    );
    assert_eq!(driver_brand_from_path(Path::new("TIPPY-DRIVER"), false), None);
    assert!(compiler_path_is_valid(Path::new("TRUSTC.EXE"), true));
    assert!(!compiler_path_is_valid(Path::new("TRUSTC"), false));
    assert_eq!(driver_brand_from_path(Path::new("tippy-driver.backup"), false), None);
    assert_eq!(driver_brand_from_path(Path::new("tippy-driver.com"), true), None);
    assert!(!compiler_path_is_valid(Path::new("trustc.backup"), false));

    let wrapped = [
        "/toolchain/bin/TIPPY-DRIVER.EXE",
        "/toolchain/bin/TRUSTC.EXE",
        "--crate-name",
        "demo",
    ]
    .map(String::from);
    assert!(is_compiler_wrapper_mode_with_windows_semantics(&wrapped, true));
    assert!(!is_compiler_wrapper_mode_with_windows_semantics(&wrapped, false));
}

#[test]
fn direct_version_queries_are_distinct_from_wrapped_compiler_queries() {
    for flag in ["--version", "-V"] {
        let direct = ["/toolchain/bin/tippy-driver", flag].map(String::from);
        assert!(should_print_tippy_version(&compiler_matches(&direct).unwrap(), false));

        let wrapped = ["/toolchain/bin/tippy-driver", "/toolchain/bin/trustc", flag].map(String::from);
        assert!(is_compiler_wrapper_mode(&wrapped));
        let compiler_args = ["/toolchain/bin/tippy-driver", flag].map(String::from);
        assert!(!should_print_tippy_version(
            &compiler_matches(&compiler_args).unwrap(),
            true
        ));
    }

    // Combined verbose-version flags are rustc protocol queries. ui_test and
    // Cargo invoke the driver directly with these and must receive parseable
    // compiler metadata rather than Tippy's product version.
    for flag in ["-vV", "-Vv"] {
        let direct = ["/toolchain/bin/tippy-driver", flag].map(String::from);
        assert!(!should_print_tippy_version(&compiler_matches(&direct).unwrap(), false));
    }

    let source_file = ["/toolchain/bin/tippy-driver", "/src/trustc.rs", "-Vv"].map(String::from);
    assert!(!is_compiler_wrapper_mode(&source_file));
}

#[test]
fn compiler_policy_queries_use_getopts_separator_and_option_value_semantics() {
    let semantic_separator = ["tippy-driver", "--", "--cap-lints", "allow"].map(String::from);
    assert_eq!(
        compiler_matches(&semantic_separator).unwrap().opt_str("cap-lints"),
        None
    );

    let consumed_double_dash =
        ["tippy-driver", "--crate-name", "--", "--cap-lints=allow", "--print=cfg"].map(String::from);
    let matches = compiler_matches(&consumed_double_dash).unwrap();
    assert_eq!(matches.opt_str("cap-lints").as_deref(), Some("allow"));
    assert_eq!(matches.opt_strs("print"), ["cfg"]);
}

#[test]
fn response_files_drive_callback_and_sysroot_decisions_with_rustc_semantics() {
    use std::time::{SystemTime, UNIX_EPOCH};

    let _lock = DRIVER_IDENTITY_FIXTURE_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!("tippy-driver-argfiles-{}-{nonce}", std::process::id()));
    std::fs::create_dir(&root).expect("create response-file test directory");
    let regular = root.join("regular.args");
    let shell = root.join("shell.args");
    std::fs::write(&regular, "--cap-lints\nallow\n").expect("write regular argfile");
    std::fs::write(&shell, "--sysroot '/toolchain root' --print cfg\n").expect("write shell argfile");

    let early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());
    let args = [
        "/toolchain/bin/tippy-driver".to_string(),
        format!("@{}", regular.display()),
        "-Zshell-argfiles".to_string(),
        format!("@shell:{}", shell.display()),
    ];
    let expanded = expanded_args_snapshot(&early_dcx, &args);
    let matches = compiler_matches(&expanded).unwrap();
    assert_eq!(matches.opt_str("cap-lints").as_deref(), Some("allow"));
    assert_eq!(matches.opt_strs("print"), ["cfg"]);
    assert!(has_sysroot_arg(&matches));
    assert!(expanded.iter().any(|arg| arg == "/toolchain root"));

    std::fs::remove_dir_all(root).expect("remove response-file test directory");
}

#[test]
fn every_branded_driver_route_rejects_a_caller_selected_sysroot() {
    for args in [
        ["trustc", "--sysroot", "/attacker/sysroot"].map(String::from),
        ["trustc", "--sysroot=/attacker/sysroot", "input.rs"].map(String::from),
    ] {
        let matches = compiler_matches(&args).unwrap();
        assert!(branded_args_override_selected_sysroot(true, &matches));
        assert!(
            !branded_args_override_selected_sysroot(false, &matches),
            "the inherited clippy-driver development route retains upstream sysroot overrides"
        );
    }
}

#[test]
fn direct_trustc_passthrough_is_rejected_and_project_flags_cannot_select_a_route() {
    let direct = ["/toolchain/bin/tippy-driver", "--trustc", "--version"].map(String::from);
    assert!(
        driver_wrapper_mode(&direct)
            .unwrap_err()
            .contains("no longer exposes raw `--trustc` passthrough")
    );

    let wrapped = [
        "/toolchain/bin/tippy-driver",
        "/toolchain/bin/trustc",
        "--crate-name",
        "demo",
        "--trustc",
    ]
    .map(String::from);
    assert!(is_compiler_wrapper_mode(&wrapped));
    assert_eq!(
        driver_wrapper_mode(&wrapped),
        Ok(true),
        "a trailing project rustflag must remain on the normal lint-callback path"
    );

    let misplaced = ["/toolchain/bin/tippy-driver", "input.rs", "--trustc"].map(String::from);
    assert_eq!(driver_wrapper_mode(&misplaced), Ok(false));
}

#[test]
fn branded_driver_derives_only_its_own_toolchain_sysroot() {
    use std::time::{SystemTime, UNIX_EPOCH};

    let _lock = DRIVER_IDENTITY_FIXTURE_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = env::temp_dir().join(format!("tippy-driver-toolchain-{}-{nonce}", std::process::id()));
    let sysroot = root.join("toolchain");
    let bin = sysroot.join("bin");
    fs::create_dir_all(&bin).expect("create selected toolchain bin");
    let current_exe = bin.join("tippy-driver");
    let compiler = bin.join("trustc");
    write_test_executable(&current_exe);
    write_test_executable(&compiler);
    let evil_compiler = bin.join("evil-compiler");
    write_test_executable(&evil_compiler);
    assert!(
        validate_branded_compiler_executable(&evil_compiler)
            .expect_err("an arbitrary executable sibling is not a Trust compiler")
            .contains("required `rustc` or `trustc`")
    );

    let branded = vec![
        current_exe.to_string_lossy().into_owned(),
        compiler.to_string_lossy().into_owned(),
        "--crate-name".into(),
        "demo".into(),
    ];
    assert_eq!(
        branded_driver_sysroot(&branded, Some(&current_exe)),
        Ok(Some(sysroot.to_string_lossy().into_owned()))
    );

    let mixed = vec![
        current_exe.to_string_lossy().into_owned(),
        root.join("attacker/bin/rustc").to_string_lossy().into_owned(),
        "--crate-name".into(),
        "demo".into(),
    ];
    assert!(
        branded_driver_sysroot(&mixed, Some(&current_exe))
            .unwrap_err()
            .contains("not a sibling")
    );

    for direct in [
        vec![
            current_exe.to_string_lossy().into_owned(),
            "--trustc".into(),
            "--version".into(),
        ],
        vec![current_exe.to_string_lossy().into_owned(), "input.rs".into()],
    ] {
        assert_eq!(
            branded_driver_sysroot(&direct, Some(&current_exe)),
            Ok(Some(sysroot.to_string_lossy().into_owned()))
        );
    }

    let relative = ["tippy-driver", "trustc", "--crate-name", "demo"].map(String::from);
    assert!(
        branded_driver_sysroot(&relative, Some(&current_exe))
            .expect_err("relative compiler paths must fail closed")
            .contains("absolute")
    );

    let lexical_alias = vec![
        current_exe.to_string_lossy().into_owned(),
        bin.join("../bin/trustc").to_string_lossy().into_owned(),
        "--crate-name".into(),
        "demo".into(),
    ];
    assert!(
        branded_driver_sysroot(&lexical_alias, Some(&current_exe))
            .expect_err("the compiler must use the exact sibling directory")
            .contains("not a sibling")
    );

    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;

        let rustc = bin.join("rustc");
        symlink(&compiler, &rustc).expect("create compiler symlink fixture");
        let symlinked = vec![
            current_exe.to_string_lossy().into_owned(),
            rustc.to_string_lossy().into_owned(),
            "--crate-name".into(),
            "demo".into(),
        ];
        assert!(
            branded_driver_sysroot(&symlinked, Some(&current_exe))
                .expect_err("a branded compiler symlink must fail closed")
                .contains("not a plain regular file")
        );
    }

    let inherited = [
        // The converse spoof must not promote a development clippy-driver to
        // the branded policy merely by changing argv[0].
        "/toolchain/bin/tippy-driver",
        "/attacker/bin/rustc",
        "--crate-name",
        "demo",
    ]
    .map(String::from);
    assert_eq!(
        branded_driver_sysroot(&inherited, Some(Path::new("/toolchain/bin/clippy-driver")))
            .expect_err("raw branding must conflict with a development executable")
            .contains("conflicts"),
        true
    );

    let conflicting = ["/toolchain/bin/clippy-driver", "input.rs"].map(String::from);
    assert!(
        branded_driver_sysroot(&conflicting, Some(&current_exe))
            .expect_err("raw development branding must conflict with the public driver")
            .contains("conflicts")
    );

    let development = ["clippy-driver", "input.rs"].map(String::from);
    assert_eq!(branded_driver_sysroot(&development, None), Ok(None));
    let unauthenticated_public = ["tippy-driver", "input.rs"].map(String::from);
    assert!(
        branded_driver_sysroot(&unauthenticated_public, None)
            .expect_err("an unauthenticated public driver must fail closed")
            .contains("cannot authenticate")
    );
    for (raw, current) in [
        ("renamed-driver", Some(Path::new("/toolchain/bin/renamed-driver"))),
        ("clippy-driver", Some(Path::new("/toolchain/bin/renamed-driver"))),
        (
            "tippy-driver.backup",
            Some(Path::new("/toolchain/bin/tippy-driver.backup")),
        ),
        ("renamed-driver", None),
    ] {
        let args = [raw, "input.rs"].map(String::from);
        let error = branded_driver_sysroot(&args, current)
            .expect_err("an unknown driver executable must not enter ambient development mode");
        assert!(
            error.contains("unrecognized name") || error.contains("without a recognized"),
            "{error}"
        );
    }

    fs::remove_dir_all(root).expect("remove selected toolchain fixture");
}

#[cfg(test)]
static DRIVER_IDENTITY_FIXTURE_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

#[cfg(test)]
fn write_test_executable(path: &Path) {
    fs::write(path, b"executable fixture").expect("write executable fixture");
    make_test_executable(path);
}

#[cfg(test)]
fn make_test_executable(path: &Path) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        let mut permissions = fs::metadata(path).expect("fixture metadata").permissions();
        permissions.set_mode(0o700);
        fs::set_permissions(path, permissions).expect("make fixture executable");
    }
}

#[cfg(unix)]
#[test]
fn raw_symlink_path_cannot_relocate_the_branded_driver_toolchain() {
    use std::os::unix::fs::symlink;
    use std::time::{SystemTime, UNIX_EPOCH};

    let _lock = DRIVER_IDENTITY_FIXTURE_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let root = env::temp_dir().join(format!("tippy-driver-symlink-{}-{nonce}", std::process::id()));
    let real_bin = root.join("real/bin");
    let selected_bin = root.join("selected/bin");
    std::fs::create_dir_all(&real_bin).expect("create real toolchain bin");
    std::fs::create_dir_all(&selected_bin).expect("create selected toolchain bin");
    let real_driver = real_bin.join("tippy-driver");
    let selected_driver = selected_bin.join("tippy-driver");
    write_test_executable(&real_driver);
    write_test_executable(&real_bin.join("rustc"));
    symlink(&real_driver, &selected_driver).expect("link selected driver");

    let args = [
        selected_driver.to_str().expect("UTF-8 test path"),
        real_bin.join("rustc").to_str().expect("UTF-8 test compiler path"),
        "--crate-name",
        "demo",
    ]
    .map(String::from);
    assert_eq!(
        branded_driver_sysroot(&args, Some(&real_driver)),
        Ok(Some(root.join("real").to_str().expect("UTF-8 test sysroot").into()))
    );

    std::fs::remove_dir_all(root).expect("remove symlink toolchain fixture");
}

#[cfg(unix)]
#[test]
fn direct_branded_driver_guard_rejects_ancestor_redirect_restore_after_raced_process_runs() {
    use std::os::unix::fs::symlink;
    use std::process::Command;
    use std::time::{SystemTime, UNIX_EPOCH};

    let _lock = DRIVER_IDENTITY_FIXTURE_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let temp = env::temp_dir().canonicalize().unwrap_or_else(|_| env::temp_dir());
    let root = temp.join(format!("tippy-driver-ancestor-race-{}-{nonce}", std::process::id()));
    let selected_root = root.join("selected");
    let selected_bin = selected_root.join("bin");
    let attacker_root = root.join("attacker");
    let attacker_bin = attacker_root.join("bin");
    fs::create_dir_all(&selected_bin).expect("create selected driver directory");
    fs::create_dir_all(&attacker_bin).expect("create attacker driver directory");
    let driver = selected_bin.join("tippy-driver");
    fs::write(&driver, b"#!/bin/sh\nexit 0\n").expect("write selected driver");
    make_test_executable(&driver);
    let compiler = selected_bin.join("trustc");
    fs::write(&compiler, b"#!/bin/sh\nexit 0\n").expect("write selected compiler");
    make_test_executable(&compiler);
    let hostile_driver = attacker_bin.join("tippy-driver");
    fs::write(&hostile_driver, b"#!/bin/sh\nexit 23\n").expect("write hostile driver");
    make_test_executable(&hostile_driver);
    let saved_root = root.join("selected-saved");

    let authenticated = AuthenticatedDriverExecution::capture(driver.clone())
        .expect("authenticate direct branded driver and directory chain");
    let mut hostile_process_ran = false;
    let result = authenticated.run_guarded(|| {
        fs::rename(&selected_root, &saved_root).expect("save selected driver root");
        symlink(&attacker_root, &selected_root).expect("redirect selected driver root");
        let status = Command::new(&driver)
            .status()
            .expect("run driver through redirected pathname");
        hostile_process_ran = status.code() == Some(23);
        fs::remove_file(&selected_root).expect("remove attacker redirect");
        fs::rename(&saved_root, &selected_root).expect("restore exact selected driver root");
    });

    assert!(hostile_process_ran, "fixture did not execute the redirected driver");
    assert!(
        result.is_err(),
        "an ancestor redirect-and-restore escaped direct branded driver authentication"
    );
    drop(authenticated);
    fs::remove_dir_all(root).expect("remove direct-driver ancestor-race fixture");
}

#[cfg(unix)]
#[test]
fn direct_branded_driver_queries_the_authenticated_sibling_compiler_full_commit() {
    use std::time::{SystemTime, UNIX_EPOCH};

    let _lock = DRIVER_IDENTITY_FIXTURE_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after Unix epoch")
        .as_nanos();
    let temp = env::temp_dir().canonicalize().unwrap_or_else(|_| env::temp_dir());
    let root = temp.join(format!("tippy-driver-compiler-version-{}-{nonce}", std::process::id()));
    let bin = root.join("bin");
    fs::create_dir_all(&bin).expect("create selected driver directory");
    let driver = bin.join("tippy-driver");
    fs::write(&driver, b"#!/bin/sh\nexit 0\n").expect("write selected driver");
    make_test_executable(&driver);
    let compiler = bin.join("trustc");
    fs::write(
        &compiler,
        b"#!/bin/sh\n[ \"$1\" = \"-vV\" ] || exit 2\nprintf '%s\\n' 'rustc 1.99.0-dev' 'commit-hash: 0123456789abcdef0123456789abcdef01234567'\n",
    )
    .expect("write selected compiler");
    make_test_executable(&compiler);

    let authenticated =
        AuthenticatedDriverExecution::capture(driver).expect("authenticate direct branded driver and sibling compiler");
    assert_eq!(
        authenticated.compiler_commit_hash(),
        Ok("0123456789abcdef0123456789abcdef01234567".to_owned())
    );

    drop(authenticated);
    fs::remove_dir_all(root).expect("remove direct-driver compiler-version fixture");
}

#[test]
fn frontend_owned_compiler_args_do_not_split_an_option_from_its_double_dash_value() {
    let mut args = ["tippy-driver", "--crate-name", "--", "--print=cfg"]
        .map(String::from)
        .to_vec();
    insert_compiler_args_after_program(&mut args, ["--sysroot".into(), "/toolchain".into()]);
    assert_eq!(
        args,
        [
            "tippy-driver",
            "--sysroot",
            "/toolchain",
            "--crate-name",
            "--",
            "--print=cfg"
        ]
    );
    let matches = compiler_matches(&args).unwrap();
    assert_eq!(matches.opt_str("crate-name").as_deref(), Some("--"));
    assert_eq!(matches.opt_str("sysroot").as_deref(), Some("/toolchain"));
    assert_eq!(matches.opt_strs("print"), ["cfg"]);
}

#[test]
fn lint_args_keep_tail_precedence_after_multiple_consumed_double_dashes() {
    let mut args = [
        "tippy-driver",
        "-Awarnings",
        "--crate-name",
        "--",
        "--out-dir",
        "--",
        "--",
        "literal-input",
    ]
    .map(String::from)
    .to_vec();

    assert_eq!(compiler_semantic_separator(&args).unwrap(), Some(6));
    insert_lint_compiler_args(&mut args, ["-Dwarnings".into()]).unwrap();
    assert_eq!(
        args,
        [
            "tippy-driver",
            "-Awarnings",
            "--crate-name",
            "--",
            "--out-dir",
            "--",
            "-Dwarnings",
            "--",
            "literal-input",
        ],
        "Tippy's requested lint level must remain later than Cargo/RUSTFLAGS while every option/value pair stays intact"
    );
}

#[test]
fn branded_internal_arg_channel_cannot_reselect_the_toolchain() {
    for args in [
        vec!["--sysroot".into(), "/attacker".into()],
        vec!["--sysroot=/attacker".into()],
    ] {
        assert!(
            internal_tippy_args_override_toolchain(&args).unwrap(),
            "accepted {args:?}"
        );
    }
    assert!(
        !internal_tippy_args_override_toolchain(&["-Wclippy::pedantic".into(), "--cfg=feature=\"demo\"".into(),])
            .unwrap()
    );
}

#[test]
fn tippy_frontend_controls_are_removed_before_compiler_option_parsing() {
    let (no_deps, compiler_args) = resolve_tippy_frontend_args(DecodedTippyArgs {
        no_deps: NoDepsFlag::LegacyInBand,
        compiler_args: vec!["--no-deps".into(), "-Wclippy::pedantic".into(), "--no-deps".into()],
    })
    .unwrap();
    assert!(no_deps);
    assert_eq!(compiler_args, ["-Wclippy::pedantic"]);
    assert!(!internal_tippy_args_override_toolchain(&compiler_args).unwrap());
}

#[test]
fn internal_arg_channels_cannot_introduce_response_files() {
    for args in [
        vec!["@attacker.args".into()],
        vec!["@shell:attacker.args".into()],
        vec!["@".into()],
        vec!["--".into(), "@after-separator.args".into()],
    ] {
        assert!(has_response_file_arg(&args), "accepted {args:?}");
    }
    assert!(!has_response_file_arg(&[
        "-Wclippy::pedantic".into(),
        "--cfg=feature=\"demo\"".into(),
    ]));
}

fn decode_tippy_arg_channel(encoded_args: Option<&str>, legacy_args: Option<&str>) -> Result<DecodedTippyArgs, String> {
    if let Some(encoded_args) = encoded_args {
        return decode_args(encoded_args);
    }

    Ok(DecodedTippyArgs {
        no_deps: NoDepsFlag::LegacyInBand,
        compiler_args: legacy_args
            .unwrap_or_default()
            .split("__CLIPPY_HACKERY__")
            .filter(|arg| !arg.is_empty())
            .map(str::to_string)
            .collect(),
    })
}

fn resolve_tippy_frontend_args(payload: DecodedTippyArgs) -> Result<(bool, Vec<String>), String> {
    match payload.no_deps {
        NoDepsFlag::Explicit(no_deps) => Ok((no_deps, payload.compiler_args)),
        NoDepsFlag::LegacyInBand => split_legacy_no_deps(payload.compiler_args),
    }
}

fn unicode_env_var(name: &str) -> Result<Option<String>, String> {
    match env::var(name) {
        Ok(value) => Ok(Some(value)),
        Err(env::VarError::NotPresent) => Ok(None),
        Err(env::VarError::NotUnicode(value)) => Err(format!("{name} is not valid UTF-8: {value:?}")),
    }
}

#[test]
fn versioned_arg_channel_wins_and_preserves_exact_boundaries() {
    let args = [
        "-Wclippy::pedantic__CLIPPY_HACKERY__-Aclippy::all",
        "",
        "--cfg=feature=\"λ\"",
    ]
    .map(String::from);
    let encoded = arg_protocol::encode_args(false, &args);

    assert_eq!(
        decode_tippy_arg_channel(Some(&encoded), Some("attacker__CLIPPY_HACKERY__fallback")),
        Ok(DecodedTippyArgs {
            no_deps: NoDepsFlag::Explicit(false),
            compiler_args: args.to_vec(),
        })
    );
}

#[test]
fn malformed_versioned_arg_channel_never_falls_back_to_legacy_data() {
    assert!(decode_tippy_arg_channel(Some("tippy-args-v2;1:a"), Some("-Aclippy::all")).is_err());
}

#[test]
fn explicit_v2_no_deps_never_reinterprets_exact_compiler_arguments() {
    let payload = DecodedTippyArgs {
        no_deps: NoDepsFlag::Explicit(true),
        compiler_args: vec!["--cfg".into(), "--no-deps".into()],
    };
    assert_eq!(
        resolve_tippy_frontend_args(payload),
        Ok((true, vec!["--cfg".into(), "--no-deps".into()]))
    );
}

#[test]
fn legacy_no_deps_resolution_is_option_arity_aware() {
    let payload = DecodedTippyArgs {
        no_deps: NoDepsFlag::LegacyInBand,
        compiler_args: ["--cfg", "--no-deps", "--no-deps", "-Wclippy::all"]
            .map(String::from)
            .to_vec(),
    };
    assert_eq!(
        resolve_tippy_frontend_args(payload),
        Ok((true, ["--cfg", "--no-deps", "-Wclippy::all"].map(String::from).to_vec()))
    );
}

#[cfg(unix)]
#[test]
// Blessed `env_mutation` site: single test mutating a private key it restores.
#[allow(unknown_lints, env_mutation)]
fn non_unicode_internal_argument_environment_is_rejected() {
    use std::os::unix::ffi::OsStringExt as _;

    let name = "TIPPY_TEST_NON_UNICODE_ARGUMENTS";
    let saved = env::var_os(name);
    // SAFETY: this test restores the variable before returning. The Tippy test
    // binary does not otherwise use this private key.
    unsafe { env::set_var(name, std::ffi::OsString::from_vec(vec![0xff])) };
    let error = unicode_env_var(name).expect_err("non-Unicode argument channel must fail");
    // SAFETY: see the restoration guarantee above.
    unsafe {
        if let Some(saved) = saved {
            env::set_var(name, saved);
        } else {
            env::remove_var(name);
        }
    }

    assert!(error.contains("is not valid UTF-8"), "{error}");
}

fn track_clippy_args(sess: &Session, args_env_var: Option<&str>, encoded_args_env_var: Option<&str>) {
    let mut env_depinfo = sess.env_depinfo.borrow_mut();
    env_depinfo.insert((sym::CLIPPY_ARGS, args_env_var.map(Symbol::intern)));
    env_depinfo.insert((
        Symbol::intern(TIPPY_ENCODED_ARGS_ENV),
        encoded_args_env_var.map(Symbol::intern),
    ));
}

/// Track files that may be accessed at runtime in `file_depinfo` so that cargo will re-run clippy
/// when any of them are modified
fn track_files(sess: &Session) {
    let mut file_depinfo = sess.file_depinfo.borrow_mut();

    // Used by `clippy::cargo` lints and to determine the MSRV. `cargo clippy` executes `clippy-driver`
    // with the current directory set to `CARGO_MANIFEST_DIR` so a relative path is fine
    if Path::new("Cargo.toml").exists() {
        file_depinfo.insert(sym::Cargo_toml);
    }

    // `clippy.toml` will be automatically tracked as it's loaded with `sess.source_map().load_file()`

    // During development track the `clippy-driver` executable so that cargo will re-run clippy whenever
    // it is rebuilt
    if cfg!(debug_assertions)
        && let Ok(current_exe) = env::current_exe()
        && let Some(current_exe) = current_exe.to_str()
    {
        file_depinfo.insert(Symbol::intern(current_exe));
    }
}

/// Inform Cargo that both Tippy argument channels participate in this unit's
/// tracked inputs even when lint callbacks are disabled for the invocation.
struct RustcCallbacks {
    clippy_args_var: Option<String>,
    tippy_encoded_args_var: Option<String>,
}

impl rustc_driver::Callbacks for RustcCallbacks {
    fn config(&mut self, config: &mut interface::Config) {
        let clippy_args_var = self.clippy_args_var.take();
        let tippy_encoded_args_var = self.tippy_encoded_args_var.take();
        config.track_state = Some(Box::new(move |sess| {
            track_clippy_args(sess, clippy_args_var.as_deref(), tippy_encoded_args_var.as_deref());
        }));
        config.extra_symbols = sym::EXTRA_SYMBOLS.into();
    }
}

struct ClippyCallbacks {
    clippy_args_var: Option<String>,
    tippy_encoded_args_var: Option<String>,
}

impl rustc_driver::Callbacks for ClippyCallbacks {
    #[expect(rustc::bad_opt_access, reason = "necessary in clippy driver to set `mir_opt_level`")]
    fn config(&mut self, config: &mut interface::Config) {
        let conf_path = clippy_config::lookup_conf_file();
        let previous = config.register_lints.take();
        let clippy_args_var = self.clippy_args_var.take();
        let tippy_encoded_args_var = self.tippy_encoded_args_var.take();
        config.track_state = Some(Box::new(move |sess| {
            track_clippy_args(sess, clippy_args_var.as_deref(), tippy_encoded_args_var.as_deref());
            track_files(sess);

            // Trigger a rebuild if CLIPPY_CONF_DIR changes. The value must be a valid string so
            // changes between dirs that are invalid UTF-8 will not trigger rebuilds
            sess.env_depinfo.borrow_mut().insert((
                sym::CLIPPY_CONF_DIR,
                env::var("CLIPPY_CONF_DIR").ok().map(|dir| Symbol::intern(&dir)),
            ));
        }));
        config.register_lints = Some(Box::new(move |sess, lint_store| {
            // technically we're ~guaranteed that this is none but might as well call anything that
            // is there already. Certainly it can't hurt.
            if let Some(previous) = &previous {
                (previous)(sess, lint_store);
            }

            let mut list_builder = LintListBuilder::default();
            list_builder.insert(clippy_lints::declared_lints::LINTS);
            list_builder.register(lint_store);

            let conf = clippy_config::Conf::read(sess, &conf_path);
            clippy_lints::register_lint_passes(lint_store, conf);

            #[cfg(feature = "internal")]
            clippy_lints_internal::register_lints(lint_store);
        }));
        config.extra_symbols = sym::EXTRA_SYMBOLS.into();

        // FIXME: #4825; This is required, because Clippy lints that are based on MIR have to be
        // run on the unoptimized MIR. On the other hand this results in some false negatives. If
        // MIR passes can be enabled / disabled separately, we should figure out, what passes to
        // use for Clippy.
        config.opts.unstable_opts.mir_opt_level = Some(0);
        config.opts.unstable_opts.mir_enable_passes =
            vec![("CheckNull".to_owned(), false), ("CheckAlignment".to_owned(), false)];

        // Disable flattening and inlining of format_args!(), so the HIR matches with the AST.
        config.opts.unstable_opts.flatten_format_args = false;
    }
}

fn run_compiler_args(args: &[String], callbacks: &mut (dyn rustc_driver::Callbacks + Send)) {
    // Tippy changes proof-relevant compiler state in its callbacks. Enter
    // rustc through the typed no-evidence boundary before callback authority
    // is captured; no accepted Tippy route can lower or publish TrustIR/proof
    // evidence.
    rustc_driver::run_compiler_with_expanded_args_and_no_trust_evidence(args, callbacks, rustc_driver::NoTrustEvidence);
}

fn strip_overlay_process_environment() {
    // SAFETY: `main` calls this before logger initialization, ICE-hook
    // installation, argument expansion, or any compiler worker can start.
    // No other thread exists yet, and neither variable is read again from the
    // process environment: the owned snapshot is the only accepted input.
    unsafe {
        env::remove_var(HOST_DIR_ENV);
        env::remove_var(TARGET_DIR_ENV);
    }
}

fn display_help() -> ExitCode {
    if writeln!(&mut anstream::stdout().lock(), "{}", help_message_for_display()).is_err() {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

const BUG_REPORT_URL: &str = concat!(
    "https://github.com/alabsystems/Trust/issues/new",
    "?labels=C-bug%2CT-tippy",
);

fn main() -> ExitCode {
    let overlay_environment = OverlayEnvironment::capture();
    strip_overlay_process_environment();
    let early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());

    rustc_driver::init_rustc_env_logger(&early_dcx);

    rustc_driver::install_ice_hook_with_default_compiler(BUG_REPORT_URL, "tippy-driver", |dcx| {
        // FIXME: this macro calls unwrap internally but is called in a panicking context!  It's not
        // as simple as moving the call from the hook to main, because `install_ice_hook` doesn't
        // accept a generic closure.
        let version_info = clippy_version_info_for_display();
        dcx.handle().note(format!("Tippy version: {version_info}"));
    });

    let current_exe = invocation_executable_path();
    let authenticated_driver = match current_exe.as_deref().and_then(recognized_driver_brand) {
        Some(true) => match AuthenticatedDriverExecution::capture(
            current_exe.clone().expect("recognized driver has an executable path"),
        ) {
            Ok(authenticated) => Some(authenticated),
            Err(error) => {
                eprintln!("error: invalid branded Tippy driver identity: {error}");
                return ExitCode::FAILURE;
            },
        },
        _ => None,
    };
    let authenticated_sysroot = authenticated_driver
        .as_ref()
        .map(|authenticated| authenticated.sysroot().to_owned());
    let authenticated_compiler_commit_hash = if overlay_environment.is_configured() {
        match authenticated_driver.as_ref() {
            Some(authenticated) => match authenticated.compiler_commit_hash() {
                Ok(hash) => Some(hash),
                Err(error) => {
                    eprintln!("error: cannot authenticate selected Trust compiler version: {error}");
                    return ExitCode::FAILURE;
                },
            },
            None => None,
        }
    } else {
        None
    };

    let run_driver = move || {
        rustc_driver::catch_with_exit_code(move || {
            let mut orig_args = rustc_driver::args::raw_args(&early_dcx);
            let wrapper_mode = driver_wrapper_mode(&orig_args).unwrap_or_else(|error| early_dcx.early_fatal(error));

            let branded_sysroot = branded_driver_sysroot(&orig_args, current_exe.as_deref()).unwrap_or_else(|error| {
                early_dcx.early_fatal(format!("invalid branded Tippy toolchain selection: {error}"))
            });
            if let Some(expected) = authenticated_sysroot.as_deref()
                && branded_sysroot.as_deref().map(Path::new) != Some(expected)
            {
                early_dcx.early_fatal(format!(
                    "derived branded Tippy sysroot `{}` does not match the authenticated sysroot `{}`",
                    branded_sysroot.as_deref().unwrap_or_default(),
                    expected.display()
                ));
            }
            let branded_driver = branded_sysroot.is_some();
            let configured_overlay = ConfiguredOverlay::for_driver(
                branded_sysroot.as_deref().map(Path::new),
                authenticated_compiler_commit_hash.as_deref(),
                rustc_interface::util::rustc_version_str(),
                overlay_environment.clone(),
            )
            .unwrap_or_else(|error| early_dcx.early_fatal(format!("invalid Tippy rustc-private overlay: {error}")));

            // A branded invocation never trusts the child environment's SYSROOT:
            // Cargo project configuration can forcibly replace it. The sibling
            // compiler path above is the authoritative toolchain selection.
            let sys_root_env = if branded_driver {
                branded_sysroot.clone()
            } else {
                unicode_env_var("SYSROOT").unwrap_or_else(|error| early_dcx.early_fatal(error))
            };
            let pass_sysroot_if_given =
                |args: &mut Vec<String>, matches: &rustc_session::getopts::Matches, sys_root: Option<&str>| {
                    if let Some(sys_root) = sys_root
                        && !has_sysroot_arg(matches)
                    {
                        insert_compiler_args_after_program(args, ["--sysroot".to_string(), sys_root.to_owned()]);
                    }
                };

            // Setting RUSTC_WRAPPER causes Cargo to pass the configured compiler as
            // the first argument. Trust's public compiler name is `trustc`.
            // We're invoking the compiler programmatically, so we ignore this.
            if wrapper_mode {
                // we still want to be able to invoke it normally though
                orig_args.remove(1);
            }

            let inspected_args = expanded_args_snapshot(&early_dcx, &orig_args);
            let matches = compiler_matches(&inspected_args).unwrap_or_else(|error| early_dcx.early_fatal(error));

            if should_print_tippy_version(&matches, wrapper_mode) {
                let version_info = clippy_version_info_for_display();

                return match writeln!(&mut anstream::stdout().lock(), "{version_info}") {
                    Ok(()) => ExitCode::SUCCESS,
                    Err(_) => ExitCode::FAILURE,
                };
            }

            if !wrapper_mode && (matches.opt_present("h") || matches.opt_present("help") || inspected_args.len() == 1) {
                return display_help();
            }

            let mut args = inspected_args.clone();
            if branded_args_override_selected_sysroot(branded_sysroot.is_some(), &matches) {
                early_dcx.early_fatal(
                    "branded Tippy rejects project-controlled `--sysroot`; the selected toolchain fixes the sysroot",
                );
            }
            pass_sysroot_if_given(&mut args, &matches, sys_root_env.as_deref());

            let clippy_args_var = unicode_env_var(CLIPPY_ARGS_ENV).unwrap_or_else(|error| early_dcx.early_fatal(error));
            let tippy_encoded_args_var =
                unicode_env_var(TIPPY_ENCODED_ARGS_ENV).unwrap_or_else(|error| early_dcx.early_fatal(error));
            let encoded_tippy_args =
                decode_tippy_arg_channel(tippy_encoded_args_var.as_deref(), clippy_args_var.as_deref()).unwrap_or_else(
                    |error| {
                        early_dcx.early_fatal(format!("invalid internal {TIPPY_ENCODED_ARGS_ENV} payload: {error}"))
                    },
                );
            if has_response_file_arg(&encoded_tippy_args.compiler_args) {
                early_dcx.early_fatal(
                "Tippy rejects response files in CLIPPY_ARGS/TIPPY_ENCODED_ARGS; pass explicit compiler arguments instead",
            );
            }
            let (no_deps, internal_compiler_args) =
                resolve_tippy_frontend_args(encoded_tippy_args).unwrap_or_else(|error| early_dcx.early_fatal(error));
            if branded_driver
                && internal_tippy_args_override_toolchain(&internal_compiler_args)
                    .unwrap_or_else(|error| early_dcx.early_fatal(error))
            {
                early_dcx.early_fatal("branded Tippy rejects `--sysroot` in its internal compiler-argument channel");
            }
            let semantic_matches = merge_and_match_internal_compiler_args(&mut args, &internal_compiler_args)
                .unwrap_or_else(|error| early_dcx.early_fatal(error));

            // If no Clippy lints will be run we do not need to run Clippy
            let cap_lints_allow = semantic_matches.opt_str("cap-lints").as_deref() == Some("allow")
                && !semantic_matches
                    .opt_strs("force-warn")
                    .iter()
                    .any(|value| value.contains("clippy::"));

            // If `--no-deps` is enabled only lint the primary package
            let relevant_package = !no_deps || env::var("CARGO_PRIMARY_PACKAGE").is_ok();

            // Do not register Clippy for compiler information queries. The
            // decoded compiler channel is still part of the actual rustc argv;
            // classification must never make those arguments disappear.
            let info_query = semantic_matches.opt_present("version")
                || semantic_matches.opt_strs("print").iter().any(|value| {
                    value.split_once('=').map_or(value.as_str(), |(request, _)| request) != "crate-root-lint-levels"
                });

            let clippy_enabled = !cap_lints_allow && relevant_package && !info_query;
            if clippy_enabled {
                insert_lint_compiler_args(&mut args, ["--cfg".into(), "clippy".into()])
                    .unwrap_or_else(|error| early_dcx.early_fatal(error));
            }
            let crate_name = semantic_matches.opt_str("crate-name");
            let prepared_args: Option<PreparedCompilerArgs> = if crate_name.as_deref().is_some_and(crate_uses_overlay) {
                let overlay = configured_overlay.as_ref().unwrap_or_else(|| {
                    early_dcx.early_fatal(format!(
                        "crate `{}` requires the authenticated Tippy rustc-private overlay; configure both {HOST_DIR_ENV} and {TARGET_DIR_ENV}",
                        crate_name.as_deref().unwrap_or_default()
                    ))
                });
                overlay
                    .prepare_compiler_args(crate_name.as_deref(), &args)
                    .unwrap_or_else(|error| {
                        early_dcx.early_fatal(format!(
                            "cannot prepare Tippy rustc-private overlay for crate `{}`: {error}",
                            crate_name.as_deref().unwrap_or_default()
                        ))
                    })
            } else {
                None
            };
            let execution_args = prepared_args
                .as_ref()
                .map_or(args.as_slice(), PreparedCompilerArgs::args);
            if clippy_enabled {
                run_compiler_args(
                    execution_args,
                    &mut ClippyCallbacks {
                        clippy_args_var,
                        tippy_encoded_args_var,
                    },
                );
            } else {
                run_compiler_args(
                    execution_args,
                    &mut RustcCallbacks {
                        clippy_args_var,
                        tippy_encoded_args_var,
                    },
                );
            }
            ExitCode::SUCCESS
        })
    };

    if let Some(authenticated_driver) = authenticated_driver {
        match authenticated_driver.run_guarded(run_driver) {
            Ok(code) => code,
            Err(error) => {
                eprintln!("error: branded Tippy driver identity changed: {error}");
                ExitCode::FAILURE
            },
        }
    } else {
        run_driver()
    }
}

#[must_use]
fn help_message() -> &'static str {
    color_print::cstr!(
        "Checks a file to catch common mistakes and improve your Rust code.
Run <cyan>tippy-driver</> with the same arguments you use for <cyan>trustc</>

<green,bold>Usage</>:
    <cyan,bold>tippy-driver</> <cyan>[OPTIONS] INPUT</>

<green,bold>Common options:</>
    <cyan,bold>-h</>, <cyan,bold>--help</>               Print this message
    <cyan,bold>-V</>, <cyan,bold>--version</>            Print version info and exit
<green,bold>Allowing / Denying lints</>
You can use tool lints to allow or deny lints from your code, e.g.:

    <yellow,bold>#[allow(clippy::needless_lifetimes)]</>
"
    )
}

fn display_binary_name(default: &str) -> String {
    env::args()
        .next()
        .filter(|arg| recognized_driver_brand(Path::new(arg)).is_some())
        .and_then(|arg| Path::new(&arg).file_stem().map(|name| name.to_owned()))
        .and_then(|name| name.into_string().ok())
        .unwrap_or_else(|| default.to_owned())
}

fn clippy_version_info_for_display() -> String {
    rustc_tools_util::get_version_info!().to_string()
}

fn help_message_for_display() -> String {
    help_message().replace("tippy-driver", &display_binary_name("tippy-driver"))
}
