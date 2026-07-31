//! This module serves two purposes:
//!
//! 1. It is part of the `utils` module and used in other parts of bootstrap.
//! 2. It is embedded inside bootstrap shims to avoid a dependency on the bootstrap library.
//!    Therefore, this module should never use any other bootstrap module. This reduces binary size
//!    and improves compilation time by minimizing linking time.

// # Note on tests
//
// If we were to declare a tests submodule here, the shim binaries that include this module via
// `#[path]` would fail to find it, which breaks `./x check bootstrap`. So instead the unit tests
// for this module are in `super::tests::shared_helpers_tests`.

#![allow(dead_code)]

// Blessed env_mutation (2026-07-20): pre-existing code that predates the
// toolchain's deny-by-default ENV_MUTATION lint. Mutates process-global env
// under local save/restore, an RAII guard, or single-threaded harness/CLI
// context. Marked for later migration to a lock-scoped helper; the wall stays
// armed for all NEW code outside these marked modules. unknown_lints keeps the
// stock-toolchain build green (the lint name is Trust-only).
#![allow(unknown_lints)]
#![allow(env_mutation)]
use std::collections::HashMap;
use std::env;
use std::ffi::{OsStr, OsString};
use std::fs::{self, OpenOptions};
use std::io::{self, Write};
use std::process::Command;
use std::str::FromStr;

pub const TRUST_CARGO_TEST_SHIM_CONFIG: &str = ".trust-cargo-test-shim.json";
pub const TRUST_CARGO_TEST_SHIM_VERSION: &str = "2";

const TRUST_CARGO_TEST_SHIM_KEYS: [&str; 12] = [
    "CFG_COMPILER_BUILD_TRIPLE",
    "RUSTC_LIBDIR",
    "RUSTC_LINK_STD_INTO_RUSTC_DRIVER",
    "RUSTC_REAL",
    "RUSTC_SNAPSHOT",
    "RUSTC_SNAPSHOT_LIBDIR",
    "RUSTC_STAGE",
    "RUSTC_SYSROOT",
    "RUSTDOC_LIBDIR",
    "RUSTDOC_REAL",
    "TRUST_BOOTSTRAP_SHIM_NO_VERIFY",
    "TRUST_CARGO_TEST_SHIM_VERSION",
];

/// Returns the environment variable which the dynamic library lookup path
/// resides in for this platform.
pub fn dylib_path_var() -> &'static str {
    if cfg!(any(target_os = "windows", target_os = "cygwin")) {
        "PATH"
    } else if cfg!(target_vendor = "apple") {
        "DYLD_LIBRARY_PATH"
    } else if cfg!(target_os = "haiku") {
        "LIBRARY_PATH"
    } else if cfg!(target_os = "aix") {
        "LIBPATH"
    } else {
        "LD_LIBRARY_PATH"
    }
}

/// Parses the `dylib_path_var()` environment variable, returning a list of
/// paths that are members of this lookup path.
pub fn dylib_path() -> Vec<std::path::PathBuf> {
    let var = match std::env::var_os(dylib_path_var()) {
        Some(v) => v,
        None => return vec![],
    };
    std::env::split_paths(&var).collect()
}

/// Given an executable called `name`, return the filename for the
/// executable for a particular target.
pub fn exe(name: &str, target: &str) -> String {
    // On Cygwin, the decision to append .exe or not is not as straightforward.
    // Executable files do actually have .exe extensions so on hosts other than
    // Cygwin it is necessary.  But on a Cygwin host there is magic happening
    // that redirects requests for file X to file X.exe if it exists, and
    // furthermore /proc/self/exe (and thus std::env::current_exe) always
    // returns the name *without* the .exe extension.  For comparisons against
    // that to match, we therefore do not append .exe for Cygwin targets on
    // a Cygwin host.
    if target.contains("windows") || (cfg!(not(target_os = "cygwin")) && target.contains("cygwin"))
    {
        format!("{name}.exe")
    } else if target.contains("uefi") {
        format!("{name}.efi")
    } else if target.contains("wasm") {
        format!("{name}.wasm")
    } else {
        name.to_string()
    }
}

/// Parses the value of the "RUSTC_VERBOSE" environment variable and returns it as a `usize`.
/// If it was not defined, returns 0 by default.
///
/// Panics if "RUSTC_VERBOSE" is defined with the value that is not an unsigned integer.
pub fn parse_rustc_verbose() -> usize {
    match env::var("RUSTC_VERBOSE") {
        Ok(s) => usize::from_str(&s).expect("RUSTC_VERBOSE should be an integer"),
        Err(_) => 0,
    }
}

/// Parses the value of the "RUSTC_STAGE" environment variable and returns it as a `String`.
/// This is the stage of the *build compiler*, which we are wrapping using a rustc/rustdoc wrapper.
///
/// If "RUSTC_STAGE" was not set, the program will be terminated with 101.
pub fn parse_rustc_stage() -> u32 {
    env::var("RUSTC_STAGE").ok().and_then(|v| v.parse().ok()).unwrap_or_else(|| {
        // Don't panic here; it's reasonable to try and run these shims directly. Give a helpful error instead.
        eprintln!("rustc shim: FATAL: RUSTC_STAGE was not set");
        eprintln!("rustc shim: NOTE: use `x.py build -vvv` to see all environment variables set by bootstrap");
        std::process::exit(101);
    })
}

/// Writes the command invocation to a file if `DUMP_BOOTSTRAP_SHIMS` is set during bootstrap.
///
/// Before writing it, replaces user-specific values to create generic dumps for cross-environment
/// comparisons.
pub fn maybe_dump(dump_name: String, cmd: &Command) {
    if let Ok(dump_dir) = env::var("DUMP_BOOTSTRAP_SHIMS") {
        let dump_file = format!("{dump_dir}/{dump_name}");

        fs::create_dir_all(&dump_dir).expect("Unable to create bootstrap shim dump directory");
        let mut file = OpenOptions::new().create(true).append(true).open(dump_file).unwrap();

        let mut cmd_dump = format!("{cmd:?}\n");
        if let Ok(build_out) = env::var("BUILD_OUT") {
            cmd_dump = cmd_dump.replace(&build_out, "${BUILD_OUT}");
        }
        if let Ok(cargo_home) = env::var("CARGO_HOME") {
            cmd_dump = cmd_dump.replace(&cargo_home, "${CARGO_HOME}");
        }

        file.write_all(cmd_dump.as_bytes()).expect("Unable to write file");
    }
}

/// Finds `key` and returns its value from the given list of arguments `args`.
pub fn parse_value_from_args<'a>(args: &'a [OsString], key: &str) -> Option<&'a str> {
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        let arg = arg.to_str().unwrap();

        if let Some(value) = arg.strip_prefix(&format!("{key}=")) {
            return Some(value);
        } else if arg == key {
            return args.next().map(|v| v.to_str().unwrap());
        }
    }

    None
}

/// Any spelling or value of the verification switch — INCLUDING the retired
/// `-Zno-trust-verify` name, which is the same option in its pre-consolidation
/// spelling (576db732cd renamed it; the pinned seed's binaries still speak it,
/// and the seed's targo injects it into the rustc invocations it drives). The
/// mixed-vintage bootstrap therefore sees both spellings in one process tree,
/// and each vintage of the compiler parses exactly one of them: recognizing
/// both here is what lets `canonicalize_trust_no_verify` NORMALIZE a
/// seed-authored retired spelling into the current one for a current driver —
/// which breaks the seed-targo/stage1-rustc deadlock without re-forking the
/// flag surface with a compiler-side alias. Matching the option NAME rather
/// than one value is what makes the strip total: a caller-authored
/// `-Ztrust-verify=on` has to be removed too, or bootstrap's own final
/// `-Ztrust-verify=off` would be competing with it instead of replacing it.
fn is_trust_verify_option(option: &OsStr) -> bool {
    option.to_str().is_some_and(|option| {
        let name = option.split_once('=').map_or(option, |(name, _)| name).replace('_', "-");
        name == "trust-verify" || name == "no-trust-verify"
    })
}

/// Remove every Trust verification off-switch from rustc-style options before
/// the positional `--` boundary. Positional arguments after `--` are never
/// interpreted as compiler options.
pub fn strip_trust_no_verify(args: &mut Vec<OsString>) {
    let mut index = 0;
    while index < args.len() {
        if args[index] == "--" {
            break;
        }
        if args[index] == "-Z"
            && args.get(index + 1).is_some_and(|option| is_trust_verify_option(option))
        {
            args.drain(index..=index + 1);
        } else if args[index]
            .as_os_str()
            .to_str()
            .and_then(|arg| arg.strip_prefix("-Z"))
            .filter(|option| !option.is_empty())
            .is_some_and(|option| is_trust_verify_option(OsStr::new(option)))
        {
            args.remove(index);
        } else {
            index += 1;
        }
    }
}

/// Replace every spelling/value of the Trust verification off-switch with one
/// final enabled option, immediately before a positional `--` boundary.
pub fn canonicalize_trust_no_verify(args: &mut Vec<OsString>) {
    strip_trust_no_verify(args);
    let option_boundary = args.iter().position(|arg| arg == "--").unwrap_or(args.len());
    args.insert(option_boundary, OsString::from("-Ztrust-verify=off"));
}

/// Enforce Trust's verification switch at the final driver boundary. An
/// unsupported driver sees no spelling of the Trust-only option. A supported
/// real compile for which bootstrap requested isolation sees exactly one
/// enabled spelling, regardless of earlier or later authored values.
pub fn finalize_trust_no_verify(
    args: &mut Vec<OsString>,
    driver_supports_no_verify: bool,
    applies_to_compile: bool,
) {
    if !driver_supports_no_verify {
        strip_trust_no_verify(args);
    } else if applies_to_compile {
        canonicalize_trust_no_verify(args);
    }
}

/// Whether the rustc-style options request the Trust off-switch
/// (`-Ztrust-verify=off`, either token shape) before the positional `--`
/// boundary. This is how the BUILDER's intent reaches a snapshot compile:
/// bootstrap delivers the off-switch to host units (build scripts, proc
/// macros) through `RUSTC_HOST_FLAGS`, which the shim has already folded into
/// the assembled args by the time the snapshot finalizer runs.
fn args_request_trust_no_verify_off(args: &[OsString]) -> bool {
    let mut iter = args.iter().take_while(|arg| *arg != "--").peekable();
    while let Some(arg) = iter.next() {
        if arg == "-Z" {
            if iter.peek().is_some_and(|option| is_trust_verify_off_option(option)) {
                return true;
            }
        } else if arg
            .as_os_str()
            .to_str()
            .and_then(|arg| arg.strip_prefix("-Z"))
            .filter(|option| !option.is_empty())
            .is_some_and(|option| is_trust_verify_off_option(OsStr::new(option)))
        {
            return true;
        }
    }
    false
}

fn is_trust_verify_off_option(option: &OsStr) -> bool {
    option.to_str().is_some_and(|option| {
        let (name, value) = option.split_once('=').map_or((option, ""), |(name, value)| {
            (name, value)
        });
        match name.replace('_', "-").as_str() {
            "trust-verify" => value == "off",
            // The retired spelling is a boolean whose truthy values (and bare
            // form) request verification OFF; only an explicit `=no` does not.
            "no-trust-verify" => value != "no",
            _ => false,
        }
    })
}

/// The SNAPSHOT variant of [`finalize_trust_no_verify`], for a driver whose
/// vintage is the SEED PIN's, not this source tree's. A bootstrap-managed
/// stage0 snapshot may predate the current `-Ztrust-verify=off` spelling
/// entirely — the pinned 2026-07-13 seed advertises only the retired
/// `-Zno-trust-verify`, so there is NO argv spelling this source tree knows
/// that every legitimate seed can parse. Handing it the current spelling
/// aborted every fresh-machine build at the first build script
/// (`error: unknown unstable option: trust-verify`); handing it the retired
/// one would abort under any post-rename seed, which deleted it.
///
/// So: every argv spelling is stripped, and the return value tells the caller
/// whether to address the driver through the version-invariant nested-process
/// transport `TRUST_NO_VERIFY=1` instead — the compiler translates that env
/// into its own off-switch before option parsing on every Trust vintage
/// (`trust_verify.rs`, `verification_enabled`), and a stock upstream driver
/// ignores it as an unknown environment variable.
///
/// The transport fires on EITHER signal, because the off-switch reaches a
/// snapshot compile on two distinct lanes and `applies_to_compile` only
/// models one of them: the shim's own add-path (`trust_bootstrap_no_verify_applies`,
/// whose driver gate deliberately answers false for a seed on host units) and
/// the builder's `RUSTC_HOST_FLAGS` lane, which materializes the off-switch
/// directly in the assembled args for build scripts and proc macros. A
/// stripped-but-unhonored off-request would silently re-enable batteries-on
/// verification of the whole bootstrap dependency tree — the memchr wall.
/// An `=on` request never rides the transport: only the exact off value
/// counts. In-tree drivers (`trustc` stem, stage1+) never take this path:
/// their vintage matches this shim's own source by construction, so the
/// canonical argv spelling stays authoritative and auditable for them.
#[must_use]
pub fn finalize_trust_no_verify_snapshot(
    args: &mut Vec<OsString>,
    driver_supports_no_verify: bool,
    applies_to_compile: bool,
) -> bool {
    let off_requested = args_request_trust_no_verify_off(args);
    strip_trust_no_verify(args);
    driver_supports_no_verify && (applies_to_compile || off_requested)
}

/// Ordinary Cargo fixture isolation may disable verification, but an
/// authenticated Targo frontend has already committed to its verified argv at
/// the final compiler boundary and must never be downgraded by the harness.
pub fn cargo_test_no_verify_requested(
    isolation_requested: bool,
    authenticated_targo_frontend: bool,
) -> bool {
    isolation_requested && !authenticated_targo_frontend
}

/// Bootstrap shim controls are internal IPC, not permissive user booleans.
/// Accept only the exact value emitted by bootstrap so misspellings and broad
/// truthy parsing cannot silently disable verification.
pub fn trust_bootstrap_shim_marker_enabled(value: Option<&OsStr>) -> bool {
    value == Some(OsStr::new("1"))
}

/// Whether a shim invocation is a real crate compilation rather than a
/// version/help/target-information query. Direct rustc/rustdoc invocations do
/// not have to provide `--crate-name`, and `-` is a valid compilation input;
/// query options are the reliable discriminator.
pub fn compile_uses_trust_bootstrap_no_verify(args: &[OsString]) -> bool {
    if args.is_empty() {
        return false;
    }

    let options = args.iter().take_while(|arg| *arg != "--").collect::<Vec<_>>();
    !options.iter().enumerate().any(|(index, arg)| {
        arg.to_str().is_some_and(|arg| {
            matches!(
                arg,
                "-vV"
                    | "-V"
                    | "-Vv"
                    | "--version"
                    | "-h"
                    | "--help"
                    | "--print"
                    | "--explain"
                    | "-Zhelp"
                    | "-Chelp"
                    | "-Whelp"
            ) || arg.starts_with("--print=")
                || arg.starts_with("--explain=")
                || matches!(arg, "-Z" | "-C" | "-W")
                    && options.get(index + 1).is_some_and(|next| *next == "help")
        })
    })
}

fn push_expanded_rustc_arg(
    expanded: &mut Vec<OsString>,
    shell_argfiles: &mut bool,
    next_is_unstable_option: &mut bool,
    arg: String,
) {
    if *next_is_unstable_option {
        if arg == "shell-argfiles" {
            *shell_argfiles = true;
        }
        *next_is_unstable_option = false;
    } else if let Some(option) = arg.strip_prefix("-Z") {
        if option.is_empty() {
            *next_is_unstable_option = true;
        } else if option == "shell-argfiles" {
            *shell_argfiles = true;
        }
    }
    expanded.push(OsString::from(arg));
}

/// Expand rustc-compatible `@argfile` inputs before a bootstrap shim makes
/// routing or verification-policy decisions. Cargo deliberately falls back to
/// this transport for long command lines (and tests can force it), so treating
/// raw argv as authoritative would hide `--target`, `--crate-name`, and probes.
pub fn expand_rustc_argfiles(args: &[OsString]) -> io::Result<Vec<OsString>> {
    let mut expanded = Vec::new();
    let mut shell_argfiles = false;
    let mut next_is_unstable_option = false;

    for arg in args {
        let arg = arg.to_str().ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("compiler argument is not valid Unicode: {arg:?}"),
            )
        })?;
        let Some(path) = arg.strip_prefix('@') else {
            push_expanded_rustc_arg(
                &mut expanded,
                &mut shell_argfiles,
                &mut next_is_unstable_option,
                arg.to_owned(),
            );
            continue;
        };

        if let Some(path) = path.strip_prefix("shell:").filter(|_| shell_argfiles) {
            let contents = fs::read_to_string(path)?;
            let shell_args = shlex::split(&contents).ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("invalid shell-style compiler argument file: {path}"),
                )
            })?;
            for arg in shell_args {
                push_expanded_rustc_arg(
                    &mut expanded,
                    &mut shell_argfiles,
                    &mut next_is_unstable_option,
                    arg,
                );
            }
        } else {
            for arg in fs::read_to_string(path)?.lines() {
                push_expanded_rustc_arg(
                    &mut expanded,
                    &mut shell_argfiles,
                    &mut next_is_unstable_option,
                    arg.to_owned(),
                );
            }
        }
    }

    Ok(expanded)
}

fn is_isolated_shim_control_env(key: &OsStr) -> bool {
    let Some(key) = key.to_str() else { return false };
    let key = key.to_ascii_uppercase();
    (key.starts_with("RUSTC_") && key != "RUSTC_BOOTSTRAP")
        || key.starts_with("RUSTDOC_")
        || key.starts_with("TRUST_")
        || matches!(
            key.as_str(),
            "CFG_COMPILER_BUILD_TRIPLE" | "DUMP_BOOTSTRAP_SHIMS" | "FORCE_ON_BROKEN_PIPE_KILL"
        )
}

/// A single-process environment overlay used by dedicated Cargo-test shim
/// copies. It hides bootstrap-private variables authored by fixture config
/// while the shim makes routing decisions, then restores those exact variables
/// before spawning the real compiler so Cargo's environment semantics remain
/// observable to build scripts and `env!`.
pub struct IsolatedShimEnvironment {
    original: Vec<(OsString, OsString)>,
    active: bool,
}

impl IsolatedShimEnvironment {
    pub fn restore(&mut self) {
        if !self.active {
            return;
        }

        let installed = env::vars_os()
            .map(|(key, _)| key)
            .filter(|key| is_isolated_shim_control_env(key))
            .collect::<Vec<_>>();
        // SAFETY: bootstrap compiler shims are single-threaded. The overlay is
        // installed before command construction and restored before spawning.
        unsafe {
            for key in installed {
                env::remove_var(key);
            }
            for (key, value) in &self.original {
                env::set_var(key, value);
            }
        }
        self.active = false;
    }
}

impl Drop for IsolatedShimEnvironment {
    fn drop(&mut self) {
        self.restore();
    }
}

/// Activate the collision-free bootstrap context encoded beside a dedicated
/// Cargo-test rustc/rustdoc shim. Normal bootstrap shims have no sidecar and
/// retain their existing environment behavior.
pub fn activate_cargo_test_shim_environment() -> io::Result<Option<IsolatedShimEnvironment>> {
    let config_path = env::current_exe()?
        .parent()
        .expect("bootstrap shim executable must have a parent directory")
        .join(TRUST_CARGO_TEST_SHIM_CONFIG);
    if !config_path.is_file() {
        return Ok(None);
    }

    let configured: HashMap<String, String> = serde_json::from_slice(&fs::read(&config_path)?)
        .map_err(|err| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("invalid Cargo-test shim config {}: {err}", config_path.display()),
            )
        })?;
    if let Some(key) = configured.keys().find(|key| {
        !TRUST_CARGO_TEST_SHIM_KEYS.contains(&key.as_str())
            || !is_isolated_shim_control_env(OsStr::new(key))
    }) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("Cargo-test shim config {} has unsupported key {key:?}", config_path.display(),),
        ));
    }
    if let Some(missing) =
        TRUST_CARGO_TEST_SHIM_KEYS.iter().find(|key| !configured.contains_key(**key))
    {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("Cargo-test shim config {} is missing {missing}", config_path.display()),
        ));
    }
    if configured.len() != TRUST_CARGO_TEST_SHIM_KEYS.len() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "Cargo-test shim config {} has duplicate authority keys",
                config_path.display()
            ),
        ));
    }
    if configured["TRUST_CARGO_TEST_SHIM_VERSION"] != TRUST_CARGO_TEST_SHIM_VERSION
        || configured["TRUST_BOOTSTRAP_SHIM_NO_VERIFY"] != "1"
        || !matches!(configured["RUSTC_LINK_STD_INTO_RUSTC_DRIVER"].as_str(), "0" | "1")
        || configured["RUSTC_STAGE"].parse::<u32>().is_err()
        || configured.values().any(String::is_empty)
    {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "Cargo-test shim config {} has invalid authority values",
                config_path.display()
            ),
        ));
    }

    let original =
        env::vars_os().filter(|(key, _)| is_isolated_shim_control_env(key)).collect::<Vec<_>>();
    // SAFETY: see IsolatedShimEnvironment::restore. No shim threads exist.
    unsafe {
        for (key, _) in &original {
            env::remove_var(key);
        }
        for (key, value) in configured {
            env::set_var(key, value);
        }
    }

    Ok(Some(IsolatedShimEnvironment { original, active: true }))
}
