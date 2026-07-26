// We need this feature as it changes `dylib` linking behavior and allows us to link to
// `rustc_driver`.
#![feature(rustc_private)]
// warn on lints, that are included in `rust-lang/rust`s bootstrap
#![warn(rust_2018_idioms, unused_lifetimes)]

extern crate rustc_driver;
extern crate rustc_session;

mod arg_protocol;
mod compiler_identity;
mod frontend_args;
mod path_identity;
mod rustc_private_overlay;

use std::ffi::OsString;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{self, Command, ExitStatus, exit};
use std::{env, fs};

use arg_protocol::{
    CLIPPY_ARGS_ENV, TIPPY_ENCODED_ARGS_ENV, encode_args, executable_path_matches_with_windows_semantics,
};
use compiler_identity::AuthenticatedCompiler;
use frontend_args::split_legacy_no_deps;
use path_identity::{AuthenticatedExecutable, metadata_is_plain_file};
use rustc_private_overlay::{
    ConfiguredOverlay, OverlayEnvironment, clear_overlay_command_environment, query_compiler_commit_hash,
};

fn show_help() {
    if writeln!(&mut anstream::stdout().lock(), "{}", help_message_for_display()).is_err() {
        exit(rustc_driver::EXIT_FAILURE);
    }
}

fn show_version() {
    let version_info = clippy_version_info_for_display();
    if writeln!(&mut anstream::stdout().lock(), "{version_info}").is_err() {
        exit(rustc_driver::EXIT_FAILURE);
    }
}

#[cfg(test)]
fn frontend_command_for_binary(binary: Option<&str>) -> &'static str {
    frontend_command_for_invocation(binary, None)
}

fn frontend_command_for_invocation(raw_argv0: Option<&str>, current_exe: Option<&Path>) -> &'static str {
    let identity = current_exe.and_then(recognized_frontend_identity).or_else(|| {
        current_exe
            .is_none()
            .then(|| raw_argv0.and_then(|arg| recognized_frontend_identity(Path::new(arg))))
            .flatten()
    });
    match identity {
        Some(FrontendIdentity::TargoTippy) => "targo tippy",
        // These inherited names are Cargo build selectors and development
        // entrypoints, not installed Trust aliases.
        Some(FrontendIdentity::CargoClippy) => "cargo clippy",
        Some(FrontendIdentity::Tippy) | None => "tippy",
    }
}

fn clippy_version_info_for_display() -> String {
    rustc_tools_util::get_version_info!().to_string()
}

pub fn main() {
    let raw_args = unicode_args(env::args_os()).unwrap_or_else(|error| {
        report_setup_error(&error);
        process::exit(rustc_driver::EXIT_FAILURE);
    });
    let current_exe = invocation_executable_path().unwrap_or_else(|error| {
        report_setup_error(&error);
        process::exit(rustc_driver::EXIT_FAILURE);
    });
    if let Err(error) = validate_frontend_identity(raw_args.first().map(String::as_str), current_exe.as_deref()) {
        report_setup_error(&error);
        process::exit(rustc_driver::EXIT_FAILURE);
    }
    let control_args = frontend_control_args(&raw_args);

    // Check frontend controls even when invoked as `cargo-clippy`, but never
    // consume arguments after `--`: those belong byte-for-byte to the lint /
    // compiler driver.
    if control_args.iter().any(|a| a == "--help" || a == "-h") {
        show_help();
        return;
    }

    if control_args.iter().any(|arg| is_version_flag(arg)) {
        show_version();
        return;
    }

    if let Some(pos) = control_args.iter().position(|a| a == "--explain") {
        if let Some(mut lint) = control_args.get(pos + 1).cloned() {
            lint.make_ascii_lowercase();
            process::exit(clippy_lints::explain(
                &lint.strip_prefix("clippy::").unwrap_or(&lint).replace('-', "_"),
            ));
        } else {
            show_help();
        }
        return;
    }

    if let Err(code) = process(
        tippy_command_args(raw_args.into_iter(), current_exe.as_deref()),
        current_exe.as_deref(),
    ) {
        process::exit(code);
    }
}

fn unicode_args(args: impl IntoIterator<Item = OsString>) -> Result<Vec<String>, String> {
    args.into_iter()
        .enumerate()
        .map(|(index, arg)| {
            arg.into_string()
                .map_err(|arg| format!("argument {index} is not valid Unicode: {arg:?}"))
        })
        .collect()
}

fn frontend_control_args(raw_args: &[String]) -> &[String] {
    let args = raw_args.get(1..).unwrap_or_default();
    let end = args.iter().position(|arg| arg == "--").unwrap_or(args.len());
    &args[..end]
}

fn is_version_flag(arg: &str) -> bool {
    matches!(arg, "--version" | "-V" | "-vV" | "-Vv")
}

fn tippy_command_args<I>(mut args: I, current_exe: Option<&Path>) -> std::vec::IntoIter<String>
where
    I: Iterator<Item = String>,
{
    let binary = args.next();
    // `argv[0]` is caller-controlled and `tippy` and `targo-tippy` have
    // different argument protocols despite selecting the same public
    // toolchain. Take the protocol from the authenticated executable. The
    // raw development identity is only a compatibility fallback when the OS
    // executable path is unavailable; branded raw identities already fail
    // validation in that case.
    let identity = current_exe.and_then(recognized_frontend_identity).or_else(|| {
        current_exe
            .is_none()
            .then(|| {
                binary
                    .as_deref()
                    .and_then(|arg| recognized_frontend_identity(Path::new(arg)))
            })
            .flatten()
            .filter(|identity| !identity.is_branded())
    });
    let mut args = args.peekable();
    if identity.is_some_and(|identity| {
        args.peek()
            .is_some_and(|arg| identity.is_external_subcommand_marker(arg))
    }) {
        // Cargo-style external subcommands receive the subcommand name as
        // argv[1]. Strip only a marker accepted by this authenticated
        // executable, never a direct user's first flag.
        args.next();
    }

    args.collect::<Vec<_>>().into_iter()
}

struct TippyCmd {
    cargo_subcommand: &'static str,
    args: Vec<String>,
    no_deps: bool,
    clippy_args: Vec<String>,
}

struct PreparedTippyCommand {
    command: Command,
    authenticated_toolchain: Option<AuthenticatedTippyToolchain>,
}

#[derive(Debug)]
struct AuthenticatedTippyToolchain {
    compiler: AuthenticatedCompiler,
    targo: AuthenticatedExecutable,
    driver: AuthenticatedExecutable,
}

impl AuthenticatedTippyToolchain {
    fn new(compiler: AuthenticatedCompiler, targo: PathBuf, driver: PathBuf) -> Result<Self, String> {
        let targo = AuthenticatedExecutable::capture(targo, "targo")?;
        let driver = AuthenticatedExecutable::capture(driver, "tippy-driver")?;
        Ok(Self {
            compiler,
            targo,
            driver,
        })
    }

    fn compiler_path(&self) -> &Path {
        self.compiler.path()
    }

    fn compiler_commit_hash(&self) -> Result<String, String> {
        self.compiler
            .run_guarded(|| query_compiler_commit_hash(self.compiler.path()))
            .and_then(|result| result)
    }

    fn run_guarded<T>(&self, operation: impl FnOnce() -> T) -> Result<T, String> {
        // Keep the compiler's bin-directory guard outermost so all three open
        // executable handles and the complete Targo child lifetime are
        // covered by one coherent toolchain-directory identity.
        self.compiler
            .run_guarded(|| {
                self.targo
                    .run_guarded_for("Targo", || self.driver.run_guarded_for("Tippy driver", operation))
            })
            .and_then(|result| result)
            .and_then(|result| result)
    }
}

impl TippyCmd {
    fn new<I>(mut old_args: I) -> Result<Self, String>
    where
        I: Iterator<Item = String>,
    {
        let mut cargo_subcommand = "check";
        let mut args = vec![];
        let mut no_deps = false;

        for arg in old_args.by_ref() {
            match arg.as_str() {
                "--fix" => {
                    cargo_subcommand = "fix";
                    continue;
                },
                "--no-deps" => {
                    no_deps = true;
                    continue;
                },
                "--" => break,
                _ => {},
            }

            args.push(arg);
        }

        let (trailing_no_deps, clippy_args) = split_legacy_no_deps(old_args.collect())?;
        no_deps |= trailing_no_deps || cargo_subcommand == "fix";

        Ok(Self {
            cargo_subcommand,
            args,
            no_deps,
            clippy_args,
        })
    }

    fn path(current_exe: Option<&Path>, branded: bool) -> Result<PathBuf, String> {
        let public_driver = sibling_tool_path(current_exe, "tippy-driver");
        if branded {
            return validate_sibling_executable(public_driver, "tippy-driver");
        }
        let inherited_driver =
            sibling_tool_path(current_exe, "clippy-driver").filter(|path| path_is_executable_file(path));
        Ok(driver_path_for_invocation(
            branded,
            public_driver.filter(|path| path_is_executable_file(path)),
            inherited_driver,
        ))
    }

    fn into_std_cmd(self, current_exe: Option<&Path>) -> Result<PreparedTippyCommand, String> {
        // Use the same OS-reported path that passed frontend validation for
        // every sibling decision. Re-reading current_exe independently for
        // Targo, the driver, and the compiler could otherwise construct one
        // mixed command if the invocation path changed between reads.
        let branded = branded_executable(current_exe);
        let targo = targo_path(current_exe, branded)?;
        let driver = Self::path(current_exe, branded)?;
        let compiler = if branded {
            Some(selected_toolchain_compiler(current_exe)?)
        } else {
            None
        };
        let authenticated_toolchain = compiler
            .map(|compiler| AuthenticatedTippyToolchain::new(compiler, targo.clone(), driver.clone()))
            .transpose()?;
        let compiler_path = authenticated_toolchain
            .as_ref()
            .map(|toolchain| toolchain.compiler_path().to_owned());
        let overlay_environment = OverlayEnvironment::capture();
        let compiler_commit_hash = if overlay_environment.is_configured() {
            authenticated_toolchain
                .as_ref()
                .map(AuthenticatedTippyToolchain::compiler_commit_hash)
                .transpose()?
        } else {
            None
        };
        let configured_overlay = ConfiguredOverlay::for_frontend(
            compiler_path.as_deref(),
            compiler_commit_hash.as_deref(),
            overlay_environment,
        )?;
        let mut command = self.into_std_cmd_with_tools_and_compiler(targo, driver, compiler_path);
        if let Some(overlay) = configured_overlay {
            overlay.configure_command(&mut command);
        }
        Ok(PreparedTippyCommand {
            command,
            authenticated_toolchain,
        })
    }

    #[cfg(test)]
    fn into_std_cmd_with_tools(self, targo: PathBuf, driver: PathBuf) -> Command {
        self.into_std_cmd_with_tools_and_compiler(targo, driver, None)
    }

    fn into_std_cmd_with_tools_and_compiler(
        self,
        targo: PathBuf,
        driver: PathBuf,
        compiler: Option<PathBuf>,
    ) -> Command {
        let mut cmd = Command::new(&targo);
        // The overlay is an authenticated branded-Tippy capability. Never
        // inherit raw project values; `into_std_cmd` re-emits canonical paths
        // only after validating them against the selected compiler.
        clear_overlay_command_environment(&mut cmd);
        let branded = compiler.is_some();
        // Keep the inherited channel for mixed/upstream tooling, but build it
        // in one allocation.  The old repeated `String +` fold copied the
        // complete prefix once per argument (quadratic for long lint lists).
        // Tippy's versioned length-prefixed channel below remains authoritative
        // and preserves arguments containing this legacy delimiter.
        let mut legacy_args = self.clippy_args.clone();
        if self.no_deps {
            legacy_args.push("--no-deps".to_string());
        }
        let mut clippy_args = legacy_args.join("__CLIPPY_HACKERY__");
        if !legacy_args.is_empty() {
            clippy_args.push_str("__CLIPPY_HACKERY__");
        }
        let tippy_encoded_args = encode_args(self.no_deps, &self.clippy_args);

        // Currently, `CLIPPY_TERMINAL_WIDTH` is used only to format "unknown field" error messages.
        let terminal_width = termize::dimensions().map_or(0, |(w, _)| w);

        cmd.env("RUSTC_WORKSPACE_WRAPPER", driver)
            .env(CLIPPY_ARGS_ENV, clippy_args)
            .env(TIPPY_ENCODED_ARGS_ENV, tippy_encoded_args)
            .env("CLIPPY_TERMINAL_WIDTH", terminal_width.to_string())
            // Tippy is a lint frontend, not a proof supervisor. Never inherit
            // an enclosing verifier invocation's private Targo marker: doing
            // so suppresses the native off-switch and can turn a lint run into
            // an unexpectedly expensive evidence-grade build. The selected
            // child Targo will establish its own native lane.
            .env_remove("TRUST_TARGO_VERIFY")
            // Tippy intentionally uses Targo's native check/fix transport;
            // the public frontend authorizes that unverified lint lane
            // explicitly below.
            .env("TRUST_NO_MIGRATE_WARN", "1");

        if branded {
            // The branded Targo frontend admits a compilation command through
            // exactly two doors: an authenticated verified session, or this
            // explicit authorization. There is deliberately no silent third
            // outcome, so dropping the argument does not buy a verified lint
            // run — it makes the command fail. The other door stays shut on
            // purpose: the verified marker is accepted only beside a proof
            // session and artifact root that only the verifier driver mints,
            // and lint passes run long before the MIR verification pass
            // anyway, so no lint could read this run's verdicts even inside it.
            cmd.arg("--unverified");
        }
        cmd.arg(self.cargo_subcommand).args(&self.args);

        if let Some(compiler) = compiler {
            // A branded Tippy invocation selects one coherent Trust toolchain.
            // Do not let ambient Cargo compiler/wrapper controls splice a
            // second toolchain or an outer wrapper into that closed trio.
            // Inherited `cargo-clippy` development invocations retain upstream
            // override behavior through the `None` path above.
            cmd.env("CARGO", &targo)
                .env("RUSTC", compiler)
                // A branded Tippy child owns its lane through the visible
                // `--unverified` argument above. Do not combine that opt-in
                // with bootstrap's inherited shim controls or retired
                // frontend-authorization markers.
                .env_remove("TRUST_BOOTSTRAP_SHIM_NO_VERIFY")
                .env_remove("TRUST_BOOTSTRAP_SHIM_NO_VERIFY_TARGET_ONLY")
                .env_remove("TRUST_BOOTSTRAP_NO_VERIFY")
                .env_remove("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
                // Cargo defines an empty wrapper value as disabled. Set it
                // explicitly (rather than merely removing it) so a project
                // `build.rustc-wrapper` config cannot become an outer wrapper.
                .env("RUSTC_WRAPPER", "")
                .env("CARGO_BUILD_RUSTC_WRAPPER", "")
                .env("CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "")
                .env_remove("SYSROOT");
        }

        cmd
    }
}

fn selected_toolchain_compiler(current_exe: Option<&Path>) -> Result<AuthenticatedCompiler, String> {
    let trustc = sibling_tool_path(current_exe, "trustc").ok_or_else(|| {
        "cannot locate required sibling `trustc` because the current Tippy executable path is unavailable; repair or reinstall the selected Trust toolchain".to_string()
    })?;
    // Prefer the rustc-compatible sibling: build scripts commonly require a
    // `rustc ...` version banner. The compatibility name is authoritative only
    // when its complete bytes equal the selected `trustc`; a stale or ambient
    // executable merely occupying that sibling path must not splice a second
    // compiler into the branded toolchain.
    if let Some(rustc) = sibling_tool_path(current_exe, "rustc") {
        match fs::symlink_metadata(&rustc) {
            Ok(_) => return AuthenticatedCompiler::alias(trustc, rustc),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {},
            Err(error) => {
                return Err(format!(
                    "cannot inspect rustc-compatible sibling `{}`: {error}; repair or reinstall the selected Trust toolchain",
                    rustc.display()
                ));
            },
        }
    }
    AuthenticatedCompiler::selected_trustc(trustc)
}

fn targo_path(current_exe: Option<&Path>, branded: bool) -> Result<PathBuf, String> {
    let sibling_targo = sibling_tool_path(current_exe, "targo");
    if branded {
        return validate_sibling_executable(sibling_targo, "targo");
    }
    Ok(targo_path_for_invocation(
        branded,
        sibling_targo.filter(|path| path_is_executable_file(path)),
        env::var_os("CARGO").map(PathBuf::from),
    ))
}

fn branded_executable(executable: Option<&Path>) -> bool {
    executable
        .and_then(recognized_frontend_identity)
        .is_some_and(FrontendIdentity::is_branded)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FrontendIdentity {
    Tippy,
    TargoTippy,
    CargoClippy,
}

impl FrontendIdentity {
    fn is_branded(self) -> bool {
        matches!(self, Self::Tippy | Self::TargoTippy)
    }

    fn is_external_subcommand_marker(self, argument: &str) -> bool {
        match self {
            Self::Tippy => false,
            // `targo tippy` is canonical; `targo clippy` remains a protected
            // compatibility spelling and must reach this same sibling binary.
            Self::TargoTippy => matches!(argument, "tippy" | "clippy"),
            Self::CargoClippy => argument == "clippy",
        }
    }
}

fn recognized_frontend_identity(executable: &Path) -> Option<FrontendIdentity> {
    frontend_identity_from_path(executable, cfg!(windows))
}

fn frontend_identity_from_path(executable: &Path, windows_semantics: bool) -> Option<FrontendIdentity> {
    let matches = |expected| executable_path_matches_with_windows_semantics(executable, expected, windows_semantics);
    if matches("tippy") {
        Some(FrontendIdentity::Tippy)
    } else if matches("targo-tippy") {
        Some(FrontendIdentity::TargoTippy)
    } else if matches("cargo-clippy") || matches("clippy") {
        Some(FrontendIdentity::CargoClippy)
    } else {
        None
    }
}

fn validate_frontend_identity(raw_argv0: Option<&str>, current_exe: Option<&Path>) -> Result<(), String> {
    let raw_identity = raw_argv0.and_then(|arg| recognized_frontend_identity(Path::new(arg)));
    let current_identity = current_exe.and_then(recognized_frontend_identity);
    match (raw_identity, current_identity) {
        (Some(raw), Some(current)) if raw != current => Err(format!(
            "invocation name `{}` conflicts with the running Tippy executable `{}`; executable identity, not argv[0], selects the toolchain and argument protocol",
            raw_argv0.unwrap_or_default(),
            current_exe.expect("matched current executable").display()
        )),
        (_, Some(_)) => Ok(()),
        (Some(raw), None) if raw.is_branded() => Err(format!(
            "cannot authenticate branded Tippy invocation `{}` against the running executable; repair or reinstall the selected toolchain",
            raw_argv0.unwrap_or_default()
        )),
        (_, None) if current_exe.is_some() => Err(format!(
            "running Tippy executable `{}` has an unrecognized name; expected `tippy`, `targo-tippy`, `cargo-clippy`, or `clippy`",
            current_exe.expect("guarded current executable").display()
        )),
        (Some(FrontendIdentity::CargoClippy), None) => Ok(()),
        _ => Err(format!(
            "cannot authenticate Tippy invocation `{}` without a recognized running or development executable identity",
            raw_argv0.unwrap_or_default()
        )),
    }
}

fn targo_path_for_invocation(branded: bool, sibling_targo: Option<PathBuf>, cargo_env: Option<PathBuf>) -> PathBuf {
    if branded {
        // A selected Trust sysroot is a coherent unit. Public Tippy must not
        // silently cross that boundary because the caller has an ambient or
        // attacker-controlled CARGO value.
        sibling_targo.unwrap_or_else(|| PathBuf::from("targo"))
    } else {
        // Retain upstream cargo-clippy development behavior for the inherited
        // Cargo build selector, where CARGO deliberately chooses the frontend.
        cargo_env.or(sibling_targo).unwrap_or_else(|| PathBuf::from("targo"))
    }
}

fn driver_path_for_invocation(
    branded: bool,
    public_driver: Option<PathBuf>,
    inherited_driver: Option<PathBuf>,
) -> PathBuf {
    if branded {
        public_driver.unwrap_or_else(|| PathBuf::from("tippy-driver"))
    } else {
        inherited_driver
            .or(public_driver)
            .unwrap_or_else(|| PathBuf::from("clippy-driver"))
    }
}

fn process<I>(old_args: I, current_exe: Option<&Path>) -> Result<(), i32>
where
    I: Iterator<Item = String>,
{
    let cmd = match TippyCmd::new(old_args) {
        Ok(cmd) => cmd,
        Err(error) => {
            report_setup_error(&format!("invalid Tippy frontend arguments: {error}"));
            return Err(rustc_driver::EXIT_FAILURE);
        },
    };

    let mut prepared = match cmd.into_std_cmd(current_exe) {
        Ok(prepared) => prepared,
        Err(error) => {
            report_setup_error(&error);
            return Err(rustc_driver::EXIT_FAILURE);
        },
    };

    run_frontend_command(&mut prepared.command, prepared.authenticated_toolchain.as_ref())
}

fn run_frontend_command(
    cmd: &mut Command,
    authenticated_toolchain: Option<&AuthenticatedTippyToolchain>,
) -> Result<(), i32> {
    let program = cmd.get_program().to_string_lossy().into_owned();
    let child_status = if let Some(authenticated_toolchain) = authenticated_toolchain {
        match authenticated_toolchain.run_guarded(|| cmd.status()) {
            Ok(status) => status,
            Err(error) => {
                report_setup_error(&format!(
                    "refusing to accept `{program}` execution with an unauthenticated toolchain process: {error}; repair or reinstall the selected Trust toolchain"
                ));
                return Err(rustc_driver::EXIT_FAILURE);
            },
        }
    } else {
        cmd.status()
    };
    let exit_status = match child_status {
        Ok(status) => status,
        Err(error) => {
            report_setup_error(&format!(
                "failed to launch `{program}`: {error}; repair or reinstall the selected Trust \
                 toolchain so `tippy`, `targo`, and `tippy-driver` are executable siblings"
            ));
            return Err(rustc_driver::EXIT_FAILURE);
        },
    };

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status_code(&exit_status))
    }
}

fn exit_status_code(status: &ExitStatus) -> i32 {
    if let Some(code) = status.code() {
        return code;
    }

    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt as _;

        if let Some(signal) = status.signal() {
            // Match conventional shell status while preserving the actual
            // terminating signal instead of turning every signal into -1/255.
            return 128_i32.saturating_add(signal).min(u8::MAX.into());
        }
    }

    rustc_driver::EXIT_FAILURE
}

fn report_setup_error(error: &str) {
    // Diagnostics must not turn a recoverable setup failure into a second panic
    // if stderr itself is closed.
    let _ = writeln!(std::io::stderr().lock(), "tippy: setup error: {error}");
}

#[must_use]
pub fn help_message() -> &'static str {
    color_print::cstr!(
"Checks a package to catch common mistakes and improve your Rust code.

<green,bold>Usage</>:
    <cyan,bold>cargo clippy</> <cyan>[OPTIONS] [--] [<<ARGS>>...]</>

<green,bold>Common options:</>
    <cyan,bold>--no-deps</>                Run Tippy only on the given crate, without linting the dependencies
    <cyan,bold>--fix</>                    Automatically apply lint suggestions. This flag implies <cyan>--no-deps</> and <cyan>--all-targets</>
    <cyan,bold>-h</>, <cyan,bold>--help</>               Print this message
    <cyan,bold>-V</>, <cyan,bold>--version</>            Print version info and exit
    <cyan,bold>--explain [LINT]</>         Print the documentation for a given lint

See all options with <cyan,bold>targo check --help</>.

<green,bold>Allowing / Denying lints</>

To allow or deny a lint from the command line you can use <cyan,bold>cargo clippy --</> with:

    <cyan,bold>-W</> / <cyan,bold>--warn</> <cyan>[LINT]</>       Set lint warnings
    <cyan,bold>-A</> / <cyan,bold>--allow</> <cyan>[LINT]</>      Set lint allowed
    <cyan,bold>-D</> / <cyan,bold>--deny</> <cyan>[LINT]</>       Set lint denied
    <cyan,bold>-F</> / <cyan,bold>--forbid</> <cyan>[LINT]</>     Set lint forbidden

You can use tool lints to allow or deny lints from your code, e.g.:

    <yellow,bold>#[allow(clippy::needless_lifetimes)]</>

<green,bold>Manifest Options:</>
    <cyan,bold>--manifest-path</> <cyan><<PATH>></>  Path to Cargo.toml
    <cyan,bold>--frozen</>                Require Cargo.lock and cache are up to date
    <cyan,bold>--locked</>                Require Cargo.lock is up to date
    <cyan,bold>--offline</>               Run without accessing the network
    ")
}

fn help_message_for_display() -> String {
    let binary = env::args().next();
    // `main` authenticates this path before any help/version dispatch. Keep the
    // display helper fallible for direct test/library callers without allowing
    // it to grant toolchain authority.
    let current_exe = invocation_executable_path().ok().flatten();
    help_message().replace(
        "cargo clippy",
        frontend_command_for_invocation(binary.as_deref(), current_exe.as_deref()),
    )
}

fn sibling_tool_path(current_exe: Option<&Path>, tool: &str) -> Option<PathBuf> {
    let mut path = current_exe?.with_file_name(tool);
    if cfg!(windows) {
        path.set_extension("exe");
    }
    Some(path)
}

fn invocation_executable_path() -> Result<Option<PathBuf>, String> {
    // `argv[0]` is caller-controlled. Even a path that canonicalizes to this
    // executable can be an attacker-owned symlink whose parent contains a
    // forged toolchain. Only the operating system's executable path may own
    // sibling discovery and branding.
    let path = match env::current_exe() {
        Ok(path) => path,
        Err(_) => return Ok(None),
    };
    // Some platforms may report the invocation symlink rather than its
    // resolved target. Such a path cannot safely own sibling discovery: its
    // parent may be attacker-controlled. Public aliases are installed as hard
    // links or copies, so fail closed instead of adopting that directory.
    let metadata = fs::symlink_metadata(&path).map_err(|error| {
        format!(
            "cannot inspect the OS-reported Tippy executable `{}`: {error}",
            path.display()
        )
    })?;
    if !metadata_is_plain_file(&metadata) {
        return Err(format!(
            "cannot authenticate branded Tippy invocation: OS-reported executable `{}` is not a plain regular file; frontends cannot be symlinks or reparse points",
            path.display()
        ));
    }
    Ok(Some(path))
}

fn validate_sibling_executable(candidate: Option<PathBuf>, tool: &str) -> Result<PathBuf, String> {
    let Some(path) = candidate else {
        return Err(format!(
            "cannot locate required sibling `{tool}` because the current Tippy executable path \
             is unavailable; repair or reinstall the selected Trust toolchain"
        ));
    };
    let metadata = fs::symlink_metadata(&path).map_err(|error| {
        format!(
            "required sibling `{tool}` at `{}` is unavailable: {error}; repair or reinstall the \
             selected Trust toolchain so `tippy`, `targo`, and `tippy-driver` share one bin directory",
            path.display()
        )
    })?;
    if !metadata_is_plain_file(&metadata) {
        return Err(format!(
            "required sibling `{tool}` at `{}` is not a regular file or is a symlink/reparse point; \
             repair or reinstall the selected Trust toolchain with plain executables",
            path.display()
        ));
    }
    if !metadata_is_executable(&metadata) {
        return Err(format!(
            "required sibling `{tool}` at `{}` is not executable; repair or reinstall the \
             selected Trust toolchain",
            path.display()
        ));
    }
    Ok(path)
}

fn path_is_executable_file(path: &Path) -> bool {
    // Optional development discovery retains upstream support for symlinked
    // cargo-clippy/clippy-driver tools. Required public siblings go through
    // `validate_sibling_executable`, which deliberately rejects symlinks.
    fs::metadata(path).is_ok_and(|metadata| metadata.is_file() && metadata_is_executable(&metadata))
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

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::time::{SystemTime, UNIX_EPOCH};
    use std::{env, fs};

    use super::{
        FrontendIdentity, TippyCmd, branded_executable, driver_path_for_invocation, frontend_command_for_binary,
        frontend_command_for_invocation, frontend_control_args, frontend_identity_from_path, is_version_flag,
        run_frontend_command, targo_path_for_invocation, tippy_command_args, unicode_args, validate_frontend_identity,
        validate_sibling_executable,
    };

    fn command_args(args: &[&str]) -> Vec<String> {
        let current_exe = args.first().map(Path::new);
        tippy_command_args(args.iter().map(ToString::to_string), current_exe).collect()
    }

    #[test]
    fn direct_tippy_preserves_the_first_user_argument() {
        assert_eq!(command_args(&["/toolchain/bin/tippy", "--workspace"]), ["--workspace"]);
    }

    #[test]
    fn targo_tippy_discards_only_the_external_subcommand_marker() {
        assert_eq!(
            command_args(&["/toolchain/bin/targo-tippy", "tippy", "--workspace"]),
            ["--workspace"]
        );
    }

    #[test]
    fn targo_clippy_compatibility_discards_only_its_protected_marker() {
        assert_eq!(
            command_args(&["/toolchain/bin/targo-tippy", "clippy", "--workspace"]),
            ["--workspace"]
        );
    }

    #[test]
    fn helper_invoked_without_a_marker_preserves_the_first_user_argument() {
        assert_eq!(
            command_args(&["/toolchain/bin/targo-tippy", "--workspace"]),
            ["--workspace"]
        );
    }

    #[test]
    fn inherited_cargo_clippy_dispatch_remains_compatible() {
        assert_eq!(
            command_args(&["/toolchain/bin/cargo-clippy", "clippy", "--workspace"]),
            ["--workspace"]
        );
    }

    #[test]
    fn authenticated_executable_not_raw_argv0_selects_argument_protocol() {
        let direct = tippy_command_args(
            ["/attacker/bin/targo-tippy", "tippy", "--workspace"]
                .map(String::from)
                .into_iter(),
            Some(Path::new("/toolchain/bin/tippy")),
        )
        .collect::<Vec<_>>();
        assert_eq!(direct, ["tippy", "--workspace"]);

        let external = tippy_command_args(
            ["/attacker/bin/tippy", "tippy", "--workspace"]
                .map(String::from)
                .into_iter(),
            Some(Path::new("/toolchain/bin/targo-tippy")),
        )
        .collect::<Vec<_>>();
        assert_eq!(external, ["--workspace"]);
    }

    #[test]
    fn help_uses_the_invoked_public_frontend() {
        assert_eq!(frontend_command_for_binary(Some("/toolchain/bin/tippy")), "tippy");
        assert_eq!(
            frontend_command_for_binary(Some("/toolchain/bin/targo-tippy")),
            "targo tippy"
        );
        assert_eq!(
            frontend_command_for_invocation(
                Some("/attacker/bin/renamed"),
                Some(Path::new("/toolchain/bin/targo-tippy")),
            ),
            "targo tippy",
            "help branding must follow the authenticated executable, not caller-controlled argv[0]"
        );
    }

    #[test]
    fn all_supported_version_spellings_are_recognized() {
        for flag in ["--version", "-V", "-vV", "-Vv"] {
            assert!(is_version_flag(flag));
        }
    }

    #[test]
    fn frontend_controls_stop_at_the_driver_separator() {
        let raw = [
            "/toolchain/bin/tippy",
            "--workspace",
            "--",
            "--help",
            "--version",
            "--explain",
        ]
        .map(String::from);
        assert_eq!(frontend_control_args(&raw), ["--workspace"]);

        let raw = ["/toolchain/bin/tippy", "--version", "--", "--help"].map(String::from);
        assert_eq!(frontend_control_args(&raw), ["--version"]);
    }

    #[cfg(unix)]
    #[test]
    fn non_unicode_frontend_arguments_are_reported_without_panicking() {
        use std::os::unix::ffi::OsStringExt as _;

        let error = unicode_args([
            std::ffi::OsString::from("tippy"),
            std::ffi::OsString::from_vec(vec![0xff]),
        ])
        .expect_err("non-Unicode argv must fail");
        assert!(error.contains("argument 1 is not valid Unicode"), "{error}");
    }

    #[test]
    fn branded_tippy_uses_sibling_targo_over_ambient_cargo() {
        let selected = targo_path_for_invocation(
            true,
            Some(PathBuf::from("/toolchain/bin/targo")),
            Some(PathBuf::from("/tmp/attacker/cargo")),
        );

        assert_eq!(selected, PathBuf::from("/toolchain/bin/targo"));
    }

    #[test]
    fn inherited_cargo_clippy_keeps_cargo_environment_compatibility() {
        let selected = targo_path_for_invocation(
            false,
            Some(PathBuf::from("/target/debug/targo")),
            Some(PathBuf::from("/custom/cargo")),
        );

        assert_eq!(selected, PathBuf::from("/custom/cargo"));
    }

    #[test]
    fn branded_tippy_uses_only_the_public_sibling_driver() {
        let selected = driver_path_for_invocation(
            true,
            Some(PathBuf::from("/toolchain/bin/tippy-driver")),
            Some(PathBuf::from("/tmp/clippy-driver")),
        );

        assert_eq!(selected, PathBuf::from("/toolchain/bin/tippy-driver"));
    }

    #[test]
    fn authenticated_executable_path_not_raw_argv0_selects_branding() {
        assert!(branded_executable(Some(Path::new("/toolchain/bin/tippy"))));
        assert!(branded_executable(Some(Path::new("/toolchain/bin/targo-tippy"))));
        assert!(!branded_executable(Some(Path::new("/target/debug/cargo-clippy"))));
    }

    #[test]
    fn recognized_raw_frontend_brand_cannot_conflict_with_executable_identity() {
        let error = validate_frontend_identity(Some("/attacker/bin/tippy"), Some(Path::new("/build/bin/cargo-clippy")))
            .expect_err("raw branded argv[0] must not promote a development frontend");
        assert!(error.contains("conflicts"), "{error}");

        let error = validate_frontend_identity(
            Some("/attacker/bin/cargo-clippy"),
            Some(Path::new("/toolchain/bin/tippy")),
        )
        .expect_err("raw development argv[0] must not demote a branded frontend");
        assert!(error.contains("conflicts"), "{error}");

        assert_eq!(
            validate_frontend_identity(Some("/attacker/bin/tippy"), Some(Path::new("/toolchain/bin/tippy")),),
            Ok(())
        );

        let error = validate_frontend_identity(
            Some("/attacker/bin/targo-tippy"),
            Some(Path::new("/toolchain/bin/tippy")),
        )
        .expect_err("same-brand frontends with different protocols must conflict");
        assert!(error.contains("argument protocol"), "{error}");
    }

    #[test]
    fn unknown_or_renamed_frontend_never_demotes_to_ambient_cargo() {
        for (raw, current) in [
            ("/attacker/bin/renamed", "/toolchain/bin/renamed-tippy"),
            ("/attacker/bin/cargo-clippy", "/toolchain/bin/renamed-tippy"),
            ("/attacker/bin/tippy.backup", "/toolchain/bin/tippy.backup"),
        ] {
            let error = validate_frontend_identity(Some(raw), Some(Path::new(current)))
                .expect_err("an unknown or renamed running executable must not enter development mode");
            assert!(
                error.contains("unrecognized name") || error.contains("cannot authenticate"),
                "{error}"
            );
        }
        assert!(
            validate_frontend_identity(Some("cargo-clippy"), None).is_ok(),
            "the explicit upstream development identity remains compatible when current_exe is unavailable"
        );
        assert!(
            validate_frontend_identity(Some("renamed-tippy"), None).is_err(),
            "an unknown argv[0] must not supply ambient development authority"
        );
    }

    #[test]
    fn frontend_names_require_complete_platform_valid_names() {
        assert_eq!(
            frontend_identity_from_path(Path::new("TIPPY.EXE"), true),
            Some(FrontendIdentity::Tippy)
        );
        assert_eq!(
            frontend_identity_from_path(Path::new("TaRgO-TiPpY.ExE"), true),
            Some(FrontendIdentity::TargoTippy)
        );
        assert_eq!(
            frontend_identity_from_path(Path::new("CARGO-CLIPPY.EXE"), true),
            Some(FrontendIdentity::CargoClippy)
        );
        assert_eq!(frontend_identity_from_path(Path::new("TIPPY"), false), None);
        assert_eq!(frontend_identity_from_path(Path::new("tippy.backup"), false), None);
        assert_eq!(frontend_identity_from_path(Path::new("tippy.com"), true), None);
    }

    #[test]
    fn development_child_drops_only_the_private_verified_lane_marker() {
        let cmd = TippyCmd::new(std::iter::empty()).unwrap().into_std_cmd_with_tools(
            PathBuf::from("/toolchain/bin/targo"),
            PathBuf::from("/toolchain/bin/tippy-driver"),
        );
        let suppression = cmd
            .get_envs()
            .find(|(name, _)| *name == "TRUST_NO_MIGRATE_WARN")
            .and_then(|(_, value)| value)
            .and_then(|value| value.to_str());

        assert_eq!(suppression, Some("1"));
        assert_eq!(
            cmd.get_envs()
                .find(|(name, _)| *name == "TRUST_TARGO_VERIFY")
                .map(|(_, value)| value),
            Some(None),
            "a Tippy lint run must not inherit the private verified-Targo marker"
        );
        assert!(
            cmd.get_envs().all(|(name, _)| name != "TRUST_VERIFY"),
            "Tippy must not rewrite unrelated compiler environment controls"
        );
        let encoded = cmd
            .get_envs()
            .find(|(name, _)| *name == super::arg_protocol::TIPPY_ENCODED_ARGS_ENV)
            .and_then(|(_, value)| value)
            .and_then(|value| value.to_str())
            .expect("encoded Tippy argument channel");
        assert_eq!(
            super::arg_protocol::decode_args(encoded),
            Ok(super::arg_protocol::DecodedTippyArgs {
                no_deps: super::arg_protocol::NoDepsFlag::Explicit(false),
                compiler_args: Vec::new(),
            })
        );
    }

    #[test]
    fn child_argument_channels_preserve_legacy_shape_and_exact_versioned_values() {
        let args = ["--warn=clippy::all", "contains__CLIPPY_HACKERY__delimiter"];
        let cmd = TippyCmd::new(std::iter::once("--".to_owned()).chain(args.into_iter().map(String::from)))
            .unwrap()
            .into_std_cmd_with_tools(
                PathBuf::from("/toolchain/bin/targo"),
                PathBuf::from("/toolchain/bin/tippy-driver"),
            );
        let envs = cmd.get_envs().collect::<Vec<_>>();
        let value = |name: &str| {
            envs.iter()
                .find(|(key, _)| *key == std::ffi::OsStr::new(name))
                .and_then(|(_, value)| *value)
                .and_then(std::ffi::OsStr::to_str)
        };

        assert_eq!(
            value(super::arg_protocol::CLIPPY_ARGS_ENV),
            Some("--warn=clippy::all__CLIPPY_HACKERY__contains__CLIPPY_HACKERY__delimiter__CLIPPY_HACKERY__")
        );
        let encoded = value(super::arg_protocol::TIPPY_ENCODED_ARGS_ENV).expect("versioned Tippy argument channel");
        assert_eq!(
            super::arg_protocol::decode_args(encoded),
            Ok(super::arg_protocol::DecodedTippyArgs {
                no_deps: super::arg_protocol::NoDepsFlag::Explicit(false),
                compiler_args: args.into_iter().map(String::from).collect(),
            })
        );
    }

    #[test]
    fn branded_child_pins_compiler_and_removes_outer_wrapper_controls() {
        let cmd = TippyCmd::new(std::iter::empty())
            .unwrap()
            .into_std_cmd_with_tools_and_compiler(
                PathBuf::from("/toolchain/bin/targo"),
                PathBuf::from("/toolchain/bin/tippy-driver"),
                Some(PathBuf::from("/toolchain/bin/rustc")),
            );
        let envs = cmd.get_envs().collect::<Vec<_>>();
        let value = |name: &str| {
            envs.iter()
                .find(|(key, _)| *key == std::ffi::OsStr::new(name))
                .map(|(_, value)| value.and_then(std::ffi::OsStr::to_str))
        };

        assert_eq!(value("RUSTC"), Some(Some("/toolchain/bin/rustc")));
        assert_eq!(value("CARGO"), Some(Some("/toolchain/bin/targo")));
        assert_eq!(
            value("RUSTC_WORKSPACE_WRAPPER"),
            Some(Some("/toolchain/bin/tippy-driver"))
        );
        for disabled in [
            "RUSTC_WRAPPER",
            "CARGO_BUILD_RUSTC_WRAPPER",
            "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
        ] {
            assert_eq!(value(disabled), Some(Some("")), "{disabled} was not disabled");
        }
        assert_eq!(value("SYSROOT"), Some(None));
        for removed in [
            super::rustc_private_overlay::HOST_DIR_ENV,
            super::rustc_private_overlay::TARGET_DIR_ENV,
        ] {
            assert_eq!(
                value(removed),
                Some(None),
                "unvalidated overlay authority {removed} was inherited"
            );
        }
    }

    fn nonexistent_temp_path(label: &str) -> PathBuf {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock after Unix epoch")
            .as_nanos();
        canonical_temp_dir().join(format!("tippy-{label}-{}-{nanos}", std::process::id()))
    }

    fn canonical_temp_dir() -> PathBuf {
        env::temp_dir().canonicalize().unwrap_or_else(|_| env::temp_dir())
    }

    #[test]
    fn required_public_siblings_must_exist_and_error_is_actionable() {
        for tool in ["targo", "tippy-driver"] {
            let path = nonexistent_temp_path(tool);
            let error = validate_sibling_executable(Some(path.clone()), tool)
                .expect_err("a missing sibling must fail validation");
            assert!(error.contains(tool));
            assert!(error.contains(&path.display().to_string()));
            assert!(error.contains("repair or reinstall"));
        }
    }

    #[test]
    fn executable_regular_file_is_accepted_as_a_sibling() {
        let current_exe = env::current_exe().expect("test executable path");
        assert_eq!(
            validate_sibling_executable(Some(current_exe.clone()), "targo").unwrap(),
            current_exe
        );
    }

    #[cfg(unix)]
    #[test]
    fn non_executable_sibling_is_rejected() {
        use std::os::unix::fs::PermissionsExt as _;

        let path = nonexistent_temp_path("non-executable-driver");
        fs::write(&path, b"not executable\n").expect("write non-executable fixture");
        let mut permissions = fs::metadata(&path).expect("fixture metadata").permissions();
        permissions.set_mode(0o600);
        fs::set_permissions(&path, permissions).expect("remove execute bits");

        let error =
            validate_sibling_executable(Some(path.clone()), "tippy-driver").expect_err("execute bits are mandatory");
        let _ = fs::remove_file(path);
        assert!(error.contains("not executable"));
        assert!(error.contains("repair or reinstall"));
    }

    #[cfg(unix)]
    #[test]
    fn public_symlink_sibling_is_rejected_but_development_discovery_remains_permissive() {
        use std::os::unix::fs::symlink;

        let target = env::current_exe().expect("test executable path");
        let path = nonexistent_temp_path("symlink-driver");
        symlink(target, &path).expect("create symlink sibling fixture");
        assert!(
            super::path_is_executable_file(&path),
            "optional development discovery should follow a valid symlink"
        );
        let error = validate_sibling_executable(Some(path.clone()), "tippy-driver")
            .expect_err("a sibling symlink must not relocate executable authority");
        let _ = fs::remove_file(path);
        assert!(error.contains("not a regular file"), "{error}");
    }

    #[test]
    fn frontend_launch_failure_returns_setup_exit_instead_of_panicking() {
        let path = nonexistent_temp_path("missing-targo-launch");
        let mut command = Command::new(&path);
        assert_eq!(
            run_frontend_command(&mut command, None),
            Err(rustc_driver::EXIT_FAILURE)
        );
    }

    #[cfg(unix)]
    #[test]
    fn frontend_preserves_the_child_signal_as_conventional_shell_status() {
        let mut command = Command::new("sh");
        command.args(["-c", "kill -TERM $$"]);
        assert_eq!(run_frontend_command(&mut command, None), Err(128 + 15));
    }

    #[test]
    fn fix() {
        let args = "cargo clippy --fix".split_whitespace().map(ToString::to_string);
        let cmd = TippyCmd::new(args).unwrap();
        assert_eq!("fix", cmd.cargo_subcommand);
        assert!(!cmd.args.iter().any(|arg| arg.ends_with("unstable-options")));
    }

    #[test]
    fn fix_implies_no_deps() {
        let args = "cargo clippy --fix".split_whitespace().map(ToString::to_string);
        let cmd = TippyCmd::new(args).unwrap();
        assert!(cmd.no_deps);
        assert!(!cmd.clippy_args.iter().any(|arg| arg == "--no-deps"));
    }

    #[test]
    fn no_deps_not_duplicated_with_fix() {
        let args = "cargo clippy --fix -- --no-deps"
            .split_whitespace()
            .map(ToString::to_string);
        let cmd = TippyCmd::new(args).unwrap();
        assert!(cmd.no_deps);
        assert!(!cmd.clippy_args.iter().any(|arg| arg == "--no-deps"));
    }

    #[test]
    fn v2_producer_does_not_steal_no_deps_spelling_used_as_a_rustc_value() {
        let cmd = TippyCmd::new(
            ["--", "--cfg", "--no-deps", "--no-deps", "-Wclippy::all"]
                .map(String::from)
                .into_iter(),
        )
        .unwrap();
        assert!(cmd.no_deps);
        assert_eq!(
            cmd.clippy_args,
            ["--cfg", "--no-deps", "-Wclippy::all"].map(String::from)
        );

        let command = cmd.into_std_cmd_with_tools(
            PathBuf::from("/toolchain/bin/targo"),
            PathBuf::from("/toolchain/bin/tippy-driver"),
        );
        let encoded = command
            .get_envs()
            .find(|(name, _)| *name == super::arg_protocol::TIPPY_ENCODED_ARGS_ENV)
            .and_then(|(_, value)| value)
            .and_then(std::ffi::OsStr::to_str)
            .expect("v2 Tippy argument payload");
        assert_eq!(
            super::arg_protocol::decode_args(encoded),
            Ok(super::arg_protocol::DecodedTippyArgs {
                no_deps: super::arg_protocol::NoDepsFlag::Explicit(true),
                compiler_args: ["--cfg", "--no-deps", "-Wclippy::all"].map(String::from).to_vec(),
            })
        );
    }

    #[test]
    fn targo_tippy_fix_keeps_the_native_fix_proxy_and_tippy_protocol_wired() {
        let command = TippyCmd::new(
            ["--fix", "--lib", "--", "-Wclippy::pedantic"]
                .map(String::from)
                .into_iter(),
        )
        .unwrap()
        .into_std_cmd_with_tools_and_compiler(
            PathBuf::from("/toolchain/bin/targo"),
            PathBuf::from("/toolchain/bin/tippy-driver"),
            Some(PathBuf::from("/toolchain/bin/trustc")),
        );
        assert_eq!(command.get_program(), std::ffi::OsStr::new("/toolchain/bin/targo"));
        assert_eq!(
            command.get_args().collect::<Vec<_>>(),
            [
                std::ffi::OsStr::new("--unverified"),
                std::ffi::OsStr::new("fix"),
                std::ffi::OsStr::new("--lib"),
            ]
        );
        let encoded = command
            .get_envs()
            .find(|(name, _)| *name == super::arg_protocol::TIPPY_ENCODED_ARGS_ENV)
            .and_then(|(_, value)| value)
            .and_then(std::ffi::OsStr::to_str)
            .expect("fix command carries authoritative Tippy arguments");
        assert_eq!(
            super::arg_protocol::decode_args(encoded),
            Ok(super::arg_protocol::DecodedTippyArgs {
                no_deps: super::arg_protocol::NoDepsFlag::Explicit(true),
                compiler_args: vec!["-Wclippy::pedantic".into()],
            })
        );
        assert_eq!(
            command
                .get_envs()
                .find(|(name, _)| *name == "RUSTC_WORKSPACE_WRAPPER")
                .and_then(|(_, value)| value),
            Some(std::ffi::OsStr::new("/toolchain/bin/tippy-driver"))
        );
        assert_eq!(
            command
                .get_envs()
                .find(|(name, _)| *name == "CARGO")
                .and_then(|(_, value)| value),
            Some(std::ffi::OsStr::new("/toolchain/bin/targo"))
        );
        assert_eq!(
            command
                .get_envs()
                .find(|(name, _)| *name == "RUSTC")
                .and_then(|(_, value)| value),
            Some(std::ffi::OsStr::new("/toolchain/bin/trustc"))
        );
        for marker in [
            "TRUST_BOOTSTRAP_SHIM_NO_VERIFY",
            "TRUST_BOOTSTRAP_SHIM_NO_VERIFY_TARGET_ONLY",
            "TRUST_BOOTSTRAP_NO_VERIFY",
            "TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY",
        ] {
            assert_eq!(
                command
                    .get_envs()
                    .find(|(name, _)| *name == marker)
                    .map(|(_, value)| value),
                Some(None),
                "branded Tippy must not combine --unverified with inherited {marker}"
            );
        }
    }

    #[test]
    fn check() {
        let args = "cargo clippy".split_whitespace().map(ToString::to_string);
        let cmd = TippyCmd::new(args).unwrap();
        assert_eq!("check", cmd.cargo_subcommand);
    }
}
