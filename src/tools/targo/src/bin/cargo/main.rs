use cargo::core::features;
use cargo::util::network::http::http_handle;
use cargo::util::network::http::needs_custom_http_transport;
use cargo::util::{self, CargoResult, closest_msg, command_prelude};
use cargo_util::{ProcessBuilder, ProcessError};
use cargo_util_schemas::manifest::StringOrVec;
use cargo_util_terminal::Shell;
use std::collections::BTreeMap;
use std::env;
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitStatus;

mod cli;
mod commands;

use crate::command_prelude::*;
use cargo::util::file_identity::{
    OpenedFileIdentity, metadata_is_plain_file, opened_file_identity,
};

fn main() {
    let _guard = setup_logger();

    // Trust: this binary is installed under two names with different authority.
    // Which one was invoked has to be settled before anything reads argv or
    // configuration, because every later decision keys off it.
    if let Err(error) = cargo::validate_frontend_invocation() {
        let mut shell = Shell::new();
        cargo::exit_with_error(
            anyhow::format_err!("could not authenticate Cargo/Targo frontend identity: {error}")
                .into(),
            &mut shell,
        );
    }

    // Trust: `cargo fix` re-enters this executable as a rustc proxy. An ambient
    // `__CARGO_FIX_PLZ` used to bypass CLI lane selection entirely. Authenticate
    // the branded parent handoff before configuration, completion handling, or
    // argv-selected compiler parsing. Ordinary Cargo retains its upstream
    // marker behavior.
    let fix_proxy_lock_addr = cargo::ops::prepare_fix_proxy_dispatch().unwrap_or_else(|error| {
        let mut shell = Shell::new();
        cargo::exit_with_error(error.into(), &mut shell)
    });

    // Trust: `$CARGO` descendants of an explicitly unverified Targo build
    // re-enter this binary without the ancestor's CLI arguments. Authenticate
    // a live exchange with that exact ancestor before project/user
    // configuration can influence command parsing. The abstract socket address
    // is inert.
    if let Err(error) = cargo::prepare_nested_unverified_targo_handoff() {
        let mut shell = Shell::new();
        cargo::exit_with_error(
            anyhow::format_err!(
                "could not authenticate nested-unverified Targo authority: {error}"
            )
            .into(),
            &mut shell,
        );
    }

    let mut gctx = match GlobalContext::default() {
        Ok(gctx) => gctx,
        Err(e) => {
            let mut shell = Shell::new();
            cargo::exit_with_error(e.into(), &mut shell)
        }
    };

    let nightly_features_allowed =
        features::nightly_features_allowed_on_channel(&features::channel());
    if nightly_features_allowed {
        let _span = tracing::span!(tracing::Level::TRACE, "completions").entered();
        let args = std::env::args_os();
        let current_dir = std::env::current_dir().ok();
        let completer = clap_complete::CompleteEnv::with_factory(|| {
            let mut gctx = GlobalContext::default().expect("already loaded without errors");
            cli::cli(&mut gctx)
        })
        .var("CARGO_COMPLETE");
        if completer
            .try_complete(args, current_dir.as_deref())
            .unwrap_or_else(|e| {
                let mut shell = Shell::new();
                cargo::exit_with_error(e.into(), &mut shell)
            })
        {
            return;
        }
    }

    let result = if let Some(lock_addr) = fix_proxy_lock_addr {
        cargo::ops::fix_exec_rustc(&gctx, &lock_addr).map_err(|e| CliError::from(e))
    } else {
        let _token = cargo::util::job::setup();
        cli::main(&mut gctx)
    };

    match result {
        Err(e) => cargo::exit_with_error(e, &mut *gctx.shell()),
        Ok(()) => {}
    }
}

fn setup_logger() -> Option<ChromeFlushGuard> {
    use tracing_subscriber::prelude::*;

    let env = tracing_subscriber::EnvFilter::from_env("CARGO_LOG");
    let fmt_layer = tracing_subscriber::fmt::layer()
        .with_timer(tracing_subscriber::fmt::time::Uptime::default())
        .with_ansi(std::io::IsTerminal::is_terminal(&std::io::stderr()))
        .with_writer(std::io::stderr)
        .with_filter(env);

    let (profile_layer, profile_guard) = chrome_layer();

    let registry = tracing_subscriber::registry()
        .with(fmt_layer)
        .with(profile_layer);
    registry.init();
    tracing::trace!(start = jiff::Timestamp::now().to_string());
    profile_guard
}

#[cfg(target_has_atomic = "64")]
type ChromeFlushGuard = tracing_chrome::FlushGuard;
#[cfg(target_has_atomic = "64")]
fn chrome_layer<S>() -> (
    Option<tracing_chrome::ChromeLayer<S>>,
    Option<ChromeFlushGuard>,
)
where
    S: tracing::Subscriber
        + for<'span> tracing_subscriber::registry::LookupSpan<'span>
        + Send
        + Sync,
{
    #![expect(clippy::disallowed_methods, reason = "runs before config is loaded")]
    if env_to_bool(std::env::var_os("CARGO_LOG_PROFILE").as_deref()) {
        let capture_args =
            env_to_bool(std::env::var_os("CARGO_LOG_PROFILE_CAPTURE_ARGS").as_deref());
        let (layer, guard) = tracing_chrome::ChromeLayerBuilder::new()
            .include_args(capture_args)
            .build();
        (Some(layer), Some(guard))
    } else {
        (None, None)
    }
}

#[cfg(not(target_has_atomic = "64"))]
type ChromeFlushGuard = ();
#[cfg(not(target_has_atomic = "64"))]
fn chrome_layer() -> (
    Option<tracing_subscriber::layer::Identity>,
    Option<ChromeFlushGuard>,
) {
    (None, None)
}

fn env_to_bool(os: Option<&OsStr>) -> bool {
    match os.and_then(|os| os.to_str()) {
        Some("1") | Some("true") => true,
        _ => false,
    }
}

/// Table for defining the aliases which come builtin in `Cargo`.
/// The contents are structured as: `(alias, aliased_command, description)`.
const BUILTIN_ALIASES: [(&str, &str, &str); 6] = [
    ("b", "build", "alias: build"),
    ("c", "check", "alias: check"),
    ("d", "doc", "alias: doc"),
    ("r", "run", "alias: run"),
    ("t", "test", "alias: test"),
    ("rm", "remove", "alias: remove"),
];

/// Function which contains the list of all of the builtin aliases and it's
/// corresponding execs represented as &str.
fn builtin_aliases_execs(cmd: &str) -> Option<&(&str, &str, &str)> {
    BUILTIN_ALIASES.iter().find(|alias| alias.0 == cmd)
}

/// Resolve the aliased command from the [`GlobalContext`] with a given command string.
///
/// The search fallback chain is:
///
/// 1. Get the aliased command as a string.
/// 2. If an `Err` occurs (missing key, type mismatch, or any possible error),
///    try to get it as an array again.
/// 3. If still cannot find any, finds one insides [`BUILTIN_ALIASES`].
fn aliased_command(gctx: &GlobalContext, command: &str) -> CargoResult<Option<Vec<String>>> {
    // Trust: these names are security boundaries in the branded frontend, so
    // upstream's "user alias wins" rule is inverted for them. They must resolve
    // to the tool shipped beside the selected `targo`, never to a
    // workspace/CARGO_HOME alias an untrusted checkout can supply.
    if !user_alias_allowed_for_invocation(cargo::is_targo_invocation(), command) {
        return Ok(None);
    }
    let alias_name = format!("alias.{}", command);
    let user_alias = match gctx.get_string(&alias_name) {
        Ok(Some(record)) => Some(
            record
                .val
                .split_whitespace()
                .map(|s| s.to_string())
                .collect(),
        ),
        Ok(None) => None,
        Err(_) => gctx.get::<Option<Vec<String>>>(&alias_name)?,
    };

    let result = user_alias.or_else(|| {
        builtin_aliases_execs(command).map(|command_str| vec![command_str.1.to_string()])
    });
    if result
        .as_ref()
        .map(|alias| alias.is_empty())
        .unwrap_or_default()
    {
        anyhow::bail!("subcommand is required, but `{alias_name}` is empty");
    }
    Ok(result)
}

/// List all runnable commands
fn list_commands(gctx: &GlobalContext) -> BTreeMap<String, CommandInfo> {
    let mut commands = third_party_subcommands(gctx);

    for cmd in commands::builtin() {
        commands.insert(
            cmd.get_name().to_string(),
            CommandInfo::BuiltIn {
                about: cmd.get_about().map(|s| s.to_string()),
            },
        );
    }

    // Add the builtin_aliases and them descriptions to the
    // `commands` `BTreeMap`.
    for command in &BUILTIN_ALIASES {
        commands.insert(
            command.0.to_string(),
            CommandInfo::BuiltIn {
                about: Some(command.2.to_string()),
            },
        );
    }

    // Add the user-defined aliases
    let alias_commands = user_defined_aliases(gctx);
    commands.extend(alias_commands);

    // `help` is special, so it needs to be inserted separately.
    commands.insert(
        "help".to_string(),
        CommandInfo::BuiltIn {
            about: Some(
                if cargo::is_targo_invocation() {
                    "Displays help for a targo command"
                } else {
                    "Displays help for a cargo command"
                }
                .to_string(),
            ),
        },
    );

    commands
}

/// Warn when branded Targo is explicitly pointed at a non-Trust compiler.
/// This cosmetic warning may be suppressed; execution-lane authorization and
/// the explicit unverified banner cannot be suppressed.
// This runs before `configure_gctx`, so the configured environment API is not
// available yet. The messages are intentionally direct CLI stderr output.
#[allow(clippy::disallowed_methods, clippy::print_stderr)]
pub(crate) fn maybe_warn_trust_compiler() {
    // Only nudge for the real targo frontend, never plain `cargo`.
    if !cargo::is_targo_invocation() {
        return;
    }
    if env_to_bool(env::var_os("TRUST_NO_MIGRATE_WARN").as_deref()) {
        return;
    }
    // Warn when RUSTC is explicitly a non-trustc compiler.
    if let Some(rustc) = env::var_os("RUSTC") {
        let rustc = PathBuf::from(&rustc);
        // The Trust compiler ships as `trustc` and as a `rustc`-named compat alias
        // (same binary; libc-compatible --version banner). Both are fine.
        if !trust_compiler_override_name(&rustc) {
            eprintln!(
                "warning: RUSTC={} is not the Trust compiler (trustc); Trust verification \
                 needs the Trust toolchain (set TRUST_NO_MIGRATE_WARN=1 to silence)",
                rustc.display()
            );
        }
    }
}

fn trust_compiler_override_name(path: &Path) -> bool {
    ["trustc", "rustc"]
        .iter()
        .any(|expected| cargo::trust_executable_path_matches(path, expected))
}

/// Trust: the branded frontend never produces an artifact whose verification
/// status is implicit. A compilation command must arrive here either inside an
/// authenticated verified session or with an explicit `--unverified`
/// authorization; there is deliberately no third, silent outcome.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TrustExecutionAuthorization {
    NotApplicable,
    Verified,
    ExplicitUnverified,
    InheritedExplicitUnverified,
}

fn authorize_trust_execution(
    is_targo: bool,
    cmd: &str,
    is_manifest_command: bool,
    explicit_unverified: bool,
    inherited_unverified: bool,
    verified_marker: bool,
    legacy_bootstrap_marker: bool,
) -> CargoResult<TrustExecutionAuthorization> {
    if is_targo && legacy_bootstrap_marker {
        anyhow::bail!(
            "legacy TRUST_BOOTSTRAP_NO_VERIFY markers do not authorize branded Targo; bootstrap must invoke the sibling `cargo` compatibility entrypoint"
        );
    }
    if !is_targo || !(is_manifest_command || is_native_compilation_command(cmd)) {
        if is_targo && explicit_unverified {
            anyhow::bail!("`--unverified` is valid only for a Targo compilation command");
        }
        return Ok(TrustExecutionAuthorization::NotApplicable);
    }

    if verified_marker && (explicit_unverified || inherited_unverified) {
        anyhow::bail!(
            "explicit-unverified Targo authority conflicts with the authenticated verified lane"
        );
    }
    if verified_marker {
        return Ok(TrustExecutionAuthorization::Verified);
    }
    if explicit_unverified && inherited_unverified {
        // A nested invocation already has a live root broker. Reuse that
        // authenticated authority rather than allowing the child to mint a
        // replacement broker merely because it also received `--unverified`.
        return Ok(TrustExecutionAuthorization::InheritedExplicitUnverified);
    }
    if explicit_unverified {
        return Ok(TrustExecutionAuthorization::ExplicitUnverified);
    }
    if inherited_unverified {
        return Ok(TrustExecutionAuthorization::InheritedExplicitUnverified);
    }

    anyhow::bail!(unauthorized_lane_message(cmd, is_manifest_command))
}

/// Trust: the `targo trust` sub-subcommand that performs the same work as a
/// branded compilation command while producing a proof claim, or `None` when
/// the verifier driver has no counterpart for it.
///
/// Naming a counterpart that does not exist would be worse than naming none: a
/// reader who types it and gets "unknown subcommand" learns that verification
/// was unavailable, when what actually happened is that this frontend guessed.
/// Only the sub-subcommands the driver dispatches (`targo-trust`'s `check`,
/// `build`, `test`) may appear here.
fn verified_trust_lane_for(cmd: &str) -> Option<&'static str> {
    match cmd {
        "build" => Some("build"),
        "check" => Some("check"),
        "test" => Some("test"),
        _ => None,
    }
}

/// Trust: this refusal is the only place a human is ever shown Targo's two
/// lanes side by side, so it names the exact command for each one and states
/// the claim that command's artifact carries.
///
/// Refusing without naming the verified spelling teaches the reader that
/// `--unverified` is how you make Targo work, which is how an unverified build
/// becomes someone's habit. Naming the lanes without naming their claims is
/// worse still: the failure this whole authorization exists to prevent is a
/// binary whose owner believes it was proved.
fn unauthorized_lane_message(cmd: &str, is_manifest_command: bool) -> String {
    let invocation = if is_manifest_command {
        format!("-Zscript {cmd}")
    } else {
        cmd.to_owned()
    };
    let unverified = format!(
        "  `targo --unverified {invocation}`\n      \
         UNVERIFIED: runs with the proof pipeline off. Anything it produces carries NO proof claim."
    );

    // A manifest command's `cmd` is the script path, so there is no
    // sub-subcommand to name; the driver has no `-Zscript` lane either.
    match verified_trust_lane_for(cmd).filter(|_| !is_manifest_command) {
        Some(lane) => format!(
            "`targo {invocation}` refuses to create an implicitly unverified artifact. \
             Targo has exactly two lanes, and neither of them is silent:\n\
             \x20 `targo trust {lane}`\n      \
             VERIFIED: fail-closed verification, an authenticated per-unit proof report, \
             and an explicit dependency-TCB assumption ledger. The artifact carries a proof claim.\n\
             {unverified}"
        ),
        None => format!(
            "`targo {invocation}` refuses to create an implicitly unverified artifact. \
             Targo has exactly two lanes, and neither of them is silent:\n\
             {unverified} This is the only lane for `{invocation}`: the verifier driver has no \
             `targo trust` counterpart for it.\n\
             \x20 `targo trust check`\n      \
             VERIFIED: verifies this crate fail-closed and writes a proof report. \
             It does not perform `{invocation}` and does not substitute for it."
        ),
    }
}

/// Establish the process-local compilation policy before Cargo constructs any
/// units. Branded Targo has exactly two authorization roots: its authenticated
/// verifier loader, or a human-visible `--unverified` decision (direct or
/// broker-authenticated from an ancestor). Bootstrap's shim controls are
/// deliberately not frontend authority.
#[allow(clippy::disallowed_methods)]
pub(crate) fn configure_trust_execution_policy(
    cmd: &str,
    is_manifest_command: bool,
    explicit_unverified: bool,
) -> CargoResult<()> {
    let verified_marker = env::var_os("TRUST_TARGO_VERIFY").as_deref() == Some(OsStr::new("1"));
    let inherited_unverified = cargo::nested_unverified_targo_handoff_active();
    let legacy_bootstrap_marker = env::var_os("TRUST_BOOTSTRAP_NO_VERIFY").is_some()
        || env::var_os("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY").is_some();
    match authorize_trust_execution(
        cargo::is_targo_invocation(),
        cmd,
        is_manifest_command,
        explicit_unverified,
        inherited_unverified,
        verified_marker,
        legacy_bootstrap_marker,
    )? {
        TrustExecutionAuthorization::Verified => {
            cargo::validate_verified_targo_startup_loader_environment()
                .map_err(anyhow::Error::msg)?;
            cargo::set_trust_verified_targo(true);
        }
        TrustExecutionAuthorization::ExplicitUnverified => {
            // Trust: this exact authorization match is the only place allowed
            // to create live nested-unverified authority.
            cargo::start_explicit_unverified_targo_broker().map_err(anyhow::Error::msg)?;
            cargo::set_trust_no_verify_fast(true);
            let invocation = if is_manifest_command {
                format!("-Zscript {cmd}")
            } else {
                cmd.to_owned()
            };
            eprintln!(
                "warning: UNVERIFIED: `targo {invocation}` was explicitly authorized with Trust verification disabled; this run emits no proof claim"
            );
        }
        TrustExecutionAuthorization::InheritedExplicitUnverified => {
            cargo::set_trust_no_verify_fast(true);
            let invocation = if is_manifest_command {
                format!("-Zscript {cmd}")
            } else {
                cmd.to_owned()
            };
            eprintln!(
                "warning: UNVERIFIED: `targo {invocation}` inherited live broker-authenticated explicit-unverified authority from its Targo ancestor; this run emits no proof claim"
            );
        }
        TrustExecutionAuthorization::NotApplicable => {}
    }
    Ok(())
}

fn is_native_compilation_command(cmd: &str) -> bool {
    matches!(
        cmd,
        "build"
            | "check"
            | "fix"
            | "clippy"
            | "miri"
            | "test"
            | "run"
            | "bench"
            | "doc"
            | "rustc"
            | "rustdoc"
            | "install"
            | "package"
            | "publish"
    )
}

fn external_subcommand_prefixes() -> &'static [&'static str] {
    external_subcommand_prefixes_for_invocation(cargo::is_targo_invocation())
}

fn external_subcommand_prefixes_for_invocation(trust_invocation: bool) -> &'static [&'static str] {
    if trust_invocation {
        &["targo-", "cargo-"]
    } else {
        &["cargo-"]
    }
}

/// Trust: one executable is installed under both `targo` and a `cargo` compat
/// symlink, so which name a user typed is a runtime fact. Every help string
/// upstream writes as a `cargo` literal has to route through here instead, or
/// the tool tells users to run a command that does not exist on their PATH.
fn frontend_binary_name() -> &'static str {
    if cargo::is_targo_invocation() {
        "targo"
    } else {
        "cargo"
    }
}

pub(crate) fn command_help_footer(command: &str) -> String {
    color_print::cformat!(
        "Run `<bright-cyan,bold>{} help {}</>` for more detailed information.\n",
        frontend_binary_name(),
        command
    )
}

pub(crate) fn command_help_footer_with_invocation(
    command: &str,
    invocation: &str,
    detail: &str,
) -> String {
    let mut footer = command_help_footer(command);
    footer.push_str(&color_print::cformat!(
        "Run `<bright-cyan,bold>{} {}</>` {}.\n",
        frontend_binary_name(),
        invocation,
        detail
    ));
    footer
}

fn third_party_subcommands(gctx: &GlobalContext) -> BTreeMap<String, CommandInfo> {
    let suffix = env::consts::EXE_SUFFIX;
    let mut commands = BTreeMap::new();
    let search_directories = search_directories(gctx);
    for prefix in external_subcommand_prefixes() {
        for dir in &search_directories {
            let entries = match fs::read_dir(dir) {
                Ok(entries) => entries,
                _ => continue,
            };
            for entry in entries.filter_map(|e| e.ok()) {
                let path = entry.path();
                let Some(filename) = path.file_name().and_then(|s| s.to_str()) else {
                    continue;
                };
                let Some(name) = filename
                    .strip_prefix(prefix)
                    .and_then(|s| s.strip_suffix(suffix))
                else {
                    continue;
                };
                if cargo::is_targo_invocation() && protected_trust_subcommand_binary(name).is_some()
                {
                    // Trust: upstream resolves external subcommands from PATH,
                    // which would let any directory on it supply `targo trust`.
                    // Protected names are added only from the selected
                    // frontend's own bin directory below.
                    continue;
                }
                if is_executable(entry.path()) {
                    commands
                        .entry(name.to_string())
                        .or_insert_with(|| CommandInfo::External { path: path.clone() });
                }
            }
        }
    }
    if cargo::is_targo_invocation()
        && let Ok(frontend) = gctx.cargo_exe()
    {
        for command in PROTECTED_TRUST_SUBCOMMANDS {
            if let Some(path) = protected_trust_subcommand_path(&frontend, command) {
                commands.insert((*command).to_string(), CommandInfo::External { path });
            }
        }
    }
    commands
}

fn user_defined_aliases(gctx: &GlobalContext) -> BTreeMap<String, CommandInfo> {
    let mut commands = BTreeMap::new();
    if let Ok(aliases) = gctx.get::<BTreeMap<String, StringOrVec>>("alias") {
        for (name, target) in aliases.iter() {
            if !user_alias_allowed_for_invocation(cargo::is_targo_invocation(), name.as_str()) {
                continue;
            }
            commands.insert(
                name.to_string(),
                CommandInfo::Alias {
                    target: target.clone(),
                },
            );
        }
    }
    commands
}

fn find_external_subcommand(gctx: &GlobalContext, cmd: &str) -> Option<PathBuf> {
    if cargo::is_targo_invocation() && protected_trust_subcommand_binary(cmd).is_some() {
        let frontend = gctx.cargo_exe().ok()?;
        return protected_trust_subcommand_path(&frontend, cmd);
    }
    let search_directories = search_directories(gctx);
    for prefix in external_subcommand_prefixes() {
        let command_exe = format!("{}{}{}", prefix, cmd, env::consts::EXE_SUFFIX);
        if let Some(path) = search_directories
            .iter()
            .map(|dir| dir.join(&command_exe))
            .find(|file| is_executable(file))
        {
            return Some(path);
        }
    }
    None
}

// Trust: everything from here to `execute_external_subcommand` is
// Trust-authored — the protected-subcommand guard. Upstream treats an external
// subcommand as an arbitrary PATH executable it spawns and forgets. For the
// branded toolchain a handful of those names carry proof, lint, formatting, or
// interpreter authority, so their binary has to be resolved from the selected
// frontend's own directory and its identity has to still hold when the run
// finishes. The guard therefore captures identity before launch and revalidates
// after, rather than checking once.
//
// On a cargo re-align this block has no upstream counterpart; only
// `execute_external_subcommand` below is shared code.

/// Branded subcommands that are installed as part of the selected Trust
/// toolchain and whose identity affects proof, lint, formatting, or interpreter
/// semantics. Ordinary third-party Cargo/Targo extensions intentionally retain
/// Cargo's historical PATH/CARGO_HOME lookup behavior.
const PROTECTED_TRUST_SUBCOMMANDS: &[&str] = &["trust", "tippy", "clippy", "fmt", "miri"];

fn protected_trust_subcommand_binary(command: &str) -> Option<&'static str> {
    match command {
        "trust" => Some("targo-trust"),
        "tippy" | "clippy" => Some("targo-tippy"),
        "fmt" => Some("targo-fmt"),
        "miri" => Some("targo-miri"),
        _ => None,
    }
}

/// Trust: `targo trust` sub-subcommands that run the developer/CI harness or a
/// diagnostic rather than produce a user-facing proof claim, and so run WITHOUT
/// the protected-subcommand guard on their OUTER wrapper.
///
/// INCLUSION CRITERION — a subcommand belongs here iff BOTH hold:
///   1. It makes no proof claim about user code (guard integrity is only
///      security-relevant for a run that credits a proof), AND
///   2. it can build / churn the in-tree `build/` toolchain directories that
///      ARE ancestors of the protected `targo-trust` binary during a long run,
///      which the post-run integrity guard would otherwise (correctly, for a
///      proof-producing run) treat as tampering — the self-inflicted false
///      positive this list removes.
///
/// `domination` runs the local gate suite (three-suite + corpus verification);
/// `doctor` builds an environment/toolchain diagnostic report. Any proof work a
/// dev-gate performs is dispatched through separately-guarded nested
/// `targo trust check`/`build` invocations, so excluding only the outer wrapper
/// weakens the guard for nothing.
///
/// NEVER add a proof-producing subcommand here (`check`, `build`, `test`,
/// `report`, `loop`, `prove`, `verify`, …): excluding one would let a raced
/// `targo-trust` swap escape detection on a run that credits a proof.
const TRUST_DEV_GATE_SUBCOMMANDS: &[&str] = &["domination", "doctor"];

/// True when this is a `targo trust <dev-gate>` invocation whose outer wrapper
/// must run WITHOUT the protected-subcommand guard. `args` is the external
/// command's argv with the repeated subcommand token at index 0
/// (`["trust", "domination", ...]`), so the sub-subcommand is the first
/// non-flag token after it.
fn trust_invocation_is_dev_gate(command: &str, args: &[&OsStr]) -> bool {
    if command != "trust" {
        return false;
    }
    args.iter()
        .skip(1)
        .filter_map(|arg| arg.to_str())
        .find(|token| !token.starts_with('-'))
        .is_some_and(|subcommand| TRUST_DEV_GATE_SUBCOMMANDS.contains(&subcommand))
}

fn user_alias_allowed_for_invocation(trust_invocation: bool, command: &str) -> bool {
    !trust_invocation || protected_trust_subcommand_binary(command).is_none()
}

fn protected_trust_subcommand_path(frontend: &Path, command: &str) -> Option<PathBuf> {
    let binary = protected_trust_subcommand_binary(command)?;
    if !frontend.is_absolute() {
        return None;
    }
    let directory = frontend.parent()?;
    let candidate = directory.join(format!("{binary}{}", env::consts::EXE_SUFFIX));
    let is_regular_file = fs::symlink_metadata(&candidate)
        .map(|metadata| metadata_is_plain_file(&metadata))
        .unwrap_or(false);
    (is_regular_file && is_executable(&candidate)).then_some(candidate)
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ProtectedPathSnapshot {
    len: u64,
    #[cfg(unix)]
    device: u64,
    #[cfg(unix)]
    inode: u64,
    #[cfg(unix)]
    mode: u32,
    #[cfg(unix)]
    links: u64,
    #[cfg(unix)]
    uid: u32,
    #[cfg(unix)]
    gid: u32,
    #[cfg(unix)]
    modified_seconds: i64,
    #[cfg(unix)]
    modified_nanoseconds: i64,
    #[cfg(unix)]
    changed_seconds: i64,
    #[cfg(unix)]
    changed_nanoseconds: i64,
    #[cfg(windows)]
    file_attributes: u32,
    #[cfg(windows)]
    creation_time: u64,
    #[cfg(windows)]
    last_write_time: u64,
}

impl ProtectedPathSnapshot {
    #[cfg(unix)]
    fn from_metadata(metadata: &fs::Metadata, _path: &Path) -> Result<Self, String> {
        use std::os::unix::fs::MetadataExt as _;

        Ok(Self {
            len: metadata.len(),
            device: metadata.dev(),
            inode: metadata.ino(),
            mode: metadata.mode(),
            links: metadata.nlink(),
            uid: metadata.uid(),
            gid: metadata.gid(),
            modified_seconds: metadata.mtime(),
            modified_nanoseconds: metadata.mtime_nsec(),
            changed_seconds: metadata.ctime(),
            changed_nanoseconds: metadata.ctime_nsec(),
        })
    }

    #[cfg(windows)]
    fn from_metadata(metadata: &fs::Metadata, path: &Path) -> Result<Self, String> {
        use std::os::windows::fs::MetadataExt as _;

        let _ = path;
        Ok(Self {
            len: metadata.len(),
            file_attributes: metadata.file_attributes(),
            creation_time: metadata.creation_time(),
            last_write_time: metadata.last_write_time(),
        })
    }

    #[cfg(not(any(unix, windows)))]
    fn from_metadata(_metadata: &fs::Metadata, path: &Path) -> Result<Self, String> {
        Err(format!(
            "cannot authenticate protected Trust path `{}` because this platform has no supported stable file-identity API",
            path.display()
        ))
    }

    // Trust: cross-time identity comparison that excludes the modification and
    // change timestamps. The OS mutates a protected executable's `ctime` (and
    // can touch `mtime`) for reasons unrelated to its contents — most notably
    // macOS writing the `com.apple.provenance` extended attribute the first
    // time the guard *executes* the binary, which bumps `ctime` between the
    // pre-launch capture and the post-run revalidation and would otherwise fail
    // the run closed against the guard's own execution side effect. Device +
    // inode (independently cross-checked via the retained `OpenedFileIdentity`
    // handle), size, mode, link count, and ownership are the fields a genuine
    // rebuild (cargo installs via a temp file + atomic rename -> new inode) or
    // tampering event actually changes; a currently-executing image cannot be
    // rewritten in place (ETXTBSY), so the timestamps were never the
    // load-bearing signal. The microsecond-wide capture-window stability check
    // (`capture_protected_path`) keeps full equality, timestamps included,
    // because no execution-time xattr write can occur inside that read-only
    // window.
    #[cfg(unix)]
    fn same_stable_identity(&self, other: &Self) -> bool {
        self.len == other.len
            && self.device == other.device
            && self.inode == other.inode
            && self.mode == other.mode
            && self.links == other.links
            && self.uid == other.uid
            && self.gid == other.gid
    }

    #[cfg(windows)]
    fn same_stable_identity(&self, other: &Self) -> bool {
        self.len == other.len && self.file_attributes == other.file_attributes
    }

    #[cfg(not(any(unix, windows)))]
    fn same_stable_identity(&self, other: &Self) -> bool {
        self == other
    }
}

struct ProtectedSubcommandGuard {
    executable: ProtectedPathGuard,
    directories: Vec<ProtectedDirectoryGuard>,
}

struct ProtectedDirectoryGuard {
    path: PathBuf,
    selected: ProtectedPathGuard,
}

struct ProtectedPathGuard {
    // On Windows this is opened with sharing that denies executable writes and
    // all path deletion/renaming. Retaining it from initial selection through
    // child completion closes timestamp-restorable rewrite/replacement races.
    _handle: fs::File,
    identity: OpenedFileIdentity,
    snapshot: ProtectedPathSnapshot,
}

impl ProtectedSubcommandGuard {
    fn capture(path: &Path) -> Result<Self, String> {
        let directory_path = path.parent().ok_or_else(|| {
            format!(
                "protected Trust subcommand `{}` has no toolchain bin directory",
                path.display()
            )
        })?;
        let canonical_directory = directory_path.canonicalize().map_err(|error| {
            format!(
                "cannot canonicalize protected Trust toolchain directory `{}`: {error}",
                directory_path.display()
            )
        })?;
        #[cfg(unix)]
        if canonical_directory != directory_path {
            return Err(format!(
                "protected Trust toolchain directory `{}` traverses a symlink or non-canonical path to `{}`",
                directory_path.display(),
                canonical_directory.display()
            ));
        }

        // The protected child is launched through a pathname. Retain the full
        // launch and canonical ancestor chains so rename -> redirect -> restore
        // of any selected directory changes the nearest unchanged parent even
        // when the original directory object itself is restored.
        let paths = protected_directory_ancestors(directory_path, &canonical_directory);
        let directories = capture_protected_directories(&paths)?;
        let executable = capture_protected_path(path, true)?;
        let confirmed_directories = capture_protected_directories(&paths)?;
        let confirmed_canonical_directory = directory_path.canonicalize().map_err(|error| {
            format!(
                "cannot re-canonicalize protected Trust toolchain directory `{}`: {error}",
                directory_path.display()
            )
        })?;
        if confirmed_canonical_directory != canonical_directory {
            return Err(format!(
                "protected Trust toolchain directory `{}` changed canonical target from `{}` to `{}` while subcommand identity was captured",
                directory_path.display(),
                canonical_directory.display(),
                confirmed_canonical_directory.display()
            ));
        }
        if !same_protected_directories(&directories, &confirmed_directories) {
            return Err(format!(
                "protected Trust toolchain directory chain `{}` changed while subcommand identity was captured",
                directory_path.display()
            ));
        }
        Ok(Self {
            executable,
            directories,
        })
    }

    fn same_identity(&self, other: &Self) -> bool {
        self.executable.identity == other.executable.identity
            && self.executable.snapshot.same_stable_identity(&other.executable.snapshot)
            && same_protected_directories(&self.directories, &other.directories)
    }
}

fn protected_directory_ancestors(launch: &Path, canonical: &Path) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    for ancestor in launch.ancestors().chain(canonical.ancestors()) {
        if !paths.iter().any(|path| path == ancestor) {
            paths.push(ancestor.to_owned());
        }
    }
    paths
}

fn capture_protected_directories(
    paths: &[PathBuf],
) -> Result<Vec<ProtectedDirectoryGuard>, String> {
    paths
        .iter()
        .map(|path| {
            let selected = capture_protected_path(path, false)?;
            Ok(ProtectedDirectoryGuard {
                path: path.clone(),
                selected,
            })
        })
        .collect()
}

fn same_protected_directories(
    left: &[ProtectedDirectoryGuard],
    right: &[ProtectedDirectoryGuard],
) -> bool {
    left.len() == right.len()
        && left.iter().zip(right).all(|(left, right)| {
            left.path == right.path
                && left.selected.identity == right.selected.identity
                // Trust: directories keep FULL snapshot equality, timestamps
                // included. A rename -> redirect -> restore of an ancestor
                // preserves that directory's own inode, so the changed
                // modification/change time is the only signal that reveals the
                // race — and executing a binary never mutates a parent
                // directory's timestamps, so the provenance-xattr false
                // positive that motivates `same_stable_identity` cannot arise
                // here. Only the executable file needs the timestamp-tolerant
                // comparison.
                && left.selected.snapshot == right.selected.snapshot
        })
}

struct AuthenticatedProtectedSubcommand {
    path: PathBuf,
    selected: ProtectedSubcommandGuard,
}

impl AuthenticatedProtectedSubcommand {
    fn capture(path: PathBuf) -> Result<Self, String> {
        if !path.is_absolute() {
            return Err(format!(
                "protected Trust subcommand `{}` is not an absolute selected-toolchain path",
                path.display()
            ));
        }
        let selected = ProtectedSubcommandGuard::capture(&path)?;
        Ok(Self { path, selected })
    }

    /// Run a protected child with latest-boundary handles open, then reject
    /// its result if the executable or full launch/canonical directory chain
    /// no longer has the selected identity. This is not stable-handle execution:
    /// the process abstraction still launches a pathname, so a raced child's
    /// side effects can occur before the post-check rejects its result. Unrelated
    /// direct-entry churn in a recorded shared ancestor can also fail closed.
    fn run_guarded<T>(&self, operation: impl FnOnce() -> T) -> Result<T, String> {
        let guard = self.revalidate().map_err(|error| {
            format!("protected Trust subcommand authentication failed before launch: {error}")
        })?;
        let result = operation();
        let _post_guard = self.revalidate().map_err(|error| {
            format!(
                "protected Trust subcommand `{}` changed while it was running: {error}",
                self.path.display()
            )
        })?;
        drop(guard);
        Ok(result)
    }

    fn revalidate(&self) -> Result<ProtectedSubcommandGuard, String> {
        let current = ProtectedSubcommandGuard::capture(&self.path)?;
        if !self.selected.same_identity(&current) {
            return Err(format!(
                "selected protected Trust subcommand `{}` changed identity or contents",
                self.path.display()
            ));
        }
        Ok(current)
    }
}

fn capture_protected_path(
    path: &Path,
    require_executable: bool,
) -> Result<ProtectedPathGuard, String> {
    let before = fs::symlink_metadata(path).map_err(|error| {
        format!(
            "cannot inspect protected Trust path `{}`: {error}",
            path.display()
        )
    })?;
    if !protected_path_type_is_valid(&before, require_executable) {
        return Err(format!(
            "protected Trust path `{}` is not an admissible protected {} object",
            path.display(),
            if require_executable {
                "file"
            } else {
                "directory"
            }
        ));
    }
    if require_executable && !metadata_is_executable(&before) {
        return Err(format!(
            "protected Trust subcommand `{}` is not executable",
            path.display()
        ));
    }
    let before_snapshot = ProtectedPathSnapshot::from_metadata(&before, path)?;
    let handle = open_protected_path(path, &before, require_executable).map_err(|error| {
        format!(
            "cannot open protected Trust path `{}`: {error}",
            path.display()
        )
    })?;
    let identity = opened_file_identity(&handle).map_err(|error| {
        format!(
            "cannot identify opened protected Trust path `{}`: {error}",
            path.display()
        )
    })?;
    let opened = handle.metadata().map_err(|error| {
        format!(
            "cannot inspect opened protected Trust path `{}`: {error}",
            path.display()
        )
    })?;
    let opened_snapshot = ProtectedPathSnapshot::from_metadata(&opened, path)?;
    let after = fs::symlink_metadata(path).map_err(|error| {
        format!(
            "cannot re-inspect protected Trust path `{}`: {error}",
            path.display()
        )
    })?;
    let after_snapshot = ProtectedPathSnapshot::from_metadata(&after, path)?;
    let path_handle = open_protected_path(path, &after, require_executable).map_err(|error| {
        format!(
            "cannot reopen protected Trust path `{}`: {error}",
            path.display()
        )
    })?;
    let path_snapshot = path_handle
        .metadata()
        .map_err(|error| {
            format!(
                "cannot inspect reopened protected Trust path `{}`: {error}",
                path.display()
            )
        })
        .and_then(|metadata| ProtectedPathSnapshot::from_metadata(&metadata, path))?;
    let path_identity = opened_file_identity(&path_handle).map_err(|error| {
        format!(
            "cannot identify reopened protected Trust path `{}`: {error}",
            path.display()
        )
    })?;
    if before_snapshot != opened_snapshot
        || opened_snapshot != after_snapshot
        || after_snapshot != path_snapshot
        || identity != path_identity
    {
        return Err(format!(
            "protected Trust path `{}` changed while its identity was captured",
            path.display()
        ));
    }
    Ok(ProtectedPathGuard {
        _handle: handle,
        identity,
        snapshot: opened_snapshot,
    })
}

fn protected_path_type_is_valid(metadata: &fs::Metadata, require_executable: bool) -> bool {
    if require_executable {
        return metadata_is_plain_file(metadata);
    }

    #[cfg(windows)]
    {
        use std::os::windows::fs::MetadataExt as _;

        const FILE_ATTRIBUTE_DIRECTORY: u32 = 0x0000_0010;
        metadata.file_attributes() & FILE_ATTRIBUTE_DIRECTORY != 0
    }
    #[cfg(not(windows))]
    {
        !metadata.file_type().is_symlink() && metadata.file_type().is_dir()
    }
}

#[cfg(not(windows))]
fn open_protected_path(
    path: &Path,
    _metadata: &fs::Metadata,
    _require_executable: bool,
) -> std::io::Result<fs::File> {
    fs::File::open(path)
}

#[cfg(windows)]
fn open_protected_path(
    path: &Path,
    metadata: &fs::Metadata,
    require_executable: bool,
) -> std::io::Result<fs::File> {
    use std::os::windows::fs::{MetadataExt as _, OpenOptionsExt as _};

    const FILE_SHARE_READ: u32 = 0x0000_0001;
    const FILE_SHARE_WRITE: u32 = 0x0000_0002;
    const FILE_ATTRIBUTE_REPARSE_POINT: u32 = 0x0000_0400;
    const FILE_FLAG_BACKUP_SEMANTICS: u32 = 0x0200_0000;
    const FILE_FLAG_OPEN_REPARSE_POINT: u32 = 0x0020_0000;

    if require_executable {
        return fs::OpenOptions::new()
            .read(true)
            // Executable contents and pathname selection stay immutable for
            // the lifetime of the retained guard.
            .share_mode(FILE_SHARE_READ)
            .open(path);
    }

    let share_mode = if metadata.file_attributes() & FILE_ATTRIBUTE_REPARSE_POINT != 0 {
        // A junction/symlink target is writable reparse data; deny both write
        // and delete sharing while retaining the launch and canonical chains.
        FILE_SHARE_READ
    } else {
        // Permit ordinary descendant access, but prevent this directory object
        // from being renamed or deleted out from under the selected path.
        FILE_SHARE_READ | FILE_SHARE_WRITE
    };
    fs::OpenOptions::new()
        .access_mode(0)
        .share_mode(share_mode)
        .custom_flags(FILE_FLAG_BACKUP_SEMANTICS | FILE_FLAG_OPEN_REPARSE_POINT)
        .open(path)
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

fn execute_external_subcommand(gctx: &GlobalContext, cmd: &str, args: &[&OsStr]) -> CliResult {
    let path = find_external_subcommand(gctx, cmd);
    let command = match path {
        Some(command) => command,
        None => {
            let script_suggestion = if gctx.cli_unstable().script
                && std::path::Path::new(cmd).is_file()
            {
                let sep = std::path::MAIN_SEPARATOR;
                format!(
                    "\nhelp: to run the file `{cmd}`, provide a relative path like `.{sep}{cmd}`"
                )
            } else {
                "".to_owned()
            };
            let err = if cmd.starts_with('+') {
                anyhow::format_err!(
                    "no such command: `{cmd}`\n\n\
                    help: invoke `{}` through `rustup` to handle `+toolchain` directives{script_suggestion}",
                    frontend_binary_name(),
                )
            } else {
                let suggestions = list_commands(gctx);
                // Trust: upstream 1.99's rustfmt->fmt hint, extended to the
                // Trust spelling (`trustfmt`).
                let did_you_mean = if cmd == "rustfmt" || cmd == "trustfmt" {
                    "\n\nhelp: a command with a similar name exists: `fmt`".to_string()
                } else {
                    closest_msg(cmd, suggestions.keys(), |c| c, "command")
                };
                let frontend = frontend_binary_name();
                let package_prefix = if cargo::is_targo_invocation() {
                    "targo"
                } else {
                    "cargo"
                };

                anyhow::format_err!(
                    "no such command: `{cmd}`{did_you_mean}\n\n\
                    help: view all installed commands with `{frontend} --list`\n\
                    help: find a package to install `{cmd}` with `{frontend} search {package_prefix}-{cmd}`{script_suggestion}",
                )
            };

            return Err(CliError::new(err, 101));
        }
    };
    let protected = cargo::is_targo_invocation()
        && protected_trust_subcommand_binary(cmd).is_some()
        && !trust_invocation_is_dev_gate(cmd, args);
    execute_subcommand(gctx, Some(&command), args, protected)
}

fn execute_internal_subcommand(gctx: &GlobalContext, args: &[&OsStr]) -> CliResult {
    execute_subcommand(gctx, None, args, false)
}

// This function is used to execute a subcommand. It is used to execute both
// internal and external subcommands.
// If `cmd_path` is `None`, then the subcommand is an internal subcommand.
fn execute_subcommand(
    gctx: &GlobalContext,
    cmd_path: Option<&PathBuf>,
    args: &[&OsStr],
    protected: bool,
) -> CliResult {
    let cargo_exe = gctx.cargo_exe()?;
    let mut cmd = match cmd_path {
        Some(cmd_path) => ProcessBuilder::new(cmd_path),
        None => ProcessBuilder::new(&cargo_exe),
    };
    cmd.env(cargo::CARGO_ENV, cargo_exe).args(args);
    if let Some(client) = gctx.jobserver_from_env() {
        cmd.inherit_jobserver(client);
    }

    // Trust: a protected subcommand cannot use upstream's `exec_replace` — this
    // process has to survive the child in order to revalidate the toolchain
    // identity it captured before launch.
    if protected {
        let path = cmd_path.expect("only an external Trust subcommand can be protected");
        let authenticated =
            AuthenticatedProtectedSubcommand::capture(path.clone()).map_err(|error| {
                CliError::new(
                    anyhow::format_err!(
                        "could not authenticate protected Trust subcommand: {error}"
                    ),
                    // Same authority class as a post-run guard trip, just
                    // detected before launch.
                    PROTECTED_SUBCOMMAND_AUTHORITY_EXIT,
                )
            })?;
        return finish_guarded_protected_subcommand(authenticated.run_guarded(|| cmd.status()));
    }

    let err = match cmd.exec_replace() {
        Ok(()) => return Ok(()),
        Err(e) => e,
    };

    if let Some(perr) = err.downcast_ref::<ProcessError>() {
        if let Some(code) = perr.code {
            return Err(CliError::code(code));
        }
    }
    Err(CliError::new(err, 101))
}

/// Trust: exit code for a protected-subcommand AUTHORITY failure (the toolchain
/// or its recorded ancestor chain changed while the subcommand ran, so the
/// captured identity can no longer be trusted).
///
/// This is a setup/toolchain-authority failure, which the CLI contract numbers
/// 2 — the same code `targo-trust`'s own pipeline returns for every
/// setup/evidence failure. It is NOT 101: cargo reserves 101 for "could not
/// compile", so mapping a raced toolchain there makes an environment defect
/// impersonate a compiler crash, and (worse) DISCARDS the child's real exit
/// status after it has already written a complete, sealed report to stdout —
/// turning an honest `exit 1` verification-gate failure into an unexplained
/// 101.
const PROTECTED_SUBCOMMAND_AUTHORITY_EXIT: i32 = 2;

/// Trust: the single mapping point from a guarded protected-subcommand run to
/// this process's exit contract.
///
/// A guard failure NEVER inherits or fabricates the child's status (the guard
/// exists precisely because the child's identity is in doubt); the child's own
/// status governs only when the guard HOLDS. Extracted from
/// `execute_subcommand` so the mapping is unit-testable without a
/// `GlobalContext`.
fn finish_guarded_protected_subcommand(
    outcome: Result<CargoResult<ExitStatus>, String>,
) -> CliResult {
    let status = outcome
        .map_err(|error| {
            CliError::new(anyhow::format_err!(error), PROTECTED_SUBCOMMAND_AUTHORITY_EXIT)
        })?
        // A spawn-level io error genuinely is "cargo could not execute the
        // tool", which is cargo's own 101 convention.
        .map_err(|error| CliError::new(error, 101))?;
    if status.success() {
        Ok(())
    } else {
        Err(CliError::code(subcommand_exit_status_code(&status)))
    }
}

fn subcommand_exit_status_code(status: &ExitStatus) -> i32 {
    if let Some(code) = status.code() {
        return code;
    }

    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt as _;

        if let Some(signal) = status.signal() {
            return 128_i32.saturating_add(signal).min(u8::MAX.into());
        }
    }

    101
}

#[cfg(unix)]
fn is_executable<P: AsRef<Path>>(path: P) -> bool {
    use std::os::unix::prelude::*;
    fs::metadata(path)
        .map(|metadata| metadata.is_file() && metadata.permissions().mode() & 0o111 != 0)
        .unwrap_or(false)
}
#[cfg(windows)]
fn is_executable<P: AsRef<Path>>(path: P) -> bool {
    path.as_ref().is_file()
}

fn search_directories(gctx: &GlobalContext) -> Vec<PathBuf> {
    let mut path_dirs = if let Some(val) = gctx.get_env_os("PATH") {
        env::split_paths(&val).collect()
    } else {
        vec![]
    };

    let home_bin = gctx.home().clone().into_path_unlocked().join("bin");

    // If any of that PATH elements contains `home_bin`, do not
    // add it again. This is so that the users can control priority
    // of it using PATH, while preserving the historical
    // behavior of preferring it over system global directories even
    // when not in PATH at all.
    // See https://github.com/rust-lang/cargo/issues/11020 for details.
    //
    // Note: `p == home_bin` will ignore trailing slash, but we don't
    // `canonicalize` the paths.
    if !path_dirs.iter().any(|p| p == &home_bin) {
        path_dirs.insert(0, home_bin);
    };

    // Trust toolchains ship `targo-trust` as a sibling of the installed
    // `targo` binary. rustup does not add arbitrary component binaries to PATH.
    // This directory must be first: inserting CARGO_HOME after it used to let a
    // stale or attacker-controlled `~/.cargo/bin/targo-trust` shadow the
    // verifier bundled with the selected Trust toolchain.
    if cargo::is_targo_invocation()
        && let Ok(frontend_exe) = gctx.cargo_exe()
        && let Some(current_bin) = frontend_exe.parent()
    {
        path_dirs.retain(|path| path != current_bin);
        path_dirs.insert(0, current_bin.to_path_buf());
    }

    path_dirs
}

// Trust: pins the frontend's authorization contract — lane selection, alias and
// external-subcommand resolution, and the guard's exit-code mapping. These live
// here rather than in `tests/testsuite` because a testsuite binary cannot
// observe this process's own argv-derived frontend identity.
#[cfg(test)]
mod trust_tests {
    use super::{
        AuthenticatedProtectedSubcommand, PROTECTED_SUBCOMMAND_AUTHORITY_EXIT,
        TrustExecutionAuthorization, authorize_trust_execution, env_to_bool,
        external_subcommand_prefixes_for_invocation, finish_guarded_protected_subcommand,
        is_native_compilation_command, protected_trust_subcommand_binary,
        protected_trust_subcommand_path, subcommand_exit_status_code,
        trust_compiler_override_name, trust_invocation_is_dev_gate, unauthorized_lane_message,
        user_alias_allowed_for_invocation, verified_trust_lane_for,
    };
    use cargo::CargoResult;
    use std::ffi::{OsStr, OsString};
    use std::fs;
    use std::path::Path;
    use std::process::{Command, ExitStatus};
    use std::sync::Mutex;

    static PROTECTED_FIXTURE_LOCK: Mutex<()> = Mutex::new(());

    #[test]
    fn trust_boolean_environment_values_are_explicit() {
        assert!(env_to_bool(Some(OsStr::new("1"))));
        assert!(env_to_bool(Some(OsStr::new("true"))));
        assert!(!env_to_bool(Some(OsStr::new("0"))));
        assert!(!env_to_bool(Some(OsStr::new("false"))));
        assert!(!env_to_bool(Some(OsStr::new(""))));
        assert!(!env_to_bool(None));
    }

    #[test]
    fn every_native_compilation_command_requires_an_explicit_lane() {
        for command in [
            "build", "check", "fix", "clippy", "miri", "test", "run", "bench", "doc", "rustc",
            "rustdoc", "install", "package", "publish",
        ] {
            assert!(
                is_native_compilation_command(command),
                "native `{command}` transport must require an explicit authorization lane"
            );
        }
        for command in ["trust", "metadata", "fetch"] {
            assert!(!is_native_compilation_command(command));
        }
    }

    #[test]
    fn branded_native_compilation_refuses_implicit_unverified_mode() {
        let error = authorize_trust_execution(true, "build", false, false, false, false, false)
            .expect_err("implicit unverified Targo must fail");
        assert!(error.to_string().contains("implicitly unverified artifact"));
    }

    #[test]
    fn the_refusal_names_both_lanes_and_the_claim_each_artifact_carries() {
        // A refusal that only forbids leaves the reader to discover
        // `--unverified` first, because it is the spelling the message
        // mentions. Both exact commands, and what each one's artifact asserts,
        // have to be in the text a human actually sees.
        let message = unauthorized_lane_message("build", false);
        assert!(message.contains("`targo trust build`"), "{message}");
        assert!(message.contains("`targo --unverified build`"), "{message}");
        let verified = message.find("VERIFIED: fail-closed").expect("verified lane claim");
        let unverified = message.find("UNVERIFIED:").expect("unverified lane claim");
        assert!(
            verified < unverified,
            "the lane that carries a proof claim is the one being recommended: {message}"
        );
        assert!(message.contains("carries a proof claim"), "{message}");
        assert!(message.contains("carries NO proof claim"), "{message}");

        for (command, lane) in [("check", "check"), ("test", "test")] {
            let message = unauthorized_lane_message(command, false);
            assert!(message.contains(&format!("`targo trust {lane}`")), "{message}");
            assert!(message.contains(&format!("`targo --unverified {command}`")), "{message}");
        }
    }

    #[test]
    fn a_command_with_no_verified_counterpart_is_told_so_rather_than_sent_to_one() {
        // `targo trust doc` does not exist. Printing it would read as "you
        // declined verification", when the truth is that this command has no
        // verified lane at all — and the reader would then run a command that
        // errors out with `unknown subcommand`.
        for command in ["doc", "miri", "run", "install", "publish"] {
            assert!(
                verified_trust_lane_for(command).is_none(),
                "`targo trust {command}` is not a driver subcommand"
            );
            let message = unauthorized_lane_message(command, false);
            assert!(
                !message.contains(&format!("targo trust {command}")),
                "invented a verified lane for `{command}`: {message}"
            );
            assert!(message.contains("This is the only lane for"), "{message}");
            assert!(
                message.contains(&format!("does not perform `{command}`")),
                "the nearest verified lane must not read as an equivalent: {message}"
            );
        }
    }

    #[test]
    fn a_manifest_command_is_not_offered_a_script_lane_the_driver_lacks() {
        // Here `cmd` is the script path, not a subcommand name, and the driver
        // resolves no embedded manifest. Substituting the path into
        // `targo trust <cmd>` would print a command that cannot work.
        let message = unauthorized_lane_message("./script.rs", true);
        assert!(message.contains("`targo --unverified -Zscript ./script.rs`"), "{message}");
        assert!(!message.contains("targo trust ./script.rs"), "{message}");
        assert!(message.contains("`targo trust check`"), "{message}");
    }

    #[test]
    fn branded_native_compilation_accepts_each_authenticated_or_explicit_lane() {
        assert_eq!(
            authorize_trust_execution(true, "check", false, true, false, false, false).unwrap(),
            TrustExecutionAuthorization::ExplicitUnverified
        );
        assert_eq!(
            authorize_trust_execution(true, "check", false, false, true, false, false).unwrap(),
            TrustExecutionAuthorization::InheritedExplicitUnverified
        );
        assert_eq!(
            authorize_trust_execution(true, "test", false, false, false, true, false).unwrap(),
            TrustExecutionAuthorization::Verified
        );
    }

    #[test]
    fn legacy_bootstrap_markers_never_authorize_branded_targo() {
        for command in ["build", "metadata"] {
            let error = authorize_trust_execution(true, command, false, false, false, false, true)
                .expect_err("legacy ambient marker must fail before command dispatch");
            assert!(error.to_string().contains("do not authorize branded Targo"));
        }
    }

    #[test]
    fn targo_authorization_lanes_cannot_be_combined_or_misapplied() {
        assert!(authorize_trust_execution(true, "build", false, true, false, true, false).is_err());
        assert!(authorize_trust_execution(true, "build", false, false, true, true, false).is_err());
        assert!(authorize_trust_execution(true, "build", false, false, false, true, true).is_err());
        assert_eq!(
            authorize_trust_execution(true, "build", false, true, true, false, false).unwrap(),
            TrustExecutionAuthorization::InheritedExplicitUnverified,
            "an explicit flag in an inherited subtree must reuse the live root broker"
        );
        assert!(
            authorize_trust_execution(true, "metadata", false, true, false, false, false).is_err()
        );
        assert_eq!(
            authorize_trust_execution(true, "metadata", false, false, true, false, false).unwrap(),
            TrustExecutionAuthorization::NotApplicable,
            "an inherited capability grants only native compilation authority"
        );
    }

    #[test]
    fn cargo_compatibility_identity_is_never_promoted_by_targo_markers() {
        for command in ["build", "miri"] {
            assert_eq!(
                authorize_trust_execution(false, command, false, false, true, true, true).unwrap(),
                TrustExecutionAuthorization::NotApplicable
            );
        }
    }

    #[test]
    fn branded_manifest_script_is_a_native_compilation_entry_path() {
        let error =
            authorize_trust_execution(true, "./subject.rs", true, false, false, false, false)
                .expect_err("implicit Targo script compilation must fail");
        assert!(error.to_string().contains("implicitly unverified artifact"));
        assert!(error.to_string().contains("-Zscript ./subject.rs"));
        assert_eq!(
            authorize_trust_execution(true, "./subject.rs", true, true, false, false, false)
                .unwrap(),
            TrustExecutionAuthorization::ExplicitUnverified
        );
        assert_eq!(
            authorize_trust_execution(false, "./subject.rs", true, false, true, true, false)
                .unwrap(),
            TrustExecutionAuthorization::NotApplicable,
            "ordinary Cargo script behavior remains outside Targo policy"
        );
    }

    #[test]
    fn compiler_override_warning_uses_whole_executable_names() {
        assert!(trust_compiler_override_name(Path::new("trustc")));
        assert!(trust_compiler_override_name(Path::new("rustc")));
        assert!(!trust_compiler_override_name(Path::new("trustc.backup")));
        assert!(!trust_compiler_override_name(Path::new("not-rustc")));
        if !cfg!(windows) {
            assert!(!trust_compiler_override_name(Path::new("TRUSTC")));
            assert!(!trust_compiler_override_name(Path::new("trustc.exe")));
        }
    }

    #[test]
    fn targo_prefers_trust_subcommand_names() {
        assert_eq!(
            external_subcommand_prefixes_for_invocation(true),
            &["targo-", "cargo-"]
        );
        assert_eq!(
            external_subcommand_prefixes_for_invocation(false),
            &["cargo-"]
        );
    }

    #[test]
    fn protected_front_doors_have_one_bundled_binary_identity() {
        assert_eq!(
            protected_trust_subcommand_binary("trust"),
            Some("targo-trust")
        );
        assert_eq!(
            protected_trust_subcommand_binary("tippy"),
            Some("targo-tippy")
        );
        assert_eq!(
            protected_trust_subcommand_binary("clippy"),
            Some("targo-tippy")
        );
        assert_eq!(protected_trust_subcommand_binary("fmt"), Some("targo-fmt"));
        assert_eq!(
            protected_trust_subcommand_binary("miri"),
            Some("targo-miri")
        );
        assert_eq!(protected_trust_subcommand_binary("third-party"), None);
    }

    #[test]
    fn branded_front_door_aliases_cannot_shadow_bundled_tools() {
        for command in ["trust", "tippy", "clippy", "fmt", "miri"] {
            assert!(
                !user_alias_allowed_for_invocation(true, command),
                "[alias] {command} must not replace a bundled Trust front door"
            );
            assert!(
                user_alias_allowed_for_invocation(false, command),
                "ordinary Cargo alias semantics must remain unchanged"
            );
        }
        assert!(user_alias_allowed_for_invocation(true, "third-party"));
    }

    #[cfg(unix)]
    #[test]
    fn protected_front_door_never_falls_back_to_ambient_or_nonexecutable_binary() {
        use std::os::unix::fs::PermissionsExt as _;

        let _lock = PROTECTED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let temp = std::env::temp_dir()
            .canonicalize()
            .unwrap_or_else(|_| std::env::temp_dir());
        let root = temp.join(format!(
            "targo-protected-command-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let selected_bin = root.join("selected/bin");
        let ambient_bin = root.join("ambient/bin");
        fs::create_dir_all(&selected_bin).expect("create selected bin");
        fs::create_dir_all(&ambient_bin).expect("create ambient bin");
        let frontend = selected_bin.join("targo");
        fs::write(&frontend, b"frontend").expect("write frontend fixture");
        assert_eq!(
            protected_trust_subcommand_path(std::path::Path::new("targo"), "trust"),
            None,
            "relative frontend identity must fail closed"
        );
        let ambient = ambient_bin.join("targo-trust");
        fs::write(&ambient, b"ambient shadow").expect("write ambient fixture");
        fs::set_permissions(&ambient, fs::Permissions::from_mode(0o755))
            .expect("make ambient fixture executable");

        assert_eq!(
            protected_trust_subcommand_path(&frontend, "trust"),
            None,
            "an executable ambient shadow must not satisfy a missing sibling"
        );

        let sibling = selected_bin.join("targo-trust");
        fs::write(&sibling, b"selected but not executable").expect("write sibling fixture");
        fs::set_permissions(&sibling, fs::Permissions::from_mode(0o644))
            .expect("make sibling nonexecutable");
        assert_eq!(protected_trust_subcommand_path(&frontend, "trust"), None);

        fs::set_permissions(&sibling, fs::Permissions::from_mode(0o755))
            .expect("make sibling executable");
        assert_eq!(
            protected_trust_subcommand_path(&frontend, "trust"),
            Some(sibling)
        );

        fs::remove_file(&selected_bin.join("targo-trust")).expect("remove regular sibling");
        std::os::unix::fs::symlink(&ambient, selected_bin.join("targo-trust"))
            .expect("install sibling symlink shadow");
        assert_eq!(
            protected_trust_subcommand_path(&frontend, "trust"),
            None,
            "protected front doors require a regular sibling executable, not a redirecting symlink"
        );
        let _ = fs::remove_dir_all(root);
    }

    #[cfg(windows)]
    #[test]
    fn protected_windows_handles_deny_hidden_rewrite_and_ancestor_rename() {
        let _lock = PROTECTED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let temp = std::env::temp_dir()
            .canonicalize()
            .unwrap_or_else(|_| std::env::temp_dir());
        let root = temp.join(format!(
            "targo-protected-windows-lock-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let bin = root.join("bin");
        fs::create_dir_all(&bin).expect("create selected Windows toolchain directory");
        let command = bin.join("targo-trust.exe");
        fs::write(&command, b"selected protected Windows command")
            .expect("write selected Windows command");

        let authenticated = AuthenticatedProtectedSubcommand::capture(command.clone())
            .expect("authenticate protected Windows command");
        assert!(
            fs::OpenOptions::new().write(true).open(&command).is_err(),
            "protected executable unexpectedly shared write authority"
        );
        let renamed = root.join("bin-renamed");
        assert!(
            fs::rename(&bin, &renamed).is_err(),
            "protected directory unexpectedly shared delete/rename authority"
        );

        drop(authenticated);
        fs::rename(&bin, &renamed).expect("selection locks are released when the guard is dropped");
        fs::remove_dir_all(root).expect("remove protected Windows fixture");
    }

    #[cfg(unix)]
    #[test]
    fn protected_subcommand_guard_rejects_rewrite_and_swap_restore() {
        use std::os::unix::fs::PermissionsExt as _;

        let _lock = PROTECTED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let temp = std::env::temp_dir()
            .canonicalize()
            .unwrap_or_else(|_| std::env::temp_dir());
        let root = temp.join(format!(
            "targo-protected-command-identity-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        fs::create_dir(&root).expect("create protected-command identity fixture");
        let command = root.join("targo-trust");
        let replacement = root.join("replacement");
        let saved = root.join("saved");
        fs::write(&command, b"selected protected command").expect("write selected command");
        fs::set_permissions(&command, fs::Permissions::from_mode(0o755))
            .expect("make selected command executable");

        let authenticated = AuthenticatedProtectedSubcommand::capture(command.clone())
            .expect("authenticate protected command");
        let rewrite = authenticated.run_guarded(|| {
            fs::write(&command, b"hostile protected command").expect("rewrite selected command");
        });
        assert!(
            rewrite.is_err(),
            "an in-place protected-command rewrite was accepted"
        );
        assert_eq!(
            fs::read(&command).expect("read rewritten command"),
            b"hostile protected command",
            "rewrite fixture did not reach the guarded operation"
        );
        drop(authenticated);

        fs::write(&command, b"selected protected command").expect("restore selected bytes");
        fs::set_permissions(&command, fs::Permissions::from_mode(0o755))
            .expect("restore selected permissions");
        fs::write(&replacement, b"hostile protected command").expect("write hostile replacement");
        fs::set_permissions(&replacement, fs::Permissions::from_mode(0o755))
            .expect("make hostile replacement executable");
        let authenticated = AuthenticatedProtectedSubcommand::capture(command.clone())
            .expect("reauthenticate protected command");
        let swap_restore = authenticated.run_guarded(|| {
            fs::rename(&command, &saved).expect("save selected command inode");
            fs::rename(&replacement, &command).expect("install hostile command");
            fs::remove_file(&command).expect("remove hostile command");
            fs::rename(&saved, &command).expect("restore exact selected inode");
        });
        assert!(
            swap_restore.is_err(),
            "a swap-and-restore escaped protected toolchain-directory authentication"
        );
        assert!(
            !replacement.exists(),
            "swap-and-restore fixture did not reach the guarded operation"
        );

        drop(authenticated);
        fs::remove_dir_all(root).expect("remove protected-command identity fixture");
    }

    #[cfg(unix)]
    #[test]
    fn protected_subcommand_guard_rejects_mutable_ancestor_symlink() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let _lock = PROTECTED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let temp = std::env::temp_dir()
            .canonicalize()
            .unwrap_or_else(|_| std::env::temp_dir());
        let root = temp.join(format!(
            "targo-protected-command-symlink-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let real_bin = root.join("real/bin");
        fs::create_dir_all(&real_bin).expect("create real protected-command directory");
        let command = real_bin.join("targo-trust");
        fs::write(&command, b"selected protected command").expect("write selected command");
        fs::set_permissions(&command, fs::Permissions::from_mode(0o755))
            .expect("make selected command executable");
        let redirected_root = root.join("redirected");
        symlink(root.join("real"), &redirected_root).expect("create mutable ancestor symlink");

        let redirected_command = redirected_root.join("bin/targo-trust");
        let error = AuthenticatedProtectedSubcommand::capture(redirected_command)
            .err()
            .expect("an ancestor-symlink toolchain spelling must be rejected");
        assert!(
            error.contains("traverses a symlink or non-canonical path"),
            "{error}"
        );

        fs::remove_dir_all(root).expect("remove protected-command symlink fixture");
    }

    #[cfg(unix)]
    #[test]
    fn protected_subcommand_guard_rejects_ancestor_redirect_restore_after_raced_child_runs() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let _lock = PROTECTED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let temp = std::env::temp_dir()
            .canonicalize()
            .unwrap_or_else(|_| std::env::temp_dir());
        let root = temp.join(format!(
            "targo-protected-ancestor-race-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let selected_root = root.join("selected");
        let selected_bin = selected_root.join("bin");
        let attacker_root = root.join("attacker");
        let attacker_bin = attacker_root.join("bin");
        fs::create_dir_all(&selected_bin).expect("create selected toolchain directory");
        fs::create_dir_all(&attacker_bin).expect("create attacker toolchain directory");
        let command = selected_bin.join("targo-trust");
        fs::write(&command, b"#!/bin/sh\nexit 0\n").expect("write selected command");
        fs::set_permissions(&command, fs::Permissions::from_mode(0o755))
            .expect("make selected command executable");
        let hostile_command = attacker_bin.join("targo-trust");
        fs::write(&hostile_command, b"#!/bin/sh\nexit 23\n").expect("write hostile command");
        fs::set_permissions(&hostile_command, fs::Permissions::from_mode(0o755))
            .expect("make hostile command executable");
        let saved_root = root.join("selected-saved");

        let authenticated = AuthenticatedProtectedSubcommand::capture(command.clone())
            .expect("authenticate protected command and ancestor chain");
        let mut hostile_child_ran = false;
        let result = authenticated.run_guarded(|| {
            fs::rename(&selected_root, &saved_root).expect("save selected toolchain root");
            symlink(&attacker_root, &selected_root).expect("redirect selected toolchain root");
            let status = Command::new(&command)
                .status()
                .expect("run protected command through redirected pathname");
            hostile_child_ran = status.code() == Some(23);
            fs::remove_file(&selected_root).expect("remove attacker redirect");
            fs::rename(&saved_root, &selected_root).expect("restore exact selected toolchain root");
        });

        assert!(
            hostile_child_ran,
            "fixture did not execute the redirected command"
        );
        assert!(
            result.is_err(),
            "an ancestor redirect-and-restore escaped protected subcommand authentication"
        );
        drop(authenticated);
        fs::remove_dir_all(root).expect("remove protected-command ancestor-race fixture");
    }

    #[cfg(unix)]
    #[test]
    fn protected_subcommand_guard_admits_executable_timestamp_churn_but_rejects_content_change() {
        // Regression: macOS writes the `com.apple.provenance` extended
        // attribute the first time the guard *executes* a protected Mach-O
        // binary, bumping the executable's `ctime` between the pre-launch
        // capture and the post-run revalidation. The cross-time comparison
        // included the full stat snapshot (timestamps and all), so the guard
        // failed the run closed against its own execution side effect: on the
        // first run after every rebuild, `targo trust check` exited 2 with an
        // empty stdout even though the child had produced a complete report.
        // The executable's cross-time identity must ignore OS-mutated
        // timestamps (its device+inode is anchored by the retained handle)
        // while still rejecting a genuine content/size change.
        use std::os::unix::fs::PermissionsExt as _;

        let _lock = PROTECTED_FIXTURE_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let temp = std::env::temp_dir()
            .canonicalize()
            .unwrap_or_else(|_| std::env::temp_dir());
        let root = temp.join(format!(
            "targo-protected-timestamp-churn-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        let bin = root.join("bin");
        fs::create_dir_all(&bin).expect("create toolchain directory");
        let command = bin.join("targo-trust");
        fs::write(&command, b"#!/bin/sh\nexit 0\n").expect("write selected command");
        fs::set_permissions(&command, fs::Permissions::from_mode(0o755))
            .expect("make selected command executable");

        let authenticated = AuthenticatedProtectedSubcommand::capture(command.clone())
            .expect("authenticate protected command and ancestor chain");

        // A timestamp-only change to the executable — exactly what the OS
        // inflicts by writing the provenance xattr on execution — must NOT
        // trip the guard.
        let holds = authenticated.run_guarded(|| {
            let earlier =
                std::time::SystemTime::UNIX_EPOCH + std::time::Duration::from_secs(1_000_000);
            fs::File::options()
                .write(true)
                .open(&command)
                .expect("open protected command to bump its timestamp")
                .set_modified(earlier)
                .expect("bump protected command mtime (and ctime)");
        });
        assert!(
            holds.is_ok(),
            "an executable timestamp-only change (provenance-xattr churn) must not trip the guard: {:?}",
            holds.err()
        );

        // A genuine content/size change to the executable must STILL fail the
        // guarded run closed.
        let rejects = authenticated.run_guarded(|| {
            fs::write(&command, b"#!/bin/sh\nexit 0\n# tampered: strictly longer body\n")
                .expect("rewrite protected command with different content");
        });
        assert!(
            rejects.is_err(),
            "a genuine content change to the executable must still fail the guarded run closed"
        );

        drop(authenticated);
        fs::remove_dir_all(root).expect("remove protected-command timestamp-churn fixture");
    }

    #[cfg(unix)]
    #[test]
    fn guarded_subcommand_status_preserves_exit_and_signal_identity() {
        use std::os::unix::process::ExitStatusExt as _;

        let exited = Command::new("sh")
            .args(["-c", "exit 42"])
            .status()
            .expect("run exit-status fixture");
        assert_eq!(subcommand_exit_status_code(&exited), 42);

        let signaled = Command::new("sh")
            .args(["-c", "kill -TERM $$"])
            .status()
            .expect("run signal-status fixture");
        assert_eq!(signaled.signal(), Some(15));
        assert_eq!(subcommand_exit_status_code(&signaled), 128 + 15);
    }

    #[test]
    fn trust_dev_gate_subcommands_bypass_the_protected_guard_but_proof_commands_do_not() {
        // The external command's argv repeats the subcommand token at index 0.
        let argv = |tokens: &[&str]| -> Vec<OsString> {
            tokens.iter().map(OsString::from).collect()
        };
        // A local `fn` (not a closure) so the returned `&OsStr` borrows tie to
        // the input slice's lifetime.
        fn as_os(v: &[OsString]) -> Vec<&OsStr> {
            v.iter().map(OsString::as_os_str).collect()
        }

        // `targo trust domination …` is a dev/CI gate: it builds (churning the
        // in-tree toolchain ancestors) and dispatches its proof work through
        // separately-guarded nested checks, so the outer wrapper is unguarded.
        let domination = argv(&["trust", "domination", "trust-added", "native-contracts-pipeline-v2"]);
        assert!(trust_invocation_is_dev_gate("trust", &as_os(&domination)));

        // `doctor` is a pure diagnostic (builds an environment report, makes no
        // proof claim), so it is likewise unguarded.
        let doctor = argv(&["trust", "doctor", "--format", "json"]);
        assert!(trust_invocation_is_dev_gate("trust", &as_os(&doctor)));

        // A leading flag before the sub-subcommand must not hide it.
        let flagged = argv(&["trust", "--frozen", "domination", "trust-added"]);
        assert!(trust_invocation_is_dev_gate("trust", &as_os(&flagged)));

        // Proof-producing commands STAY guarded.
        for proof in [["trust", "check"], ["trust", "build"], ["trust", "test"], ["trust", "report"]] {
            let v = argv(&proof);
            assert!(
                !trust_invocation_is_dev_gate("trust", &as_os(&v)),
                "{proof:?} is proof-producing and must remain guarded"
            );
        }

        // Only the `trust` front door has dev-gate subcommands.
        let fmt = argv(&["fmt", "domination"]);
        assert!(!trust_invocation_is_dev_gate("fmt", &as_os(&fmt)));
    }

    #[test]
    fn protected_guard_failure_is_not_reported_as_a_compiler_error() {
        // Regression: a post-run guard trip DISCARDED the child's real
        // `ExitStatus` and returned 101. `targo trust check` therefore exited
        // 101 — cargo's "could not compile" — even though the child had
        // already written a complete sealed report to stdout whose own gate
        // object recorded `exit_code: 1` with complete coverage. Any churn in
        // a recorded ancestor directory (a concurrent build or test writing
        // under `build/`) tripped it, so an ordinary verification-gate
        // failure was indistinguishable from a compiler crash.
        //
        // A guard trip is a toolchain-AUTHORITY failure: exit 2, the code this
        // project's own pipeline uses for every setup/evidence failure.
        let guard_failure: Result<CargoResult<ExitStatus>, String> =
            Err("protected Trust subcommand `x` changed while it was running".to_string());
        let error = finish_guarded_protected_subcommand(guard_failure)
            .expect_err("a guard failure must fail closed");
        assert_eq!(
            error.exit_code, PROTECTED_SUBCOMMAND_AUTHORITY_EXIT,
            "a guard failure is a setup/authority failure, not a compiler error"
        );
        assert_ne!(error.exit_code, 101, "101 is reserved for `could not compile`");

        // When the guard HOLDS, the child's own status governs unchanged —
        // in particular an ordinary verification-gate failure stays exit 1.
        let gate_failure = Command::new("sh")
            .args(["-c", "exit 1"])
            .status()
            .expect("run gate-failure fixture");
        let error = finish_guarded_protected_subcommand(Ok(Ok(gate_failure)))
            .expect_err("a nonzero child status must fail closed");
        assert_eq!(error.exit_code, 1, "an ordinary verification-gate failure stays exit 1");

        let success = Command::new("sh")
            .args(["-c", "exit 0"])
            .status()
            .expect("run success fixture");
        assert!(
            finish_guarded_protected_subcommand(Ok(Ok(success))).is_ok(),
            "a successful guarded run stays successful"
        );
    }
}

/// Initialize libgit2.
#[tracing::instrument(skip_all)]
fn init_git(gctx: &GlobalContext) {
    // Disabling the owner validation in git can, in theory, lead to code execution
    // vulnerabilities. However, libgit2 does not launch executables, which is the foundation of
    // the original security issue. Meanwhile, issues with refusing to load git repos in
    // `CARGO_HOME` for example will likely be very frustrating for users. So, we disable the
    // validation.
    //
    // For further discussion of Cargo's current interactions with git, see
    //
    //   https://github.com/rust-lang/rfcs/pull/3279
    //
    // and in particular the subsection on "Git support".
    //
    // Note that we only disable this when Cargo is run as a binary. If Cargo is used as a library,
    // this code won't be invoked. Instead, developers will need to explicitly disable the
    // validation in their code. This is inconvenient, but won't accidentally open consuming
    // applications up to security issues if they use git2 to open repositories elsewhere in their
    // code.
    unsafe {
        git2::opts::set_verify_owner_validation(false)
            .expect("set_verify_owner_validation should never fail");
    }

    init_git_transports(gctx);
}

/// Configure libgit2 to use libcurl if necessary.
///
/// If the user has a non-default network configuration, then libgit2 will be
/// configured to use libcurl instead of the built-in networking support so
/// that those configuration settings can be used.
#[tracing::instrument(skip_all)]
fn init_git_transports(gctx: &GlobalContext) {
    match needs_custom_http_transport(gctx) {
        Ok(true) => {}
        _ => return,
    }

    let handle = match http_handle(gctx) {
        Ok(handle) => handle,
        Err(..) => return,
    };

    // The unsafety of the registration function derives from two aspects:
    //
    // 1. This call must be synchronized with all other registration calls as
    //    well as construction of new transports.
    // 2. The argument is leaked.
    //
    // We're clear on point (1) because this is only called at the start of this
    // binary (we know what the state of the world looks like) and we're mostly
    // clear on point (2) because we'd only free it after everything is done
    // anyway
    unsafe {
        git2_curl::register(handle);
    }
}
