use crate::util::data_structures::{HashMap, HashSet};
use anyhow::{Context as _, anyhow};
use cargo_util_terminal::report::Level;
use clap::builder::UnknownArgumentValueParser;
use itertools::Itertools;
use std::ffi::OsStr;
use std::ffi::OsString;
use std::fmt::Write;
use targo::context::TermConfig;
use targo::workspace::{CliUnstable, features};
use targo::{CargoResult, drop_print, drop_println};

use super::commands;
use super::list_commands;
use super::third_party_subcommands;
use super::user_defined_aliases;
use crate::command_prelude::*;
use crate::util::is_rustup;
use cargo_util_terminal::ColorChoice;
use targo::util::style;

const UNBOUND_TRUST_REPO_COMMIT: &str = "unbound";

#[tracing::instrument(skip_all)]
pub fn main(gctx: &mut GlobalContext) -> CliResult {
    run(gctx, std::env::args_os().collect(), RunPurpose::Execute)
}

pub(super) fn native_capability(gctx: &mut GlobalContext, args: &[OsString]) -> CliResult {
    let mut argv = vec![OsString::from("targo")];
    argv.extend_from_slice(args);
    run(gctx, argv, RunPurpose::NativeCapability)
}

/// Trust: the actual original Full owner supplies this library context. No
/// native startup, scheduler, environment import or process is created here.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(super) fn original_full(
    gctx: &mut GlobalContext,
    args: &[OsString],
    owner: std::sync::Arc<targo::context::bootstrap_full::BootstrapFull>,
) -> CliResult {
    owner.check_current()?;
    if !owner.owns_context(gctx) {
        return Err(anyhow!("Full parser has a different original context").into());
    }
    let mut argv = vec![owner.original().control_targo()?.into_os_string()];
    argv.extend_from_slice(args);
    let result = run(gctx, argv, RunPurpose::OriginalFull(owner.clone()));
    owner.check_current()?;
    result
}

enum RunPurpose {
    Execute,
    NativeCapability,
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    OriginalFull(std::sync::Arc<targo::context::bootstrap_full::BootstrapFull>),
}
impl RunPurpose {
    fn is_original_full(&self) -> bool {
        match self {
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            Self::OriginalFull(_) => true,
            _ => false,
        }
    }
    fn reload_directory(
        &self,
        gctx: &mut GlobalContext,
        directory: &std::path::Path,
    ) -> CargoResult<()> {
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        if let Self::OriginalFull(owner) = self {
            return owner.reload_context_directory(gctx, directory);
        }
        std::env::set_current_dir(directory).context("could not change to requested directory")?;
        gctx.reload_cwd()
    }
    fn configure_policy(
        &self,
        gctx: &GlobalContext,
        command: &str,
        manifest: bool,
        explicit_unverified: bool,
    ) -> CargoResult<()> {
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        if let Self::OriginalFull(owner) = self {
            owner.check_current()?;
            anyhow::ensure!(
                owner.owns_context(gctx),
                "Full policy has a different original context"
            );
            // The actual original entry already initialized its disclosed
            // unverified policy. Parsing another command cannot renew the
            // broker, mutate global flags, or select a different proof lane.
            anyhow::ensure!(
                targo::trust_no_verify_fast() && !targo::trust_verified_targo(),
                "Full library commands require the original entry's existing unverified policy"
            );
            let authorization = super::authorize_trust_execution(
                true,
                command,
                manifest,
                explicit_unverified,
                false,
                gctx.get_env_os("TRUST_TARGO_VERIFY") == Some(OsStr::new("1")),
                gctx.get_env_os("TRUST_BOOTSTRAP_NO_VERIFY").is_some()
                    || gctx
                        .get_env_os("TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY")
                        .is_some(),
            )?;
            anyhow::ensure!(
                matches!(
                    authorization,
                    super::TrustExecutionAuthorization::NotApplicable
                        | super::TrustExecutionAuthorization::ExplicitUnverified
                ),
                "Full command cannot change the original proof lane"
            );
            return Ok(());
        }
        let _ = gctx;
        super::configure_trust_execution_policy(command, manifest, explicit_unverified)
    }
}

fn run(gctx: &mut GlobalContext, argv: Vec<OsString>, purpose: RunPurpose) -> CliResult {
    // CAUTION: Be careful with using `config` until it is configured below.
    // In general, try to avoid loading config values unless necessary (like
    // the [alias] table).

    let native_shape =
        super::resource_capabilities::invocation_supported(argv.get(1..).unwrap_or_default());
    // Trust: a library call's actual argv is independent of the Root process
    // prelude. Capture consent before this canonical parser consumes it.
    let original_tail_unverified = argv_has_unverified_before_delimiter(&argv);
    let mut command = cli(gctx);
    let args = command.try_get_matches_from_mut(argv)?;
    if args.flag("resource-worker-v2") && !native_shape {
        return Err(anyhow::anyhow!(
            "native worker invocation is outside the supported command profile"
        )
        .into());
    }
    if purpose.is_original_full() {
        require_no_native_startup(&args)?;
    } else {
        targo::set_resource_worker_v2(args.flag("resource-worker-v2"))?;
        targo::set_resource_worker_v3(
            args.flag("resource-worker-v3"),
            args.flag("resource-subgroups-v3"),
        )?;
    }
    // Trust: lane consent is an authorization input, so capture its origin
    // before config-backed alias expansion reparses any arguments — after
    // expansion, a flag from `[alias]` is indistinguishable from one the human
    // typed. Clap preserves the
    // flag for built-ins and direct manifest commands, but an unexpanded
    // external/alias tail is opaque. Consult the process argv only for that
    // non-manifest case, stopping at `--`; direct manifest program argv after
    // the script path must never be reinterpreted as consent.
    let original_is_manifest_command = args
        .subcommand_name()
        .is_some_and(commands::run::is_manifest_command);
    let original_explicit_unverified =
        args.flag("unverified") || (!original_is_manifest_command && original_tail_unverified);
    // Trust: collect only parser-owned options, before aliases replace a frame.
    // Opaque program/manifest/external arguments grant no frontend options.
    let append_args = AppendArgs::from_matches(&command, &args);

    // Update the process-level notion of cwd
    if let Some(new_cwd) = args.get_one::<std::path::PathBuf>("directory") {
        // This is a temporary hack.
        // This cannot access `GlobalContext`, so this is a bit messy.
        // The error message is not as helpful as the standard one.
        let nightly_features_allowed =
            features::nightly_features_allowed_on_channel(&features::channel());
        if !nightly_features_allowed
            || (nightly_features_allowed
                && !append_args
                    .unstable_flags
                    .iter()
                    .any(|value| value == "unstable-options"))
        {
            return Err(anyhow::format_err!(
                "the `-C` flag is unstable, \
                 pass `-Z unstable-options` on the nightly channel to enable it"
            )
            .into());
        }
        purpose.reload_directory(gctx, new_cwd)?;
    }

    let (expanded_args, global_args) = expand_aliases(gctx, args, append_args, vec![])?;
    if purpose.is_original_full() {
        require_no_native_startup(&expanded_args)?;
    }

    // Trust: the pre-expansion capture above is what makes this detectable —
    // configuration is not a party that can consent to dropping verification.
    if targo::is_targo_invocation()
        && expanded_args.flag("unverified")
        && !original_explicit_unverified
    {
        return Err(anyhow!(
            "a Targo alias attempted to inject `--unverified`; configuration cannot grant verification bypass authority, so spell `--unverified` on the original Targo command line"
        )
        .into());
    }

    let is_verbose = expanded_args.verbose() > 0;

    if matches!(purpose, RunPurpose::NativeCapability) || targo::resource_worker_v2() {
        if expanded_args.flag("version")
            || expanded_args.flag("list")
            || expanded_args.get_one::<String>("explain").is_some()
            || global_args
                .append_args
                .unstable_flags
                .first()
                .is_some_and(|flag| flag == "help")
        {
            return Err(anyhow::anyhow!(
                "native worker discovery/dispatch does not accept early informational modes"
            )
            .into());
        }
    }

    if global_args
        .append_args
        .unstable_flags
        .first()
        .map(String::as_str)
        == Some("help")
    {
        // Don't let config errors get in the way of parsing arguments
        let _ = configure_gctx(gctx, &expanded_args, None, global_args, None);
        print_zhelp(gctx);
    } else if expanded_args.flag("version") {
        // Don't let config errors get in the way of parsing arguments
        let _ = configure_gctx(gctx, &expanded_args, None, global_args, None);
        let version = get_version_string(is_verbose);
        drop_print!(gctx, "{}", version);
    } else if let Some(code) = expanded_args.get_one::<String>("explain") {
        // Don't let config errors get in the way of parsing arguments
        let _ = configure_gctx(gctx, &expanded_args, None, global_args, None);
        let mut process = gctx.load_global_rustc(None)?.process();
        process.arg("--explain").arg(code).exec()?;
    } else if expanded_args.flag("list") {
        // Don't let config errors get in the way of parsing arguments
        let _ = configure_gctx(gctx, &expanded_args, None, global_args, None);
        print_list(gctx, is_verbose);
    } else {
        let (cmd, subcommand_args) = match expanded_args.subcommand() {
            Some((cmd, args)) => (cmd, args),
            _ => {
                // No subcommand provided.
                if purpose.is_original_full() {
                    let mut command = cli(gctx);
                    drop_print!(gctx, "{}", command.render_help());
                } else {
                    cli(gctx).print_help()?;
                }
                return Ok(());
            }
        };
        let exec = Exec::infer(cmd)?;
        if purpose.is_original_full() {
            if !matches!(&exec, Exec::Builtin(_))
                || !matches!(
                    cmd,
                    "build" | "check" | "rustc" | "rustdoc" | "doc" | "test" | "metadata" | "fetch"
                )
            {
                return Err(anyhow!(
                    "Full library command has no supported original native execution role"
                )
                .into());
            }
        }
        // Trust: a branded Targo compile, including the implicit `-Zscript`
        // manifest command, must select an authenticated verified lane or an
        // explicit unverified lane before Cargo configuration can create any
        // build units — once a Unit exists its rustflags are already fixed.
        // Plain Cargo retains upstream-compatible semantics.
        purpose.configure_policy(
            gctx,
            cmd,
            exec.is_manifest_command(),
            original_explicit_unverified,
        )?;
        // Original endpoint custody selects no lane and cannot authenticate a
        // command. The one existing policy initializer above owns the verified
        // runtime-library closure; bind its result before configuration/exec.
        super::validate_retained_test_dispatch(
            gctx.has_retained_test(),
            targo::is_targo_invocation() && targo::trust_verified_targo(),
            cmd,
            cmd == "test"
                && !exec.is_manifest_command()
                && subcommand_args.flag("no-run")
                && subcommand_args.flag("__retained-test-session"),
            original_explicit_unverified,
        )?;
        if matches!(purpose, RunPurpose::Execute) {
            targo::initialize_resource_worker_v3(gctx, cmd)?;
        }
        super::maybe_warn_trust_compiler();
        configure_gctx(
            gctx,
            &expanded_args,
            Some(subcommand_args),
            global_args,
            Some(&exec),
        )?;
        if matches!(purpose, RunPurpose::NativeCapability) {
            super::resource_capabilities::configured(gctx, || {
                if cmd == "test" && !subcommand_args.flag("no-run") {
                    match commands::test::native_budget_check(gctx, subcommand_args)? {
                        commands::test::NativeBudgetCheck::Allowed => {}
                        commands::test::NativeBudgetCheck::ExistingBoundary => {
                            anyhow::bail!(
                                "test arguments require their existing execution boundary"
                            )
                        }
                    }
                }
                Ok(())
            })?;
            return Ok(());
        }
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        let _paired_compiler_inputs = if purpose.is_original_full() {
            // Full already holds and bookends its original compiler/context.
            // A library command must not rediscover a second ambient pair.
            None
        } else if targo::resource_worker_v2() {
            Some(super::resource_capabilities::require_paired_compiler(gctx)?)
        } else if matches!(cmd, "build" | "check" | "test") {
            super::resource_capabilities::optional_paired_compiler(gctx)?
        } else {
            None
        };
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        if cmd == "test"
            && !subcommand_args.flag("no-run")
            && (purpose.is_original_full() || _paired_compiler_inputs.is_some())
        {
            // Older admission clients may not understand a fatal discovery
            // field. Actual selected execution enforces the same restriction.
            let _ = commands::test::native_budget_check(gctx, subcommand_args)?;
        }
        #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
        if targo::resource_worker_v2() {
            return Err(
                anyhow::anyhow!("native compiler pairing is unsupported on this host").into(),
            );
        }
        super::init_git();

        exec.exec(gctx, subcommand_args)?;
    }
    Ok(())
}

// Trust: marker rejection is a restriction. Only the typed actual owner above
// may select Full dispatch; these arguments cannot issue another native Root.
fn require_no_native_startup(args: &ArgMatches) -> CargoResult<()> {
    anyhow::ensure!(
        !args.flag("resource-worker-v2")
            && !args.flag("resource-worker-v3")
            && !args.flag("resource-subgroups-v3"),
        "Full library commands and aliases cannot create a second native startup"
    );
    Ok(())
}

/// Trust: `--` ends Targo's own arguments; anything after it belongs to the
/// program being run and must never be read as consent.
fn argv_has_unverified_before_delimiter(argv: &[OsString]) -> bool {
    argv.iter()
        .skip(1)
        .take_while(|argument| argument.as_os_str() != OsStr::new("--"))
        .any(|argument| argument.as_os_str() == OsStr::new("--unverified"))
}

fn print_zhelp(gctx: &GlobalContext) {
    let header = style::HEADER;
    let literal = style::LITERAL;
    let placeholder = style::PLACEHOLDER;
    // Trust: keep the authenticated Cargo alias's original help and links.
    let is_targo = targo::is_targo_invocation();
    let title = if is_targo {
        "Available Trust unstable flags:"
    } else {
        "Available unstable (nightly-only) flags:"
    };

    let options = CliUnstable::help();
    let max_length = options
        .iter()
        .filter(|(_, help)| help.is_some())
        .map(|(option_name, _)| option_name.len())
        .max()
        .unwrap_or(0);
    let z_flags = options
        .iter()
        .filter(|(_, help)| help.is_some())
        .map(|(opt, help)| {
            let opt = opt.replace("_", "-");
            let help = help.unwrap();
            format!("    {literal}-Z {opt:<max_length$}{literal:#}  {help}")
        })
        .join("\n");
    drop_println!(
        gctx,
        "\
	{header}{title}{header:#}

{z_flags}

Run with `{literal}{} -Z{literal:#} {placeholder}[FLAG] [COMMAND]{placeholder:#}`",
        super::frontend_binary_name(),
    );
    if !gctx.nightly_features_allowed {
        drop_println!(
            gctx,
            "\nUnstable flags are only available on {}, but this is the `{}` channel.\n\
                 {}",
            features::unstable_channels(),
            features::channel(),
            features::see_channels()
        );
    }
    drop_println!(
        gctx,
        "\n{}",
        if is_targo {
            "See the Trust Cargo unstable-features documentation shipped with this toolchain \
             for more information about these flags."
        } else {
            "See https://doc.rust-lang.org/nightly/cargo/reference/unstable.html \
             for more information about these flags."
        }
    );
}

/// A one-line description for every externally-dispatched subcommand `--list`
/// prints.
///
/// A const rather than a local so `every_protected_lane_is_described` can read
/// it. It was a `HashMap` literal inside `print_list`, unreachable from any
/// test, and three of the five protected lanes -- `trust`, `tippy`, `miri` --
/// had no entry and printed blank. `trust` is the flagship lane this binary's
/// own error paths tell users to type. The mapping each name resolves to is
/// `main.rs::protected_trust_subcommand_binary`.
const KNOWN_EXTERNAL_COMMAND_DESCRIPTIONS: &[(&str, &str)] = &[
    (
        "trust",
        "Trust's own verification lane: gates, proofs, and release checks (targo-trust).",
    ),
    (
        "tippy",
        "Lints a package to catch common mistakes — this toolchain's clippy (targo-tippy).",
    ),
    (
        "clippy",
        "Alias for `tippy` on this toolchain; both run targo-tippy.",
    ),
    (
        "fmt",
        "Formats all bin and lib files of the current crate using targo-fmt.",
    ),
    (
        "miri",
        "Runs a crate's tests under the Miri interpreter (targo-miri).",
    ),
];

fn print_list(gctx: &GlobalContext, is_verbose: bool) {
    // Maps from commonly known external commands (not builtin to cargo)
    // to their description, for the help page. Reserved for external
    // subcommands that are core within the rust ecosystem (esp ones that
    // might become internal in the future).
    // Trust: every PROTECTED_TRUST_SUBCOMMAND is described here. Three of the
    // five (`trust`, `tippy`, `miri`) printed with a blank description until
    // 2026-09-01 — including `trust`, which is the flagship lane this binary's
    // own error paths tell users to type. And `fmt` claimed to run `rustfmt`,
    // a binary this toolchain's installer deletes; it runs `targo-fmt`.
    // The mapping each name resolves to is
    // `main.rs::protected_trust_subcommand_binary`.
    let mut known_external_command_descriptions: HashMap<&str, &str> =
        KNOWN_EXTERNAL_COMMAND_DESCRIPTIONS
            .iter()
            .copied()
            .collect();
    // Trust: the compatibility frontend retains the upstream tool description.
    if !targo::is_targo_invocation() {
        known_external_command_descriptions.insert(
            "fmt",
            "Formats all bin and lib files of the current crate using rustfmt.",
        );
    }
    drop_println!(
        gctx,
        color_print::cstr!("<bright-green,bold>Installed Commands:</>")
    );
    for (name, command) in list_commands(gctx) {
        let known_external_desc = known_external_command_descriptions.get(name.as_str());
        let literal = style::LITERAL;
        match command {
            CommandInfo::BuiltIn { about } => {
                assert!(
                    known_external_desc.is_none(),
                    "known_external_commands shouldn't contain builtin `{name}`",
                );
                let summary = about.unwrap_or_default();
                let summary = summary.lines().next().unwrap_or(&summary); // display only the first line
                drop_println!(gctx, "    {literal}{name:<20}{literal:#} {summary}");
            }
            CommandInfo::External { path } => {
                if let Some(desc) = known_external_desc {
                    drop_println!(gctx, "    {literal}{name:<20}{literal:#} {desc}");
                } else if is_verbose {
                    drop_println!(
                        gctx,
                        "    {literal}{name:<20}{literal:#} {}",
                        path.display()
                    );
                } else {
                    drop_println!(gctx, "    {literal}{name}{literal:#}");
                }
            }
            CommandInfo::Alias { target } => {
                drop_println!(
                    gctx,
                    "    {literal}{name:<20}{literal:#} alias: {}",
                    target.iter().join(" ")
                );
            }
        }
    }
}

pub fn get_version_string(is_verbose: bool) -> String {
    let version = targo::version();
    // Trust: brand by the INVOKED name, exactly as `rustc_driver_impl` does for
    // `trustc`. `version` here is the Rust COMPAT line (CFG_RELEASE — "which Rust is
    // this compatible with"), NOT Trust's own version, and it must keep leading:
    // dispatched as `cargo`, this banner is parsed by the same version-sniffing build
    // scripts that assert the `cargo <semver>` shape, and Trust's `0.1.0` there would
    // read as a Cargo predating 1.0.
    //
    // But under `targo` there is no such obligation — nothing in the ecosystem expects
    // a tool called `targo`, so wearing the compat number as its own name buys nothing
    // and hides what the binary actually is. The parenthetical is where it says so,
    // and it is emitted ONLY for the non-`cargo` frontend, so the compat surface is
    // untouched.
    let brand = match (cargo_binary_name(), option_env!("CFG_TRUST_VERSION")) {
        ("cargo", _) => String::new(),
        (name, Some(trust_version)) => format!(" ({name} {trust_version})"),
        (name, None) => format!(" ({name})"),
    };
    let mut version_string = format!("{} {}{}\n", cargo_binary_name(), version, brand);
    if is_verbose {
        // Trust: both frontends write/read this internal cache policy. This
        // describes compatibility only, independently of content mode or proof.
        version_string.push_str(&format!(
            "encoded-dep-info-version: {}\n",
            targo::encoded_dep_info_version()
        ));
        // Trust: software capability only. Consumers must select content mode;
        // this reports neither a proof grade nor hermetic undeclared inputs.
        if cargo_binary_name() != "cargo" {
            version_string.push_str("freshness: rust-and-build-input-content-v1\n");
            // Trust: native content reuse refuses incomplete filename inventories.
            version_string.push_str("freshness: compiler-filename-inventory-v1\n");
            // Trust: cached build-script directives are checked independently
            // of input freshness. This line carries software metadata only.
            version_string.push_str("cache-integrity: build-script-control-output-v1\n");
            // Trust: this covers the compiled executable, separately from
            // control output; neither line inventories generated OUT_DIR data.
            version_string.push_str("cache-integrity: compiled-build-script-executable-v1\n");
            version_string.push_str("cache-integrity: build-script-generated-tree-v1\n");
            // Trust: exact original-stdout analysis identity, not log freshness.
            version_string.push_str("analysis-session: build-json-v1\n");
        }
        version_string.push_str(&format!("release: {}\n", version.version));
        // Trust: the product version, beside the compat `release:` above and never in
        // place of it — the two answer different questions and a consumer must not have
        // to infer either from the other. Absent binding reports as `unknown` rather
        // than being omitted, so a parser can tell "standalone build" from "old build".
        version_string.push_str(&format!(
            "trust: {}\n",
            option_env!("CFG_TRUST_VERSION").unwrap_or("unknown")
        ));
        if let Some(ref ci) = version.commit_info {
            version_string.push_str(&format!("commit-hash: {}\n", ci.commit_hash));
            version_string.push_str(&format!("commit-date: {}\n", ci.commit_date));
        }
        // Trust: `CFG_VER_HASH` is injected by the parent Trust bootstrap and
        // names the exact Trust source commit, which is distinct from
        // Cargo/Targo's own optional `commit-hash` above. A standalone Cargo
        // build receives no such binding and must say so instead of inferring
        // authority from an ambient checkout.
        writeln!(
            version_string,
            "trust-repo-commit-hash: {}",
            embedded_trust_repo_commit_hash(option_env!("CFG_VER_HASH"))
        )
        .unwrap();
        writeln!(version_string, "host: {}", env!("RUST_HOST_TARGET")).unwrap();
        add_libgit2(&mut version_string);
        add_curl(&mut version_string);
        add_ssl(&mut version_string);
        writeln!(version_string, "os: {}", os_info::get()).unwrap();
    }
    version_string
}

/// Trust: a malformed or absent binding reports as unbound rather than being
/// echoed. A version banner is read by tooling as provenance, so a
/// half-plausible value is worse than an honest "no binding".
fn embedded_trust_repo_commit_hash(value: Option<&str>) -> &str {
    value
        .filter(|value| {
            matches!(value.len(), 40 | 64)
                && value
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        })
        .unwrap_or(UNBOUND_TRUST_REPO_COMMIT)
}

fn cargo_binary_name() -> &'static str {
    super::frontend_binary_name()
}

fn add_libgit2(version_string: &mut String) {
    let git2_v = git2::Version::get();
    let lib_v = git2_v.libgit2_version();
    let vendored = if git2_v.vendored() {
        format!("vendored")
    } else {
        format!("system")
    };
    writeln!(
        version_string,
        "libgit2: {}.{}.{} (sys:{} {})",
        lib_v.0,
        lib_v.1,
        lib_v.2,
        git2_v.crate_version(),
        vendored
    )
    .unwrap();
}

fn add_curl(version_string: &mut String) {
    let curl_v = curl::Version::get();
    let vendored = if curl_v.vendored() {
        format!("vendored")
    } else {
        format!("system")
    };
    writeln!(
        version_string,
        "libcurl: {} (sys:{} {} ssl:{})",
        curl_v.version(),
        curl_sys::rust_crate_version(),
        vendored,
        curl_v.ssl_version().unwrap_or("none")
    )
    .unwrap();
}

fn add_ssl(version_string: &mut String) {
    #[cfg(feature = "openssl")]
    {
        writeln!(version_string, "ssl: {}", openssl::version::version()).unwrap();
    }
    #[cfg(not(feature = "openssl"))]
    {
        let _ = version_string; // Silence unused warning.
    }
}

/// Expands aliases iteratively to collect all the command line arguments.
///
/// Preserve scalar global options and each parser-local accumulating frame
/// before replacing an alias with its expansion.
#[tracing::instrument(skip_all)]
fn expand_aliases(
    gctx: &mut GlobalContext,
    mut args: ArgMatches,
    mut append_args: AppendArgs,
    mut already_expanded: Vec<String>,
) -> Result<(ArgMatches, GlobalArgs), CliError> {
    let mut global_args = GlobalArgs::default();
    let mut expanded_names: HashSet<String> = already_expanded.iter().cloned().collect();
    let mut alias_parser = None;
    loop {
        if let Some((cmd, sub_args)) = args.subcommand() {
            let exec = commands::builtin_exec(cmd);
            let aliased_cmd = super::aliased_command(gctx, cmd);

            match (exec, aliased_cmd) {
                (Some(_), Ok(Some(_))) => {
                    // User alias conflicts with a built-in subcommand
                    gctx.shell().warn(format!(
                    "user-defined alias `{}` is ignored, because it is shadowed by a built-in command",
                    cmd,
                ))?;
                }
                (Some(_), Ok(None) | Err(_)) => {
                    // Here we ignore errors from aliasing as we already favor built-in command,
                    // and alias doesn't involve in this context.

                    if let Some(values) = sub_args.get_many::<OsString>("") {
                        // Command is built-in and is not conflicting with alias, but contains ignored values.
                        return Err(anyhow::format_err!(
                            "\
trailing arguments after built-in command `{}` are unsupported: `{}`

To pass the arguments to the subcommand, remove `--`",
                            cmd,
                            values.map(|s| s.to_string_lossy()).join(" "),
                        )
                        .into());
                    }
                }
                (None, Ok(None)) => {}
                (None, Ok(Some(alias))) => {
                    // Check if a user-defined alias is shadowing an external subcommand
                    // (binary of the form `cargo-<subcommand>`)
                    // Currently this is only a warning, but after a transition period this will become
                    // a hard error.
                    if super::builtin_aliases_execs(cmd).is_none() {
                        if let Some(path) = super::find_external_subcommand(gctx, cmd) {
                            gctx.shell().print_report(
                            &[
                                Level::WARNING.secondary_title(format!(
                                    "user-defined alias `{}` is shadowing an external subcommand found at `{}`",
                                    cmd,
                                    path.display()
                                )).element(
                                    Level::NOTE.message(
                                        "this was previously accepted but will become a hard error in the future; \
                                        see <https://github.com/rust-lang/cargo/issues/10049>"
                                    )
                                )
                            ],
                            false,
                        )?;
                        }
                    }
                    if commands::run::is_manifest_command(cmd) {
                        if gctx.cli_unstable().script {
                            global_args.append_args = append_args;
                            return Ok((args, global_args));
                        } else {
                            gctx.shell().print_report(
                            &[
                                Level::WARNING.secondary_title(
                                    format!("user-defined alias `{cmd}` has the appearance of a manifest-command")
                                ).element(
                                    Level::NOTE.message(
                                        "this was previously accepted but will be phased out when `-Zscript` is stabilized; \
                                        see <https://github.com/rust-lang/cargo/issues/12207>"
                                    )
                                )
                            ],
                            false
                        )?;
                        }
                    }

                    let mut alias = alias
                        .into_iter()
                        .map(|s| OsString::from(s))
                        .collect::<Vec<_>>();
                    alias.extend(
                        sub_args
                            .get_many::<OsString>("")
                            .unwrap_or_default()
                            .cloned(),
                    );
                    // new_args strips out everything before the subcommand, so
                    // capture those global options now.
                    // Note that an alias to an external command will not receive
                    // these arguments. That may be confusing, but such is life.
                    let frame_globals = GlobalArgs::new(sub_args);
                    // Original directory handling has completed before expansion.
                    // Reuse only this dedicated schema; every parse owns fresh matches.
                    let alias_command =
                        alias_parser.get_or_insert_with(|| cli(gctx).no_binary_name(true));
                    let new_args = alias_command.try_get_matches_from_mut(alias)?;
                    let alias_append_args = AppendArgs::from_matches(alias_command, &new_args);

                    let Some(new_cmd) = new_args.subcommand_name() else {
                        return Err(anyhow!(
                        "subcommand is required, add a subcommand to the command alias `alias.{cmd}`"
                    )
                        .into());
                    };

                    already_expanded.push(cmd.to_string());
                    expanded_names.insert(cmd.to_string());
                    if expanded_names.contains(new_cmd) {
                        // Refuse corecursive / unresolvable aliases with their path.
                        return Err(anyhow!(
                            "alias {} has unresolvable recursive definition: {} -> {}",
                            already_expanded[0],
                            already_expanded.join(" -> "),
                            new_cmd,
                        )
                        .into());
                    }

                    // Retain only the accumulated values and current parsed frame.
                    // Terminal scalars stay in args for configure_gctx to add once.
                    append_args.extend(alias_append_args);
                    // Trust: aliases may add restrictions, but no intermediate
                    // frame can discard an already requested restriction.
                    global_args.locked |= frame_globals.locked;
                    global_args.offline |= frame_globals.offline;
                    global_args.frozen |= frame_globals.frozen;
                    // Trust: retain the same scalar composition as a single alias;
                    // the final parser's explicit color still wins in configure.
                    global_args.verbose += frame_globals.verbose;
                    global_args.quiet |= frame_globals.quiet;
                    global_args.color = frame_globals.color.or(global_args.color);
                    args = new_args;
                    // Drop previous matches before the next expansion. The one
                    // retained parser caches schema, not prior argument values.
                    continue;
                }
                (None, Err(e)) => return Err(e.into()),
            }
        };

        global_args.append_args = append_args;
        return Ok((args, global_args));
    }
}

#[tracing::instrument(skip_all)]
fn configure_gctx(
    gctx: &mut GlobalContext,
    args: &ArgMatches,
    subcommand_args: Option<&ArgMatches>,
    global_args: GlobalArgs,
    exec: Option<&Exec>,
) -> CliResult {
    let arg_target_dir = &subcommand_args.and_then(|a| a.value_of_path("target-dir", gctx));
    let mut verbose = global_args.verbose + args.verbose();
    // quiet is unusual because it is redefined in some subcommands in order
    // to provide custom help text.
    let mut quiet = args.flag("quiet")
        || subcommand_args.map(|a| a.flag("quiet")).unwrap_or_default()
        || global_args.quiet;
    if matches!(exec, Some(Exec::Manifest(_))) && !quiet {
        // Verbosity is shifted quieter for `Exec::Manifest` as it is can be used as if you ran
        // `cargo install` and we especially shouldn't pollute programmatic output.
        //
        // For now, interactive output has the same default output as `cargo run` but that is
        // subject to change.
        if let Some(lower) = verbose.checked_sub(1) {
            verbose = lower;
        } else if !gctx.shell().is_err_tty() {
            // Don't pollute potentially-scripted output
            quiet = true;
        }
    }
    let global_color = global_args.color; // Extract so it can take reference.
    let color = args
        .get_one::<String>("color")
        .map(String::as_str)
        .or_else(|| global_color.as_deref());
    let frozen = args.flag("frozen") || global_args.frozen;
    let locked = args.flag("locked") || global_args.locked;
    let offline = args.flag("offline") || global_args.offline;
    // Trust: every recognized parser/alias frame was already collected once.
    let AppendArgs {
        unstable_flags,
        config_args,
    } = global_args.append_args;
    gctx.configure(
        verbose,
        quiet,
        color,
        frozen,
        locked,
        offline,
        arg_target_dir,
        &unstable_flags,
        &config_args,
    )?;
    Ok(())
}

enum Exec {
    Builtin(commands::Exec),
    Manifest(String),
    External(String),
}

impl Exec {
    /// Precedence isn't the most obvious from this function because
    /// - Some is determined by `expand_aliases`
    /// - Some is enforced by `avoid_ambiguity_between_builtins_and_manifest_commands`
    ///
    /// In actuality, it is:
    /// 1. built-ins xor manifest-command
    /// 2. aliases
    /// 3. external subcommands
    fn infer(cmd: &str) -> CargoResult<Self> {
        if let Some(exec) = commands::builtin_exec(cmd) {
            Ok(Self::Builtin(exec))
        } else if commands::run::is_manifest_command(cmd) {
            Ok(Self::Manifest(cmd.to_owned()))
        } else {
            Ok(Self::External(cmd.to_owned()))
        }
    }

    fn is_manifest_command(&self) -> bool {
        matches!(self, Self::Manifest(_))
    }

    #[tracing::instrument(skip_all)]
    fn exec(self, gctx: &mut GlobalContext, subcommand_args: &ArgMatches) -> CliResult {
        match self {
            Self::Builtin(exec) => exec(gctx, subcommand_args),
            Self::Manifest(cmd) => {
                let ext_path = super::find_external_subcommand(gctx, &cmd);
                if !gctx.cli_unstable().script && ext_path.is_some() {
                    gctx.shell().print_report(
                        &[
                            Level::WARNING.secondary_title(
                                format!("external subcommand `{cmd}` has the appearance of a manifest-command")
                            ).element(
                                Level::NOTE.message(
                                    "this was previously accepted but will be phased out when `-Zscript` is stabilized; \
                                    see <https://github.com/rust-lang/cargo/issues/12207>"
                                )
                            )
                        ],
                        false
                    )?;

                    Self::External(cmd).exec(gctx, subcommand_args)
                } else {
                    let ext_args: Vec<OsString> = subcommand_args
                        .get_many::<OsString>("")
                        .unwrap_or_default()
                        .cloned()
                        .collect();
                    commands::run::exec_manifest_command(gctx, &cmd, &ext_args)
                }
            }
            Self::External(cmd) => {
                let mut ext_args = vec![OsStr::new(&cmd)];
                ext_args.extend(
                    subcommand_args
                        .get_many::<OsString>("")
                        .unwrap_or_default()
                        .map(OsString::as_os_str),
                );
                super::execute_external_subcommand(gctx, &cmd, &ext_args)
            }
        }
    }
}

/// Trust: Clap's global propagation selects one command level's complete value
/// list even for Append. These options instead belong to each parsed frame.
#[derive(Default, Debug, PartialEq, Eq)]
struct AppendArgs {
    unstable_flags: Vec<String>,
    config_args: Vec<String>,
}

impl AppendArgs {
    fn from_matches(mut command: &Command, mut args: &ArgMatches) -> Self {
        let mut result = Self::default();
        loop {
            result.unstable_flags.extend(
                args.get_many::<String>("unstable-features")
                    .unwrap_or_default()
                    .cloned(),
            );
            result.config_args.extend(
                args.get_many::<String>("config")
                    .unwrap_or_default()
                    .cloned(),
            );
            let Some((name, sub_args)) = args.subcommand() else {
                break;
            };
            // Unknown external commands and manifest/program tails remain
            // opaque. Positional help targets are not a command spine either.
            let Some(subcommand) = command.find_subcommand(name) else {
                break;
            };
            command = subcommand;
            args = sub_args;
        }
        result
    }

    fn extend(&mut self, mut other: Self) {
        self.unstable_flags.append(&mut other.unstable_flags);
        self.config_args.append(&mut other.config_args);
    }
}

// Trust: mirror inherited option availability on declared builder descendants,
// without giving Clap a global Append list to overwrite during propagation.
fn inherit_append_args(mut command: Command, append_args: &[Arg]) -> Command {
    for arg in append_args {
        if !command
            .get_arguments()
            .any(|existing| existing.get_id() == arg.get_id())
        {
            command = command.arg(arg.clone());
        }
    }
    command.mut_subcommands(|subcommand| inherit_append_args(subcommand, append_args))
}

#[derive(Default)]
struct GlobalArgs {
    verbose: u32,
    quiet: bool,
    color: Option<String>,
    frozen: bool,
    locked: bool,
    offline: bool,
    append_args: AppendArgs,
}

impl GlobalArgs {
    fn new(args: &ArgMatches) -> GlobalArgs {
        GlobalArgs {
            verbose: args.verbose(),
            quiet: args.flag("quiet"),
            color: args.get_one::<String>("color").cloned(),
            frozen: args.flag("frozen"),
            locked: args.flag("locked"),
            offline: args.flag("offline"),
            append_args: AppendArgs::default(),
        }
    }
}

#[tracing::instrument(skip_all)]
pub fn cli(gctx: &GlobalContext) -> Command {
    cli_for_frontend(gctx, targo::is_targo_invocation())
}

// Trust: parser surface DATA only. Actual dispatch/admission still authenticates
// the frontend and its original owner; this flag constructs no native startup.
fn cli_for_frontend(gctx: &GlobalContext, is_targo: bool) -> Command {
    // Don't let config errors get in the way of parsing arguments
    let term = gctx.get::<TermConfig>(["term"]).unwrap_or_default();
    let color = term
        .color
        .and_then(|c| c.parse().ok())
        .unwrap_or(ColorChoice::CargoAuto);
    let color = match color {
        ColorChoice::Always => clap::ColorChoice::Always,
        ColorChoice::Never => clap::ColorChoice::Never,
        ColorChoice::CargoAuto => clap::ColorChoice::Auto,
    };

    // Trust: the whole `cli()` builder is branded per invoked name — usage,
    // about line, help template, and the `--unverified` flag below only exist
    // for `targo`. `color_print::cstr!` needs literals, so the branded usage is
    // a match over pre-expanded arms rather than a format at runtime.
    let usage = match (is_targo, is_rustup()) {
        (true, true) => color_print::cstr!(
            "<bright-cyan,bold>targo</> <cyan>[+toolchain] [OPTIONS] [COMMAND]</>\n       <bright-cyan,bold>targo</> <cyan>[+toolchain] [OPTIONS]</> <bright-cyan,bold>-Zscript</> <cyan><<MANIFEST_RS>> [ARGS]...</>"
        ),
        (true, false) => color_print::cstr!(
            "<bright-cyan,bold>targo</> <cyan>[OPTIONS] [COMMAND]</>\n       <bright-cyan,bold>targo</> <cyan>[OPTIONS]</> <bright-cyan,bold>-Zscript</> <cyan><<MANIFEST_RS>> [ARGS]...</>"
        ),
        (false, true) => color_print::cstr!(
            "<bright-cyan,bold>cargo</> <cyan>[+toolchain] [OPTIONS] [COMMAND]</>\n       <bright-cyan,bold>cargo</> <cyan>[+toolchain] [OPTIONS]</> <bright-cyan,bold>-Zscript</> <cyan><<MANIFEST_RS>> [ARGS]...</>"
        ),
        (false, false) => color_print::cstr!(
            "<bright-cyan,bold>cargo</> <cyan>[OPTIONS] [COMMAND]</>\n       <bright-cyan,bold>cargo</> <cyan>[OPTIONS]</> <bright-cyan,bold>-Zscript</> <cyan><<MANIFEST_RS>> [ARGS]...</>"
        ),
    };

    let styles = {
        clap::builder::styling::Styles::styled()
            .header(style::HEADER)
            .usage(style::USAGE)
            .literal(style::LITERAL)
            .placeholder(style::PLACEHOLDER)
            .error(style::ERROR)
            .valid(style::VALID)
            .invalid(style::INVALID)
    };

    let command = Command::new(super::frontend_binary_name())
        .about(if is_targo {
            "Trust's Cargo-compatible package manager"
        } else {
            "Rust's package manager"
        })
        // Subcommands all count their args' display order independently (from 0),
        // which makes their args interspersed with global args. This puts global args last.
        //
        // We also want these to come before auto-generated `--help`
        .next_display_order(800)
        .allow_external_subcommands(true)
        .color(color)
        .styles(styles)
        // Provide a custom help subcommand for calling into man pages
        .disable_help_subcommand(true)
        .override_usage(usage)
        .help_template(color_print::cstr!(
            "\
{about}

<bright-green,bold>Usage:</> {usage}

<bright-green,bold>Options:</>
{options}

<bright-green,bold>Commands:</>
    <bright-cyan,bold>build</>, <bright-cyan,bold>b</>    Compile the current package
    <bright-cyan,bold>check</>, <bright-cyan,bold>c</>    Analyze the current package and report errors, but don't build object files
    <bright-cyan,bold>clean</>       Remove the target directory
    <bright-cyan,bold>doc</>, <bright-cyan,bold>d</>      Build this package's and its dependencies' documentation
    <bright-cyan,bold>new</>         Create a new cargo package
    <bright-cyan,bold>init</>        Create a new cargo package in an existing directory
    <bright-cyan,bold>add</>         Add dependencies to a manifest file
    <bright-cyan,bold>remove</>      Remove dependencies from a manifest file
    <bright-cyan,bold>run</>, <bright-cyan,bold>r</>      Run a binary or example of the local package
    <bright-cyan,bold>test</>, <bright-cyan,bold>t</>     Run the tests
    <bright-cyan,bold>bench</>       Run the benchmarks
    <bright-cyan,bold>update</>      Update dependencies listed in Cargo.lock
    <bright-cyan,bold>search</>      Search registry for crates
    <bright-cyan,bold>publish</>     Package and upload this package to the registry
    <bright-cyan,bold>install</>     Install a Rust binary
    <bright-cyan,bold>uninstall</>   Uninstall a Rust binary
    <cyan>...</>         See all commands with <bright-cyan,bold>--list</>

See '<bright-cyan,bold>{name} help</> <cyan><<command>></>' for more information on a specific command.\n",
        ))
        .arg(flag("version", "Print version info and exit").short('V'))
        .arg(flag("list", "List installed commands"))
        .arg(
            opt(
                "explain",
                "Provide a detailed explanation of a rustc error message",
            )
            .value_name("CODE"),
        )
        .arg(
            opt(
                "verbose",
                "Use verbose output (-vv very verbose/build.rs output)",
            )
            .short('v')
            .action(ArgAction::Count)
            .global(true),
        )
        .arg(flag("quiet", "Do not print cargo log messages").short('q').global(true))
        .arg(
            opt("color", "Coloring")
                .value_name("WHEN")
                .global(true)
                .value_parser(["auto", "always", "never"])
                .ignore_case(true),
        )
        .arg(
            Arg::new("directory")
                .help(if is_targo {
                    "Change to DIRECTORY before doing anything (Trust/nightly-only)"
                } else {
                    "Change to DIRECTORY before doing anything (nightly-only)"
                })
                .short('C')
                .value_name("DIRECTORY")
                .value_hint(clap::ValueHint::DirPath)
                .value_parser(clap::builder::ValueParser::path_buf()),
        )
        .arg(
            flag("locked", "Assert that `Cargo.lock` will remain unchanged")
                .help_heading(heading::MANIFEST_OPTIONS)
                .global(true),
        )
        .arg(
            flag("offline", "Run without accessing the network")
                .help_heading(heading::MANIFEST_OPTIONS)
                .global(true),
        )
        .arg(
            flag("frozen", "Equivalent to specifying both --locked and --offline")
                .help_heading(heading::MANIFEST_OPTIONS)
                .global(true),
        )
        // Better suggestion for the unsupported short config flag.
        .arg( Arg::new("unsupported-short-config-flag")
            .help("")
            .short('c')
            .value_parser(UnknownArgumentValueParser::suggest_arg("--config"))
            .action(ArgAction::SetTrue)
            .global(true)
            .hide(true))
        .arg(multi_opt("config", "KEY=VALUE|PATH", "Override a configuration value").add(clap_complete::engine::ArgValueCompleter::new(
                    clap_complete::engine::PathCompleter::any()
                        .filter(|path| path.is_file() && path.extension() == Some(OsStr::new("toml"))),
                )))
        // Better suggestion for the unsupported lowercase unstable feature flag.
        .arg( Arg::new("unsupported-lowercase-unstable-feature-flag")
            .help("")
            .short('z')
            .value_parser(UnknownArgumentValueParser::suggest_arg("-Z"))
            .action(ArgAction::SetTrue)
            .global(true)
            .hide(true))
        .arg(Arg::new("unstable-features")
            .help(format!(
                "{}, see '{} -Z help' for details",
                if is_targo {
                    "Unstable flags to Targo"
                } else {
                    "Unstable (nightly-only) flags to Cargo"
                },
                super::frontend_binary_name()
            ))
            .short('Z')
            .value_name("FLAG")
            .action(ArgAction::Append)
        .add(clap_complete::ArgValueCandidates::new(|| {
            let flags = CliUnstable::help();
            flags.into_iter().map(|flag| {
                clap_complete::CompletionCandidate::new(flag.0.replace("_", "-")).help(flag.1.map(|help| {
                    help.into()
                }))
            }).collect()
        })))
        .add(clap_complete::engine::SubcommandCandidates::new(move || {
            let mut candidates = get_toolchains_from_rustup()
                .into_iter()
                .map(|t| clap_complete::CompletionCandidate::new(t))
                .collect::<Vec<_>>();
            if let Ok(gctx) = new_gctx_for_completions() {
                candidates.extend(get_command_candidates(&gctx));
            }
            candidates
        }))
        .subcommands(commands::builtin());

    // Trust: the compat `cargo` name must not even accept `--unverified` — it
    // makes no verification claim to waive, and accepting it would make the two
    // frontends' argument surfaces indistinguishable to a script.
    let command = if is_targo {
        command.arg(flag("resource-worker-v2", "Native CPU worker protocol").hide(true).global(true))
            .arg(flag("resource-worker-v3", "Host-owned worker protocol").hide(true).global(true).requires("resource-subgroups-v3").conflicts_with("resource-worker-v2"))
            .arg(flag("resource-subgroups-v3", "Host-owned subgroup protocol").hide(true).global(true).requires("resource-worker-v3").conflicts_with("resource-worker-v2"))
            .arg(
            flag(
                "unverified",
                "Explicitly authorize a native build with Trust verification disabled (for -Zscript, place this before the script path)",
            )
            .long("unverified")
            .global(true),
        )
    } else {
        command
    };
    let append_args = command
        .get_arguments()
        .filter(|arg| matches!(arg.get_id().as_str(), "unstable-features" | "config"))
        .cloned()
        .collect::<Vec<_>>();
    command.mut_subcommands(|subcommand| inherit_append_args(subcommand, &append_args))
}

fn get_toolchains_from_rustup() -> Vec<String> {
    let Ok(output) = std::process::Command::new("rustup")
        .arg("toolchain")
        .arg("list")
        .arg("-q")
        .output()
    else {
        return vec![];
    };

    if !output.status.success() {
        return vec![];
    }

    let Ok(stdout) = String::from_utf8(output.stdout) else {
        return vec![];
    };

    stdout.lines().map(|line| format!("+{}", line)).collect()
}

fn get_command_candidates(gctx: &GlobalContext) -> Vec<clap_complete::CompletionCandidate> {
    let mut commands = user_defined_aliases(gctx);
    commands.extend(third_party_subcommands(gctx));
    commands
        .iter()
        .map(|(name, cmd_info)| {
            let help_text = match cmd_info {
                CommandInfo::Alias { target } => {
                    let cmd_str = target
                        .iter()
                        .map(String::as_str)
                        .collect::<Vec<_>>()
                        .join(" ");
                    format!("alias for {}", cmd_str)
                }
                CommandInfo::BuiltIn { .. } => {
                    unreachable!("BuiltIn command shouldn't appear in alias map")
                }
                CommandInfo::External { path } => {
                    format!("from {}", path.display())
                }
            };
            clap_complete::CompletionCandidate::new(name.clone()).help(Some(help_text.into()))
        })
        .collect()
}

#[test]
fn verify_cli() {
    let gctx = GlobalContext::default().unwrap();
    cli(&gctx).debug_assert();
}

#[test]
fn avoid_ambiguity_between_builtins_and_manifest_commands() {
    for cmd in commands::builtin() {
        let name = cmd.get_name();
        assert!(
            !commands::run::is_manifest_command(&name),
            "built-in command {name} is ambiguous with manifest-commands"
        )
    }
}

// Trust: the two tests below pin the version banner's provenance line — that a
// malformed binding degrades to `unbound`, and that the line appears exactly
// once and only in verbose output, since a duplicate would let a reader pick.
#[test]
fn trust_repo_commit_identity_is_exact_or_explicitly_unbound() {
    let commit = "0123456789abcdef0123456789abcdef01234567";
    assert_eq!(embedded_trust_repo_commit_hash(Some(commit)), commit);
    let sha256 = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
    assert_eq!(embedded_trust_repo_commit_hash(Some(sha256)), sha256);
    for invalid in [
        None,
        Some(""),
        Some("0123456789abcdef0123456789abcdef0123456"),
        Some("0123456789ABCDEF0123456789ABCDEF01234567"),
        Some("g123456789abcdef0123456789abcdef01234567"),
    ] {
        assert_eq!(
            embedded_trust_repo_commit_hash(invalid),
            UNBOUND_TRUST_REPO_COMMIT
        );
    }
}

#[test]
fn verbose_version_reports_the_exact_trust_repo_binding_only_once() {
    let expected = embedded_trust_repo_commit_hash(option_env!("CFG_VER_HASH"));
    let verbose = get_version_string(true);
    assert_eq!(
        verbose
            .lines()
            .filter_map(|line| line.strip_prefix("trust-repo-commit-hash: "))
            .collect::<Vec<_>>(),
        [expected]
    );
    assert!(!get_version_string(false).contains("trust-repo-commit-hash:"));
}

/// THE TWO NUMBERS NEVER TRADE PLACES.
///
/// `release:` is the Rust COMPAT line (CFG_RELEASE, from `src/rust-compat-version`) —
/// the field ecosystem build scripts parse. `trust:` is Trust's own product version
/// (CFG_TRUST_VERSION, from `src/version`). Reporting the product version in
/// `release:` would tell every `autocfg`-style build script that this toolchain
/// predates Rust 1.0, which is exactly the confusion `rustc_driver_impl` documents and
/// avoids for `trustc`.
///
/// Both lines must therefore be present and DISTINCTLY NAMED. This asserts the shape,
/// not the values — a bootstrap that binds neither still satisfies it, and the values
/// are the bootstrap's business.
#[test]
fn verbose_version_reports_compat_and_product_versions_as_separate_fields() {
    let verbose = get_version_string(true);
    let field = |k: &str| {
        verbose
            .lines()
            .filter_map(|l| l.strip_prefix(k))
            .collect::<Vec<_>>()
    };
    assert_eq!(
        field("release: ").len(),
        1,
        "exactly one compat line:\n{verbose}"
    );
    assert_eq!(
        field("trust: ").len(),
        1,
        "exactly one product line:\n{verbose}"
    );
    // `trust-repo-commit-hash:` also starts with "trust" — the product line must not
    // be that one misread by a sloppier prefix test.
    assert_ne!(field("trust: ")[0], "");
    assert!(
        !get_version_string(false).contains("trust: "),
        "terse banner stays terse"
    );
}

/// The parenthetical brand is owed to the INVOKED NAME, not to the binary.
///
/// Under `cargo` the banner must stay byte-identical to Cargo's, because that is the
/// string version-sniffing build scripts assert against. Under `targo` there is no
/// such consumer, so the tool says what it actually is instead of wearing the compat
/// number as its name.
///
/// This pins the RULE (branded iff not `cargo`) rather than a literal, because which
/// frontend a test binary reports depends on how it was invoked.
#[test]
fn the_version_banner_is_branded_only_for_the_non_cargo_frontend() {
    let first = get_version_string(false)
        .lines()
        .next()
        .unwrap_or_default()
        .to_string();
    let name = cargo_binary_name();
    assert!(
        first.starts_with(name),
        "banner must lead with the invoked name: {first}"
    );
    if name == "cargo" {
        // Cargo's native banner can itself contain a parenthesized commit hash
        // and date, for example `cargo 1.99.0-nightly (abc123 2026-08-20)`.
        // That provenance is part of the compatibility surface, not Trust's
        // product brand. Reject only the suffix shapes emitted by `brand`
        // above; rejecting every `(` makes a correctly bootstrap-bound Cargo
        // banner fail this test.
        assert!(
            !first.contains(" (cargo ") && !first.ends_with(" (cargo)"),
            "the `cargo` frontend carries a compat obligation and must not be branded: {first}"
        );
    } else {
        let expected_brand = option_env!("CFG_TRUST_VERSION").map_or_else(
            || format!(" ({name})"),
            |version| format!(" ({name} {version})"),
        );
        assert!(
            first.ends_with(&expected_brand),
            "the `{name}` frontend must identify itself: {first}"
        );
    }
}

/// Every protected lane `--list` prints carries a description.
///
/// `PROTECTED_TRUST_SUBCOMMANDS` (`main.rs`) is the set this frontend inserts
/// into the command list when their binaries resolve; `--list` then looks each
/// up in [`KNOWN_EXTERNAL_COMMAND_DESCRIPTIONS`] for the text beside it. Until
/// 2026-09-01 that map held two of the five, so `trust`, `tippy` and `miri`
/// printed with a blank description -- including `trust`, the lane this
/// binary's own error paths tell users to type.
///
/// The two sets live in different files, which is how they drifted; this pins
/// them together.
#[test]
fn every_protected_lane_is_described() {
    let described: Vec<&str> = KNOWN_EXTERNAL_COMMAND_DESCRIPTIONS
        .iter()
        .map(|(name, _)| *name)
        .collect();
    let missing: Vec<&str> = crate::PROTECTED_TRUST_SUBCOMMANDS
        .iter()
        .copied()
        .filter(|c| !described.contains(c))
        .collect();
    assert!(
        missing.is_empty(),
        "`--list` prints {} protected lane(s) with no description: {missing:?}. \
         A user reading a blank line next to a command cannot tell what it is for, \
         and `trust` is the one the error paths tell them to type.",
        missing.len()
    );
}

/// No description names a binary this toolchain deletes.
///
/// `fmt`'s read "Formats all bin and lib files of the current crate using
/// rustfmt" -- and the installer removes `rustfmt`; the lane runs `targo-fmt`.
/// A reader who reached for the named binary got nothing.
#[test]
fn no_description_names_a_deleted_binary() {
    for (name, desc) in KNOWN_EXTERNAL_COMMAND_DESCRIPTIONS {
        for gone in ["rustfmt", "cargo-clippy", "cargo-fmt"] {
            assert!(
                !desc.contains(gone),
                "the `{name}` description names `{gone}`, which this toolchain \
                 does not ship"
            );
        }
    }
}

#[cfg(test)]
mod append_transport_tests {
    use super::*;

    fn parse(gctx: &GlobalContext, values: &[&str]) -> (ArgMatches, AppendArgs) {
        let mut command = cli(gctx);
        let args = command
            .try_get_matches_from_mut(values.iter().copied())
            .unwrap();
        let append = AppendArgs::from_matches(&command, &args);
        (args, append)
    }

    #[test]
    fn local_append_options_cover_every_declared_command() {
        fn check(command: &Command) {
            for id in ["unstable-features", "config"] {
                let args = command
                    .get_arguments()
                    .filter(|arg| arg.get_id() == id)
                    .collect::<Vec<_>>();
                assert_eq!(args.len(), 1, "{}: {id}", command.get_name());
                assert!(!args[0].is_global_set());
                assert!(matches!(args[0].get_action(), ArgAction::Append));
            }
            for subcommand in command.get_subcommands() {
                check(subcommand);
            }
        }
        check(&cli(&GlobalContext::default().unwrap()));
    }

    #[test]
    fn local_append_values_keep_order_duplicates_and_operands() {
        let gctx = GlobalContext::default().unwrap();
        let (_, append) = parse(
            &gctx,
            &[
                "targo",
                "-Zroot",
                "--config",
                "order=['A']",
                "build",
                "-Zleaf",
                "-Zroot",
                "--config",
                "order=['B']",
                "--config",
                "build.rustflags=['-Zoperand']",
            ],
        );
        assert_eq!(append.unstable_flags, ["root", "leaf", "root"]);
        assert_eq!(
            append.config_args,
            [
                "order=['A']",
                "order=['B']",
                "build.rustflags=['-Zoperand']"
            ]
        );
    }

    #[test]
    fn local_append_values_follow_nested_commands_and_clap_aliases() {
        let gctx = GlobalContext::default().unwrap();
        let (args, append) = parse(
            &gctx,
            &[
                "targo",
                "-Zroot",
                "--config",
                "order='A'",
                "report",
                "-Zmiddle",
                "--config",
                "order='B'",
                "future-incompat",
                "-Zleaf",
                "--config",
                "order='C'",
            ],
        );
        assert_eq!(
            args.subcommand().unwrap().1.subcommand_name(),
            Some("future-incompatibilities")
        );
        assert_eq!(append.unstable_flags, ["root", "middle", "leaf"]);
        assert_eq!(append.config_args, ["order='A'", "order='B'", "order='C'"]);
    }

    #[test]
    fn local_append_values_stop_at_opaque_or_positional_tails() {
        let gctx = GlobalContext::default().unwrap();
        for tail in [
            vec![
                "external-append-test",
                "-Zprogram",
                "--config",
                "program='X'",
            ],
            vec!["entry.rs", "-Zprogram", "--config", "program='X'"],
            vec!["run", "--", "-Zprogram", "--config", "program='X'"],
            vec![
                "run",
                "first-program-arg",
                "-Zprogram",
                "--config",
                "program='X'",
            ],
            vec!["rustc", "--", "-Zprogram", "--config", "program='X'"],
            vec!["help", "report", "rebuilds"],
        ] {
            let mut values = vec!["targo", "-Zroot", "--config", "root='A'"];
            values.extend(tail);
            let (_, append) = parse(&gctx, &values);
            assert_eq!(append.unstable_flags, ["root"], "{values:?}");
            assert_eq!(append.config_args, ["root='A'"], "{values:?}");
        }
    }

    #[test]
    fn early_controls_use_only_recognized_spine_values() {
        let gctx = GlobalContext::default().unwrap();
        let (_, append) = parse(
            &gctx,
            &["targo", "-C", "directory", "build", "-Zunstable-options"],
        );
        assert!(
            append
                .unstable_flags
                .iter()
                .any(|value| value == "unstable-options")
        );
        let (_, append) = parse(
            &gctx,
            &["targo", "-C", "directory", "entry.rs", "-Zunstable-options"],
        );
        assert!(
            !append
                .unstable_flags
                .iter()
                .any(|value| value == "unstable-options")
        );
        let (_, append) = parse(&gctx, &["targo", "report", "rebuilds", "-Zhelp"]);
        assert_eq!(
            append.unstable_flags.first().map(String::as_str),
            Some("help")
        );
        let (_, append) = parse(&gctx, &["targo", "-Zfirst", "build", "-Zhelp"]);
        assert_eq!(
            append.unstable_flags.first().map(String::as_str),
            Some("first")
        );
    }

    #[test]
    fn scalar_global_propagation_is_unchanged() {
        let gctx = GlobalContext::default().unwrap();
        let (args, append) = parse(
            &gctx,
            &[
                "targo",
                "-v",
                "--color=always",
                "--locked",
                "-Zroot",
                "build",
                "-vv",
                "--color=never",
                "--offline",
                "-Zleaf",
            ],
        );
        assert_eq!(args.verbose(), 2);
        assert_eq!(
            args.get_one::<String>("color").map(String::as_str),
            Some("never")
        );
        assert!(args.flag("locked") && args.flag("offline"));
        assert_eq!(append.unstable_flags, ["root", "leaf"]);
    }

    fn alias_context(source: &str) -> (tempfile::TempDir, GlobalContext) {
        let directory = tempfile::tempdir().unwrap();
        let cwd = directory.path().join("project");
        let home = directory.path().join("home");
        std::fs::create_dir_all(cwd.join(".cargo")).unwrap();
        std::fs::create_dir_all(&home).unwrap();
        std::fs::write(cwd.join(".cargo/config.toml"), source).unwrap();
        let gctx = GlobalContext::new(cargo_util_terminal::Shell::new(), cwd, home);
        (directory, gctx)
    }

    #[test]
    fn nested_alias_frames_keep_expanded_order_exactly_once() {
        let (_directory, mut gctx) = alias_context(
            r#"
[alias]
append-outer-test = ["-Zouter", "--config", "order='B'", "append-inner-test", "-Zouter-tail", "--config", "order='C'"]
append-inner-test = ["build", "-Zinner", "--config", "order='D'"]
"#,
        );
        let (args, append) = parse(
            &gctx,
            &[
                "targo",
                "-Zcaller",
                "--config",
                "order='A'",
                "append-outer-test",
                "-Zcaller-tail",
                "--config",
                "order='E'",
            ],
        );
        let (expanded, globals) = expand_aliases(&mut gctx, args, append, vec![]).unwrap();
        assert_eq!(expanded.subcommand_name(), Some("build"));
        assert_eq!(
            globals.append_args.unstable_flags,
            ["caller", "outer", "inner", "outer-tail", "caller-tail"]
        );
        assert_eq!(
            globals.append_args.config_args,
            [
                "order='A'",
                "order='B'",
                "order='D'",
                "order='C'",
                "order='E'"
            ]
        );
    }

    #[test]
    fn nested_alias_cycles_remain_refused() {
        let (_directory, mut gctx) = alias_context(
            r#"
[alias]
append-cycle-a = ["-Zouter", "append-cycle-b"]
append-cycle-b = ["-Zinner", "append-cycle-a"]
"#,
        );
        let (args, append) = parse(&gctx, &["targo", "append-cycle-a"]);
        let result = expand_aliases(&mut gctx, args, append, vec![]);
        let error = match result {
            Ok(_) => panic!("recursive alias accepted"),
            Err(error) => error,
        };
        assert!(format!("{error:?}").contains("unresolvable recursive definition"));
    }

    #[test]
    fn intermediate_alias_restrictions_are_monotone() {
        for (flag, locked, network_restricted) in [
            ("--locked", Some("--locked"), false),
            ("--offline", None, true),
            ("--frozen", Some("--frozen"), true),
        ] {
            let source = format!(
                "[alias]\nbool-outer = [\"{flag}\", \"bool-inner\"]\nbool-inner = [\"build\"]\n"
            );
            let (_directory, mut gctx) = alias_context(&source);
            let (args, append) = parse(&gctx, &["targo", "bool-outer"]);
            let (expanded, globals) = expand_aliases(&mut gctx, args, append, vec![]).unwrap();
            assert_eq!(globals.locked, flag == "--locked");
            assert_eq!(globals.offline, flag == "--offline");
            assert_eq!(globals.frozen, flag == "--frozen");
            configure_gctx(
                &mut gctx,
                &expanded,
                expanded.subcommand().map(|(_, args)| args),
                globals,
                None,
            )
            .unwrap();
            assert_eq!(gctx.locked_flag(), locked);
            if network_restricted {
                assert!(!gctx.network_allowed());
            }
        }
    }

    #[test]
    fn restrictions_combine_across_alias_frames() {
        let (_directory, mut gctx) = alias_context(
            r#"
[alias]
bool-outer = ["--offline", "bool-middle"]
bool-middle = ["--frozen", "bool-inner"]
bool-inner = ["build"]
"#,
        );
        let (args, append) = parse(&gctx, &["targo", "--locked", "bool-outer"]);
        let (expanded, globals) = expand_aliases(&mut gctx, args, append, vec![]).unwrap();
        assert!(globals.locked && globals.offline && globals.frozen);
        configure_gctx(
            &mut gctx,
            &expanded,
            expanded.subcommand().map(|(_, args)| args),
            globals,
            None,
        )
        .unwrap();
        assert_eq!(gctx.locked_flag(), Some("--frozen"));
        assert!(!gctx.network_allowed());
    }

    #[test]
    fn program_arguments_cannot_add_alias_restrictions() {
        let (_directory, mut gctx) = alias_context(
            r#"
[alias]
bool-outer = ["bool-inner"]
bool-inner = ["run"]
"#,
        );
        let (args, append) = parse(
            &gctx,
            &[
                "targo",
                "bool-outer",
                "--",
                "--locked",
                "--offline",
                "--frozen",
            ],
        );
        let (expanded, globals) = expand_aliases(&mut gctx, args, append, vec![]).unwrap();
        assert!(!globals.locked && !globals.offline && !globals.frozen);
        assert!(!expanded.flag("locked") && !expanded.flag("offline") && !expanded.flag("frozen"));
        let tail = expanded
            .subcommand()
            .unwrap()
            .1
            .get_many::<OsString>("args")
            .unwrap()
            .map(|arg| arg.to_str().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(tail, ["--locked", "--offline", "--frozen"]);
    }

    fn configure_alias(gctx: &mut GlobalContext, values: &[&str]) -> CliResult {
        let (args, append) = parse(gctx, values);
        let (expanded, globals) = expand_aliases(gctx, args, append, vec![])?;
        configure_gctx(
            gctx,
            &expanded,
            expanded.subcommand().map(|(_, args)| args),
            globals,
            None,
        )
    }

    #[test]
    fn nested_scalar_flags_override_term_configuration() {
        for flag in ["--quiet", "--verbose", "--color=never"] {
            let term = if flag == "--color=never" {
                "[term]\ncolor='invalid-color-for-test'\n"
            } else {
                "[term]\nverbose=true\nquiet=true\n"
            };
            let source = format!(
                "{term}[alias]\nscalar-outer=[\"{flag}\",\"scalar-inner\"]\nscalar-inner=['locate-project']\n"
            );
            let (_directory, mut gctx) = alias_context(&source);
            configure_alias(&mut gctx, &["targo", "scalar-outer"]).unwrap();
            match flag {
                "--quiet" => assert!(matches!(
                    gctx.shell().verbosity(),
                    cargo_util_terminal::Verbosity::Quiet
                )),
                "--verbose" => {
                    assert!(matches!(
                        gctx.shell().verbosity(),
                        cargo_util_terminal::Verbosity::Verbose
                    ));
                    assert!(!gctx.extra_verbose());
                }
                "--color=never" => {
                    assert!(matches!(gctx.shell().color_choice(), ColorChoice::Never))
                }
                _ => unreachable!(),
            }
        }
    }

    #[test]
    fn single_and_nested_scalar_composition_match() {
        let source = r#"
[alias]
scalar-single=['locate-project','-v','--color=never']
scalar-outer=['-v','--color=never','scalar-inner']
scalar-inner=['locate-project']
scalar-color-outer=['--color=never','scalar-color-inner']
scalar-color-inner=['locate-project','--color=always']
"#;
        for route in ["scalar-single", "scalar-outer"] {
            let (_directory, mut gctx) = alias_context(source);
            configure_alias(&mut gctx, &["targo", "-v", "--color=always", route]).unwrap();
            assert!(matches!(
                gctx.shell().verbosity(),
                cargo_util_terminal::Verbosity::Verbose
            ));
            assert!(gctx.extra_verbose());
            assert!(matches!(gctx.shell().color_choice(), ColorChoice::Never));
        }
        let (_directory, mut gctx) = alias_context(source);
        configure_alias(&mut gctx, &["targo", "--color=never", "scalar-color-outer"]).unwrap();
        assert!(matches!(gctx.shell().color_choice(), ColorChoice::Always));
    }

    #[test]
    fn nested_alias_scalar_conflicts_remain_errors() {
        for (caller, middle) in [("--verbose", "--quiet"), ("--quiet", "--verbose")] {
            let source = format!(
                "[alias]\nscalar-outer=[\"{middle}\",\"scalar-inner\"]\nscalar-inner=['locate-project']\n"
            );
            let (_directory, mut gctx) = alias_context(&source);
            let error = configure_alias(&mut gctx, &["targo", caller, "scalar-outer"]).unwrap_err();
            assert!(format!("{error:?}").contains("cannot set both --verbose and --quiet"));
        }
    }

    #[test]
    fn program_scalars_remain_opaque_after_alias_expansion() {
        let (_directory, mut gctx) = alias_context(
            r#"
[alias]
scalar-outer=['scalar-inner']
scalar-inner=['run']
"#,
        );
        let (args, append) = parse(
            &gctx,
            &[
                "targo",
                "scalar-outer",
                "--",
                "--quiet",
                "--verbose",
                "--color=never",
            ],
        );
        let (expanded, globals) = expand_aliases(&mut gctx, args, append, vec![]).unwrap();
        assert!(!globals.quiet && globals.verbose == 0 && globals.color.is_none());
        assert!(
            !expanded.flag("quiet")
                && expanded.verbose() == 0
                && expanded.get_one::<String>("color").is_none()
        );
        let tail = expanded
            .subcommand()
            .unwrap()
            .1
            .get_many::<OsString>("args")
            .unwrap()
            .map(|arg| arg.to_str().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(tail, ["--quiet", "--verbose", "--color=never"]);
    }

    #[test]
    fn alias_cycles_keep_exact_ordered_diagnostics() {
        for (start, expected) in [
            (
                "self-cycle",
                "alias self-cycle has unresolvable recursive definition: self-cycle -> self-cycle",
            ),
            (
                "cycle-prefix",
                "alias cycle-prefix has unresolvable recursive definition: cycle-prefix -> cycle-a -> cycle-b -> cycle-a",
            ),
        ] {
            let (_directory, mut gctx) = alias_context(
                r#"
[alias]
self-cycle=['self-cycle']
cycle-prefix=['cycle-a']
cycle-a=['cycle-b']
cycle-b=['cycle-a']
"#,
            );
            let (args, append) = parse(&gctx, &["targo", start]);
            let error = expand_aliases(&mut gctx, args, append, vec![])
                .err()
                .expect("recursive alias accepted");
            assert_eq!(error.exit_code, 101);
            assert_eq!(error.error.unwrap().to_string(), expected);
        }
    }

    #[test]
    fn conflicting_builtin_alias_stops_before_expansion() {
        let (_directory, mut gctx) = alias_context(
            r#"
[alias]
builtin-outer=['--offline','-Zouter','build']
build=['build']
"#,
        );
        let (args, append) = parse(&gctx, &["targo", "--locked", "-Zcaller", "builtin-outer"]);
        let (expanded, globals) = expand_aliases(&mut gctx, args, append, vec![]).unwrap();
        assert_eq!(expanded.subcommand_name(), Some("build"));
        assert!(globals.locked && expanded.flag("offline"));
        assert_eq!(globals.append_args.unstable_flags, ["caller", "outer"]);
    }

    #[test]
    fn malformed_builtin_alias_does_not_override_builtin() {
        let (_directory, mut gctx) = alias_context(
            r#"
[alias]
builtin-outer=['--offline','build']
build=17
"#,
        );
        let (args, append) = parse(&gctx, &["targo", "--locked", "builtin-outer"]);
        let (expanded, globals) = expand_aliases(&mut gctx, args, append, vec![]).unwrap();
        assert_eq!(expanded.subcommand_name(), Some("build"));
        assert!(globals.locked && expanded.flag("offline"));
    }

    #[test]
    fn external_alias_tail_stays_opaque_with_prior_flags_retained() {
        let (_directory, mut gctx) = alias_context(
            r#"
[alias]
external-outer=['--locked','-v','--color=never','-Zouter','--config',"order='B'",'external-inner']
external-inner=['external-preservation-test','--opaque']
"#,
        );
        let (args, append) = parse(
            &gctx,
            &[
                "targo",
                "--offline",
                "-Zcaller",
                "--config",
                "order='A'",
                "external-outer",
                "--config",
                "program='opaque'",
                "-Zprogram",
            ],
        );
        let (expanded, globals) = expand_aliases(&mut gctx, args, append, vec![]).unwrap();
        assert_eq!(
            expanded.subcommand_name(),
            Some("external-preservation-test")
        );
        assert!(globals.locked && globals.offline);
        assert_eq!(globals.verbose, 1);
        assert_eq!(globals.color.as_deref(), Some("never"));
        assert_eq!(globals.append_args.unstable_flags, ["caller", "outer"]);
        assert_eq!(globals.append_args.config_args, ["order='A'", "order='B'"]);
        let tail = expanded
            .subcommand()
            .unwrap()
            .1
            .get_many::<OsString>("")
            .unwrap()
            .map(|arg| arg.to_str().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            tail,
            ["--opaque", "--config", "program='opaque'", "-Zprogram"]
        );
    }

    #[test]
    fn manifest_alias_expands_until_script_is_already_enabled() {
        for script in [false, true] {
            let (_directory, mut gctx) = alias_context(
                r#"
[alias]
manifest-outer=['--offline','-Zouter','--config',"order='B'",'entry.rs']
'entry.rs'=['-Zmanifest','locate-project']
"#,
            );
            if script {
                // Use the public per-context test hook, not process environment.
                gctx.nightly_features_allowed = true;
                gctx.configure(
                    0,
                    false,
                    None,
                    false,
                    false,
                    false,
                    &None,
                    &["script".to_owned()],
                    &[],
                )
                .unwrap();
                assert!(gctx.cli_unstable().script);
            }
            let (args, append) = parse(
                &gctx,
                &[
                    "targo",
                    "--locked",
                    "-Zcaller",
                    "--config",
                    "order='A'",
                    "manifest-outer",
                ],
            );
            let (expanded, globals) = expand_aliases(&mut gctx, args, append, vec![]).unwrap();
            assert!(globals.locked);
            assert_eq!(globals.append_args.config_args, ["order='A'", "order='B'"]);
            if script {
                assert_eq!(expanded.subcommand_name(), Some("entry.rs"));
                assert!(expanded.flag("offline") && !globals.offline);
                assert_eq!(globals.append_args.unstable_flags, ["caller", "outer"]);
            } else {
                assert_eq!(expanded.subcommand_name(), Some("locate-project"));
                assert!(globals.offline);
                assert_eq!(
                    globals.append_args.unstable_flags,
                    ["caller", "outer", "manifest"]
                );
            }
        }
    }

    #[test]
    fn alias_missing_command_and_parse_errors_remain_errors() {
        let source = r#"
[alias]
empty-command=[]
flag-only=['--locked']
invalid-option=['locate-project','--not-a-real-option']
"#;
        for (name, expected) in [
            (
                "empty-command",
                "subcommand is required, but `alias.empty-command` is empty",
            ),
            (
                "flag-only",
                "subcommand is required, add a subcommand to the command alias `alias.flag-only`",
            ),
        ] {
            let (_directory, mut gctx) = alias_context(source);
            let (args, append) = parse(&gctx, &["targo", name]);
            let error = expand_aliases(&mut gctx, args, append, vec![])
                .err()
                .expect("missing alias command accepted");
            assert_eq!(error.exit_code, 101);
            assert_eq!(error.error.unwrap().to_string(), expected);
        }
        let (_directory, mut gctx) = alias_context(source);
        let (args, append) = parse(&gctx, &["targo", "invalid-option"]);
        let error = expand_aliases(&mut gctx, args, append, vec![])
            .err()
            .expect("invalid alias option accepted");
        assert_eq!(error.exit_code, 1);
        assert_eq!(
            error
                .error
                .as_ref()
                .unwrap()
                .downcast_ref::<clap::Error>()
                .unwrap()
                .kind(),
            clap::error::ErrorKind::UnknownArgument
        );
    }

    #[derive(Debug, Eq, PartialEq)]
    struct ReparsedFlags {
        verbose: u32,
        quiet: bool,
        unverified: bool,
        color: Option<String>,
        frozen: bool,
        offline: bool,
        locked: bool,
    }

    #[derive(Debug, Eq, PartialEq)]
    struct ReparsedCommand {
        frames: Vec<ReparsedFlags>,
        unstable: Vec<String>,
        config: Vec<String>,
        commands: Vec<String>,
        opaque: Vec<OsString>,
    }

    fn observe_reparse(
        command: &mut Command,
        values: &[OsString],
    ) -> Result<ReparsedCommand, (clap::error::ErrorKind, bool, i32, String)> {
        let args = command
            .try_get_matches_from_mut(values.iter().cloned())
            .map_err(|error| {
                (
                    error.kind(),
                    error.use_stderr(),
                    error.exit_code(),
                    error.render().to_string(),
                )
            })?;
        let append = AppendArgs::from_matches(command, &args);
        let mut observed = ReparsedCommand {
            frames: Vec::new(),
            unstable: append.unstable_flags,
            config: append.config_args,
            commands: Vec::new(),
            opaque: Vec::new(),
        };
        let mut declared = &*command;
        let mut matches = &args;
        loop {
            observed.frames.push(ReparsedFlags {
                verbose: matches.verbose(),
                quiet: matches.flag("quiet"),
                unverified: matches
                    .try_get_one::<bool>("unverified")
                    .ok()
                    .flatten()
                    .copied()
                    .unwrap_or(false),
                color: matches.get_one::<String>("color").cloned(),
                frozen: matches.flag("frozen"),
                offline: matches.flag("offline"),
                locked: matches.flag("locked"),
            });
            if let Ok(Some(tail)) = matches.try_get_many::<OsString>("args") {
                observed.opaque.extend(tail.cloned());
            }
            let Some((name, sub_args)) = matches.subcommand() else {
                break;
            };
            observed.commands.push(name.to_owned());
            let Some(subcommand) = declared.find_subcommand(name) else {
                observed.opaque.extend(
                    sub_args
                        .get_many::<OsString>("")
                        .unwrap_or_default()
                        .cloned(),
                );
                break;
            };
            declared = subcommand;
            matches = sub_args;
        }
        Ok(observed)
    }

    #[test]
    fn mutable_alias_parser_matches_fresh_parser_after_success_help_and_errors() {
        let (_directory, gctx) = alias_context("[term]\ncolor='never'\n");
        // Alias frames have no executable operand. Keep that policy identical
        // on reused/fresh builders, rather than changing sticky bin_name state.
        let mut reused = cli(&gctx).no_binary_name(true);
        let native_consent = reused
            .get_arguments()
            .any(|argument| argument.get_id() == "unverified");
        let cases: &[(&str, &[&str])] = &[
            (
                "rich",
                &[
                    "-vv",
                    "--quiet",
                    "--color=always",
                    "--frozen",
                    "--offline",
                    "--locked",
                    "-Zone",
                    "--config",
                    "order=['A']",
                    "build",
                    "-v",
                    "--color=never",
                    "-Zone",
                    "--config",
                    "order=['B']",
                ],
            ),
            ("consent", &["--unverified", "build"]),
            ("reset", &["locate-project", "--message-format=plain"]),
            (
                "nested",
                &[
                    "-Zroot",
                    "--config",
                    "order='A'",
                    "report",
                    "-Zmiddle",
                    "--config",
                    "order='B'",
                    "future-incompat",
                    "-Zleaf",
                    "--config",
                    "order='C'",
                ],
            ),
            (
                "external",
                &[
                    "-v",
                    "--offline",
                    "-Zfrontend",
                    "--config",
                    "order='front'",
                    "external-parser-test",
                    "-Zprogram",
                    "--config",
                    "program='opaque'",
                    "--locked",
                ],
            ),
            (
                "run-tail",
                &[
                    "--locked",
                    "-Zfrontend",
                    "run",
                    "--",
                    "--offline",
                    "-Zprogram",
                    "--config",
                    "program='opaque'",
                    "--quiet",
                    "--color=always",
                ],
            ),
            ("help", &["--help"]),
            ("after-help", &["locate-project"]),
            ("unknown", &["--not-a-real-parser-option"]),
            (
                "after-unknown",
                &["-q", "--color=auto", "--offline", "locate-project"],
            ),
            ("nested-help", &["report", "rebuilds", "--help"]),
            ("after-nested-help", &["locate-project"]),
            ("invalid-color", &["--color=invalid", "locate-project"]),
            ("after-invalid-color", &["locate-project"]),
            ("identical-retry", &["locate-project"]),
        ];
        for (name, values) in cases {
            let values = values
                .iter()
                .map(|value| OsString::from(*value))
                .collect::<Vec<_>>();
            let expected = observe_reparse(&mut cli(&gctx).no_binary_name(true), &values);
            let actual = observe_reparse(&mut reused, &values);
            assert_eq!(actual, expected, "case={name}");
            if let Ok(observed) = &actual {
                assert!(
                    observed
                        .frames
                        .iter()
                        .all(|frame| frame.unverified == (*name == "consent" && native_consent)),
                    "consent leaked or disappeared: case={name} observed={observed:?}"
                );
            }
            match *name {
                "consent" if !native_consent => assert_eq!(
                    actual.unwrap_err().0,
                    clap::error::ErrorKind::UnknownArgument,
                    "Cargo compatibility must keep refusing native consent"
                ),
                "rich" => {
                    let actual = actual.unwrap();
                    assert_eq!(actual.frames[0].verbose, 1);
                    assert!(actual.frames[0].quiet);
                    assert_eq!(actual.frames[0].color.as_deref(), Some("never"));
                    assert!(
                        actual.frames[0].frozen
                            && actual.frames[0].offline
                            && actual.frames[0].locked
                    );
                    assert_eq!(actual.unstable, ["one", "one"]);
                    assert_eq!(actual.config, ["order=['A']", "order=['B']"]);
                }
                "reset" => {
                    let actual = actual.unwrap();
                    assert_eq!(
                        actual.frames[0],
                        ReparsedFlags {
                            verbose: 0,
                            quiet: false,
                            unverified: false,
                            color: None,
                            frozen: false,
                            offline: false,
                            locked: false,
                        }
                    );
                    assert!(
                        actual.unstable.is_empty()
                            && actual.config.is_empty()
                            && actual.opaque.is_empty()
                    );
                }
                "nested" => {
                    let actual = actual.unwrap();
                    assert_eq!(actual.commands, ["report", "future-incompatibilities"]);
                    assert_eq!(actual.unstable, ["root", "middle", "leaf"]);
                    assert_eq!(actual.config, ["order='A'", "order='B'", "order='C'"]);
                }
                "external" | "run-tail" => {
                    let actual = actual.unwrap();
                    assert_eq!(actual.unstable, ["frontend"]);
                    assert!(
                        actual
                            .opaque
                            .iter()
                            .any(|arg| arg == OsStr::new("-Zprogram"))
                    );
                    assert!(
                        actual
                            .opaque
                            .iter()
                            .any(|arg| arg == OsStr::new("program='opaque'"))
                    );
                    if *name == "external" {
                        assert_eq!(actual.config, ["order='front'"]);
                        assert!(!actual.frames[0].locked);
                    } else {
                        assert!(actual.config.is_empty());
                        assert!(
                            actual.frames[0].locked
                                && !actual.frames[0].offline
                                && !actual.frames[0].quiet
                        );
                        assert!(actual.frames[0].color.is_none());
                    }
                }
                "help" | "nested-help" => {
                    assert_eq!(actual.unwrap_err().0, clap::error::ErrorKind::DisplayHelp)
                }
                "unknown" => assert_eq!(
                    actual.unwrap_err().0,
                    clap::error::ErrorKind::UnknownArgument
                ),
                "invalid-color" => {
                    assert_eq!(actual.unwrap_err().0, clap::error::ErrorKind::InvalidValue)
                }
                _ => assert!(actual.is_ok()),
            }
        }
        #[cfg(unix)]
        {
            use std::os::unix::ffi::OsStringExt as _;
            let opaque = OsString::from_vec(b"opaque-\xff".to_vec());
            for values in [
                vec![OsString::from("external-parser-test"), opaque.clone()],
                vec![OsString::from("run"), OsString::from("--"), opaque.clone()],
            ] {
                let expected = observe_reparse(&mut cli(&gctx).no_binary_name(true), &values);
                let actual = observe_reparse(&mut reused, &values);
                assert_eq!(actual, expected);
                assert!(
                    actual
                        .as_ref()
                        .unwrap()
                        .frames
                        .iter()
                        .all(|frame| !frame.unverified)
                );
                assert_eq!(
                    actual.unwrap().opaque.as_slice(),
                    std::slice::from_ref(&opaque)
                );
            }
        }
    }

    #[test]
    fn mutable_alias_parser_is_built_after_rooted_term_reload() {
        let (directory, mut gctx) = alias_context("[term]\ncolor='always'\n");
        let new_root = directory.path().join("selected-root");
        std::fs::create_dir_all(new_root.join(".cargo")).unwrap();
        std::fs::write(
            new_root.join(".cargo/config.toml"),
            "[term]\ncolor='never'\n",
        )
        .unwrap();
        let mut original = cli(&gctx);
        assert_eq!(original.get_color(), clap::ColorChoice::Always);
        let args = original
            .try_get_matches_from_mut([
                OsString::from("targo"),
                OsString::from("-Zunstable-options"),
                OsString::from("-C"),
                new_root.clone().into_os_string(),
            ])
            .unwrap();
        assert_eq!(
            args.get_one::<std::path::PathBuf>("directory"),
            Some(&new_root)
        );
        // Exercise only the public config-root reload, without changing the
        // process cwd/HOME. This is not an actual main() -C execution.
        gctx.reload_rooted_at(&new_root).unwrap();
        let mut reused = cli(&gctx).no_binary_name(true);
        assert_eq!(reused.get_color(), clap::ColorChoice::Never);
        for values in [
            ["--help"],
            ["--not-a-real-parser-option"],
            ["locate-project"],
        ] {
            let values = values.into_iter().map(OsString::from).collect::<Vec<_>>();
            assert_eq!(
                observe_reparse(&mut reused, &values),
                observe_reparse(&mut cli(&gctx).no_binary_name(true), &values),
            );
        }
    }

    #[test]
    fn context_directory_reload_preserves_process_cwd_and_selected_home() {
        let (directory, mut gctx) = alias_context("[term]\ncolor='always'\n");
        let process_cwd = std::env::current_dir().unwrap();
        let selected_home = gctx.home().as_path_unlocked().to_owned();
        let selected = directory.path().join("library-directory");
        std::fs::create_dir_all(selected.join(".cargo")).unwrap();
        std::fs::write(
            selected.join(".cargo/config.toml"),
            "[term]\ncolor='never'\n",
        )
        .unwrap();
        gctx.reload_directory(selected.clone()).unwrap();
        assert_eq!(gctx.cwd(), selected);
        assert_eq!(gctx.home().as_path_unlocked(), selected_home);
        assert_eq!(std::env::current_dir().unwrap(), process_cwd);
        assert_eq!(cli(&gctx).get_color(), clap::ColorChoice::Never);
        assert!(gctx.reload_directory("relative-directory".into()).is_err());
        assert_eq!(gctx.cwd(), selected);
    }

    #[test]
    fn consent_comes_from_each_actual_argv_before_its_delimiter() {
        let words = |args: &[&str]| args.iter().map(OsString::from).collect::<Vec<_>>();
        assert!(argv_has_unverified_before_delimiter(&words(&[
            "targo",
            "--unverified",
            "build",
        ])));
        assert!(argv_has_unverified_before_delimiter(&words(&[
            "targo",
            "external",
            "--unverified",
        ])));
        assert!(!argv_has_unverified_before_delimiter(&words(&[
            "targo", "build",
        ])));
        assert!(!argv_has_unverified_before_delimiter(&words(&[
            "targo",
            "run",
            "--",
            "--unverified",
        ])));
        assert!(!argv_has_unverified_before_delimiter(&words(&[
            "targo",
            "--",
            "--unverified",
            "build",
        ])));
    }

    #[test]
    fn full_library_marker_guard_uses_the_canonical_parser() {
        let (_directory, gctx) = alias_context("");
        let mut parser = cli_for_frontend(&gctx, true);
        let ordinary = parser.try_get_matches_from_mut(["targo", "build"]).unwrap();
        require_no_native_startup(&ordinary).unwrap();
        for flags in [
            vec!["targo", "--resource-worker-v2", "build"],
            vec![
                "targo",
                "--resource-worker-v3",
                "--resource-subgroups-v3",
                "build",
            ],
        ] {
            let parsed = parser.try_get_matches_from_mut(flags).unwrap();
            assert!(require_no_native_startup(&parsed).is_err());
        }
        let error = cli_for_frontend(&gctx, false)
            .try_get_matches_from(["cargo", "--resource-worker-v2", "build"])
            .unwrap_err();
        assert_eq!(error.kind(), clap::error::ErrorKind::UnknownArgument);
    }
}
