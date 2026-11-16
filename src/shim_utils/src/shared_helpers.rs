// Trust: formerly `src/bootstrap/src/utils/shared_helpers.rs`, embedded in the
// bootstrap shims via `#[path]`; upstream 1.101 moved it into this crate and
// Trust's shim logic (~800 lines: the cargo-test shim environment and the
// trust-verify argv canonicalization) moved with it. This module must never
// use any bootstrap-crate module (it is shared with the shim binaries).

use std::collections::HashMap;
use std::env;
use std::ffi::{OsStr, OsString};
use std::fs::{self, OpenOptions};
use std::io::{self, BufRead, Write};
use std::path::Path;
use std::process::Command;
use std::str::FromStr;

pub const TRUST_CARGO_TEST_SHIM_CONFIG: &str = ".trust-cargo-test-shim.json";
pub const TRUST_CARGO_TEST_SHIM_VERSION: &str = "3";

const TRUST_CARGO_TEST_SHIM_KEYS: [&str; 13] = [
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
    "TRUST_VANILLA_ANNOUNCED",
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

/// Bootstrap's per-unit `library/` verification channel.
///
/// The counterpart of [`TRUST_BOOTSTRAP_SHIM_NO_VERIFY`][no-verify]: bootstrap
/// sets this ONLY on cargo invocations whose `Mode` it authorized (library
/// units, stage>=1) and `env_remove`s it on every other invocation, so an
/// ambient value cannot reach a compiler, bootstrap or tool unit. This function
/// is the second half of the check and the reason the lane is *per unit* rather
/// than per invocation: the same `Mode::Std` cargo invocation that compiles
/// `core` also compiles std's third-party dependency graph, and only the shim
/// knows the `--crate-name` of the crate it is about to hand to the driver.
///
/// Names are compared after `-` -> `_` normalization, matching how Cargo spells
/// a crate name on the command line.
///
/// [no-verify]: trust_bootstrap_shim_marker_enabled
pub fn trust_bootstrap_verify_unit_requested(
    units: Option<&OsStr>,
    crate_name: Option<&str>,
) -> bool {
    let (Some(units), Some(crate_name)) = (units.and_then(OsStr::to_str), crate_name) else {
        return false;
    };
    let crate_name = crate_name.trim().replace('-', "_");
    if crate_name.is_empty() {
        return false;
    }
    units.split(',').any(|unit| unit.trim().replace('-', "_") == crate_name)
}

/// Replace every spelling/value of the Trust verification switch with one final
/// `-Ztrust-verify=on`, immediately before a positional `--` boundary.
///
/// The unit reaches the shim carrying bootstrap's invocation-wide
/// `-Ztrust-verify=off` in argv (rustflags arrive as argv). Last-value-wins
/// would already do the right thing, but canonicalizing leaves exactly ONE
/// verifier control on the command line, so `x.py -vv` output and any later
/// audit of the recorded argv read unambiguously.
pub fn canonicalize_trust_verify_on(args: &mut Vec<OsString>) {
    strip_trust_no_verify(args);
    let option_boundary = args.iter().position(|arg| arg == "--").unwrap_or(args.len());
    args.insert(option_boundary, OsString::from("-Ztrust-verify=on"));
}

/// A verifier control the per-unit `library/` lane must never carry: everything
/// in the `-Ztrust-*` verifier surface EXCEPT the plain on/off switch, which
/// [`canonicalize_trust_verify_on`] owns. Name-matched after `_` -> `-`
/// normalization, exactly like the driver resolves `-Z` options.
fn is_trust_verifier_scope_or_identity_option(option: &OsStr) -> bool {
    option.to_str().is_some_and(|option| {
        let name = option.split_once('=').map_or(option, |(name, _)| name).replace('_', "-");
        name == "trust-policy" || name.starts_with("trust-verify-")
    })
}

/// Refuse any verifier control besides the plain on/off switch on a unit the
/// per-unit `library/` opt-in authorized. `None` means the argv is clean.
///
/// WHY, because this is the lane's SEPARATE NAME made checkable: the opt-in is
/// the one bootstrap-driven path where the verifier runs, and it runs
/// UNAUTHENTICATED and UNSCOPED — `-Ztrust-verify=on` with no proof-session
/// identity. Every other verifier control is one of:
///
///  * an authenticated proof-session identity — `-Ztrust-verify-session`,
///    whose PRESENCE the driver reads as "requests authenticated verification
///    coverage" (`rustc_driver_impl/src/lib.rs`) and whose value the
///    self-verify harness mints as `self-verify-<nonce>`
///    (`targo-trust/src/self_verify_cli.rs`), plus the Targo-reserved metadata
///    that requires it (`-Ztrust-verify-package-name`,
///    `-Ztrust-verify-crate-role`);
///  * a policy or scope control — `-Ztrust-policy=advisory` alone would
///    silently change what this lane's green MEANS while every banner still
///    reads full verification.
///
/// A library unit carrying the former would masquerade as the authenticated
/// self-verify lane — the exact confusion the separately-named lane exists to
/// prevent — and one carrying the latter would verify at a weaker policy than
/// it reports. Bootstrap's rustflags refusal
/// (`core/builder/cargo.rs::refuse_bootstrap_verification_request`) already
/// aborts these invocation-wide; this is the per-unit half, at the one boundary
/// that sees the FINAL argv, so no other flag source can smuggle one in.
/// Refused, not stripped: a control that is silently discarded is
/// indistinguishable from one that worked.
pub fn trust_bootstrap_verify_unit_argv_refusal(args: &[OsString]) -> Option<String> {
    let mut iter = args.iter().take_while(|arg| *arg != "--").peekable();
    while let Some(arg) = iter.next() {
        let option = if arg == "-Z" {
            iter.peek().map(|option| option.as_os_str())
        } else {
            arg.to_str()
                .and_then(|arg| arg.strip_prefix("-Z"))
                .filter(|option| !option.is_empty())
                .map(OsStr::new)
        };
        if let Some(option) = option
            && is_trust_verifier_scope_or_identity_option(option)
        {
            return Some(format!(
                "trust: the per-unit library verification lane refuses the verifier control \
                 `-Z{}` on this unit. The lane compiles a `library/` unit with exactly \
                 `-Ztrust-verify=on` and nothing else from the verifier surface: it is \
                 unauthenticated and unscoped, so a proof-session identity \
                 (`trust-verify-session`, `trust-verify-package-name`, \
                 `trust-verify-crate-role`) would masquerade as the authenticated \
                 self-verify lane, and a policy control (`trust-policy`) would silently \
                 change what this lane's green means. Options: drop the flag; unset \
                 TRUST_BOOTSTRAP_VERIFY_LIBRARY so the unit keeps the default \
                 `-Ztrust-verify=off`; or use the authenticated lanes that own these \
                 controls (`targo trust check|build`).",
                option.to_string_lossy()
            ));
        }
    }
    None
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

/// EXACT, both spellings. This answer decides whether a snapshot compile gets
/// the `TRUST_NO_VERIFY=1` transport, i.e. whether verification is ON or OFF for
/// that unit, so a value this function does not recognize must never be read as
/// "off".
///
/// * `trust-verify` is `parse_trust_verify`, "one of `on` or `off`"
///   (`rustc_session/src/options.rs`), so only the literal `off` is an
///   off-request.
/// * `no-trust-verify`, the retired pre-`576db732cd` name, was
///   `no_trust_verify: bool = (false, parse_bool, [TRACKED], ...)`
///   (`576db732cd^:compiler/rustc_session/src/options.rs:2788`). `parse_bool`
///   accepts `y`/`yes`/`on`/`true` and the bare form as TRUE (= do not verify),
///   `n`/`no`/`off`/`false` as FALSE (= do verify), and REJECTS anything else.
///   All three spellings the retired ecosystem actually emitted are covered:
///   compiletest used bare and `=yes` to turn verification off and `=no` to turn
///   it on (`576db732cd^:src/tools/compiletest/src/directives.rs:458-463`).
///
/// Note the double negative in `no-trust-verify=off`: under `parse_bool` that
/// sets `no_trust_verify = false`, which means verification ON. This used to
/// accept every value except the literal `no` — so `=off`, `=false`, `=0` and
/// every typo silently meant "off". Anything outside `parse_bool`'s two sets
/// would have been a hard parse error at the driver; treating it as "not an
/// off-request" keeps the caller fail-closed (verification stays on and the
/// build fails loudly) instead of silently unverified.
fn is_trust_verify_off_option(option: &OsStr) -> bool {
    option.to_str().is_some_and(|option| {
        let (name, value) = match option.split_once('=') {
            Some((name, value)) => (name, Some(value)),
            None => (option, None),
        };
        match name.replace('_', "-").as_str() {
            "trust-verify" => value == Some("off"),
            "no-trust-verify" => matches!(value, None | Some("y" | "yes" | "on" | "true")),
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
/// which admits real target and host compiles on supported snapshots) and an
/// explicit argv off-request, such as one materialized by `RUSTC_HOST_FLAGS`
/// for a build script or proc macro. The latter must be honored even when the
/// shim's own add-path is not requested. A
/// stripped-but-unhonored off-request would silently re-enable batteries-on
/// verification of the whole bootstrap dependency tree — the memchr wall.
/// An `=on` request never rides the transport: only the exact off value
/// counts. Non-snapshot drivers (stage1+, or a `trustc` outside stage0) keep
/// the canonical argv spelling instead.
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

/// A retired bootstrap-shim marker that is still scrubbed in six places but read
/// nowhere. Setting it used to be a silent no-op, which is indistinguishable
/// from a control that worked.
pub const RETIRED_TRUST_BOOTSTRAP_SHIM_TARGET_ONLY_ENV: &str =
    "TRUST_BOOTSTRAP_SHIM_NO_VERIFY_TARGET_ONLY";

/// Refuse the retired marker by name, the way `TRUST_FLYWHEEL` is refused.
///
/// It named a "target crates only" isolation lane that no longer exists:
/// bootstrap isolation has to cover untargeted HOST units (build scripts, proc
/// macros) too, so there is nothing left to select. Presence is the trigger —
/// any value, including the empty string — because there is no value that could
/// have the effect the name promises.
///
/// Returns `None` when the variable is unset, i.e. for every existing workflow.
pub fn retired_trust_bootstrap_shim_target_only_refusal(value: Option<&OsStr>) -> Option<String> {
    value.is_some().then(|| {
        format!(
            "{RETIRED_TRUST_BOOTSTRAP_SHIM_TARGET_ONLY_ENV} is retired and has no effect: \
             bootstrap isolation must cover target crates AND untargeted host units (build \
             scripts, proc macros), so there is no target-only lane to select. Unset it. The \
             live controls are `TRUST_BOOTSTRAP_SHIM_NO_VERIFY=1` (bootstrap-internal IPC, set \
             by bootstrap itself) and, to verify a `library/` unit, \
             `TRUST_BOOTSTRAP_VERIFY_LIBRARY=<unit>[,<unit>...]`."
        )
    })
}

/// Does bootstrap's non-self-proving off-switch apply to THIS shim invocation?
///
/// One policy, one implementation. The rustc and rustdoc shims each used to
/// carry a copy of this predicate and had already diverged once historically.
/// A shim with a single driver (rustdoc) passes the same capability answer for
/// both `has_target` arms, which reduces the expression to
/// `requested && supports && is_a_real_compile` — exactly what its private copy
/// computed.
pub fn trust_bootstrap_no_verify_applies(
    has_target: bool,
    requested: bool,
    targeted_driver_supports_no_verify: bool,
    no_target_driver_supports_no_verify: bool,
    args: &[OsString],
    // Not read: the crate name selects the per-unit VERIFY opt-in
    // (`trust_bootstrap_verify_unit_applies`), never the off-switch, which is
    // invocation-wide. Kept in the signature because every call site has the
    // name in hand and the two predicates are read side by side.
    _crate_name: Option<&str>,
) -> bool {
    // Trust: `-Ztrust-verify=off` only exists in Trust drivers. With a
    // bring-your-own stage0 (bootstrap/trust-stage0/README.md), targeted
    // stage0 invocations run a stock upstream rustc, which rejects the flag.
    requested
        && compile_uses_trust_bootstrap_no_verify(args)
        && if has_target {
            targeted_driver_supports_no_verify
        } else {
            no_target_driver_supports_no_verify
        }
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

/// Trust: the `--print` kinds Cargo's target-information probe sends, and the
/// only ones [`is_cargo_target_info_probe`] admits. `TargetInfo::new`
/// (`src/tools/targo/src/cargo/core/compiler/build_context/target_info.rs`; the
/// print kinds are upstream Cargo's) sends `--print=file-names`,
/// `--print=sysroot`, `--print=split-debuginfo`, `--print=crate-name` and
/// `--print=cfg`; the installed pack's Targo (`321aaeda7`, `build.cargo` in
/// atpkg mode) sends the same five (its argv logged 2026-10-13 through a
/// `RUSTC_WRAPPER`). Each one STOPS compilation after
/// printing. `native-static-libs` and `link-args` are deliberately absent:
/// rustc keeps compiling when every print request is one of those two, which
/// are printed during linking (`rustc_driver_impl::print_crate_info`).
const CARGO_TARGET_INFO_PROBE_PRINT_KINDS: [&str; 5] =
    ["file-names", "sysroot", "split-debuginfo", "crate-name", "cfg"];

/// Trust: rustc's options whose value may be the NEXT argument
/// (`rustc_session::config::rustc_optgroups`: every `Opt` and `Multi` group), so
/// [`is_cargo_target_info_probe`] reads `--cfg --print=cfg` as one `--cfg` and
/// never as a print request. A short option's value may also be glued on
/// (`-Wwarnings`, `-Zhelp`); a long option's may follow an `=`.
const RUSTC_OPTIONS_WITH_A_VALUE: [&str; 35] = [
    "-L",
    "-l",
    "-o",
    "-A",
    "-W",
    "-D",
    "-F",
    "-C",
    "-Z",
    "--cfg",
    "--check-cfg",
    "--crate-type",
    "--crate-name",
    "--edition",
    "--emit",
    "--print",
    "--out-dir",
    "--explain",
    "--target",
    "--allow",
    "--warn",
    "--force-warn",
    "--deny",
    "--forbid",
    "--cap-lints",
    "--codegen",
    "--extern",
    "--sysroot",
    "--error-format",
    "--json",
    "--color",
    "--diagnostic-width",
    "--remap-path-prefix",
    "--remap-path-scope",
    "--env-set",
];

/// Trust: the options whose value `help` makes rustc print a help text and
/// exit, compiling nothing (`-Z help`, `-C help`/`--codegen=help`, and a lint
/// `help` at any level, `rustc_session::config::get_cmd_lint_options`). Not a
/// probe in any spelling.
const RUSTC_HELP_QUERY_OPTIONS: [&str; 12] = [
    "-Z",
    "-C",
    "--codegen",
    "-A",
    "--allow",
    "-W",
    "--warn",
    "--force-warn",
    "-D",
    "--deny",
    "-F",
    "--forbid",
];

/// Trust: whether a shim invocation is Cargo's TARGET-INFORMATION probe, the
/// query Cargo runs before any unit to learn file names, the sysroot and the
/// target cfgs:
///
/// ```text
/// [<compiler>…] - --crate-name ___ --print=file-names <rustflags> [--target T]
///     --crate-type bin … --print=sysroot --print=split-debuginfo
///     --print=crate-name --print=cfg -Wwarnings
/// ```
///
/// (`<compiler>…` is Cargo's `RUSTC`, and a workspace wrapper before it,
/// present when the shim runs as `RUSTC_WRAPPER`, as bootstrap runs it.) Narrow
/// by construction, so that a compile which is not CERTAINLY a probe keeps
/// today's answer (DECISION_QUEUE BOOTSTRAP-PROBE-OFF-1, review follow-ups).
/// The argv is read the way rustc's getopts reads it, and every token outside
/// Cargo's shape answers "not a probe". All of these must hold:
///
/// * at least one `--print` request, and EVERY one is a kind in
///   [`CARGO_TARGET_INFO_PROBE_PRINT_KINDS`], written to stdout (no `=PATH`),
///   in either spelling (`--print=KIND`, `--print KIND`). Each of those kinds
///   stops compilation, so the probe compiles nothing. A
///   `--print=native-static-libs` or `--print=link-args` compile (rustc keeps
///   compiling for those) is not a probe, nor is any print Cargo's probe does
///   not send;
/// * the input is stdin: one `-`, before every option. Free arguments are
///   admitted only before it (the compiler paths a wrapper sees); a free
///   argument after it or after any option is a second input, not Cargo's
///   shape;
/// * `--crate-name` is `___`;
/// * every single-dash token is one short option: `-X`, or `-X` with its value
///   glued on (`-Wwarnings`, `-Zinline-mir`) when `-X` takes a value. A
///   cluster (`-gL`, `-OL`, `-vV`) is refused: getopts reads `-gL` as `-g -L`,
///   and that `-L` takes the NEXT argument, so `-gL --print=cfg` prints nothing
///   and compiles. Cargo never sends one;
/// * no `--` boundary (Cargo's probe has none), and no version, help or
///   `--explain` query (`-V`, `--help`, `-Z help`, `--codegen=help`,
///   `--warn help`, …: not probes);
/// * every argument is UTF-8, and every option that takes a value has one.
pub fn is_cargo_target_info_probe(args: &[OsString]) -> bool {
    let mut prints = 0_usize;
    let mut reads_stdin = false;
    let mut crate_name_is_probe = false;
    // Still before the input `-` and before every option: the only place a
    // free argument (a wrapper's compiler path) is admitted.
    let mut leading = true;
    let mut index = 0;
    while let Some(arg) = args.get(index) {
        index += 1;
        let Some(arg) = arg.to_str() else {
            return false;
        };
        // A free argument, as getopts reads one: not an option token (`-` is
        // free: it names stdin).
        if !arg.starts_with('-') || arg == "-" {
            if !leading {
                return false;
            }
            if arg == "-" {
                reads_stdin = true;
                leading = false;
            }
            continue;
        }
        leading = false;
        // Split the option from its value: `--long=value`, `--long value`,
        // `-Xvalue` or `-X value`; anything else is a flag.
        let mut next_value = || {
            let value = args.get(index).and_then(|value| value.to_str());
            index += 1;
            value
        };
        let (option, value) = if arg.starts_with("--") {
            match arg.split_once('=') {
                Some((long, value)) => (long, Some(value)),
                None if RUSTC_OPTIONS_WITH_A_VALUE.contains(&arg) => {
                    let Some(value) = next_value() else {
                        return false;
                    };
                    (arg, Some(value))
                }
                None => (arg, None),
            }
        } else if arg.len() == 2 {
            if RUSTC_OPTIONS_WITH_A_VALUE.contains(&arg) {
                let Some(value) = next_value() else {
                    return false;
                };
                (arg, Some(value))
            } else {
                (arg, None)
            }
        } else if let Some(short) =
            arg.get(..2).filter(|short| RUSTC_OPTIONS_WITH_A_VALUE.contains(short))
        {
            (short, arg.get(2..))
        } else {
            // A cluster of short options, or a non-ASCII one: never Cargo's.
            return false;
        };
        match (option, value) {
            ("--", _) => return false,
            ("--print", Some(kind)) => {
                if !CARGO_TARGET_INFO_PROBE_PRINT_KINDS.contains(&kind) {
                    return false;
                }
                prints += 1;
            }
            ("--crate-name", Some(name)) => crate_name_is_probe = name == "___",
            ("-h" | "--help" | "-V" | "--version" | "--explain", _) => return false,
            (option, Some("help")) if RUSTC_HELP_QUERY_OPTIONS.contains(&option) => return false,
            _ => {}
        }
    }
    prints > 0 && reads_stdin && crate_name_is_probe
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
    /// Restore fixture-authored variables, then carry the owner's already
    /// announced ordinary policy to this compiler child only. An authored
    /// variable cannot manufacture that authority for a verified invocation.
    pub fn restore_for_compiler_command(&mut self, command: &mut Command, no_verify_applies: bool) {
        self.restore();
        if no_verify_applies {
            command.env("TRUST_VANILLA_ANNOUNCED", "1");
        } else {
            command.env_remove("TRUST_VANILLA_ANNOUNCED");
        }
    }

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

    let configured = read_cargo_test_shim_config(&config_path)?;
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

fn read_cargo_test_shim_config(config_path: &Path) -> io::Result<HashMap<String, String>> {
    let configured: HashMap<String, String> = serde_json::from_slice(&fs::read(config_path)?)
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
        || configured["TRUST_VANILLA_ANNOUNCED"] != "1"
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

    Ok(configured)
}

// Trust: keep the original test namespace in a separate test file.
#[cfg(test)]
#[path = "shared_helpers/tests.rs"]
mod cargo_test_shim_context_tests;

/// Collect all the command line arguments, including the arguments from any `@argfile`
pub fn collect_args() -> Vec<OsString> {
    let mut args = Vec::with_capacity(env::args_os().len());
    for arg in env::args_os().skip(1) {
        if let Some(s) = arg.to_str()
            && let Some(path) = s.strip_prefix('@')
        {
            args.extend(args_from_argfile(Path::new(path)));
        } else {
            args.push(arg)
        }
    }
    args
}

/// Reads all the arguments from argfile given by `path`.
/// Each argument should be on a line by itself
fn args_from_argfile(path: &Path) -> Vec<OsString> {
    fn collect_lines(path: &Path) -> Result<Vec<OsString>, std::io::Error> {
        let file = std::fs::File::open(path)?;
        let lines: Result<Vec<OsString>, std::io::Error> =
            std::io::BufReader::new(file).lines().map(|r| r.map(OsString::from)).collect();
        lines
    }
    collect_lines(path).expect("read args from argfile {path:?}")
}
