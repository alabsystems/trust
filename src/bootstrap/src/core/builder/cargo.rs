use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::{env, fs};

// Trust: shim helpers live in the `shim_utils` crate since the 1.101 port.
use shim_utils::{
    BOOTSTRAP_FRONTEND_CEILING_ENV, RETIRED_TRUST_BOOTSTRAP_SHIM_TARGET_ONLY_ENV,
    bootstrap_seed_frontend_ceiling, retired_trust_bootstrap_shim_target_only_refusal,
};

use super::{Builder, Kind};
use crate::core::backend::CodegenBackendKind;
use crate::core::build_steps::compile::{is_lto_stage, std_compiler_runtime_identity};
use crate::core::build_steps::llvm::Llvm;
use crate::core::build_steps::test;
use crate::core::build_steps::tool::{SourceType, TargoBuildTool};
use crate::core::compiler::Compiler;
use crate::core::config::flags::{Color, Subcommand};
use crate::core::config::toml::pgo::PgoConfig;
use crate::core::config::{
    CompressDebuginfo, Config, DebuginfoLevel, DryRun, RustcLto, SplitDebuginfo, TargetSelection,
};
use crate::core::session::{CLang, Mode, RemapScheme};
use crate::utils::build_stamp;
use crate::utils::exec::{BootstrapCommand, ExecutionContext, command};
use crate::utils::helpers::{self, LldThreads, check_cfg_arg, envify, linker_flags, t};

/// Extra `--check-cfg` to add when building the compiler or tools
/// (Mode restriction, config name, config values (if any))
#[expect(clippy::type_complexity)] // It's fine for hard-coded list and type is explained above.
const EXTRA_CHECK_CFGS: &[(Option<Mode>, &str, Option<&[&'static str]>)] = &[
    (Some(Mode::Rustc), "bootstrap", None),
    (Some(Mode::Codegen), "bootstrap", None),
    (Some(Mode::ToolRustcPrivate), "bootstrap", None),
    (Some(Mode::ToolStd), "bootstrap", None),
    (Some(Mode::ToolRustcPrivate), "rust_analyzer", None),
    (Some(Mode::ToolStd), "rust_analyzer", None),
    // Any library specific cfgs like `target_os`, `target_arch` should be put in
    // priority the `[lints.rust.unexpected_cfgs.check-cfg]` table
    // in the appropriate `library/{std,alloc,core}/Cargo.toml`
];

/// Represents flag values in `String` form with a `\x1f` delimiter to pass to the compiler later.
///
/// Flags are emitted via `CARGO_ENCODED_RUSTFLAGS` / `CARGO_ENCODED_RUSTDOCFLAGS`,
/// which use `\x1f` (ASCII Unit Separator) as the delimiter and therefore allow spaces
/// within individual flag values (e.g. paths from `llvm-config --libdir`).
///
/// `-Z crate-attr` flags will be applied recursively on the target code using the
/// `rustc_parse::parser::Parser`. See `rustc_builtin_macros::cmdline_attrs::inject` for more
/// information.
#[derive(Debug, Clone)]
struct Rustflags(String, TargetSelection);

// Trust: mirror rustc's direct-linker name hints. Unknown configured drivers
// keep the target's existing CC convention; do not guess from a path substring.
fn configured_direct_linker(linker: Option<&Path>) -> bool {
    let Some(stem) = linker.and_then(Path::file_stem).and_then(OsStr::to_str) else {
        return false;
    };
    let stem = stem
        .rsplit_once('-')
        .filter(|(_, version)| version.chars().all(char::is_numeric))
        .map_or(stem, |(name, _)| name);
    matches!(stem, "lld" | "rust-lld" | "ld.lld" | "lld-link" | "ld" | "link")
        || stem.ends_with("-ld")
}

// Trust: preserve the sysroot-relative loader policy while passing flags to
// the configured linker at its own interface, rather than always through CC.
fn append_sysroot_rpath(
    flags: &mut Rustflags,
    target: TargetSelection,
    libdir: &str,
    direct: bool,
) {
    let rpath = if target.contains("apple") {
        flags.arg("-Zosx-rpath-install-name");
        format!("@loader_path/../{libdir}")
    } else if !target.is_windows()
        && !target.contains("cygwin")
        && !target.contains("aix")
        && !target.contains("xous")
    {
        if direct {
            flags.arg("-Clink-arg=-z").arg("-Clink-arg=origin");
        } else {
            flags.arg("-Clink-args=-Wl,-z,origin");
        }
        format!("$ORIGIN/../{libdir}")
    } else {
        return;
    };
    if direct {
        flags.arg("-Clink-arg=-rpath").arg(&format!("-Clink-arg={rpath}"));
    } else {
        flags.arg(&format!("-Clink-args=-Wl,-rpath,{rpath}"));
    }
}

impl Rustflags {
    fn new(target: TargetSelection) -> Rustflags {
        Rustflags(String::new(), target)
    }

    /// By default, cargo will pick up on various variables in the environment. However, bootstrap
    /// reuses those variables to pass additional flags to rustdoc, so by default they get
    /// overridden. Explicitly add back any previous value in the environment.
    ///
    /// `prefix` is usually `RUSTFLAGS` or `RUSTDOCFLAGS`.
    fn propagate_cargo_env(&mut self, prefix: &str) {
        // Inherit `RUSTFLAGS` by default ...
        self.env(prefix);

        // ... and also handle target-specific env RUSTFLAGS if they're configured.
        let target_specific = format!("CARGO_TARGET_{}_{}", envify(&self.1.triple), prefix);
        self.env(&target_specific);
    }

    fn env(&mut self, env: &str) {
        if cfg!(test) {
            return;
        }
        if let Ok(s) = env::var(env) {
            for part in s.split(' ') {
                self.arg(part);
            }
        }
    }

    fn arg(&mut self, arg: &str) -> &mut Self {
        assert!(
            !arg.contains('\x1f'),
            "rustflag must not contain the ASCII unit separator (\\x1f): {arg:?}"
        );
        if !arg.is_empty() {
            if !self.0.is_empty() {
                self.0.push('\x1f');
            }
            self.0.push_str(arg);
        }
        self
    }

    fn propagate_rustflag_envs(&mut self, build_compiler_stage: u32) {
        self.propagate_cargo_env("RUSTFLAGS");
        if build_compiler_stage != 0 {
            self.env("RUSTFLAGS_NOT_BOOTSTRAP");
        } else {
            self.env("RUSTFLAGS_BOOTSTRAP");
            self.arg("--cfg=bootstrap");
        }
    }
}

/// Picks the environment variable and value to pass a set of [`Rustflags`] to cargo.
///
/// `flags` is the `\x1f`-separated string built by [`Rustflags`]. We prefer the plain,
/// space-separated form (`RUSTFLAGS`/`RUSTDOCFLAGS`) so the command stays readable and
/// copy-pasteable in bootstrap's debug output, and only fall back to the `CARGO_ENCODED_*` form
/// (which keeps the `\x1f` separators) when a flag value contains a space that the plain,
/// whitespace-split form can't represent. See <https://github.com/rust-lang/rust/issues/158749>.
pub(super) fn flags_env(
    plain: &'static str,
    encoded: &'static str,
    flags: &str,
) -> (&'static str, String) {
    // A space can only appear inside a flag value, since the separators are `\x1f`.
    if flags.contains(' ') {
        (encoded, flags.to_string())
    } else {
        (plain, flags.replace('\x1f', " "))
    }
}

/// Flags that are passed to the `rustc` shim binary. These flags will only be applied when
/// compiling host code, i.e. when `--target` is unset.
#[derive(Debug, Default)]
struct HostFlags {
    rustc: Vec<String>,
}

impl HostFlags {
    const SEPARATOR: &'static str = " ";

    /// Adds a host rustc flag.
    fn arg<S: Into<String>>(&mut self, flag: S) {
        let value = flag.into().trim().to_string();
        assert!(!value.contains(Self::SEPARATOR));
        self.rustc.push(value);
    }

    /// Encodes all the flags into a single string.
    fn encode(self) -> String {
        self.rustc.join(Self::SEPARATOR)
    }
}

// Trust: Cargo's profile is the keyed authority for checked engine arithmetic,
// including host units. Refuse later flag overrides rather than hiding an
// enforcement flag in the rustc shim, outside Cargo's freshness key.
fn checked_engine_flags(flags: &str) -> Result<(), String> {
    if flags.split('\x1f').any(|arg| arg.starts_with('@')) {
        return Err("response files are unsupported in compiler/tool flags; pass their flags \
             explicitly so bootstrap can check engine overflow policy"
            .into());
    }
    let mut args = flags.split('\x1f');
    while let Some(arg) = args.next() {
        let option = if matches!(arg, "-C" | "--codegen") {
            args.next()
        } else {
            arg.strip_prefix("-C").or_else(|| arg.strip_prefix("--codegen="))
        };
        if let Some((name, value)) = option.and_then(|option| option.split_once('=')) {
            let name = name.replace('_', "-");
            // Cargo can omit both flags when opt-level=0 implies assertions
            // and assertions imply checks. Later optimization flags invalidate
            // that implication; keep optimization in the resolved profile.
            if name == "opt-level" {
                return Err("compiler/tool optimization must use rust.optimize, not codegen \
                            flag overrides that can disable implicit overflow checks"
                    .into());
            }
            if matches!(name.as_str(), "overflow-checks" | "debug-assertions")
                && matches!(value, "n" | "no" | "off" | "false")
            {
                return Err(format!(
                    "compiler/tool flags cannot disable overflow checks or their \
                     debug-assertions implication: {arg} {name}={value}"
                ));
            }
        }
    }
    Ok(())
}

// Trust: inspect forwarded inline Cargo configuration as TOML, including
// package/build overrides and flag arrays. External config/include resolution
// belongs to Cargo; do not pretend a partial resolver can audit those files.
fn checked_engine_config(value: &toml::Value) -> Result<(), String> {
    if value
        .get("env")
        .and_then(toml::Value::as_table)
        .is_some_and(|env| env.contains_key("RUSTC_HOST_FLAGS"))
    {
        return Err("Cargo configuration cannot set bootstrap-private RUSTC_HOST_FLAGS".into());
    }
    if let Some(table) = value.as_table() {
        for (key, value) in table {
            match key.as_str() {
                "include" => {
                    return Err("Cargo config includes are unsupported for compiler/tools; \
                                pass audited inline settings instead"
                        .into());
                }
                "overflow-checks" | "overflow_checks" if value.as_bool() == Some(false) => {
                    return Err("Cargo configuration cannot disable compiler/tool \
                                overflow checks"
                        .into());
                }
                "rustflags" | "rustdocflags" => {
                    if let Some(flags) = value.as_str() {
                        let flags = flags.split_whitespace().collect::<Vec<_>>().join("\x1f");
                        checked_engine_flags(&flags)?;
                    } else if let Some(flags) = value.as_array() {
                        let flags: Vec<_> = flags.iter().filter_map(toml::Value::as_str).collect();
                        checked_engine_flags(&flags.join("\x1f"))?;
                    }
                }
                _ => {}
            }
            checked_engine_config(value)?;
        }
    }
    Ok(())
}

fn checked_engine_cargo_args(args: &[OsString], cwd: &Path) -> Result<(), String> {
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        let arg = arg.to_string_lossy();
        let setting = if arg == "--config" {
            Some(args.next().ok_or("missing forwarded Cargo --config value")?.to_string_lossy())
        } else {
            arg.strip_prefix("--config=").map(std::borrow::Cow::Borrowed)
        };
        if let Some(setting) = setting {
            // Cargo tries an existing path before parsing inline TOML. Even a
            // filename like `net.offline=true` can therefore hide settings.
            if cwd.join(setting.as_ref()).try_exists().map_err(|error| error.to_string())? {
                return Err("external Cargo config files are unsupported for compiler/tools; \
                            pass audited inline settings instead"
                    .into());
            }
            let value = setting.parse::<toml::Value>().map_err(|_| {
                "compiler/tools require inline TOML for forwarded Cargo --config; \
                 external config files cannot be audited by bootstrap"
                    .to_string()
            })?;
            checked_engine_config(&value)?;
        }
    }
    Ok(())
}

fn is_trust_verifier_unstable_option(option: &str) -> bool {
    // `-Z` option names accept `_` and `-` interchangeably (rustc normalizes
    // before lookup), so the underscore spellings are THE SAME OPTIONS and must
    // be recognized here. Before this normalization `-Ztrust_policy=advisory`
    // in RUSTFLAGS walked past both the self-proof refusal and the suppression
    // check — harmless on an ordinary unit, where the appended off-switch still
    // wins by last-value, but on a unit named by the per-unit `library/` opt-in
    // the shim replaces only the on/off switch, so a policy downgrade in the
    // underscore spelling would have SURVIVED into the one verifying compile:
    // a green that means `advisory` while the lane reads as full verification.
    let name = option.split_once('=').map_or(option, |(name, _)| name).replace('_', "-");
    matches!(name.as_str(), "trust-verify" | "trust-policy") || name.starts_with("trust-verify-")
}

/// [`TRUST_BOOTSTRAP_NO_VERIFY_OPTION`] equality on the option's CANONICAL
/// spelling: `-Z` names accept `_` for `-`, so `trust_verify=off` is the same
/// off-switch and must suppress the default (one off-switch, either spelling)
/// rather than being refused as a verification request.
fn is_bootstrap_no_verify_option(option: &str) -> bool {
    option.replace('_', "-") == TRUST_BOOTSTRAP_NO_VERIFY_OPTION
}

/// Every Trust verifier control in `rustflags`, in order, in both token shapes
/// (`-Zname=value` and the split `-Z name=value`).
///
/// ONE walker on purpose. Bootstrap asks two questions about these flags —
/// "must this invocation be refused as a self-proof claim?" and "does bootstrap's
/// default off-switch still apply?" — and they used to be answered by two
/// separate walkers with two different notions of "a control". That is how the
/// suppression came to admit strictly MORE than the refusal caught (see
/// [`bootstrap_disables_default_trust_verification`]).
fn trust_verifier_controls(rustflags: &str) -> Vec<&str> {
    let mut controls = Vec::new();
    // Trust: split on the UNIT SEPARATOR as well as whitespace.
    //
    // `Rustflags::arg` joins with `\x1f` (it asserts no argument contains one,
    // precisely because that byte is the separator). `split_whitespace` does NOT
    // treat `\x1f` as whitespace — U+001F is not in Unicode's White_Space set —
    // so splitting a `Rustflags` value on whitespace yielded ONE token,
    // `"-Zannotate-moves\x1f--check-cfg=…\x1f-Ztrust-verify=off"`, whose
    // `strip_prefix("-Z")` matches no known option. Every caller therefore saw
    // an EMPTY control list regardless of what was actually in the flags.
    //
    // Two consequences, both measured 2026-08-25 by instrumenting the decision:
    //
    //  * `bootstrap_disables_default_trust_verification` could not see a
    //    `-Ztrust-verify=off` that was already present, so it added a SECOND
    //    copy — observed as `stage=1 present=1 add=true`. A repeated rustflag
    //    forks the cargo unit (rustflags feed `unit_id`, not `c_metadata`),
    //    which built a `std` the sysroot did not contain and killed ~31 of
    //    std's integration tests with `dyld: Library not loaded`, plus the
    //    `core` StableCrateId collision behind `std_detect`.
    //
    //  * `rustflags_request_bootstrap_verification` — the SELF-PROOF REFUSAL —
    //    was equally blind. It exists to refuse a verifier control in
    //    bootstrap's own rustflags, and it could not observe one. Whitespace
    //    input (an env-provided `RUSTFLAGS`) still parsed, which is why this
    //    survived: the tests exercise the whitespace form.
    //
    // Both separators are accepted because both forms genuinely occur: `\x1f`
    // from `Rustflags` itself, spaces from an inherited environment variable.
    let mut tokens =
        rustflags.split(['\u{1f}', ' ', '\t', '\n']).filter(|t| !t.is_empty()).peekable();

    while let Some(token) = tokens.next() {
        let option = match token.strip_prefix("-Z") {
            Some("") => tokens.peek().copied(),
            Some(option) => Some(option),
            None => None,
        };
        if let Some(option) = option
            && is_trust_verifier_unstable_option(option)
        {
            controls.push(option);
        }
    }

    controls
}

fn rustflags_request_bootstrap_verification(rustflags: &str) -> bool {
    trust_verifier_controls(rustflags).iter().any(|option| !is_bootstrap_no_verify_option(option))
}

/// Does bootstrap still owe this invocation its default off-switch?
///
/// FAIL-CLOSED, and deliberately not coupled to the self-proof refusal. Only
/// the EXACT off-switch already being present — the same name+value identity
/// the driver resolves, so either `-`/`_` spelling — suppresses the default;
/// every
/// other verifier control leaves the default in place, so the composed rustflags
/// still end in `-Ztrust-verify=off` (last value wins) and the unit still has an
/// off-switch.
///
/// This used to be "any verifier control at all suppresses the default", which
/// was safe only by coincidence: [`refuse_bootstrap_verification_request`] runs
/// first and aborts on every control except the exact off-switch, so the extra
/// cases were unreachable. The two functions shared no assertion, though —
/// narrowing the refusal (to admit some future authenticated lane, say) would
/// have silently produced units with NO off-switch and verification default-ON.
/// Enforcing the invariant here rather than pinning it to the panic is the
/// choice that survives the panic being narrowed: with the exact-match rule the
/// worst case is a redundant off-switch, never a missing one.
fn bootstrap_disables_default_trust_verification(
    build_compiler_stage: u32,
    rustflags: &str,
) -> bool {
    build_compiler_stage != 0
        && !trust_verifier_controls(rustflags)
            .iter()
            .any(|option| is_bootstrap_no_verify_option(option))
}

pub(super) const TRUST_BOOTSTRAP_NO_VERIFY_FLAG: &str = "-Ztrust-verify=off";

/// [`TRUST_BOOTSTRAP_NO_VERIFY_FLAG`] as it appears after the `-Z` prefix is
/// stripped, i.e. as [`trust_verifier_controls`] yields it. Pinned equal to the
/// flag by `no_verify_option_and_flag_are_the_same_switch`.
const TRUST_BOOTSTRAP_NO_VERIFY_OPTION: &str = "trust-verify=off";

/// Put bootstrap's non-self-proving off-switch in the ONE rustflags lane Cargo
/// will actually read for these units.
///
/// Cargo does not merge rustflags sources; it picks the first that exists, in
/// the order `CARGO_ENCODED_RUSTFLAGS`, `RUSTFLAGS`, `target.<triple>.rustflags`
/// (env form `CARGO_TARGET_<TRIPLE>_RUSTFLAGS`), `build.rustflags`. Bootstrap
/// sets one of the first two for essentially every step (`-Wrust_2018_idioms`
/// alone guarantees it), so the off-switch used to be delivered through a
/// variable Cargo had already decided to ignore — it never reached rustc, and
/// the batteries-on default verified the entire third-party dependency graph.
/// Measured against memchr-2.7.6 with the stage0 seed: target-var only -> the
/// unit gets `-Zno-trust-verify` and builds in 8s; both vars set -> the unit
/// gets bootstrap's `-W` flags and NO verifier control, and dies in the SIMD
/// paths. The scope is unchanged: bootstrap always passes `--target`, so plain
/// `RUSTFLAGS` reaches exactly the target units the target-specific variable
/// was aiming at, and host build-script/proc-macro units keep going through the
/// shim's `TRUST_BOOTSTRAP_SHIM_NO_VERIFY` lane as before.
///
/// Bootstrap's own off-switch already being in `rustflags` — and ONLY that —
/// suppresses this default, so the flag is never duplicated. Any other verifier
/// control has already aborted in `rustflags_request_bootstrap_verification`;
/// if it ever stops aborting, the default still lands and the unit still has an
/// off-switch. See [`bootstrap_disables_default_trust_verification`].
fn apply_bootstrap_trust_verification_default(
    rustflags: &mut Rustflags,
    build_compiler_stage: u32,
) {
    if bootstrap_disables_default_trust_verification(build_compiler_stage, &rustflags.0) {
        rustflags.arg(TRUST_BOOTSTRAP_NO_VERIFY_FLAG);
    }
}

/// The self-proof refusal, as a value so it can be tested without a `Builder`.
///
/// Bootstrap has no authenticated artifact-bound proof session, so a verifier
/// control in bootstrap's OWN rustflags is refused — for **every** [`Mode`],
/// library modes included. That is deliberate and it is not what the per-unit
/// library opt-in below relaxes: rustflags are invocation-wide, so honouring one
/// here would turn the verifier on for every crate in the invocation (std's
/// whole third-party dependency graph included) with no unit named anywhere.
///
/// Returns `None` when nothing in `rustflags` requests verification.
fn bootstrap_verification_request_refusal(mode: Mode, rustflags: &str) -> Option<String> {
    if !rustflags_request_bootstrap_verification(rustflags) {
        return None;
    }

    // The refusal prefix is load-bearing: `docs/SELF_PROOF.md` quotes it.
    // Replacement guidance names the compiled owner, never an evidence wrapper.
    Some(format!(
        "bootstrap compiler verification flags are unsupported without an authenticated \
         artifact-bound bootstrap protocol; use `targo trust verify self --full-verifier` instead \
         (refused for a {mode:?} unit; rustflags {rustflags:?}). To verify an in-tree \
         `library/` unit — which is NOT a self-proof claim — use the per-unit opt-in \
         `{TRUST_BOOTSTRAP_VERIFY_LIBRARY_ENV}=<unit>[,<unit>...]` instead; it is refused for \
         compiler, bootstrap and tool units."
    ))
}

#[track_caller]
fn refuse_bootstrap_verification_request(mode: Mode, rustflags: &str) {
    if let Some(message) = bootstrap_verification_request_refusal(mode, rustflags) {
        panic!("{message}");
    }
}

/// User-facing opt-in: verify these in-tree `library/` units with the already
/// built stage>=1 `trustc`.
///
/// This is category (B) — "an existing compiler verified an ordinary Rust
/// library as an ordinary target unit" — and it is deliberately a different
/// switch from category (A), "bootstrap verified ITSELF", which
/// [`bootstrap_verification_request_refusal`] still refuses outright.
///
/// Unset (the default) nothing changes: every stage>=1 unit keeps
/// [`TRUST_BOOTSTRAP_NO_VERIFY_FLAG`], so a build that verifies nothing today
/// still verifies nothing.
pub(super) const TRUST_BOOTSTRAP_VERIFY_LIBRARY_ENV: &str = "TRUST_BOOTSTRAP_VERIFY_LIBRARY";

/// Bootstrap -> rustc-shim IPC carrying the AUTHORIZED unit list for exactly one
/// cargo invocation.
///
/// Bootstrap removes this from every command it builds and re-adds it only for
/// invocations whose [`Mode`] it authorized, so an ambient value in the caller's
/// environment can never reach a compiler, bootstrap or tool unit.
pub(super) const TRUST_BOOTSTRAP_SHIM_VERIFY_UNITS_ENV: &str = "TRUST_BOOTSTRAP_SHIM_VERIFY_UNITS";

/// The in-tree `library/` units this opt-in may be pointed at.
///
/// An enumerated allowlist, not a directory scan: the whole point of the lane is
/// that the set of things a non-self-proving bootstrap may verify is small,
/// named and reviewable. A name outside it is a hard error rather than a silent
/// no-op — that includes every compiler crate, `bootstrap` itself, every tool,
/// and every third-party crate in std's dependency graph (`compiler_builtins`,
/// `libc`, `hashbrown`, `memchr`, ...), which are compiled by the same
/// `Mode::Std` cargo invocation as `core` and must not be swept in with it.
const TRUST_VERIFIABLE_LIBRARY_UNITS: &[&str] = &[
    "alloc",
    "core",
    "panic_abort",
    "panic_unwind",
    "proc_macro",
    "std",
    "std_detect",
    "test",
    "unwind",
];

fn normalized_library_unit(name: &str) -> String {
    name.trim().replace('-', "_")
}

/// Parse [`TRUST_BOOTSTRAP_VERIFY_LIBRARY_ENV`] into a canonical unit list.
///
/// `Ok(None)` means, and only means, "the variable is not set". Every other
/// degenerate input — empty value, stray comma, non-UTF-8, a name that is not an
/// allowed library unit — is an `Err`, because a control that is silently
/// ignored is indistinguishable from one that worked. Unsetting the variable is
/// the documented way to turn the lane off.
fn parse_trust_verify_library_request(raw: Option<&OsStr>) -> Result<Option<Vec<String>>, String> {
    let Some(raw) = raw else { return Ok(None) };
    let allowed = || TRUST_VERIFIABLE_LIBRARY_UNITS.join(", ");
    let Some(raw) = raw.to_str() else {
        return Err(format!(
            "{TRUST_BOOTSTRAP_VERIFY_LIBRARY_ENV} is not valid UTF-8; unset it to keep \
             verification off, or name library units explicitly (allowed: {})",
            allowed()
        ));
    };

    let mut units: Vec<String> = Vec::new();
    for entry in raw.split(',') {
        let unit = normalized_library_unit(entry);
        if unit.is_empty() {
            return Err(format!(
                "{TRUST_BOOTSTRAP_VERIFY_LIBRARY_ENV}={raw:?} contains an empty unit name; \
                 unset the variable to keep verification off, or name library units \
                 explicitly (allowed: {})",
                allowed()
            ));
        }
        if !TRUST_VERIFIABLE_LIBRARY_UNITS.contains(&unit.as_str()) {
            return Err(format!(
                "{TRUST_BOOTSTRAP_VERIFY_LIBRARY_ENV} names `{unit}`, which is not an in-tree \
                 `library/` unit. This opt-in verifies library units only: compiler, \
                 bootstrap and tool units are refused, because bootstrap has no \
                 authenticated artifact-bound self-proof protocol (use \
                 `targo trust verify self --full-verifier` for bounded compiler-crate \
                 evidence). Allowed: {}",
                allowed()
            ));
        }
        if !units.contains(&unit) {
            units.push(unit);
        }
    }

    Ok(Some(units))
}

/// Which cargo invocations may carry the library-verification opt-in at all.
///
/// [`Mode::Std`] is the only mode whose primary units are `library/` crates.
/// Every other mode compiles the compiler, bootstrap or a tool, and for those
/// the refusal above is the whole answer: an artifact that built itself cannot
/// also be the authority that proved itself.
///
/// `build_compiler_stage != 0` matches the existing off-switch condition: at
/// stage 0 the build compiler is the *seed*, whose vintage is the pin's and not
/// this tree's, so it is never the compiler this lane means by "an already-built
/// stage2 trustc".
fn trust_verify_library_units_authorized(mode: Mode, build_compiler_stage: u32) -> bool {
    build_compiler_stage != 0 && matches!(mode, Mode::Std)
}

fn trust_cg_codegen_is_active(
    build_compiler_stage: u32,
    compiler_default_backend: &CodegenBackendKind,
) -> bool {
    build_compiler_stage != 0 && compiler_default_backend.is_trust_cg()
}

/// Trust: whether a staged compiler's DEFAULT backend is the trust-ir → trust-cg
/// self-host plugin. It shares the builtin adapter's profile constraints (no
/// debuginfo, one codegen unit per crate) but NOT its `-Cpanic=abort`: the
/// plugin lowers real unwinding, and the compiler it self-hosts requires it.
fn trust_ir_cg_codegen_is_active(
    build_compiler_stage: u32,
    compiler_default_backend: &CodegenBackendKind,
) -> bool {
    build_compiler_stage != 0 && compiler_default_backend.is_trust_ir_cg()
}

fn effective_debuginfo_level(
    trust_cg_is_active: bool,
    requested: DebuginfoLevel,
) -> DebuginfoLevel {
    if trust_cg_is_active { DebuginfoLevel::None } else { requested }
}

fn effective_codegen_units(trust_cg_is_active: bool, requested: Option<u32>) -> Option<u32> {
    if trust_cg_is_active { Some(1) } else { requested }
}

fn trust_cg_codegen_flags(trust_cg_is_active: bool, is_test: bool) -> &'static [&'static str] {
    match (trust_cg_is_active, is_test) {
        (false, _) => &[],
        (true, false) => &["-Cpanic=abort"],
        (true, true) => &["-Cpanic=abort", "-Zpanic-abort-tests"],
    }
}

#[derive(Debug)]
pub(crate) struct Cargo {
    command: BootstrapCommand,
    args: Vec<OsString>,
    compiler: Compiler,
    mode: Mode,
    target: TargetSelection,
    rustflags: Rustflags,
    rustdocflags: Rustflags,
    hostflags: HostFlags,
    allow_features: String,
    build_compiler_stage: u32,
    extra_rustflags: Vec<String>,
    profile: Option<&'static str>,
    kind: Kind,
}

impl Cargo {
    /// Calls [`Builder::cargo`] and [`Cargo::configure_linker`] to prepare an invocation of `cargo`
    /// to be run.
    #[track_caller]
    pub(crate) fn new(
        builder: &Builder<'_>,
        compiler: Compiler,
        mode: Mode,
        source_type: SourceType,
        target: TargetSelection,
        cmd_kind: Kind,
    ) -> Cargo {
        Self::new_with_input(
            builder,
            compiler,
            mode,
            source_type,
            target,
            cmd_kind,
            builder.cargo_input(mode),
        )
    }

    // Trust: only the native build-tool producer explicitly selects the seed.
    #[expect(clippy::too_many_arguments)]
    pub(crate) fn new_with_input(
        builder: &Builder<'_>,
        compiler: Compiler,
        mode: Mode,
        source_type: SourceType,
        target: TargetSelection,
        cmd_kind: Kind,
        input: CargoInput,
    ) -> Cargo {
        let mut cargo =
            builder.cargo_with_input(compiler, mode, source_type, target, cmd_kind, input);
        if target.synthetic {
            cargo.arg("-Zjson-target-spec");
        }

        match cmd_kind {
            // No need to configure the target linker for these command types.
            Kind::Clean | Kind::Check | Kind::Format | Kind::Setup => {}
            _ => {
                cargo.configure_linker(builder);
            }
        }

        cargo
    }

    pub(crate) fn release_build(&mut self, release_build: bool) {
        self.profile = if release_build { Some("release") } else { None };
    }

    #[expect(dead_code, reason = "general-purpose, currently unused")]
    pub(crate) fn profile(&mut self, profile: &'static str) {
        self.profile = Some(profile);
    }

    pub(crate) fn compiler(&self) -> Compiler {
        self.compiler
    }

    // Trust: the effective stage, which can differ from the compiler's stage for
    // local rebuilds and explicit seed tool inputs. It is the stage the off-switch
    // default is decided on, so `compile::apply_trust_std_rustflags` reads the same
    // one for the trust-ir producer flags; tests observe it too.
    pub(crate) fn build_compiler_stage(&self) -> u32 {
        self.build_compiler_stage
    }

    pub(crate) fn mode(&self) -> Mode {
        self.mode
    }

    pub(crate) fn into_cmd(self) -> BootstrapCommand {
        self.into()
    }

    pub(crate) fn kind(&self) -> Kind {
        self.kind
    }

    /// Same as [`Cargo::new`] except this one doesn't configure the linker with
    /// [`Cargo::configure_linker`].
    #[track_caller]
    pub(crate) fn new_for_mir_opt_tests(
        builder: &Builder<'_>,
        compiler: Compiler,
        mode: Mode,
        source_type: SourceType,
        target: TargetSelection,
        cmd_kind: Kind,
    ) -> Cargo {
        let mut cargo = builder.cargo(compiler, mode, source_type, target, cmd_kind);
        if target.synthetic {
            cargo.arg("-Zjson-target-spec");
        }
        cargo
    }

    pub(crate) fn rustdocflag(&mut self, arg: &str) -> &mut Cargo {
        self.rustdocflags.arg(arg);
        self
    }

    pub(crate) fn rustflag(&mut self, arg: &str) -> &mut Cargo {
        self.rustflags.arg(arg);
        self
    }

    /// Trust: add a rustflag only if it is not already present.
    ///
    /// WHY THIS EXISTS, because a duplicate flag looks harmless and is not.
    /// Cargo hashes rustflags into a unit's `unit_id` — the `-Cextra-filename`
    /// and the `build/<pkg>/<hash>/` directory — but DELIBERATELY NOT into
    /// `c_metadata`, which becomes `-Cmetadata`. So repeating a flag forks the
    /// unit: a second `std` with the SAME `-Cmetadata` and a different filename
    /// hash.
    ///
    /// Measured 2026-08-25: the release gate's child runs
    /// `bootstrap test --stage 2 --trust-vanilla`, and `--trust-vanilla` pushed
    /// `-Ztrust-verify=off` on top of the copy
    /// `apply_bootstrap_trust_verification_default` already adds for every
    /// stage != 0. The resulting `std` unit hashed to
    /// `libstd-32483c54e2ddf828` while the sysroot held
    /// `libstd-4899ad891801794d` — identical features, profile and target, the
    /// flag list differing by ONE repeated entry — and 28 of std's integration
    /// tests died at `dyld: Library not loaded`, SIGABRT.
    ///
    /// The same repetition also collides `core`, because `StableCrateId` is
    /// hash(name, -Cmetadata, is_exe, cfg_version) and `extra_filename` is not
    /// an input: two `core`s, one id.
    pub(crate) fn rustflag_once(&mut self, arg: &str) -> &mut Cargo {
        if !self.rustflags.0.split('\u{1f}').any(|existing| existing == arg) {
            self.rustflags.arg(arg);
        }
        self
    }

    pub(crate) fn arg(&mut self, arg: impl AsRef<OsStr>) -> &mut Cargo {
        self.args.push(arg.as_ref().into());
        self
    }

    pub(crate) fn args<I, S>(&mut self, args: I) -> &mut Cargo
    where
        I: IntoIterator<Item = S>,
        S: AsRef<OsStr>,
    {
        for arg in args {
            self.arg(arg.as_ref());
        }
        self
    }

    /// Add an env var to the cargo command instance. Note that `RUSTFLAGS`/`RUSTDOCFLAGS` must go
    /// through [`Cargo::rustdocflags`] and [`Cargo::rustflags`] because inconsistent `RUSTFLAGS`
    /// and `RUSTDOCFLAGS` usages will trigger spurious rebuilds.
    pub(crate) fn env(&mut self, key: impl AsRef<OsStr>, value: impl AsRef<OsStr>) -> &mut Cargo {
        assert_ne!(key.as_ref(), "RUSTFLAGS");
        assert_ne!(key.as_ref(), "RUSTDOCFLAGS");
        self.command.env(key.as_ref(), value.as_ref());
        self
    }

    /// Remove a private constructor input instead of forwarding the caller's value.
    pub(crate) fn env_remove(&mut self, key: impl AsRef<OsStr>) -> &mut Cargo {
        assert_ne!(key.as_ref(), "RUSTFLAGS");
        assert_ne!(key.as_ref(), "RUSTDOCFLAGS");
        self.command.env_remove(key.as_ref());
        self
    }

    /// Append a value to an env var of the cargo command instance.
    /// If the variable was unset previously, this is equivalent to [`Cargo::env`].
    /// If the variable was already set, this will append `delimiter` and then `value` to it.
    ///
    /// Note that this only considers the existence of the env. var. configured on this `Cargo`
    /// instance. It does not look at the environment of this process.
    pub(crate) fn append_to_env(
        &mut self,
        key: impl AsRef<OsStr>,
        value: impl AsRef<OsStr>,
        delimiter: impl AsRef<OsStr>,
    ) -> &mut Cargo {
        assert_ne!(key.as_ref(), "RUSTFLAGS");
        assert_ne!(key.as_ref(), "RUSTDOCFLAGS");

        let key = key.as_ref();
        if let Some((_, Some(previous_value))) = self.command.get_envs().find(|(k, _)| *k == key) {
            let mut combined: OsString = previous_value.to_os_string();
            combined.push(delimiter.as_ref());
            combined.push(value.as_ref());
            self.env(key, combined)
        } else {
            self.env(key, value)
        }
    }

    pub(crate) fn add_rustc_lib_path(&mut self, builder: &Builder<'_>) {
        builder.add_rustc_lib_path(self.compiler, &mut self.command);
    }

    // Trust: the active bare_cargo command sets its source working directory before wrapping.
    /// Adds nightly-only features that this invocation is allowed to use.
    ///
    /// By default, all nightly features are allowed. Once this is called, it will be restricted to
    /// the given set.
    pub(crate) fn allow_features(&mut self, features: &str) -> &mut Cargo {
        if !self.allow_features.is_empty() {
            self.allow_features.push(',');
        }
        self.allow_features.push_str(features);
        self
    }

    // FIXME(onur-ozkan): Add coverage to make sure modifications to this function
    // doesn't cause cache invalidations (e.g., #130108).
    fn configure_linker(&mut self, builder: &Builder<'_>) -> &mut Cargo {
        let target = self.target;
        let compiler = self.compiler;

        // Dealing with rpath here is a little special, so let's go into some
        // detail. First off, `-rpath` is a linker option on Unix platforms
        // which adds to the runtime dynamic loader path when looking for
        // dynamic libraries. We use this by default on Unix platforms to ensure
        // that our nightlies behave the same on Windows, that is they work out
        // of the box. This can be disabled by setting `rpath = false` in `[rust]`
        // table of `bootstrap.toml`
        //
        // Ok, so the astute might be wondering "why isn't `-C rpath` used
        // here?" and that is indeed a good question to ask. This codegen
        // option is the compiler's current interface to generating an rpath.
        // Unfortunately it doesn't quite suffice for us. The flag currently
        // takes no value as an argument, so the compiler calculates what it
        // should pass to the linker as `-rpath`. This unfortunately is based on
        // the **compile time** directory structure which when building with
        // Cargo will be very different than the runtime directory structure.
        //
        // All that's a really long winded way of saying that if we use
        // `-Crpath` then the executables generated have the wrong rpath of
        // something like `$ORIGIN/deps` when in fact the way we distribute
        // rustc requires the rpath to be `$ORIGIN/../lib`.
        //
        // So, all in all, to set up the correct rpath we pass the linker
        // argument manually via `-C link-args=-Wl,-rpath,...`. Plus isn't it
        // fun to pass a flag to a tool to pass a flag to pass a flag to a tool
        // to change a flag in a binary?
        // Trust: ToolTarget is the standalone, non-rustc-private tool mode.
        // Its binaries (including trustd) must use the system loader defaults;
        // injecting $ORIGIN/../lib or @loader_path gives mutable sysroot siblings
        // authority and defeats the daemon's empty runtime-closure policy.
        // Compiler/private modes still require their ordinary sysroot rpath.
        if self.mode != Mode::ToolTarget
            && builder.config.rpath_enabled(target)
            && helpers::use_host_linker(target)
        {
            let libdir = builder.sysroot_libdir_relative(compiler).to_str().unwrap();
            let linker =
                builder.config.target_config.get(&target).and_then(|c| c.linker.as_deref());
            append_sysroot_rpath(
                &mut self.rustflags,
                target,
                libdir,
                configured_direct_linker(linker),
            );
        }

        // We need to set host linker flags for compiling build scripts and proc-macros.
        // This is done the same way as the target linker flags below, so cargo won't see
        // any fingerprint difference between host==target versus cross-compiled targets
        // when it comes to those host build artifacts.
        if let Some(host_linker) = builder.linker(compiler.host) {
            let host = envify(&compiler.host.triple);
            self.command.env(format!("CARGO_TARGET_{host}_LINKER"), host_linker);
        }
        for arg in linker_flags(builder, compiler.host, LldThreads::Yes) {
            self.hostflags.arg(&arg);
        }

        if let Some(target_linker) = builder.linker(target) {
            let target = envify(&target.triple);
            self.command.env(format!("CARGO_TARGET_{target}_LINKER"), target_linker);
        }
        // We want to set -Clinker using Cargo, therefore we only call `linker_flags` and not
        // `linker_args` here. Cargo will pass that to both rustc and rustdoc invocations.
        for flag in linker_flags(builder, target, LldThreads::Yes) {
            self.rustflags.arg(&flag);
        }
        for arg in linker_flags(builder, target, LldThreads::Yes) {
            self.rustdocflags.arg(&arg);
        }

        match builder.config.compress_debuginfo(target) {
            CompressDebuginfo::Zlib => {
                // Do not enable Zlib compression on:
                // - Windows, because MSVC/PDB doesn't support it
                // - macOS, because its linker doesn't know the flag
                // - Cygwin, because its linker may not support the flag
                if !self.target.is_windows() && !self.target.is_apple() && !self.target.is_cygwin()
                {
                    // If we link through cc, we need the -Wl prefix.
                    // If we don't, then we must not add it, because the linker wouldn't
                    // understand it.
                    if helpers::use_host_linker(target) {
                        self.rustflags.arg("-Clink-arg=-Wl,--compress-debug-sections=zlib");
                    } else {
                        self.rustflags.arg("-Clink-arg=--compress-debug-sections=zlib");
                    }
                }
            }
            CompressDebuginfo::Off => {}
        }

        // Ignore linker warnings for now. These are complicated to fix and don't affect the build.
        // FIXME: we should really investigate these...
        self.rustflags.arg("-Alinker-messages");

        // Throughout the build Cargo can execute a number of build scripts
        // compiling C/C++ code and we need to pass compilers, archivers, flags, etc
        // obtained previously to those build scripts.
        // Build scripts use either the `cc` crate or `configure/make` so we pass
        // the options through environment variables that are fetched and understood by both.
        //
        // FIXME: the guard against msvc shouldn't need to be here
        if target.is_msvc() {
            if let Some(ref cl) = builder.config.llvm_clang_cl {
                // FIXME: There is a bug in Clang 18 when building for ARM64:
                // https://github.com/llvm/llvm-project/pull/81849. This is
                // fixed in LLVM 19, but can't be backported.
                if !target.starts_with("aarch64") && !target.starts_with("arm64ec") {
                    self.command.env("CC", cl).env("CXX", cl);
                }
            }
        } else {
            let ccache = builder.config.ccache.as_ref();
            let ccacheify = |s: &Path| {
                let ccache = match ccache {
                    Some(ref s) => s,
                    None => return s.display().to_string(),
                };
                // FIXME: the cc-rs crate only recognizes the literal strings
                // `ccache` and `sccache` when doing caching compilations, so we
                // mirror that here. It should probably be fixed upstream to
                // accept a new env var or otherwise work with custom ccache
                // vars.
                match &ccache[..] {
                    "ccache" | "sccache" => format!("{} {}", ccache, s.display()),
                    _ => s.display().to_string(),
                }
            };
            let triple_underscored = target.triple.replace('-', "_");
            let cc = ccacheify(&builder.cc(target));
            self.command.env(format!("CC_{triple_underscored}"), &cc);

            // Compiling C deps, like jemalloc and llvm-wrapper, should be with
            // the same LTO mode as the Rust code they are linked into.
            //
            // Std's C deps, e.g. compiler_builtins, ship inside rlibs that
            // end users consume directly. Building with `-flto` may break
            // non-LLVM linkers or mismatch on bitcode versions. Therefore we
            // must not build std in LTO mode here.
            let lto_cflag = if matches!(self.mode, Mode::Rustc | Mode::ToolRustcPrivate)
                && is_lto_stage(&self.compiler)
                && builder.cc_tool(target).is_like_clang()
                // Exclude aarch64-linux as we can't assume the user has an LTO-capable linker
                // (and these files get distributed in the rustc-dev component).
                // FIXME: this means the argument above about doing this for rustc but not std makes
                // no sense. We distribute rlibs for both, so both need to be linkable by users. I
                // guess we just don't want to risk this for std, but are less worried about
                // breaking rustc-dev.
                && !target.starts_with("aarch64-unknown-linux")
            {
                match builder.config.rust_lto {
                    RustcLto::Thin => Some("-flto=thin"),
                    RustcLto::Fat => Some("-flto=full"),
                    RustcLto::ThinLocal | RustcLto::Off => None,
                }
            } else {
                None
            };

            // Extend `CFLAGS_$TARGET` with our extra flags.
            let env = format!("CFLAGS_{triple_underscored}");
            let mut cflags = builder.cc_unhandled_cflags(target, CLang::C).join(" ");
            if let Some(lto_cflag) = lto_cflag {
                cflags.push(' ');
                cflags.push_str(lto_cflag);
            }
            if let Ok(var) = std::env::var(&env) {
                cflags.push(' ');
                cflags.push_str(&var);
            }
            self.command.env(env, &cflags);

            if let Some(ar) = builder.ar(target) {
                let ranlib = format!("{} s", ar.display());
                self.command
                    .env(format!("AR_{triple_underscored}"), ar)
                    .env(format!("RANLIB_{triple_underscored}"), ranlib);
            }

            if let Ok(cxx) = builder.cxx(target) {
                let cxx = ccacheify(&cxx);
                self.command.env(format!("CXX_{triple_underscored}"), &cxx);

                // Extend `CXXFLAGS_$TARGET` with our extra flags.
                let env = format!("CXXFLAGS_{triple_underscored}");
                let mut cxxflags = builder.cc_unhandled_cflags(target, CLang::Cxx).join(" ");
                if let Some(lto_cflag) = lto_cflag {
                    cxxflags.push(' ');
                    cxxflags.push_str(lto_cflag);
                }
                if let Ok(var) = std::env::var(&env) {
                    cxxflags.push(' ');
                    cxxflags.push_str(&var);
                }
                self.command.env(&env, cxxflags);
            }
        }

        self
    }
}

impl From<Cargo> for BootstrapCommand {
    fn from(mut cargo: Cargo) -> BootstrapCommand {
        if let Some(profile) = cargo.profile {
            cargo.args.insert(0, format!("--profile={profile}").into());
        }

        for arg in &cargo.extra_rustflags {
            cargo.rustflags.arg(arg);
            cargo.rustdocflags.arg(arg);
        }

        // Propagate the envs here at the very end to make sure they override any previously set flags.
        cargo.rustflags.propagate_rustflag_envs(cargo.build_compiler_stage);
        cargo.rustdocflags.propagate_rustflag_envs(cargo.build_compiler_stage);
        cargo.rustdocflags.propagate_cargo_env("RUSTDOCFLAGS");

        if cargo.build_compiler_stage == 0 {
            cargo.rustdocflags.env("RUSTDOCFLAGS_BOOTSTRAP");
            if let Ok(s) = env::var("CARGOFLAGS_BOOTSTRAP") {
                cargo.args(s.split_whitespace());
            }
        } else {
            cargo.rustdocflags.env("RUSTDOCFLAGS_NOT_BOOTSTRAP");
            if let Ok(s) = env::var("CARGOFLAGS_NOT_BOOTSTRAP") {
                cargo.args(s.split_whitespace());
            }
        }

        if let Ok(s) = env::var("CARGOFLAGS") {
            cargo.args(s.split_whitespace());
        }

        // Trust: extras and all supported inherited flag forms have now been
        // folded in. Std retains its separate overflow policy.
        if cargo.mode != Mode::Std {
            checked_engine_flags(&cargo.rustflags.0)
                .and_then(|()| checked_engine_flags(&cargo.rustdocflags.0))
                .and_then(|()| {
                    checked_engine_cargo_args(
                        &cargo.args,
                        cargo.command.get_current_dir().expect("bootstrap sets Cargo's directory"),
                    )
                })
                .unwrap_or_else(|message| panic!("{message}"));
        }

        cargo.command.args(cargo.args);

        // Unset any inherited flag variables (plain and encoded) so cargo uses only the flags
        // bootstrap sets below. Flags from the caller's environment have already been folded into
        // the Rustflags struct via `propagate_cargo_env`. This also matters because we may set the
        // plain form below, which cargo ignores when `CARGO_ENCODED_RUSTFLAGS` is also present.
        cargo.command.env_remove("RUSTFLAGS");
        cargo.command.env_remove("CARGO_ENCODED_RUSTFLAGS");
        cargo.command.env_remove("RUSTDOCFLAGS");
        cargo.command.env_remove("CARGO_ENCODED_RUSTDOCFLAGS");

        // Bootstrap is deliberately not self-proof. It uses Cargo's
        // compatibility identity and gives only its rustc/rustdoc shims this
        // narrow control marker; Stage1+ target units also receive the compiler
        // off-switch explicitly. The bounded self-verification harness is a
        // separate evidence producer.
        //
        // This runs BEFORE the rustflags env is materialized below, because the
        // off-switch has to be part of that payload — see
        // `apply_bootstrap_trust_verification_default` for why any other
        // variable is silently discarded by Cargo.
        if std::env::var_os("TRUST_FLYWHEEL").is_some() {
            panic!(
                "TRUST_FLYWHEEL is retired: bootstrap has no authenticated proof session and cannot claim self-verification; use `targo trust verify self --full-verifier` for bounded compiler-crate evidence"
            );
        }
        // Same rung: a retired name that is still scrubbed in six places but read
        // nowhere. Refuse it here so it cannot be a silent no-op on the x.py path.
        if let Some(message) = retired_trust_bootstrap_shim_target_only_refusal(
            std::env::var_os(RETIRED_TRUST_BOOTSTRAP_SHIM_TARGET_ONLY_ENV).as_deref(),
        ) {
            panic!("{message}");
        }
        refuse_bootstrap_verification_request(cargo.mode, &cargo.rustflags.0);
        cargo.command.env("TRUST_BOOTSTRAP_SHIM_NO_VERIFY", "1");
        // Trust (loud-when-off): the off-switch below is bootstrap's
        // announced, recorded non-self-proving policy — quiet the compiler's
        // once-per-crate vanilla note for every unit this invocation drives.
        cargo.command.env("TRUST_VANILLA_ANNOUNCED", "1");

        // Trust: the per-unit `library/` verification opt-in.
        //
        // Two different claims used to ride the single off-switch below:
        //   (A) "bootstrap verified ITSELF" — circular, no authenticated proof
        //       session. Still blocked, by the refusal above.
        //   (B) "the already-built stage>=1 trustc verified `library/core`, an
        //       ordinary Rust library, as an ordinary target unit" — neither
        //       circular nor a self-proof claim, and blocked today only because
        //       it rode the same switch.
        //
        // (B) is now opted into per unit with `TRUST_BOOTSTRAP_VERIFY_LIBRARY=core[,...]`.
        //
        // The opt-in deliberately does NOT ride rustflags, and the off-switch
        // below is applied exactly as before even when the opt-in is set. A
        // `Mode::Std` invocation compiles std's whole third-party dependency
        // graph alongside `core`; putting `-Ztrust-verify=on` in rustflags would
        // verify all of it — the same batteries-on accident
        // `apply_bootstrap_trust_verification_default` documents. So the
        // invocation-wide default stays OFF and only the AUTHORIZED unit list
        // travels, to the one component that knows which crate it is about to
        // compile: the rustc shim, which flips exactly those `--crate-name`s to
        // `-Ztrust-verify=on` at the driver boundary.
        //
        // Scrub first, unconditionally: the shim channel is bootstrap-internal
        // IPC, so an ambient value inherited from the caller's environment must
        // never reach a unit bootstrap did not authorize.
        cargo.command.env_remove(TRUST_BOOTSTRAP_SHIM_VERIFY_UNITS_ENV);
        let library_verify_units = parse_trust_verify_library_request(
            std::env::var_os(TRUST_BOOTSTRAP_VERIFY_LIBRARY_ENV).as_deref(),
        )
        .unwrap_or_else(|message| panic!("{message}"));
        if let Some(units) = library_verify_units
            && trust_verify_library_units_authorized(cargo.mode, cargo.build_compiler_stage)
        {
            let units = units.join(",");
            // Loud when on, per invocation: the whole build otherwise looks
            // identical to a default one.
            eprintln!(
                "trust: {TRUST_BOOTSTRAP_VERIFY_LIBRARY_ENV} is set — verifying library \
                 unit(s) [{units}] with the stage{stage} compiler. This is not a \
                 self-proof claim: every other unit in this {mode:?} invocation keeps \
                 {TRUST_BOOTSTRAP_NO_VERIFY_FLAG}.",
                stage = cargo.build_compiler_stage,
                mode = cargo.mode,
            );
            cargo.command.env(TRUST_BOOTSTRAP_SHIM_VERIFY_UNITS_ENV, units);
        }

        apply_bootstrap_trust_verification_default(
            &mut cargo.rustflags,
            cargo.build_compiler_stage,
        );

        // Trust: the HOST half uses the marker already set above, at every
        // compiler stage. Cargo omits target rustflags (including a modern
        // seed's RUSTFLAGS_BOOTSTRAP) from explicit-target host dependencies.
        // The marker expresses intent, not driver capability: the shim must
        // admit the concrete snapshot's host capability and use its existing
        // version-invariant environment transport. Raw hostflags could instead
        // hand an old or stock seed a Trust option it cannot parse.
        // The separately authorized per-unit library opt-in takes precedence
        // in the shim. Its authenticated-frontend, real-compile and query guards
        // remain responsible for the exact scope of the marker.

        if !cargo.rustflags.0.is_empty() {
            let (var, value) =
                flags_env("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", &cargo.rustflags.0);
            cargo.command.env(var, value);
        }

        if !cargo.rustdocflags.0.is_empty() {
            let (var, value) =
                flags_env("RUSTDOCFLAGS", "CARGO_ENCODED_RUSTDOCFLAGS", &cargo.rustdocflags.0);
            cargo.command.env(var, value);
        }

        let encoded_hostflags = cargo.hostflags.encode();
        // Trust: this is bootstrap-internal IPC, not a caller override. In
        // particular, an empty internal list must not inherit unchecked flags.
        cargo.command.env_remove("RUSTC_HOST_FLAGS");
        if !encoded_hostflags.is_empty() {
            cargo.command.env("RUSTC_HOST_FLAGS", encoded_hostflags);
        }

        if !cargo.allow_features.is_empty() {
            let mut features = cargo.allow_features.clone();
            if !features.contains("contracts_internals") {
                features.push_str(",contracts_internals,rustc_attrs,register_tool");
            }
            cargo.command.env("RUSTC_ALLOW_FEATURES", features);
        }

        cargo.command
    }
}

// Trust: a private dependency edge, never a configuration/authority override.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CargoInput {
    Seed,
    // Trust: an actual original Full owner executes this control SDK driver
    // in its library. It does not impersonate seed or produced Cargo.
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    OriginalControl,
    CurrentBuildTool,
    // Trust: native compiler units may use the produced Targo's owned test queue.
    CurrentNativeUnitTests,
    // Native artifact-only tools use the current Cargo generation with the
    // actual snapshot's std and flags, independently of local-rebuild detection.
    CurrentBuildToolSnapshotStd,
}

impl CargoInput {
    pub(crate) fn for_original(self, session: &crate::core::session::Session) -> Self {
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        if self == Self::Seed && session.original_compilation().is_some() {
            return Self::OriginalControl;
        }
        let _ = session;
        self
    }

    pub(crate) fn is_original_control(self) -> bool {
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        if self == Self::OriginalControl {
            return true;
        }
        false
    }

    pub(crate) fn uses_snapshot_compiler(self) -> bool {
        matches!(self, Self::Seed | Self::CurrentBuildToolSnapshotStd) || self.is_original_control()
    }
    pub(crate) fn for_mode(mode: Mode) -> Self {
        match mode {
            // Bootstrap utilities remain seed-built prerequisites.
            Mode::ToolBootstrap => Self::Seed,
            _ => Self::CurrentBuildTool,
        }
    }

    fn uses_current_build_tool(self) -> bool {
        matches!(
            self,
            Self::CurrentBuildTool
                | Self::CurrentBuildToolSnapshotStd
                | Self::CurrentNativeUnitTests
        )
    }

    /// Trust: cache formats belong to the selected Cargo generation. Preserve
    /// the actual build mode and flags; this projection is used only for output
    /// paths. The native Cargo producer is a ToolTarget recipe run by the seed,
    /// so it must share the seed prerequisites' domain, not its consumers'.
    pub(crate) fn cache_mode(self, mode: Mode) -> Mode {
        match (self, mode) {
            (Self::Seed, Mode::ToolTarget) => Mode::ToolBootstrap,
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            (Self::OriginalControl, Mode::ToolTarget) => Mode::ToolBootstrap,
            _ => mode,
        }
    }
}

// Trust: what a Cargo command gets of the GNU jobserver Bootstrap inherited
// (BOOTSTRAP-JOBSERVER-PROBE-1).
//
// A FIFO survives Trust std's strip of non-stdio descriptors, so an inherited
// one is forwarded unchanged. A numeric pipe does not, so it is stripped. The
// seed Cargo may predate CARGO_JOBSERVER_HANDOFF (29ebb403de and earlier): with
// no FIFO it gives build scripts a numeric pipe that their compiler probes
// reach closed, and the shim refuses them. So the seed Cargo gets Bootstrap's
// own FIFO. The current Targo hands build scripts a recoverable pipe
// (CARGO_JOBSERVER_HANDOFF), so its inputs keep the strip.
//
// One exception: under an enclosing owner's dispatch (the embedded engine's
// protected scope, the macOS hosted graph) every command is handed that
// owner's transport when it starts, over whatever MAKEFLAGS it carries, so the
// seed Cargo there gets no FIFO of Bootstrap's (`enclosing_owner_transport`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MakeflagsPolicy {
    ForwardInherited,
    Strip,
    #[cfg(unix)]
    SeedFifo,
}

pub(crate) fn makeflags_policy(
    inherited: Option<&std::ffi::OsStr>,
    input: CargoInput,
    enclosing_owner_transport: bool,
) -> MakeflagsPolicy {
    let inherited_fifo = inherited
        .and_then(std::ffi::OsStr::to_str)
        .is_some_and(|flags| flags.contains("--jobserver-auth=fifo:"));
    if inherited_fifo {
        return MakeflagsPolicy::ForwardInherited;
    }
    #[cfg(unix)]
    if input == CargoInput::Seed && !enclosing_owner_transport {
        return MakeflagsPolicy::SeedFifo;
    }
    #[cfg(not(unix))]
    let _ = (input, enclosing_owner_transport);
    MakeflagsPolicy::Strip
}

// Trust: whether this process's commands start under an enclosing owner's
// dispatch, which configures that owner's GNU transport on each one
// (`metadata_scheduler::prepare_producer`, `host_graph::output`). A scope that
// can no longer be upgraded refuses every start, so it counts too.
fn enclosing_owner_transport() -> bool {
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        !matches!(crate::utils::exec::protected_scope(), Ok(None))
            || crate::utils::metadata_scheduler::hosted_graph_active()
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        false
    }
}

// Trust: capabilities belong to the exact executable spelling (including argv0),
// not a process-wide seed answer shared with the newly compiled Cargo.
#[derive(Clone, Debug)]
pub(crate) struct CargoProgram {
    pub(crate) path: PathBuf,
    pub(crate) unverified_lane: bool,
    pub(crate) metadata_flag: &'static str,
}

impl CargoProgram {
    // Trust: compatibility consumers retain their exact existing program and
    // never depend on native probing. Only the explicit native unit input probes.
    fn for_current_input(
        &self,
        exec_ctx: &ExecutionContext,
        native_path: PathBuf,
        input: CargoInput,
    ) -> Self {
        match input {
            CargoInput::CurrentNativeUnitTests => Self::probe_native(exec_ctx, native_path),
            CargoInput::CurrentBuildTool | CargoInput::CurrentBuildToolSnapshotStd => self.clone(),
            _ => unreachable!("prerequisite driver selection is separate from the current tool"),
        }
    }

    // Trust: native test scheduling requires the actual produced Targo spelling,
    // successful branding probe and explicit lane, never a compatibility fallback.
    pub(crate) fn probe_native(exec_ctx: &ExecutionContext, path: PathBuf) -> Self {
        if !exec_ctx.dry_run() {
            let help = command(&path).allow_failure().arg("--help").cached().run_capture(exec_ctx);
            assert!(help.is_success(), "native Targo at {} --help failed", path.display());
        }
        let program = Self::probe(exec_ctx, path);
        assert!(
            exec_ctx.dry_run() || program.unverified_lane,
            "native compiler unit tests require produced Targo branding at {}",
            program.path.display(),
        );
        program
    }

    pub(crate) fn probe(exec_ctx: &ExecutionContext, path: PathBuf) -> Self {
        if exec_ctx.dry_run() {
            return Self { path, unverified_lane: false, metadata_flag: "-Zembed-metadata=no" };
        }
        // These source-owned inputs are immutable during an admitted build.
        // The existing execution cache keys the literal program, arguments and
        // explicit environment; never canonicalize cargo/targo hard-link names.
        let output = command(&path).allow_failure().arg("--help").cached().run_capture(exec_ctx);
        let unverified_lane = output
            .stdout_if_present()
            .into_iter()
            .chain(output.stderr_if_present())
            .any(|text| text.contains("--unverified"));
        let mut probe = command(&path).allow_failure();
        if unverified_lane {
            probe.arg("--unverified");
        }
        let output =
            probe.args(["-Z", "help"]).env("RUSTC_BOOTSTRAP", "1").cached().run_capture(exec_ctx);
        // Trust: stdout from a failed probe grants no metadata capability,
        // including when this execution context delays command failures.
        assert!(
            output.is_success(),
            "Cargo at {} -Z help failed while probing separate-metadata support: {}",
            path.display(),
            output.stderr(),
        );
        // Preserve either help stream while binding the capability to this executable.
        let help = format!("{}\n{}", output.stdout(), output.stderr());
        let metadata_flag = no_embed_metadata_flag_from_help(&help).unwrap_or_else(|| {
            panic!(
                "Cargo at {} supports neither -Zembed-metadata=no nor -Zno-embed-metadata",
                path.display(),
            )
        });
        Self { path, unverified_lane, metadata_flag }
    }
}

// Trust: Cargo renamed `-Zno-embed-metadata` to `-Zembed-metadata=no`
// after the shipped Trust stage0. Both request the same split rlib/rmeta
// artifacts that bootstrap requires. Ask the actual seed rather than deriving
// its capabilities from the compiler's version (the two may be refreshed
// independently), and never silently omit the metadata policy.
fn no_embed_metadata_flag_from_help(help: &str) -> Option<&'static str> {
    let advertises = |name| {
        help.lines().any(|line| {
            let mut words = line.split_whitespace();
            words.next() == Some("-Z") && words.next() == Some(name)
        })
    };
    if advertises("embed-metadata") {
        Some("-Zembed-metadata=no")
    } else if advertises("no-embed-metadata") {
        Some("-Zno-embed-metadata")
    } else {
        None
    }
}

// Trust: whether a compiler whose `-vV` is `version` borrow-checks with Polonius
// unless told otherwise. A Trust compiler (`(trustc ...)` on the first line) of
// release 1.101 or later does: its `trust` channel takes upstream nightly's
// defaults (PERF-SEP26-DEFAULTS), and its `-Zpolonius` knows `off` (1.98 and
// earlier reject `off`; a 1.101 Trust compiler built before that ruling only
// gets a flag it already obeys). A stock beta or stable does not. `-vV`, not
// `-Z help`: in a strict custody context a Trust compiler answers only fixed
// metadata queries (CUSTODY-BOUNDED-QUERY-SPELLINGS-1).
fn compiler_defaults_to_polonius(version: &str) -> bool {
    let trust = version
        .lines()
        .next()
        .is_some_and(|line| line.starts_with("rustc ") && line.contains("(trustc "));
    let at_least_1_101 =
        version.lines().find_map(|line| line.strip_prefix("release: ")).and_then(|release| {
            let mut parts = release.split(['.', '-']);
            let major: u32 = parts.next()?.parse().ok()?;
            let minor: u32 = parts.next()?.parse().ok()?;
            Some((major, minor) >= (1, 101))
        });
    trust && at_least_1_101 == Some(true)
}

impl Builder<'_> {
    pub(crate) fn cargo_input(&self, mode: Mode) -> CargoInput {
        CargoInput::for_mode(mode).for_original(self.sess)
    }

    // Trust: command writers and artifact readers must use the SAME selected
    // Cargo generation. The control library cannot share seed fingerprints.
    pub(crate) fn cargo_stage_out(
        &self,
        compiler: Compiler,
        mode: Mode,
        input: CargoInput,
    ) -> PathBuf {
        let ordinary = self.stage_out(compiler, input.cache_mode(mode));
        if input.is_original_control() {
            ordinary.with_file_name("bootstrap-control-tools")
        } else {
            ordinary
        }
    }

    pub(crate) fn cargo_out_for_input(
        &self,
        compiler: Compiler,
        mode: Mode,
        target: TargetSelection,
        input: CargoInput,
    ) -> PathBuf {
        self.cargo_stage_out(compiler, mode, input)
            .join(target)
            .join(self.cargo_dir(input.cache_mode(mode)))
    }

    // Trust: whether the stage0 compiler borrow-checks with Polonius by default
    // (cached per execution context).
    fn stage0_defaults_to_polonius(&self) -> bool {
        if self.config.dry_run() {
            return false;
        }
        let output = command(&self.initial_rustc)
            .allow_failure()
            .arg("-vV")
            .cached()
            .run_capture(self.config.exec_ctx());
        assert!(
            output.is_success(),
            "stage0 compiler at {} -vV failed while reading its borrow-checker default: {}",
            self.initial_rustc.display(),
            output.stderr(),
        );
        compiler_defaults_to_polonius(&output.stdout())
    }
}

impl Builder<'_> {
    // Trust: Session.initial_cargo continues to name only the pinned seed.
    pub(crate) fn build_cargo_program(&self, input: CargoInput) -> CargoProgram {
        match input {
            CargoInput::Seed => {
                CargoProgram::probe(self.config.exec_ctx(), self.initial_cargo.clone())
            }
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            CargoInput::OriginalControl => {
                CargoProgram::probe(self.config.exec_ctx(), t!(self.sess.original_control_targo()))
            }
            CargoInput::CurrentBuildTool
            | CargoInput::CurrentBuildToolSnapshotStd
            | CargoInput::CurrentNativeUnitTests => {
                let tool = self.ensure(TargoBuildTool::native(self));
                tool.cargo.for_current_input(self.config.exec_ctx(), tool.native_path, input)
            }
        }
    }

    /// Like [`Builder::cargo`], but only passes flags that are valid for all commands.
    #[track_caller]
    pub(crate) fn bare_cargo(
        &self,
        compiler: Compiler,
        mode: Mode,
        target: TargetSelection,
        cmd_kind: Kind,
    ) -> BootstrapCommand {
        let input = self.cargo_input(mode);
        let program = self.build_cargo_program(input);
        self.bare_cargo_with_program(compiler, mode, target, cmd_kind, &program, input)
    }

    fn bare_cargo_with_program(
        &self,
        compiler: Compiler,
        mode: Mode,
        target: TargetSelection,
        cmd_kind: Kind,
        program: &CargoProgram,
        input: CargoInput,
    ) -> BootstrapCommand {
        let mut cargo = match cmd_kind {
            Kind::Clippy => {
                let mut cargo = self.cargo_clippy_cmd(compiler);
                cargo.arg(cmd_kind.as_str());
                cargo
            }
            Kind::MiriSetup => {
                let mut cargo = self.cargo_miri_cmd(compiler);
                cargo.arg("miri").arg("setup");
                cargo
            }
            Kind::MiriTest => {
                let mut cargo = self.cargo_miri_cmd(compiler);
                cargo.arg("miri").arg("test");
                cargo
            }
            _ => {
                let mut cargo = command(&program.path);
                // Targo's two-lane policy: a targo new enough to have it REFUSES a
                // bare `targo build`, because that would mint an artifact carrying
                // no proof claim while looking like it might. Bootstrap builds the
                // compiler and its tooling, which is unverified by definition, so
                // the honest lane is `--unverified` — and saying so explicitly is
                // the whole point of the policy.
                //
                // Probed once rather than assumed, so a seed targo that predates
                // the policy keeps working: passing it an unknown global flag
                // would be a hard error. Costs one `--help` per bootstrap run.
                if program.unverified_lane {
                    cargo.arg("--unverified");
                }
                cargo.arg(cmd_kind.as_str());
                cargo
            }
        };
        // Trust: the native compiler-unit input requires the managed test owner.
        // Normal x.py scrubs ambient Cargo settings; select this existing queue
        // explicitly instead of depending on inherited configuration. Two is the
        // minimum guaranteed queue selector, not an extra CPU grant: its actual
        // concurrency still respects the admitted build-job ceiling.
        if input == CargoInput::CurrentNativeUnitTests {
            assert_eq!(cmd_kind, Kind::Test);
            cargo.args(["--config", "build.test-jobs=2", "--config", "build.test-weight=1"]);
        }
        // Trust: cargo-clippy/miri and nested build scripts must use the same
        // selected executable and compatibility identity as this invocation.
        cargo.env("CARGO", &program.path);

        // Optionally suppress cargo output.
        if self.config.quiet {
            cargo.arg("--quiet");
        }

        // Run cargo from the source root so it can find .cargo/config.
        // This matters when using vendoring and the working directory is outside the repository.
        cargo.current_dir(&self.src);

        let out_dir = self.cargo_stage_out(compiler, mode, input);
        cargo.env("CARGO_TARGET_DIR", &out_dir);

        // Bootstrap makes a lot of assumptions about the artifacts produced in the target
        // directory. If users override the "build directory" using `build-dir`
        // (https://doc.rust-lang.org/nightly/cargo/reference/unstable.html#build-dir), then
        // bootstrap couldn't find these artifacts. So we forcefully override that option to our
        // target directory here.
        // In the future, we could attempt to read the build-dir location from Cargo and actually
        // respect it.
        cargo.env("CARGO_BUILD_BUILD_DIR", &out_dir);

        // Found with `rg "init_env_logger\("`. If anyone uses `init_env_logger`
        // from out of tree it shouldn't matter, since x.py is only used for
        // building in-tree.
        let color_logs = ["RUSTDOC_LOG_COLOR", "RUSTC_LOG_COLOR", "RUST_LOG_COLOR"];
        match self.sess.config.color {
            Color::Always => {
                cargo.arg("--color=always");
                for log in &color_logs {
                    cargo.env(log, "always");
                }
            }
            Color::Never => {
                cargo.arg("--color=never");
                for log in &color_logs {
                    cargo.env(log, "never");
                }
            }
            Color::Auto => {} // nothing to do
        }

        if cmd_kind != Kind::Install {
            cargo.arg("--target").arg(target.rustc_target_arg());
        } else {
            assert_eq!(target, compiler.host);
        }

        // Bootstrap only supports modern FIFO jobservers. Older pipe-based jobservers can run into
        // "invalid file descriptor" errors, as the jobserver file descriptors are not inherited by
        // scripts like bootstrap.py, while the environment variable is propagated. So, we pass
        // MAKEFLAGS only if we detect a FIFO jobserver, otherwise we clear it.
        // Trust: and a seed Cargo that inherits none gets Bootstrap's own FIFO
        // (BOOTSTRAP-JOBSERVER-PROBE-1, `makeflags_policy`).
        self.apply_makeflags_policy(&mut cargo, env::var_os("MAKEFLAGS").as_deref(), input);

        cargo
    }

    // Trust: one decision per Cargo command, from the MAKEFLAGS Bootstrap inherited.
    pub(crate) fn apply_makeflags_policy(
        &self,
        cargo: &mut BootstrapCommand,
        inherited: Option<&std::ffi::OsStr>,
        input: CargoInput,
    ) {
        match makeflags_policy(inherited, input, enclosing_owner_transport()) {
            MakeflagsPolicy::ForwardInherited => {}
            MakeflagsPolicy::Strip => {
                cargo.env_remove("MAKEFLAGS");
                cargo.env_remove("MFLAGS");
            }
            #[cfg(unix)]
            MakeflagsPolicy::SeedFifo => self.seed_jobserver().configure(cargo),
        }
    }

    // Trust: this builder's seed jobserver, made on first use. A dry run makes
    // one too: a command marked to run in a dry run still needs it. Stale
    // servers are removed only by a build that holds the build lock.
    #[cfg(unix)]
    fn seed_jobserver(&self) -> &crate::utils::seed_jobserver::SeedJobserver {
        self.seed_jobserver.get_or_init(|| {
            let parent = self.tempdir();
            let remove_stale = !self.config.dry_run() && !self.config.bypass_bootstrap_lock;
            crate::utils::seed_jobserver::SeedJobserver::for_build(
                &parent,
                self.jobs(),
                remove_stale,
            )
            .unwrap_or_else(|error| {
                panic!(
                    "cannot create the seed Cargo's FIFO jobserver under {}: {error}",
                    parent.display()
                )
            })
        })
    }

    /// This will create a [`BootstrapCommand`] that represents a pending execution of cargo. This
    /// cargo will be configured to use `compiler` as the actual rustc compiler, its output will be
    /// scoped by `mode`'s output directory, it will pass the `--target` flag for the specified
    /// `target`, and will be executing the Cargo command `cmd`. `cmd` can be `miri-cmd` for
    /// commands to be run with Miri.
    #[track_caller]
    fn cargo(
        &self,
        compiler: Compiler,
        mode: Mode,
        source_type: SourceType,
        target: TargetSelection,
        cmd_kind: Kind,
    ) -> Cargo {
        self.cargo_with_input(compiler, mode, source_type, target, cmd_kind, self.cargo_input(mode))
    }

    // Trust: configure one selected program once for both invocation and flags.
    #[expect(clippy::too_many_arguments)]
    fn cargo_with_input(
        &self,
        compiler: Compiler,
        mode: Mode,
        source_type: SourceType,
        target: TargetSelection,
        cmd_kind: Kind,
        input: CargoInput,
    ) -> Cargo {
        let program = self.build_cargo_program(input);
        let mut cargo =
            self.bare_cargo_with_program(compiler, mode, target, cmd_kind, &program, input);
        let out_dir = self.cargo_stage_out(compiler, mode, input);

        let mut hostflags = HostFlags::default();

        // Trust: the stage0 Cargo's experimental layout adds every unit's
        // package/hash directory to the dynamic-library search path. Large
        // compiler and rustc-private tool graphs exceed Linux's per-environment
        // string limit before rustc can start (E2BIG). The traditional layout
        // keeps this search path bounded by using shared `deps` directories,
        // and also preserves compiler tests' runtime lookup of rustc_driver.
        // Fine-grain locking implicitly re-enables the experimental layout,
        // so both controls must agree until stage0 supports bounded unit paths.
        cargo.env("CARGO_UNSTABLE_BUILD_DIR_NEW_LAYOUT", "false");
        cargo.env("CARGO_UNSTABLE_FINE_GRAIN_LOCKING", "false");

        // Codegen backends are not yet tracked by -Zbinary-dep-depinfo,
        // so we need to explicitly clear out if they've been updated.
        for backend in self.codegen_backends(compiler) {
            build_stamp::clear_if_dirty(self, &out_dir, &backend);
        }

        if self.config.cmd.timings() {
            cargo.arg("--timings");
        }

        if cmd_kind == Kind::Doc {
            // Will be stabilized soon -> let's dogfood it.
            // No effect on doc output but massive doc-generation time improvements.
            cargo.arg("-Zrustdoc-mergeable-info");

            // FIXME: remove this directory clearing here, and do it explicitly in individua doc
            // steps, to reduce dependency on implicit doc output paths.
            let my_out = match mode {
                // This is the intended out directory for compiler documentation.
                Mode::Rustc | Mode::ToolRustcPrivate | Mode::ToolBootstrap | Mode::ToolTarget => {
                    self.compiler_doc_out(target)
                }
                Mode::Std => {
                    if self.config.cmd.json() {
                        out_dir.join(target).join("json-doc")
                    } else {
                        out_dir.join(target).join("doc")
                    }
                }
                _ => panic!("doc mode {mode:?} not expected"),
            };
            let rustdoc = self.rustdoc_for_compiler(compiler);
            build_stamp::clear_if_dirty(self, &my_out, &rustdoc);
        }

        let profile_var = |name: &str| cargo_profile_var(name, &self.config, mode);

        // See comment in rustc_llvm/build.rs for why this is necessary, largely llvm-config
        // needs to not accidentally link to libLLVM in stage0/lib.
        cargo.env("REAL_LIBRARY_PATH_VAR", helpers::dylib_path_var());
        if let Some(e) = env::var_os(helpers::dylib_path_var()) {
            cargo.env("REAL_LIBRARY_PATH", e);
        }

        // Forward `./x fix --allow-dirty` from bootstrap to cargo.
        if matches!(cmd_kind, Kind::Fix)
            && let Subcommand::Fix { allow_dirty } = self.config.cmd
            && allow_dirty
        {
            cargo.arg("--allow-dirty");
        }

        // Trust: exact native artifact roles use the raw snapshot for stage,
        // flags and shim IPC as well as std, even under auto local-rebuild.
        // Their Cargo generation remains the independently selected input.
        let snapshot_tool = input.uses_snapshot_compiler()
            && mode == Mode::ToolTarget
            && compiler.is_snapshot(self);
        let build_compiler_stage = if compiler.stage == 0 && self.local_rebuild && !snapshot_tool {
            // Assume the local-rebuild rustc already has stage1 features.
            1
        } else {
            compiler.stage
        };
        let trust_cg_is_active = trust_cg_codegen_is_active(
            build_compiler_stage,
            // A staged compiler's default backend is fixed when that compiler
            // is built for its host. `target` is only the artifact target and
            // may have a different target-specific bootstrap override.
            self.config.default_codegen_backend(compiler.host),
        );
        let trust_ir_cg_is_active = trust_ir_cg_codegen_is_active(
            build_compiler_stage,
            self.config.default_codegen_backend(compiler.host),
        );
        // Profile constraints shared by both narrow Trust backends.
        let narrow_trust_backend_is_active = trust_cg_is_active || trust_ir_cg_is_active;

        // We synthetically interpret a stage0 compiler used to build tools as a
        // "raw" compiler in that it's the exact snapshot we download. For things like
        // ToolRustcPrivate, we would have to use the artificial stage0-sysroot compiler instead.
        let use_snapshot =
            mode == Mode::ToolBootstrap || (mode == Mode::ToolTarget && build_compiler_stage == 0);
        assert!(!use_snapshot || build_compiler_stage == 0 || self.local_rebuild);

        let sysroot = if use_snapshot {
            self.rustc_snapshot_sysroot().to_path_buf()
        } else {
            self.sysroot(compiler)
        };
        let libdir = self.rustc_libdir(compiler);

        let sysroot_str = sysroot.as_os_str().to_str().expect("sysroot should be UTF-8");
        if self.is_verbose() && !matches!(self.config.get_dry_run(), DryRun::SelfCheck) {
            println!("using sysroot {sysroot_str}");
        }

        let mut rustflags = Rustflags::new(target);

        if cmd_kind == Kind::Clippy {
            // clippy overwrites sysroot if we pass it to cargo.
            // Pass it directly to clippy instead.
            // NOTE: this can't be fixed in clippy because we explicitly don't set `RUSTC`,
            // so it has no way of knowing the sysroot.
            rustflags.arg("--sysroot");
            rustflags.arg(sysroot_str);
        }

        // By default, windows-rs depends on a native library that doesn't get copied into the
        // sysroot. Passing this cfg enables raw-dylib support instead, which makes the native
        // library unnecessary. This can be removed when windows-rs enables raw-dylib
        // unconditionally.
        if let Mode::Rustc | Mode::ToolRustcPrivate | Mode::ToolBootstrap | Mode::ToolTarget = mode
        {
            rustflags.arg("--cfg=windows_raw_dylib");
        }

        // When unset, follow the default of the compiler flag - the compiler, tools and std use v0
        if let Some(usm) = self.config.rust_new_symbol_mangling {
            rustflags.arg(if usm {
                "-Csymbol-mangling-version=v0"
            } else {
                "-Csymbol-mangling-version=legacy"
            });
        }

        // Always enable move/copy annotations for profiler visibility (non-stage0 only).
        // Note that -Zannotate-moves is only effective with debugging info enabled.
        if build_compiler_stage >= 1 {
            if let Some(limit) = self.config.rust_annotate_moves_size_limit {
                rustflags.arg(&format!("-Zannotate-moves={limit}"));
            } else {
                rustflags.arg("-Zannotate-moves");
            }
        }

        // FIXME: the following components don't build with `-Zrandomize-layout` yet:
        // - rust-analyzer, due to the rowan crate
        // so we exclude an entire category of steps here due to lack of fine-grained control over
        // rustflags.
        if self.config.rust_randomize_layout && mode != Mode::ToolRustcPrivate {
            rustflags.arg("-Zrandomize-layout");
        }

        // Enable compile-time checking of `cfg` names, values and Cargo `features`.
        //
        // Note: `std`, `alloc` and `core` imports some dependencies by #[path] (like
        // backtrace, core_simd, std_float, ...), those dependencies have their own
        // features but cargo isn't involved in the #[path] process and so cannot pass the
        // complete list of features, so for that reason we don't enable checking of
        // features for std crates.
        if mode == Mode::Std {
            rustflags.arg("--check-cfg=cfg(feature,values(any()))");
        }

        // Add extra cfg not defined in/by rustc
        //
        // Note: Although it would seems that "-Zunstable-options" to `rustflags` is useless as
        // cargo would implicitly add it, it was discover that sometimes bootstrap only use
        // `rustflags` without `cargo` making it required.
        rustflags.arg("-Zunstable-options");

        // Explicit configuration retains its existing argv, including config0.
        // A seed Cargo route has no Targo frontend planner. Publish stable local
        // potential; the concrete shim alone decides seed/off/query eligibility
        // and requires an actual inherited GNU scheduler before using it.
        cargo.env_remove(BOOTSTRAP_FRONTEND_CEILING_ENV);
        if let Some(threads) = self.config.rust_parallel_frontend_threads {
            rustflags.arg(&format!("-Zthreads={threads}"));
        } else if let Some(ceiling) = bootstrap_seed_frontend_ceiling(
            self.config.rust_parallel_frontend_threads,
            std::thread::available_parallelism().ok().map(std::num::NonZeroUsize::get),
        ) {
            cargo.env(BOOTSTRAP_FRONTEND_CEILING_ENV, ceiling.to_string());
        }

        for (restricted_mode, name, values) in EXTRA_CHECK_CFGS {
            if restricted_mode.is_none() || *restricted_mode == Some(mode) {
                rustflags.arg(&check_cfg_arg(name, *values));

                if *name == "bootstrap" {
                    // Cargo doesn't pass RUSTFLAGS to proc_macros:
                    // https://github.com/rust-lang/cargo/issues/4423
                    // Thus, if we are on stage 0, we explicitly set `--cfg=bootstrap`.
                    // We also declare that the flag is expected, which we need to do to not
                    // get warnings about it being unexpected.
                    hostflags.arg(check_cfg_arg(name, *values));
                }
            }
        }

        // FIXME(rust-lang/cargo#5754) we shouldn't be using special command arguments
        // to the host invocation here, but rather Cargo should know what flags to pass rustc
        // itself.
        if build_compiler_stage == 0 {
            hostflags.arg("--cfg=bootstrap");
        }

        // FIXME: It might be better to use the same value for both `RUSTFLAGS` and `RUSTDOCFLAGS`,
        // but this breaks CI. At the very least, stage0 `rustdoc` needs `--cfg bootstrap`. See
        // #71458.
        let mut rustdocflags = rustflags.clone();

        // Trust: D12's double compile replaces the stage0 compiler with a stock
        // oracle, whose borrow checker is NLL. A Trust stage0 defaults to Polonius
        // alpha (the `trust` channel; DECISION_QUEUE.md PERF-SEP26-DEFAULTS) and
        // accepts programs NLL rejects, so without this such code builds here and
        // first fails at the cut. A stock stage0 already borrow-checks with NLL
        // (and an old one rejects `-Zpolonius=off`), so it gets nothing.
        // Std is outside it: the double compile builds std with stage 1, never with
        // the oracle.
        if compiler.stage == 0 && mode != Mode::Std && self.stage0_defaults_to_polonius() {
            rustflags.arg("-Zpolonius=off");
            hostflags.arg("-Zpolonius=off");
        }

        match mode {
            Mode::Std | Mode::ToolBootstrap | Mode::ToolStd | Mode::ToolTarget => {}
            Mode::Rustc | Mode::Codegen | Mode::ToolRustcPrivate => {
                // Build proc macros both for the host and the target unless proc-macros are not
                // supported by the target.
                if target != compiler.host && cmd_kind != Kind::Check {
                    let error = self
                        .rustc_cmd(compiler)
                        .arg("--target")
                        .arg(target.rustc_target_arg())
                        // FIXME(#152709): -Zunstable-options is to handle JSON targets.
                        // Remove when JSON targets are stabilized.
                        .arg("-Zunstable-options")
                        .env("RUSTC_BOOTSTRAP", "1")
                        .arg("--print=file-names")
                        .arg("--crate-type=proc-macro")
                        .arg("-")
                        .stdin(std::process::Stdio::null())
                        .run_capture(self)
                        .stderr();

                    let not_supported = error
                        .lines()
                        .any(|line| line.contains("unsupported crate type `proc-macro`"));
                    if !not_supported {
                        cargo.arg("-Zdual-proc-macros");
                        rustflags.arg("-Zdual-proc-macros");
                    }
                }
            }
        }

        // This tells Cargo (and in turn, rustc) to output more complete
        // dependency information.  Most importantly for bootstrap, this
        // includes sysroot artifacts, like libstd, which means that we don't
        // need to track those in bootstrap (an error prone process!). This
        // feature is currently unstable as there may be some bugs and such, but
        // it represents a big improvement in bootstrap's reliability on
        // rebuilds, so we're using it here.
        //
        // For some additional context, see #63470 (the PR originally adding
        // this), as well as #63012 which is the tracking issue for this
        // feature on the rustc side.
        cargo.arg("-Zbinary-dep-depinfo");
        let allow_features = match mode {
            Mode::ToolBootstrap | Mode::ToolStd | Mode::ToolTarget => {
                // Restrict the allowed features so we don't depend on nightly
                // accidentally.
                //
                // binary-dep-depinfo is used by bootstrap itself for all
                // compilations.
                //
                // Lots of tools depend on proc_macro2 and proc-macro-error.
                // Those have build scripts which assume nightly features are
                // available if the `rustc` version is "nighty" or "dev". See
                // bin/rustc.rs for why that is a problem. Instead of labeling
                // those features for each individual tool that needs them,
                // just blanket allow them here.
                //
                // If this is ever removed, be sure to add something else in
                // its place to keep the restrictions in place (or make a way
                // to unset RUSTC_BOOTSTRAP).
                "binary-dep-depinfo,proc_macro_span,proc_macro_span_shrink,proc_macro_diagnostic"
                    .to_string()
            }
            Mode::Std | Mode::Rustc | Mode::Codegen | Mode::ToolRustcPrivate => String::new(),
        };

        cargo.arg("-j").arg(self.jobs().to_string());

        // Make cargo emit diagnostics relative to the rustc src dir.
        cargo.arg(format!("-Zroot-dir={}", self.src.display()));

        // Trust: in-tree Targo records paths under this tree's roots (its sources and its
        // git directory) as tokens, so that a stage 1 cloned into another worktree
        // (`utils::trust_stage1_seed`, EW-9) is checked against that worktree's files.
        // The seed Cargo has no such flag.
        if input.uses_current_build_tool()
            && let Some(roots) = crate::utils::trust_stage1_seed::relocation_roots(&self.src)
        {
            cargo.arg(format!("-Ztrust-relocation-roots={roots}"));
        }
        // Trust: and reads the times a seed carried from the donor for the inputs of the
        // units it cloned (EW-9), only in the target directories it cloned.
        if input.uses_current_build_tool()
            && let Some(table) = crate::utils::trust_stage1_seed::carried_times(&out_dir)
        {
            cargo.arg(format!("-Ztrust-carried-times={}", table.display()));
        }

        if self.config.compile_time_deps {
            // Build only build scripts and proc-macros for rust-analyzer when requested.
            cargo.arg("-Zunstable-options");
            cargo.arg("--compile-time-deps");
        }

        // FIXME: Temporary fix for https://github.com/rust-lang/cargo/issues/3005
        // Force cargo to output binaries with disambiguating hashes in the name
        let mut metadata = if compiler.stage == 0 {
            // Treat stage0 like a special channel, whether it's a normal prior-
            // release rustc or a local rebuild with the same version, so we
            // never mix these libraries by accident.
            "bootstrap".to_string()
        } else {
            self.config.channel.to_string()
        };
        // We want to make sure that none of the dependencies between
        // std/test/rustc unify with one another. This is done for weird linkage
        // reasons but the gist of the problem is that if librustc, libtest, and
        // libstd all depend on libc from crates.io (which they actually do) we
        // want to make sure they all get distinct versions. Things get really
        // weird if we try to unify all these dependencies right now, namely
        // around how many times the library is linked in dynamic libraries and
        // such. If rustc were a static executable or if we didn't ship dylibs
        // this wouldn't be a problem, but we do, so it is. This is in general
        // just here to make sure things build right. If you can remove this and
        // things still build right, please do!
        match mode {
            Mode::Std => metadata.push_str("std"),
            // When we're building rustc tools, they're built with a search path
            // that contains things built during the rustc build. For example,
            // bitflags is built during the rustc build, and is a dependency of
            // rustdoc as well. We're building rustdoc in a different target
            // directory, though, which means that Cargo will rebuild the
            // dependency. When we go on to build rustdoc, we'll look for
            // bitflags, and find two different copies: one built during the
            // rustc step and one that we just built. This isn't always a
            // problem, somehow -- not really clear why -- but we know that this
            // fixes things.
            Mode::ToolRustcPrivate => metadata.push_str("tool-rustc"),
            // Same for codegen backends.
            Mode::Codegen => metadata.push_str("codegen"),
            // Trust: pin the compiler crates' -Cmetadata the same way Std/Codegen
            // are pinned. Without this, Mode::Rustc fell into the `_ => {}` arm and
            // received NO mode-specific suffix, so its StableCrateId/-Cmetadata
            // disambiguator was derived solely from <channel><version> and could
            // drift run-to-run on the driver crates (rustc_driver_impl,
            // rustc_interface, rustc_mir_transform + the transitive trust_*/ay_*
            // deps). That drift made bin/trustc and librustc_driver fail to
            // reproduce byte-identically across independent rebuilds. Pinning it
            // here gives __CARGO_DEFAULT_LIB_METADATA = <channel>rustc<version>,
            // which cargo propagates across the whole Mode::Rustc invocation
            // (including the transitive workspace/patch deps). This is the
            // whole-stage2 determinism PREREQUISITE for DDC (gap 2 / Thompson).
            Mode::Rustc => metadata.push_str("rustc"),
            _ => {}
        }
        // `rustc_driver`'s version number is always `0.0.0`, which can cause linker search path
        // problems on side-by-side installs because we don't include the version number of the
        // `rustc_driver` being built. This can cause builds of different version numbers to produce
        // `librustc_driver*.so` artifacts that end up with identical filename hashes.
        metadata.push_str(&self.version);

        cargo.env("__CARGO_DEFAULT_LIB_METADATA", &metadata);

        if cmd_kind == Kind::Clippy {
            rustflags.arg("-Zforce-unstable-if-unmarked");
        }

        rustflags.arg("-Zmacro-backtrace");

        // Clear the output directory if the real rustc we're using has changed;
        // Cargo cannot detect this as it thinks rustc is bootstrap/debug/rustc.
        //
        // Avoid doing this during dry run as that usually means the relevant
        // compiler is not yet linked/copied properly.
        //
        // Only clear out the directory if we're running Cargo on std; otherwise, we
        // should let Cargo take care of things for us (via depdep info)
        // Trust: `Kind::Test` must clear too. The reasoning above justifies only the `Mode::Std`
        // half -- cargo cannot see that the real rustc changed, because it thinks rustc is
        // bootstrap/debug/rustc. Restricting the clear to `Kind::Build` leaves
        // `build/<host>/stage2-std` NEVER cleared: stage-2 std is UPLIFTED from stage 1
        // (`Std::should_be_uplifted_from_stage_1`), so no `Mode::Std` + `Kind::Build` cargo is
        // ever constructed for that directory -- while `x.py test --stage 2` DOES build units
        // into it. Trust feels this far harder than upstream because CFG_VERSION embeds the git
        // short sha, so every commit changes compiler identity and invalidates those artifacts.
        //
        // Measured 2026-08-24: `stage1-std/.stamp` exists, `stage2-std/.stamp` did not exist at
        // all, and the release gate's log carried 16x `E0514: found crate 'core' compiled by an
        // incompatible version of rustc` with `cannot resolve a prelude import` on the next line
        // -- which was the entire "missing prelude" symptom.
        //
        // When --keep-stage[-std] is passed, two things can happen:
        // - Either this function is not invoked on `std` at all, because the corresponding Std step
        //   checks the flag and doesn't invoke Cargo for std at all.
        // - This function is invoked, in which case it will (most likely) do a no-op stdlib
        //   rebuild.
        //
        // In the second situation, we must ensure that we will not clear the standard library
        // output directory, otherwise --keep-stage[-std] will of course break.
        // Note that the compiler stage corresponds to the standard library stage.
        let keep_previously_built_std = self.config.keep_stage.contains(&compiler.stage)
            || self.config.keep_stage_std.contains(&compiler.stage);
        if !self.config.dry_run()
            && std_out_dir_needs_clear(mode, cmd_kind)
            && !keep_previously_built_std
        {
            // Trust: rustc can be a stable thin launcher while its loaded
            // librustc_driver changes. Cargo no longer persists its `-vV` answer
            // (CARGO_CACHE_RUSTC_INFO below), so a changed version string rebuilds
            // every domain; this clear additionally ties std to the runtime's bytes,
            // which can change while the version string does not.
            let identity = std_compiler_runtime_identity(self, compiler);
            if t!(build_stamp::clear_if_identity_changed(&out_dir, &identity)) {
                self.do_if_verbose(|| {
                    println!("Cleared `{}` for the selected compiler runtime", out_dir.display());
                });
            }
        }

        let rustdoc_path = match cmd_kind {
            Kind::Doc => self.rustdoc_for_compiler(compiler),
            Kind::Test | Kind::MiriTest if self.test_target.runs_doctests() => {
                self.rustdoc_for_compiler(compiler)
            }
            _ => PathBuf::from("/path/to/nowhere/rustdoc/not/required"),
        };

        // Customize the compiler we're running. Specify the compiler to cargo
        // as our shim and then pass it some various options used to configure
        // how the actual compiler itself is called.
        //
        // These variables are primarily all read by
        // src/bootstrap/bin/{rustc.rs,rustdoc.rs}
        cargo
            .env("RUSTC_REAL", self.rustc(compiler))
            .env("RUSTC_STAGE", build_compiler_stage.to_string())
            .env("RUSTC_SYSROOT", sysroot)
            .env("RUSTC_LIBDIR", &libdir)
            .env("RUSTDOC_LIBDIR", libdir)
            .env("RUSTDOC", self.bootstrap_out.join("rustdoc"))
            .env("RUSTDOC_REAL", rustdoc_path);

        if self.config.rust_break_on_ice {
            cargo.env("RUSTC_BREAK_ON_ICE", "1");
        }

        // Set RUSTC_WRAPPER to the bootstrap shim, which switches between beta and in-tree
        // sysroot depending on whether we're building build scripts.
        // NOTE: we intentionally use RUSTC_WRAPPER so that we can support clippy - RUSTC is not
        // respected by clippy-driver; RUSTC_WRAPPER happens earlier, before clippy runs.
        cargo.env("RUSTC_WRAPPER", self.bootstrap_out.join("rustc"));
        // NOTE: we also need to set RUSTC so cargo can run `rustc -vV`; apparently that ignores RUSTC_WRAPPER >:(
        cargo.env("RUSTC", self.bootstrap_out.join("rustc"));
        // Trust: RUSTC is this shim, never the compiler it runs (RUSTC_REAL, or RUSTC_SNAPSHOT
        // for host units, `bin/rustc.rs`). Cargo persists its compiler queries in
        // `<build-dir>/.rustc_info.json` (`-vV` and the target-info probes, failed answers
        // included) and reuses them while RUSTC and RUSTC_WRAPPER keep their path, size and
        // times (`rustc_fingerprint`). A driver rebuilt behind the unchanged shim was therefore
        // answered with the previous driver's `-vV`; every unit fingerprint (whose `rustc` field
        // is that text) still matched, so units the old driver built were kept, and std's
        // consumers failed E0514. The std runtime-identity clear below covered std Build/Test
        // only, never keep-stage runs, std Check/Doc/Clippy or any other domain. Asking the
        // compiler once per Cargo invocation closes it for all of them; both the pinned seed
        // Cargo and the current one honor this variable. (TG16, docs/DECISION_QUEUE.md.)
        cargo.env("CARGO_CACHE_RUSTC_INFO", "0");

        // Someone might have set some previous rustc wrapper (e.g.
        // sccache) before bootstrap overrode it. Respect that variable.
        if let Some(existing_wrapper) = env::var_os("RUSTC_WRAPPER") {
            cargo.env("RUSTC_WRAPPER_REAL", existing_wrapper);
        }

        // If this is for `miri-test`, prepare the sysroots.
        if cmd_kind == Kind::MiriTest {
            self.std(compiler, compiler.host);
            let host_sysroot = self.sysroot(compiler);
            let miri_sysroot = test::Miri::build_miri_sysroot(self, compiler, target);
            cargo.env("MIRI_SYSROOT", &miri_sysroot);
            cargo.env("MIRI_HOST_SYSROOT", &host_sysroot);
        }

        cargo.env(profile_var("STRIP"), self.config.rust_strip.to_string());

        if let Some(stack_protector) = &self.config.rust_stack_protector {
            rustflags.arg(&format!("-Zstack-protector={stack_protector}"));
        }

        let requested_debuginfo_level = match mode {
            Mode::Rustc | Mode::Codegen => self.config.rust_debuginfo_level_rustc,
            Mode::Std => self.config.rust_debuginfo_level_std,
            Mode::ToolBootstrap | Mode::ToolStd | Mode::ToolRustcPrivate | Mode::ToolTarget => {
                self.config.rust_debuginfo_level_tools
            }
        };
        // trust-cg emits no faithful debug sections and rejects any nonzero
        // request.  Cargo profiles otherwise inherit `rust.debuginfo-level`
        // and can make an audited Trust-CG build impossible before the backend
        // sees user code.
        let debuginfo_level =
            effective_debuginfo_level(narrow_trust_backend_is_active, requested_debuginfo_level);
        cargo.env(profile_var("DEBUG"), debuginfo_level.to_string());
        if let Some(opt_level) = &self.config.rust_optimize.get_opt_level() {
            cargo.env(profile_var("OPT_LEVEL"), opt_level);
        }
        cargo.env(
            profile_var("DEBUG_ASSERTIONS"),
            match mode {
                Mode::Std => self.config.std_debug_assertions,
                Mode::Rustc | Mode::Codegen => self.config.rustc_debug_assertions,
                Mode::ToolBootstrap | Mode::ToolStd | Mode::ToolRustcPrivate | Mode::ToolTarget => {
                    self.config.tools_debug_assertions
                }
            }
            .to_string(),
        );
        cargo.env(
            profile_var("OVERFLOW_CHECKS"),
            if mode == Mode::Std {
                self.config.rust_overflow_checks_std.to_string()
            } else {
                self.config.rust_overflow_checks.to_string()
            },
        );

        match self.config.split_debuginfo(target) {
            SplitDebuginfo::Packed => rustflags.arg("-Csplit-debuginfo=packed"),
            SplitDebuginfo::Unpacked => rustflags.arg("-Csplit-debuginfo=unpacked"),
            SplitDebuginfo::Off => rustflags.arg("-Csplit-debuginfo=off"),
        };

        // trust-cg deliberately rejects unwinding until its invoke, cleanup,
        // personality, LSDA, and resume lowering is complete.  Once a staged
        // compiler uses trust-cg as its default backend, rustbuild must request
        // the supported panic ABI for every target crate instead of relying on
        // each Cargo profile to rediscover that backend capability.
        for flag in trust_cg_codegen_flags(trust_cg_is_active, cmd_kind == Kind::Test) {
            // Cargo omits target RUSTFLAGS from host build scripts and proc
            // macros in a cross build. The staged host compiler still uses
            // trust-cg, so keep both invocation classes on the same supported
            // panic ABI.
            rustflags.arg(flag);
            hostflags.arg(*flag);
        }

        if self.config.cmd.bless() {
            // Bless `expect!` tests.
            cargo.env("UPDATE_EXPECT", "1");
        }

        // Set an environment variable that tells the rustc/rustdoc wrapper
        // binary to pass `-Zforce-unstable-if-unmarked` to the real compiler.
        match mode {
            // Any library crate that's part of the sysroot should be marked unstable
            // (including third-party dependencies), unless it uses a staged_api
            // `#![stable(..)]` attribute to explicitly mark itself stable.
            Mode::Std | Mode::Codegen | Mode::Rustc => {
                cargo.env("RUSTC_FORCE_UNSTABLE", "1");
            }

            // For everything else, crate stability shouldn't matter, so don't set a flag.
            Mode::ToolBootstrap | Mode::ToolRustcPrivate | Mode::ToolStd | Mode::ToolTarget => {}
        }

        if let Some(x) = self.crt_static(target) {
            if x {
                rustflags.arg("-Ctarget-feature=+crt-static");
            } else {
                rustflags.arg("-Ctarget-feature=-crt-static");
            }
        }

        if let Some(x) = self.crt_static(compiler.host) {
            let sign = if x { "+" } else { "-" };
            hostflags.arg(format!("-Ctarget-feature={sign}crt-static"));
        }

        // `rustc` needs to know the remapping scheme, in order to know how to reverse it (unremap)
        // later. Two env vars are set and made available to the compiler
        //
        // - `CFG_VIRTUAL_RUST_SOURCE_BASE_DIR`: `rust-src` remap scheme (`NonCompiler`)
        // - `CFG_VIRTUAL_RUSTC_DEV_SOURCE_BASE_DIR`: `rustc-dev` remap scheme (`Compiler`)
        //
        // Keep this scheme in sync with `rustc_metadata::rmeta::decoder`'s
        // `try_to_translate_virtual_to_real`.
        let trim_paths = |cargo: &mut BootstrapCommand, ws_remap: &str| {
            cargo.arg("-Ztrim-paths");
            cargo.arg("--config").arg("profile.release.trim-paths='all'");
            cargo.arg("--config").arg("profile.dev.trim-paths='all'");
            // This is an internal contract with cargo.
            // bootstrap needs workspace sources remapped to `/rust{c,-dev}/<sha>` instead of `.`
            // See <https://github.com/rust-lang/cargo/issues/17309>.
            cargo.env("__CARGO_RUSTC_BOOTSTRAP_WS_REMAP", ws_remap);
        };

        match mode {
            Mode::Rustc | Mode::Codegen => {
                if let Some(ref map_to) = self.sess.debuginfo_map_to(RemapScheme::NonCompiler) {
                    // Tell the compiler which prefix was used for remapping the standard library
                    cargo.env("CFG_VIRTUAL_RUST_SOURCE_BASE_DIR", map_to);
                }

                if let Some(ref map_to) = self.sess.debuginfo_map_to(RemapScheme::Compiler) {
                    // Tell the compiler which prefix was used for remapping the compiler it-self
                    cargo.env("CFG_VIRTUAL_RUSTC_DEV_SOURCE_BASE_DIR", map_to);

                    trim_paths(&mut cargo, map_to);
                }
            }
            Mode::Std
            | Mode::ToolBootstrap
            | Mode::ToolRustcPrivate
            | Mode::ToolStd
            | Mode::ToolTarget => {
                if let Some(ref map_to) = self.sess.debuginfo_map_to(RemapScheme::NonCompiler) {
                    trim_paths(&mut cargo, map_to);
                }
            }
        }

        // Enable usage of unstable features
        cargo.env("RUSTC_BOOTSTRAP", "1");

        // Trust: use the selected executable's capability, including when the
        // pinned seed and source-built Cargo advertise different spellings.
        cargo.arg(program.metadata_flag);

        if self.config.dump_bootstrap_shims {
            prepare_shims_dump_dir(self);

            cargo
                .env("DUMP_BOOTSTRAP_SHIMS", self.sess.out.join("bootstrap-shims-dump"))
                .env("BUILD_OUT", &self.sess.out)
                .env("CARGO_HOME", t!(home::cargo_home()));
        };

        self.add_rust_test_threads(&mut cargo);

        // Almost all of the crates that we compile as part of the bootstrap may
        // have a build script, including the standard library. To compile a
        // build script, however, it itself needs a standard library! This
        // introduces a bit of a pickle when we're compiling the standard
        // library itself.
        //
        // To work around this we actually end up using the snapshot compiler
        // (stage0) for compiling build scripts of the standard library itself.
        // The stage0 compiler is guaranteed to have a libstd available for use.
        //
        // For other crates, however, we know that we've already got a standard
        // library up and running, so we can use the normal compiler to compile
        // build scripts in that situation.
        if mode == Mode::Std {
            cargo
                .env("RUSTC_SNAPSHOT", &self.initial_rustc)
                .env("RUSTC_SNAPSHOT_LIBDIR", self.rustc_snapshot_libdir());
        } else {
            cargo
                .env("RUSTC_SNAPSHOT", self.rustc(compiler))
                .env("RUSTC_SNAPSHOT_LIBDIR", self.rustc_libdir(compiler));
        }

        // Tools that use compiler libraries inherit LLVM's native link
        // requirements, but Cargo metadata does not propagate the matching
        // search directories across separate projects. Recover LLVM's own
        // libdir, absolute system-library parents, and the common Homebrew
        // prefix libdir. Homebrew's llvm-config emits dependencies such as
        // zstd as bare `-l` names, so LLVM's Cellar libdir alone is not enough.
        if (mode == Mode::ToolRustcPrivate || mode == Mode::Codegen)
            && self.is_llvm_enabled_for(target)
        {
            let llvm = self.ensure(Llvm { target });
            let isolated = crate::utils::llvm_native_dev::applies(
                &target.triple,
                &self.host_target.triple,
                llvm.kind() == crate::core::build_steps::llvm::LlvmKind::External,
                llvm.link_shared(),
            );
            if isolated && !self.config.dry_run() {
                // The compiler build script already confines this static
                // inventory. Do not undo that confinement for rustdoc and
                // other private tools by exporting the whole LLVM prefix,
                // which may contain a private libc++/ABI/unwind runtime.
                let help = command(llvm.llvm_config()).cached().arg("--help").run_capture(self);
                let quoted =
                    help.stdout().contains("quote-paths") || help.stderr().contains("quote-paths");
                let mut query = command(llvm.llvm_config());
                query.cached().args(["--link-static", "--libfiles"]);
                if quoted {
                    query.arg("--quote-paths");
                }
                let files = query.run_capture_stdout(self).stdout();
                // Older LLVM's documented unquoted output is whitespace
                // delimited. Match the compiler build script's parser;
                // every resulting absolute file is checked below.
                let files = if quoted {
                    files
                } else {
                    files
                        .split_whitespace()
                        .map(shlex::try_quote)
                        .collect::<Result<Vec<_>, _>>()
                        .unwrap_or_else(|error| panic!("invalid unquoted LLVM inventory: {error}"))
                        .join(" ")
                };
                let directory = crate::utils::llvm_native_dev::isolated_tool_search(
                    &files,
                    &target.triple,
                    &self.sess.out.join("llvm-tool-native-search"),
                )
                .unwrap_or_else(|error| panic!("invalid native LLVM tool search: {error}"));
                rustflags.arg(&format!("-Clink-arg=-L{}", directory.display()));
            } else {
                let llvm_libdir = if self.config.is_host_target(target) {
                    command(self.host_llvm_config())
                        .cached()
                        .arg("--libdir")
                        .run_capture_stdout(self)
                        .stdout()
                        .trim()
                        .to_owned()
                } else {
                    let llvm_output = self.ensure(Llvm { target });
                    llvm_output.root_dir().join("lib").to_string_lossy().into_owned()
                };
                let mut native_dirs = Vec::new();
                let llvm_libdir = PathBuf::from(llvm_libdir);
                if llvm_libdir.is_dir() {
                    native_dirs.push(llvm_libdir);
                }

                // Trust: recover the remaining native dirs from `llvm-config` (see the
                // comment above the guard). That binary can only be run when it was
                // built for this host, which is also the system/Homebrew LLVM case this
                // recovery exists for.
                let llvm_config;
                let system_libs = if self.config.is_host_target(target) {
                    llvm_config = self.host_llvm_config();
                    command(&llvm_config)
                        .cached()
                        .args(["--link-static", "--system-libs"])
                        .run_capture_stdout(self)
                        .stdout()
                } else {
                    llvm_config = PathBuf::new();
                    String::new()
                };
                for token in system_libs.split_whitespace() {
                    let library = Path::new(token);
                    if library.is_absolute()
                        && let Some(parent) = library.parent()
                        && parent.is_dir()
                    {
                        let parent = parent.to_path_buf();
                        if !native_dirs.contains(&parent) {
                            native_dirs.push(parent);
                        }
                    }
                }

                if let Some(opt_dir) =
                    llvm_config.ancestors().find(|path| path.file_name() == Some(OsStr::new("opt")))
                    && let Some(prefix) = opt_dir.parent()
                {
                    let common_libdir = prefix.join("lib");
                    if common_libdir.is_dir() && !native_dirs.contains(&common_libdir) {
                        native_dirs.push(common_libdir);
                    }
                }

                for native_dir in native_dirs {
                    if target.is_msvc() {
                        rustflags.arg(&format!("-Clink-arg=-LIBPATH:{}", native_dir.display()));
                    } else {
                        rustflags.arg(&format!("-Clink-arg=-L{}", native_dir.display()));
                    }
                }
            }
        }

        // Compile everything except libraries and proc macros with the more
        // efficient initial-exec TLS model. This doesn't work with `dlopen`,
        // so we can't use it by default in general, but we can use it for tools
        // and our own internal libraries.
        //
        // Cygwin only supports emutls.
        if !mode.must_support_dlopen()
            && !target.triple.starts_with("powerpc-")
            && !target.triple.contains("cygwin")
        {
            cargo.env("RUSTC_TLS_MODEL_INITIAL_EXEC", "1");
        }

        // Ignore incremental modes except for stage0, since we're
        // not guaranteeing correctness across builds if the compiler
        // is changing under your feet.
        if self.config.incremental && compiler.stage == 0 {
            cargo.env("CARGO_INCREMENTAL", "1");
        } else {
            // Don't rely on any default setting for incr. comp. in Cargo
            cargo.env("CARGO_INCREMENTAL", "0");
        }

        if let Some(ref on_fail) = self.config.on_fail {
            cargo.env("RUSTC_ON_FAIL", on_fail);
        }

        if self.config.print_step_timings {
            cargo.env("RUSTC_PRINT_STEP_TIMINGS", "1");
        }

        if self.config.print_step_rusage {
            cargo.env("RUSTC_PRINT_STEP_RUSAGE", "1");
        }

        if self.config.backtrace_on_ice {
            cargo.env("RUSTC_BACKTRACE_ON_ICE", "1");
        }

        if self.verbosity >= 2 {
            // This provides very useful logs especially when debugging build cache-related stuff.
            // Trust: tracing targets are module paths, which start with the library's
            // name. The in-tree Targo keeps its fingerprints in its `targo-core`
            // library (`targo_core::compiler::…`), the pinned stage0 seal's Targo
            // (29ebb403d) in its `targo` library (`targo::compiler::…`), and a stock
            // Cargo, which the stage0 check admits, in `cargo::core::compiler::…`.
            cargo.env(
                "CARGO_LOG",
                "targo_core::compiler::fingerprint=info,targo::compiler::fingerprint=info,\
                 cargo::core::compiler::fingerprint=info",
            );
        }

        cargo.env("RUSTC_VERBOSE", self.verbosity.to_string());

        // Downstream forks of the Rust compiler might want to use a custom libc to add support for
        // targets that are not yet available upstream. Adding a patch to replace libc with a
        // custom one would cause compilation errors though, because Cargo would interpret the
        // custom libc as part of the workspace, and apply the check-cfg lints on it.
        //
        // The libc build script emits check-cfg flags only when this environment variable is set,
        // so this line allows the use of custom libcs.
        cargo.env("LIBC_CHECK_CFG", "1");

        let mut lint_flags = Vec::new();
        let mut compiler_lint_flags = Vec::new();

        // Lints for all in-tree code: compiler, rustdoc, cranelift, gcc,
        // clippy, rustfmt, rust-analyzer, etc.
        if source_type == SourceType::InTree {
            // When extending this list, add the new lints to the RUSTFLAGS of the
            // build_bootstrap function of src/bootstrap/bootstrap.py as well as
            // some code doesn't go through this `rustc` wrapper.
            lint_flags.push("-Wrust_2018_idioms");
            lint_flags.push("-Wunused_lifetimes");

            if self.config.deny_warnings && mode != Mode::Rustc {
                // We use this instead of `lint_flags` so that we don't have to rebuild all
                // workspace dependencies when `deny-warnings` changes, but we still get an error
                // immediately instead of having to wait until the next rebuild.
                cargo.env("CARGO_BUILD_WARNINGS", "deny");
            }

            rustdocflags.arg("-Wrustdoc::invalid_codeblock_attributes");
        }

        // Lints just for `compiler/` crates.
        if mode == Mode::Rustc {
            // Rustc mode contains Trust's first-party workspace dependencies,
            // for which Cargo's workspace-primary warning policy is too broad.
            // Keep denial on the same manifest-scoped compiler boundary as the
            // internal lints instead of setting Cargo's global warning policy.
            if self.config.deny_warnings {
                compiler_lint_flags.push("-Dwarnings");
            }
            compiler_lint_flags.push("-Wrustc::internal");
            compiler_lint_flags.push("-Drustc::symbol_intern_string_literal");
            // FIXME(edition_2024): Change this to `-Wrust_2024_idioms` when all
            // of the individual lints are satisfied.
            compiler_lint_flags.push("-Wkeyword_idents_2024");
            compiler_lint_flags.push("-Wunreachable_pub");
            compiler_lint_flags.push("-Wunsafe_op_in_unsafe_fn");
            compiler_lint_flags.push("-Wunused_crate_dependencies");
        }

        // This does not use RUSTFLAGS for two reasons.
        // - Due to caching issues with Cargo. Clippy is treated as an "in
        //   tree" tool, but shares the same cache as other "submodule" tools.
        //   With these options set in RUSTFLAGS, that causes *every* shared
        //   dependency to be rebuilt. By injecting this into the rustc
        //   wrapper, this circumvents Cargo's fingerprint detection. This is
        //   fine because lint flags are always ignored in dependencies.
        //   Eventually this should be fixed via better support from Cargo.
        // - RUSTFLAGS is ignored for proc macro crates that are being built on
        //   the host (because `--target` is given). But we want the lint flags
        //   to be applied to proc macro crates.
        cargo.env("RUSTC_LINT_FLAGS", lint_flags.join(" "));
        cargo.env("RUSTC_COMPILER_LINT_FLAGS", compiler_lint_flags.join(" "));
        cargo.env("RUSTC_COMPILER_ROOT", self.sess.src.join("compiler"));

        if self.config.rust_frame_pointers {
            rustflags.arg("-Cforce-frame-pointers=true");
        }

        // If Control Flow Guard is enabled, pass the `control-flow-guard` flag to rustc
        // when compiling the standard library, since this might be linked into the final outputs
        // produced by rustc. Since this mitigation is only available on Windows, only enable it
        // for the standard library in case the compiler is run on a non-Windows platform.
        if cfg!(windows) && mode == Mode::Std && self.config.control_flow_guard {
            rustflags.arg("-Ccontrol-flow-guard");
        }

        // If EHCont Guard is enabled, pass the `-Zehcont-guard` flag to rustc when compiling the
        // standard library, since this might be linked into the final outputs produced by rustc.
        // Since this mitigation is only available on Windows, only enable it for the standard
        // library in case the compiler is run on a non-Windows platform.
        if cfg!(windows) && mode == Mode::Std && self.config.ehcont_guard {
            rustflags.arg("-Zehcont-guard");
        }

        // Optionally override the rc.exe when compiling rustc on Windows.
        if let Some(windows_rc) = &self.config.windows_rc {
            cargo.env("RUSTC_WINDOWS_RC", windows_rc);
        }

        // For `cargo doc` invocations, make rustdoc print the Rust version into the docs
        // This replaces spaces with tabs because RUSTDOCFLAGS does not
        // support arguments with regular spaces. Hopefully someday Cargo will
        // have space support.
        let rust_version = self.rust_version().replace(' ', "\t");
        rustdocflags.arg("--crate-version").arg(&rust_version);

        // Environment variables *required* throughout the build

        // The host this new compiler is being *built* on.
        cargo.env("CFG_COMPILER_BUILD_TRIPLE", compiler.host.triple);

        // Set this for all builds to make sure doc builds also get it.
        cargo.env("CFG_RELEASE_CHANNEL", &self.config.channel);

        // verbose cargo output is very noisy, so only enable it with -vv
        for _ in 0..self.verbosity.saturating_sub(1) {
            cargo.arg("--verbose");
        }

        let requested_codegen_units =
            match (mode, self.config.rust_codegen_units_std, self.config.rust_codegen_units) {
                (Mode::Std, Some(n), _) | (_, _, Some(n)) => Some(n),
                _ => None,
            };
        if let Some(n) =
            effective_codegen_units(narrow_trust_backend_is_active, requested_codegen_units)
        {
            // The current Trust-CG adapter emits exactly one rustc module and
            // rejects explicit multi-CGU profiles. Use Cargo's profile setting
            // so the constraint covers target crates and host units alike.
            cargo.env(profile_var("CODEGEN_UNITS"), n.to_string());
        }

        if self.config.locked_deps {
            cargo.arg("--locked");
        }
        // Trust: enforce lock/offline policy on the actual producer, including
        // selected stage0/1 requests that use native source readiness. Cargo
        // completes resolution/source acquisition before executing build units;
        // full-recipe online preparation is a separate explicit operation.
        cargo.arg("--frozen");

        // Try to use a sysroot-relative bindir, in case it was configured absolutely.
        cargo.env("RUSTC_INSTALL_BINDIR", self.config.bindir_relative());

        if self.config.is_running_on_ci() {
            // Tell cargo to use colored output for nicer logs in CI, even
            // though CI isn't printing to a terminal.
            // Also set an explicit `TERM=xterm` so that cargo doesn't warn
            // about TERM not being set.
            cargo.env("TERM", "xterm").args(["--color=always"]);
        };

        // When we build Rust dylibs they're all intended for intermediate
        // usage, so make sure we pass the -Cprefer-dynamic flag instead of
        // linking all deps statically into the dylib.
        if matches!(mode, Mode::Std) {
            rustflags.arg("-Cprefer-dynamic");
        }

        // When building incrementally we default to a lower ThinLTO import limit
        // (unless explicitly specified otherwise). This will produce a somewhat
        // slower code but give way better compile times.
        {
            let limit = match self.config.rust_thin_lto_import_instr_limit {
                Some(limit) => Some(limit),
                None if self.config.incremental => Some(10),
                _ => None,
            };

            if let Some(limit) = limit
                && (build_compiler_stage == 0
                    || self.config.default_codegen_backend(compiler.host).is_llvm())
            {
                rustflags.arg(&format!("-Cllvm-args=-import-instr-limit={limit}"));
            }
        }

        if matches!(mode, Mode::Std) {
            if let Some(mir_opt_level) = self.config.rust_validate_mir_opts {
                rustflags.arg("-Zvalidate-mir");
                rustflags.arg(&format!("-Zmir-opt-level={mir_opt_level}"));
            }
            if self.config.rust_randomize_layout {
                rustflags.arg("--cfg=randomized_layouts");
            }
            // Always enable inlining MIR when building the standard library.
            // Without this flag, MIR inlining is disabled when incremental compilation is enabled.
            // That causes some mir-opt tests which inline functions from the standard library to
            // break when incremental compilation is enabled. So this overrides the "no inlining
            // during incremental builds" heuristic for the standard library.
            rustflags.arg("-Zinline-mir");

            // Similarly, we need to keep debug info for functions inlined into other std functions,
            // even if we're not going to output debuginfo for the crate we're currently building,
            // so that it'll be available when downstream consumers of std try to use it.
            rustflags.arg("-Zinline-mir-preserve-debug");

            rustflags.arg("-Zmir_strip_debuginfo=locals-in-tiny-functions");
        }

        // take target-specific extra rustflags if any otherwise take `rust.rustflags`
        let extra_rustflags = self
            .config
            .target_config
            .get(&target)
            .map(|t| &t.rustflags)
            .unwrap_or(&self.config.rust_rustflags)
            .clone();

        let profile =
            if matches!(cmd_kind, Kind::Bench | Kind::Miri | Kind::MiriSetup | Kind::MiriTest) {
                // Use the default profile for bench/miri
                None
            } else {
                match (mode, self.config.rust_optimize.is_release()) {
                    // Some std configuration exists in its own profile
                    (Mode::Std, _) => Some("dist"),
                    (_, true) => Some("release"),
                    (_, false) => Some("dev"),
                }
            };

        Cargo {
            command: cargo,
            args: vec![],
            compiler,
            mode,
            target,
            rustflags,
            rustdocflags,
            hostflags,
            allow_features,
            build_compiler_stage,
            extra_rustflags,
            profile,
            kind: cmd_kind,
        }
    }
}

pub(crate) fn cargo_profile_var(name: &str, config: &Config, mode: Mode) -> String {
    let profile = match (mode, config.rust_optimize.is_release()) {
        // Some std configuration exists in its own profile
        (Mode::Std, _) => "DIST",
        (_, true) => "RELEASE",
        (_, false) => "DEV",
    };
    format!("CARGO_PROFILE_{profile}_{name}")
}

/// Trust: does a `<mode>` + `<cmd_kind>` cargo invocation have to clear the std output
/// directory before it runs?
///
/// Extracted from the call site so the answer can be taken over every `Kind` in a unit test.
/// Cargo cannot detect that the real rustc changed -- it thinks rustc is `bootstrap/debug/rustc`
/// -- so bootstrap has to clear on its behalf, and the set of kinds that WRITE into a std out
/// dir is what decides the answer. `Kind::Build` is upstream's; `Kind::Test` is Trust's addition,
/// because stage-2 std is uplifted from stage 1 (`Std::should_be_uplifted_from_stage_1`) and so
/// no `Mode::Std` + `Kind::Build` cargo is ever constructed for `build/<host>/stage2-std`, while
/// `x.py test --stage 2` does build units into it.
fn std_out_dir_needs_clear(mode: Mode, cmd_kind: Kind) -> bool {
    mode == Mode::Std && matches!(cmd_kind, Kind::Build | Kind::Test)
}

#[cfg(test)]
mod tests;
/// Applies PGO compile flags to the given Cargo invocation based on the given PGO config.
/// PGO flags are only applied when compiling a stage2 component.
pub(crate) fn apply_pgo(
    builder: &Builder<'_>,
    cargo: &mut Cargo,
    build_compiler: Compiler,
    config: &PgoConfig,
) {
    let is_collecting = if let Some(path) = &config.generate_profile {
        if build_compiler.stage == 1 {
            cargo
                .rustflag(&format!("-Cprofile-generate={}", path.to_str().expect("non-UTF8 path")));
            // Apparently necessary to avoid overflowing the counters during
            // a Cargo build profile
            cargo.rustflag("-Cllvm-args=-vp-counters-per-site=4");
            true
        } else {
            false
        }
    } else if let Some(path) = &config.use_profile {
        if build_compiler.stage == 1 {
            cargo.rustflag(&format!("-Cprofile-use={}", path.to_str().expect("non-UTF8 path")));
            if builder.is_verbose() {
                cargo.rustflag("-Cllvm-args=-pgo-warn-missing-function");
            }
            true
        } else {
            false
        }
    } else {
        false
    };
    if is_collecting {
        // Ensure paths to Rust sources are relative, not absolute.
        cargo.rustflag(&format!(
            "-Cllvm-args=-static-func-strip-dirname-prefix={}",
            builder.config.src.components().count()
        ));
    }
}

/// Ensures that the behavior dump directory is properly initialized.
fn prepare_shims_dump_dir(builder: &Builder<'_>) {
    static INITIALIZED: OnceLock<bool> = OnceLock::new();

    let dump_path = builder.out.join("bootstrap-shims-dump");

    let initialized = INITIALIZED.get().unwrap_or(&false);
    if !initialized {
        // clear old dumps
        if dump_path.exists() {
            t!(fs::remove_dir_all(&dump_path));
        }

        t!(fs::create_dir_all(&dump_path));

        t!(INITIALIZED.set(true));
    }
}
