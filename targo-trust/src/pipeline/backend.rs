// The verified lane's rustflags (T14a): the tracked verifier policy, the
// selected codegen backend and the codegen contract, handed to the sibling
// Targo in TRUST_TARGO_LANE_RUSTFLAGS, which appends them to the project's own
// flags. Plus the direct-rustc classifiers, and the notices that name ambient
// `-Ztrust-*` options and TRUSTFLAGS.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::borrow::Cow;
use std::ffi::OsStr;

use crate::config::{
    DEFAULT_CODEGEN_BACKEND, known_verification_levels, normalize_verification_level,
};

/// Return the effective rustc option key in the spelling used by Targo policy.
///
/// rustc canonicalizes `-` to `_` before looking up every `-C`/`-Z` option, so
/// callers must treat both spellings as identical. Keeping that rule here avoids
/// policy checks disagreeing with the compiler about the option that will run.
pub(crate) fn canonical_rustc_option_name(option: &str) -> Cow<'_, str> {
    let name = option.split_once('=').map_or(option, |(name, _)| name);
    if name.contains('_') { Cow::Owned(name.replace('_', "-")) } else { Cow::Borrowed(name) }
}

fn effective_codegen_backend(selected_codegen_backend: Option<&str>) -> &str {
    selected_codegen_backend.unwrap_or(DEFAULT_CODEGEN_BACKEND)
}

/// Convert a validated verification level to the numeric `-Ztrust-verify-level`
/// value.
///
/// The catch-all this used to carry answered `0` — L0, the WEAKEST level — for
/// every string it did not recognise, and a test pinned it
/// (`level_to_num("unknown") == 0`). That is the same shape as the profile
/// defect above it: a string selects how much gets verified, and an
/// unrecognised one quietly selects the least. Nothing reaches it with a bad
/// level today — every caller passes `TrustConfig::level`, which
/// `deserialize_level` has already checked against `known_verification_levels`
/// and stored in canonical spelling — so the refusal below is unreachable on
/// every existing path. It is here so that a path which stops validating fails
/// loudly instead of verifying less than the project asked for.
///
/// A panic rather than a demotion because this is the last point before the
/// flag is spelled and the rustflags builders around it return `String` with
/// no error channel; `normalize_verification_level` is reused so the accepted
/// spellings cannot drift from the ones the config loader accepts.
pub(crate) fn level_to_num(level: &str) -> u8 {
    match normalize_verification_level(level) {
        Some("L0") => 0,
        Some("L1") => 1,
        Some("L2") => 2,
        _ => panic!(
            "invariant: verification level `{level}` never passed config validation \
             (known levels: {}); refusing to spell -Ztrust-verify-level rather than \
             silently verify at L0",
            known_verification_levels().join(", ")
        ),
    }
}

fn trust_cg_output_gate(allow_l0_gaps: bool) -> &'static str {
    if allow_l0_gaps { "allow-unknown" } else { "strict" }
}

fn rustc_bool_value(value: Option<&str>) -> Option<bool> {
    match value {
        None | Some("y") | Some("yes") | Some("on") | Some("true") => Some(true),
        Some("n") | Some("no") | Some("off") | Some("false") => Some(false),
        _ => None,
    }
}

pub(super) fn split_plain_rustflags(flags: &str) -> Vec<&str> {
    // Match Cargo/Targo's literal-space protocol exactly. Shell quoting is not
    // interpreted, and tabs/newlines inside one segment remain part of that
    // argument rather than silently becoming new compiler arguments here.
    flags.split(' ').map(str::trim).filter(|arg| !arg.is_empty()).collect()
}

pub(super) fn split_encoded_rustflags(flags: &str) -> Vec<&str> {
    if flags.is_empty() {
        Vec::new()
    } else {
        // Empty interior/trailing arguments are real encoded arguments. Keep
        // them so an invalid caller invocation remains invalid instead of
        // being silently repaired into a different proof build.
        flags.split('\x1f').collect()
    }
}

fn targo_owned_safety_codegen_option(option: &str) -> bool {
    matches!(canonical_rustc_option_name(option).as_ref(), "overflow-checks" | "debug-assertions")
}

/// Codegen settings that form trust-cg's currently audited linked-artifact
/// contract.  These are not performance preferences: allowing Cargo profiles
/// or inherited RUSTFLAGS to select unwind tables, debug-info emission,
/// multiple CGUs, or an incremental object cache reaches backend paths that
/// trust-cg explicitly does not implement.
fn targo_owned_trust_cg_codegen_option(option: &str) -> bool {
    matches!(
        canonical_rustc_option_name(option).as_ref(),
        "panic" | "debuginfo" | "codegen-units" | "incremental"
    )
}

fn forbidden_in_process_codegen_option(option: &str) -> bool {
    canonical_rustc_option_name(option) == "llvm-args"
}

/// Inspect one rustc codegen option using every spelling accepted by getopts.
/// `--codegen` is the long alias for `-C`; policy must parse both or a caller
/// can select the same compiler option through the unaudited spelling.
fn rustc_codegen_option_at(args: &[String], index: usize) -> (Option<&str>, usize, bool) {
    let argument = &args[index];
    if matches!(argument.as_str(), "-C" | "--codegen") {
        return (args.get(index + 1).map(String::as_str), 2.min(args.len() - index), true);
    }
    if let Some(option) = argument.strip_prefix("-C").filter(|option| !option.is_empty()) {
        return (Some(option), 1, false);
    }
    if let Some(option) = argument.strip_prefix("--codegen=") {
        return (Some(option), 1, false);
    }
    (None, 1, false)
}

pub(crate) fn find_forbidden_in_process_codegen_arg(args: &[String]) -> Option<String> {
    let mut index = 0;
    while index < args.len() {
        let argument = &args[index];
        let (option, consumed, split) = rustc_codegen_option_at(args, index);
        if let Some(option) = option.filter(|option| forbidden_in_process_codegen_option(option)) {
            return Some(if split { format!("{argument} {option}") } else { argument.clone() });
        }
        index += consumed;
    }
    None
}

pub(crate) fn find_codegen_help_arg(args: &[String]) -> Option<String> {
    let mut index = 0;
    while index < args.len() {
        let argument = &args[index];
        let (option, consumed, split) = rustc_codegen_option_at(args, index);
        if option.is_some_and(|option| canonical_rustc_option_name(option) == "help") {
            return Some(if split {
                format!("{argument} {}", option.expect("matched codegen option"))
            } else {
                argument.clone()
            });
        }
        index += consumed;
    }
    None
}

fn trust_cg_codegen_option_is_canonical(option: &str) -> bool {
    let Some((_name, value)) = option.split_once('=') else {
        return false;
    };
    match canonical_rustc_option_name(option).as_ref() {
        "panic" => value == "abort",
        // `none` is accepted by rustc as a spelling of disabled debug info;
        // normalize either spelling to the one emitted below.
        "debuginfo" => matches!(value, "0" | "none"),
        "codegen-units" => value == "1",
        // There is no stable `-Cincremental=off` value: absence is the only
        // canonical compiler argument. Cargo is disabled separately with
        // CARGO_INCREMENTAL=0 before it constructs the rustc command.
        "incremental" => false,
        _ => false,
    }
}

/// Reject a direct-rustc attempt to change trust-cg's linked-output contract.
/// Matching spellings are removed and re-appended canonically by the caller.
pub(super) fn canonicalize_trust_cg_codegen_args(args: &[String]) -> Result<Vec<String>, String> {
    let mut sanitized = Vec::with_capacity(args.len());
    let mut index = 0;
    while index < args.len() {
        if args[index] == "-g" {
            return Err("-g".to_string());
        }

        let (option, consumed, split) = rustc_codegen_option_at(args, index);
        if let Some(option) = option.filter(|option| targo_owned_trust_cg_codegen_option(option)) {
            if !trust_cg_codegen_option_is_canonical(option) {
                return Err(if split {
                    format!("{} {option}", args[index])
                } else {
                    args[index].clone()
                });
            }
            index += consumed;
            continue;
        }

        sanitized.push(args[index].clone());
        index += 1;
    }
    Ok(sanitized)
}

/// Direct rustc has no Cargo metadata target inventory. Require an explicit
/// crate-type boundary so a source file's default executable cannot reach the
/// backend and fail only after compilation has started. CLI crate types take
/// precedence over crate attributes, so this is also an honest preflight for
/// files that contain `#![crate_type = ...]`.
pub(super) fn validate_direct_trust_cg_rlib_target(args: &[String]) -> Result<(), String> {
    if args.iter().any(|arg| arg == "--test") {
        return Err("`--test` selects an executable test harness".to_string());
    }

    let mut crate_types = Vec::new();
    let mut index = 0;
    while index < args.len() {
        let value = if args[index] == "--crate-type" {
            index += 1;
            Some(
                args.get(index)
                    .filter(|value| !value.is_empty())
                    .ok_or_else(|| "--crate-type requires a non-empty value".to_string())?
                    .as_str(),
            )
        } else {
            args[index].strip_prefix("--crate-type=")
        };
        if let Some(value) = value {
            if value.is_empty() {
                return Err("--crate-type requires a non-empty value".to_string());
            }
            crate_types.extend(value.split(',').map(str::to_string));
        }
        index += 1;
    }

    if crate_types.is_empty() {
        return Err(
            "a direct Rust source defaults to an executable; pass `--crate-type=rlib`".to_string()
        );
    }
    if let Some(unsupported) =
        crate_types.iter().find(|crate_type| !matches!(crate_type.as_str(), "lib" | "rlib"))
    {
        return Err(format!(
            "direct crate type `{unsupported}` is not supported; pass exactly `--crate-type=rlib`"
        ));
    }
    Ok(())
}

fn safety_codegen_option_value(option: &str) -> Option<bool> {
    let (_name, value) =
        option.split_once('=').map_or((option, None), |(name, value)| (name, Some(value)));
    targo_owned_safety_codegen_option(option).then(|| rustc_bool_value(value)).flatten()
}

pub(super) fn find_safety_codegen_override(args: &[String]) -> Option<String> {
    let mut index = 0;
    while index < args.len() {
        let argument = &args[index];
        let (option, consumed, split) = rustc_codegen_option_at(args, index);
        if let Some(option) = option {
            if targo_owned_safety_codegen_option(option)
                && safety_codegen_option_value(option) != Some(true)
            {
                return Some(if split { format!("{argument} {option}") } else { argument.clone() });
            }
        }
        index += consumed;
    }
    None
}

pub(super) fn canonicalize_strict_safety_codegen_args(
    args: &[String],
) -> Result<Vec<String>, String> {
    if let Some(override_arg) = find_safety_codegen_override(args) {
        return Err(override_arg);
    }

    let mut sanitized = Vec::with_capacity(args.len());
    let mut index = 0;
    while index < args.len() {
        let (option, consumed, _) = rustc_codegen_option_at(args, index);
        if option.is_some_and(targo_owned_safety_codegen_option) {
            index += consumed;
            continue;
        }
        sanitized.push(args[index].clone());
        index += 1;
    }
    Ok(sanitized)
}

pub(super) fn targo_owned_z_option(option: &str, replace_codegen_backend: bool) -> bool {
    let name = canonical_rustc_option_name(option);
    // Targo owns the whole Trust option namespace.  An enumerated list drifted
    // when new dump paths were added to rustc_session, allowing inherited or
    // direct `trust-dump` sinks
    // values to select unreported artifact sinks. Namespace ownership makes a
    // newly added Trust authority/artifact option fail closed automatically.
    name.starts_with("trust-")
        // The retired upstream execution projection predates Trust's
        // namespace and must never leak from a mixed-version environment.
        || name == "contract-checks"
        // LLVM plugins execute inside trustc and can forge authenticated
        // verifier transport. Strip every inherited key spelling.
        || name == "llvm-plugins"
        || (replace_codegen_backend && name == "codegen-backend")
}

/// The compiler budget options targo derives from the budget profile alone
/// (`[trust] effort`/`backstop`): the effort scale, the two clocks the
/// backstop sets, and the step budget, a seal constant targo does not pass.
/// Never accepted from inherited RUSTFLAGS.
fn is_budget_option(name: &str) -> bool {
    matches!(
        name,
        "trust-verify-effort"
            | "trust-verify-timeout-ms"
            | "trust-verify-function-budget-ms"
            | "trust-verify-function-budget-steps"
    )
}

/// Where a run's budgets are set, for every notice that ignores one.
const BUDGET_SPELLING: &str =
    "budgets are `[trust] effort` and `backstop` in the workspace root manifest";

/// Where each per-run Trust selection lives (determinism plan §3.6;
/// DECISION_QUEUE T7a), for every notice that ignores an ambient spelling of
/// one: the lane and the hardened profile are command-line flags, a level
/// below the resolved one is the `[trust]` table's alone, and a tightening is
/// Cargo configuration, which the project-policy query reads and adopts.
pub(crate) const PER_RUN_SELECTIONS: &str = "select the lane with --certify, --memory-safe \
     or --allow-l0-gaps, the hardened profile with --trust-profile or --no-hardened, \
     verifier worker threads with --worker-threads, a lower level with `level` in the \
     [trust] table, and a tightening (a higher level, -Ztrust-verify-include-dependencies=yes, \
     -Ztrust-ir-lower=strict) in Cargo configuration (`--config` for one run)";

/// The one notice for an ambient TRUSTFLAGS / CARGO_ENCODED_TRUSTFLAGS, or
/// `None` when neither carries anything.
///
/// TRUSTFLAGS was the per-run `-Ztrust-*` override channel until T7a
/// (determinism plan §3.6: "TRUSTFLAGS leaves whole"). It is no longer read,
/// so a verdict depends only on declared inputs: the command line, the
/// manifests and Cargo configuration. A value left in a shell or a script is
/// IGNORED, never an error, and never silent: the notice names what was
/// ignored and where each selection now lives, as the inherited-RUSTFLAGS
/// warning does. An empty variable selects nothing, so it is not named.
pub(crate) fn ignored_trustflags_notice(
    plain: Option<&OsStr>,
    encoded: Option<&OsStr>,
) -> Option<String> {
    let ignored = [("TRUSTFLAGS", plain, ' '), ("CARGO_ENCODED_TRUSTFLAGS", encoded, '\x1f')]
        .into_iter()
        .filter_map(|(name, value, separator)| {
            let value = value.filter(|value| !value.is_empty())?.to_string_lossy();
            Some(format!("{name}=\"{}\"", value.replace(separator, " ")))
        })
        .collect::<Vec<_>>();
    (!ignored.is_empty()).then(|| {
        format!(
            "{} ignored: targo trust no longer reads TRUSTFLAGS; {PER_RUN_SELECTIONS}; \
             {BUDGET_SPELLING}",
            ignored.join(" and ")
        )
    })
}

/// List the inherited `-Ztrust-*`-family options that a verified run ignores:
/// under the lane the sibling Targo drops every environment `-Ztrust-*`
/// token (T14a). The crate-mode pipeline surfaces these as a warning naming
/// where each per-run selection lives ([`PER_RUN_SELECTIONS`]), so the drop is
/// never silent. Built on `targo_owned_z_option`; non-trust options the lane
/// owns (codegen-backend, llvm-plugins) stay out of the warning because no
/// Trust selection replaces them, and the sibling Targo names those itself.
fn stripped_inherited_trust_options(args: &[String]) -> Vec<String> {
    let mut stripped = Vec::new();
    let mut index = 0;
    while index < args.len() {
        let split = args[index] == "-Z";
        let option = if split {
            args.get(index + 1).map(String::as_str)
        } else {
            args[index].strip_prefix("-Z").filter(|option| !option.is_empty())
        };
        if let Some(option) = option {
            if targo_owned_z_option(option, false) {
                let name = canonical_rustc_option_name(option);
                if name.starts_with("trust-") || name.starts_with("no-trust-") {
                    stripped.push(if split { format!("-Z {option}") } else { args[index].clone() });
                }
            }
        }
        index += if split { 2 } else { 1 };
    }
    stripped
}

/// Render the warning for `-Ztrust-*` options in inherited rustflags, using
/// the same source precedence as `merged_cargo_rustflags_with_options`
/// (encoded rustflags, when present, make Cargo ignore plain RUSTFLAGS).
/// `None` when nothing trust-flavored would be stripped.
pub(crate) fn inherited_trust_rustflags_warning(
    encoded: Option<&str>,
    plain: Option<&str>,
) -> Option<String> {
    let (source, args) = if let Some(encoded) = encoded {
        (
            "CARGO_ENCODED_RUSTFLAGS",
            split_encoded_rustflags(encoded).into_iter().map(str::to_string).collect::<Vec<_>>(),
        )
    } else {
        let plain = plain?;
        (
            "RUSTFLAGS",
            split_plain_rustflags(plain).into_iter().map(str::to_string).collect::<Vec<_>>(),
        )
    };
    // A budget option's one spelling is the budget profile, so its notice
    // names `[trust]`; every other option's names the per-run selections.
    let (budget, policy): (Vec<String>, Vec<String>) =
        stripped_inherited_trust_options(&args).into_iter().partition(|flag| {
            let option = flag.strip_prefix("-Z").unwrap_or(flag).trim_start();
            is_budget_option(&canonical_rustc_option_name(option))
        });
    let mut notices = Vec::new();
    if !policy.is_empty() {
        notices.push(format!(
            "warning: -Ztrust-* in {source} is ignored (ignored: {}); {PER_RUN_SELECTIONS}",
            policy.join(", ")
        ));
    }
    if !budget.is_empty() {
        notices.push(format!("warning: {source} {} ignored: {BUDGET_SPELLING}", budget.join(", ")));
    }
    (!notices.is_empty()).then(|| notices.join("\n"))
}

pub(super) fn append_trust_cg_codegen_args(args: &mut Vec<String>) {
    args.extend([
        "-C".to_string(),
        "panic=abort".to_string(),
        "-C".to_string(),
        "debuginfo=0".to_string(),
        "-C".to_string(),
        "codegen-units=1".to_string(),
    ]);
}

pub(super) fn append_strict_safety_check_args(args: &mut Vec<String>) {
    args.extend([
        "-C".to_string(),
        "overflow-checks=yes".to_string(),
        "-C".to_string(),
        "debug-assertions=yes".to_string(),
    ]);
}

pub(super) fn append_codegen_backend_args(
    cmd_args: &mut Vec<String>,
    selected_codegen_backend: Option<&str>,
    allow_l0_gaps: bool,
) {
    let backend = effective_codegen_backend(selected_codegen_backend);
    cmd_args.push("-Z".to_string());
    cmd_args.push(format!("codegen-backend={backend}"));
    if backend == "trust-cg" {
        cmd_args.push("-Z".to_string());
        cmd_args.push(format!("trust-cg-output-gate={}", trust_cg_output_gate(allow_l0_gaps)));
    }
}

pub(super) fn append_verification_mode_args(cmd_args: &mut Vec<String>, allow_l0_gaps: bool) {
    if allow_l0_gaps {
        cmd_args.push("-Z".to_string());
        cmd_args.push("trust-policy=advisory".to_string());
    }
}

/// The private variable that carries the lane to the sibling Targo, in
/// Cargo's encoded form (`\x1f`-separated): it appends the lane to the
/// project's rustflags, resolved by Cargo's own precedence, so a verified unit
/// compiles `<project> <lane>` (determinism plan §5.3, DECISION_QUEUE
/// T14-APPEND-1). The caller's RUSTFLAGS and CARGO_ENCODED_RUSTFLAGS are left
/// as they are.
pub(crate) const TRUST_TARGO_LANE_RUSTFLAGS_ENV: &str = "TRUST_TARGO_LANE_RUSTFLAGS";

/// The verified lane's own flags, before the per-run verification controls
/// and the adopted project requirements are appended: the level, the output
/// transport, the codegen backend and its output gate, the policy, trust-cg's
/// codegen contract and the strict safety checks. Nothing ambient is read:
/// the sibling Targo drops the project's `-Ztrust-*` tokens from the
/// environment, and the options the lane owns from every channel, with a
/// notice naming each one's source (T14-APPEND-2).
pub(crate) fn lane_rustflags(
    level: &str,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
    strict_artifact_policy: bool,
    allow_l0_gaps: bool,
) -> Vec<String> {
    let mut args = vec!["-Z".to_string(), format!("trust-verify-level={}", level_to_num(level))];
    if supports_json_transport {
        args.push("-Z".to_string());
        args.push("trust-verify-output=json".to_string());
    }
    append_codegen_backend_args(&mut args, selected_codegen_backend, allow_l0_gaps);
    append_verification_mode_args(&mut args, allow_l0_gaps);
    if selected_codegen_backend == Some("trust-cg") {
        append_trust_cg_codegen_args(&mut args);
    }
    if strict_artifact_policy {
        append_strict_safety_check_args(&mut args);
    }
    args
}

/// The lane of a selection probe that evaluates target cfgs (the trust-cg
/// unit-graph preflight, the temporal gate's `--filter-platform` metadata,
/// the project-policy query): trust-cg's codegen contract and the strict
/// safety checks the build forces, which are target cfgs (`panic`,
/// `debug_assertions`), and no `-Ztrust-*` option, since those probes run in
/// Targo's unverified dry and metadata lanes. The probe's Targo resolves the
/// project's flags as the build does and appends this lane, so the probe
/// selects the `[target.'cfg(..)']` tables and dependencies the build selects,
/// and the lane's ownership of the backend keeps any external one out of the
/// probe's compiler.
pub(crate) fn cfg_probe_lane_rustflags(
    selected_codegen_backend: Option<&str>,
    strict_artifact_policy: bool,
) -> Vec<String> {
    let mut args = Vec::new();
    if selected_codegen_backend == Some("trust-cg") {
        append_trust_cg_codegen_args(&mut args);
    }
    if strict_artifact_policy {
        append_strict_safety_check_args(&mut args);
    }
    args
}

/// Encode a lane for TRUST_TARGO_LANE_RUSTFLAGS. One argument cannot carry
/// Cargo's delimiter.
pub(crate) fn encode_lane_rustflags(lane: &[String]) -> Result<String, String> {
    if lane.iter().any(|argument| argument.contains('\x1f')) {
        return Err(
            "a lane argument cannot contain Cargo's U+001F encoded-rustflags delimiter".to_string()
        );
    }
    Ok(lane.join("\x1f"))
}

#[cfg(test)]
mod option_token_tests {
    use super::*;

    #[test]
    fn rustc_option_key_normalization_covers_owned_z_and_c_policy() {
        assert_eq!(canonical_rustc_option_name("trust_verify_level=0"), "trust-verify-level");
        assert_eq!(canonical_rustc_option_name("overflow_checks=no"), "overflow-checks");
        assert!(targo_owned_z_option("trust_verify_output=human", false));
        assert!(targo_owned_z_option("contract_checks=yes", false));
        assert!(targo_owned_z_option("contract-checks=no", false));
        assert!(targo_owned_z_option("contract_checks", false));
        assert!(targo_owned_z_option("trust_targo_test_monitor", false));
        assert!(targo_owned_z_option("codegen_backend=llvm", true));
        assert!(targo_owned_z_option("llvm_plugins=/tmp/forged.dylib", false));
        assert!(targo_owned_safety_codegen_option("debug_assertions=off"));
        assert!(targo_owned_trust_cg_codegen_option("codegen_units=8"));
    }

    #[test]
    fn targo_owns_the_complete_trust_session_option_namespace() {
        // This inventory documents the current rustc_session surface, while
        // the future sentinel verifies that ownership does not depend on this
        // list being updated in lockstep with the compiler.
        for option in [
            "trust-audited-proc-macro",
            "trust-certified-test-monitors",
            "trust-cg-output-gate",
            "trust-dump",
            "trust-ir-flip",
            "trust-ir-lower",
            "trust-no-adapter-yield",
            "trust-no-r1",
            "trust-no-str-byte-position",
            "trust-proc-macro-boundary",
            "trust-proof-artifact-root",
            "trust-tinv",
            "trust-targo-test-monitor",
            "trust-verify-crate-role",
            "trust-policy",
            "trust-verify",
            "trust-verify-effort",
            "trust-verify-function-budget-ms",
            "trust-verify-function-budget-steps",
            "trust-verify-include-dependencies",
            "trust-verify-level",
            "trust-verify-output",
            "trust-verify-package-name",
            "trust-verify-profile",
            "trust-verify-session",
            "trust-verify-timeout-ms",
            "trust-verify-worker-threads",
            "trust-witness",
            "trust-witness-precise",
        ] {
            assert!(targo_owned_z_option(option, false), "unowned Trust option: {option}");
        }
        assert!(targo_owned_z_option("trust-verify=off", false));
        assert!(targo_owned_z_option("trust-future-authority-option=/tmp/hostile", false));
        assert!(!targo_owned_z_option("unrelated-compiler-option", false));
    }

    #[test]
    fn artifact_sink_options_are_forbidden_in_direct_rustc_passthrough() {
        for option in [
            "trust-dump=mir:/tmp/mir",
            "trust_dump=mir:/tmp/mir",
            "trust-dump=native-bundle:/tmp/native",
            "trust-dump=ir:/tmp/ir",
        ] {
            assert!(targo_owned_z_option(option, true), "direct artifact sink survived: {option}");
        }
    }

    #[test]
    fn rustflags_tokenization_matches_cargo_and_preserves_encoded_empty_arguments() {
        assert_eq!(
            split_plain_rustflags("--cfg\tjoined  -C opt-level=2"),
            ["--cfg\tjoined", "-C", "opt-level=2"]
        );

        let inherited = "--cfg\x1f\x1fvalue\x1f";
        assert_eq!(split_encoded_rustflags(inherited), ["--cfg", "", "value", ""]);
    }

    fn strings(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| (*value).to_string()).collect()
    }

    /// T14a: the lane is the tracked policy alone, in a fixed order, whatever
    /// the caller's environment holds; the sibling Targo appends it to the
    /// project's own flags.
    #[test]
    fn the_lane_is_the_tracked_policy_and_reads_nothing_ambient() {
        let _lock = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|error| error.into_inner());
        let _plain = crate::tests::TestEnvVar::set(
            "RUSTFLAGS",
            "-Zcodegen-backend=/abs/trust_mc.dylib -Ztrust-dump=mir:/tmp/mir -Coverflow-checks=no",
        );
        let _encoded =
            crate::tests::TestEnvVar::set("CARGO_ENCODED_RUSTFLAGS", "-Ztrust-policy=advisory");
        assert_eq!(
            lane_rustflags("L2", Some("trust-cg"), true, true, false),
            strings(&[
                "-Z",
                "trust-verify-level=2",
                "-Z",
                "trust-verify-output=json",
                "-Z",
                "codegen-backend=trust-cg",
                "-Z",
                "trust-cg-output-gate=strict",
                "-C",
                "panic=abort",
                "-C",
                "debuginfo=0",
                "-C",
                "codegen-units=1",
                "-C",
                "overflow-checks=yes",
                "-C",
                "debug-assertions=yes",
            ])
        );
        assert_eq!(
            lane_rustflags("L1", None, false, false, true),
            strings(&[
                "-Z",
                "trust-verify-level=1",
                "-Z",
                "codegen-backend=llvm",
                "-Z",
                "trust-policy=advisory",
            ])
        );
    }

    #[test]
    fn a_probe_lane_carries_the_codegen_contract_and_no_trust_option() {
        assert_eq!(
            cfg_probe_lane_rustflags(Some("trust-cg"), true),
            strings(&[
                "-C",
                "panic=abort",
                "-C",
                "debuginfo=0",
                "-C",
                "codegen-units=1",
                "-C",
                "overflow-checks=yes",
                "-C",
                "debug-assertions=yes",
            ])
        );
        assert!(cfg_probe_lane_rustflags(None, false).is_empty());
        assert!(cfg_probe_lane_rustflags(Some("llvm"), false).is_empty());
    }

    #[test]
    fn a_lane_argument_cannot_carry_the_encoded_delimiter() {
        assert_eq!(
            encode_lane_rustflags(&strings(&["-Z", "trust-proof-artifact-root=/tmp/a b"])).unwrap(),
            "-Z\x1ftrust-proof-artifact-root=/tmp/a b"
        );
        assert!(encode_lane_rustflags(&strings(&["--cfg", "a\x1fb"])).is_err());
        assert_eq!(encode_lane_rustflags(&[]).unwrap(), "");
    }

    #[test]
    fn stripped_inherited_trust_policy_warns_toward_the_per_run_selections() {
        let warning = inherited_trust_rustflags_warning(
            None,
            Some("-C opt-level=2 -Ztrust-verify-level=0 -Z trust-policy=advisory -Zcodegen-backend=llvm"),
        )
        .expect("stripped trust policy must be surfaced");
        assert!(warning.contains("-Ztrust-* in RUSTFLAGS is ignored"), "{warning}");
        assert!(warning.contains(PER_RUN_SELECTIONS), "{warning}");
        assert!(!warning.contains("TRUSTFLAGS"), "T7a: no TRUSTFLAGS replacement: {warning}");
        assert!(warning.contains("-Ztrust-verify-level=0"), "{warning}");
        assert!(warning.contains("-Z trust-policy=advisory"), "{warning}");
        assert!(
            !warning.contains("codegen-backend"),
            "non-trust strips have no Trust replacement: {warning}"
        );

        // Encoded rustflags take precedence, matching Cargo and the merge path,
        // and a budget option names `[trust]`, its only spelling.
        let encoded = inherited_trust_rustflags_warning(
            Some("-Z\x1ftrust-verify-timeout-ms=1\x1f-Ztrust-verify-effort=9"),
            Some("-Ztrust-verify-level=0"),
        )
        .expect("encoded trust policy must be surfaced");
        assert!(encoded.contains("CARGO_ENCODED_RUSTFLAGS"), "{encoded}");
        assert!(encoded.contains("-Z trust-verify-timeout-ms=1"), "{encoded}");
        assert!(encoded.contains("-Ztrust-verify-effort=9"), "{encoded}");
        assert!(encoded.contains("`[trust] effort` and `backstop`"), "{encoded}");
        assert!(!encoded.contains("TRUSTFLAGS"), "{encoded}");
        assert!(!encoded.contains("trust-verify-level"), "{encoded}");

        // Trust-free rustflags stay silent.
        assert_eq!(inherited_trust_rustflags_warning(None, Some("-C opt-level=2")), None);
        assert_eq!(inherited_trust_rustflags_warning(None, None), None);
    }

    /// Trust (platform protocols, plan L1a), adversarial: inherited RUSTFLAGS is not a policy
    /// channel in a verified run, so a `-Ztrust-platform-*` option there is dropped like every
    /// `-Ztrust-*` option (namespace ownership, not the inventory above). The drop must be
    /// ANNOUNCED for each of the five controls in every spelling, never a silent drop of a
    /// property the caller asked for. Since T14a the drop itself is the sibling Targo's
    /// (`without_trust_options` in target_info.rs, pinned there for these controls).
    #[test]
    fn inherited_platform_controls_are_stripped_and_announced() {
        let spellings = [
            "-Ztrust-platform-properties=fd-inherit",
            "-Ztrust_platform_unanalysed=deny",
            "-Ztrust-platform-budget=1",
            "-Ztrust-platform-report=verbose",
            "-Ztrust-platform-dump-facts=/tmp/facts",
        ];
        let plain =
            format!("--cfg kept {} -Z trust-platform-properties=fd-inherit", spellings.join(" "));
        let warning = inherited_trust_rustflags_warning(None, Some(&plain))
            .expect("a stripped platform control must be surfaced");
        for spelling in spellings {
            assert!(warning.contains(spelling), "{spelling} stripped silently: {warning}");
        }
        assert!(warning.contains("-Z trust-platform-properties=fd-inherit"), "{warning}");
        assert!(!warning.contains("--cfg"), "{warning}");

        let encoded =
            format!("-Z\x1ftrust-platform-properties=fd-inherit\x1f{}", spellings.join("\x1f"));
        let warning = inherited_trust_rustflags_warning(Some(&encoded), None)
            .expect("a stripped encoded platform control must be surfaced");
        assert!(warning.contains("CARGO_ENCODED_RUSTFLAGS"), "{warning}");
        assert!(warning.contains("-Z trust-platform-properties=fd-inherit"), "{warning}");
    }

    /// T7a: an ambient TRUSTFLAGS is ignored with one notice naming what was
    /// ignored and where each selection lives; an empty one selects nothing.
    #[test]
    fn an_ambient_trustflags_is_named_once_and_ignored() {
        let notice = ignored_trustflags_notice(
            Some(OsStr::new("-Ztrust-policy=certify -Ztrust-verify-worker-threads=1")),
            None,
        )
        .expect("a non-empty TRUSTFLAGS is named");
        assert!(
            notice.starts_with(
                "TRUSTFLAGS=\"-Ztrust-policy=certify -Ztrust-verify-worker-threads=1\" ignored: \
                 targo trust no longer reads TRUSTFLAGS; "
            ),
            "{notice}"
        );
        assert!(notice.contains(PER_RUN_SELECTIONS), "{notice}");
        assert!(notice.contains(BUDGET_SPELLING), "{notice}");
        assert!(!notice.contains('\n'), "one line: {notice}");
        for flag in ["--certify", "--trust-profile", "--worker-threads", "--config"] {
            assert!(notice.contains(flag), "{flag}: {notice}");
        }

        let both = ignored_trustflags_notice(
            Some(OsStr::new("-Ztrust-verify-level=0")),
            Some(OsStr::new("-Z\x1ftrust-ir-lower=strict")),
        )
        .expect("both channels are named");
        assert!(
            both.starts_with(
                "TRUSTFLAGS=\"-Ztrust-verify-level=0\" and \
                 CARGO_ENCODED_TRUSTFLAGS=\"-Z trust-ir-lower=strict\" ignored"
            ),
            "{both}"
        );
        assert_eq!(ignored_trustflags_notice(Some(OsStr::new("")), Some(OsStr::new(""))), None);
        assert_eq!(ignored_trustflags_notice(None, None), None);

        // A value TRUSTFLAGS used to refuse (not Unicode) is named, not an error.
        #[cfg(unix)]
        {
            use std::os::unix::ffi::OsStrExt;
            let notice =
                ignored_trustflags_notice(Some(OsStr::from_bytes(b"-Ztrust-policy=\xff")), None)
                    .expect("a non-Unicode TRUSTFLAGS is still named");
            assert!(
                notice.starts_with("TRUSTFLAGS=\"-Ztrust-policy=\u{fffd}\" ignored"),
                "{notice}"
            );
        }
    }

    #[test]
    fn direct_safety_override_detection_is_token_aware() {
        assert_eq!(
            find_safety_codegen_override(&["-Coverflow_checks=no".to_string()]).as_deref(),
            Some("-Coverflow_checks=no")
        );
        assert_eq!(
            find_safety_codegen_override(&["-Coverflow-checks=no".to_string()]).as_deref(),
            Some("-Coverflow-checks=no")
        );
        assert_eq!(
            find_safety_codegen_override(&["--codegen=overflow_checks=no".to_string()]).as_deref(),
            Some("--codegen=overflow_checks=no")
        );
        assert_eq!(
            find_safety_codegen_override(&[
                "--codegen".to_string(),
                "debug_assertions=false".to_string(),
            ])
            .as_deref(),
            Some("--codegen debug_assertions=false")
        );
        assert_eq!(
            find_safety_codegen_override(
                &["-C".to_string(), "debug-assertions=false".to_string(),]
            )
            .as_deref(),
            Some("-C debug-assertions=false")
        );
        assert_eq!(
            find_safety_codegen_override(&[
                "-C".to_string(),
                "metadata=overflow-checks=no".to_string(),
            ]),
            None
        );
        assert_eq!(
            find_safety_codegen_override(&[
                "-Coverflow-checks=yes".to_string(),
                "-C".to_string(),
                "debug-assertions=on".to_string(),
            ]),
            None
        );
        assert_eq!(
            canonicalize_strict_safety_codegen_args(&[
                "input.rs".to_string(),
                "-Coverflow-checks=yes".to_string(),
                "-C".to_string(),
                "debug-assertions=on".to_string(),
            ])
            .expect("matching explicit policy should canonicalize"),
            ["input.rs".to_string()]
        );
    }

    #[test]
    fn llvm_plugin_argument_channels_are_recognized_and_removed() {
        for forbidden in [
            vec!["--codegen=llvm_args=-load=/tmp/forged.dylib".to_string()],
            vec!["--codegen".to_string(), "llvm-args=-load=/tmp/forged.dylib".to_string()],
            vec!["-Cllvm_args=-load=/tmp/forged.dylib".to_string()],
        ] {
            assert!(
                find_forbidden_in_process_codegen_arg(&forbidden).is_some(),
                "LLVM plugin channel escaped detection: {forbidden:?}"
            );
        }
    }

    #[test]
    fn direct_trust_cg_codegen_contract_canonicalizes_matches_and_rejects_conflicts() {
        assert_eq!(
            canonicalize_trust_cg_codegen_args(&[
                "input.rs".to_string(),
                "-Cpanic=abort".to_string(),
                "-C".to_string(),
                "debuginfo=none".to_string(),
                "-Ccodegen-units=1".to_string(),
            ])
            .expect("matching trust-cg policy should canonicalize"),
            ["input.rs"]
        );
        for conflicting in [
            vec!["-g".to_string()],
            vec!["-Cpanic=unwind".to_string()],
            vec!["-C".to_string(), "debuginfo=1".to_string()],
            vec!["-Ccodegen-units=2".to_string()],
            vec!["-Ccodegen_units=2".to_string()],
            vec!["-Cincremental=/tmp/cache".to_string()],
            vec!["--codegen=panic=unwind".to_string()],
            vec!["--codegen".to_string(), "codegen_units=2".to_string()],
            vec!["--codegen=incremental=/tmp/cache".to_string()],
        ] {
            assert!(
                canonicalize_trust_cg_codegen_args(&conflicting).is_err(),
                "conflicting direct policy survived: {conflicting:?}"
            );
        }
    }

    #[test]
    fn direct_trust_cg_target_preflight_requires_only_an_explicit_rlib() {
        for admitted in [
            vec!["input.rs".to_string(), "--crate-type=rlib".to_string()],
            vec!["--crate-type".to_string(), "lib".to_string(), "input.rs".to_string()],
        ] {
            validate_direct_trust_cg_rlib_target(&admitted)
                .expect("lib/rlib direct target should be admitted");
        }
        for rejected in [
            vec!["input.rs".to_string()],
            vec!["input.rs".to_string(), "--test".to_string()],
            vec!["input.rs".to_string(), "--crate-type=bin".to_string()],
            vec!["input.rs".to_string(), "--crate-type=rlib,staticlib".to_string()],
        ] {
            assert!(
                validate_direct_trust_cg_rlib_target(&rejected).is_err(),
                "unsupported direct target survived: {rejected:?}"
            );
        }
    }

    const TRUST_MC_BACKEND_DYLIB: &str = "/abs/librustc_codegen_trust_mc.dylib";

    /// S9 / `kani_gate` premise 2: trust-mc engine code reaches trustc only as
    /// an explicitly selected external `-Zcodegen-backend`, so targo trust
    /// check/build never take one. Both `-Z` spellings are owned by the
    /// direct-passthrough check, and the value is not a backend targo could
    /// re-select for the run. In crate mode the sibling Targo drops it from
    /// every rustflags channel under the lane (T14a; its
    /// `lane_inheritance_tests`).
    #[test]
    fn a_trust_mc_backend_is_owned_in_both_spellings_and_never_selectable() {
        let options = [
            format!("codegen-backend={TRUST_MC_BACKEND_DYLIB}"),
            format!("codegen_backend={TRUST_MC_BACKEND_DYLIB}"),
            "codegen-backend=trust_mc".to_string(),
            "codegen-backend=trust-mc".to_string(),
        ];
        for option in &options {
            assert!(targo_owned_z_option(option, true), "targo must own `-Z {option}`");
            let value = option.split_once('=').expect("valued option").1;
            assert!(
                !crate::config::known_codegen_backend_names().contains(&value),
                "`{value}` must not be a known targo backend name"
            );
            assert_eq!(
                crate::config::normalize_codegen_backend(value),
                None,
                "`{value}` must not be selectable through [trust] or --codegen-backend"
            );
        }
    }
}
