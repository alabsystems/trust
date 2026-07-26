// RUSTFLAGS assembly: merge user flags with tracked verifier policy and the
// selected codegen backend while removing ambient attempts to own Targo policy.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::borrow::Cow;
use std::env;

use crate::config::DEFAULT_CODEGEN_BACKEND;

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

/// Convert level string to numeric value for -Z trust-verify-level.
pub(crate) fn level_to_num(level: &str) -> u8 {
    match level {
        "L0" => 0,
        "L1" => 1,
        "L2" => 2,
        _ => 0,
    }
}

pub(super) fn append_codegen_backend_rustflag(
    flags: &mut String,
    selected_codegen_backend: Option<&str>,
    allow_l0_gaps: bool,
) {
    let backend = effective_codegen_backend(selected_codegen_backend);
    if !args_have_z_option(&split_plain_rustflags(flags), "codegen-backend") {
        if !flags.is_empty() {
            flags.push(' ');
        }
        flags.push_str("-Z ");
        flags.push_str(&format!("codegen-backend={backend}"));
    }
    if backend == "trust-cg"
        && !args_have_z_option(&split_plain_rustflags(flags), "trust-cg-output-gate")
    {
        flags.push_str(" -Z trust-cg-output-gate=");
        flags.push_str(trust_cg_output_gate(allow_l0_gaps));
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

fn z_option_bool_value(option: &str, name: &str) -> Option<bool> {
    let (_option_name, value) = option
        .split_once('=')
        .map_or((option, None), |(option_name, value)| (option_name, Some(value)));

    (canonical_rustc_option_name(option) == name).then(|| rustc_bool_value(value)).flatten()
}

fn args_have_z_bool_flag(args: &[&str], name: &str, expected: bool) -> bool {
    let compact_prefix = format!("-Z{name}");
    let mut idx = 0;
    while idx < args.len() {
        let arg = args[idx];
        if arg == "-Z" {
            if args.get(idx + 1).and_then(|option| z_option_bool_value(option, name))
                == Some(expected)
            {
                return true;
            }
            idx += 2;
            continue;
        }

        if let Some(option) = arg.strip_prefix("-Z") {
            if !option.is_empty() && z_option_bool_value(option, name) == Some(expected) {
                return true;
            }
        }

        if arg == compact_prefix {
            return expected;
        }

        idx += 1;
    }

    false
}

fn split_plain_rustflags(flags: &str) -> Vec<&str> {
    // Match Cargo/Targo's literal-space protocol exactly. Shell quoting is not
    // interpreted, and tabs/newlines inside one segment remain part of that
    // argument rather than silently becoming new compiler arguments here.
    flags.split(' ').map(str::trim).filter(|arg| !arg.is_empty()).collect()
}

fn split_encoded_rustflags(flags: &str) -> Vec<&str> {
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
            if targo_owned_safety_codegen_option(option) {
                if safety_codegen_option_value(option) != Some(true) {
                    return Some(if split {
                        format!("{argument} {option}")
                    } else {
                        argument.clone()
                    });
                }
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

fn args_have_z_option<S: AsRef<str>>(args: &[S], name: &str) -> bool {
    let mut index = 0;
    while index < args.len() {
        let argument = args[index].as_ref();
        let option = if argument == "-Z" {
            index += 1;
            args.get(index).map(AsRef::as_ref)
        } else {
            argument.strip_prefix("-Z").filter(|option| !option.is_empty())
        };
        if option.is_some_and(|option| canonical_rustc_option_name(option) == name) {
            return true;
        }
        index += 1;
    }
    false
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

/// List the inherited `-Ztrust-*`-family options that a verified run strips
/// (see `sanitize_inherited_z_options`). The crate-mode pipeline surfaces
/// these as a warning pointing at TRUSTFLAGS, the sanctioned override channel,
/// so the policy filter is no longer silent. Built on `targo_owned_z_option`
/// so the warning can never disagree with the sanitizer about what is removed;
/// non-trust strips (codegen-backend, llvm-plugins) stay out of the warning
/// because TRUSTFLAGS is not their replacement channel.
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
    } else if let Some(plain) = plain {
        (
            "RUSTFLAGS",
            split_plain_rustflags(plain).into_iter().map(str::to_string).collect::<Vec<_>>(),
        )
    } else {
        return None;
    };
    let stripped = stripped_inherited_trust_options(&args);
    if stripped.is_empty() {
        return None;
    }
    Some(format!(
        "warning: -Ztrust-* in {source} is ignored; set TRUSTFLAGS instead (ignored: {})",
        stripped.join(", ")
    ))
}

/// Remove inherited options whose effective value is owned by targo-trust.
/// Keeping a valid-but-different inherited value used to let ambient RUSTFLAGS
/// lower the requested proof level, scope verification to the wrong crate, or
/// select a backend different from the one recorded in the report. Unrelated
/// rustc flags are preserved byte-for-token.
fn sanitize_inherited_z_options(
    args: impl IntoIterator<Item = String>,
    replace_codegen_backend: bool,
) -> Vec<String> {
    let args = args.into_iter().collect::<Vec<_>>();
    let mut sanitized = Vec::with_capacity(args.len());
    let mut index = 0;
    while index < args.len() {
        if args[index] == "-Z"
            && args
                .get(index + 1)
                .is_some_and(|option| targo_owned_z_option(option, replace_codegen_backend))
        {
            index += 2;
            continue;
        }
        if args[index]
            .strip_prefix("-Z")
            .filter(|option| !option.is_empty())
            .is_some_and(|option| targo_owned_z_option(option, replace_codegen_backend))
        {
            index += 1;
            continue;
        }
        sanitized.push(args[index].clone());
        index += 1;
    }
    sanitized
}

fn sanitize_inherited_options(
    args: impl IntoIterator<Item = String>,
    replace_codegen_backend: bool,
    force_strict_safety_checks: bool,
    force_trust_cg_codegen_contract: bool,
) -> Vec<String> {
    let args = sanitize_inherited_z_options(args, replace_codegen_backend);
    let mut sanitized = Vec::with_capacity(args.len());
    let mut index = 0;
    while index < args.len() {
        if force_trust_cg_codegen_contract && args[index] == "-g" {
            index += 1;
            continue;
        }
        let (option, consumed, _) = rustc_codegen_option_at(&args, index);
        if option.is_some_and(|option| {
            forbidden_in_process_codegen_option(option)
                || (force_strict_safety_checks && targo_owned_safety_codegen_option(option))
                || (force_trust_cg_codegen_contract && targo_owned_trust_cg_codegen_option(option))
        }) {
            index += consumed;
            continue;
        }
        sanitized.push(args[index].clone());
        index += 1;
    }
    sanitized
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

fn append_trust_cg_codegen_rustflags(flags: &mut String) {
    if !flags.is_empty() {
        flags.push(' ');
    }
    flags.push_str("-C panic=abort -C debuginfo=0 -C codegen-units=1");
}

pub(super) fn append_strict_safety_check_args(args: &mut Vec<String>) {
    args.extend([
        "-C".to_string(),
        "overflow-checks=yes".to_string(),
        "-C".to_string(),
        "debug-assertions=yes".to_string(),
    ]);
}

fn append_strict_safety_check_rustflags(flags: &mut String) {
    if !flags.is_empty() {
        flags.push(' ');
    }
    flags.push_str("-C overflow-checks=yes -C debug-assertions=yes");
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

pub(super) fn append_verification_mode_rustflags(flags: &mut String, allow_l0_gaps: bool) {
    // Verification and strictness are batteries-on. Only the explicit
    // advisory loosener needs a mode flag.
    if allow_l0_gaps && !args_have_z_bool_flag(&split_plain_rustflags(flags), "trust-policy=advisory", true) {
        if !flags.is_empty() {
            flags.push(' ');
        }
        flags.push_str("-Z trust-policy=advisory");
    }
}

fn append_verification_mode_encoded_args(args: &mut Vec<String>, allow_l0_gaps: bool) {
    let refs = args.iter().map(String::as_str).collect::<Vec<_>>();
    if allow_l0_gaps && !args_have_z_bool_flag(&refs, "trust-policy=advisory", true) {
        args.push("-Z".to_string());
        args.push("trust-policy=advisory".to_string());
    }
}

pub(super) fn append_verification_mode_args(cmd_args: &mut Vec<String>, allow_l0_gaps: bool) {
    if allow_l0_gaps {
        cmd_args.push("-Z".to_string());
        cmd_args.push("trust-policy=advisory".to_string());
    }
}

#[cfg(test)]
pub(crate) fn merged_rustflags(level: &str) -> String {
    merged_rustflags_with_backend(level, None)
}

#[cfg(test)]
pub(crate) fn merged_rustflags_with_backend(
    level: &str,
    selected_codegen_backend: Option<&str>,
) -> String {
    merged_rustflags_with_json_transport(level, selected_codegen_backend, true)
}

#[cfg(test)]
pub(crate) fn merged_rustflags_with_json_transport(
    level: &str,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
) -> String {
    merged_rustflags_with_options(
        level,
        selected_codegen_backend,
        supports_json_transport,
        false,
        false,
    )
}

pub(crate) fn merged_rustflags_with_options(
    level: &str,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
    strict_artifact_policy: bool,
    allow_l0_gaps: bool,
) -> String {
    let inherited = env::var("RUSTFLAGS").unwrap_or_default();
    let inherited = split_plain_rustflags(&inherited).into_iter().map(str::to_string);
    let mut merged = sanitize_inherited_options(
        inherited,
        true,
        strict_artifact_policy,
        selected_codegen_backend == Some("trust-cg"),
    )
    .join(" ");
    if !merged.is_empty() {
        merged.push(' ');
    }
    merged.push_str(&format!("-Z trust-verify-level={}", level_to_num(level)));
    if supports_json_transport {
        merged.push_str(" -Z trust-verify-output=json");
    }
    append_codegen_backend_rustflag(&mut merged, selected_codegen_backend, allow_l0_gaps);
    append_verification_mode_rustflags(&mut merged, allow_l0_gaps);
    if selected_codegen_backend == Some("trust-cg") {
        append_trust_cg_codegen_rustflags(&mut merged);
    }
    if strict_artifact_policy {
        append_strict_safety_check_rustflags(&mut merged);
    }
    merged
}

pub(crate) enum CargoRustflags {
    Plain(String),
    Encoded(String),
}

fn append_codegen_backend_encoded_arg(
    args: &mut Vec<String>,
    selected_codegen_backend: Option<&str>,
    allow_l0_gaps: bool,
) {
    let backend = effective_codegen_backend(selected_codegen_backend);
    if !args_have_z_option(args, "codegen-backend") {
        args.push("-Z".to_string());
        args.push(format!("codegen-backend={backend}"));
    }
    if backend == "trust-cg" && !args_have_z_option(args, "trust-cg-output-gate") {
        args.push("-Z".to_string());
        args.push(format!("trust-cg-output-gate={}", trust_cg_output_gate(allow_l0_gaps)));
    }
}

fn merged_encoded_rustflags_with_options(
    encoded: &str,
    level: &str,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
    strict_artifact_policy: bool,
    allow_l0_gaps: bool,
) -> String {
    let inherited = split_encoded_rustflags(encoded).into_iter().map(str::to_string);
    let mut args = sanitize_inherited_options(
        inherited,
        true,
        strict_artifact_policy,
        selected_codegen_backend == Some("trust-cg"),
    );

    args.push("-Z".to_string());
    args.push(format!("trust-verify-level={}", level_to_num(level)));
    if supports_json_transport {
        args.push("-Z".to_string());
        args.push("trust-verify-output=json".to_string());
    }
    append_codegen_backend_encoded_arg(&mut args, selected_codegen_backend, allow_l0_gaps);
    append_verification_mode_encoded_args(&mut args, allow_l0_gaps);
    if selected_codegen_backend == Some("trust-cg") {
        append_trust_cg_codegen_args(&mut args);
    }
    if strict_artifact_policy {
        append_strict_safety_check_args(&mut args);
    }
    args.join("\x1f")
}

pub(crate) fn merged_cargo_rustflags_with_options(
    level: &str,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
    strict_artifact_policy: bool,
    allow_l0_gaps: bool,
) -> CargoRustflags {
    match env::var("CARGO_ENCODED_RUSTFLAGS") {
        // Match Cargo's precedence: when encoded rustflags are present, Cargo
        // ignores plain RUSTFLAGS instead of merging the two representations.
        Ok(flags) => CargoRustflags::Encoded(merged_encoded_rustflags_with_options(
            &flags,
            level,
            selected_codegen_backend,
            supports_json_transport,
            strict_artifact_policy,
            allow_l0_gaps,
        )),
        Err(_) => CargoRustflags::Plain(merged_rustflags_with_options(
            level,
            selected_codegen_backend,
            supports_json_transport,
            strict_artifact_policy,
            allow_l0_gaps,
        )),
    }
}

#[cfg(test)]
mod option_token_tests {
    use super::*;

    #[test]
    fn z_option_detection_ignores_unrelated_substrings_and_accepts_both_spellings() {
        assert!(!args_have_z_option(
            &["-C", "metadata=trust-verify-level=fake"],
            "trust-verify-level"
        ));
        assert!(args_have_z_option(&["-Z", "trust-verify-level=1"], "trust-verify-level"));
        assert!(args_have_z_option(&["-Ztrust-verify-level=2"], "trust-verify-level"));
        assert!(args_have_z_option(&["-Ztrust_verify_level=2"], "trust-verify-level"));
    }

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

        let sanitized = sanitize_inherited_options(
            [
                "-Ztrust_verify_level=0".to_string(),
                "-Coverflow_checks=no".to_string(),
                "-Ccodegen_units=8".to_string(),
                "-Copt-level=2".to_string(),
            ],
            false,
            true,
            true,
        );
        assert_eq!(sanitized, ["-Copt-level=2"]);

        let sanitized_monitor_markers = sanitize_inherited_options(
            [
                "-Z".to_string(),
                "trust-targo-test-monitor".to_string(),
                "-Ztrust-targo-test-monitor".to_string(),
                "-Ztrust_targo_test_monitor".to_string(),
                "--cfg".to_string(),
                "kept".to_string(),
            ],
            false,
            true,
            true,
        );
        assert_eq!(sanitized_monitor_markers, ["--cfg", "kept"]);
    }

    #[test]
    fn targo_owns_the_complete_trust_session_option_namespace() {
        // This inventory documents the current rustc_session surface, while
        // the future sentinel verifies that ownership does not depend on this
        // list being updated in lockstep with the compiler.
        for option in [
            "trust-certified-test-monitors",
            "trust-cg-output-gate",
            "trust-dump",
            "trust-ir-flip",
            "trust-ir-lower",
            "trust-no-r1",
            "trust-proof-artifact-root",
            "trust-targo-test-monitor",
            "trust-verify-ay-path",
            "trust-verify-crate-role",
            "trust-policy",
            "trust-verify",
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
    fn artifact_sink_options_cannot_pass_through_plain_rustflags() {
        let inherited = split_plain_rustflags(
            "--cfg kept -Ztrust-dump=mir:/tmp/mir -Z trust_dump=native-bundle:/tmp/native \
             -Ztrust-dump=ir:/tmp/ir",
        )
        .into_iter()
        .map(str::to_string);
        let sanitized = sanitize_inherited_z_options(inherited, true);
        assert_eq!(sanitized, ["--cfg", "kept"]);
    }

    #[test]
    fn artifact_sink_options_cannot_pass_through_encoded_rustflags() {
        let merged = merged_encoded_rustflags_with_options(
            "--cfg\x1fkept\x1f-Ztrust-dump=mir:/tmp/mir\x1f-Z\x1ftrust_dump=native-bundle:/tmp/native\x1f-Ztrust-dump=ir:/tmp/ir",
            "L1",
            None,
            true,
            false,
            false,
        );
        let args = split_encoded_rustflags(&merged);
        assert!(args.windows(2).any(|pair| pair == ["--cfg", "kept"]));
        for option in ["trust-dump"] {
            assert!(!args_have_z_option(&args, option), "encoded artifact sink survived: {args:?}");
        }
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
    fn encoded_merge_replaces_owned_compact_z_options_but_not_metadata_values() {
        let compact = merged_encoded_rustflags_with_options(
            "-Ztrust-verify-level=2\x1f-Ztrust-verify-output=both\x1f-Ztrust-verify-target=wrong",
            "L1",
            None,
            true,
            false,
            false,
        );
        assert_eq!(compact.matches("trust-verify-level=").count(), 1);
        assert_eq!(compact.matches("trust-verify-output=").count(), 1);
        assert!(compact.contains("trust-verify-level=1"));
        assert!(compact.contains("trust-verify-output=json"));
        assert!(!compact.contains("trust-verify-target"));

        let unrelated = merged_encoded_rustflags_with_options(
            "-C\x1fmetadata=trust-verify-level=fake",
            "L1",
            None,
            false,
            false,
            false,
        );
        assert!(unrelated.contains("trust-verify-level=1"));
    }

    #[test]
    fn rustflags_tokenization_matches_cargo_and_preserves_encoded_empty_arguments() {
        assert_eq!(
            split_plain_rustflags("--cfg\tjoined  -C opt-level=2"),
            ["--cfg\tjoined", "-C", "opt-level=2"]
        );

        let inherited = "--cfg\x1f\x1fvalue\x1f";
        assert_eq!(split_encoded_rustflags(inherited), ["--cfg", "", "value", ""]);
        let merged =
            merged_encoded_rustflags_with_options(inherited, "L1", None, false, false, false);
        assert!(
            merged.starts_with("--cfg\x1f\x1fvalue\x1f\x1f-Z\x1f"),
            "encoded empty arguments were not preserved: {merged:?}"
        );
    }

    #[test]
    fn inherited_policy_and_selected_backend_are_canonicalized() {
        let sanitized = sanitize_inherited_z_options(
            [
                "-C".to_string(),
                "opt-level=2".to_string(),
                "-Zcodegen-backend=llvm".to_string(),
                "-Z".to_string(),
                "trust-policy=advisory".to_string(),
                "-Ztrust-verify-target=wrong".to_string(),
                "-Ztrust-compiler-cache=no".to_string(),
                "-Ztrust-proof-artifact-root=/tmp/forged".to_string(),
            ],
            true,
        );
        assert_eq!(sanitized, ["-C".to_string(), "opt-level=2".to_string()]);

        let merged = merged_encoded_rustflags_with_options(
            "-Zcodegen-backend=llvm\x1f-Ztrust-policy=advisory\x1f-Ztrust-verify-target=wrong\x1f-Ztrust-compiler-cache=no",
            "L2",
            Some("trust-cg"),
            true,
            true,
            false,
        );
        assert!(!merged.contains("codegen-backend=llvm"));
        assert!(!merged.contains("trust-policy=advisory"));
        assert!(!merged.contains("trust-verify-target=wrong"));
        assert!(!merged.contains("trust-compiler-cache"));
        assert!(merged.contains("codegen-backend=trust-cg"));
        assert!(merged.contains("trust-cg-output-gate=strict"));
        assert!(!merged.contains("trust-verify-target"));
    }

    #[test]
    fn stripped_inherited_trust_policy_warns_toward_trustflags() {
        let warning = inherited_trust_rustflags_warning(
            None,
            Some("-C opt-level=2 -Ztrust-verify-level=0 -Z trust-policy=advisory -Zcodegen-backend=llvm"),
        )
        .expect("stripped trust policy must be surfaced");
        assert!(warning.contains("-Ztrust-* in RUSTFLAGS is ignored"), "{warning}");
        assert!(warning.contains("set TRUSTFLAGS instead"), "{warning}");
        assert!(warning.contains("-Ztrust-verify-level=0"), "{warning}");
        assert!(warning.contains("-Z trust-policy=advisory"), "{warning}");
        assert!(
            !warning.contains("codegen-backend"),
            "non-trust strips have no TRUSTFLAGS replacement: {warning}"
        );

        // Encoded rustflags take precedence, matching Cargo and the merge path.
        let encoded = inherited_trust_rustflags_warning(
            Some("-Z\x1ftrust-verify-timeout-ms=1"),
            Some("-Ztrust-verify-level=0"),
        )
        .expect("encoded trust policy must be surfaced");
        assert!(encoded.contains("CARGO_ENCODED_RUSTFLAGS"), "{encoded}");
        assert!(encoded.contains("-Z trust-verify-timeout-ms=1"), "{encoded}");
        assert!(!encoded.contains("trust-verify-level"), "{encoded}");

        // Trust-free rustflags stay silent.
        assert_eq!(inherited_trust_rustflags_warning(None, Some("-C opt-level=2")), None);
        assert_eq!(inherited_trust_rustflags_warning(None, None), None);
    }

    #[test]
    fn strict_safety_checks_replace_both_codegen_option_spellings() {
        let sanitized = sanitize_inherited_options(
            [
                "-Coverflow-checks=no".to_string(),
                "-C".to_string(),
                "debug-assertions=off".to_string(),
                "--codegen=overflow_checks=no".to_string(),
                "--codegen".to_string(),
                "debug_assertions=off".to_string(),
                "-Copt-level=2".to_string(),
            ],
            false,
            true,
            false,
        );
        assert_eq!(sanitized, ["-Copt-level=2".to_string()]);

        let mut args = sanitized;
        append_strict_safety_check_args(&mut args);
        assert_eq!(
            args,
            ["-Copt-level=2", "-C", "overflow-checks=yes", "-C", "debug-assertions=yes",]
        );
    }

    #[test]
    fn advisory_safety_policy_preserves_inherited_profile_fidelity() {
        let inherited = vec![
            "-Coverflow-checks=no".to_string(),
            "-C".to_string(),
            "debug-assertions=no".to_string(),
        ];
        assert_eq!(sanitize_inherited_options(inherited.clone(), false, false, false), inherited);
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
            assert!(
                sanitize_inherited_options(forbidden, true, false, false).is_empty(),
                "LLVM plugin channel escaped inherited sanitation"
            );
        }
    }

    #[test]
    fn trust_cg_codegen_contract_replaces_inherited_plain_and_encoded_values() {
        let sanitized = sanitize_inherited_options(
            [
                "-g".to_string(),
                "-Cpanic=unwind".to_string(),
                "-C".to_string(),
                "debuginfo=2".to_string(),
                "-Ccodegen-units=16".to_string(),
                "-C".to_string(),
                "incremental=/tmp/hostile".to_string(),
                "--codegen=incremental=/tmp/hostile-long".to_string(),
                "--codegen".to_string(),
                "codegen_units=32".to_string(),
                "-Copt-level=3".to_string(),
            ],
            true,
            false,
            true,
        );
        assert_eq!(sanitized, ["-Copt-level=3"]);

        let merged = merged_encoded_rustflags_with_options(
            "-g\x1f-Cpanic=unwind\x1f-C\x1fdebuginfo=1\x1f-Ccodegen-units=8\x1f-Cincremental=/tmp/cache",
            "L1",
            Some("trust-cg"),
            true,
            false,
            false,
        );
        let args = merged.split('\x1f').collect::<Vec<_>>();
        assert!(!args.iter().any(|arg| *arg == "-g"));
        assert_eq!(args.iter().filter(|arg| **arg == "panic=abort").count(), 1);
        assert_eq!(args.iter().filter(|arg| **arg == "debuginfo=0").count(), 1);
        assert_eq!(args.iter().filter(|arg| **arg == "codegen-units=1").count(), 1);
        assert!(!args.iter().any(|arg| arg.starts_with("incremental=")));
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
}
