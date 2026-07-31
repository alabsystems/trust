//! The Rust compiler.
//!
//! # Note
//!
//! This API is completely unstable and subject to change.

// tidy-alphabetical-start
#![feature(decl_macro)]
#![feature(file_buffered)]
#![feature(panic_backtrace_config)]
#![feature(panic_update_hook)]
#![feature(trim_prefix_suffix)]
#![feature(try_blocks)]
// tidy-alphabetical-end

use std::cmp::max;
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{OsStr, OsString};
use std::fmt::Write as _;
use std::fs::{self, File};
use std::io::{self, IsTerminal, Read, Write};
use std::panic::{self, PanicHookInfo};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio, Termination};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;
use std::{env, str};

use rustc_ast as ast;
use rustc_codegen_ssa::traits::CodegenBackend;
use rustc_codegen_ssa::{CodegenError, CompiledModules};
use rustc_data_structures::profiling::{
    TimePassesFormat, get_resident_set_size, print_time_passes_entry,
};
pub use rustc_errors::catch_fatal_errors;
use rustc_errors::emitter::stderr_destination;
use rustc_errors::{ColorConfig, DiagCtxt, ErrCode, PResult, markdown};
use rustc_feature::find_gated_cfg;
use rustc_hir::attrs::AttributeKind;
use rustc_hir::def::DefKind;
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::lang_items::LangItem;
use rustc_hir::{self, Attribute};
// This avoids a false positive with `-Wunused_crate_dependencies`.
// `rust_index` isn't used in this crate's code, but it must be named in the
// `Cargo.toml` for the `rustc_randomized_layouts` feature.
use rustc_index as _;
use rustc_interface::passes::collect_crate_types;
use rustc_interface::util::{self, get_codegen_backend};
use rustc_interface::{Linker, create_and_enter_global_ctxt, interface, passes};
use rustc_lint::unerased_lint_store;
use rustc_metadata::creader::MetadataLoader;
use rustc_metadata::locator;
use rustc_middle::hir::nested_filter::OnlyBodies;
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
use rustc_middle::middle::dependency_format::Linkage;
use rustc_middle::middle::exported_symbols::ExportedSymbol;
use rustc_middle::ty::TyCtxt;
use rustc_parse::lexer::StripTokens;
use rustc_parse::{new_parser_from_file, new_parser_from_source_str, unwrap_or_emit_fatal};
use rustc_session::config::{
    CG_OPTIONS, CrateType, ErrorOutputType, Input, OptionDesc, OutFileName, OutputType, Sysroot,
    UnstableOptions, Z_OPTIONS, nightly_options, parse_target_triple,
};
use rustc_session::getopts::{self, Matches};
use rustc_session::lint::{Lint, LintId};
use rustc_session::output::invalid_output_for_target;
use rustc_session::{EarlyDiagCtxt, Session, config};
use rustc_span::def_id::{CrateNum, DefId, DefIndex, LOCAL_CRATE};
use rustc_span::{DUMMY_SP, FileName};
use rustc_target::json::ToJson;
use rustc_target::spec::{Target, TargetTuple};
use tracing::trace;

#[allow(unused_macros)]
macro do_not_use_print($($t:tt)*) {
    std::compile_error!(
        "Don't use `print` or `println` here, use `safe_print` or `safe_println` instead"
    )
}

#[allow(unused_macros)]
macro do_not_use_safe_print($($t:tt)*) {
    std::compile_error!("Don't use `safe_print` or `safe_println` here, use `println_info` instead")
}

// This import blocks the use of panicking `print` and `println` in all the code
// below. Please use `safe_print` and `safe_println` to avoid ICE when
// encountering an I/O error during print.
#[allow(unused_imports)]
use {do_not_use_print as print, do_not_use_print as println};

pub mod args;
pub mod pretty;
#[macro_use]
mod print;
pub mod highlighter;
mod session_diagnostics;

// Keep the OS parts of this `cfg` in sync with the `cfg` on the `libc`
// dependency in `compiler/rustc_driver/Cargo.toml`, to keep
// `-Wunused-crated-dependencies` satisfied.
#[cfg(all(not(miri), unix, any(target_env = "gnu", target_os = "macos")))]
mod signal_handler;

#[cfg(not(all(not(miri), unix, any(target_env = "gnu", target_os = "macos"))))]
mod signal_handler {
    /// On platforms which don't support our signal handler's requirements,
    /// simply use the default signal handler provided by std.
    pub(super) fn install() {}
}

use crate::session_diagnostics::{
    CantEmitMir, RLinkEmptyVersionNumber, RLinkEncodingVersionMismatch, RLinkRustcVersionMismatch,
    RLinkWrongFileType, RlinkCorruptFile, RlinkNotAFile, RlinkUnableToRead, UnstableFeatureUsage,
};

/// Whether anything Trust-specific runs at all: verification, direct TrustIR
/// lowering, or both. Direct lowering already subsumes verification, so this is
/// the resolved lowering predicate.
#[allow(rustc::bad_opt_access)]
fn trust_semantics_are_active(opts: &config::Options) -> bool {
    trust_ir_lower_is_active(opts)
}

/// Whether the direct source (THIR) -> Trust-IR frontend runs for `opts`.
///
/// Answers for a raw command line as well as for one canonicalization has
/// already stamped, so an option-domain check cannot disagree with the
/// compilation it is validating.
#[allow(rustc::bad_opt_access)]
fn trust_ir_lower_is_active(opts: &config::Options) -> bool {
    rustc_session::trust_ir_lower_enabled_by_flags(
        opts.unstable_opts.trust_verify,
        opts.unstable_opts.trust_ir_lower,
    )
}

/// Whether the caller explicitly asked for direct lowering. Distinct from
/// [`trust_ir_lower_is_active`]: the requests that must be *rejected* as
/// inert — a burn-in perturbation, an artifact dump with verification off —
/// are the ones the user has to spell out, not the ones verification implies.
#[allow(rustc::bad_opt_access)]
fn trust_ir_lower_is_requested(opts: &config::Options) -> bool {
    // `strict` is a request too — it is `on` plus fail-closed reporting, not a separate mode.
    opts.unstable_opts.trust_ir_lower.is_some_and(config::TrustIrLower::runs)
}

#[allow(rustc::bad_opt_access)]
fn trust_strict_policy_is_active(opts: &config::Options) -> bool {
    rustc_session::trust_verification_enabled_by_flags(opts.unstable_opts.trust_verify)
        && opts.unstable_opts.trust_policy.is_strict()
}

#[allow(rustc::bad_opt_access)]
fn trust_callback_changed_contract_checks(
    command_line_value: Option<bool>,
    opts: &config::Options,
) -> bool {
    // Keep the upstream field mutable for an explicitly vanilla frontend, but
    // do not let a callback erase an explicitly supplied retired option before
    // the post-callback Trust domain check observes it. Setting the field in a
    // Trust compilation is covered by the same guard as well.
    trust_semantics_are_active(opts) && command_line_value != opts.unstable_opts.contract_checks
}

fn validate_trust_environment(opts: &config::Options) {
    let Some(key) =
        config::forbidden_trust_environment_key(opts, env::vars_os().map(|(key, _)| key))
    else {
        return;
    };
    // Do not `remove_var` here. `run_compiler` is a reusable in-process API and
    // the embedding process may already have unrelated threads (or a global
    // worker pool) reading its environment. Mutating the process environment
    // would therefore violate `remove_var`'s safety contract. Rejecting the
    // invocation is both race-free and fail-closed: untracked state can neither
    // affect this compilation nor be silently erased for the caller.
    EarlyDiagCtxt::new(opts.error_format).early_fatal(config::trust_environment_error(&key));
}

#[allow(rustc::bad_opt_access)]
fn trust_targo_test_monitor_domain_error(
    opts: &config::Options,
    marker: Option<&OsStr>,
) -> Option<&'static str> {
    let selected = opts.unstable_opts.trust_targo_test_monitor;
    match (selected, marker) {
        (false, None) => None,
        (true, None) => Some(
            "-Ztrust-targo-test-monitor is a reserved internal Targo option and cannot be selected directly",
        ),
        (false, Some(_)) => Some(
            "TRUST_TARGO_TEST_MONITOR_SESSION was supplied to a compiler unit without Targo's tracked per-unit monitor selection",
        ),
        (true, Some(marker)) => {
            let Some(marker) =
                marker.to_str().filter(|marker| !marker.is_empty() && marker.trim() == *marker)
            else {
                return Some(
                    "Targo certified-monitor session is empty, padded, or not valid Unicode",
                );
            };
            if opts.unstable_opts.trust_verify_session.as_deref() != Some(marker) {
                return Some(
                    "Targo certified-monitor session does not match -Ztrust-verify-session",
                );
            }
            None
        }
    }
}

#[allow(rustc::bad_opt_access)]
fn trust_targo_test_monitor_sysroot_error(opts: &config::Options) -> Option<&'static str> {
    if !opts.unstable_opts.trust_targo_test_monitor {
        return None;
    }

    if opts.cg.prefer_dynamic {
        return Some(
            "evidence-grade certified-monitor tests require a static Rust dependency closure; -Cprefer-dynamic is unavailable",
        );
    }

    // Recompute this from the running compiler rather than trusting the
    // mutable Options::sysroot.default field: an embedding callback can edit
    // both the explicit and default paths. An explicit --sysroot spelling is
    // harmless only when it resolves to the compiler's own toolchain sysroot
    // (bootstrap/compiletest use that form).
    let compiler_default = Sysroot::new(None);
    let authenticated = fs::canonicalize(opts.sysroot.path())
        .ok()
        .zip(fs::canonicalize(compiler_default.path()).ok())
        .is_some_and(|(active, expected)| active == expected);
    (!authenticated).then_some(
        "evidence-grade certified-monitor tests require the running compiler's authenticated sysroot; caller --sysroot overrides are unavailable",
    )
}

#[allow(rustc::bad_opt_access)]
fn trust_strict_policy_option_error(opts: &config::Options) -> Option<&'static str> {
    if !trust_strict_policy_is_active(opts) {
        return None;
    }
    if opts.unstable_opts.trust_cg_output_gate == "off" {
        return Some(
            "-Ztrust-cg-output-gate=off is incompatible with batteries-on strict Trust \
             verification; use -Ztrust-verify=off for a vanilla compile",
        );
    }
    None
}

/// Canonicalize effective Trust policy and reject combinations that cannot be
/// honored. A successful compiler exit with no requested evidence is more dangerous than
/// an ordinary bad flag: downstream automation can mistake absence for a clean
/// result. Keep this validation after callbacks so compiler frontends cannot
/// accidentally construct an unwired combination either.
#[allow(rustc::bad_opt_access)]
fn normalize_and_validate_trust_options(opts: &mut config::Options) {
    let marker = env::var_os("TRUST_TARGO_TEST_MONITOR_SESSION");
    let error = trust_targo_test_monitor_domain_error(opts, marker.as_deref())
        .or_else(|| trust_targo_test_monitor_sysroot_error(opts))
        .or_else(|| trust_option_domain_error(opts))
        .or_else(|| trust_strict_policy_option_error(opts))
        .or_else(|| trust_dump_domain_error(opts));

    if let Some(error) = error {
        EarlyDiagCtxt::new(opts.error_format).early_fatal(error);
    }

    // Store strict verification's effective output and safety-check policy
    // before Session/dependency hashes are built. This makes raw-full and
    // Targo's explicit spellings converge on one canonical compilation. The
    // codegen backend independently enforces the output rule for custom
    // drivers that do not pass through this normalization.
    canonicalize_trust_options(opts);
}

#[allow(rustc::bad_opt_access)]
fn trust_dump_domain_error(opts: &config::Options) -> Option<&'static str> {
    let dump = &opts.unstable_opts.trust_dump;
    let verifying =
        rustc_session::trust_verification_enabled_by_flags(opts.unstable_opts.trust_verify);
    if dump.ir.is_some() && !trust_ir_lower_is_requested(opts) && !verifying {
        return Some(
            "-Ztrust-dump=ir:<dir> requires batteries-on verification or -Ztrust-ir-lower",
        );
    }
    if (dump.mir.is_some() || dump.native_bundle.is_some()) && !verifying {
        return Some(
            "-Ztrust-dump=mir:<dir> and -Ztrust-dump=native-bundle:<dir> require batteries-on \
             Trust verification",
        );
    }
    if dump.mir_only && !opts.unstable_opts.trust_policy.is_advisory() {
        return Some(
            "-Ztrust-dump=mir-only:<dir> skips proof dispatch and therefore requires the \
             nonfatal -Ztrust-policy=advisory",
        );
    }
    None
}

#[allow(rustc::bad_opt_access)]
fn canonicalize_trust_options(opts: &mut config::Options) {
    // P1 direct Rust frontend: batteries-on builds exercise typed source ->
    // Trust-IR, its differential oracle, and eligible codegen migration instead
    // of leaving that producer behind an unwired experimental flag. Ratified P9
    // still retains the capability-complete MIR proving routes until the direct
    // source/router routes reach verdict parity; this option is not a proof-path
    // precondition.
    //
    // The frontend is therefore NOT optional under verification. Resolving the
    // request here, before any Session or dependency hash exists, is what makes
    // `trustc x.rs`, `trustc -Ztrust-ir-lower x.rs` and
    // `trustc -Ztrust-ir-lower=no x.rs` one tracked identity instead of three
    // hashes for one compilation; the same collapse applies to the two off
    // spellings in the `-Ztrust-verify=off` lane. Nothing downstream should ever
    // observe an unresolved request.
    // A `strict` request must survive canonicalization. Resolving "does the frontend run" and
    // stamping `On` would silently drop "and fail closed on a body it cannot lower" — the
    // resolved answer has to carry both halves, not just the one this predicate asks about.
    let resolved_ir_lower = if opts.unstable_opts.trust_ir_lower
        == Some(config::TrustIrLower::Strict)
    {
        config::TrustIrLower::Strict
    } else if trust_ir_lower_is_active(opts) {
        config::TrustIrLower::On
    } else {
        config::TrustIrLower::Off
    };
    opts.unstable_opts.trust_ir_lower = Some(resolved_ir_lower);

    if trust_strict_policy_is_active(opts) {
        // The trust-cg backend already forces the strict gate under strict
        // verification, so a surviving `allow-unknown` would only be a tracked
        // value that disagrees with the enforced behavior — two crate hashes for
        // one compilation. `off` is rejected outright before this point.
        opts.unstable_opts.trust_cg_output_gate = "strict".to_string();

        // Strict verification must analyze the program that includes Rust's
        // dynamic safety checks. In particular, MIR construction observes
        // these effective options, so accepting `-Coverflow-checks=no` or
        // `-Cdebug-assertions=no` would remove operations before the verifier
        // ever sees them. Canonicalize both the raw codegen spelling and the
        // already-derived session value before Session/dependency hashes are
        // built. This also protects direct trustc users and callback-based
        // frontends instead of relying solely on Targo's argv construction.
        opts.cg.overflow_checks = Some(true);
        opts.cg.debug_assertions = Some(true);
        opts.debug_assertions = true;
    }
}

#[allow(rustc::bad_opt_access)]
fn trust_option_domain_error(opts: &config::Options) -> Option<&'static str> {
    let unstable = &opts.unstable_opts;
    if unstable.contract_checks.is_some() && trust_semantics_are_active(opts) {
        return Some(
            "-Zcontract-checks is retired for Trust compilations; runtime enforcement is selected \
             automatically by rustc --test or the session-bound `targo trust test` certified-monitor lane (use -Ztrust-verify=off only for an explicit vanilla-rustc compatibility compile)",
        );
    }
    if unstable.trust_certified_test_monitors {
        if !unstable.trust_verify.is_on() {
            return Some(
                "-Ztrust-certified-test-monitors requires full Trust verification; it cannot be combined with -Ztrust-verify=off",
            );
        }
        if opts.test {
            return Some(
                "-Ztrust-certified-test-monitors is redundant for a native --test unit, which already enables certified monitors",
            );
        }
        // The legacy flag is retained only as a tracked phase-A fingerprint
        // for Targo's resolved execution subject. It is not independent
        // monitor authority: without the nonce-bound phase-B selector it would
        // bypass the authenticated sysroot/startup/native-link closure below.
        if !unstable.trust_targo_test_monitor {
            return Some(
                "-Ztrust-certified-test-monitors requires Targo's authenticated tracked -Ztrust-targo-test-monitor selection",
            );
        }
        if unstable.trust_verify_session.is_none()
            || unstable.trust_verify_package_name.is_none()
            || !matches!(unstable.trust_verify_crate_role.as_str(), "primary" | "dependency")
        {
            return Some(
                "-Ztrust-certified-test-monitors is reserved for a session-scoped Targo primary harness-free test/bench root or dependency-role library/binary execution unit selected by the resolved test graph",
            );
        }
    }
    if unstable.link_only && trust_semantics_are_active(opts) {
        return Some(
            "-Zlink-only skips Trust analysis and cannot be combined with batteries-on \
             verification or -Ztrust-ir-lower; rebuild from source or disable all Trust \
             semantics with -Ztrust-verify=off",
        );
    }
    if unstable.trust_verify_session.is_some()
        && (unstable.no_analysis
            || unstable.parse_crate_root_only
            || unstable.trust_dump.mir_only
            || opts.pretty.is_some()
            || opts.describe_lints
            || !opts.prints.is_empty()
            || !unstable.ls.is_empty()
            || (opts.output_types.len() == 1
                && opts.output_types.contains_key(&OutputType::DepInfo)))
    {
        return Some(
            "-Ztrust-verify-session requests authenticated verification coverage and cannot be combined with a compiler early-exit mode (--print/help/list/unpretty, dep-info-only, -Zno-analysis, -Zparse-crate-root-only, or -Ztrust-dump=mir-only:<dir>)",
        );
    }
    if !matches!(unstable.trust_cg_output_gate.as_str(), "allow-unknown" | "strict" | "off") {
        return Some("invalid callback-injected -Ztrust-cg-output-gate value");
    }
    if let Some(perturbation) = unstable.trust_sat_perturb.as_deref() {
        if !matches!(
            perturbation,
            "enum-reshape"
                | "enum-case-value"
                | "enum-ctor"
                | "enum-disc-index"
                | "switch-map"
                | "enum-payload"
        ) {
            return Some(
                "invalid -Ztrust-sat-perturb value: expected enum-reshape, \
                 enum-case-value, enum-ctor, enum-disc-index, switch-map, or enum-payload",
            );
        }
        // A perturbation deliberately corrupts one lowering class so the
        // differential comparator must reject it. Requiring both switches
        // keeps it out of every evidence policy and prevents a valid-looking
        // but inert request when direct Trust-IR lowering is disabled.
        if unstable.trust_verify.is_on() || !trust_ir_lower_is_requested(opts) {
            return Some(
                "-Ztrust-sat-perturb is a burn-in-only control and requires \
                 -Ztrust-verify=off -Ztrust-ir-lower",
            );
        }
    }
    if unstable.trust_verify_level > 2 {
        return Some("invalid callback-injected -Ztrust-verify-level value");
    }
    if unstable.trust_verify_timeout_ms == 0 {
        return Some("invalid callback-injected -Ztrust-verify-timeout-ms value: must be positive");
    }
    if unstable.trust_verify_worker_threads > 256 {
        return Some(
            "invalid callback-injected -Ztrust-verify-worker-threads value: maximum is 256",
        );
    }
    if !matches!(unstable.trust_verify_output.as_str(), "human" | "json" | "both") {
        return Some("invalid callback-injected -Ztrust-verify-output value");
    }
    if !matches!(
        unstable.trust_verify_crate_role.as_str(),
        "unscoped" | "primary" | "dependency" | "build-script"
    ) {
        return Some("invalid callback-injected -Ztrust-verify-crate-role value");
    }
    for (value, error) in [
        (
            unstable.trust_verify_package_name.as_deref(),
            "invalid callback-injected -Ztrust-verify-package-name value: must be non-empty and trimmed",
        ),
        (
            unstable.trust_verify_profile.as_deref(),
            "invalid callback-injected -Ztrust-verify-profile value: must be non-empty and trimmed",
        ),
        (
            unstable.trust_verify_session.as_deref(),
            "invalid callback-injected -Ztrust-verify-session value: must be non-empty and trimmed",
        ),
    ] {
        if value.is_some_and(|value| value.is_empty() || value.trim() != value) {
            return Some(error);
        }
    }
    let has_package = unstable.trust_verify_package_name.is_some();
    let has_session = unstable.trust_verify_session.is_some();
    if unstable.trust_targo_test_monitor && !has_session {
        return Some("-Ztrust-targo-test-monitor requires -Ztrust-verify-session");
    }
    if has_package && !has_session {
        return Some("-Ztrust-verify-package-name requires -Ztrust-verify-session");
    }
    if unstable.trust_verify_crate_role != "unscoped" && !has_package {
        return Some(
            "non-unscoped -Ztrust-verify-crate-role requires both \
             -Ztrust-verify-package-name and -Ztrust-verify-session",
        );
    }
    for path in [unstable.trust_verify_ay_path.as_ref(), unstable.trust_proof_artifact_root.as_ref()]
        .into_iter()
        .flatten()
        .chain(unstable.trust_dump.paths())
    {
        if path.as_os_str().is_empty()
            || path.to_str().is_some_and(|value| value.trim().is_empty())
        {
            return Some("invalid callback-injected Trust path option: must be non-empty");
        }
    }
    if unstable.trust_proof_artifact_root.as_ref().is_some_and(|path| !path.is_absolute()) {
        return Some(
            "invalid callback-injected -Ztrust-proof-artifact-root value: path must be absolute",
        );
    }
    None
}

fn raw_z_option_named(option: &str, expected: &str) -> bool {
    raw_trust_option_name(option) == expected
}

/// Detect an authenticated coverage request before `build_session_options` is
/// available. Some successful rustc modes print and return directly from
/// `handle_options`; waiting for the typed option-domain check would let those
/// modes bypass the promised per-crate coverage row.
fn raw_matches_request_authenticated_verification(matches: &getopts::Matches) -> bool {
    matches.opt_strs("Z").iter().any(|option| raw_z_option_named(option, "trust_verify_session"))
}

/// The raw `ir:<dir>` payloads of every `-Ztrust-dump` in an argument vector.
///
/// Publication leases the directory before typed options exist, so the guard has
/// to read argv with rustc's own option grammar rather than waiting for the
/// parsed value. A payload that is not an `ir:` request is another sink and is
/// not a publication request at all.
fn raw_direct_ir_dump_directories(matches: &getopts::Matches) -> Vec<String> {
    matches
        .opt_strs("Z")
        .into_iter()
        .filter(|option| raw_z_option_named(option, "trust_dump"))
        .filter_map(|option| {
            option
                .split_once('=')
                .and_then(|(_, value)| {
                    value.strip_prefix(config::TrustDump::IR_REQUEST_PREFIX).map(str::to_string)
                })
        })
        .collect()
}

fn raw_matches_request_direct_ir_publication(matches: &getopts::Matches) -> bool {
    !raw_direct_ir_dump_directories(matches).is_empty()
}

/// Modes that return from `handle_options` before typed `Options` exist. A
/// direct-TrustIR publication request cannot safely discover or invalidate its
/// validated target in these modes, so the raw option guard rejects them.
fn raw_pre_typed_options_early_exit(
    matches: &getopts::Matches,
    args: &[String],
) -> Option<&'static str> {
    let z_options = matches.opt_strs("Z");
    let c_options = matches.opt_strs("C");

    if args.is_empty() || matches.opt_present("h") || matches.opt_present("help") {
        Some("compiler help")
    } else if z_options.iter().any(|option| option == "help") {
        Some("unstable-option help")
    } else if c_options.iter().any(|option| option == "help") {
        Some("codegen-option help")
    } else if c_options.iter().any(|option| option == "passes=list") {
        Some("codegen pass listing")
    } else if matches.opt_present("version") {
        Some("compiler version output")
    } else if matches.opt_strs("W").iter().any(|option| option == "all") {
        Some("-Wall help")
    } else {
        None
    }
}

fn raw_post_typed_options_early_exit(matches: &getopts::Matches) -> Option<&'static str> {
    let lint_help = ["A", "W", "D", "F", "allow", "warn", "force-warn", "deny", "forbid"]
        .into_iter()
        .any(|level| matches.opt_strs(level).iter().any(|value| value == "help"));

    if lint_help {
        Some("lint help")
    } else if matches.opt_str("explain").is_some() {
        Some("error-code explanation")
    } else {
        None
    }
}

fn raw_pre_session_early_exit(matches: &getopts::Matches, args: &[String]) -> Option<&'static str> {
    raw_pre_typed_options_early_exit(matches, args)
        .or_else(|| raw_post_typed_options_early_exit(matches))
}

fn authenticated_pre_session_early_exit(
    matches: &getopts::Matches,
    args: &[String],
) -> Option<&'static str> {
    raw_matches_request_authenticated_verification(matches)
        .then(|| raw_pre_session_early_exit(matches, args))
        .flatten()
}

fn direct_ir_pre_typed_options_early_exit(
    matches: &getopts::Matches,
    args: &[String],
) -> Option<&'static str> {
    raw_matches_request_direct_ir_publication(matches)
        .then(|| raw_pre_typed_options_early_exit(matches, args))
        .flatten()
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct DirectIrPublicationIdentity {
    directory: PathBuf,
    crate_name: String,
}

struct DirectIrPublicationLease {
    identity: DirectIrPublicationIdentity,
    lease: rustc_mir_build::TrustIrArtifactPublicationLease,
}

struct ParsedDirectIrPublicationRequest {
    identity: Option<DirectIrPublicationIdentity>,
}

fn parse_rustc_options(args: &[String]) -> Result<getopts::Matches, getopts::Fail> {
    let mut options = getopts::Options::new();
    for option in config::rustc_optgroups() {
        option.apply(&mut options);
    }
    options.parse(args)
}

#[allow(rustc::bad_opt_access)]
fn direct_ir_publication_identity(
    early_dcx: &EarlyDiagCtxt,
    opts: &config::Options,
) -> Option<DirectIrPublicationIdentity> {
    let Some(directory) = opts.unstable_opts.trust_dump.ir.clone() else {
        return None;
    };
    let Some(crate_name) = opts.crate_name.as_deref() else {
        early_dcx
            .early_fatal(
                "-Ztrust-dump=ir:<dir> with -Ztrust-ir-lower requires an explicit --crate-name",
            );
    };
    if crate_name.is_empty() {
        early_dcx.early_fatal("crate name must not be empty");
    }
    if let Some(character) = rustc_session::output::invalid_crate_name_chars(crate_name).next() {
        early_dcx
            .early_fatal(format!("invalid character {character} in crate name: `{crate_name}`"));
    }
    Some(DirectIrPublicationIdentity { directory, crate_name: crate_name.to_string() })
}

fn acquire_direct_ir_publication(
    early_dcx: &EarlyDiagCtxt,
    identity: DirectIrPublicationIdentity,
) -> DirectIrPublicationLease {
    match rustc_mir_build::trust_ir_acquire_artifact_publication_target(
        identity.directory.clone(),
        &identity.crate_name,
    ) {
        Ok(lease) => DirectIrPublicationLease { identity, lease },
        Err(error) => early_dcx.early_fatal(format!(
            "trust-ir-lower artifact target preparation failed for `{}`: {error}",
            identity.crate_name
        )),
    }
}

/// Discover a complete direct-publication identity from the outer argument
/// vector without opening an `@response-file`. Direct publication rejects
/// response files, but a complete outer identity must still be acquired before
/// response-file I/O: otherwise a missing, malformed, or non-UTF-8 file can
/// leave a preceding generation's commit marker current.
fn raw_outer_direct_ir_publication_identity(
    at_args: &[String],
) -> Result<Option<DirectIrPublicationIdentity>, String> {
    let args = at_args.get(1..).unwrap_or_default();
    // Use rustc's actual option grammar, including clustered short options and
    // value ownership. If raw argv is not itself parseable, the normal parser
    // remains responsible for its established diagnostic; no accepted outer
    // publication identity exists yet.
    let Ok(matches) = parse_rustc_options(args) else {
        return Ok(None);
    };

    let dump_directories = raw_direct_ir_dump_directories(&matches);
    if dump_directories.is_empty() {
        return Ok(None);
    }
    if dump_directories.len() != 1 {
        return Err(
            "direct-TrustIR publication requires exactly one outer -Ztrust-dump=ir:<directory>"
                .to_string(),
        );
    }

    let directory = Some(dump_directories[0].as_str())
        .filter(|value| !value.trim().is_empty())
        .ok_or_else(|| {
            "outer -Ztrust-dump=ir: requires one non-empty `<directory>` value".to_string()
        })?;
    let crate_names = matches.opt_strs("crate-name");
    if crate_names.len() != 1 {
        return Err(
            "-Ztrust-dump=ir:<dir> with -Ztrust-ir-lower requires an explicit --crate-name; provide exactly one literal outer value before any @response-file is read"
                .to_string(),
        );
    }
    let crate_name = &crate_names[0];
    if crate_name.is_empty() {
        return Err("crate name must not be empty".to_string());
    }
    if crate_name.starts_with('@') {
        return Err(
            "direct-TrustIR publication requires --crate-name to be a literal outer argument, not an @response-file"
                .to_string(),
        );
    }
    if let Some(character) = rustc_session::output::invalid_crate_name_chars(crate_name).next() {
        return Err(format!("invalid character {character} in crate name: `{crate_name}`"));
    }

    Ok(Some(DirectIrPublicationIdentity {
        directory: PathBuf::from(directory),
        crate_name: crate_name.clone(),
    }))
}

fn parsed_direct_ir_publication_request(
    args: &[String],
) -> Result<Option<ParsedDirectIrPublicationRequest>, getopts::Fail> {
    let matches = parse_rustc_options(args)?;
    let dump_directories = raw_direct_ir_dump_directories(&matches);
    if dump_directories.is_empty() {
        return Ok(None);
    }

    // This parser runs only as a fail-closed response-file guard. Acquire an
    // expanded target only when getopts leaves one unambiguous dump/name pair;
    // every other parsed publication request is still rejected, but does not
    // grant an ambiguous string authority to mutate the filesystem.
    let crate_names = matches.opt_strs("crate-name");
    let identity =
        if let ([directory], [crate_name]) = (dump_directories.as_slice(), crate_names.as_slice()) {
            Some(directory.as_str())
                .filter(|value| !value.trim().is_empty())
                .filter(|_| !crate_name.is_empty())
                .filter(|_| {
                    rustc_session::output::invalid_crate_name_chars(crate_name).next().is_none()
                })
                .map(|directory| DirectIrPublicationIdentity {
                    directory: PathBuf::from(directory),
                    crate_name: crate_name.clone(),
                })
        } else {
            None
        };
    Ok(Some(ParsedDirectIrPublicationRequest { identity }))
}

fn reject_direct_ir_publication_with_response_files(
    early_dcx: &EarlyDiagCtxt,
    raw_lease: Option<DirectIrPublicationLease>,
    expanded_args: &[String],
) {
    let expanded_request = parsed_direct_ir_publication_request(expanded_args).ok().flatten();
    if raw_lease.is_none() && expanded_request.is_none() {
        return;
    }

    let expanded_identity = expanded_request.and_then(|request| request.identity);
    let acquire_expanded = expanded_identity
        .as_ref()
        .is_some_and(|identity| raw_lease.as_ref().map_or(true, |raw| raw.identity != *identity));

    // Invalidate every unambiguous, fully known target before rejecting. Drop
    // the outer directory lock first so a distinct crate in the same directory
    // can be invalidated without self-deadlocking.
    drop(raw_lease);
    if acquire_expanded {
        drop(acquire_direct_ir_publication(
            early_dcx,
            expanded_identity.expect("expanded identity was checked as present"),
        ));
    }
    early_dcx.early_fatal(
        "direct-TrustIR publication cannot use @response-files; pass every compiler argument directly",
    );
}

fn should_preflight_direct_ir_publication(
    frontend_policy: FrontendTrustPolicy,
    expand_argfiles: bool,
    at_args: &[String],
) -> bool {
    frontend_policy == FrontendTrustPolicy::CanonicalTrustc
        && expand_argfiles
        && at_args
            .get(1..)
            .is_some_and(|args| args.iter().any(|argument| argument.starts_with('@')))
}

fn authenticated_pre_analysis_exit_message(session: Option<&str>, mode: &str) -> Option<String> {
    session.is_some().then(|| {
        format!(
            "-Ztrust-verify-session requests authenticated verification coverage, but {mode} stopped the compiler before analysis"
        )
    })
}

#[allow(rustc::bad_opt_access)]
fn reject_successful_authenticated_pre_analysis_exit(sess: &Session, mode: &str) {
    // Preserve the original diagnostic for a genuinely failing compile. The
    // Trust-specific fatal applies only to what would otherwise be a successful
    // pre-analysis return with no authenticated coverage.
    sess.dcx().abort_if_errors();
    if let Some(message) = authenticated_pre_analysis_exit_message(
        sess.opts.unstable_opts.trust_verify_session.as_deref(),
        mode,
    ) {
        sess.dcx().fatal(message);
    }
}

/// Reject runtime/startup surfaces that are outside the certified monitor's
/// authenticated execution closure before a selected Targo unit reaches
/// codegen.
///
/// Targo separately rejects `-l`, non-dependency `-L`, linker arguments, and
/// dynamic Rust artifacts at its process boundary. Source `#[link]`
/// attributes are encoded in Rust metadata, however, so neither a selected
/// crate's declaration nor one inherited from a dependency is visible in that
/// command-line audit. A native library can execute arbitrary code before
/// `main` (for example through an initializer), outside the certified monitor
/// proof and executable manifest. Keep that closure fail-closed until Trust
/// has an authenticated native-library inventory.
#[allow(rustc::bad_opt_access)]
fn reject_targo_certified_monitor_runtime_surface(tcx: TyCtxt<'_>) {
    if !tcx.sess.opts.unstable_opts.trust_targo_test_monitor {
        return;
    }

    reject_targo_certified_monitor_local_startup_surface(tcx);
    reject_targo_certified_monitor_dependency_symbol_controls(tcx);

    for cnum in std::iter::once(LOCAL_CRATE).chain(tcx.crates(()).iter().copied()) {
        // The standard library and compiler runtimes are part of the selected
        // compiler's TCB. Do not trust a crate name or internal attribute: the
        // resolved artifact itself must live beneath the active sysroot.
        if cnum != LOCAL_CRATE && crate_is_from_active_sysroot(tcx, cnum) {
            continue;
        }

        if let Some(lib) = tcx.native_libraries(cnum).first() {
            let source = if lib.foreign_module.is_some() {
                "source-level #[link]"
            } else {
                "compiler/build-script native-library input"
            };
            tcx.dcx().fatal(format!(
                "evidence-grade certified-monitor tests reject unauthenticated native linkage: crate `{}` has {source} library `{}`; only compiler-sysroot crates may contain native-library records",
                tcx.crate_name(cnum),
                lib.name,
            ));
        }
    }

    if let Some(formats) = tcx.dependency_formats(()).get(&CrateType::Executable) {
        for (cnum, linkage) in formats.iter_enumerated() {
            if matches!(linkage, Linkage::Dynamic | Linkage::IncludedFromDylib)
                && !tcx.crate_dep_kind(cnum).macros_only()
            {
                tcx.dcx().fatal(format!(
                    "evidence-grade certified-monitor tests require a static Rust dependency closure: crate `{}` has dynamic linkage `{linkage:?}`",
                    tcx.crate_name(cnum),
                ));
            }
        }
    }
}

/// Source-level startup controls can run arbitrary code before the generated
/// test harness or avoid that harness entirely. They are not represented by a
/// function's ordinary MIR proof obligations: `global_asm!` is emitted as a
/// standalone object fragment, `#[link_section]` can populate an initializer
/// section, and a naked function's assembly body bypasses normal MIR/codegen
/// structure. Entry-point overrides similarly invalidate the authenticated
/// harness boundary. Reject the complete local surface rather than trying to
/// recognize a platform-specific set of initializer section names.
fn reject_targo_certified_monitor_local_startup_surface(tcx: TyCtxt<'_>) {
    let runtime_role = if tcx.has_global_allocator(LOCAL_CRATE) {
        Some("a custom #[global_allocator]")
    } else if tcx.has_alloc_error_handler(LOCAL_CRATE) {
        Some("a custom #[alloc_error_handler]")
    } else if tcx.has_panic_handler(LOCAL_CRATE) {
        Some("a custom #[panic_handler]")
    } else {
        None
    };
    if let Some(runtime_role) = runtime_role {
        tcx.dcx().fatal(format!(
            "evidence-grade certified-monitor tests reject source-controlled runtime roles in the selected crate: it provides {runtime_role}",
        ));
    }

    if tcx
        .hir_crate_items(())
        .definitions()
        .any(|def_id| tcx.def_kind(def_id) == DefKind::GlobalAsm)
    {
        tcx.dcx().fatal(
            "evidence-grade certified-monitor tests reject unauthenticated global assembly; global_asm! can add startup code outside function MIR",
        );
    }

    // A source #[rustc_main] is removed when rustc synthesizes the test
    // harness. Treat the attempted override as an error instead of silently
    // accepting a source whose entry-point meaning changed in this lane.
    if tcx.sess.removed_rustc_main_attr.load(Ordering::Relaxed) {
        tcx.dcx().fatal(
            "evidence-grade certified-monitor tests reject source #[rustc_main] entry-point overrides",
        );
    }

    for owner in tcx.hir_crate_items(()).owners() {
        for attrs in tcx.hir_attr_map(owner).map.values() {
            for attr in *attrs {
                let Attribute::Parsed(attr) = attr else { continue };
                let message = match attr {
                    AttributeKind::LinkSection { .. } => Some(
                        "evidence-grade certified-monitor tests reject #[link_section]; custom sections can install unauthenticated startup code",
                    ),
                    AttributeKind::ExportName { .. } => Some(
                        "evidence-grade certified-monitor tests reject #[export_name]; source-controlled symbols can interpose the authenticated runtime",
                    ),
                    AttributeKind::Linkage(..) => Some(
                        "evidence-grade certified-monitor tests reject #[linkage]; source-controlled linkage can interpose the authenticated runtime",
                    ),
                    AttributeKind::Naked(_) => Some(
                        "evidence-grade certified-monitor tests reject #[naked]; naked assembly is outside the certified function-MIR monitor boundary",
                    ),
                    AttributeKind::NoMangle(_) => Some(
                        "evidence-grade certified-monitor tests reject #[no_mangle]; source-controlled symbols can interpose the authenticated runtime",
                    ),
                    AttributeKind::NoMain => Some(
                        "evidence-grade certified-monitor tests reject #![no_main]; the authenticated test harness must remain the executable entry point",
                    ),
                    AttributeKind::TestRunner(_) => Some(
                        "evidence-grade certified-monitor tests reject custom #![test_runner] entry points",
                    ),
                    AttributeKind::CompilerBuiltins
                    | AttributeKind::DefaultLibAllocator
                    | AttributeKind::NeedsAllocator
                    | AttributeKind::NeedsPanicRuntime
                    | AttributeKind::NoBuiltins
                    | AttributeKind::PanicRuntime
                    | AttributeKind::ProfilerRuntime => Some(
                        "evidence-grade certified-monitor tests reject source-controlled compiler/runtime crate roles",
                    ),
                    AttributeKind::Lang(LangItem::Start) => Some(
                        "evidence-grade certified-monitor tests reject a source-defined start language item",
                    ),
                    // In a non-test selected unit no compiler-generated
                    // #[rustc_main] exists, so any surviving occurrence is a
                    // source entry override. In a --test unit the cleaner
                    // above records and removes every source occurrence before
                    // adding the single synthetic harness entry.
                    AttributeKind::RustcMain if !tcx.sess.opts.test => Some(
                        "evidence-grade certified-monitor tests reject source #[rustc_main] entry-point overrides",
                    ),
                    _ => None,
                };
                if let Some(message) = message {
                    tcx.dcx().fatal(message);
                }
            }
        }
    }

    // Attribute-controlled runtime surfaces get their specific diagnostic
    // before scanning bodies. In particular, every valid #[naked] body also
    // contains naked_asm!, but the naked ABI boundary is independently part of
    // the rejected surface and should not be hidden behind the generic asm
    // diagnostic.
    struct InlineAsmFinder<'tcx> {
        tcx: TyCtxt<'tcx>,
        found: bool,
    }
    impl<'tcx> Visitor<'tcx> for InlineAsmFinder<'tcx> {
        type NestedFilter = OnlyBodies;

        fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
            self.tcx
        }

        fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
            if matches!(expr.kind, rustc_hir::ExprKind::InlineAsm(..)) {
                self.found = true;
            } else {
                intravisit::walk_expr(self, expr);
            }
        }
    }
    let mut inline_asm = InlineAsmFinder { tcx, found: false };
    tcx.hir_visit_all_item_likes_in_crate(&mut inline_asm);
    if inline_asm.found {
        tcx.dcx().fatal(
            "evidence-grade certified-monitor tests reject inline assembly; asm! can bypass MIR return monitors at machine level",
        );
    }
}

/// A statically linked dependency can interpose a runtime, abort, allocator,
/// or entry symbol without declaring a native library. Iterate every external
/// definition, not only public/exported symbols: metadata retains anonymous
/// `global_asm!` definitions and codegen attributes for private retained
/// statics. Compiler-synthesized symbols with no DefId and crate-level runtime
/// roles are rejected separately. Ordinary Rust-mangled definitions remain
/// available.
fn reject_targo_certified_monitor_dependency_symbol_controls(tcx: TyCtxt<'_>) {
    for cnum in tcx.crates(()).iter().copied() {
        if crate_is_from_active_sysroot(tcx, cnum) || tcx.crate_dep_kind(cnum).macros_only() {
            continue;
        }

        let runtime_role = if tcx.has_global_allocator(cnum) {
            Some("a custom #[global_allocator]")
        } else if tcx.has_alloc_error_handler(cnum) {
            Some("a custom #[alloc_error_handler]")
        } else if tcx.has_panic_handler(cnum) {
            Some("a custom #[panic_handler]")
        } else if tcx.is_panic_runtime(cnum) {
            Some("a custom panic runtime")
        } else if tcx.is_profiler_runtime(cnum) {
            Some("a custom profiler runtime")
        } else if tcx.is_compiler_builtins(cnum) {
            Some("custom compiler builtins")
        } else {
            None
        };
        if let Some(runtime_role) = runtime_role {
            tcx.dcx().fatal(format!(
                "evidence-grade certified-monitor tests reject source-controlled runtime roles in dependencies: crate `{}` provides {runtime_role}",
                tcx.crate_name(cnum),
            ));
        }

        for index in 0..tcx.num_extern_def_ids(cnum) {
            let def_id = DefId { krate: cnum, index: DefIndex::from_usize(index) };
            let def_kind = tcx.def_kind(def_id);
            if def_kind == DefKind::GlobalAsm {
                tcx.dcx().fatal(format!(
                    "evidence-grade certified-monitor tests reject unauthenticated global assembly in dependency crate `{}`",
                    tcx.crate_name(cnum),
                ));
            }
            if !def_kind.has_codegen_attrs() {
                continue;
            }
            let attrs = tcx.codegen_fn_attrs(def_id);
            let control = if attrs.flags.contains(CodegenFnAttrFlags::NO_MANGLE) {
                Some("#[no_mangle]")
            } else if attrs.flags.contains(CodegenFnAttrFlags::NAKED) {
                Some("#[naked]")
            } else if attrs.flags.contains(CodegenFnAttrFlags::USED_LINKER) {
                Some("#[used(linker)]")
            } else if attrs.symbol_name.is_some() {
                Some("#[export_name] or a source-defined runtime symbol")
            } else if attrs.link_section.is_some() {
                Some("#[link_section]")
            } else if attrs.linkage.is_some() {
                Some("#[linkage]")
            } else {
                None
            };
            if let Some(control) = control {
                tcx.dcx().fatal(format!(
                    "evidence-grade certified-monitor tests reject source-controlled symbols or retained sections in dependencies: crate `{}` uses {control}",
                    tcx.crate_name(cnum),
                ));
            }
        }

        let exported =
            tcx.exported_non_generic_symbols(cnum).iter().chain(tcx.exported_generic_symbols(cnum));
        if let Some(ExportedSymbol::NoDefId(symbol)) = exported
            .map(|(symbol, _)| *symbol)
            .find(|symbol| matches!(symbol, ExportedSymbol::NoDefId(_)))
        {
            tcx.dcx().fatal(format!(
                "evidence-grade certified-monitor tests reject dependency symbols without auditable Rust definitions: crate `{}` exports `{symbol}`",
                tcx.crate_name(cnum),
            ));
        }
    }
}

fn crate_is_from_active_sysroot(tcx: TyCtxt<'_>, cnum: CrateNum) -> bool {
    // Do not use broad path containment here. A caller can place Cargo's
    // target directory beneath a writable sysroot and otherwise make an
    // ordinary project artifact look like part of the compiler TCB. Sysroot
    // Rust artifacts are resolved directly from the target lib directory;
    // require exact canonical parent membership in that inventory directory.
    let target_libdir = rustc_session::filesearch::make_target_lib_path(
        tcx.sess.opts.sysroot.path(),
        tcx.sess.opts.target_triple.tuple(),
    );
    let Ok(target_libdir) = fs::canonicalize(target_libdir) else {
        return false;
    };
    let source = tcx.used_crate_source(cnum);
    let mut paths = source.paths().chain(source.sdylib_interface.iter());
    let Some(first) = paths.next() else {
        return false;
    };
    std::iter::once(first).chain(paths).all(|path| {
        fs::canonicalize(path).is_ok_and(|path| path.parent() == Some(target_libdir.as_path()))
    })
}

/// Exit status code used for successful compilation and help output.
pub const EXIT_SUCCESS: i32 = 0;

/// Exit status code used for compilation failures and invalid flags.
pub const EXIT_FAILURE: i32 = 1;

pub const DEFAULT_BUG_REPORT_URL: &str =
    "https://github.com/alabsystems/Trust/issues/new?labels=C-bug%2C+I-ICE%2C+T-trustc";

pub trait Callbacks {
    /// Called before creating the compiler instance
    fn config(&mut self, _config: &mut interface::Config) {}
    /// Called after parsing the crate root. Submodules are not yet parsed when
    /// this callback is called. Return value instructs the compiler whether to
    /// continue the compilation afterwards (defaults to `Compilation::Continue`)
    fn after_crate_root_parsing(
        &mut self,
        _compiler: &interface::Compiler,
        _krate: &mut ast::Crate,
    ) -> Compilation {
        Compilation::Continue
    }
    /// Called after expansion. Return value instructs the compiler whether to
    /// continue the compilation afterwards (defaults to `Compilation::Continue`)
    fn after_expansion<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        _tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        Compilation::Continue
    }
    /// Called after analysis. Return value instructs the compiler whether to
    /// continue the compilation afterwards (defaults to `Compilation::Continue`)
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        _tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        Compilation::Continue
    }
}

#[derive(Default)]
pub struct TimePassesCallbacks {
    time_passes: Option<TimePassesFormat>,
}

impl Callbacks for TimePassesCallbacks {
    // JUSTIFICATION: the session doesn't exist at this point.
    #[allow(rustc::bad_opt_access)]
    fn config(&mut self, config: &mut interface::Config) {
        // If a --print=... option has been given, we don't print the "total"
        // time because it will mess up the --print output. See #64339.
        //
        self.time_passes = (config.opts.prints.is_empty() && config.opts.unstable_opts.time_passes)
            .then_some(config.opts.unstable_opts.time_passes_format);
        config.opts.trimmed_def_paths = true;
    }
}

/// Run an in-process embedded compiler without official Trust evidence
/// authority. The actual compiler executable uses the callback-fixed canonical
/// dispatch in [`main`].
pub fn run_compiler(at_args: &[String], callbacks: &mut (dyn Callbacks + Send)) {
    run_compiler_with_argfile_mode(
        at_args,
        callbacks,
        true,
        FrontendTrustPolicy::EmbeddedNoOfficialEvidence,
    );
}

/// Run rustc from an immutable, already-expanded argument snapshot.
///
/// This entry point is for in-process compiler wrappers that must inspect the
/// exact arguments they execute. `at_args[0]` is still the binary name, but no
/// remaining argument is interpreted as an `@file`: in particular, a literal
/// `@inner` line from a (non-recursive) rustc response file stays literal.
/// Callers must use [`args::arg_expand_all`] exactly once before invoking this.
pub fn run_compiler_with_expanded_args(at_args: &[String], callbacks: &mut (dyn Callbacks + Send)) {
    run_compiler_with_argfile_mode(
        at_args,
        callbacks,
        false,
        FrontendTrustPolicy::EmbeddedNoOfficialEvidence,
    );
}

/// A typed, deauthorization-only marker for a fresh-process compiler
/// invocation that must not produce Trust evidence.
pub use rustc_interface::interface::NoTrustEvidence;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FrontendTrustPolicy {
    CanonicalTrustc,
    EmbeddedNoOfficialEvidence,
    EvidenceInert,
}

impl FrontendTrustPolicy {
    fn deauthorizes_official_evidence(self) -> bool {
        self != Self::CanonicalTrustc
    }

    fn requires_evidence_inert_backend(self) -> bool {
        self == Self::EvidenceInert
    }

    fn compiler_backend_route(self) -> config::CompilerBackendRoute {
        if self.requires_evidence_inert_backend() {
            config::CompilerBackendRoute::EvidenceInert
        } else {
            config::CompilerBackendRoute::BackendCapable
        }
    }

    fn diagnostic_name(self) -> &'static str {
        match self {
            Self::CanonicalTrustc => "CanonicalTrustc",
            Self::EmbeddedNoOfficialEvidence => "EmbeddedNoOfficialEvidence",
            Self::EvidenceInert => "NoTrustEvidence",
        }
    }
}

/// Run rustc from an immutable, already-expanded argument snapshot under a
/// typed policy that cannot lower TrustIR or publish Trust evidence.
///
/// This entry point is for Tippy-like lint frontends whose callbacks change
/// proof-relevant semantics. Every authority-bearing `-Ztrust-*` control and
/// every compiler-managed dynamic LLVM loading route is rejected. The sole
/// accepted Trust selection is the exact semantic option/value
/// `trust-verify=off` (including getopts-equivalent joined, split, and
/// dash/underscore spellings): it redundantly selects the same evidence-inert
/// policy and is needed when a build coordinator stamps all Rust units
/// uniformly. The typed `trust_verify` switch is then forced off and
/// `trust_ir_lower` forced off before callbacks or artifact target acquisition.
/// The callback authority snapshot prevents either field or any evidence
/// output from being re-enabled later. The argument vector itself is not
/// rewritten, so getopts retains exact response-file, option-value, and `--`
/// ownership semantics.
///
/// Compiler-owned entry points are process-tracked: this route fails closed if
/// an earlier compiler invocation could have initialized backend state and
/// excludes concurrent backend-capable compiler routes. Arbitrary host code
/// that calls LLVM or a backend directly remains outside that marker.
pub fn run_compiler_with_expanded_args_and_no_trust_evidence(
    at_args: &[String],
    callbacks: &mut (dyn Callbacks + Send),
    _authority: NoTrustEvidence,
) {
    run_compiler_with_argfile_mode(at_args, callbacks, false, FrontendTrustPolicy::EvidenceInert);
}

fn compiler_arguments(
    early_dcx: &EarlyDiagCtxt,
    at_args: &[String],
    expand_argfiles: bool,
) -> Vec<String> {
    // Throw away the first argument, the name of the binary.
    // In case of at_args being empty, as might be the case by
    // passing empty argument array to execve under some platforms,
    // just use an empty slice.
    //
    // This situation was possible before due to arg_expand_all being
    // called before removing the argument, enabling a crash by calling
    // the compiler with @empty_file as argv[0] and no more arguments.
    let at_args = at_args.get(1..).unwrap_or_default();
    if expand_argfiles { args::arg_expand_all(early_dcx, at_args) } else { at_args.to_vec() }
}

fn trust_verify_override_requested(
    frontend_policy: FrontendTrustPolicy,
    inherited_no_verify: Option<&OsStr>,
) -> bool {
    frontend_policy.deauthorizes_official_evidence() || inherited_no_verify == Some(OsStr::new("1"))
}

fn apply_trust_verify_override(opts: &mut config::Options, requested: bool) {
    if requested {
        opts.unstable_opts.trust_verify = config::TrustVerify::Off;
    }
}

fn raw_trust_option_name(option: &str) -> String {
    option.split_once('=').map_or(option, |(name, _)| name).replace('-', "_")
}

fn frontend_forbidden_option(
    frontend_policy: FrontendTrustPolicy,
    matches: &getopts::Matches,
) -> Option<String> {
    if !frontend_policy.deauthorizes_official_evidence() {
        return None;
    }

    let forbidden_z = matches
        .opt_strs("Z")
        .into_iter()
        .find_map(|option| {
            let name = raw_trust_option_name(&option);
            // Both typed deauthorization routes force this value to Off below.
            // Accepting the caller's identical semantic value is monotonic and
            // lets a coordinator stamp dependency and workspace units
            // uniformly. The exact-value check deliberately excludes a bare
            // selector, malformed values, and every enabling value.
            let redundant_deauthorization = name == "trust_verify"
                && option.split_once('=').is_some_and(|(_, value)| value == "off");
            (name.starts_with("trust_") && !redundant_deauthorization
                || frontend_policy.requires_evidence_inert_backend()
                    && matches!(
                        name.as_str(),
                        "autodiff" | "autodiff_post_passes" | "codegen_backend" | "llvm_plugins"
                    ))
            .then_some(name)
        });
    if let Some(name) = forbidden_z {
        return Some(format!("-Z{}", name.replace('_', "-")));
    }

    if !frontend_policy.requires_evidence_inert_backend() {
        return None;
    }
    matches
        .opt_strs("C")
        .into_iter()
        .map(|option| raw_trust_option_name(&option))
        .find(|name| name == "llvm_args")
        .map(|name| format!("-C{}", name.replace('_', "-")))
}

fn validate_frontend_pre_backend_authority(
    early_dcx: &EarlyDiagCtxt,
    matches: &getopts::Matches,
    frontend_policy: FrontendTrustPolicy,
) {
    if let Some(option) = frontend_forbidden_option(frontend_policy, matches) {
        early_dcx.early_fatal(format!(
            "{} compiler frontend rejects semantic, evidence, or backend control `{option}`",
            frontend_policy.diagnostic_name(),
        ));
    }
    if frontend_policy.deauthorizes_official_evidence()
        && let Some(key) = config::forbidden_no_official_evidence_environment_key(
            env::vars_os().map(|(key, _)| key),
        )
    {
        early_dcx.early_fatal(config::trust_environment_error(&key));
    }
}

fn no_trust_evidence_callback_backend_error(
    frontend_policy: FrontendTrustPolicy,
    has_callback_backend_factory: bool,
) -> Option<&'static str> {
    (frontend_policy.requires_evidence_inert_backend() && has_callback_backend_factory).then_some(
        "NoTrustEvidence compiler frontend rejects callback-provided codegen backend factories",
    )
}

fn run_compiler_with_argfile_mode(
    at_args: &[String],
    callbacks: &mut (dyn Callbacks + Send),
    expand_argfiles: bool,
    frontend_policy: FrontendTrustPolicy,
) {
    let mut default_early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());
    let compiler_backend_route_guard =
        config::enter_compiler_backend_route(frontend_policy.compiler_backend_route())
            .unwrap_or_else(|error| default_early_dcx.early_fatal(error));
    let expanded_response_files =
        should_preflight_direct_ir_publication(frontend_policy, expand_argfiles, at_args);
    let raw_artifact_publication_lease = if expanded_response_files {
        raw_outer_direct_ir_publication_identity(at_args)
            .unwrap_or_else(|error| default_early_dcx.early_fatal(error))
            .map(|identity| acquire_direct_ir_publication(&default_early_dcx, identity))
    } else {
        None
    };
    let args = compiler_arguments(&default_early_dcx, at_args, expand_argfiles);
    // Reject immediately after successful argfile I/O. Option handling has
    // effectful early modes (including backend construction), and an expanded
    // `--` can hide an outer publication option from those guards.
    if expanded_response_files {
        reject_direct_ir_publication_with_response_files(
            &default_early_dcx,
            raw_artifact_publication_lease,
            &args,
        );
    }
    if frontend_policy.deauthorizes_official_evidence()
        && let Some(key) = config::forbidden_no_official_evidence_environment_key(
            env::vars_os().map(|(key, _)| key),
        )
    {
        default_early_dcx.early_fatal(config::trust_environment_error(&key));
    }
    // `TRUST_NO_VERIFY=1` is the one documented inheritance transport for
    // nested compiler processes. Convert it, or an explicit deauthorization
    // request from a trusted frontend entry point, directly into tracked typed
    // state. Rewriting argv cannot preserve getopts semantics because a literal
    // `--` may itself be the required value of the preceding option.
    let trust_verify_override = trust_verify_override_requested(
        frontend_policy,
        env::var_os("TRUST_NO_VERIFY").as_deref(),
    );

    let (matches, help_only) =
        match handle_options_with_frontend_policy(&default_early_dcx, &args, frontend_policy) {
            HandledOptions::None => return,
            HandledOptions::Normal(matches) => (matches, false),
            HandledOptions::HelpOnly(matches) => (matches, true),
        };

    let mut sopts = config::build_session_options(&mut default_early_dcx, &matches);
    apply_trust_verify_override(&mut sopts, trust_verify_override);
    if frontend_policy.deauthorizes_official_evidence() {
        sopts.unstable_opts.trust_ir_lower = Some(config::TrustIrLower::Off);
        sopts.trust_solver_content_fingerprint.clear();
    }
    let mut artifact_publication_lease = None;
    // A direct artifact request must establish its effective typed Trust
    // policy before any mode can inspect compiler input. Keep ordinary typed
    // early exits on their upstream path: without a publication target there
    // is no reason to move callback normalization or environment validation
    // ahead of `--explain`/input selection. The normal post-callback checks
    // below still cover every invocation that proceeds into a Session.
    if sopts.unstable_opts.trust_dump.ir.is_some() {
        normalize_and_validate_trust_options(&mut sopts);
        validate_trust_environment(&sopts);
    }
    if !expanded_response_files && trust_ir_lower_is_active(&sopts) {
        artifact_publication_lease = direct_ir_publication_identity(&default_early_dcx, &sopts)
            .map(|identity| acquire_direct_ir_publication(&default_early_dcx, identity));
    }
    // fully initialize ice path static once unstable options are available as context
    let ice_file = ice_path_with_config(Some(&sopts.unstable_opts)).clone();

    if let Some(ref code) = matches.opt_str("explain") {
        handle_explain(&default_early_dcx, code, sopts.color);
        return;
    }

    let input = make_input(&default_early_dcx, &matches.free);
    let has_input = input.is_some();
    let (odir, ofile) = make_output(&matches);

    drop(default_early_dcx);

    let mut config = interface::Config {
        opts: sopts,
        crate_cfg: matches.opt_strs("cfg"),
        crate_check_cfg: matches.opt_strs("check-cfg"),
        input: input.unwrap_or(Input::File(PathBuf::new())),
        output_file: ofile,
        output_dir: odir,
        ice_file,
        file_loader: None,
        lint_caps: Default::default(),
        psess_created: None,
        track_state: None,
        register_lints: None,
        override_queries: None,
        extra_symbols: Vec::new(),
        make_codegen_backend: None,
        using_internal_features: &USING_INTERNAL_FEATURES,
    };

    let callback_authority = config::TrustFrontendAuthoritySnapshot::capture(&config.opts);
    let command_line_contract_checks = config.opts.unstable_opts.contract_checks;
    let artifact_crate_name_authority = (trust_ir_lower_is_active(&config.opts)
        && config.opts.unstable_opts.trust_dump.ir.is_some())
    .then(|| config.opts.crate_name.clone());
    callbacks.config(&mut config);
    if let Some(error) = no_trust_evidence_callback_backend_error(
        frontend_policy,
        config.make_codegen_backend.is_some(),
    ) {
        EarlyDiagCtxt::new(config.opts.error_format).early_fatal(error);
    }
    if let Some(option) = callback_authority.changed_option(&config.opts) {
        EarlyDiagCtxt::new(config.opts.error_format).early_fatal(format!(
            "compiler callback changed command-line Trust authority `{option}`; callbacks may not mutate Trust verification policy or explicit codegen-backend selection"
        ));
    }
    if trust_callback_changed_contract_checks(command_line_contract_checks, &config.opts) {
        EarlyDiagCtxt::new(config.opts.error_format).early_fatal(
            "compiler callback changed command-line Trust authority `-Zcontract-checks`; callbacks may not set or erase the retired Trust exec projection",
        );
    }
    if artifact_crate_name_authority
        .as_ref()
        .is_some_and(|crate_name| *crate_name != config.opts.crate_name)
    {
        EarlyDiagCtxt::new(config.opts.error_format).early_fatal(
            "compiler callback changed direct-TrustIR artifact authority `--crate-name`",
        );
    }
    normalize_and_validate_trust_options(&mut config.opts);
    // Recheck process-global controls after the callback. Typed Trust fields
    // are authority-protected above, but callback code can still introduce an
    // untracked environment variable after the pre-input validation.
    validate_trust_environment(&config.opts);

    let registered_lints = config.register_lints.is_some();

    let run = |compiler: &interface::Compiler| {
        let sess = &compiler.sess;
        let codegen_backend = &*compiler.codegen_backend;
        if let Some(lease) = artifact_publication_lease.take() {
            rustc_mir_build::trust_ir_install_artifact_publication(sess, lease.lease);
        }

        // This is used for early exits unrelated to errors. E.g. when just
        // printing some information without compiling, or exiting immediately
        // after parsing, etc.
        let pre_analysis_early_exit = |mode| {
            reject_successful_authenticated_pre_analysis_exit(sess, mode);
        };

        // This implements `-Whelp`. It should be handled very early, like
        // `--help`/`-Zhelp`/`-Chelp`. This is the earliest it can run, because
        // it must happen after lints are registered, during session creation.
        if sess.opts.describe_lints {
            describe_lints(sess, registered_lints);
            return pre_analysis_early_exit("lint help");
        }

        // We have now handled all help options, exit
        if help_only {
            return pre_analysis_early_exit("compiler help");
        }

        if print_crate_info(codegen_backend, sess, has_input) == Compilation::Stop {
            return pre_analysis_early_exit("a --print request");
        }

        if !has_input {
            sess.dcx().fatal("no input filename given"); // this is fatal
        }

        if !sess.opts.unstable_opts.ls.is_empty() {
            list_metadata(sess, &*codegen_backend.metadata_loader());
            return pre_analysis_early_exit("a metadata listing request");
        }

        if sess.opts.unstable_opts.link_only {
            process_rlink(sess, compiler);
            return pre_analysis_early_exit("-Zlink-only");
        }

        // Parse the crate root source code (doesn't parse submodules yet)
        // Everything else is parsed during macro expansion.
        let mut krate = passes::parse(sess);

        // If pretty printing is requested: Figure out the representation, print it and exit
        if let Some(pp_mode) = sess.opts.pretty {
            if pp_mode.needs_ast_map() {
                create_and_enter_global_ctxt(compiler, krate, |tcx| {
                    tcx.ensure_ok().early_lint_checks(());
                    pretty::print(sess, pp_mode, pretty::PrintExtra::NeedsAstMap { tcx });
                    passes::write_dep_info(tcx);
                });
            } else {
                pretty::print(sess, pp_mode, pretty::PrintExtra::AfterParsing { krate: &krate });
            }
            trace!("finished pretty-printing");
            return pre_analysis_early_exit("pretty printing");
        }

        if callbacks.after_crate_root_parsing(compiler, &mut krate) == Compilation::Stop {
            return pre_analysis_early_exit("Callbacks::after_crate_root_parsing");
        }

        if sess.opts.unstable_opts.parse_crate_root_only {
            return pre_analysis_early_exit("-Zparse-crate-root-only");
        }

        let linker = create_and_enter_global_ctxt(compiler, krate, |tcx| {
            let pre_analysis_early_exit = |mode| {
                reject_successful_authenticated_pre_analysis_exit(sess, mode);
                None
            };

            // Make sure name resolution and macro expansion is run.
            let _ = tcx.resolver_for_lowering();

            if callbacks.after_expansion(compiler, tcx) == Compilation::Stop {
                return pre_analysis_early_exit("Callbacks::after_expansion");
            }

            passes::write_dep_info(tcx);

            passes::write_interface(tcx);

            if sess.opts.output_types.contains_key(&OutputType::DepInfo)
                && sess.opts.output_types.len() == 1
            {
                return pre_analysis_early_exit("dep-info-only output");
            }

            if sess.opts.unstable_opts.no_analysis {
                return pre_analysis_early_exit("-Zno-analysis");
            }

            tcx.ensure_ok().analysis(());

            reject_targo_certified_monitor_runtime_surface(tcx);

            if let Some(metrics_dir) = &sess.opts.unstable_opts.metrics_dir {
                dump_feature_usage_metrics(tcx, metrics_dir);
            }

            if callbacks.after_analysis(compiler, tcx) == Compilation::Stop {
                sess.dcx().abort_if_errors();
                return None;
            }

            if tcx.sess.opts.output_types.contains_key(&OutputType::Mir) {
                if let Err(error) = pretty::emit_mir(tcx) {
                    tcx.dcx().emit_fatal(CantEmitMir { error });
                }
            }

            let linker = Linker::codegen_and_build_linker(tcx, &*compiler.codegen_backend);

            tcx.report_unused_features();

            Some(linker)
        });

        // Linking is done outside the `compiler.enter()` so that the
        // `GlobalCtxt` within `Queries` can be freed as early as possible.
        if let Some(linker) = linker {
            linker.link(sess, codegen_backend);
        }
    };
    match frontend_policy {
        FrontendTrustPolicy::CanonicalTrustc => {
            interface::run_compiler_with_canonical_trustc_policy_unchecked(config, run)
        }
        FrontendTrustPolicy::EmbeddedNoOfficialEvidence => interface::run_compiler(config, run),
        FrontendTrustPolicy::EvidenceInert => {
            interface::run_compiler_with_no_trust_evidence_driver_handoff_unchecked(
                config,
                NoTrustEvidence,
                compiler_backend_route_guard,
                run,
            )
        }
    }
}

fn dump_feature_usage_metrics(tcx: TyCtxt<'_>, metrics_dir: &Path) {
    let hash = tcx.crate_hash(LOCAL_CRATE);
    let crate_name = tcx.crate_name(LOCAL_CRATE);
    let metrics_file_name = format!("unstable_feature_usage_metrics-{crate_name}-{hash}.json");
    let metrics_path = metrics_dir.join(metrics_file_name);
    if let Err(error) = tcx.features().dump_feature_usage_metrics(metrics_path) {
        // FIXME(yaahc): once metrics can be enabled by default we will want "failure to emit
        // default metrics" to only produce a warning when metrics are enabled by default and emit
        // an error only when the user manually enables metrics
        tcx.dcx().emit_err(UnstableFeatureUsage { error });
    }
}

/// Extract output directory and file from matches.
fn make_output(matches: &getopts::Matches) -> (Option<PathBuf>, Option<OutFileName>) {
    let odir = matches.opt_str("out-dir").map(|o| PathBuf::from(&o));
    let ofile = matches.opt_str("o").map(|o| match o.as_str() {
        "-" => OutFileName::Stdout,
        path => OutFileName::Real(PathBuf::from(path)),
    });
    (odir, ofile)
}

/// Extract input (string or file and optional path) from matches.
/// This handles reading from stdin if `-` is provided.
fn make_input(early_dcx: &EarlyDiagCtxt, free_matches: &[String]) -> Option<Input> {
    match free_matches {
        [] => None, // no input: we will exit early,
        [ifile] if ifile == "-" => {
            // read from stdin as `Input::Str`
            let mut input = String::new();
            if io::stdin().read_to_string(&mut input).is_err() {
                // Immediately stop compilation if there was an issue reading
                // the input (for example if the input stream is not UTF-8).
                early_dcx
                    .early_fatal("couldn't read from stdin, as it did not contain valid UTF-8");
            }

            let name = match env::var("UNSTABLE_RUSTDOC_TEST_PATH") {
                Ok(path) => {
                    let line = env::var("UNSTABLE_RUSTDOC_TEST_LINE").expect(
                        "when UNSTABLE_RUSTDOC_TEST_PATH is set \
                                    UNSTABLE_RUSTDOC_TEST_LINE also needs to be set",
                    );
                    let line = line
                        .parse::<isize>()
                        .expect("UNSTABLE_RUSTDOC_TEST_LINE needs to be a number");
                    FileName::doc_test_source_code(PathBuf::from(path), line)
                }
                Err(_) => FileName::anon_source_code(&input),
            };

            Some(Input::Str { name, input })
        }
        [ifile] => Some(Input::File(PathBuf::from(ifile))),
        [ifile1, ifile2, ..] => early_dcx.early_fatal(format!(
            "multiple input filenames provided (first two filenames are `{}` and `{}`)",
            ifile1, ifile2
        )),
    }
}

/// Whether to stop or continue compilation.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Compilation {
    Stop,
    Continue,
}

fn handle_explain(early_dcx: &EarlyDiagCtxt, code: &str, color: ColorConfig) {
    // Allow "E0123" or "0123" form.
    let upper_cased_code = code.to_ascii_uppercase();
    if let Ok(code) = upper_cased_code.trim_prefix('E').parse::<u32>()
        && code <= ErrCode::MAX_AS_U32
        && let Ok(description) = rustc_errors::codes::try_find_description(ErrCode::from_u32(code))
    {
        let mut is_in_code_block = false;
        let mut text = String::new();
        // Slice off the leading newline and print.
        for line in description.lines() {
            let indent_level = line.find(|c: char| !c.is_whitespace()).unwrap_or(line.len());
            let dedented_line = &line[indent_level..];
            if dedented_line.starts_with("```") {
                is_in_code_block = !is_in_code_block;
                text.push_str(&line[..(indent_level + 3)]);
            } else if is_in_code_block && dedented_line.starts_with("# ") {
                continue;
            } else {
                text.push_str(line);
            }
            text.push('\n');
        }

        // If output is a terminal, use a pager to display the content.
        if io::stdout().is_terminal() {
            show_md_content_with_pager(&text, color);
        } else {
            // Otherwise, if the user has requested colored output
            // print the content in color, else print the md content.
            if color == ColorConfig::Always {
                show_colored_md_content(&text);
            } else {
                safe_print!("{text}");
            }
        }
    } else {
        early_dcx.early_fatal(format!("{code} is not a valid error code"));
    }
}

/// If `color` is `always` or `auto`, try to print pretty (formatted & colorized) markdown. If
/// that fails or `color` is `never`, print the raw markdown.
///
/// Uses a pager if possible, falls back to stdout.
fn show_md_content_with_pager(content: &str, color: ColorConfig) {
    let pager_name = env::var_os("PAGER").unwrap_or_else(|| {
        if cfg!(windows) { OsString::from("more.com") } else { OsString::from("less") }
    });

    let mut cmd = Command::new(&pager_name);
    if pager_name == "less" {
        cmd.arg("-R"); // allows color escape sequences
    }

    let pretty_on_pager = match color {
        ColorConfig::Auto => {
            // Add other pagers that accept color escape sequences here.
            ["less", "bat", "batcat", "delta"].iter().any(|v| *v == pager_name)
        }
        ColorConfig::Always => true,
        ColorConfig::Never => false,
    };

    // Try to prettify the raw markdown text. The result can be used by the pager or on stdout.
    let mut pretty_data = {
        let mdstream = markdown::MdStream::parse_str(content);
        let bufwtr = markdown::create_stdout_bufwtr();
        let mut mdbuf = Vec::new();
        if mdstream.write_anstream_buf(&mut mdbuf, Some(&highlighter::highlight)).is_ok() {
            Some((bufwtr, mdbuf))
        } else {
            None
        }
    };

    // Try to print via the pager, pretty output if possible.
    let pager_res = try {
        let mut pager = cmd.stdin(Stdio::piped()).spawn().ok()?;

        let pager_stdin = pager.stdin.as_mut()?;
        if pretty_on_pager && let Some((_, mdbuf)) = &pretty_data {
            pager_stdin.write_all(mdbuf.as_slice()).ok()?;
        } else {
            pager_stdin.write_all(content.as_bytes()).ok()?;
        };

        pager.wait().ok()?;
    };
    if pager_res.is_some() {
        return;
    }

    // The pager failed. Try to print pretty output to stdout.
    if let Some((bufwtr, mdbuf)) = &mut pretty_data
        && bufwtr.write_all(&mdbuf).is_ok()
    {
        return;
    }

    // Everything failed. Print the raw markdown text.
    safe_print!("{content}");
}

/// Prints the markdown content with colored output.
///
/// This function is used when the output is not a terminal,
/// but the user has requested colored output with `--color=always`.
fn show_colored_md_content(content: &str) {
    // Try to prettify the raw markdown text.
    let mut pretty_data = {
        let mdstream = markdown::MdStream::parse_str(content);
        let bufwtr = markdown::create_stdout_bufwtr();
        let mut mdbuf = Vec::new();
        if mdstream.write_anstream_buf(&mut mdbuf, Some(&highlighter::highlight)).is_ok() {
            Some((bufwtr, mdbuf))
        } else {
            None
        }
    };

    if let Some((bufwtr, mdbuf)) = &mut pretty_data
        && bufwtr.write_all(&mdbuf).is_ok()
    {
        return;
    }

    // Everything failed. Print the raw markdown text.
    safe_print!("{content}");
}

fn process_rlink(sess: &Session, compiler: &interface::Compiler) {
    assert!(sess.opts.unstable_opts.link_only);
    let dcx = sess.dcx();
    if let Input::File(file) = &sess.io.input {
        let rlink_data = fs::read(file).unwrap_or_else(|err| {
            dcx.emit_fatal(RlinkUnableToRead { err });
        });
        let (compiled_modules, crate_info, metadata, outputs) =
            match CompiledModules::deserialize_rlink(sess, rlink_data) {
                Ok((codegen, crate_info, metadata, outputs)) => {
                    (codegen, crate_info, metadata, outputs)
                }
                Err(err) => {
                    match err {
                        CodegenError::WrongFileType => dcx.emit_fatal(RLinkWrongFileType),
                        CodegenError::EmptyVersionNumber => dcx.emit_fatal(RLinkEmptyVersionNumber),
                        CodegenError::EncodingVersionMismatch { version_array, rlink_version } => {
                            dcx.emit_fatal(RLinkEncodingVersionMismatch {
                                version_array,
                                rlink_version,
                            })
                        }
                        CodegenError::RustcVersionMismatch { rustc_version } => {
                            dcx.emit_fatal(RLinkRustcVersionMismatch {
                                rustc_version,
                                current_version: sess.cfg_version,
                            })
                        }
                        CodegenError::CorruptFile => {
                            dcx.emit_fatal(RlinkCorruptFile { file });
                        }
                    };
                }
            };
        compiler.codegen_backend.link(sess, compiled_modules, crate_info, metadata, &outputs);
    } else {
        dcx.emit_fatal(RlinkNotAFile {});
    }
}

fn list_metadata(sess: &Session, metadata_loader: &dyn MetadataLoader) {
    match sess.io.input {
        Input::File(ref path) => {
            let mut v = Vec::new();
            locator::list_file_metadata(
                &sess.target,
                path,
                metadata_loader,
                &mut v,
                &sess.opts.unstable_opts.ls,
                sess.cfg_version,
            )
            .unwrap();
            safe_println!("{}", String::from_utf8(v).unwrap());
        }
        Input::Str { .. } => {
            sess.dcx().fatal("cannot list metadata for stdin");
        }
    }
}

fn print_crate_info(
    codegen_backend: &dyn CodegenBackend,
    sess: &Session,
    parse_attrs: bool,
) -> Compilation {
    use rustc_session::config::PrintKind::*;
    // This import prevents the following code from using the printing macros
    // used by the rest of the module. Within this function, we only write to
    // the output specified by `sess.io.output_file`.
    #[allow(unused_imports)]
    use {do_not_use_safe_print as safe_print, do_not_use_safe_print as safe_println};

    // NativeStaticLibs and LinkArgs are special - printed during linking
    // (empty iterator returns true)
    if sess.opts.prints.iter().all(|p| p.kind == NativeStaticLibs || p.kind == LinkArgs) {
        return Compilation::Continue;
    }

    let attrs = if parse_attrs {
        let result = parse_crate_attrs(sess);
        match result {
            Ok(attrs) => Some(attrs),
            Err(parse_error) => {
                parse_error.emit();
                return Compilation::Stop;
            }
        }
    } else {
        None
    };

    for req in &sess.opts.prints {
        let mut crate_info = String::new();
        macro println_info($($arg:tt)*) {
            crate_info.write_fmt(format_args!("{}\n", format_args!($($arg)*))).unwrap()
        }

        match req.kind {
            TargetList => {
                let mut targets = rustc_target::spec::TARGETS.to_vec();
                targets.sort_unstable();
                println_info!("{}", targets.join("\n"));
            }
            HostTuple => println_info!("{}", rustc_session::config::host_tuple()),
            Sysroot => println_info!("{}", sess.opts.sysroot.path().display()),
            TargetLibdir => println_info!("{}", sess.target_tlib_path.dir.display()),
            TargetSpecJson => {
                println_info!("{}", serde_json::to_string_pretty(&sess.target.to_json()).unwrap());
            }
            TargetSpecJsonSchema => {
                let schema = rustc_target::spec::json_schema();
                println_info!("{}", serde_json::to_string_pretty(&schema).unwrap());
            }
            AllTargetSpecsJson => {
                let mut targets = BTreeMap::new();
                for name in rustc_target::spec::TARGETS {
                    let triple = TargetTuple::from_tuple(name);
                    let target = Target::expect_builtin(&triple);
                    targets.insert(name, target.to_json());
                }
                println_info!("{}", serde_json::to_string_pretty(&targets).unwrap());
            }
            FileNames => {
                let Some(attrs) = attrs.as_ref() else {
                    // no crate attributes, print out an error and exit
                    return Compilation::Continue;
                };
                let t_outputs = rustc_interface::util::build_output_filenames(attrs, sess);
                let crate_name = passes::get_crate_name(sess, attrs);
                let crate_types = collect_crate_types(
                    sess,
                    &codegen_backend.supported_crate_types(sess),
                    codegen_backend.name(),
                    attrs,
                    DUMMY_SP,
                );
                for &style in &crate_types {
                    let fname = rustc_session::output::filename_for_input(
                        sess, style, crate_name, &t_outputs,
                    );
                    println_info!("{}", fname.as_path().file_name().unwrap().to_string_lossy());
                }
            }
            CrateName => {
                let Some(attrs) = attrs.as_ref() else {
                    // no crate attributes, print out an error and exit
                    return Compilation::Continue;
                };
                println_info!("{}", passes::get_crate_name(sess, attrs));
            }
            CrateRootLintLevels => {
                let Some(attrs) = attrs.as_ref() else {
                    // no crate attributes, print out an error and exit
                    return Compilation::Continue;
                };
                let crate_name = passes::get_crate_name(sess, attrs);
                let lint_store = crate::unerased_lint_store(sess);
                let features = rustc_expand::config::features(sess, attrs, crate_name);
                let registered_tools = rustc_resolve::registered_tools_ast(sess.dcx(), attrs, sess);
                let builder = rustc_lint::LintLevelsBuilder::crate_root(
                    sess,
                    &features,
                    true,
                    lint_store,
                    &registered_tools,
                    attrs,
                );
                for lint in lint_store.get_lints() {
                    if let Some(feature_symbol) = lint.feature_gate
                        && !features.enabled(feature_symbol)
                    {
                        // lint is unstable and feature gate isn't active, don't print
                        continue;
                    }
                    let level = builder.lint_level_spec(lint).level();
                    println_info!("{}={}", lint.name_lower(), level.as_str());
                }
            }
            Cfg => {
                let mut cfgs = sess
                    .config
                    .iter()
                    .filter_map(|&(name, value)| {
                        // On stable, exclude unstable flags.
                        if !sess.is_nightly_build()
                            && find_gated_cfg(|cfg_sym| cfg_sym == name).is_some()
                        {
                            return None;
                        }

                        if let Some(value) = value {
                            Some(format!("{name}=\"{value}\""))
                        } else {
                            Some(name.to_string())
                        }
                    })
                    .collect::<Vec<String>>();

                cfgs.sort();
                for cfg in cfgs {
                    println_info!("{cfg}");
                }
            }
            CheckCfg => {
                let mut check_cfgs: Vec<String> = Vec::with_capacity(410);

                // INSTABILITY: We are sorting the output below.
                #[allow(rustc::potential_query_instability)]
                for (name, expected_values) in &sess.check_config.expecteds {
                    use crate::config::ExpectedValues;
                    match expected_values {
                        ExpectedValues::Any => {
                            check_cfgs.push(format!("cfg({name}, values(any()))"))
                        }
                        ExpectedValues::Some(values) => {
                            let mut values: Vec<_> = values
                                .iter()
                                .map(|value| {
                                    if let Some(value) = value {
                                        format!("\"{value}\"")
                                    } else {
                                        "none()".to_string()
                                    }
                                })
                                .collect();

                            values.sort_unstable();

                            let values = values.join(", ");

                            check_cfgs.push(format!("cfg({name}, values({values}))"))
                        }
                    }
                }

                check_cfgs.sort_unstable();
                if !sess.check_config.exhaustive_names && sess.check_config.exhaustive_values {
                    println_info!("cfg(any())");
                }
                for check_cfg in check_cfgs {
                    println_info!("{check_cfg}");
                }
            }
            CallingConventions => {
                let calling_conventions = rustc_abi::all_names();
                println_info!("{}", calling_conventions.join("\n"));
            }
            BackendHasMnemonic => {
                let has_mnemonic: bool =
                    codegen_backend.has_mnemonic(sess, req.arg.as_ref().unwrap());
                println_info!("{has_mnemonic}");
            }
            BackendHasZstd => {
                let has_zstd: bool = codegen_backend.has_zstd();
                println_info!("{has_zstd}");
            }
            RelocationModels
            | CodeModels
            | TlsModels
            | TargetCPUs
            | StackProtectorStrategies
            | TargetFeatures => {
                codegen_backend.print(req, &mut crate_info, sess);
            }
            // Any output here interferes with Cargo's parsing of other printed output
            NativeStaticLibs => {}
            LinkArgs => {}
            SplitDebuginfo => {
                use rustc_target::spec::SplitDebuginfo::{Off, Packed, Unpacked};

                for split in &[Off, Packed, Unpacked] {
                    if sess.target.options.supported_split_debuginfo.contains(split) {
                        println_info!("{split}");
                    }
                }
            }
            DeploymentTarget => {
                if sess.target.is_like_darwin {
                    println_info!(
                        "{}={}",
                        rustc_target::spec::apple::deployment_target_env_var(&sess.target.os),
                        sess.apple_deployment_target().fmt_pretty(),
                    )
                } else {
                    sess.dcx().fatal("only Apple targets currently support deployment version info")
                }
            }
            SupportedCrateTypes => {
                let backend_supported = codegen_backend.supported_link_crate_types(sess);
                let supported_crate_types = CrateType::all()
                    .iter()
                    .filter(|(_, crate_type)| backend_supported.contains(crate_type))
                    .filter(|(_, crate_type)| !invalid_output_for_target(sess, *crate_type))
                    .filter(|(_, crate_type)| *crate_type != CrateType::Sdylib)
                    .map(|(crate_type_sym, _)| *crate_type_sym)
                    .collect::<BTreeSet<_>>();
                for supported_crate_type in supported_crate_types {
                    println_info!("{}", supported_crate_type.as_str());
                }
            }
        }

        req.out.overwrite(&crate_info, sess);
    }
    Compilation::Stop
}

/// Prints version information
///
/// NOTE: this is a macro to support drivers built at a different time than the main `rustc_driver` crate.
pub macro version($early_dcx: expr, $binary: literal, $matches: expr) {
    fn unw(x: Option<&str>) -> &str {
        x.unwrap_or("unknown")
    }
    $crate::version_at_macro_invocation(
        $early_dcx,
        $binary,
        $matches,
        unw(option_env!("CFG_VERSION")),
        unw(option_env!("CFG_VER_HASH")),
        unw(option_env!("CFG_VER_DATE")),
        unw(option_env!("CFG_RELEASE")),
    )
}

#[doc(hidden)] // use the macro instead
pub fn version_at_macro_invocation(
    early_dcx: &EarlyDiagCtxt,
    binary: &str,
    matches: &getopts::Matches,
    version: &str,
    commit_hash: &str,
    commit_date: &str,
    release: &str,
) {
    let _compiler_backend_route_guard =
        config::enter_compiler_backend_route(config::CompilerBackendRoute::BackendCapable)
            .unwrap_or_else(|error| early_dcx.early_fatal(error));
    version_at_macro_invocation_with_frontend_policy(
        early_dcx,
        binary,
        matches,
        FrontendTrustPolicy::EmbeddedNoOfficialEvidence,
        version,
        commit_hash,
        commit_date,
        release,
    );
}

fn compiler_version_with_frontend_policy(
    early_dcx: &EarlyDiagCtxt,
    matches: &getopts::Matches,
    frontend_policy: FrontendTrustPolicy,
) {
    fn unw(value: Option<&str>) -> &str {
        value.unwrap_or("unknown")
    }
    version_at_macro_invocation_with_frontend_policy(
        early_dcx,
        "rustc",
        matches,
        frontend_policy,
        unw(option_env!("CFG_VERSION")),
        unw(option_env!("CFG_VER_HASH")),
        unw(option_env!("CFG_VER_DATE")),
        unw(option_env!("CFG_RELEASE")),
    );
}

fn version_at_macro_invocation_with_frontend_policy(
    early_dcx: &EarlyDiagCtxt,
    binary: &str,
    matches: &getopts::Matches,
    frontend_policy: FrontendTrustPolicy,
    version: &str,
    commit_hash: &str,
    commit_date: &str,
    release: &str,
) {
    validate_frontend_pre_backend_authority(early_dcx, matches, frontend_policy);
    let verbose = matches.opt_present("verbose");

    let display_binary = trust_display_binary(binary);
    let mut version = version.to_string();
    let mut release = release.to_string();
    let tmp;
    if let Ok(force_version) = std::env::var("RUSTC_OVERRIDE_VERSION_STRING") {
        tmp = force_version;
        version = tmp.clone();
        release = tmp;
    }

    // Trust: drop-in by construction. The version line is a machine-parsed contract — the
    // Cargo ecosystem's version-detecting build scripts (libc's `build.rs`, `autocfg`,
    // `rustc_version`) split `--version`/`-vV` output and assert the leading token is `rustc`
    // (e.g. libc asserts the first `.`-split piece equals `"rustc 1"`). Branding the leading
    // token as `trustc` broke those builds. So lead with the canonical `rustc` and preserve the
    // Trust binary identity as a parenthetical — precisely how upstream rustc annotates its own
    // version with `(<commit> <date>)`. The `binary:` field below still reports the real
    // invoked binary (`trustc`) for human/identity use; parsers key off the leading line and
    // `release:`, both of which are now drop-in.
    //
    // The number here is deliberately NOT Trust's version. It comes from
    // `src/rust-compat-version` and says which Rust this toolchain is
    // compatible with; Trust's own `major.minor.dev` version is a separate line
    // (`src/version` -> CFG_TRUST_VERSION), reported as `trust:` below and by
    // `targo trust version`. Keeping them apart is what lets Trust be 0.1.0
    // without a build script concluding the compiler predates Rust 1.0.
    // The parenthetical carries the toolchain's OWN identity and version
    // (`(trustc 0.1.0)`) — the leading `rustc` token is untouchable (the
    // ecosystem's version-sniffing build scripts assert it; see the block
    // comment above), so this parenthetical is where trustc introduces
    // itself honestly instead of wearing the compat token as its name.
    let trust_brand = if display_binary == "rustc" {
        String::new()
    } else {
        match option_env!("CFG_TRUST_VERSION") {
            Some(trust_version) => format!(" ({display_binary} {trust_version})"),
            None => format!(" ({display_binary})"),
        }
    };
    safe_println!("rustc {version}{trust_brand}");

    if verbose {
        safe_println!("binary: {display_binary}");
        safe_println!("commit-hash: {commit_hash}");
        safe_println!("commit-date: {commit_date}");
        safe_println!("host: {}", config::host_tuple());
        safe_println!("release: {release}");
        safe_println!("trust: {}", option_env!("CFG_TRUST_VERSION").unwrap_or("unknown"));

        get_backend_from_raw_matches_with_frontend_policy(early_dcx, matches, frontend_policy)
            .print_version();
    }
}

pub fn trust_display_binary(binary: &str) -> String {
    let invoked_name = std::env::args()
        .next()
        .and_then(|arg| std::path::Path::new(&arg).file_name().map(|name| name.to_owned()))
        .and_then(|name| name.into_string().ok());

    match (binary, invoked_name.as_deref()) {
        ("rustc", Some("trustc")) | ("rustc", Some("trustc.exe")) => "trustc".to_string(),
        ("rustdoc", Some("trustdoc")) | ("rustdoc", Some("trustdoc.exe")) => "trustdoc".to_string(),
        _ => binary.to_string(),
    }
}

fn trust_invoked_binary(default: &str) -> String {
    let invoked_name = std::env::args()
        .next()
        .and_then(|arg| std::path::Path::new(&arg).file_stem().map(|name| name.to_owned()))
        .and_then(|name| name.into_string().ok());

    match invoked_name {
        Some(name) if matches!(name.as_str(), "trustc" | "trustdoc") => name,
        _ => default.to_string(),
    }
}

fn usage(verbose: bool, include_unstable_options: bool, nightly_build: bool) {
    let display_binary = trust_display_binary("rustc");
    let mut options = getopts::Options::new();
    for option in config::rustc_optgroups()
        .iter()
        .filter(|x| verbose || !x.is_verbose_help_only)
        .filter(|x| include_unstable_options || x.is_stable())
    {
        option.apply(&mut options);
    }
    let message = format!("Usage: {display_binary} [OPTIONS] INPUT");
    let nightly_help = if nightly_build {
        "\n    -Z help             Print unstable compiler options"
    } else {
        ""
    };
    let verbose_help = if verbose {
        String::new()
    } else {
        format!("\n    --help -v           Print the full set of options {display_binary} accepts")
    };
    let at_path = if verbose {
        "    @path               Read newline separated options from `path`\n"
    } else {
        ""
    };
    safe_println!(
        "{options}{at_path}\nAdditional help:
    -C help             Print codegen options
    -W help             \
              Print 'lint' options and default settings{nightly}{verbose}\n",
        options = options.usage(&message),
        at_path = at_path,
        nightly = nightly_help,
        verbose = verbose_help
    );
}

fn print_wall_help() {
    let compiler = trust_display_binary("rustc");
    safe_println!(
        "
The flag `-Wall` does not exist in `{compiler}`. Most useful lints are enabled by
default. Use `{compiler} -W help` to see all available lints. It's more common to put
warning settings in the crate root using `#![warn(LINT_NAME)]` instead of using
the command line flag directly.
"
    );
}

/// Write to stdout lint command options, together with a list of all available lints
pub fn describe_lints(sess: &Session, registered_lints: bool) {
    safe_println!(
        "
Available lint options:
    -W <foo>           Warn about <foo>
    -A <foo>           Allow <foo>
    -D <foo>           Deny <foo>
    -F <foo>           Forbid <foo> (deny <foo> and all attempts to override)

"
    );

    fn sort_lints(sess: &Session, mut lints: Vec<&'static Lint>) -> Vec<&'static Lint> {
        // The sort doesn't case-fold but it's doubtful we care.
        lints.sort_by_cached_key(|x: &&Lint| (x.default_level(sess.edition()), x.name));
        lints
    }

    fn sort_lint_groups(
        lints: Vec<(&'static str, Vec<LintId>, bool)>,
    ) -> Vec<(&'static str, Vec<LintId>)> {
        let mut lints: Vec<_> = lints.into_iter().map(|(x, y, _)| (x, y)).collect();
        lints.sort_by_key(|l| l.0);
        lints
    }

    let lint_store = unerased_lint_store(sess);
    let (loaded, builtin): (Vec<_>, _) =
        lint_store.get_lints().iter().cloned().partition(|&lint| lint.is_externally_loaded);
    let loaded = sort_lints(sess, loaded);
    let builtin = sort_lints(sess, builtin);

    let (loaded_groups, builtin_groups): (Vec<_>, _) =
        lint_store.get_lint_groups().partition(|&(.., p)| p);
    let loaded_groups = sort_lint_groups(loaded_groups);
    let builtin_groups = sort_lint_groups(builtin_groups);

    let max_name_len =
        loaded.iter().chain(&builtin).map(|&s| s.name.chars().count()).max().unwrap_or(0);
    let compiler = trust_display_binary("rustc");
    let padded = |x: &str| {
        let mut s = " ".repeat(max_name_len - x.chars().count());
        s.push_str(x);
        s
    };

    safe_println!("Lint checks provided by {compiler}:\n");

    let print_lints = |lints: Vec<&Lint>| {
        safe_println!("    {}  {:7.7}  {}", padded("name"), "default", "meaning");
        safe_println!("    {}  {:7.7}  {}", padded("----"), "-------", "-------");
        for lint in lints {
            let name = lint.name_lower().replace('_', "-");
            safe_println!(
                "    {}  {:7.7}  {}",
                padded(&name),
                lint.default_level(sess.edition()).as_str(),
                lint.desc
            );
        }
        safe_println!("\n");
    };

    print_lints(builtin);

    let max_name_len = max(
        "warnings".len(),
        loaded_groups
            .iter()
            .chain(&builtin_groups)
            .map(|&(s, _)| s.chars().count())
            .max()
            .unwrap_or(0),
    );

    let padded = |x: &str| {
        let mut s = " ".repeat(max_name_len - x.chars().count());
        s.push_str(x);
        s
    };

    safe_println!("Lint groups provided by {compiler}:\n");

    let print_lint_groups = |lints: Vec<(&'static str, Vec<LintId>)>, all_warnings| {
        safe_println!("    {}  sub-lints", padded("name"));
        safe_println!("    {}  ---------", padded("----"));

        if all_warnings {
            safe_println!("    {}  all lints that are set to issue warnings", padded("warnings"));
        }

        for (name, to) in lints {
            let name = name.to_lowercase().replace('_', "-");
            let desc = to
                .into_iter()
                .map(|x| x.to_string().replace('_', "-"))
                .collect::<Vec<String>>()
                .join(", ");
            safe_println!("    {}  {}", padded(&name), desc);
        }
        safe_println!("\n");
    };

    print_lint_groups(builtin_groups, true);

    match (registered_lints, loaded.len(), loaded_groups.len()) {
        (false, 0, _) | (false, _, 0) => {
            safe_println!("Lint tools like Clippy can load additional lints and lint groups.");
        }
        (false, ..) => panic!("didn't load additional lints but got them anyway!"),
        (true, 0, 0) => {
            safe_println!("This crate does not load any additional lints or lint groups.")
        }
        (true, l, g) => {
            if l > 0 {
                safe_println!("Lint checks loaded by this crate:\n");
                print_lints(loaded);
            }
            if g > 0 {
                safe_println!("Lint groups loaded by this crate:\n");
                print_lint_groups(loaded_groups, false);
            }
        }
    }
}

/// Show help for flag categories shared between rustdoc and rustc.
///
/// Returns whether a help option was printed.
pub fn describe_flag_categories(early_dcx: &EarlyDiagCtxt, matches: &Matches) -> bool {
    let _compiler_backend_route_guard =
        config::enter_compiler_backend_route(config::CompilerBackendRoute::BackendCapable)
            .unwrap_or_else(|error| early_dcx.early_fatal(error));
    validate_frontend_pre_backend_authority(
        early_dcx,
        matches,
        FrontendTrustPolicy::EmbeddedNoOfficialEvidence,
    );
    // Handle the special case of -Wall.
    let wall = matches.opt_strs("W");
    if wall.iter().any(|x| *x == "all") {
        print_wall_help();
        return true;
    }

    // Don't handle -W help here, because we might first load additional lints.
    let debug_flags = matches.opt_strs("Z");
    if debug_flags.iter().any(|x| *x == "help") {
        describe_unstable_flags();
        return true;
    }

    let cg_flags = matches.opt_strs("C");
    if cg_flags.iter().any(|x| *x == "help") {
        describe_codegen_flags();
        return true;
    }

    if cg_flags.iter().any(|x| *x == "passes=list") {
        get_backend_from_raw_matches(early_dcx, matches).print_passes();
        return true;
    }

    false
}

/// Get the codegen backend based on the raw [`Matches`].
///
/// `rustc -vV` and `rustc -Cpasses=list` need to get the codegen backend before we have parsed all
/// arguments and created a [`Session`]. This function reads `-Zcodegen-backend`, `--target` and
/// `--sysroot` without validating any other arguments and loads the codegen backend based on these
/// arguments.
fn get_backend_from_raw_matches(
    early_dcx: &EarlyDiagCtxt,
    matches: &Matches,
) -> Box<dyn CodegenBackend> {
    get_backend_from_raw_matches_with_frontend_policy(
        early_dcx,
        matches,
        FrontendTrustPolicy::EmbeddedNoOfficialEvidence,
    )
}

fn get_backend_from_raw_matches_with_frontend_policy(
    early_dcx: &EarlyDiagCtxt,
    matches: &Matches,
    frontend_policy: FrontendTrustPolicy,
) -> Box<dyn CodegenBackend> {
    let debug_flags = matches.opt_strs("Z");
    let backend_name = debug_flags
        .iter()
        .find_map(|x| x.strip_prefix("codegen-backend=").or(x.strip_prefix("codegen_backend=")));
    let unstable_options = debug_flags.iter().find(|x| *x == "unstable-options").is_some();
    let target_tuple = parse_target_triple(early_dcx, matches);
    let sysroot = Sysroot::new(matches.opt_str("sysroot").map(PathBuf::from));
    let target =
        config::build_target_config(early_dcx, &target_tuple, sysroot.path(), unstable_options);

    if frontend_policy.requires_evidence_inert_backend()
        && let Some(error) = config::evidence_inert_target_llvm_args_error(
            &target_tuple,
            !target.options.llvm_args.is_empty(),
        )
    {
        early_dcx.early_fatal(error);
    }

    match frontend_policy {
        FrontendTrustPolicy::CanonicalTrustc | FrontendTrustPolicy::EmbeddedNoOfficialEvidence => {
            get_codegen_backend(early_dcx, &sysroot, backend_name, &target)
        }
        FrontendTrustPolicy::EvidenceInert => {
            let effective_backend = util::effective_codegen_backend_name(backend_name, &target);
            util::get_no_trust_evidence_codegen_backend(backend_name, &target).unwrap_or_else(|| {
                early_dcx.early_fatal(format!(
                    "NoTrustEvidence compiler frontend rejects effective codegen backend `{effective_backend}`; early compiler modes require an already-linked `llvm` or `dummy` backend"
                ))
            })
        }
    }
}

fn describe_unstable_flags() {
    safe_println!("\nAvailable unstable options:\n");
    print_flag_list("-Z", config::Z_OPTIONS);
}

fn describe_codegen_flags() {
    safe_println!("\nAvailable codegen options:\n");
    print_flag_list("-C", config::CG_OPTIONS);
}

fn print_flag_list<T>(cmdline_opt: &str, flag_list: &[OptionDesc<T>]) {
    let max_len =
        flag_list.iter().map(|opt_desc| opt_desc.name().chars().count()).max().unwrap_or(0);

    for opt_desc in flag_list {
        safe_println!(
            "    {} {:>width$}=val -- {}",
            cmdline_opt,
            opt_desc.name().replace('_', "-"),
            opt_desc.desc(),
            width = max_len
        );
    }
}

pub enum HandledOptions {
    /// Parsing failed, or we parsed a flag causing an early exit
    None,
    /// Successful parsing
    Normal(getopts::Matches),
    /// Parsing succeeded, but we received one or more 'help' flags
    /// The compiler should proceed only until a possible `-W help` flag has been processed
    HelpOnly(getopts::Matches),
}

/// Process command line options. Emits messages as appropriate. If compilation
/// should continue, returns a getopts::Matches object parsed from args,
/// otherwise returns `None`.
///
/// The compiler's handling of options is a little complicated as it ties into
/// our stability story. The current intention of each compiler option is to
/// have one of two modes:
///
/// 1. An option is stable and can be used everywhere.
/// 2. An option is unstable, and can only be used on nightly.
///
/// Like unstable library and language features, however, unstable options have
/// always required a form of "opt in" to indicate that you're using them. This
/// provides the easy ability to scan a code base to check to see if anything
/// unstable is being used. Currently, this "opt in" is the `-Z` "zed" flag.
///
/// All options behind `-Z` are considered unstable by default. Other top-level
/// options can also be considered unstable, and they were unlocked through the
/// `-Z unstable-options` flag. Note that `-Z` remains to be the root of
/// instability in both cases, though.
///
/// So with all that in mind, the comments below have some more detail about the
/// contortions done here to get things to work out correctly.
///
/// This does not need to be `pub` for rustc itself, but @chaosite needs it to
/// be public when using rustc as a library, see
/// <https://github.com/rust-lang/rust/commit/2b4c33817a5aaecabf4c6598d41e190080ec119e>
pub fn handle_options(early_dcx: &EarlyDiagCtxt, args: &[String]) -> HandledOptions {
    let _compiler_backend_route_guard =
        config::enter_compiler_backend_route(config::CompilerBackendRoute::BackendCapable)
            .unwrap_or_else(|error| early_dcx.early_fatal(error));
    handle_options_with_frontend_policy(
        early_dcx,
        args,
        FrontendTrustPolicy::EmbeddedNoOfficialEvidence,
    )
}

fn handle_options_with_frontend_policy(
    early_dcx: &EarlyDiagCtxt,
    args: &[String],
    frontend_policy: FrontendTrustPolicy,
) -> HandledOptions {
    // Parse with *all* options defined in the compiler, we don't worry about
    // option stability here we just want to parse as much as possible.
    let mut options = getopts::Options::new();
    let optgroups = config::rustc_optgroups();
    for option in &optgroups {
        option.apply(&mut options);
    }
    let matches = options.parse(args).unwrap_or_else(|e| {
        let msg: Option<String> = match e {
            getopts::Fail::UnrecognizedOption(ref opt) => CG_OPTIONS
                .iter()
                .map(|opt_desc| ('C', opt_desc.name()))
                .chain(Z_OPTIONS.iter().map(|opt_desc| ('Z', opt_desc.name())))
                .find(|&(_, name)| *opt == name.replace('_', "-"))
                .map(|(flag, _)| format!("{e}. Did you mean `-{flag} {opt}`?")),
            getopts::Fail::ArgumentMissing(ref opt) => {
                optgroups.iter().find(|option| option.name == opt).map(|option| {
                    // Print the help just for the option in question.
                    let mut options = getopts::Options::new();
                    option.apply(&mut options);
                    // getopt requires us to pass a function for joining an iterator of
                    // strings, even though in this case we expect exactly one string.
                    options.usage_with_format(|it| {
                        it.fold(format!("{e}\nUsage:"), |a, b| a + "\n" + &b)
                    })
                })
            }
            _ => None,
        };
        early_dcx.early_fatal(msg.unwrap_or_else(|| e.to_string()));
    });

    // For all options we just parsed, we check a few aspects:
    //
    // * If the option is stable, we're all good
    // * If the option wasn't passed, we're all good
    // * If `-Z unstable-options` wasn't passed (and we're not a -Z option
    //   ourselves), then we require the `-Z unstable-options` flag to unlock
    //   this option that was passed.
    // * If we're a nightly compiler, then unstable options are now unlocked, so
    //   we're good to go.
    // * Otherwise, if we're an unstable option then we generate an error
    //   (unstable option being used on stable)
    nightly_options::check_nightly_options(early_dcx, &matches, &config::rustc_optgroups());

    // This must precede every early mode below. `-vV` and `-Cpasses=list`
    // construct the selected codegen backend while processing options, so a
    // later typed-options check would execute an attacker-selected backend
    // before a deauthorized frontend could reject it.
    validate_frontend_pre_backend_authority(early_dcx, &matches, frontend_policy);

    if let Some(mode) = authenticated_pre_session_early_exit(&matches, args) {
        early_dcx.early_fatal(format!(
            "-Ztrust-verify-session requests authenticated verification coverage and cannot be combined with {mode}"
        ));
    }

    if let Some(mode) = direct_ir_pre_typed_options_early_exit(&matches, args) {
        early_dcx.early_fatal(format!(
            "-Ztrust-dump=ir:<dir> requests direct-TrustIR artifact publication and cannot be combined with {mode}, which exits before typed publication-target validation"
        ));
    }

    // Handle the special case of -Wall.
    let wall = matches.opt_strs("W");
    if wall.iter().any(|x| *x == "all") {
        print_wall_help();
        return HandledOptions::None;
    }

    if handle_help(&matches, args) {
        return HandledOptions::HelpOnly(matches);
    }

    if matches.opt_strs("C").iter().any(|x| x == "passes=list") {
        get_backend_from_raw_matches_with_frontend_policy(early_dcx, &matches, frontend_policy)
            .print_passes();
        return HandledOptions::None;
    }

    if matches.opt_present("version") {
        compiler_version_with_frontend_policy(early_dcx, &matches, frontend_policy);
        return HandledOptions::None;
    }

    warn_on_confusing_output_filename_flag(early_dcx, &matches, args);

    HandledOptions::Normal(matches)
}

/// Handle help options in the order they are provided, ignoring other flags. Returns if any options were handled
/// Handled options:
/// - `-h`/`--help`/empty arguments
/// - `-Z help`
/// - `-C help`
/// NOTE: `-W help` is NOT handled here, as additional lints may be loaded.
pub fn handle_help(matches: &getopts::Matches, args: &[String]) -> bool {
    let opt_pos = |opt| matches.opt_positions(opt).first().copied();
    let opt_help_pos = |opt| {
        matches
            .opt_strs_pos(opt)
            .iter()
            .filter_map(|(pos, oval)| if oval == "help" { Some(*pos) } else { None })
            .next()
    };
    let help_pos = if args.is_empty() { Some(0) } else { opt_pos("h").or_else(|| opt_pos("help")) };
    let zhelp_pos = opt_help_pos("Z");
    let chelp_pos = opt_help_pos("C");
    let print_help = || {
        // Only show unstable options in --help if we accept unstable options.
        let unstable_enabled = nightly_options::is_unstable_enabled(&matches);
        let nightly_build = nightly_options::match_is_nightly_build(&matches);
        usage(matches.opt_present("verbose"), unstable_enabled, nightly_build);
    };

    let mut helps = [
        (help_pos, &print_help as &dyn Fn()),
        (zhelp_pos, &describe_unstable_flags),
        (chelp_pos, &describe_codegen_flags),
    ];
    helps.sort_by_key(|(pos, _)| pos.clone());
    let mut printed_any = false;
    for printer in helps.iter().filter_map(|(pos, func)| pos.is_some().then_some(func)) {
        printer();
        printed_any = true;
    }
    printed_any
}

/// Warn if `-o` is used without a space between the flag name and the value
/// and the value is a high-value confusables,
/// e.g. `-optimize` instead of `-o optimize`, see issue #142812.
fn warn_on_confusing_output_filename_flag(
    early_dcx: &EarlyDiagCtxt,
    matches: &getopts::Matches,
    args: &[String],
) {
    fn eq_ignore_separators(s1: &str, s2: &str) -> bool {
        let s1 = s1.replace('-', "_");
        let s2 = s2.replace('-', "_");
        s1 == s2
    }

    if let Some(name) = matches.opt_str("o")
        && let Some(suspect) = args.iter().find(|arg| arg.starts_with("-o") && *arg != "-o")
    {
        let filename = suspect.trim_prefix("-");
        let optgroups = config::rustc_optgroups();
        let fake_args = ["optimize", "o0", "o1", "o2", "o3", "ofast", "og", "os", "oz"];

        // Check if provided filename might be confusing in conjunction with `-o` flag,
        // i.e. consider `-o{filename}` such as `-optimize` with `filename` being `ptimize`.
        // There are high-value confusables, for example:
        // - Long name of flags, e.g. `--out-dir` vs `-out-dir`
        // - C compiler flag, e.g. `optimize`, `o0`, `o1`, `o2`, `o3`, `ofast`.
        // - Codegen flags, e.g. `pt-level` of `-opt-level`.
        if optgroups.iter().any(|option| eq_ignore_separators(option.long_name(), filename))
            || config::CG_OPTIONS.iter().any(|option| eq_ignore_separators(option.name(), filename))
            || fake_args.iter().any(|arg| eq_ignore_separators(arg, filename))
        {
            early_dcx.early_warn(
                "option `-o` has no space between flag name and value, which can be confusing",
            );
            early_dcx.early_note(format!(
                "output filename `-o {name}` is applied instead of a flag named `o{name}`"
            ));
            early_dcx.early_help(format!(
                "insert a space between `-o` and `{name}` if this is intentional: `-o {name}`"
            ));
        }
    }
}

fn parse_crate_attrs<'a>(sess: &'a Session) -> PResult<'a, ast::AttrVec> {
    let mut parser = unwrap_or_emit_fatal(match &sess.io.input {
        Input::File(file) => {
            new_parser_from_file(&sess.psess, file, StripTokens::ShebangAndFrontmatter, None)
        }
        Input::Str { name, input } => new_parser_from_source_str(
            &sess.psess,
            name.clone(),
            input.clone(),
            StripTokens::ShebangAndFrontmatter,
        ),
    });
    parser.parse_inner_attributes()
}

/// Variant of `catch_fatal_errors` for the `interface::Result` return type
/// that also computes the exit code.
pub fn catch_with_exit_code<T: Termination>(f: impl FnOnce() -> T) -> ExitCode {
    match catch_fatal_errors(f) {
        Ok(status) => status.report(),
        _ => ExitCode::FAILURE,
    }
}

static ICE_PATH: OnceLock<Option<PathBuf>> = OnceLock::new();
static ICE_DEFAULT_COMPILER: OnceLock<&'static str> = OnceLock::new();

fn ice_default_compiler() -> &'static str {
    ICE_DEFAULT_COMPILER.get().copied().unwrap_or("trustc")
}

// This function should only be called from the ICE hook.
//
// The intended behavior is that `run_compiler` will invoke `ice_path_with_config` early in the
// initialization process to properly initialize the ICE_PATH static based on parsed CLI flags.
//
// Subsequent calls to either function will then return the proper ICE path as configured by
// the environment and cli flags
fn ice_path() -> &'static Option<PathBuf> {
    ice_path_with_config(None)
}

fn ice_path_with_config(config: Option<&UnstableOptions>) -> &'static Option<PathBuf> {
    if ICE_PATH.get().is_some() && config.is_some() && cfg!(debug_assertions) {
        tracing::warn!(
            "ICE_PATH has already been initialized -- files may be emitted at unintended paths"
        )
    }

    ICE_PATH.get_or_init(|| {
        if !rustc_feature::UnstableFeatures::from_environment(None).is_nightly_build() {
            return None;
        }
        let mut path = match std::env::var_os("RUSTC_ICE") {
            Some(s) => {
                if s == "0" {
                    // Explicitly opting out of writing ICEs to disk.
                    return None;
                }
                if let Some(unstable_opts) = config && unstable_opts.metrics_dir.is_some() {
                    tracing::warn!("ignoring -Zerror-metrics in favor of RUSTC_ICE for destination of ICE report files");
                }
                PathBuf::from(s)
            }
            None => config
                .and_then(|unstable_opts| unstable_opts.metrics_dir.to_owned())
                .or_else(|| std::env::current_dir().ok())
                .unwrap_or_default(),
        };
        // Don't use a standard datetime format because Windows doesn't support `:` in paths
        let file_now = jiff::Zoned::now().strftime("%Y-%m-%dT%H_%M_%S");
        let pid = std::process::id();
        let ice_prefix = trust_invoked_binary(ice_default_compiler());
        path.push(format!("{ice_prefix}-ice-{file_now}-{pid}.txt"));
        Some(path)
    })
}

pub static USING_INTERNAL_FEATURES: AtomicBool = AtomicBool::new(false);

/// Installs a panic hook that will print the ICE message on unexpected panics.
///
/// The hook is intended to be useable even by external tools. You can pass a custom
/// `bug_report_url`, or report arbitrary info in `extra_info`. Note that `extra_info` is called in
/// a context where *the thread is currently panicking*, so it must not panic or the process will
/// abort.
///
/// If you have no extra info to report, pass the empty closure `|_| ()` as the argument to
/// extra_info.
///
/// A custom rustc driver can skip calling this to set up a custom ICE hook.
pub fn install_ice_hook(bug_report_url: &'static str, extra_info: fn(&DiagCtxt)) {
    install_ice_hook_with_default_compiler(bug_report_url, "trustc", extra_info);
}

/// Installs a panic hook for a Trust tool whose compatibility executable name
/// does not identify the canonical product.
pub fn install_ice_hook_with_default_compiler(
    bug_report_url: &'static str,
    default_compiler: &'static str,
    extra_info: fn(&DiagCtxt),
) {
    let _ = ICE_DEFAULT_COMPILER.set(default_compiler);

    // If the user has not explicitly overridden "RUST_BACKTRACE", then produce
    // full backtraces. When a compiler ICE happens, we want to gather
    // as much information as possible to present in the issue opened
    // by the user. Compiler developers and other rustc users can
    // opt in to less-verbose backtraces by manually setting "RUST_BACKTRACE"
    // (e.g. `RUST_BACKTRACE=1`)
    if env::var_os("RUST_BACKTRACE").is_none() {
        // HACK: this check is extremely dumb, but we don't really need it to be smarter since this should only happen in the test suite anyway.
        let ui_testing = std::env::args().any(|arg| arg == "-Zui-testing");
        if env!("CFG_RELEASE_CHANNEL") == "dev" && !ui_testing {
            panic::set_backtrace_style(panic::BacktraceStyle::Short);
        } else {
            panic::set_backtrace_style(panic::BacktraceStyle::Full);
        }
    }

    panic::update_hook(Box::new(
        move |default_hook: &(dyn Fn(&PanicHookInfo<'_>) + Send + Sync + 'static),
              info: &PanicHookInfo<'_>| {
            // Lock stderr to prevent interleaving of concurrent panics.
            let _guard = io::stderr().lock();
            // If the error was caused by a broken pipe then this is not a bug.
            // Write the error and return immediately. See #98700.
            #[cfg(windows)]
            if let Some(msg) = info.payload().downcast_ref::<String>() {
                if msg.starts_with("failed printing to stdout: ") && msg.ends_with("(os error 232)")
                {
                    // the error code is already going to be reported when the panic unwinds up the stack
                    let early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());
                    let _ = early_dcx.early_err(msg.clone());
                    return;
                }
            };

            // Invoke the default handler, which prints the actual panic message and optionally a backtrace
            // Don't do this for delayed bugs, which already emit their own more useful backtrace.
            if !info.payload().is::<rustc_errors::DelayedBugPanic>() {
                default_hook(info);
                // Separate the output with an empty line
                eprintln!();

                if let Some(ice_path) = ice_path()
                    && let Ok(mut out) = File::options().create(true).append(true).open(ice_path)
                {
                    // The current implementation always returns `Some`.
                    let location = info.location().unwrap();
                    let msg = match info.payload().downcast_ref::<&'static str>() {
                        Some(s) => *s,
                        None => match info.payload().downcast_ref::<String>() {
                            Some(s) => &s[..],
                            None => "Box<dyn Any>",
                        },
                    };
                    let thread = std::thread::current();
                    let name = thread.name().unwrap_or("<unnamed>");
                    let _ = write!(
                        &mut out,
                        "thread '{name}' panicked at {location}:\n\
                        {msg}\n\
                        stack backtrace:\n\
                        {:#}",
                        std::backtrace::Backtrace::force_capture()
                    );
                }
            }

            // Print the ICE message
            report_ice(info, bug_report_url, extra_info, &USING_INTERNAL_FEATURES);
        },
    ));
}

/// Prints the ICE message, including query stack, but without backtrace.
///
/// The message will point the user at `bug_report_url` to report the ICE.
///
/// When `install_ice_hook` is called, this function will be called as the panic
/// hook.
fn report_ice(
    info: &panic::PanicHookInfo<'_>,
    bug_report_url: &str,
    extra_info: fn(&DiagCtxt),
    using_internal_features: &AtomicBool,
) {
    let emitter =
        Box::new(rustc_errors::annotate_snippet_emitter_writer::AnnotateSnippetEmitter::new(
            stderr_destination(rustc_errors::ColorConfig::Auto),
        ));
    let dcx = rustc_errors::DiagCtxt::new(emitter);
    let dcx = dcx.handle();

    // a .span_bug or .bug call has already printed what
    // it wants to print.
    if !info.payload().is::<rustc_errors::ExplicitBug>()
        && !info.payload().is::<rustc_errors::DelayedBugPanic>()
    {
        dcx.emit_err(session_diagnostics::Ice);
    }

    if using_internal_features.load(std::sync::atomic::Ordering::Relaxed) {
        dcx.emit_note(session_diagnostics::IceBugReportInternalFeature);
    } else {
        dcx.emit_note(session_diagnostics::IceBugReport { bug_report_url });

        // Only emit update nightly hint for users on nightly builds.
        if rustc_feature::UnstableFeatures::from_environment(None).is_nightly_build() {
            dcx.emit_note(session_diagnostics::UpdateNightlyNote);
        }
    }

    let version = util::version_str!().unwrap_or("unknown_version");
    let tuple = config::host_tuple();

    static FIRST_PANIC: AtomicBool = AtomicBool::new(true);

    let file = if let Some(path) = ice_path() {
        // Create the ICE dump target file.
        match crate::fs::File::options().create(true).append(true).open(path) {
            Ok(mut file) => {
                dcx.emit_note(session_diagnostics::IcePath { path: path.clone() });
                if FIRST_PANIC.swap(false, Ordering::SeqCst) {
                    let display_binary = trust_invoked_binary(ice_default_compiler());
                    let _ =
                        write!(file, "\n\n{display_binary} version: {version}\nplatform: {tuple}");
                }
                Some(file)
            }
            Err(err) => {
                // The path ICE couldn't be written to disk, provide feedback to the user as to why.
                dcx.emit_warn(session_diagnostics::IcePathError {
                    path: path.clone(),
                    error: err.to_string(),
                    env_var: std::env::var_os("RUSTC_ICE")
                        .map(PathBuf::from)
                        .map(|env_var| session_diagnostics::IcePathErrorEnv { env_var }),
                });
                None
            }
        }
    } else {
        None
    };

    dcx.emit_note(session_diagnostics::IceVersion {
        compiler: trust_invoked_binary(ice_default_compiler()),
        version,
        triple: tuple,
    });

    if let Some((flags, excluded_cargo_defaults)) = rustc_session::utils::extra_compiler_flags() {
        dcx.emit_note(session_diagnostics::IceFlags { flags: flags.join(" ") });
        if excluded_cargo_defaults {
            dcx.emit_note(session_diagnostics::IceExcludeCargoDefaults);
        }
    }

    // If backtraces are enabled, also print the query stack
    let backtrace = env::var_os("RUST_BACKTRACE").is_some_and(|x| &x != "0");

    let limit_frames = if backtrace { None } else { Some(2) };

    interface::try_print_query_stack(dcx, limit_frames, file);

    // We don't trust this callback not to panic itself, so run it at the end after we're sure we've
    // printed all the relevant info.
    extra_info(&dcx);

    #[cfg(windows)]
    if env::var("RUSTC_BREAK_ON_ICE").is_ok() {
        // Trigger a debugger if we crashed during bootstrap
        unsafe { windows::Win32::System::Diagnostics::Debug::DebugBreak() };
    }
}

/// This allows tools to enable rust logging without having to magically match rustc's
/// tracing crate version.
pub fn init_rustc_env_logger(early_dcx: &EarlyDiagCtxt) {
    init_logger(early_dcx, rustc_log::LoggerConfig::from_env("RUSTC_LOG"));
}

/// This allows tools to enable rust logging without having to magically match rustc's
/// tracing crate version. In contrast to `init_rustc_env_logger` it allows you to choose
/// the logger config directly rather than having to set an environment variable.
pub fn init_logger(early_dcx: &EarlyDiagCtxt, cfg: rustc_log::LoggerConfig) {
    if let Err(error) = rustc_log::init_logger(cfg) {
        early_dcx.early_fatal(error.to_string());
    }
}

/// This allows tools to enable rust logging without having to magically match rustc's
/// tracing crate version. In contrast to `init_rustc_env_logger`, it allows you to
/// choose the logger config directly rather than having to set an environment variable.
/// Moreover, in contrast to `init_logger`, it allows you to add a custom tracing layer
/// via `build_subscriber`, for example `|| Registry::default().with(custom_layer)`.
pub fn init_logger_with_additional_layer<F, T>(
    early_dcx: &EarlyDiagCtxt,
    cfg: rustc_log::LoggerConfig,
    build_subscriber: F,
) where
    F: FnOnce() -> T,
    T: rustc_log::BuildSubscriberRet,
{
    if let Err(error) = rustc_log::init_logger_with_additional_layer(cfg, build_subscriber) {
        early_dcx.early_fatal(error.to_string());
    }
}

/// Install our usual `ctrlc` handler, which sets [`rustc_const_eval::CTRL_C_RECEIVED`].
/// Making this handler optional lets tools can install a different handler, if they wish.
pub fn install_ctrlc_handler() {
    #[cfg(all(not(miri), not(target_family = "wasm")))]
    ctrlc::set_handler(move || {
        // Indicate that we have been signaled to stop, then give the rest of the compiler a bit of
        // time to check CTRL_C_RECEIVED and run its own shutdown logic, but after a short amount
        // of time exit the process. This sleep+exit ensures that even if nobody is checking
        // CTRL_C_RECEIVED, the compiler exits reasonably promptly.
        rustc_const_eval::CTRL_C_RECEIVED.store(true, Ordering::Relaxed);
        std::thread::sleep(std::time::Duration::from_millis(100));
        std::process::exit(1);
    })
    .expect("Unable to install ctrlc handler");
}

fn main_with_frontend_trust_policy(frontend_policy: FrontendTrustPolicy) -> ExitCode {
    let start_time = Instant::now();
    let start_rss = get_resident_set_size();

    let early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());

    init_rustc_env_logger(&early_dcx);
    signal_handler::install();
    let mut callbacks = TimePassesCallbacks::default();
    install_ice_hook(DEFAULT_BUG_REPORT_URL, |_| ());
    install_ctrlc_handler();

    let exit_code = catch_with_exit_code(|| {
        run_compiler_with_argfile_mode(
            &args::raw_args(&early_dcx),
            &mut callbacks,
            true,
            frontend_policy,
        )
    });

    if let Some(format) = callbacks.time_passes {
        let end_rss = get_resident_set_size();
        print_time_passes_entry("total", start_time.elapsed(), start_rss, end_rss, format);
    }

    exit_code
}

/// Entry point for the actual `rustc`/`trustc` compiler executable.
///
/// This route is callback-fixed, but its symbol visibility is not a security
/// boundary. Official proof acceptance must additionally authenticate the
/// exact executable and runtime image closure that ran it.
pub fn main() -> ExitCode {
    main_with_frontend_trust_policy(FrontendTrustPolicy::CanonicalTrustc)
}

/// Entry point exposed by the `rustc_driver` embedding facade.
///
/// It preserves host-rustc compatibility for tools such as Miri without
/// granting those executables official Trust evidence authority.
#[doc(hidden)]
pub fn embedded_main() -> ExitCode {
    main_with_frontend_trust_policy(FrontendTrustPolicy::EmbeddedNoOfficialEvidence)
}

// Trust: the driver-level `-Z` admission cases are Trust's and reach a large
// set of private helpers in this file, so they stay in the crate's own tree.
#[cfg(test)]
mod tests;
