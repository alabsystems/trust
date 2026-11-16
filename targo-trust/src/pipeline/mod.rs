// targo-trust pipeline: compiler invocation, rewrite loop, and standalone analysis.
//
// Submodule layout:
// - discovery: locate trustc next to targo-trust or in repo build dirs
// - probe: run a tiny crate through the discovered trustc to detect capabilities
// - surface: classify the linked Trust toolchain (targo, trustfmt, tippy, ...)
// - backend: assemble the verified lane (TRUST_TARGO_LANE_RUSTFLAGS) and the
//   trust-verify driver flags, and name (then ignore) ambient -Ztrust-*
//   RUSTFLAGS and TRUSTFLAGS
// - project_policy: adopt the Cargo project requirements and carry them to the
//   compile
// - transport: parse trustc's stderr JSON transport into VerificationResult records
// - hardened: gate hardened-profile obligations on publishable proof evidence
// - kani_gate: post-compile disclosure boundary (check and build) for packages that
//   declare a `kani` dependency (zero-authority ingestion lane, v5 §3.2: the run
//   proceeds, the operator is told)
// - creusot_gate: the same post-compile disclosure for packages that declare a
//   Creusot-family dependency (same v5 lane; the disclosure names the tippy reader for
//   migration — their `#[requires]`/`#[ensures]`/`#[logic]` specs are otherwise
//   silently unverified)
// - provenance: import binary-source-provenance and source-backpropagation-gate artifacts
// - standalone: source-level analysis renderer (no compiler invocation)
// - run: build the trustc command, spawn it, render the report, drive the rewrite loop
// - tests: cross-cutting unit tests for the submodules above
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub(crate) mod backend;
pub(crate) mod cargo_selection;
pub(crate) mod creusot_gate;
pub(crate) mod discovery;
pub(crate) mod gate_context;
pub(crate) mod hardened;
pub(crate) mod kani_gate;
pub(crate) mod probe;
pub(crate) mod process_environment;
pub(crate) mod project_policy;
pub(crate) mod provenance;
pub(crate) mod run;
pub(crate) mod standalone;
pub(crate) mod surface;
pub(crate) mod transport;

#[cfg(test)]
mod tests;

/// The Cargo-lane verb a post-compile disclosure is attached to. Kani and
/// Creusot are zero-authority ingestion lanes (two-language design v5, §3.2)
/// whether the crate was checked or built, so both verbs run the same
/// boundaries; only the verb named on stderr and the closing advice differ.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CompileVerb {
    Check,
    Build,
}

impl CompileVerb {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Check => "check",
            Self::Build => "build",
        }
    }
}

/// Whether a `targo trust check|build` run with these wrapper arguments was
/// help-only, so it compiled nothing a post-compile gate could inspect.
///
/// `run_subcommand_with_live_report` answers a help request with the usage text
/// and SUCCESS before it parses anything or starts a compiler. The post-compile
/// gates (temporal, Kani, Creusot) must see that no compile ran: otherwise they
/// resolve the selected packages with a `targo metadata` probe, and wherever
/// that probe cannot run — no Cargo project, no canonical compiler — a
/// successful `--help` becomes exit 2. This delegates to the very predicate the
/// help path uses, so the two cannot disagree about which runs were help-only.
pub(crate) fn run_was_help_only(args: &[String]) -> bool {
    crate::wrapper_help_requested(args)
}

/// The zero-authority ingestion-lane disclosures shared by `targo trust check`
/// and `targo trust build`, in order: Kani, then Creusot.
///
/// TRUST-26: until 2026-09-23 only the build arm ran these, so `check` passed a
/// crate carrying Kani harnesses or Creusot specs without saying they had been
/// ignored, and the two verbs disagreed about what a green run covered. Both
/// arms now call this one function, so they cannot drift apart again. A failed
/// run passes through untouched (see each gate).
///
/// `check --standalone` is skipped: it is a non-proof source audit that never
/// invokes a compiler (its report says `"proof_authority": "none"`), so there
/// is no verdict for the disclosure to qualify — and resolving the package
/// graph would demand the canonical compiler the standalone lane exists to do
/// without. A help-only run is skipped for the same reason: it compiled
/// nothing (see [`run_was_help_only`]).
pub(crate) fn disclose_zero_authority_ingestion_lanes(
    verb: CompileVerb,
    result: std::process::ExitCode,
    args: &[String],
) -> std::process::ExitCode {
    if run_was_help_only(args)
        || crate::cli::parse_subcommand_args(args).is_ok_and(|parsed| parsed.standalone)
    {
        return result;
    }
    let result = kani_gate::disclose_after_compile(verb, result, args);
    creusot_gate::disclose_after_compile(verb, result, args)
}

// Re-export the pipeline public surface used by main.rs, doctor.rs.
pub(crate) use backend::ignored_trustflags_notice;
// Re-exports used only by crate-level tests (`src/tests.rs`).
#[cfg(test)]
pub(crate) use backend::{lane_rustflags, level_to_num};
pub(crate) use cargo_selection::resolve_cargo_gate_package_roots;
#[cfg(test)]
pub(crate) use cargo_selection::{ResolvedCargoPackage, ResolvedCargoSelection};
#[cfg(test)]
pub(crate) use discovery::{NativeRustcDiscovery, is_cargo_program, select_native_rustc_discovery};
pub(crate) use discovery::{
    NativeRustcDiscoverySource, discover_native_rustc_checked, discover_native_trust_cargo_checked,
};
#[cfg(test)]
pub(crate) use gate_context::configured_cargo_build_target_with_targo;
pub(crate) use gate_context::{
    configured_cargo_build_target, post_build_cargo_context, selected_trustc_host_triple,
};
pub(crate) use probe::{apply_native_runtime_env, detect_native_rustc_capabilities};
pub(crate) use run::{
    CompilerRun, build_native_command_with_json_transport, has_output_path_flag, run_compiler,
    run_rewrite_loop, trust_verify_disable_diagnostic,
};
#[cfg(test)]
pub(crate) use run::{
    build_native_command, compiler_help_supports_option, find_trust_verify_disable_arg,
    find_trust_verify_disable_in_rustflags,
};
pub(crate) use standalone::run_standalone_check;
pub(crate) use surface::{
    LinkedTrustCargoSurfaceKind, LinkedTrustCargoSurfaceStatus, LinkedTrustSurfaceToolStatus,
    LinkedTrustSurfaceToolStatusKind, LinkedTrustToolchainStatus, LinkedTrustToolchainStatusKind,
    detect_linked_trust_cargo_surface, detect_linked_trust_toolchain,
};
#[cfg(test)]
pub(crate) use transport::parse_compiler_stderr;
