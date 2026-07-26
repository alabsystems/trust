// targo-trust pipeline: compiler invocation, rewrite loop, and standalone analysis.
//
// Submodule layout:
// - discovery: locate trustc next to targo-trust or in repo build dirs
// - probe: run a tiny crate through the discovered trustc to detect capabilities
// - surface: classify the linked Trust toolchain (targo, trustfmt, tippy, ...)
// - backend: assemble RUSTFLAGS and the trust-verify driver flags
// - trustflags: parse/validate TRUSTFLAGS, the sanctioned per-run -Ztrust-*
//   override channel merged after config-derived policy
// - transport: parse trustc's stderr JSON transport into VerificationResult records
// - hardened: gate hardened-profile obligations on publishable proof evidence
// - kani_gate: fail-closed build boundary for packages that declare a `kani` dependency
// - creusot_gate: fail-closed build boundary for packages that declare a Creusot-family
//   dependency (their `#[requires]`/`#[ensures]`/`#[logic]` specs would be silently unverified)
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
pub(crate) mod provenance;
pub(crate) mod run;
pub(crate) mod standalone;
pub(crate) mod surface;
pub(crate) mod transport;
pub(crate) mod trustflags;

#[cfg(test)]
mod tests;

// Re-export the pipeline public surface used by main.rs, doctor.rs,
// publication_v3_release_gate_cli.rs.
// Re-exports used only by crate-level tests (`src/tests.rs`).
#[cfg(test)]
pub(crate) use backend::{
    CargoRustflags, level_to_num, merged_cargo_rustflags_with_options, merged_rustflags,
    merged_rustflags_with_backend, merged_rustflags_with_json_transport,
    merged_rustflags_with_options,
};
pub(crate) use cargo_selection::resolve_cargo_gate_package_roots;
#[cfg(test)]
pub(crate) use cargo_selection::{ResolvedCargoPackage, ResolvedCargoSelection};
#[cfg(test)]
pub(crate) use discovery::{NativeRustcDiscovery, is_cargo_program, select_native_rustc_discovery};
pub(crate) use discovery::{
    NativeRustcDiscoverySource, discover_native_rustc_checked, discover_native_trust_cargo_checked,
};
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
