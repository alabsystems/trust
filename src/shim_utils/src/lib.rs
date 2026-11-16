//! Utility code in this crate can be used by bootstrap's `rustc` and `rustdoc`
//! shims, while also being shared by bootstrap and other bootstrap tools.
//!
//! Try to keep this crate small, to avoid bloating bootstrap build times.
//!
//! Ideally, any code in this crate should be used by at least one of the shims,
//! and at least one other crate (possibly the other shim).

mod arg_file_command;
mod bootstrap_frontend;
pub use bootstrap_frontend::{
    BOOTSTRAP_FRONTEND_CEILING_ENV, bootstrap_seed_frontend_ceiling,
    bootstrap_seed_frontend_threads,
};
// Trust: blessed env_mutation (2026-07-20) — the shared shim helpers mutate
// process-global env under local save/restore, an RAII guard, or
// single-threaded harness/CLI context; unknown_lints keeps the
// stock-toolchain build green (the lint name is Trust-only). dead_code: the
// module serves both shims and bootstrap, so not every item is used by each.
#[allow(dead_code)]
#[allow(unknown_lints)]
#[allow(env_mutation)]
mod shared_helpers;

// Trust: share the same minimal owned transport with native Targo.
pub use jobserver_utils::{DESCENDANT_HANDOFF_ENV, InheritedJobserver};

pub use crate::arg_file_command::ArgFileCommand;
pub use crate::shared_helpers::{
    IsolatedShimEnvironment, RETIRED_TRUST_BOOTSTRAP_SHIM_TARGET_ONLY_ENV,
    TRUST_CARGO_TEST_SHIM_CONFIG, TRUST_CARGO_TEST_SHIM_VERSION,
    activate_cargo_test_shim_environment, canonicalize_trust_no_verify,
    canonicalize_trust_verify_on, cargo_test_no_verify_requested, collect_args,
    compile_uses_trust_bootstrap_no_verify, dylib_path, dylib_path_var, exe, expand_rustc_argfiles,
    finalize_trust_no_verify, finalize_trust_no_verify_snapshot, is_cargo_target_info_probe,
    maybe_dump, parse_rustc_stage, parse_rustc_verbose, parse_value_from_args,
    retired_trust_bootstrap_shim_target_only_refusal, strip_trust_no_verify,
    trust_bootstrap_no_verify_applies, trust_bootstrap_shim_marker_enabled,
    trust_bootstrap_verify_unit_argv_refusal, trust_bootstrap_verify_unit_requested,
};
