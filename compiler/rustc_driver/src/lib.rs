// This crate is a compatibility facade over `rustc_driver_impl`, allowing the
// implementation to compile in parallel with its consumers. Keep the public
// embedding surface explicit: canonical dispatch must not be the default
// route for arbitrary host executables, and remains visibly unchecked where
// the tiny compiler launcher needs it.

use std::process::ExitCode;

#[doc(no_inline)]
pub use rustc_driver_impl::{
    Callbacks, Compilation, DEFAULT_BUG_REPORT_URL, EXIT_FAILURE, EXIT_SUCCESS, HandledOptions,
    NoTrustEvidence, TimePassesCallbacks, USING_INTERNAL_FEATURES, args, catch_fatal_errors,
    catch_with_exit_code, describe_flag_categories, describe_lints, handle_help, handle_options,
    highlighter, init_logger, init_logger_with_additional_layer, init_rustc_env_logger,
    install_ctrlc_handler, install_ice_hook, install_ice_hook_with_default_compiler, pretty,
    run_compiler, run_compiler_with_expanded_args,
    run_compiler_with_expanded_args_and_no_trust_evidence, trust_display_binary, version,
    version_at_macro_invocation,
};

/// Run rustc as an embedded host tool without official Trust evidence
/// authority. The actual compiler executable uses the hidden canonical facade
/// dispatch below and is authenticated separately by Targo.
pub fn main() -> ExitCode {
    rustc_driver_impl::embedded_main()
}

/// Canonical compiler dispatch for the tiny `rustc-main` launcher.
///
/// This hidden symbol preserves the `librustc_driver` dynamic-link boundary;
/// it is routing, not proof authority. Targo must authenticate the exact
/// launcher and runtime image closure before accepting official evidence.
#[doc(hidden)]
pub fn canonical_main_unchecked() -> ExitCode {
    rustc_driver_impl::main()
}
