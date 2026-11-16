//@ run-pass
//@ revisions: pinned session_dep vanilla
//@ ignore-cross-compile
//@ ignore-remote

//! Trust (T4.3, DECISION_QUEUE FRONTEND-THREADS-1): a proof session runs ONE
//! front-end thread with synchronization off, whatever `-Zthreads` asked, and
//! the pin is applied where it must be: on `run_compiler`'s final options,
//! BEFORE the process-global parallel mode is set and the thread pool is built.
//!
//! This runs the canonical route itself (the one `rustc_driver::main` takes; the
//! embedded routes deauthorize verification, so no proof session exists there to
//! pin) with `threads = Some(4)` written on the `Config` after parsing — the way a
//! driver's `Callbacks::config` or any direct caller sets it, so
//! `build_session_options` never sees the request — and reads inside the compiler:
//!
//! * `Session::threads()`: `None` in a proof session. Without the pin call it
//!   reads `Some(4)` (and `build_session` refuses the session as a compiler bug).
//! * `is_dyn_thread_safe()`: `false` in a proof session. The parallel mode and the
//!   pool are set from the options once, before the session exists, so a pin moved
//!   below `set_dyn_thread_safe_mode` or `run_in_thread_pool_with_globals` leaves
//!   the session reading `None` over a 4-thread pool with synchronization on, and
//!   this reads `true`.
//!
//! One revision per process, because the parallel mode is process-global and set
//! once: `pinned` (the batteries-on default, a verifying session), `session_dep`
//! (verification off, carrying `-Ztrust-verify-session`: a dependency built for a
//! verified dependent) and `vanilla` (verification off, no session), the control,
//! which keeps the request exactly.

#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_session;
extern crate rustc_span;

use rustc_interface::interface;
use rustc_session::config::{Input, Options, TrustVerify};
use rustc_span::FileName;

fn main() {
    let mut opts = Options::default();
    opts.unstable_opts.threads = Some(4);
    #[cfg(pinned)]
    assert_eq!(opts.unstable_opts.trust_verify, TrustVerify::On, "the default verifies");
    #[cfg(session_dep)]
    {
        opts.unstable_opts.trust_verify = TrustVerify::Off;
        opts.unstable_opts.trust_verify_session = Some("t4-3".to_string());
    }
    #[cfg(vanilla)]
    {
        opts.unstable_opts.trust_verify = TrustVerify::Off;
    }

    let input = Input::Str { name: FileName::anon_source_code(""), input: String::new() };
    let config = interface::Config {
        opts,
        crate_cfg: Default::default(),
        crate_check_cfg: Default::default(),
        input,
        output_file: None,
        output_dir: None,
        ice_file: None,
        file_loader: None,
        lint_caps: Default::default(),
        psess_created: None,
        track_state: None,
        register_lints: None,
        override_queries: None,
        extra_symbols: Vec::new(),
        make_codegen_backend: None,
        using_internal_features: &rustc_driver::USING_INTERNAL_FEATURES,
    };

    let (verifying, threads, dyn_thread_safe) =
        interface::run_compiler_with_canonical_trustc_policy_unchecked(config, |compiler| {
            (
                compiler.sess.trust_verification_enabled(),
                compiler.sess.threads(),
                rustc_data_structures::sync::is_dyn_thread_safe(),
            )
        });

    #[cfg(pinned)]
    {
        assert!(verifying, "the canonical route keeps the default verifying session");
        assert_eq!(threads, None, "a verifying session's Session::threads is pinned");
        assert!(!dyn_thread_safe, "the parallel mode was set before the pin");
    }
    #[cfg(session_dep)]
    {
        assert!(!verifying);
        assert_eq!(threads, None, "a session dependency's Session::threads is pinned");
        assert!(!dyn_thread_safe, "the parallel mode was set before the pin");
    }
    #[cfg(vanilla)]
    {
        assert!(!verifying);
        assert_eq!(threads, Some(4), "the vanilla lane keeps the request");
        assert!(dyn_thread_safe, "the vanilla lane runs the parallel frontend it asked for");
    }
}
