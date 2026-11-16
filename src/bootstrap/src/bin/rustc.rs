//! Shim which is passed to Cargo as "rustc" when running the bootstrap.
//!
//! This shim will take care of some various tasks that our build process
//! requires that Cargo can't quite do through normal configuration:
//!
//! 1. When compiling build scripts and build dependencies, we need a guaranteed
//!    full standard library available. The only compiler which actually has
//!    this is the snapshot, so we detect this situation and always compile with
//!    the snapshot compiler.
//! 2. We pass a bunch of `--cfg` and other flags based on what we're compiling
//!    (and this slightly differs based on a whether we're using a snapshot or
//!    not), so we do that all here.
//!
//! This may one day be replaced by RUSTFLAGS, but the dynamic nature of
//! switching compilers for the bootstrap and for build scripts will probably
//! never get replaced.

use std::env;
use std::ffi::{OsStr, OsString};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, Command};
use std::time::Instant;

// Trust: the shim helpers live in the `shim_utils` crate since the 1.101
// port (upstream moved them out of `#[path]` includes).
use shim_utils::{
    ArgFileCommand, BOOTSTRAP_FRONTEND_CEILING_ENV, DESCENDANT_HANDOFF_ENV, InheritedJobserver,
    RETIRED_TRUST_BOOTSTRAP_SHIM_TARGET_ONLY_ENV, activate_cargo_test_shim_environment,
    bootstrap_seed_frontend_threads, canonicalize_trust_verify_on, cargo_test_no_verify_requested,
    compile_uses_trust_bootstrap_no_verify, dylib_path, dylib_path_var, exe, expand_rustc_argfiles,
    finalize_trust_no_verify, finalize_trust_no_verify_snapshot, is_cargo_target_info_probe,
    maybe_dump, parse_rustc_stage, parse_rustc_verbose, parse_value_from_args,
    retired_trust_bootstrap_shim_target_only_refusal, strip_trust_no_verify,
    trust_bootstrap_no_verify_applies, trust_bootstrap_shim_marker_enabled,
    trust_bootstrap_verify_unit_argv_refusal, trust_bootstrap_verify_unit_requested,
};

#[path = "../utils/proc_macro_deps.rs"]
mod proc_macro_deps;

#[cfg(test)]
#[path = "rustc/tests.rs"]
mod tests;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TrustVerifyEnvAction {
    Preserve,
    Remove,
    SetOff,
}

/// Finalize the verifier control at the concrete compiler boundary.
///
/// Snapshot drivers are version-skewed by definition, so they must receive the
/// version-invariant environment transport rather than this tree's current
/// command-line spelling. Keeping this dispatch in one testable function avoids
/// a particularly dangerous branch inversion: the library opt-in can never use
/// a snapshot, so placing snapshot finalization inside that branch leaves every
/// actual stage0 compile on the incompatible current spelling.
fn finalize_trust_verify_control(
    args: &mut Vec<OsString>,
    bootstrap_verify_unit_applies: bool,
    targeted_rustc_is_snapshot: bool,
    targeted_rustc_supports_trust_no_verify: bool,
    bootstrap_no_verify_applies: bool,
) -> TrustVerifyEnvAction {
    if bootstrap_verify_unit_applies {
        // The lane's separate name, enforced: exactly one verifier control,
        // `-Ztrust-verify=on`, and no proof-session identity or policy control
        // beside it. Refused loudly rather than stripped — see
        // `trust_bootstrap_verify_unit_argv_refusal`.
        if let Some(message) = trust_bootstrap_verify_unit_argv_refusal(args) {
            panic!("{message}");
        }
        canonicalize_trust_verify_on(args);
        TrustVerifyEnvAction::Remove
    } else if targeted_rustc_is_snapshot {
        if finalize_trust_no_verify_snapshot(
            args,
            targeted_rustc_supports_trust_no_verify,
            bootstrap_no_verify_applies,
        ) {
            TrustVerifyEnvAction::SetOff
        } else {
            TrustVerifyEnvAction::Preserve
        }
    } else {
        finalize_trust_no_verify(
            args,
            targeted_rustc_supports_trust_no_verify,
            bootstrap_no_verify_applies,
        );
        TrustVerifyEnvAction::Preserve
    }
}

#[cfg(unix)]
fn cargo_fixture_termination_signal(
    is_fixture: bool,
    status: std::process::ExitStatus,
) -> Option<libc::c_int> {
    use std::os::unix::process::ExitStatusExt;
    is_fixture.then(|| status.signal()).flatten()
}

/// Trust: a dedicated Cargo fixture launcher must preserve the compiler's
/// terminating signal after its argument-file and failure-hook cleanup.
/// Ordinary bootstrap retains its diagnostic exit254 convention below.
#[cfg(unix)]
fn forward_cargo_fixture_signal(signal: libc::c_int) -> ! {
    // SAFETY: reset this process's disposition, unblock this signal in the
    // calling thread, then deliver it to that same thread. A process-directed
    // kill followed by _exit can race on macOS; raise is thread-directed.
    unsafe {
        let mut action: libc::sigaction = std::mem::zeroed();
        action.sa_sigaction = libc::SIG_DFL;
        if libc::sigemptyset(&mut action.sa_mask) != 0 {
            libc::_exit(0xfe);
        }
        if signal != libc::SIGKILL
            && signal != libc::SIGSTOP
            && libc::sigaction(signal, &action, std::ptr::null_mut()) != 0
        {
            libc::_exit(0xfe);
        }
        let mut mask: libc::sigset_t = std::mem::zeroed();
        if libc::sigemptyset(&mut mask) != 0
            || libc::sigaddset(&mut mask, signal) != 0
            || libc::pthread_sigmask(libc::SIG_UNBLOCK, &mask, std::ptr::null_mut()) != 0
        {
            libc::_exit(0xfe);
        }
        libc::raise(signal);
        libc::_exit(0xfe);
    }
}

fn main() {
    // Trust: import before sidecar/argument-file opens can reuse inherited fd
    // numbers. Retain this authority until the real compiler has been waited.
    // SAFETY: this is the shim's first operation, before opening other files.
    let inherited_jobserver = unsafe { InheritedJobserver::from_env() };
    let raw_args = env::args_os().skip(1).collect::<Vec<_>>();
    let jobserver = match inherited_jobserver {
        Ok(jobserver) => Some(jobserver),
        // Trust: build scripts such as libc call the wrapper's literal version
        // query with plain Command, which strips inherited scheduling fds.
        // This exact query does no compilation and needs no parallel budget.
        // Inspect argv only: an @file must still refuse before it is opened.
        Err(_) if is_literal_version_query(&raw_args) => None,
        Err(error) => panic!("cannot inherit bootstrap jobserver: {error}"),
    };

    // Refuse the retired marker on the AMBIENT environment, before the
    // Cargo-test sidecar can rewrite anything. A stale name that does nothing
    // is indistinguishable from one that worked.
    if let Some(message) = retired_trust_bootstrap_shim_target_only_refusal(
        env::var_os(RETIRED_TRUST_BOOTSTRAP_SHIM_TARGET_ONLY_ENV).as_deref(),
    ) {
        panic!("{message}");
    }

    // Targo marks descendants after config/env processing. Capture that final
    // boundary before the Cargo-test sidecar hides fixture-authored TRUST_*
    // controls from this shim. Verified Targo invocations must never be
    // rewritten into no-verify compiles by the ordinary-Cargo test harness.
    let authenticated_targo_frontend =
        env::var_os("TRUST_TARGO_FRONTEND").is_some_and(|value| value == "1");
    let mut isolated_shim_environment = activate_cargo_test_shim_environment()
        .unwrap_or_else(|err| panic!("failed to activate Cargo-test shim environment: {err}"));

    let had_inbound_argfile =
        raw_args.iter().any(|arg| arg.to_str().is_some_and(|arg| arg.starts_with('@')));
    let orig_args = expand_rustc_argfiles(&raw_args)
        .unwrap_or_else(|err| panic!("failed to load compiler argument file: {err}"));
    let mut args = orig_args.clone();

    let stage = parse_rustc_stage();
    let verbose = parse_rustc_verbose();

    // Detect whether or not we're a build script depending on whether --target
    // is passed (a bit janky...)
    let target = parse_value_from_args(&orig_args, "--target");
    let version = args.iter().find(|w| &**w == "-vV");

    // Use a different compiler for build scripts, since there may not yet be a
    // libstd for the real compiler to use. However, if Cargo is attempting to
    // determine the version of the compiler, the real compiler needs to be
    // used. Currently, these two states are differentiated based on whether
    // --target and -vV is/isn't passed.
    let is_build_script = target.is_none() && version.is_none();
    let (rustc, libdir) = if is_build_script {
        ("RUSTC_SNAPSHOT", "RUSTC_SNAPSHOT_LIBDIR")
    } else {
        ("RUSTC_REAL", "RUSTC_LIBDIR")
    };

    let sysroot = env::var_os("RUSTC_SYSROOT").expect("RUSTC_SYSROOT was not set");
    let on_fail = env::var_os("RUSTC_ON_FAIL").map(Command::new);

    let rustc_real = env::var_os(rustc).unwrap_or_else(|| panic!("{rustc:?} was not set"));
    let libdir = env::var_os(libdir).unwrap_or_else(|| panic!("{libdir:?} was not set"));
    let mut dylib_path = dylib_path();
    dylib_path.insert(0, PathBuf::from(&libdir));

    // If we're running Tippy, trust its frontend to set the lint driver
    // appropriately (and don't override it with rustc).
    // otherwise, substitute whatever cargo thinks rustc should be with RUSTC_REAL.
    // NOTE: this means we ignore RUSTC in the environment.
    // FIXME: We might want to consider removing RUSTC_REAL and setting RUSTC directly?
    // NOTE: we intentionally pass the name of the host, not the target.
    let host = env::var("CFG_COMPILER_BUILD_TRIPLE").unwrap();
    let is_clippy = is_lint_driver_arg(&args[0], &host);
    let rustc_driver = if is_clippy {
        if is_build_script {
            // Don't run clippy on build scripts (for one thing, we may not have libstd built with
            // the appropriate version yet, e.g. for stage 1 std).
            // Also remove the `clippy-driver` param in addition to the RUSTC param.
            args.drain(..2);
            rustc_real
        } else {
            args.remove(0)
        }
    } else {
        // Cargo doesn't respect RUSTC_WRAPPER for version information >:(
        // don't remove the first arg if we're being run as RUSTC instead of RUSTC_WRAPPER.
        // Cargo also sometimes doesn't pass the `.exe` suffix on Windows - add it manually.
        let current_exe = env::current_exe().expect("couldn't get path to rustc shim");
        let cargo_rustc = env::var_os("RUSTC");
        if should_strip_cargo_rustc_arg(
            &args[0],
            &host,
            &current_exe,
            cargo_rustc.as_ref(),
            Some(&rustc_real),
        ) {
            args.remove(0);
        }
        rustc_real
    };

    // Get the name of the crate we're compiling, if any.
    let crate_name = parse_value_from_args(&orig_args, "--crate-name");

    // When compiling `rustc_driver` remove `-C prefer-dynamic` to allow statically linking `std` into it
    if crate_name == Some("rustc_driver") {
        if let Some(pos) = args.iter().enumerate().position(|(i, a)| {
            a == "-C" && args.get(i + 1).map(|a| a == "prefer-dynamic").unwrap_or(false)
        }) {
            args.remove(pos);
            args.remove(pos);
        }
        if let Some(pos) = args.iter().position(|a| a == "-Cprefer-dynamic") {
            args.remove(pos);
        }
    }

    let rustc_driver_supports_trust_no_verify =
        rustc_driver_supports_trust_no_verify(&rustc_driver);
    let targeted_rustc_supports_trust_no_verify =
        targeted_rustc_supports_trust_no_verify(&rustc_driver);
    // Computed here, before `rustc_driver` moves into the command builder.
    let targeted_rustc_is_snapshot = targeted_rustc_is_stage0_snapshot(&rustc_driver);

    // Trust: enforce the driver-capability invariant before forwarding args — a
    // driver that cannot parse `-Ztrust-verify=off` must never receive it. See
    // `enforce_trust_no_verify_capability`.
    enforce_trust_no_verify_capability(&rustc_driver, &mut args);

    let bootstrap_shim_marker = trust_bootstrap_shim_marker_enabled(
        env::var_os("TRUST_BOOTSTRAP_SHIM_NO_VERIFY").as_deref(),
    );

    // Trust: the per-unit `library/` verification opt-in
    // (`TRUST_BOOTSTRAP_VERIFY_LIBRARY=core[,...]` on the `x.py` side). Bootstrap has
    // already refused this for compiler/bootstrap/tool invocations and scrubbed
    // the channel; this is the per-unit half, and it is the ONLY thing that can
    // turn verification on inside a bootstrap-driven compile.
    let driver_is_in_tree_staged =
        targeted_rustc_supports_trust_no_verify && !targeted_rustc_is_snapshot;
    // Trust: the probe half of the off-switch (`trust_bootstrap_off_switch_applies`)
    // is scoped to a driver this tree BUILT (a `stage1`+ directory), never a seed.
    let driver_is_built_stage = targeted_rustc_is_built_stage(&rustc_driver);
    let bootstrap_verify_unit_applies = trust_bootstrap_verify_unit_applies(
        target.is_some(),
        bootstrap_shim_marker,
        authenticated_targo_frontend,
        env::var_os(TRUST_BOOTSTRAP_SHIM_VERIFY_UNITS_ENV).as_deref(),
        driver_is_in_tree_staged,
        &orig_args,
        crate_name,
    );

    let bootstrap_no_verify_applies = !bootstrap_verify_unit_applies
        && trust_bootstrap_off_switch_applies(
            target.is_some(),
            cargo_test_no_verify_requested(bootstrap_shim_marker, authenticated_targo_frontend),
            targeted_rustc_supports_trust_no_verify,
            rustc_driver_supports_trust_no_verify,
            driver_is_built_stage,
            &orig_args,
            crate_name,
        );

    if bootstrap_verify_unit_applies && verbose > 0 {
        eprintln!(
            "[RUSTC-SHIM] trust: verifying library unit `{}` (-Ztrust-verify=on)",
            crate_name.unwrap_or("<unnamed>")
        );
    }

    let mut cmd = match env::var_os("RUSTC_WRAPPER_REAL") {
        Some(wrapper) if !wrapper.is_empty() => {
            let mut cmd = ArgFileCommand::new(wrapper);
            cmd.arg(rustc_driver);
            cmd.argfile_prefix_args(1);
            cmd
        }
        _ => ArgFileCommand::new(rustc_driver),
    };
    cmd.force_argfile(had_inbound_argfile);
    cmd.args(&args).env(dylib_path_var(), env::join_paths(&dylib_path).unwrap());

    if is_version_query(&args) {
        // Trust: run_version_query rewrites `trustc`->`rustc` in --version output.
        // Upstream migrated the driver invocation to ArgFileCommand; build it into a
        // plain Command (materializing any @argfile) before the version-query handler.
        let (mut cmd, arg_file) = cmd.build().unwrap();
        if let Some(environment) = &mut isolated_shim_environment {
            environment.restore_for_compiler_command(&mut cmd, bootstrap_no_verify_applies);
        }
        if let Some(jobserver) = &jobserver {
            jobserver.configure(&mut cmd);
        } else {
            // Trust: do not advertise descriptors that this metadata-only
            // child cannot inherit. No verification/authentication fields move.
            for variable in ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS", DESCENDANT_HANDOFF_ENV] {
                cmd.env_remove(variable);
            }
        }
        run_version_query(cmd, arg_file, isolated_shim_environment.is_some());
    }

    // Trust: only the exact final version-query branch may proceed after a
    // failed import. Environment isolation or wrapper normalization must never
    // turn that exception into an independently scheduled compile.
    let jobserver = jobserver.expect("unavailable jobserver outside a pure version query");

    if let Some(crate_name) = crate_name
        && let Some(target) = env::var_os("RUSTC_TIME")
        && (target == "all"
            || target.into_string().unwrap().split(',').any(|c| c.trim() == crate_name))
    {
        cmd.arg("-Ztime-passes");
    }

    // Print backtrace in case of ICE
    if env::var("RUSTC_BACKTRACE_ON_ICE").is_ok() && env::var("RUST_BACKTRACE").is_err() {
        cmd.env("RUST_BACKTRACE", "1");
    }

    if let Ok(lint_flags) = env::var("RUSTC_LINT_FLAGS") {
        cmd.args(lint_flags.split_whitespace());
    }
    // Cargo normally caps lints for dependencies, but workspace path
    // dependencies are not uniformly capped. Trust's first-party crates are
    // dependencies of rustc_mir_transform, not rustc compiler crates, and must
    // not inherit `-Wrustc::internal` merely because they share the umbrella
    // workspace. Bind compiler-only lints to the actual manifest subtree; the
    // Cargo "primary" marker is too broad for this workspace.
    if should_apply_compiler_lint_flags(
        env::var_os("CARGO_MANIFEST_DIR").as_deref(),
        env::var_os("RUSTC_COMPILER_ROOT").as_deref(),
    ) && let Ok(lint_flags) = env::var("RUSTC_COMPILER_LINT_FLAGS")
    {
        cmd.args(lint_flags.split_whitespace());
    }

    // Conditionally pass `-Zon-broken-pipe=kill` to underlying rustc. Not all binaries want
    // `-Zon-broken-pipe=kill`, which includes cargo itself.
    if env::var_os("FORCE_ON_BROKEN_PIPE_KILL").is_some() {
        cmd.arg("-Z").arg("on-broken-pipe=kill");
    }

    if target.is_some() {
        // The stage0 compiler has a special sysroot distinct from what we
        // actually downloaded, so we just always pass the `--sysroot` option,
        // unless one is already set.
        if !args.iter().any(|arg| arg == "--sysroot") {
            cmd.arg("--sysroot").arg(&sysroot);
        }

        let crate_type = parse_value_from_args(&orig_args, "--crate-type");
        // `-Ztls-model=initial-exec` must not be applied to proc-macros, see
        // issue https://github.com/rust-lang/rust/issues/100530
        if env::var("RUSTC_TLS_MODEL_INITIAL_EXEC").is_ok()
            && crate_type != Some("proc-macro")
            && proc_macro_deps::CRATES.binary_search(&crate_name.unwrap_or_default()).is_err()
        {
            cmd.arg("-Ztls-model=initial-exec");
        }
    } else {
        // Find any host flags that were passed by bootstrap.
        // The flags are stored in a RUSTC_HOST_FLAGS variable, separated by spaces.
        if let Ok(flags) = std::env::var("RUSTC_HOST_FLAGS") {
            cmd.args(flags.split(' '));
        }
    }

    // Here we pass additional paths that essentially act as a sysroot.
    // These are used to load rustc crates (e.g. `extern crate rustc_ast;`)
    // for rustc_private tools, so that we do not have to copy them into the
    // actual sysroot of the compiler that builds the tool.
    if let Ok(dirs) = env::var("RUSTC_ADDITIONAL_SYSROOT_PATHS") {
        for dir in dirs.split(",") {
            cmd.arg(format!("-L{dir}"));
        }
    }

    // Force all crates compiled by this compiler to (a) be unstable and (b)
    // allow the `rustc_private` feature to link to other unstable crates
    // also in the sysroot. We also do this for host crates, since those
    // may be proc macros, in which case we might ship them.
    if env::var_os("RUSTC_FORCE_UNSTABLE").is_some() {
        cmd.arg("-Z").arg("force-unstable-if-unmarked");
    }

    // allow-features is handled from within this rustc wrapper because of
    // issues with build scripts. Some packages use build scripts to
    // dynamically detect if certain nightly features are available.
    // There are different ways this causes problems:
    //
    // * rustix runs `rustc` on a small test program to see if the feature is
    //   available (and sets a `cfg` if it is). It does not honor
    //   CARGO_ENCODED_RUSTFLAGS.
    // * proc-macro2 detects if `rustc -vV` says "nighty" or "dev" and enables
    //   nightly features. It will scan CARGO_ENCODED_RUSTFLAGS for
    //   -Zallow-features. Unfortunately CARGO_ENCODED_RUSTFLAGS is not set
    //   for build-dependencies when --target is used.
    //
    // The issues above means we can't just use RUSTFLAGS, and we can't use
    // `cargo -Zallow-features=…`. Passing it through here ensures that it
    // always gets set. Unfortunately that also means we need to enable more
    // features than we really want (like those for proc-macro2), but there
    // isn't much of a way around it.
    //
    // I think it is unfortunate that build scripts are doing this at all,
    // since changes to nightly features can cause crates to break even if the
    // user didn't want or care about the use of the nightly features. I think
    // nightly features should be opt-in only. Unfortunately the dynamic
    // checks are now too wide spread that we just need to deal with it.
    //
    // If you want to try to remove this, I suggest working with the crate
    // authors to remove the dynamic checking. Another option is to pursue
    // https://github.com/rust-lang/cargo/issues/11244 and
    // https://github.com/rust-lang/cargo/issues/4423, which will likely be
    // very difficult, but could help expose -Zallow-features into build
    // scripts so they could try to honor them.
    if let Ok(allow_features) = env::var("RUSTC_ALLOW_FEATURES") {
        cmd.arg(format!("-Zallow-features={allow_features}"));
    }

    if env::var_os("RUSTC_BOLT_LINK_FLAGS").is_some()
        && let Some("rustc_driver") = crate_name
    {
        cmd.arg("-Clink-args=-Wl,-q");
    }

    // Keep the fixture/build environment byte-for-byte intact (notably
    // `TRUST_NO_VERIFY` itself), but enforce capability and canonical
    // last-value-wins semantics after every argv- and environment-derived
    // option has been assembled. A stage0 SNAPSHOT is the exception: its
    // vintage is the seed pin's, not this source tree's, so it is addressed
    // through the version-invariant env transport rather than an argv
    // spelling it may not parse — the pinned seed predates the
    // `-Ztrust-verify=off` rename, and handing it the new spelling aborted
    // every fresh-machine build at the first build script.
    //
    // A unit named by the `library/` opt-in takes the third branch: it is
    // never a snapshot compile (`trust_bootstrap_verify_unit_applies` requires
    // an in-tree stage>=1 driver) and it must end up with exactly one verifier
    // control, `-Ztrust-verify=on`, replacing the invocation-wide off-switch
    // that reached it through rustflags.
    let trust_verify_env_action = finalize_trust_verify_control(
        cmd.args_mut(),
        bootstrap_verify_unit_applies,
        targeted_rustc_is_snapshot,
        targeted_rustc_supports_trust_no_verify,
        bootstrap_no_verify_applies,
    );
    if trust_verify_env_action == TrustVerifyEnvAction::Remove {
        // THE ARGV ON-SWITCH IS NOT ENOUGH — the env transport outranks it.
        //
        // Adversarial review measured this as a blocking defect: the comment above
        // deliberately leaves the build environment byte-for-byte intact, INCLUDING
        // `TRUST_NO_VERIFY`. That is correct for the OFF direction and inverts meaning
        // here. `rustc_driver_impl/src/lib.rs:1453` reads `TRUST_NO_VERIFY` and applies
        // it AFTER every argv-derived option (its own comment at :1465 says the
        // inherited `TRUST_NO_VERIFY=1` "override below forces" the result), so a unit
        // named by the opt-in would get `-Ztrust-verify=on` on the command line and
        // then be silently switched back off.
        //
        // That failure mode is the worst available one: the experiment reports success
        // and verifies nothing. An opt-in that silently does not run is indistinguishable
        // from one that ran and found no obligations — which is the same
        // silence-reads-as-success shape that cost a3d 95 unverified rows. Scrub the
        // transport for exactly the authorized units, so argv is the only authority.
        cmd.env_remove("TRUST_NO_VERIFY");
    } else if trust_verify_env_action == TrustVerifyEnvAction::SetOff {
        cmd.env("TRUST_NO_VERIFY", "1");
    }

    // Seed Cargo does not run Targo's default frontend planner. Keep this
    // potential stable across changing admitted job shares; GNU tokens remain
    // the worker authority. Never alter a proof route, query or explicit argv.
    let unverified_seed_compile = targeted_rustc_is_snapshot
        && targeted_rustc_supports_trust_no_verify
        && bootstrap_no_verify_applies
        && !bootstrap_verify_unit_applies
        && !authenticated_targo_frontend
        && compile_uses_trust_bootstrap_no_verify(&orig_args);
    if let Some(threads) = bootstrap_seed_frontend_threads(
        cmd.args_mut(),
        unverified_seed_compile,
        jobserver.is_present(),
        env::var_os(BOOTSTRAP_FRONTEND_CEILING_ENV).as_deref(),
    )
    .unwrap_or_else(|message| panic!("{message}"))
    {
        cmd.arg(format!("-Zthreads={threads}"));
    }

    let is_test = args.iter().any(|a| a == "--test");
    if verbose > 2 {
        let rust_env_vars =
            env::vars().filter(|(k, _)| k.starts_with("RUST") || k.starts_with("CARGO"));
        let prefix = if is_test { "[RUSTC-SHIM] rustc --test" } else { "[RUSTC-SHIM] rustc" };
        let prefix = match crate_name {
            Some(crate_name) => format!("{prefix} {crate_name}"),
            None => prefix.to_string(),
        };
        for (i, (k, v)) in rust_env_vars.enumerate() {
            eprintln!("{prefix} env[{i}]: {k:?}={v:?}");
        }
        eprintln!("{} working directory: {}", prefix, env::current_dir().unwrap().display());
        eprintln!(
            "{} command: {:?}={:?} {:?}",
            prefix,
            dylib_path_var(),
            env::join_paths(&dylib_path).unwrap(),
            cmd,
        );
        eprintln!("{prefix} sysroot: {sysroot:?}");
        eprintln!("{prefix} libdir: {libdir:?}");
    }

    let (mut cmd, arg_file) = cmd.build().unwrap();
    maybe_dump(format!("stage{}-rustc", stage + 1), &cmd);
    if let Some(environment) = &mut isolated_shim_environment {
        environment.restore_for_compiler_command(&mut cmd, bootstrap_no_verify_applies);
    }
    jobserver.configure(&mut cmd);
    // Trust: retain the caller's scheduling policy. Promoting every compiler
    // worker can starve other admitted builds when the host's capacity is limited.

    let start = Instant::now();
    let (child, status) = {
        let errmsg = format!("\nFailed to run:\n{cmd:?}\n-------------");
        let mut child = cmd.spawn().expect(&errmsg);
        let status = child.wait().expect(&errmsg);
        (child, status)
    };

    drop(arg_file);

    if (env::var_os("RUSTC_PRINT_STEP_TIMINGS").is_some()
        || env::var_os("RUSTC_PRINT_STEP_RUSAGE").is_some())
        && let Some(crate_name) = crate_name
    {
        let dur = start.elapsed();
        // If the user requested resource usage data, then
        // include that in addition to the timing output.
        let rusage_data =
            env::var_os("RUSTC_PRINT_STEP_RUSAGE").and_then(|_| format_rusage_data(child));
        eprintln!(
            "[RUSTC-TIMING] {} test:{} {}.{:03}{}{}",
            crate_name,
            is_test,
            dur.as_secs(),
            dur.subsec_millis(),
            if rusage_data.is_some() { " " } else { "" },
            rusage_data.unwrap_or_default(),
        );
    }

    if status.success() {
        std::process::exit(0);
        // NOTE: everything below here is unreachable. do not put code that
        // should run on success, after this block.
    }
    if verbose > 0 {
        println!("\nDid not run successfully: {status}\n{cmd:?}\n-------------");
    }

    if let Some(mut on_fail) = on_fail {
        on_fail.status().expect("Could not run the on_fail command");
    }

    // Trust: only dedicated Cargo-test compilers expose the real signal to Cargo.
    propagate_cargo_test_signal(status, isolated_shim_environment.is_some());

    // Preserve the exit code. In case of signal, exit with 0xfe since it's
    // awkward to preserve this status in a cross-platform way.
    match status.code() {
        Some(i) => std::process::exit(i),
        None => {
            eprintln!("rustc exited with {status}");
            std::process::exit(0xfe);
        }
    }
}

fn should_apply_compiler_lint_flags(
    cargo_manifest_dir: Option<&OsStr>,
    compiler_root: Option<&OsStr>,
) -> bool {
    let (Some(cargo_manifest_dir), Some(compiler_root)) = (cargo_manifest_dir, compiler_root)
    else {
        return false;
    };
    Path::new(cargo_manifest_dir).starts_with(Path::new(compiler_root))
}

fn is_lint_driver_arg(arg: &OsString, host: &str) -> bool {
    let arg = arg.to_string_lossy();
    ["tippy-driver", "clippy-driver"].into_iter().any(|driver| arg.ends_with(&exe(driver, host)))
}

fn is_version_query(args: &[OsString]) -> bool {
    // Trust: an unrecognized byte argument is an extra argument, never erased
    // when deciding whether this invocation is only an identity query.
    let Some(args) = args.iter().map(|arg| arg.to_str()).collect::<Option<Vec<_>>>() else {
        return false;
    };
    matches!(
        args.as_slice(),
        ["-V"]
            | ["--version"]
            | ["-vV"]
            | ["-Vv"]
            | ["--version", "--verbose"]
            | ["--verbose", "--version"]
    )
}

// Trust: the early jobserver exception cannot open response files or otherwise
// interpret their contents. The ordinary wrapper-prefix rule is checked here
// and the exact version-only shape is checked again at the final dispatch.
fn is_literal_version_query(args: &[OsString]) -> bool {
    // Trust: reject response-file syntax before treating a compiler-looking
    // path as a wrapper prefix. Prefix recognition must never hide an @file.
    if args.iter().any(|arg| arg.as_encoded_bytes().starts_with(b"@")) {
        return false;
    }
    if is_version_query(args) {
        return true;
    }
    let Some((prefix, rest)) = args.split_first() else { return false };
    let Ok(host) = env::var("CFG_COMPILER_BUILD_TRIPLE") else { return false };
    let Ok(current_exe) = env::current_exe() else { return false };
    let cargo_rustc = env::var_os("RUSTC");
    let real = env::var_os("RUSTC_REAL");
    let snapshot = env::var_os("RUSTC_SNAPSHOT");
    if should_strip_cargo_rustc_arg(
        prefix,
        &host,
        &current_exe,
        cargo_rustc.as_ref(),
        real.as_ref(),
    ) || should_strip_cargo_rustc_arg(
        prefix,
        &host,
        &current_exe,
        cargo_rustc.as_ref(),
        snapshot.as_ref(),
    ) {
        return is_version_query(rest);
    }
    is_lint_driver_arg(prefix, &host)
        && rest.first().is_some_and(|arg| arg == "--rustc")
        && is_version_query(&rest[1..])
}

fn should_strip_cargo_rustc_arg(
    arg0: &OsString,
    host: &str,
    current_exe: &Path,
    cargo_rustc: Option<&OsString>,
    rustc_real: Option<&OsString>,
) -> bool {
    let arg0 = normalized_exe_arg(arg0, host);
    if arg0 == current_exe {
        return true;
    }

    if cargo_rustc.is_some_and(|rustc| arg0 == normalized_exe_arg(rustc, host)) {
        return true;
    }

    // Trust: also strip the arg when it is the *real* compiler the shim forwards
    // to (`RUSTC_REAL`/`RUSTC_SNAPSHOT`). Cargo's wrapper protocol inserts the
    // real rustc as arg0 (`$RUSTC_WRAPPER $RUSTC …`); with stock cargo that is
    // the shim itself (caught above), but Trust's `targo` resolves and passes
    // the concrete stage0 compiler path when probing rustc capabilities.
    if rustc_real.is_some_and(|real| arg0 == normalized_exe_arg(real, host)) {
        return true;
    }

    // Trust: general wrapper-mode detection — strip arg0 when it is a compiler
    // binary by name (`rustc`/`trustc`, with the host exe suffix). In cargo's
    // RUSTC_WRAPPER protocol arg0 is always the compiler; in plain-RUSTC mode it
    // is a real first arg (`-`, a `.rs` path, or a flag) that never has the file
    // name `rustc`/`trustc`. Matching one specific path (shim/$RUSTC/RUSTC_REAL)
    // is insufficient when `targo` probes with its sibling stage0 `trustc` while
    // the step's RUSTC_REAL points at a different stage — the exact case that
    // arises bootstrapping from a self-hosted Trust seed. This keeps the same
    // wrapper-vs-rustc distinction the exact-match checks encode, generalized to
    // any compiler path.
    if let Some(name) = arg0.file_name().and_then(|n| n.to_str()) {
        if name == exe("rustc", host).as_str() || name == exe("trustc", host).as_str() {
            return true;
        }
    }
    false
}

/// Bootstrap -> shim IPC for the per-unit `library/` verification opt-in. Kept
/// in sync with `core::builder::cargo::TRUST_BOOTSTRAP_SHIM_VERIFY_UNITS_ENV`;
/// the shims cannot depend on the bootstrap library.
const TRUST_BOOTSTRAP_SHIM_VERIFY_UNITS_ENV: &str = "TRUST_BOOTSTRAP_SHIM_VERIFY_UNITS";

/// Trust: whether bootstrap's verification off-switch reaches this invocation:
/// every real compile [`trust_bootstrap_no_verify_applies`] admits, and ALSO a
/// targeted target-information probe ([`is_cargo_target_info_probe`]) on a
/// driver this tree built.
///
/// WHY THE PROBE. Bootstrap puts `-Ztrust-verify=off` in the rustflags of every
/// target unit (`core/builder/cargo.rs`), and upstream Cargo passes rustflags to
/// its probe verbatim. Targo does not: it strips every `-Ztrust_*` token from
/// the probe (`target_info_probe_flags`, `strip_trust_verify_probe_flags` in the
/// seed's Targo, so a Targo proof session's identity never reaches a `--print`
/// early exit), the off-switch included. With Targo as bootstrap's Cargo the
/// probe therefore runs at a stage>=1 `trustc`'s batteries-on default,
/// verification ON, while every unit it describes compiles with it off. Two
/// consequences, both measured 2026-10-13 on a stage 1 whose `build.cargo` is
/// the atpkg toolchain's Targo:
///
/// * since T6 (`8e7067d334`: a proof session refuses the MIR-pipeline options)
///   the stage-1 std build aborts before compiling anything: the probe carries
///   std's `-Zinline-mir` and answers "a Trust proof session runs the -O0 MIR
///   pipeline for every unit; -Zinline-mir would make the verified MIR, and so
///   the verdicts, depend on the caller's MIR options. Remove it." (A Targo cut
///   from this tree since DECISION_QUEUE TARGO-PROBE-MIR-1 drops those options
///   from its probe; bootstrap's Cargo is the seed's Targo, which does not.);
/// * `--print=cfg` reports `trust_verify` for units that compile without it
///   (with every Targo: it strips the switch from every probe, on purpose for a
///   branded run, DECISION_QUEUE T14-TIPPY-1).
///
/// Giving the probe the off-switch the units already carry restores what
/// upstream Cargo delivered. It turns no verification on and the probe
/// compiles nothing ([`is_cargo_target_info_probe`] admits only Cargo's probe
/// shape, read as rustc's getopts reads it, and every print kind in it stops
/// compilation: a `--print=native-static-libs` compile, or `-gL --print=cfg`,
/// whose `-L` takes the print as its path, is not a probe), so it can neither
/// produce nor launder evidence; the T6 refusal stays in force for every
/// compile that verifies.
///
/// Scope: TARGETED probes on a driver under a `stage1`, `stage2` or `stage3`
/// directory ([`targeted_rustc_is_built_stage`]). That is every Cargo run whose
/// build compiler is stage 1 or later, not only the stage-1 std build: the
/// stage-2 compiler build, tools built by a stage-1 compiler, `x.py test
/// library/*` at stage >= 1 and Cargo-testsuite fixtures under the Cargo-test
/// shim with `--target` get the switch on their probe too. Each of those units
/// already compiles with it (bootstrap's rustflags at a build-compiler stage
/// >= 1, or the shim's compile clause), and no manifest, Cargo config or build
/// script in the tree reads `cfg(trust_verify)` or `CARGO_CFG_TRUST_VERIFY`.
/// Only a seed driver's probe (bootstrap's `stage0`, or an installed `trustc`
/// named as `build.rustc`) keeps today's answer, and so does a host probe (no
/// `--target`), which bootstrap's std rustflags, and so `-Zinline-mir`, never
/// reach. The directory test is a name test: a seed that lives under another
/// checkout's `stage1`/`stage2`/`stage3` directory counts as built, which is
/// harmless for the same reason (the shim's compile clause already gives that
/// seed's units the switch).
fn trust_bootstrap_off_switch_applies(
    has_target: bool,
    requested: bool,
    targeted_rustc_supports_no_verify: bool,
    rustc_driver_supports_no_verify: bool,
    driver_is_built_stage: bool,
    args: &[OsString],
    crate_name: Option<&str>,
) -> bool {
    trust_bootstrap_no_verify_applies(
        has_target,
        requested,
        targeted_rustc_supports_no_verify,
        rustc_driver_supports_no_verify,
        args,
        crate_name,
    ) || (requested && has_target && driver_is_built_stage && is_cargo_target_info_probe(args))
}

/// Whether THIS unit is one the `library/` opt-in named, i.e. the one case where
/// a bootstrap-driven compile runs with the verifier ON.
///
/// Every conjunct is a refusal that matters, and the whole predicate is
/// fail-closed — an unset or unparsable channel yields `false`, which is
/// today's behaviour exactly:
///
/// * `shim_marker` — we are inside a bootstrap cargo invocation. Outside one,
///   an ambient `TRUST_BOOTSTRAP_SHIM_VERIFY_UNITS` means nothing.
/// * `!authenticated_targo_frontend` — a verified Targo frontend has already
///   committed to its own argv at the driver boundary; bootstrap's shim never
///   rewrites it, in either direction.
/// * `has_target` — target units only. Build scripts and proc macros are host
///   units, run on the build compiler, and stay on the no-verify lane.
/// * `driver_is_in_tree_staged` — `targeted_rustc_supports_trust_no_verify &&
///   !targeted_rustc_is_stage0_snapshot`, i.e. the driver is an in-tree stage>=1
///   `trustc`. A stage0 SEED must never be asked to verify: its vintage is the
///   pin's, not this tree's, so a proof it produced would be evidence about an
///   artifact nobody in this tree built. This is also what keeps the lane from
///   becoming a self-proof by another route.
/// * `compile_uses_trust_bootstrap_no_verify` — a real compilation, not a
///   `-vV`/`--print` query.
/// * `trust_bootstrap_verify_unit_requested` — and finally the unit's own
///   `--crate-name` must be in the authorized list, which is what keeps std's
///   third-party dependency graph (compiled by the same cargo invocation) off.
fn trust_bootstrap_verify_unit_applies(
    has_target: bool,
    shim_marker: bool,
    authenticated_targo_frontend: bool,
    units: Option<&OsStr>,
    driver_is_in_tree_staged: bool,
    args: &[OsString],
    crate_name: Option<&str>,
) -> bool {
    shim_marker
        && !authenticated_targo_frontend
        && has_target
        && driver_is_in_tree_staged
        && compile_uses_trust_bootstrap_no_verify(args)
        && trust_bootstrap_verify_unit_requested(units, crate_name)
}

fn rustc_driver_supports_trust_no_verify(rustc_driver: &OsString) -> bool {
    // Trust: host units use RUSTC_SNAPSHOT, normally stage0/bin/rustc. The
    // compatibility name supports the off-switch when its snapshot actually
    // carries a Trust payload. Vintage-specific spelling is selected by
    // finalize_trust_verify_control. A directory named stage0 alone does not
    // establish that a rustc-named snapshot is a Trust seed.

    // Trust: an admitted Trust snapshot grants the environment transport, not
    // this tree's argv spelling; snapshot finalization strips that spelling.
    Path::new(rustc_driver).file_stem().and_then(|stem| stem.to_str()) == Some("trustc")
        || targeted_rustc_is_built_stage(rustc_driver)
        || snapshot_is_trust_seed(rustc_driver)
}

/// A Trust seed snapshot, as opposed to a bring-your-own stock stage0
/// installed into the same `stage0/bin` shape: bootstrap's snapshot path
/// is the seed's `rustc` launcher, whose stem carries no Trust identity,
/// but the seed payload ships `trustc` beside it and a stock snapshot
/// does not. Without this, untargeted host units (build scripts, proc
/// macros, build dependencies) compiled by the seed got no off-switch
/// and verified against the seed's strict default (measured: memchr
/// and find-msvc-tools build units failing strict verification during
/// `x.py build --stage 1` against the 0.11.0 seed).
fn snapshot_is_trust_seed(rustc_driver: &OsString) -> bool {
    if !targeted_rustc_is_stage0_snapshot(rustc_driver) {
        return false;
    }
    let path = Path::new(rustc_driver);
    path.with_file_name("trustc").exists() || path.with_file_name("trustc.exe").exists()
}

// Trust: a driver this source tree BUILT — one under a `stage1`, `stage2` or
// `stage3` directory. Narrower than `targeted_rustc_supports_trust_no_verify`
// (which also admits a `trustc`-named seed and a `stage0` snapshot): the
// target-information probe's off-switch (`trust_bootstrap_off_switch_applies`)
// is scoped to it so that a seed driver's probe keeps today's answer. A name
// test, like its siblings: a seed under another checkout's `stage1` directory
// passes it (see `trust_bootstrap_off_switch_applies` for why that is harmless).
// The driver-capability predicates also admit snapshots, but this probe-only
// guard stays narrower: changing a host compile must not widen probe scope.
fn targeted_rustc_is_built_stage(rustc_driver: &OsString) -> bool {
    Path::new(rustc_driver).components().any(|component| {
        matches!(component.as_os_str().to_str(), Some("stage1" | "stage2" | "stage3"))
    })
}

// Trust: a SNAPSHOT driver is anything under a `stage0` directory — that
// directory is definitionally the SEED, whose vintage is the seed pin's, not
// this source tree's. The seed ships its driver under BOTH names (`rustc` is
// a launcher for its `trustc`), so the stem carries no vintage information
// here: an earlier stem-based exemption classified the seed's `trustc` as
// in-tree and handed it the current argv spelling, which the pre-rename seed
// rejected at the first build script. In-tree drivers live in stage1+ (or
// outside the build dir entirely) and their vintage matches this shim's own
// source by construction; see `finalize_trust_no_verify_snapshot` for why a
// snapshot gets the env transport instead of an argv flag.
fn targeted_rustc_is_stage0_snapshot(rustc_driver: &OsString) -> bool {
    Path::new(rustc_driver)
        .components()
        .any(|component| component.as_os_str().to_str() == Some("stage0"))
}

// Trust: targeted compiles may run on the stage0 snapshot (e.g. stage0 -> stage1
// compiler artifacts). A snapshot with a Trust companion payload, or a
// `trustc`-named driver, understands the off-switch CONCEPT; whether it parses
// the current argv SPELLING is a vintage question — see
// `targeted_rustc_is_stage0_snapshot`. A stock-shaped snapshot is unsupported
// in both the host and targeted arms.
fn targeted_rustc_supports_trust_no_verify(rustc_driver: &OsString) -> bool {
    rustc_driver_supports_trust_no_verify(rustc_driver)
}

// Trust: the shim is the only bootstrap component that knows the concrete driver
// it is about to invoke, so it is the single authority on whether that driver may
// receive `-Ztrust-verify=off` (a Trust-only flag). Enforce the invariant that a
// non-Trust-native driver never sees it.
//
// Reachable leak this closes: with a bring-your-own stage0 whose `build.rustc` is
// a stock upstream rustc (the `bootstrap/trust-stage0` workflow), `build_compiler_stage`
// is >= 1, so `builder::cargo` injects `-Ztrust-verify=off` driver-blind via
// `CARGO_TARGET_<triple>_RUSTFLAGS`; cargo delivers it to us as argv on `--target`
// compiles, where `RUSTC_REAL` is that stock rustc. It rejects the unknown option
// and aborts. The Jun-2026 gate only stopped the shim's *own* injection (the
// `cmd.arg` in `main`), leaving cargo's copy in place — this strips it. A
// Trust-native driver keeps the flag (and the canonical add still happens in
// `main` via `trust_bootstrap_no_verify_applies`).
fn enforce_trust_no_verify_capability(rustc_driver: &OsString, args: &mut Vec<OsString>) {
    if !targeted_rustc_supports_trust_no_verify(rustc_driver) {
        strip_trust_no_verify(args);
    }
}

fn normalized_exe_arg(arg: &OsString, host: &str) -> PathBuf {
    PathBuf::from(exe(arg.to_str().expect("only utf8 paths are supported"), host))
}

// Trust: normal bootstrap retains its historical 0xfe signal encoding. A
// validated Cargo-test sidecar makes this a fixture compiler, whose caller
// observes the compiler's Unix signal (not an ordinary exit code). Run only
// after reaping the compiler and dropping any materialized response file.
fn propagate_cargo_test_signal(status: std::process::ExitStatus, cargo_test_fixture: bool) {
    #[cfg(unix)]
    if let Some(signal) = cargo_fixture_termination_signal(cargo_test_fixture, status) {
        if let Err(error) = io::stdout().flush().and_then(|()| io::stderr().flush()) {
            eprintln!("rustc shim: failed to flush output before compiler {status}: {error}");
            std::process::exit(0xfe);
        }
        forward_cargo_fixture_signal(signal);
    }
    #[cfg(not(unix))]
    let _ = (status, cargo_test_fixture);
}

fn run_version_query(
    mut cmd: Command,
    arg_file: Option<tempfile::NamedTempFile>,
    cargo_test_fixture: bool,
) -> ! {
    let output =
        cmd.output().unwrap_or_else(|_| panic!("\nFailed to run:\n{cmd:?}\n-------------"));
    // `process::exit` below skips destructors, so close any forced response
    // file explicitly after the compiler has consumed it.
    drop(arg_file);
    let mut stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    stdout = stdout.replace("binary: trustc\n", "binary: rustc\n");
    if let Some(rest) = stdout.strip_prefix("trustc ") {
        stdout = format!("rustc {rest}");
    }
    io::stdout().write_all(stdout.as_bytes()).expect("failed to write rustc version stdout");
    io::stderr().write_all(&output.stderr).expect("failed to write rustc version stderr");
    propagate_cargo_test_signal(output.status, cargo_test_fixture);
    match output.status.code() {
        Some(code) => std::process::exit(code),
        None => std::process::exit(0xfe),
    }
}

#[cfg(all(not(unix), not(windows)))]
// In the future we can add this for more platforms
fn format_rusage_data(_child: Child) -> Option<String> {
    None
}

#[cfg(windows)]
fn format_rusage_data(child: Child) -> Option<String> {
    use std::os::windows::io::AsRawHandle;

    use windows::Win32::Foundation::HANDLE;
    use windows::Win32::System::ProcessStatus::{K32GetProcessMemoryInfo, PROCESS_MEMORY_COUNTERS};
    use windows::Win32::System::Threading::GetProcessTimes;
    use windows::Win32::System::Time::FileTimeToSystemTime;

    let handle = HANDLE(child.as_raw_handle());

    let mut user_filetime = Default::default();
    let mut user_time = Default::default();
    let mut kernel_filetime = Default::default();
    let mut kernel_time = Default::default();
    let mut memory_counters = PROCESS_MEMORY_COUNTERS::default();
    let memory_counters_size = size_of_val(&memory_counters);

    unsafe {
        GetProcessTimes(
            handle,
            &mut Default::default(),
            &mut Default::default(),
            &mut kernel_filetime,
            &mut user_filetime,
        )
    }
    .ok()?;
    unsafe { FileTimeToSystemTime(&user_filetime, &mut user_time) }.ok()?;
    unsafe { FileTimeToSystemTime(&kernel_filetime, &mut kernel_time) }.ok()?;

    // Unlike on Linux with RUSAGE_CHILDREN, this will only return memory information for the process
    // with the given handle and none of that process's children.
    unsafe { K32GetProcessMemoryInfo(handle, &mut memory_counters, memory_counters_size as u32) }
        .ok()
        .ok()?;

    // Guide on interpreting these numbers:
    // https://docs.microsoft.com/en-us/windows/win32/psapi/process-memory-usage-information
    let peak_working_set = memory_counters.PeakWorkingSetSize / 1024;
    let peak_page_file = memory_counters.PeakPagefileUsage / 1024;
    let peak_paged_pool = memory_counters.QuotaPeakPagedPoolUsage / 1024;
    let peak_nonpaged_pool = memory_counters.QuotaPeakNonPagedPoolUsage / 1024;
    Some(format!(
        "user: {USER_SEC}.{USER_USEC:03} \
         sys: {SYS_SEC}.{SYS_USEC:03} \
         peak working set (kb): {PEAK_WORKING_SET} \
         peak page file usage (kb): {PEAK_PAGE_FILE} \
         peak paged pool usage (kb): {PEAK_PAGED_POOL} \
         peak non-paged pool usage (kb): {PEAK_NONPAGED_POOL} \
         page faults: {PAGE_FAULTS}",
        USER_SEC = user_time.wSecond + (user_time.wMinute * 60),
        USER_USEC = user_time.wMilliseconds,
        SYS_SEC = kernel_time.wSecond + (kernel_time.wMinute * 60),
        SYS_USEC = kernel_time.wMilliseconds,
        PEAK_WORKING_SET = peak_working_set,
        PEAK_PAGE_FILE = peak_page_file,
        PEAK_PAGED_POOL = peak_paged_pool,
        PEAK_NONPAGED_POOL = peak_nonpaged_pool,
        PAGE_FAULTS = memory_counters.PageFaultCount,
    ))
}

#[cfg(unix)]
/// Tries to build a string with human readable data for several of the rusage
/// fields. Note that we are focusing mainly on data that we believe to be
/// supplied on Linux (the `rusage` struct has other fields in it but they are
/// currently unsupported by Linux).
fn format_rusage_data(_child: Child) -> Option<String> {
    let rusage: libc::rusage = unsafe {
        let mut recv = std::mem::zeroed();
        // -1 is RUSAGE_CHILDREN, which means to get the rusage for all children
        // (and grandchildren, etc) processes that have respectively terminated
        // and been waited for.
        let retval = libc::getrusage(-1, &mut recv);
        if retval != 0 {
            return None;
        }
        recv
    };
    // Mac OS X reports the maxrss in bytes, not kb.
    let divisor = if env::consts::OS == "macos" { 1024 } else { 1 };
    let maxrss = (rusage.ru_maxrss + (divisor - 1)) / divisor;

    let mut init_str = format!(
        "user: {USER_SEC}.{USER_USEC:03} \
         sys: {SYS_SEC}.{SYS_USEC:03} \
         max rss (kb): {MAXRSS}",
        USER_SEC = rusage.ru_utime.tv_sec,
        USER_USEC = rusage.ru_utime.tv_usec,
        SYS_SEC = rusage.ru_stime.tv_sec,
        SYS_USEC = rusage.ru_stime.tv_usec,
        MAXRSS = maxrss
    );

    // The remaining rusage stats vary in platform support. So we treat
    // uniformly zero values in each category as "not worth printing", since it
    // either means no events of that type occurred, or that the platform
    // does not support it.

    let minflt = rusage.ru_minflt;
    let majflt = rusage.ru_majflt;
    if minflt != 0 || majflt != 0 {
        init_str.push_str(&format!(" page reclaims: {minflt} page faults: {majflt}"));
    }

    let inblock = rusage.ru_inblock;
    let oublock = rusage.ru_oublock;
    if inblock != 0 || oublock != 0 {
        init_str.push_str(&format!(" fs block inputs: {inblock} fs block outputs: {oublock}"));
    }

    let nvcsw = rusage.ru_nvcsw;
    let nivcsw = rusage.ru_nivcsw;
    if nvcsw != 0 || nivcsw != 0 {
        init_str.push_str(&format!(
            " voluntary ctxt switches: {nvcsw} involuntary ctxt switches: {nivcsw}"
        ));
    }

    Some(init_str)
}
