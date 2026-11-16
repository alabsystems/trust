//! Shim which is passed to Cargo as "rustdoc" when running the bootstrap.
//!
//! See comments in `src/bootstrap/rustc.rs` for more information.

use std::env;
use std::path::{Path, PathBuf};

// Trust: the shim helpers live in the `shim_utils` crate since the 1.101
// port (upstream moved them out of `#[path]` includes).
use shim_utils::{
    ArgFileCommand, InheritedJobserver, RETIRED_TRUST_BOOTSTRAP_SHIM_TARGET_ONLY_ENV,
    activate_cargo_test_shim_environment, cargo_test_no_verify_requested, dylib_path,
    dylib_path_var, expand_rustc_argfiles, finalize_trust_no_verify,
    finalize_trust_no_verify_snapshot, maybe_dump, parse_rustc_stage, parse_rustc_verbose,
    parse_value_from_args, retired_trust_bootstrap_shim_target_only_refusal,
    trust_bootstrap_no_verify_applies, trust_bootstrap_shim_marker_enabled,
};

#[cfg(test)]
#[path = "rustdoc/tests.rs"]
mod tests;

/// Trust (CUSTODY-PROTOCOL1-LAUNCH-1): the markers that make the real
/// rustdoc's custody strict (`strict_context` in
/// compiler/rustc_data_structures/src/jobserver/early.rs), less the
/// descendant handoff, which is a GNU advertisement. A marker missing here
/// only withholds a loan, and the real rustdoc then refuses.
const STRICT_CUSTODY_MARKERS: [&str; 6] = [
    "BUILD_SLOT_CPU_PROTOCOL",
    "TRUST_CPU_HANDOFF",
    "TRUST_CPU_IMPLICIT_FD",
    "ATERM_SDK_LEASE_V3",
    "ATERM_WORKLOAD_CPU_FDS_V1",
    "ATERM_WORKLOAD_HOST_STORE_FD_V1",
];

/// Trust (CUSTODY-PROTOCOL1-LAUNCH-1): each variable whose presence, whatever
/// its value, is a GNU scheduler advertisement to a Trust compiler.
const GNU_ADVERTISEMENTS: [&str; 4] =
    ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS", "CARGO_JOBSERVER_HANDOFF"];

/// Trust (CUSTODY-PROTOCOL1-LAUNCH-1): what this shim hands the real rustdoc.
#[derive(Debug, PartialEq, Eq)]
enum Lending {
    /// Run it as configured: it inherited a scheduler, or was handed an
    /// advertisement it judges itself, or is not owed one.
    Forward,
    /// Lend it this shim's own execution. A doctest run also compiles and
    /// runs its doctests one at a time.
    Lend { one_doctest_at_a_time: bool },
}

/// Trust (CUSTODY-PROTOCOL1-LAUNCH-1): Cargo hands its scheduler only to
/// compilation units, so `rustdoc --test` reaches this shim with none, and in a
/// strict custody context the real rustdoc refuses for want of one: "native
/// compiler work has no captured inherited GNU scheduler". It is owed this
/// shim's own synchronous execution (Cargo waits for the shim) when the shim
/// inherited no scheduler and received no GNU advertisement at all
/// (`inbound_advertised`, read at entry), and the command marks a strict
/// context. Anything advertised, even a broken advertisement, is forwarded
/// as it was, so the real rustdoc still judges and refuses it.
///
/// A loan is ONE execution, but rustdoc's doctest harness compiles and runs
/// doctests on as many threads as libtest is told, each compiler recovering
/// the loan through the handoff. So a doctest run is lent only with one test
/// thread, and not at all when its arguments choose any other thread count:
/// then it refuses as before.
fn lending_owed(
    inherited: bool,
    inbound_advertised: bool,
    cmd: &std::process::Command,
    args: &[std::ffi::OsString],
) -> Lending {
    let child_env = |name: &str| match cmd.get_envs().find(|(key, _)| *key == name) {
        Some((_, value)) => value.is_some(),
        None => env::var_os(name).is_some(),
    };
    if inherited
        || inbound_advertised
        || GNU_ADVERTISEMENTS.into_iter().any(child_env)
        || !STRICT_CUSTODY_MARKERS.into_iter().any(child_env)
    {
        return Lending::Forward;
    }
    if !args.iter().any(|arg| arg == "--test") {
        return Lending::Lend { one_doctest_at_a_time: false };
    }
    // rustdoc splits every `--test-args` value on whitespace. Any word naming
    // a thread count other than exactly `--test-threads=1` could beat
    // RUST_TEST_THREADS, so such a run is not lent.
    let words = args.iter().flat_map(|arg| {
        let arg = arg.to_string_lossy();
        arg.split_whitespace()
            .map(|word| word.trim_start_matches("--test-args=").to_owned())
            .collect::<Vec<_>>()
    });
    if words.filter(|word| word.contains("--test-threads")).any(|word| word != "--test-threads=1") {
        return Lending::Forward;
    }
    Lending::Lend { one_doctest_at_a_time: true }
}

/// Trust (CUSTODY-PROTOCOL1-LAUNCH-1): apply `lending` to `cmd`. A loan is an
/// owned GNU pool holding ZERO tokens, with the descendant handoff each
/// doctest compiler (which rustdoc starts with no descriptor) recovers it
/// through. The returned owner, and `cmd`'s spawn hooks, which share it, must
/// outlive the child's wait.
fn lend(lending: Lending, cmd: &mut std::process::Command) -> Option<jobserver_utils::Jobserver> {
    let Lending::Lend { one_doctest_at_a_time } = lending else {
        return None;
    };
    let mut lent = jobserver_utils::Jobserver::new(0)
        .unwrap_or_else(|error| panic!("cannot lend rustdoc an empty scheduler: {error}"));
    lent.enable_descendant_handoff()
        .unwrap_or_else(|error| panic!("cannot lend rustdoc a descendant handoff: {error}"));
    lent.configure_make(cmd);
    if one_doctest_at_a_time {
        cmd.env("RUST_TEST_THREADS", "1");
    }
    Some(lent)
}

fn main() {
    // Trust: checked import precedes sidecar/argument-file opens. Keep its
    // descriptor owners alive through the final rustdoc wait.
    // SAFETY: this is the shim's first operation, before opening other files.
    let jobserver = unsafe { InheritedJobserver::from_env() }
        .unwrap_or_else(|error| panic!("cannot inherit bootstrap jobserver: {error}"));
    // Trust (CUSTODY-PROTOCOL1-LAUNCH-1): what reached this shim, before any
    // environment rewrite; see `lending_owed`.
    let inbound_advertised = GNU_ADVERTISEMENTS.into_iter().any(|name| env::var_os(name).is_some());

    // Refuse the retired marker on the AMBIENT environment, before the
    // Cargo-test sidecar can rewrite anything. Same guard as the rustc shim.
    if let Some(message) = retired_trust_bootstrap_shim_target_only_refusal(
        env::var_os(RETIRED_TRUST_BOOTSTRAP_SHIM_TARGET_ONLY_ENV).as_deref(),
    ) {
        panic!("{message}");
    }

    let authenticated_targo_frontend =
        env::var_os("TRUST_TARGO_FRONTEND").is_some_and(|value| value == "1");
    let mut isolated_shim_environment = activate_cargo_test_shim_environment()
        .unwrap_or_else(|err| panic!("failed to activate Cargo-test shim environment: {err}"));

    let raw_args = env::args_os().skip(1).collect::<Vec<_>>();
    let had_inbound_argfile =
        raw_args.iter().any(|arg| arg.to_str().is_some_and(|arg| arg.starts_with('@')));
    let args = expand_rustc_argfiles(&raw_args)
        .unwrap_or_else(|err| panic!("failed to load rustdoc argument file: {err}"));

    let stage = parse_rustc_stage();
    let verbose = parse_rustc_verbose();

    let rustdoc = env::var_os("RUSTDOC_REAL").expect("RUSTDOC_REAL was not set");
    let libdir = env::var_os("RUSTDOC_LIBDIR").expect("RUSTDOC_LIBDIR was not set");
    let sysroot = env::var_os("RUSTC_SYSROOT").expect("RUSTC_SYSROOT was not set");

    // Detect whether or not we're a build script depending on whether --target
    // is passed (a bit janky...)
    let target = parse_value_from_args(&args, "--target");

    let mut dylib_path = dylib_path();
    dylib_path.insert(0, PathBuf::from(libdir.clone()));

    // Trust: `-Ztrust-verify=off` only exists in Trust drivers. With a
    // bring-your-own stage0 (bootstrap/trust-stage0/README.md), the stage0
    // rustdoc is stock upstream and rejects the flag.
    let rustdoc_supports_trust_no_verify = {
        let path = Path::new(&rustdoc);
        path.file_stem()
            .and_then(|stem| stem.to_str())
            .is_some_and(|stem| stem.starts_with("trustdoc"))
            || path.components().any(|component| {
                matches!(
                    component.as_os_str().to_str(),
                    Some("stage0" | "stage1" | "stage2" | "stage3")
                )
            })
    };

    // ONE no-verify policy, shared with the rustc shim. rustdoc has a single
    // driver, so the same capability answer covers both the targeted and the
    // untargeted arm — which is exactly what rustdoc's own former copy of this
    // predicate computed, minus the risk of the two drifting again.
    let rustdoc_bootstrap_no_verify_applies = trust_bootstrap_no_verify_applies(
        target.is_some(),
        cargo_test_no_verify_requested(
            trust_bootstrap_shim_marker_enabled(
                env::var_os("TRUST_BOOTSTRAP_SHIM_NO_VERIFY").as_deref(),
            ),
            authenticated_targo_frontend,
        ),
        rustdoc_supports_trust_no_verify,
        rustdoc_supports_trust_no_verify,
        &args,
        parse_value_from_args(&args, "--crate-name"),
    );

    // A SNAPSHOT rustdoc is anything under a `stage0` directory — that
    // directory is definitionally the seed's, whose vintage is the seed pin's,
    // not this source tree's, so it may not parse the current off-switch
    // spelling. The stem carries no vintage information (the seed ships its
    // tools under trust names too). Computed here, before `rustdoc` moves
    // into the command builder.
    let rustdoc_is_stage0_snapshot = Path::new(&rustdoc)
        .components()
        .any(|component| component.as_os_str().to_str() == Some("stage0"));

    let mut cmd = ArgFileCommand::new(rustdoc);
    cmd.force_argfile(had_inbound_argfile);

    if target.is_some() {
        // The stage0 compiler has a special sysroot distinct from what we
        // actually downloaded, so we just always pass the `--sysroot` option,
        // unless one is already set.
        if !args.iter().any(|arg| arg == "--sysroot") {
            cmd.arg("--sysroot").arg(&sysroot);
        }
    } else {
        // Find any host flags that were passed by bootstrap.
        // The flags are stored in a RUSTC_HOST_FLAGS variable, separated by spaces.
        if let Ok(flags) = std::env::var("RUSTC_HOST_FLAGS") {
            cmd.args(flags.split(' '));
        }
    }

    cmd.args(&args);
    cmd.env(dylib_path_var(), env::join_paths(&dylib_path).unwrap());

    // Trust: the same additional sysroot paths the rustc shim adds
    // (`bin/rustc.rs`), because a DOCTEST is a rustdoc invocation and needs them
    // for exactly the same reason.
    //
    // Trust keeps staged sysroots pruned of rustc_private artifacts (upstream
    // #108767 parity), so a rustc_private tool must be handed the coherent
    // `rustc-private-tool` sysroot dirs. 681f6f5c0b9 did that for the
    // `CrateRustdoc` test rebuild — but only the RUSTC side reads the variable,
    // so `-p rustdoc --doc` still resolved `extern crate rustc_*` against
    // partially-pruned leftovers and died with the same E0463/E0460 cascade the
    // commit was written to fix ("can't find crate for `rustc_abi`", …).
    if let Ok(dirs) = env::var("RUSTC_ADDITIONAL_SYSROOT_PATHS") {
        for dir in dirs.split(',') {
            cmd.arg(format!("-L{dir}"));
        }
    }

    // Force all crates compiled by this compiler to (a) be unstable and (b)
    // allow the `rustc_private` feature to link to other unstable crates
    // also in the sysroot.
    if env::var_os("RUSTC_FORCE_UNSTABLE").is_some() {
        cmd.arg("-Z").arg("force-unstable-if-unmarked");
    }
    // Cargo doesn't pass RUSTDOCFLAGS to proc_macros:
    // https://github.com/rust-lang/cargo/issues/4423
    // Thus, if we are on stage 0, we explicitly set `--cfg=bootstrap`.
    // We also declare that the flag is expected, which we need to do to not
    // get warnings about it being unexpected.
    if stage == 0 {
        cmd.arg("--cfg=bootstrap");
    }

    if let Some(crate_name) = parse_value_from_args(&args, "--crate-name") {
        // Add rust logo and set html root for all rustc crates.
        if crate_name.starts_with("rustc_") {
            // We use `-Zcrate-attr=allow` instead of `-A` to force rustdoc to forward this flag to
            // the actual doctests. Otherwise those tests all receive the
            // `feature(rustdoc_internals)` without receiving the `-A` which leads to errors.
            cmd.arg("-Zcrate-attr=allow(internal_features)")
                .arg("-Zcrate-attr=doc(rust_logo)")
                .arg("-Zcrate-attr=doc(html_root_url = \"https://doc.rust-lang.org/nightly/nightly-rustc/\")");

            // Some crates already have this feature enabled
            cmd.arg("-Zcrate-attr=feature(rustdoc_internals)");
            cmd.arg("-Aduplicate-features");
        }
    }

    // Rustdoc parses its own rustc-style options, so enforce the Trust driver
    // capability and canonical value at its final process boundary too. Same
    // snapshot exception as the rustc shim: the stage0 seed's trustdoc may
    // predate the current spelling, so it gets the version-invariant env
    // transport instead of an argv flag it may not parse.
    if rustdoc_is_stage0_snapshot {
        if finalize_trust_no_verify_snapshot(
            cmd.args_mut(),
            rustdoc_supports_trust_no_verify,
            rustdoc_bootstrap_no_verify_applies,
        ) {
            cmd.env("TRUST_NO_VERIFY", "1");
        }
    } else {
        finalize_trust_no_verify(
            cmd.args_mut(),
            rustdoc_supports_trust_no_verify,
            rustdoc_bootstrap_no_verify_applies,
        );
    }

    let (mut cmd, arg_file) = cmd.build().unwrap();
    maybe_dump(format!("stage{}-rustdoc", stage + 1), &cmd);
    if let Some(environment) = &mut isolated_shim_environment {
        environment.restore_for_compiler_command(&mut cmd, rustdoc_bootstrap_no_verify_applies);
    }
    jobserver.configure(&mut cmd);
    // Trust (CUSTODY-PROTOCOL1-LAUNCH-1): held through the wait below.
    let lent =
        lend(lending_owed(jobserver.is_present(), inbound_advertised, &cmd, &args), &mut cmd);

    if verbose > 1 {
        eprintln!(
            "rustdoc command: {:?}={:?} {:?}",
            dylib_path_var(),
            env::join_paths(&dylib_path).unwrap(),
            cmd,
        );
        eprintln!("sysroot: {sysroot:?}");
        eprintln!("libdir: {libdir:?}");
    }

    let status = cmd.status();
    drop(arg_file);
    // Trust (CUSTODY-PROTOCOL1-LAUNCH-1): `exit` runs no destructor, and the
    // command's spawn hooks share the loan's handoff endpoint, whose drop
    // removes its socket directory. Release both before exiting.
    let rendered = status.is_err().then(|| format!("{cmd:?}"));
    drop(cmd);
    drop(lent);

    std::process::exit(match status {
        Ok(s) => s.code().unwrap_or(1),
        Err(e) => panic!("\n\nfailed to run {}: {e}\n\n", rendered.unwrap_or_default()),
    })
}
