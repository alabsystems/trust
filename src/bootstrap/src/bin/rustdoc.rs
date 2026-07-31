//! Shim which is passed to Cargo as "rustdoc" when running the bootstrap.
//!
//! See comments in `src/bootstrap/rustc.rs` for more information.

use std::env;
use std::path::{Path, PathBuf};

use arg_file_command::ArgFileCommand;
use shared_helpers::{
    activate_cargo_test_shim_environment, cargo_test_no_verify_requested,
    compile_uses_trust_bootstrap_no_verify, dylib_path, dylib_path_var, expand_rustc_argfiles,
    finalize_trust_no_verify, finalize_trust_no_verify_snapshot, maybe_dump, parse_rustc_stage,
    parse_rustc_verbose, parse_value_from_args, trust_bootstrap_shim_marker_enabled,
};

#[path = "../utils/shared_helpers.rs"]
mod shared_helpers;

#[path = "../../../build_helper/src/arg_file_command.rs"]
mod arg_file_command;

#[cfg(test)]
#[path = "rustdoc/tests.rs"]
mod tests;

fn main() {
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

    let rustdoc_bootstrap_no_verify_applies = rustdoc_bootstrap_no_verify_applies(
        cargo_test_no_verify_requested(
            trust_bootstrap_shim_marker_enabled(
                env::var_os("TRUST_BOOTSTRAP_SHIM_NO_VERIFY").as_deref(),
            ),
            authenticated_targo_frontend,
        ),
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
            cmd.arg("-Ainternal_features")
                .arg("-Zcrate-attr=doc(rust_logo)")
                .arg("-Zcrate-attr=doc(html_root_url = \"https://doc.rust-lang.org/nightly/nightly-rustc/\")");

            // rustc_proc_macro is another build of library/proc_macro which already enables this
            // feature
            if crate_name != "rustc_proc_macro" {
                cmd.arg("-Zcrate-attr=feature(rustdoc_internals)");
            }
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
        environment.restore();
    }

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

    std::process::exit(match status {
        Ok(s) => s.code().unwrap_or(1),
        Err(e) => panic!("\n\nfailed to run {cmd:?}: {e}\n\n"),
    })
}

fn rustdoc_bootstrap_no_verify_applies(
    requested: bool,
    rustdoc_supports_no_verify: bool,
    args: &[std::ffi::OsString],
    _crate_name: Option<&str>,
) -> bool {
    requested && rustdoc_supports_no_verify && compile_uses_trust_bootstrap_no_verify(args)
}
