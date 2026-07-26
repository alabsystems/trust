use std::ffi::OsString;
use std::path::Path;

use super::shared_helpers::{
    canonicalize_trust_no_verify, finalize_trust_no_verify, strip_trust_no_verify,
};
use super::{
    ArgFileCommand, enforce_trust_no_verify_capability, is_lint_driver_arg,
    rustc_driver_supports_trust_no_verify, should_apply_compiler_lint_flags,
    should_strip_cargo_rustc_arg, targeted_rustc_supports_trust_no_verify,
    trust_bootstrap_no_verify_applies,
};

fn rustc_args(args: &[&str]) -> Vec<OsString> {
    args.iter().map(OsString::from).collect()
}

#[test]
fn strips_self_when_cargo_uses_shim_as_rustc() {
    let host = "aarch64-unknown-linux-gnu";
    let current_exe = Path::new("/checkout/build/bootstrap/debug/rustc");
    let arg0 = OsString::from("/checkout/build/bootstrap/debug/rustc");

    assert!(should_strip_cargo_rustc_arg(&arg0, host, current_exe, None, None));
}

#[test]
fn strips_selected_trust_compiler_when_used_as_wrapper() {
    let host = "aarch64-unknown-linux-gnu";
    let current_exe = Path::new("/checkout/build/bootstrap/debug/rustc");
    let arg0 = OsString::from("/checkout/build/aarch64-unknown-linux-gnu/stage2/bin/trustc");
    let cargo_rustc = OsString::from("/checkout/build/aarch64-unknown-linux-gnu/stage2/bin/trustc");

    assert!(should_strip_cargo_rustc_arg(&arg0, host, current_exe, Some(&cargo_rustc), None));
}

#[test]
fn strips_real_compiler_when_targo_probes_seed_stage0() {
    // Trust: bootstrapping from a self-hosted seed — targo probes rustc
    // capabilities with the concrete stage0 compiler path (RUSTC_REAL), which
    // matches neither the shim path nor $RUSTC (both the shim). Without the
    // RUSTC_REAL check the probe would forward the compiler as a source input
    // ("multiple input filenames provided").
    let host = "aarch64-apple-darwin";
    let current_exe = Path::new("/checkout/build/bootstrap/debug/rustc");
    let cargo_rustc = OsString::from("/checkout/build/bootstrap/debug/rustc");
    let rustc_real = OsString::from("/checkout/build/trust-seed-sysroot/bin/trustc");
    let arg0 = OsString::from("/checkout/build/trust-seed-sysroot/bin/trustc");

    assert!(should_strip_cargo_rustc_arg(
        &arg0,
        host,
        current_exe,
        Some(&cargo_rustc),
        Some(&rustc_real),
    ));
}

#[test]
fn preserves_first_real_compiler_argument() {
    let host = "aarch64-unknown-linux-gnu";
    let current_exe = Path::new("/checkout/build/bootstrap/debug/rustc");
    let arg0 = OsString::from("-");
    let cargo_rustc = OsString::from("/checkout/build/aarch64-unknown-linux-gnu/stage2/bin/trustc");
    let rustc_real = OsString::from("/checkout/build/aarch64-unknown-linux-gnu/stage2/bin/trustc");

    assert!(!should_strip_cargo_rustc_arg(
        &arg0,
        host,
        current_exe,
        Some(&cargo_rustc),
        Some(&rustc_real),
    ));
}

#[test]
fn recognizes_public_and_inherited_lint_driver_names() {
    let host = "aarch64-unknown-linux-gnu";
    assert!(is_lint_driver_arg(
        &OsString::from("/checkout/build/host/stage2/bin/tippy-driver"),
        host
    ));
    assert!(is_lint_driver_arg(
        &OsString::from("/checkout/build/host/stage0/bin/clippy-driver"),
        host
    ));
    assert!(!is_lint_driver_arg(&OsString::from("/checkout/build/host/stage2/bin/trustc"), host));
}

#[test]
fn compiler_lint_flags_apply_only_below_the_compiler_manifest_root() {
    use std::ffi::OsStr;

    let compiler_root = OsStr::new("/checkout/compiler");
    assert!(should_apply_compiler_lint_flags(
        Some(OsStr::new("/checkout/compiler/rustc_mir_transform")),
        Some(compiler_root),
    ));
    assert!(!should_apply_compiler_lint_flags(
        Some(OsStr::new("/checkout/first-party/ay/crates/ay-drat-check")),
        Some(compiler_root),
    ));
    assert!(!should_apply_compiler_lint_flags(None, Some(compiler_root)));
    assert!(!should_apply_compiler_lint_flags(
        Some(OsStr::new("/checkout/compiler/rustc_driver")),
        None,
    ));
}

// Signature under test:
//   trust_bootstrap_no_verify_applies(
//       has_target, requested, targeted_rustc_supports_no_verify,
//       no_target_rustc_supports_no_verify,
//       args, crate_name)

#[test]
fn trust_bootstrap_no_verify_applies_to_target_compiles_with_trust_native_driver() {
    let args = rustc_args(&["rustc", "lib.rs", "--crate-name", "core", "--crate-type", "lib"]);

    // Targeted compile dispatched to a Trust-native driver: disable verification.
    assert!(trust_bootstrap_no_verify_applies(true, true, true, false, &args, Some("core")));
    // Not requested by bootstrap: never applies, even to a Trust-native driver.
    assert!(!trust_bootstrap_no_verify_applies(true, false, true, true, &args, Some("core")));
}

#[test]
fn trust_bootstrap_no_verify_skips_target_compiles_on_stock_stage0() {
    // A bring-your-own stage0 (stock upstream rustc) does not understand the
    // flag, so a targeted stage0 compile must not receive it. With an
    // unsupported driver both `targeted_*` and `no_target_*` support are false
    // (driver support is a strict subset of targeted support).
    let args = rustc_args(&["rustc", "lib.rs", "--crate-name", "core", "--crate-type", "lib"]);

    assert!(!trust_bootstrap_no_verify_applies(true, true, false, false, &args, Some("core")));
}

#[test]
fn trust_bootstrap_no_verify_applies_to_no_target_host_libraries() {
    let args = rustc_args(&[
        "rustc",
        "--crate-name",
        "rustc_version",
        "src/lib.rs",
        "--crate-type",
        "lib",
    ]);

    assert!(trust_bootstrap_no_verify_applies(
        false,
        true,
        false,
        true,
        &args,
        Some("rustc_version")
    ));
    assert!(!trust_bootstrap_no_verify_applies(
        false,
        true,
        false,
        false,
        &args,
        Some("rustc_version")
    ));
}

#[test]
fn trust_bootstrap_no_verify_applies_to_direct_file_and_stdin_compiles() {
    let direct = rustc_args(&["src/lib.rs", "--crate-type=lib"]);
    assert!(trust_bootstrap_no_verify_applies(false, true, false, true, &direct, None,));

    let stdin = rustc_args(&["-", "--crate-name", "direct_stdin", "--crate-type=lib"]);
    assert!(trust_bootstrap_no_verify_applies(
        false,
        true,
        false,
        true,
        &stdin,
        Some("direct_stdin"),
    ));
}

#[test]
fn trust_bootstrap_no_verify_skips_no_target_cargo_probes() {
    let split_print_args =
        rustc_args(&["rustc", "-", "--crate-name", "___", "--print", "file-names"]);
    let joined_print_args =
        rustc_args(&["rustc", "-", "--crate-name", "___", "--print=file-names"]);

    assert!(!trust_bootstrap_no_verify_applies(
        false,
        true,
        false,
        true,
        &split_print_args,
        Some("___")
    ));
    // An explicit target does not turn the same target-information query into
    // a real crate compilation.
    assert!(!trust_bootstrap_no_verify_applies(
        true,
        true,
        true,
        true,
        &joined_print_args,
        Some("___")
    ));
    assert!(!trust_bootstrap_no_verify_applies(
        false,
        true,
        false,
        true,
        &joined_print_args,
        Some("___")
    ));
}

#[test]
fn trust_bootstrap_no_verify_applies_to_no_target_build_scripts_and_proc_macros() {
    let build_script_args =
        rustc_args(&["rustc", "--crate-name", "build_script_build", "build.rs"]);
    let split_proc_macro_args =
        rustc_args(&["rustc", "--crate-name", "pm", "src/lib.rs", "--crate-type", "proc-macro"]);
    let joined_proc_macro_args =
        rustc_args(&["rustc", "--crate-name", "pm", "src/lib.rs", "--crate-type=proc-macro"]);

    assert!(trust_bootstrap_no_verify_applies(
        false,
        true,
        false,
        true,
        &build_script_args,
        Some("build_script_build")
    ));
    assert!(trust_bootstrap_no_verify_applies(
        false,
        true,
        false,
        true,
        &split_proc_macro_args,
        Some("pm")
    ));
    assert!(trust_bootstrap_no_verify_applies(
        false,
        true,
        false,
        true,
        &joined_proc_macro_args,
        Some("pm")
    ));
    // Host driver that does not understand the flag (stock stage0 snapshot): skip.
    assert!(!trust_bootstrap_no_verify_applies(
        false,
        true,
        false,
        false,
        &build_script_args,
        Some("build_script_build")
    ));
}

#[test]
fn stage1_std_host_units_get_one_canonical_no_verify_switch() {
    let driver = OsString::from("/checkout/build/aarch64-unknown-linux-gnu/stage0/bin/trustc");
    let targeted_support = targeted_rustc_supports_trust_no_verify(&driver);
    let host_support = rustc_driver_supports_trust_no_verify(&driver);
    assert!(targeted_support && host_support);

    for authored in [
        rustc_args(&[
            "-Ztrust_verify=on",
            "-Z",
            "trust-verify=on",
            "--crate-name",
            "build_script_build",
            "build.rs",
        ]),
        rustc_args(&[
            "-Ztrust-verify=on",
            "--crate-name",
            "shlex",
            "src/lib.rs",
            "--crate-type=lib",
        ]),
        rustc_args(&[
            "-Z",
            "trust_verify=on",
            "--crate-name",
            "fixture_macros",
            "src/lib.rs",
            "--crate-type=proc-macro",
        ]),
    ] {
        let mut args = authored;
        let applies = trust_bootstrap_no_verify_applies(
            false,
            true,
            targeted_support,
            host_support,
            &args,
            None,
        );
        finalize_trust_no_verify(&mut args, targeted_support, applies);

        assert_eq!(
            args.iter().filter(|arg| *arg == "-Ztrust-verify=off").count(),
            1,
            "Stage1 Std host unit did not receive one canonical off-switch: {args:?}"
        );
        assert_eq!(args.last(), Some(&OsString::from("-Ztrust-verify=off")));
        assert!(!args.iter().any(|arg| {
            arg.to_string_lossy().contains("trust_verify")
                || arg.to_string_lossy().contains("trust-verify=on")
        }));
    }
}

#[test]
fn detects_stage_rustc_drivers_that_support_trust_no_verify() {
    assert!(rustc_driver_supports_trust_no_verify(&OsString::from(
        "/checkout/build/aarch64-unknown-linux-gnu/stage1/bin/rustc"
    )));
    assert!(rustc_driver_supports_trust_no_verify(&OsString::from(
        "/checkout/build/host/stage2/bin/trustc"
    )));
    // A canonical Trust-named stage0 driver advertises and accepts the flag for
    // host build scripts and proc macros as well as target crates.
    assert!(rustc_driver_supports_trust_no_verify(&OsString::from(
        "/checkout/build/aarch64-unknown-linux-gnu/stage0/bin/trustc"
    )));
    // A stock-compatible rustc leaf in a stage0 directory remains excluded.
    assert!(!rustc_driver_supports_trust_no_verify(&OsString::from(
        "/checkout/build/aarch64-unknown-linux-gnu/stage0/bin/rustc"
    )));
    assert!(!rustc_driver_supports_trust_no_verify(&OsString::from("/opt/homebrew/bin/rustc")));
    assert!(!rustc_driver_supports_trust_no_verify(&OsString::from("/tmp/trustc-wrapper")));
}

#[test]
fn detects_targeted_drivers_that_support_trust_no_verify() {
    // Any bootstrap-managed stage snapshot understands the flag — including
    // stage0, which is a Trust `trustc` payload by default.
    for stage in ["stage0", "stage1", "stage2", "stage3"] {
        assert!(targeted_rustc_supports_trust_no_verify(&OsString::from(format!(
            "/checkout/build/aarch64-unknown-linux-gnu/{stage}/bin/rustc"
        ))));
    }
    // A `trustc`-named driver outside the build tree is Trust-native.
    assert!(targeted_rustc_supports_trust_no_verify(&OsString::from("/usr/local/bin/trustc")));
    // A bring-your-own stock upstream stage0 is not, and neither is a bare name.
    assert!(!targeted_rustc_supports_trust_no_verify(&OsString::from("/opt/homebrew/bin/rustc")));
    assert!(!targeted_rustc_supports_trust_no_verify(&OsString::from("rustc")));
    assert!(!targeted_rustc_supports_trust_no_verify(&OsString::from("/tmp/trustc-wrapper")));

    // Invariant the strip site relies on, in the contrapositive form it uses:
    // when `!targeted_rustc_supports` we strip, and that guarantees
    // `!rustc_driver_supports`, so the later add-path can never re-add the flag.
    // It holds because driver support is a subset of targeted support:
    // {trustc} ∪ {stage1,2,3} ⊂ {trustc} ∪ {stage0,1,2,3}.
    let unsupported = OsString::from("/opt/homebrew/bin/rustc");
    assert!(!targeted_rustc_supports_trust_no_verify(&unsupported));
    assert!(!rustc_driver_supports_trust_no_verify(&unsupported));

    // A canonical Trust-named stage0 is supported in both lanes. This matters
    // when local-rebuild auto-detection classifies the seed as stage1-capable:
    // build scripts and proc macros still run without an explicit --target.
    let stage0 = OsString::from("/checkout/build/aarch64-unknown-linux-gnu/stage0/bin/rustc");
    assert!(targeted_rustc_supports_trust_no_verify(&stage0));
    assert!(!rustc_driver_supports_trust_no_verify(&stage0));

    let trust_stage0 =
        OsString::from("/checkout/build/aarch64-unknown-linux-gnu/stage0/bin/trustc");
    assert!(targeted_rustc_supports_trust_no_verify(&trust_stage0));
    assert!(rustc_driver_supports_trust_no_verify(&trust_stage0));
}

#[test]
fn enforce_capability_strips_flag_for_byo_stock_stage0() {
    // The reachable leak: a bring-your-own stage0 (`build.rustc` = stock upstream
    // rustc) drives `build_compiler_stage >= 1`, so bootstrap injects
    // `-Ztrust-verify=off` driver-blind via `CARGO_TARGET_*_RUSTFLAGS`; cargo hands
    // it to the shim as argv on `--target` compiles. The stock driver cannot parse
    // it, so it must be stripped before the driver is invoked.
    let stock = OsString::from("/opt/homebrew/bin/rustc");

    let mut joined = rustc_args(&["-Ztrust-verify=off", "lib.rs", "--crate-name", "core"]);
    enforce_trust_no_verify_capability(&stock, &mut joined);
    assert_eq!(joined, rustc_args(&["lib.rs", "--crate-name", "core"]));

    let mut split = rustc_args(&["-Z", "trust-verify=off", "lib.rs", "--crate-name", "core"]);
    enforce_trust_no_verify_capability(&stock, &mut split);
    assert_eq!(split, rustc_args(&["lib.rs", "--crate-name", "core"]));
}

#[test]
fn enforce_capability_keeps_flag_for_trust_native_driver() {
    // A Trust-native driver (any stageN snapshot, including the stage0 `trustc`
    // payload, or a `trustc`-stemmed binary) understands the flag, so an injected
    // copy is preserved untouched.
    for driver in [
        "/checkout/build/aarch64-unknown-linux-gnu/stage1/bin/rustc",
        "/checkout/build/aarch64-unknown-linux-gnu/stage0/bin/trustc",
        "/usr/local/bin/trustc",
    ] {
        let mut args = rustc_args(&["-Ztrust-verify=off", "lib.rs", "--crate-name", "core"]);
        enforce_trust_no_verify_capability(&OsString::from(driver), &mut args);
        assert_eq!(args, rustc_args(&["-Ztrust-verify=off", "lib.rs", "--crate-name", "core"]));
    }
}

#[test]
fn strip_trust_no_verify_removes_joined_and_split_forms() {
    // Joined form.
    let mut joined = rustc_args(&["-Ztrust-verify=off", "--crate-name", "core"]);
    strip_trust_no_verify(&mut joined);
    assert_eq!(joined, rustc_args(&["--crate-name", "core"]));

    // Split `-Z trust-verify=off` form.
    let mut split = rustc_args(&["-Z", "trust-verify=off", "-Cdebuginfo=0"]);
    strip_trust_no_verify(&mut split);
    assert_eq!(split, rustc_args(&["-Cdebuginfo=0"]));

    // Multiple occurrences across both forms; unrelated `-Z` flags are preserved.
    let mut mixed = rustc_args(&[
        "-Ztrust-verify=off",
        "-Ztime-passes",
        "-Z",
        "trust-verify=off",
        "-Z",
        "force-unstable-if-unmarked",
    ]);
    strip_trust_no_verify(&mut mixed);
    assert_eq!(mixed, rustc_args(&["-Ztime-passes", "-Z", "force-unstable-if-unmarked"]));

    // A trailing bare `-Z` with no following token is left untouched.
    let mut trailing = rustc_args(&["-Ztrust-verify=off", "-Z"]);
    strip_trust_no_verify(&mut trailing);
    assert_eq!(trailing, rustc_args(&["-Z"]));

    // Values and underscore spellings are controls too, while a positional
    // lookalike after `--` is source input and must remain untouched.
    let mut valued = rustc_args(&[
        "-Ztrust_verify=on",
        "-Z",
        "trust-verify=off",
        "--",
        "-Ztrust-verify=off",
    ]);
    strip_trust_no_verify(&mut valued);
    assert_eq!(valued, rustc_args(&["--", "-Ztrust-verify=off"]));

    // Nothing to strip.
    let mut none = rustc_args(&["--crate-name", "core", "-Ztime-passes"]);
    strip_trust_no_verify(&mut none);
    assert_eq!(none, rustc_args(&["--crate-name", "core", "-Ztime-passes"]));
}

#[test]
fn canonical_no_verify_wins_conflicts_before_positional_tail() {
    let mut args = rustc_args(&[
        "lib.rs",
        "-Ztrust-verify=on",
        "-Z",
        "trust_verify=on",
        "--",
        "-Ztrust-verify=on",
    ]);
    canonicalize_trust_no_verify(&mut args);
    assert_eq!(args, rustc_args(&["lib.rs", "-Ztrust-verify=off", "--", "-Ztrust-verify=on",]));
}

#[test]
fn forced_argfile_preserves_nested_at_argument_for_exactly_one_driver_expansion() {
    let mut command = ArgFileCommand::new("rustc");
    command.force_argfile(true).args(["--crate-name", "fixture", "@literal-inner.args"]);
    let (command, argfile) = command.build().unwrap();
    let argfile = argfile.expect("forced response file must be retained");

    assert_eq!(command.get_args().count(), 1);
    assert_eq!(
        std::fs::read_to_string(argfile.path()).unwrap(),
        "--crate-name\nfixture\n@literal-inner.args\n",
    );
}

#[test]
fn forced_argfile_keeps_wrapper_compiler_argument_explicit() {
    let mut command = ArgFileCommand::new("wrapper");
    command.arg("/toolchain/bin/trustc").argfile_prefix_args(1).force_argfile(true).args([
        "--crate-name",
        "fixture",
        "src/lib.rs",
    ]);
    let (command, argfile) = command.build().unwrap();
    let args = command.get_args().collect::<Vec<_>>();

    assert_eq!(args.len(), 2);
    assert_eq!(args[0], "/toolchain/bin/trustc");
    assert!(args[1].to_string_lossy().starts_with('@'));
    assert_eq!(
        std::fs::read_to_string(argfile.unwrap().path()).unwrap(),
        "--crate-name\nfixture\nsrc/lib.rs\n",
    );
}
