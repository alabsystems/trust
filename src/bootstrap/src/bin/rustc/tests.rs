use std::ffi::{OsStr, OsString};
use std::path::Path;

use shim_utils::{
    canonicalize_trust_no_verify, canonicalize_trust_verify_on, cargo_test_no_verify_requested,
    finalize_trust_no_verify, finalize_trust_no_verify_snapshot, is_cargo_target_info_probe,
    strip_trust_no_verify, trust_bootstrap_verify_unit_argv_refusal,
    trust_bootstrap_verify_unit_requested,
};

use super::{
    ArgFileCommand, TrustVerifyEnvAction, enforce_trust_no_verify_capability,
    finalize_trust_verify_control, is_lint_driver_arg, is_version_query,
    rustc_driver_supports_trust_no_verify, should_apply_compiler_lint_flags,
    should_strip_cargo_rustc_arg, targeted_rustc_is_built_stage, targeted_rustc_is_stage0_snapshot,
    targeted_rustc_supports_trust_no_verify, trust_bootstrap_no_verify_applies,
    trust_bootstrap_off_switch_applies, trust_bootstrap_verify_unit_applies,
};

fn rustc_args(args: &[&str]) -> Vec<OsString> {
    args.iter().map(OsString::from).collect()
}

// Trust: capability checks inspect the seed payload, so positive snapshot
// fixtures must carry the actual sibling names rather than only a stage0 path.
fn trust_seed_snapshot_fixture() -> (tempfile::TempDir, std::path::PathBuf) {
    let directory = tempfile::tempdir().expect("seed fixture directory");
    let bin = directory.path().join("build/host/stage0/bin");
    std::fs::create_dir_all(&bin).expect("seed fixture bin directory");
    for name in ["rustc", "trustc"] {
        std::fs::write(bin.join(name), []).expect("seed fixture driver name");
    }
    (directory, bin)
}

// Trust: a positive seed-layout control must materialize the sibling that
// distinguishes a Trust snapshot from a stock driver parked under stage0.
fn seed_snapshot_drivers() -> (tempfile::TempDir, [OsString; 2]) {
    let payload = tempfile::tempdir().unwrap();
    let bin = payload.path().join("stage0/bin");
    std::fs::create_dir_all(&bin).unwrap();
    let drivers = [bin.join("rustc"), bin.join("trustc")];
    for driver in &drivers {
        std::fs::write(driver, b"seed-layout test fixture; never executed").unwrap();
    }
    (payload, drivers.map(|driver| driver.into_os_string()))
}

#[test]
fn version_query_requires_an_exact_argument_vector() {
    for args in [
        vec!["-V"],
        vec!["--version"],
        vec!["-vV"],
        vec!["-Vv"],
        vec!["--version", "--verbose"],
        vec!["--verbose", "--version"],
    ] {
        assert!(is_version_query(&rustc_args(&args)), "{args:?}");
    }
    for args in [
        vec![],
        vec!["--version", "input.rs"],
        vec!["--version", "--emit=metadata"],
        vec!["@version.args"],
        vec!["--version", "@extra.args"],
    ] {
        assert!(!is_version_query(&rustc_args(&args)), "{args:?}");
    }
}

#[cfg(unix)]
#[test]
fn version_query_never_discards_non_utf8_arguments() {
    use std::os::unix::ffi::OsStringExt;

    let args = [OsString::from("--version"), OsString::from_vec(vec![0xff])];
    assert!(!is_version_query(&args));
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
    // unsupported driver both `targeted_*` and `no_target_*` support are false.
    let args = rustc_args(&["rustc", "lib.rs", "--crate-name", "core", "--crate-type", "lib"]);

    assert!(!trust_bootstrap_no_verify_applies(true, true, false, false, &args, Some("core")));
}

/// Trust: a snapshot `rustc` leaf with no `trustc` sibling beside it is
/// indistinguishable from a bring-your-own stock stage0 and stays out of
/// both driver arms. The positive seed cases carry the companion file in an
/// isolated payload directory.
#[test]
fn snapshot_without_trustc_sibling_stays_out_of_the_driver_arm() {
    let snapshot = OsString::from("/checkout/build/aarch64-apple-darwin/stage0/bin/rustc");
    assert!(!rustc_driver_supports_trust_no_verify(&snapshot));
    assert!(!targeted_rustc_supports_trust_no_verify(&snapshot));

    let stock = OsString::from("/opt/homebrew/bin/rustc");
    assert!(!rustc_driver_supports_trust_no_verify(&stock));
    assert!(!targeted_rustc_supports_trust_no_verify(&stock));

    // Trust: without an incoming off-request, that missing sibling must also
    // prevent injection through the composed untargeted-host dispatch.
    let original = rustc_args(&["--crate-name", "host_dependency", "host.rs", "--crate-type=lib"]);
    let supports = targeted_rustc_supports_trust_no_verify(&snapshot);
    let applies = trust_bootstrap_off_switch_applies(
        false,
        true,
        supports,
        rustc_driver_supports_trust_no_verify(&snapshot),
        false,
        &original,
        Some("host_dependency"),
    );
    assert!(!applies);
    let mut args = original.clone();
    enforce_trust_no_verify_capability(&snapshot, &mut args);
    assert_eq!(
        finalize_trust_verify_control(&mut args, false, true, supports, applies),
        TrustVerifyEnvAction::Preserve
    );
    assert_eq!(args, original);
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
fn seed_snapshot_host_units_use_the_version_invariant_transport() {
    let (_payload, drivers) = seed_snapshot_drivers();
    for driver in drivers {
        let driver_name = Path::new(&driver).file_name().unwrap().to_string_lossy();
        assert!(rustc_driver_supports_trust_no_verify(&driver));
        for (name, crate_type) in [
            ("build_script_build", "bin"),
            ("host_dependency", "lib"),
            ("host_proc_macro", "proc-macro"),
        ] {
            let mut args =
                rustc_args(&["--crate-name", name, "host.rs", "--crate-type", crate_type]);
            let applies = trust_bootstrap_off_switch_applies(
                false,
                true,
                targeted_rustc_supports_trust_no_verify(&driver),
                rustc_driver_supports_trust_no_verify(&driver),
                false,
                &args,
                Some(name),
            );
            assert!(applies, "{driver_name} {name}");
            assert_eq!(
                finalize_trust_verify_control(&mut args, false, true, true, applies),
                TrustVerifyEnvAction::SetOff,
                "a snapshot must not receive a version-dependent argv off-switch"
            );
            assert!(!args.iter().any(|arg| arg.to_string_lossy().contains("trust-verify")));
        }
    }
}

#[test]
fn authenticated_seed_snapshot_is_not_isolated_by_bootstrap() {
    let (_payload, drivers) = seed_snapshot_drivers();
    for driver in drivers {
        let driver_name = Path::new(&driver).file_name().unwrap().to_string_lossy();
        let args = rustc_args(&[
            "--crate-name",
            "host_dependency",
            "host.rs",
            "--crate-type=lib",
            "-Ztrust-verify=on",
        ]);
        let supports = targeted_rustc_supports_trust_no_verify(&driver);
        let snapshot = targeted_rustc_is_stage0_snapshot(&driver);
        assert!(supports && snapshot);
        // Compose the same authentication, capability, compile and finalizer
        // predicates as main: a present bootstrap marker cannot downgrade a
        // verified frontend, even though this seed can honor an off-request.
        let requested = cargo_test_no_verify_requested(true, true);
        let applies = trust_bootstrap_off_switch_applies(
            false,
            requested,
            supports,
            rustc_driver_supports_trust_no_verify(&driver),
            targeted_rustc_is_built_stage(&driver),
            &args,
            Some("host_dependency"),
        );
        assert!(!applies, "{driver_name}: authenticated frontend was isolated");
        let mut forwarded = args.clone();
        enforce_trust_no_verify_capability(&driver, &mut forwarded);
        assert_eq!(
            finalize_trust_verify_control(&mut forwarded, false, snapshot, supports, applies),
            TrustVerifyEnvAction::Preserve,
            "{driver_name}: snapshot finalization must not set TRUST_NO_VERIFY"
        );
        // Snapshot finalization removes the versioned spelling, leaving the
        // frontend's existing environment untouched, without adding an off-switch.
        assert_eq!(
            forwarded,
            rustc_args(&["--crate-name", "host_dependency", "host.rs", "--crate-type=lib",])
        );
    }
}

#[test]
fn stock_and_snapshot_host_dispatch_never_forward_trust_verification_flags() {
    let (_payload, [snapshot_rustc, snapshot_trustc]) = seed_snapshot_drivers();
    for (driver, expected_action) in [
        (OsString::from("/opt/homebrew/bin/rustc"), TrustVerifyEnvAction::Preserve),
        // A stage0-shaped path alone is not evidence of a Trust payload.
        // Keep a stock driver's environment while stripping Trust-only argv.
        (OsString::from("/checkout/build/native/stage0/bin/rustc"), TrustVerifyEnvAction::Preserve),
        (snapshot_rustc, TrustVerifyEnvAction::SetOff),
        (snapshot_trustc, TrustVerifyEnvAction::SetOff),
    ] {
        let mut args = rustc_args(&[
            "--crate-name",
            "host_dependency",
            "host.rs",
            "--crate-type=lib",
            "-Ztrust-verify=off",
            "-Z",
            "no-trust-verify=yes",
        ]);
        let original = args.clone();
        let supports = targeted_rustc_supports_trust_no_verify(&driver);
        let snapshot = targeted_rustc_is_stage0_snapshot(&driver);
        enforce_trust_no_verify_capability(&driver, &mut args);
        let applies = trust_bootstrap_off_switch_applies(
            false,
            cargo_test_no_verify_requested(true, false),
            supports,
            rustc_driver_supports_trust_no_verify(&driver),
            targeted_rustc_is_built_stage(&driver),
            &original,
            Some("host_dependency"),
        );
        assert_eq!(
            finalize_trust_verify_control(&mut args, false, snapshot, supports, applies),
            expected_action,
            "{driver:?}"
        );
        assert_eq!(
            args,
            rustc_args(&["--crate-name", "host_dependency", "host.rs", "--crate-type=lib",]),
            "{driver:?}: versioned Trust options reached the driver"
        );
        // Every snapshot strips versioned argv. An explicit incoming request
        // remains environment-only; a stock snapshot ignores that transport.
    }
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

/// Trust: Cargo's TARGETED target-information probe of a stage-1 std build — the
/// argv measured 2026-10-13 with Targo as bootstrap's Cargo, which strips every
/// `-Ztrust_*` token (the off-switch included) from the probe — gets bootstrap's
/// off-switch back, exactly once, and keeps std's own flags. Without it the
/// stage-1 `trustc` answers the probe at its verifying default and, since T6,
/// refuses std's `-Zinline-mir`: the std build aborted before compiling anything.
#[test]
fn targeted_probe_on_a_built_stage_gets_one_off_switch() {
    let built = OsString::from("/checkout/build/aarch64-apple-darwin/stage1/bin/rustc");
    let probe = rustc_args(&[
        "-",
        "--crate-name",
        "___",
        "--print=file-names",
        "-Zannotate-moves",
        "-Zinline-mir",
        "-Zinline-mir-preserve-debug",
        "--target",
        "aarch64-apple-darwin",
        "--crate-type",
        "bin",
        "--crate-type",
        "rlib",
        "--print=sysroot",
        "--print=cfg",
    ]);
    assert!(is_cargo_target_info_probe(&probe));
    // The compile-only predicate gives a probe nothing (unchanged, and pinned by
    // `trust_bootstrap_no_verify_skips_no_target_cargo_probes`): that was the gap.
    assert!(!trust_bootstrap_no_verify_applies(true, true, true, true, &probe, Some("___")));

    let applies = trust_bootstrap_off_switch_applies(
        true,
        true,
        targeted_rustc_supports_trust_no_verify(&built),
        rustc_driver_supports_trust_no_verify(&built),
        targeted_rustc_is_built_stage(&built),
        &probe,
        Some("___"),
    );
    assert!(applies, "the stage-1 std probe must carry the units' off-switch");
    let mut args = probe.clone();
    assert_eq!(
        finalize_trust_verify_control(
            &mut args,
            false,
            targeted_rustc_is_stage0_snapshot(&built),
            targeted_rustc_supports_trust_no_verify(&built),
            applies,
        ),
        TrustVerifyEnvAction::Preserve
    );
    assert_eq!(args.iter().filter(|arg| *arg == "-Ztrust-verify=off").count(), 1, "{args:?}");
    assert!(args.iter().any(|arg| arg == "-Zinline-mir"), "std's flags stay: {args:?}");
    assert!(args.iter().any(|arg| arg == "--print=cfg"));
}

/// Trust: the probe half of the off-switch is scoped — requested by bootstrap,
/// TARGETED, on a driver this tree built, and a real probe — and changes
/// nothing else: a seed's probe and a host probe keep today's answer, version
/// and help queries are not probes, and a real compile still goes through the
/// compile predicate.
#[test]
fn probe_off_switch_is_scoped_to_requested_targeted_probes_of_built_stages() {
    let probe = rustc_args(&["-", "--crate-name", "___", "--print=file-names", "--target", "t"]);
    let host_probe = rustc_args(&["-", "--crate-name", "___", "--print=file-names"]);
    let built = OsString::from("/checkout/build/host/stage2/bin/rustc");
    assert!(targeted_rustc_is_built_stage(&built));

    // Not requested by bootstrap.
    assert!(!trust_bootstrap_off_switch_applies(true, false, true, true, true, &probe, None));
    // A host probe (no `--target`): std's rustflags never reach it.
    assert!(!trust_bootstrap_off_switch_applies(false, true, true, true, true, &host_probe, None));
    // Seeds: bootstrap's stage0 snapshot and an installed `trustc` named as
    // `build.rustc` both support the switch, and neither is a built stage.
    let (_fixture, bin) = trust_seed_snapshot_fixture();
    for seed in [
        bin.join("rustc").into_os_string(),
        bin.join("trustc").into_os_string(),
        OsString::from("/opt/pkg/store/trust/9192/bin/trustc"),
    ] {
        assert!(targeted_rustc_supports_trust_no_verify(&seed));
        assert!(!targeted_rustc_is_built_stage(&seed), "{seed:?}");
        assert!(!trust_bootstrap_off_switch_applies(
            true,
            true,
            true,
            rustc_driver_supports_trust_no_verify(&seed),
            targeted_rustc_is_built_stage(&seed),
            &probe,
            None,
        ));
    }
    // Queries that print nothing for Cargo are not probes; `--print` after `--`
    // is positional, so that argv is a compile.
    for query in [
        &["-vV"][..],
        &["--version"],
        &["-Z", "help"],
        &["--explain", "E0001"],
        &["-", "--print=cfg", "--help"],
        &["src/lib.rs", "--", "--print=cfg"],
        &[],
        // Not Cargo's shape since the review follow-up: no `--crate-name ___`.
        &["-", "--print", "cfg"],
    ] {
        assert!(!is_cargo_target_info_probe(&rustc_args(query)), "{query:?}");
    }
    assert!(is_cargo_target_info_probe(&rustc_args(&[
        "-",
        "--crate-name",
        "___",
        "--print",
        "cfg"
    ])));
    // A real targeted compile still gets the switch, through the compile predicate.
    let compile =
        rustc_args(&["--crate-name", "core", "src/lib.rs", "--crate-type", "lib", "--target", "t"]);
    assert!(trust_bootstrap_off_switch_applies(true, true, true, true, true, &compile, None));
    assert!(trust_bootstrap_off_switch_applies(true, true, true, true, false, &compile, None));
}

/// Trust: Cargo's target-information probe exactly as the installed pack's Targo
/// (`321aaeda7`, the `build.cargo` of a `bootstrap.toml` in atpkg mode) sends it
/// (argv logged 2026-10-13 through a `RUSTC_WRAPPER` on `targo --unverified build
/// --target aarch64-apple-darwin` with `RUSTFLAGS=-Zinline-mir`; Targo had
/// already dropped its own `-Ztrust-verify=off`), with and without the leading
/// compiler path the shim sees when it runs as `RUSTC_WRAPPER`, as bootstrap
/// runs it; the host probe; and the one-crate-type re-probe Cargo makes from the
/// same prefix (`crate_type_process`). All are probes.
#[test]
fn cargo_target_info_probe_argv_is_a_probe() {
    let targeted = [
        "-",
        "--crate-name",
        "___",
        "--print=file-names",
        "-Zinline-mir",
        "--target",
        "aarch64-apple-darwin",
        "--crate-type",
        "bin",
        "--crate-type",
        "rlib",
        "--crate-type",
        "dylib",
        "--crate-type",
        "cdylib",
        "--crate-type",
        "staticlib",
        "--crate-type",
        "proc-macro",
        "--print=sysroot",
        "--print=split-debuginfo",
        "--print=crate-name",
        "--print=cfg",
        "-Wwarnings",
    ];
    let host = targeted
        .iter()
        .copied()
        .filter(|arg| !matches!(*arg, "--target" | "aarch64-apple-darwin" | "-Zinline-mir"))
        .collect::<Vec<_>>();
    let re_probe =
        ["-", "--crate-name", "___", "--print=file-names", "--target", "t", "--crate-type", "x"];
    for probe in [&targeted[..], &host[..], &re_probe[..]] {
        assert!(is_cargo_target_info_probe(&rustc_args(probe)), "{probe:?}");
        for compiler in ["/checkout/build/bootstrap/debug/rustc", "/opt/trust/bin/trustc"] {
            let wrapped =
                std::iter::once(compiler).chain(probe.iter().copied()).collect::<Vec<_>>();
            assert!(is_cargo_target_info_probe(&rustc_args(&wrapped)), "{wrapped:?}");
        }
    }
    // Both `--print` spellings, repeated, and the split `-W warnings`.
    assert!(is_cargo_target_info_probe(&rustc_args(&[
        "-",
        "--crate-name=___",
        "--print",
        "file-names",
        "--print=cfg",
        "--print",
        "sysroot",
        "-W",
        "warnings",
    ])));
}

/// Trust: rustc keeps COMPILING when every print request is `native-static-libs`
/// or `link-args` (`rustc_driver_impl::print_crate_info`), so such an invocation
/// is a real compile, never a probe, in either `--print` spelling and alone or
/// together. Before the review follow-up any `--print` made a probe, so under
/// the Cargo-test shim a `--target` staticlib fixture compile with
/// `--print=native-static-libs` that verified would silently have been switched
/// off. Each argv here was a probe to the old predicate.
#[test]
fn print_requests_that_keep_compiling_are_not_probes() {
    let compile =
        ["--crate-name", "foo", "src/lib.rs", "--crate-type", "staticlib", "--target", "t"];
    let probe_shape = ["-", "--crate-name", "___", "--target", "t"];
    let mut misread = Vec::new();
    for prints in [
        &["--print=native-static-libs"][..],
        &["--print", "native-static-libs"],
        &["--print=link-args"],
        &["--print", "link-args"],
        &["--print=native-static-libs", "--print=link-args"],
        &["--print", "link-args", "--print", "native-static-libs"],
    ] {
        for base in [&compile[..], &probe_shape[..]] {
            let args = [base, prints].concat();
            // Only the probe predicate is pinned here. What the compile
            // predicate answers for such a compile is a separate, pre-existing
            // gap (DECISION_QUEUE BOOTSTRAP-PROBE-OFF-1, "Unchanged and noted"),
            // left free to be fixed without flipping this test.
            if is_cargo_target_info_probe(&rustc_args(&args)) {
                misread.push(args);
            }
        }
    }
    assert!(misread.is_empty(), "real compiles read as probes: {misread:#?}");
}

/// Trust: the probe predicate admits Cargo's probe SHAPE and nothing wider (the
/// narrower, fail-closed rule taken in the review follow-up of
/// BOOTSTRAP-PROBE-OFF-1): a print kind Cargo does not send, even one that stops
/// compilation; a print to a file; a source-file input; another crate name; a
/// `--` boundary; a `--print=…` token that is another option's value; and a
/// `--print` with no kind. Each argv here was a probe to the old predicate.
#[test]
fn only_cargo_probe_shape_is_a_probe() {
    let misread = [
        // A stop-compilation kind outside Cargo's five, alone or beside them.
        &["-", "--crate-name", "___", "--print=target-libdir"][..],
        &["-", "--crate-name", "___", "--print=cfg", "--print", "target-list"],
        // A kind Cargo sends, but to a file.
        &["-", "--crate-name", "___", "--print=cfg=out.txt"],
        &["-", "--crate-name", "___", "--print", "cfg=out.txt"],
        // A source file, not stdin; `-o -` names an output, not an input.
        &["src/lib.rs", "--crate-name", "___", "--print=cfg"],
        &["src/lib.rs", "--crate-name", "___", "--print=cfg", "-o", "-"],
        // Another crate name, or none.
        &["-", "--crate-name", "core", "--print=cfg"],
        &["-", "--print=cfg"],
        // A positional boundary, even after the probe's own tokens.
        &["-", "--crate-name", "___", "--print=cfg", "--"],
        // `--cfg`'s value, not a print request: nothing here prints.
        &["-", "--crate-name", "___", "--cfg", "--print=cfg"],
        // A `--print` with no kind.
        &["-", "--crate-name", "___", "--print=cfg", "--print"],
        &["-", "--crate-name", "___", "--print="],
    ]
    .into_iter()
    .filter(|args| is_cargo_target_info_probe(&rustc_args(args)))
    .collect::<Vec<_>>();
    assert!(misread.is_empty(), "not Cargo's probe shape, read as probes: {misread:#?}");
}

/// Trust: the probe predicate reads the argv as rustc's getopts does, and
/// refuses what it cannot read as Cargo's shape (the second review of
/// BOOTSTRAP-PROBE-OFF-1). A short-option CLUSTER: getopts reads `-gL` as `-g
/// -L`, and that `-L` takes the next argument, so `-gL --print=cfg` prints
/// nothing and compiles a crate (measured with the installed `trustc`
/// `321aaeda7`: exit 0, `lib___.rlib` written). A help query in any spelling,
/// short or long, joined or split. A free argument after the input or after an
/// option, and an input after an option. Each argv here was a probe to the
/// predicate of `b4420ca8e7`.
#[test]
fn short_option_clusters_help_queries_and_late_inputs_are_not_probes() {
    let probe = ["-", "--crate-name", "___"];
    let misread = [
        // Clusters: the value-taking `-L` at the end takes `--print=cfg`.
        &["--crate-type", "rlib", "-gL", "--print=cfg"][..],
        &["-OL", "--print=cfg"],
        &["--print=cfg", "-vL", "--print=cfg"],
        // A cluster of flags only, and one with a value glued on: never Cargo's.
        &["--print=cfg", "-gO"],
        &["--print=cfg", "-gLnative=/x"],
        // Help queries, every level and spelling.
        &["--print=cfg", "--codegen", "help"],
        &["--print=cfg", "--codegen=help"],
        &["--print=cfg", "--warn", "help"],
        &["--print=cfg", "-A", "help"],
        &["--print=cfg", "--allow=help"],
        &["--print=cfg", "--force-warn", "help"],
        &["--print=cfg", "-Dhelp"],
        &["--print=cfg", "--deny", "help"],
        &["--print=cfg", "-F", "help"],
        &["--print=cfg", "--forbid=help"],
        // A second input after the options, or a second `-`.
        &["--print=cfg", "src/lib.rs"],
        &["--print=cfg", "-"],
    ]
    .into_iter()
    .map(|tail| [&probe[..], tail].concat())
    .chain([
        // The input after an option.
        vec!["--crate-name", "___", "-", "--print=cfg"],
        // A free argument between the input and the options.
        vec!["-", "src/lib.rs", "--crate-name", "___", "--print=cfg"],
    ])
    .filter(|args| is_cargo_target_info_probe(&rustc_args(args)))
    .collect::<Vec<_>>();
    assert!(misread.is_empty(), "not Cargo's probe shape, read as probes: {misread:#?}");
    // The shape Cargo sends behind one or two wrapper paths (bootstrap's tippy
    // runs `<shim> <tippy-driver> <rustc> - …`) is still a probe.
    for wrappers in [&[][..], &["/x/rustc"], &["/x/tippy-driver", "/x/rustc"]] {
        let args = [wrappers, &probe[..], &["--print=cfg", "-Wwarnings", "-Zinline-mir"]].concat();
        assert!(is_cargo_target_info_probe(&rustc_args(&args)), "{args:?}");
    }
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
    // A real Trust snapshot's compatibility alias uses the same
    // version-invariant transport; its adjacent Trust driver must exist.
    let (_payload, [snapshot_rustc, _]) = seed_snapshot_drivers();
    assert!(rustc_driver_supports_trust_no_verify(&snapshot_rustc));
    assert!(!rustc_driver_supports_trust_no_verify(&OsString::from("/opt/homebrew/bin/rustc")));
    assert!(!rustc_driver_supports_trust_no_verify(&OsString::from("/tmp/trustc-wrapper")));
}

#[test]
fn detects_targeted_drivers_that_support_trust_no_verify() {
    // Built stages understand the switch. Snapshot capability additionally
    // requires the Trust companion payload exercised below.
    for stage in ["stage1", "stage2", "stage3"] {
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
    // Every host-supported driver is target-supported; an unidentified
    // stage0 snapshot retains only the target environment transport.
    let unsupported = OsString::from("/opt/homebrew/bin/rustc");
    assert!(!targeted_rustc_supports_trust_no_verify(&unsupported));
    assert!(!rustc_driver_supports_trust_no_verify(&unsupported));

    // A canonical Trust-named stage0 is supported in both lanes. This matters
    // when local-rebuild auto-detection classifies the seed as stage1-capable:
    // build scripts and proc macros still run without an explicit --target.
    let (_payload, [stage0, trust_stage0]) = seed_snapshot_drivers();
    assert!(targeted_rustc_supports_trust_no_verify(&stage0));
    assert!(rustc_driver_supports_trust_no_verify(&stage0));

    assert!(targeted_rustc_supports_trust_no_verify(&trust_stage0));
    assert!(rustc_driver_supports_trust_no_verify(&trust_stage0));
}

#[test]
fn stage0_host_units_honor_bootstrap_marker_without_target_rustflags() {
    // Trust: builder::cargo always exports this marker, even at stage0. With
    // --target set on Cargo itself, none of RUSTFLAGS_BOOTSTRAP reaches these
    // host units. Exercise actual capability -> compile policy -> snapshot
    // finalization, starting with NO explicit verifier flag to rescue it.
    let marker = shim_utils::trust_bootstrap_shim_marker_enabled(Some(OsStr::new("1")));
    let (_fixture, bin) = trust_seed_snapshot_fixture();
    for spelling in ["rustc", "trustc"] {
        let driver = bin.join(spelling).into_os_string();
        for authored in [
            rustc_args(&["--crate-name", "build_script_build", "build.rs", "--crate-type=bin"]),
            rustc_args(&["--crate-name", "shlex", "src/lib.rs", "--crate-type=lib"]),
            rustc_args(&[
                "--crate-name",
                "fixture_macros",
                "src/lib.rs",
                "--crate-type=proc-macro",
            ]),
        ] {
            for authenticated_frontend in [false, true] {
                let requested =
                    shim_utils::cargo_test_no_verify_requested(marker, authenticated_frontend);
                let applies = trust_bootstrap_off_switch_applies(
                    false,
                    requested,
                    targeted_rustc_supports_trust_no_verify(&driver),
                    rustc_driver_supports_trust_no_verify(&driver),
                    targeted_rustc_is_built_stage(&driver),
                    &authored,
                    None,
                );
                assert_eq!(applies, !authenticated_frontend, "{driver:?}: {authored:?}");
                let mut args = authored.clone();
                let action = finalize_trust_verify_control(
                    &mut args,
                    false,
                    targeted_rustc_is_stage0_snapshot(&driver),
                    targeted_rustc_supports_trust_no_verify(&driver),
                    applies,
                );
                assert_eq!(
                    action,
                    if authenticated_frontend {
                        TrustVerifyEnvAction::Preserve
                    } else {
                        TrustVerifyEnvAction::SetOff
                    },
                    "{driver:?}: {args:?}",
                );
                assert_eq!(args, authored, "a snapshot must receive no vintage-specific argv flag");
            }
        }
    }
    // Stock driver and host query scope remain unchanged.
    let stock = OsString::from("/opt/homebrew/bin/rustc");
    let compile = rustc_args(&["--crate-name", "shlex", "src/lib.rs"]);
    assert!(!trust_bootstrap_off_switch_applies(
        false,
        true,
        targeted_rustc_supports_trust_no_verify(&stock),
        rustc_driver_supports_trust_no_verify(&stock),
        targeted_rustc_is_built_stage(&stock),
        &compile,
        None,
    ));
    let query = rustc_args(&["-", "--crate-name", "___", "--print=cfg"]);
    assert!(!trust_bootstrap_off_switch_applies(
        false,
        true,
        true,
        true,
        false,
        &query,
        Some("___")
    ));
}

#[test]
fn stage0_snapshot_discrimination_and_env_transport() {
    // The SEED snapshot: bootstrap-managed stage0, `rustc`-named. Its vintage
    // is the seed pin's, not this source tree's — the pinned 2026-07-13 seed
    // advertises only the retired `-Zno-trust-verify`, so handing it the
    // current argv spelling aborts the compile with `unknown unstable option`
    // (the fresh-machine wall this path exists to close).
    let seed = OsString::from("/checkout/build/aarch64-apple-darwin/stage0/bin/rustc");
    assert!(targeted_rustc_is_stage0_snapshot(&seed));
    // The seed ships its driver under BOTH names (`rustc` is a launcher for
    // its `trustc`), so the trustc-named seed driver is a snapshot too — the
    // stem-based exemption of exactly this path is what handed the pre-rename
    // seed the current argv spelling and walled the build.
    assert!(targeted_rustc_is_stage0_snapshot(&OsString::from(
        "/checkout/build/aarch64-apple-darwin/stage0/bin/trustc"
    )));
    // In-tree drivers are NEVER snapshots: their vintage matches this shim's
    // source by construction, so the canonical argv spelling stays theirs.
    for in_tree in [
        "/checkout/build/aarch64-apple-darwin/stage1/bin/rustc",
        "/checkout/build/host/stage2/bin/rustc",
        "/checkout/build/host/stage2/bin/trustc",
        "/usr/local/bin/trustc",
    ] {
        assert!(
            !targeted_rustc_is_stage0_snapshot(&OsString::from(in_tree)),
            "{in_tree} must not be classified a snapshot"
        );
    }

    // Snapshot finalize: every argv spelling is stripped — the driver may not
    // parse ANY spelling this tree knows — and the env transport is requested
    // exactly when a supported driver has an applicable compile.
    let mut args = vec![
        OsString::from("-Ztrust-verify=off"),
        OsString::from("--crate-name"),
        OsString::from("build_script_build"),
    ];
    assert!(finalize_trust_no_verify_snapshot(&mut args, true, true));
    assert!(
        !args.iter().any(|arg| arg.to_string_lossy().contains("trust-verify")),
        "no argv spelling may survive for a snapshot driver: {args:?}"
    );

    // THE HOSTFLAGS LANE — an explicit off-request still needs transport when
    // the shim's own add-path was not requested. The assembled args may carry
    // it through RUSTC_HOST_FLAGS. Stripping it without honoring it re-enables
    // batteries-on verification of the dep tree (the memchr wall), so the
    // stripped off-request must ride the env transport.
    let mut args = vec![OsString::from("-Ztrust-verify=off")];
    assert!(finalize_trust_no_verify_snapshot(&mut args, true, false));
    assert!(args.is_empty());
    // Same, in the split "-Z" "trust-verify=off" token shape.
    let mut args = vec![OsString::from("-Z"), OsString::from("trust-verify=off")];
    assert!(finalize_trust_no_verify_snapshot(&mut args, true, false));
    assert!(args.is_empty());

    // An `=on` request is NOT an off-request: stripped (unparseable by the
    // seed either way), and no env transport — verification was asked FOR.
    let mut args = vec![OsString::from("-Ztrust-verify=on")];
    assert!(!finalize_trust_no_verify_snapshot(&mut args, true, false));
    assert!(args.is_empty());

    // No off-request anywhere and not applicable => no env transport.
    let mut args = vec![OsString::from("--crate-name"), OsString::from("x")];
    assert!(!finalize_trust_no_verify_snapshot(&mut args, true, false));

    // Positional args after `--` are never options: an off-spelling there
    // does not count as a request (mirrors strip/canonicalize's boundary).
    let mut args = vec![OsString::from("--"), OsString::from("-Ztrust-verify=off")];
    assert!(!finalize_trust_no_verify_snapshot(&mut args, true, false));

    // The helper's unsupported-driver contract: strip the option without
    // requesting environment transport. The composed dispatch control covers
    // actual paths, including a snapshot-named stock driver (which ignores env).
    let mut args = vec![OsString::from("-Ztrust-verify=off")];
    assert!(!finalize_trust_no_verify_snapshot(&mut args, false, true));
    assert!(args.is_empty());
}

#[test]
fn verifier_control_dispatches_actual_stage0_to_env_transport() {
    // Regression: snapshot finalization was accidentally nested under the
    // library verification opt-in. That opt-in deliberately excludes stage0,
    // so the branch was unreachable and the July seed received the current
    // spelling it cannot parse.
    let mut snapshot = rustc_args(&["-Ztrust-verify=off", "--crate-name", "build_script_build"]);
    assert_eq!(
        finalize_trust_verify_control(&mut snapshot, false, true, true, false),
        TrustVerifyEnvAction::SetOff
    );
    assert_eq!(snapshot, rustc_args(&["--crate-name", "build_script_build"]));

    // A current in-tree driver keeps the canonical argv control and does not
    // need the compatibility environment transport.
    let mut staged = rustc_args(&["--crate-name", "core"]);
    assert_eq!(
        finalize_trust_verify_control(&mut staged, false, false, true, true),
        TrustVerifyEnvAction::Preserve
    );
    assert_eq!(staged.last(), Some(&OsString::from("-Ztrust-verify=off")));

    // An explicitly selected library unit is the separate on-lane: scrub any
    // inherited off transport and leave exactly one current on-switch.
    let mut verified = rustc_args(&["-Ztrust-verify=off", "--crate-name", "core"]);
    assert_eq!(
        finalize_trust_verify_control(&mut verified, true, false, true, false),
        TrustVerifyEnvAction::Remove
    );
    assert_eq!(verified.iter().filter(|arg| **arg == "-Ztrust-verify=on").count(), 1);
    assert!(!verified.iter().any(|arg| arg == "-Ztrust-verify=off"));
}

#[test]
fn retired_spelling_is_normalized_and_never_forwarded() {
    // The seed's targo injects the retired `-Zno-trust-verify` into the rustc
    // invocations it drives (its native lane predates the 576db732cd rename),
    // and a CURRENT driver rejects that name outright — the exact
    // seed-targo/stage1-rustc deadlock from the stage2 blocker diagnosis.
    // For a current driver, canonicalize must NORMALIZE it: strip the retired
    // spelling, insert the one spelling the driver parses.
    let mut args = vec![
        OsString::from("-Zno-trust-verify"),
        OsString::from("--crate-name"),
        OsString::from("core"),
    ];
    canonicalize_trust_no_verify(&mut args);
    assert_eq!(args.iter().filter(|arg| **arg == "-Ztrust-verify=off").count(), 1);
    assert!(
        !args.iter().any(|arg| arg.to_string_lossy().contains("no-trust-verify")),
        "the retired spelling must never survive normalization: {args:?}"
    );

    // For a SNAPSHOT driver, a retired off-request rides the env transport
    // like any other off-request (bare and `=yes` forms are truthy)...
    for retired in ["-Zno-trust-verify", "-Zno-trust-verify=yes"] {
        let mut args = vec![OsString::from(retired)];
        assert!(
            finalize_trust_no_verify_snapshot(&mut args, true, false),
            "{retired} must ride the transport"
        );
        assert!(args.is_empty());
    }
    // ...and the split token shape too.
    let mut args = vec![OsString::from("-Z"), OsString::from("no-trust-verify")];
    assert!(finalize_trust_no_verify_snapshot(&mut args, true, false));
    assert!(args.is_empty());

    // `=no` is not an off-request — but it IS still stripped, because no
    // current-vintage driver parses the name at all.
    let mut args = vec![OsString::from("-Zno-trust-verify=no")];
    assert!(!finalize_trust_no_verify_snapshot(&mut args, true, false));
    assert!(args.is_empty());
}

/// FAIL-OPEN PARSING REGRESSION. The off-request test used to accept EVERY
/// value of the retired spelling except the literal `no`, so `=false`, `=0` and
/// `=off` all silently meant "verification off" — broad truthy parsing inside a
/// function whose whole job is exactness, and the opposite convention from
/// `trust_bootstrap_shim_marker_enabled`, which accepts only `1`.
///
/// The exact set is the retired option's own: `no_trust_verify` was
/// `bool = (false, parse_bool, [TRACKED], ...)`
/// (`576db732cd^:compiler/rustc_session/src/options.rs:2788`).
#[test]
fn the_retired_spelling_is_parsed_exactly_as_its_own_parse_bool() {
    // TRUE (= do not verify): the bare form and `parse_bool`'s truthy set. Bare
    // and `=yes` are the spellings the retired ecosystem actually emitted
    // (`576db732cd^:src/tools/compiletest/src/directives.rs:458-463`).
    for off in ["-Zno-trust-verify", "-Zno-trust-verify=y", "-Zno-trust-verify=yes"] {
        let mut args = vec![OsString::from(off)];
        assert!(
            finalize_trust_no_verify_snapshot(&mut args, true, false),
            "{off} is an off-request"
        );
    }
    for off in ["-Zno-trust-verify=on", "-Zno-trust-verify=true"] {
        let mut args = vec![OsString::from(off)];
        assert!(
            finalize_trust_no_verify_snapshot(&mut args, true, false),
            "{off} is an off-request"
        );
    }

    // FALSE (= DO verify): `parse_bool`'s falsy set. Note the double negative —
    // `no-trust-verify=off` sets `no_trust_verify = false`, i.e. verification
    // ON. `=off`, `=false` and `=n` used to be read as "verification off".
    for on in [
        "-Zno-trust-verify=n",
        "-Zno-trust-verify=no",
        "-Zno-trust-verify=off",
        "-Zno-trust-verify=false",
    ] {
        let mut args = vec![OsString::from(on)];
        assert!(
            !finalize_trust_no_verify_snapshot(&mut args, true, false),
            "{on} requests verification ON, not off"
        );
        assert!(args.is_empty(), "{on} must still be stripped");
    }

    // Outside `parse_bool`'s two sets the retired driver would have hard-failed
    // on the option. Fail closed: not an off-request, so the unit stays
    // verified and fails loudly rather than going silently unverified.
    for bogus in [
        "-Zno-trust-verify=0",
        "-Zno-trust-verify=1",
        "-Zno-trust-verify=",
        "-Zno-trust-verify=YES",
        "-Zno-trust-verify=nope",
    ] {
        let mut args = vec![OsString::from(bogus)];
        assert!(
            !finalize_trust_no_verify_snapshot(&mut args, true, false),
            "{bogus} is not a value the retired option ever accepted"
        );
    }

    // The CURRENT spelling is unchanged and equally exact: only `off`.
    for current in ["-Ztrust-verify=off", "-Ztrust_verify=off"] {
        let mut args = vec![OsString::from(current)];
        assert!(finalize_trust_no_verify_snapshot(&mut args, true, false), "{current}");
    }
    for current in ["-Ztrust-verify=on", "-Ztrust-verify", "-Ztrust-verify=0"] {
        let mut args = vec![OsString::from(current)];
        assert!(!finalize_trust_no_verify_snapshot(&mut args, true, false), "{current}");
    }
}

// Trust: the canonical Session's Trust-named seed reaches host libraries,
// build scripts and proc macros without target rustflags. The marker uses the
// vintage-independent transport, while stock/verified/query controls stay out.
#[test]
fn stage0_host_native_policy_preserves_queries_frontends_and_stock_drivers() {
    let seed = OsString::from("/checkout/build/host/stage0/bin/trustc");
    let stock = OsString::from("/external/bin/rustc");
    for driver in [&seed, &stock] {
        for (args, compile) in [
            (rustc_args(&["--crate-name", "dep", "dep.rs", "--crate-type=lib"]), true),
            (rustc_args(&["--crate-name", "build_script_build", "build.rs"]), true),
            (rustc_args(&["--crate-name", "derive", "lib.rs", "--crate-type=proc-macro"]), true),
            (rustc_args(&["--print=cfg"]), false),
            (rustc_args(&["-vV"]), false),
        ] {
            for frontend in [false, true] {
                let supports = rustc_driver_supports_trust_no_verify(driver);
                let requested = shim_utils::cargo_test_no_verify_requested(true, frontend);
                let applies = trust_bootstrap_off_switch_applies(
                    false,
                    requested,
                    targeted_rustc_supports_trust_no_verify(driver),
                    supports,
                    targeted_rustc_is_built_stage(driver),
                    &args,
                    None,
                );
                let mut forwarded = args.clone();
                let action = finalize_trust_verify_control(
                    &mut forwarded,
                    false,
                    targeted_rustc_is_stage0_snapshot(driver),
                    targeted_rustc_supports_trust_no_verify(driver),
                    applies,
                );
                assert_eq!(
                    action,
                    if driver == &seed && compile && !frontend {
                        TrustVerifyEnvAction::SetOff
                    } else {
                        TrustVerifyEnvAction::Preserve
                    }
                );
                assert_eq!(
                    forwarded, args,
                    "a snapshot must not receive either vintage's argv flag"
                );
            }
        }
    }
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
    // The preliminary capability filter preserves this request for a known
    // Trust-native driver. Snapshot finalization subsequently strips the argv
    // spelling and transports the request through the environment instead.
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
    let mut valued =
        rustc_args(&["-Ztrust_verify=on", "-Z", "trust-verify=off", "--", "-Ztrust-verify=off"]);
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

// ---------------------------------------------------------------------------
// The per-unit `library/` verification opt-in. Bootstrap authorizes the cargo
// INVOCATION; the shim authorizes the UNIT. Both halves have to say yes.
// ---------------------------------------------------------------------------

/// A stage>=1 in-tree driver, a real targeted compile of `core`, driven by
/// bootstrap, with `core` in the authorized list.
fn library_verify_case() -> (Vec<OsString>, OsString) {
    (
        rustc_args(&[
            "-Ztrust-verify=off",
            "--crate-name",
            "core",
            "library/core/src/lib.rs",
            "--crate-type=lib",
            "--target",
            "aarch64-apple-darwin",
        ]),
        OsString::from("/checkout/build/aarch64-apple-darwin/stage2/bin/trustc"),
    )
}

#[test]
fn the_library_opt_in_verifies_exactly_the_named_unit() {
    let (args, driver) = library_verify_case();
    let staged = targeted_rustc_supports_trust_no_verify(&driver)
        && !targeted_rustc_is_stage0_snapshot(&driver);
    assert!(staged);

    assert!(trust_bootstrap_verify_unit_applies(
        true,
        true,
        false,
        Some(OsStr::new("core")),
        staged,
        &args,
        Some("core"),
    ));
    assert!(trust_bootstrap_verify_unit_applies(
        true,
        true,
        false,
        Some(OsStr::new("core,alloc,std")),
        staged,
        &args,
        Some("alloc"),
    ));
}

/// The reason this lane is per UNIT and not per invocation: the same
/// `Mode::Std` cargo invocation that compiles `core` also compiles std's
/// third-party dependency graph, and those must keep today's off-switch.
#[test]
fn the_library_opt_in_leaves_std_s_dependency_graph_alone() {
    let (args, driver) = library_verify_case();
    let staged = targeted_rustc_supports_trust_no_verify(&driver)
        && !targeted_rustc_is_stage0_snapshot(&driver);

    for dependency in ["compiler_builtins", "libc", "hashbrown", "memchr", "object", "unwind"] {
        assert!(
            !trust_bootstrap_verify_unit_applies(
                true,
                true,
                false,
                Some(OsStr::new("core,alloc,std")),
                staged,
                &args,
                Some(dependency),
            ),
            "{dependency} was swept into the library opt-in"
        );
    }
}

/// Everything else about the invocation is a refusal, and each one is a
/// separate way the lane could have failed open.
#[test]
fn the_library_opt_in_is_refused_outside_its_exact_lane() {
    let (args, driver) = library_verify_case();
    let seed = OsString::from("/checkout/build/aarch64-apple-darwin/stage0/bin/trustc");
    let stock = OsString::from("/opt/homebrew/bin/rustc");
    let staged = |driver: &OsString| {
        targeted_rustc_supports_trust_no_verify(driver)
            && !targeted_rustc_is_stage0_snapshot(driver)
    };
    let units = Some(OsStr::new("core"));

    let applies = |has_target, marker, targo, units, staged, crate_name| {
        trust_bootstrap_verify_unit_applies(
            has_target, marker, targo, units, staged, &args, crate_name,
        )
    };

    // Not driven by bootstrap: an ambient value in the environment is inert.
    assert!(!applies(true, false, false, units, staged(&driver), Some("core")));
    // An authenticated Targo frontend owns its own argv, in either direction.
    assert!(!applies(true, true, true, units, staged(&driver), Some("core")));
    // Host units (build scripts, proc macros) run on the build compiler.
    assert!(!applies(false, true, false, units, staged(&driver), Some("core")));
    // A stage0 SEED must never be asked to verify: its vintage is the pin's.
    assert!(!staged(&seed));
    assert!(!applies(true, true, false, units, staged(&seed), Some("core")));
    // A stock upstream driver has no verifier at all.
    assert!(!staged(&stock));
    assert!(!applies(true, true, false, units, staged(&stock), Some("core")));
    // Channel unset, empty, or naming a different unit.
    assert!(!applies(true, true, false, None, staged(&driver), Some("core")));
    assert!(!applies(true, true, false, Some(OsStr::new("")), staged(&driver), Some("core")));
    assert!(!applies(true, true, false, Some(OsStr::new("alloc")), staged(&driver), Some("core")));
    // No crate name to match against.
    assert!(!applies(true, true, false, units, staged(&driver), None));
}

/// A `-vV`/`--print` probe is not a compilation and must not be rewritten.
#[test]
fn the_library_opt_in_ignores_cargo_probes() {
    let driver = OsString::from("/checkout/build/aarch64-apple-darwin/stage2/bin/trustc");
    let staged = targeted_rustc_supports_trust_no_verify(&driver)
        && !targeted_rustc_is_stage0_snapshot(&driver);

    for probe in [
        rustc_args(&["-vV"]),
        rustc_args(&["--print", "sysroot", "--target", "aarch64-apple-darwin"]),
    ] {
        assert!(!trust_bootstrap_verify_unit_applies(
            true,
            true,
            false,
            Some(OsStr::new("core")),
            staged,
            &probe,
            Some("core"),
        ));
    }
}

#[test]
fn unit_membership_normalizes_the_cargo_crate_name_spelling() {
    assert!(trust_bootstrap_verify_unit_requested(
        Some(OsStr::new("panic_abort")),
        Some("panic-abort")
    ));
    assert!(trust_bootstrap_verify_unit_requested(
        Some(OsStr::new(" core , alloc ")),
        Some("alloc")
    ));
    assert!(!trust_bootstrap_verify_unit_requested(Some(OsStr::new("core")), Some("coretests")));
    assert!(!trust_bootstrap_verify_unit_requested(Some(OsStr::new("core")), Some("")));
    assert!(!trust_bootstrap_verify_unit_requested(None, Some("core")));
    assert!(!trust_bootstrap_verify_unit_requested(Some(OsStr::new("core")), None));
}

/// The unit arrives carrying bootstrap's invocation-wide off-switch (rustflags
/// reach the shim as argv). It must leave with exactly one verifier control, and
/// that control must be `on`.
#[test]
fn a_verified_library_unit_gets_one_canonical_on_switch() {
    for authored in [
        rustc_args(&["-Ztrust-verify=off", "--crate-name", "core", "src/lib.rs"]),
        rustc_args(&["-Z", "trust-verify=off", "-Ztrust_verify=off", "--crate-name", "core"]),
        rustc_args(&["-Zno-trust-verify", "--crate-name", "core", "src/lib.rs"]),
    ] {
        let mut args = authored;
        canonicalize_trust_verify_on(&mut args);

        assert_eq!(
            args.iter().filter(|arg| *arg == "-Ztrust-verify=on").count(),
            1,
            "library unit did not receive one canonical on-switch: {args:?}"
        );
        assert!(
            !args.iter().any(|arg| {
                let arg = arg.to_string_lossy();
                arg.contains("trust-verify=off")
                    || arg.contains("trust_verify=off")
                    || arg.contains("no-trust-verify")
            }),
            "an off-switch survived beside the on-switch: {args:?}"
        );
    }
}

/// Positional arguments after `--` are program arguments, never compiler
/// options; the on-switch goes before the boundary, exactly like the off-switch.
#[test]
fn the_on_switch_respects_the_positional_boundary() {
    let mut args = rustc_args(&["--crate-name", "core", "src/lib.rs", "--", "-Ztrust-verify=off"]);
    canonicalize_trust_verify_on(&mut args);

    let boundary = args.iter().position(|arg| arg == "--").unwrap();
    let on = args.iter().position(|arg| arg == "-Ztrust-verify=on").unwrap();
    assert!(on < boundary, "{args:?}");
    assert_eq!(args.last(), Some(&OsString::from("-Ztrust-verify=off")), "{args:?}");
}

/// The lane's compiles are UNAUTHENTICATED and UNSCOPED by construction:
/// exactly `-Ztrust-verify=on`, and nothing else from the verifier surface.
/// A proof-session identity would masquerade as the authenticated self-verify
/// lane (`self-verify-<nonce>` sessions, `targo-trust/src/self_verify_cli.rs`);
/// a policy control would silently change what the lane's green means. Every
/// spelling and token shape is refused, and the refusal carries the fix.
#[test]
fn a_verified_library_unit_refuses_identity_and_policy_controls() {
    for control in [
        "-Ztrust-verify-session=self-verify-1-2-3",
        "-Ztrust-verify-session=bootstrap-library-core",
        "-Ztrust_verify_session=x",
        "-Ztrust-verify-package-name=core",
        "-Ztrust-verify-crate-role=primary",
        "-Ztrust-policy=advisory",
        "-Ztrust_policy=advisory",
        "-Ztrust-verify-level=0",
        "-Ztrust-verify-full",
    ] {
        // Joined shape.
        let args =
            rustc_args(&["-Ztrust-verify=off", control, "--crate-name", "core", "src/lib.rs"]);
        let message = trust_bootstrap_verify_unit_argv_refusal(&args)
            .unwrap_or_else(|| panic!("lane accepted {control}"));
        assert!(message.contains("refuses the verifier control"), "{message}");
        assert!(message.contains("TRUST_BOOTSTRAP_VERIFY_LIBRARY"), "{message}");

        // Split shape: `-Z` and the option as separate tokens.
        let option = control.strip_prefix("-Z").unwrap();
        let args = rustc_args(&["-Z", option, "--crate-name", "core", "src/lib.rs"]);
        assert!(
            trust_bootstrap_verify_unit_argv_refusal(&args).is_some(),
            "lane accepted the split shape of {control}"
        );
    }
}

/// The refusal fires on the verifier surface only: the lane's own off-switch
/// (which `canonicalize_trust_verify_on` replaces), ordinary flags, and
/// positional arguments after `--` are all left alone.
#[test]
fn the_lane_argv_refusal_leaves_the_ordinary_argv_alone() {
    let (args, _) = library_verify_case();
    assert_eq!(trust_bootstrap_verify_unit_argv_refusal(&args), None);

    let args = rustc_args(&[
        "-Ztrust-verify=off",
        "-Zalways-encode-mir",
        "--cfg",
        "feature=\"panic_immediate_abort\"",
        "--crate-name",
        "core",
        "src/lib.rs",
        "--",
        "-Ztrust-policy=advisory",
    ]);
    assert_eq!(
        trust_bootstrap_verify_unit_argv_refusal(&args),
        None,
        "a positional argument after `--` is not a compiler option"
    );
}

/// The wired half: `finalize_trust_verify_control` refuses before it
/// canonicalizes, so a lane unit can never leave the shim carrying both the
/// on-switch and a session identity.
#[test]
#[should_panic(expected = "refuses the verifier control")]
fn finalize_refuses_a_lane_unit_that_carries_a_session_identity() {
    let mut args = rustc_args(&[
        "-Ztrust-verify=off",
        "-Ztrust-verify-session=self-verify-1-2-3",
        "--crate-name",
        "core",
        "src/lib.rs",
    ]);
    finalize_trust_verify_control(&mut args, true, false, true, false);
}

#[cfg(unix)]
#[test]
fn fixture_signal_guard_preserves_ordinary_bootstrap_policy() {
    use std::os::unix::process::ExitStatusExt;
    assert_eq!(
        super::cargo_fixture_termination_signal(
            false,
            std::process::ExitStatus::from_raw(libc::SIGTERM)
        ),
        None
    );
    assert_eq!(
        super::cargo_fixture_termination_signal(true, std::process::ExitStatus::from_raw(7 << 8)),
        None
    );
    assert_eq!(
        super::cargo_fixture_termination_signal(
            true,
            std::process::ExitStatus::from_raw(libc::SIGTERM)
        ),
        Some(libc::SIGTERM)
    );
}

#[cfg(unix)]
#[test]
fn fixture_signal_child() {
    let Ok(mode) = std::env::var("TRUST_TEST_FIXTURE_SIGNAL_MODE") else { return };
    // SAFETY: this is an isolated child which deliberately terminates below.
    unsafe {
        if mode == "ignored" {
            libc::signal(libc::SIGTERM, libc::SIG_IGN);
        }
        if mode == "blocked" {
            let mut mask: libc::sigset_t = std::mem::zeroed();
            libc::sigemptyset(&mut mask);
            libc::sigaddset(&mut mask, libc::SIGTERM);
            libc::pthread_sigmask(libc::SIG_BLOCK, &mask, std::ptr::null_mut());
        }
    }
    super::forward_cargo_fixture_signal(libc::SIGTERM);
}

#[cfg(unix)]
#[test]
fn fixture_signal_forwarding_resets_and_unblocks_on_the_terminating_thread() {
    use std::os::unix::process::ExitStatusExt;
    for mode in ["plain", "ignored", "blocked"] {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "tests::fixture_signal_child", "--nocapture"])
            .env("TRUST_TEST_FIXTURE_SIGNAL_MODE", mode)
            .output()
            .unwrap();
        assert_eq!(output.status.signal(), Some(libc::SIGTERM), "{mode}: {output:?}");
    }
}
