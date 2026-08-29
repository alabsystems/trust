use std::ffi::{OsStr, OsString};
use std::path::Path;

use super::shared_helpers::{
    canonicalize_trust_no_verify, canonicalize_trust_verify_on, finalize_trust_no_verify,
    finalize_trust_no_verify_snapshot, strip_trust_no_verify,
    trust_bootstrap_verify_unit_requested,
};
use super::{
    ArgFileCommand, TrustVerifyEnvAction, enforce_trust_no_verify_capability,
    finalize_trust_verify_control, is_lint_driver_arg, rustc_driver_supports_trust_no_verify,
    should_apply_compiler_lint_flags, should_strip_cargo_rustc_arg,
    targeted_rustc_is_stage0_snapshot, targeted_rustc_supports_trust_no_verify,
    trust_bootstrap_no_verify_applies, trust_bootstrap_verify_unit_applies,
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

    // THE HOSTFLAGS LANE — the build-script case that walled every fresh
    // build. `trust_bootstrap_no_verify_applies` answers false for a seed on
    // a host unit (its driver gate deliberately excludes stage0), but the
    // builder already materialized the off-switch in the args via
    // RUSTC_HOST_FLAGS. Stripping it without honoring it re-enables
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

    // Unsupported (stock upstream parked in a stage0-named dir) => stripped,
    // no env transport. Stock ignores the env anyway; not setting it keeps
    // the invariant clean.
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
