//@ ignore-cross-compile (runs the doctest binary)
//! trustdoc is an evidence-deauthorized frontend: it produces no verification
//! evidence, so it must decide Trust options on the EFFECTIVE (last-wins, fully
//! parsed) configuration rather than on each `-Ztrust-*` occurrence. A project's
//! committed verification posture (ay's `.cargo/config.toml` rustflags) followed
//! by the `-Ztrust-verify=off` Targo appends for doc and doctest passes resolves to
//! verification OFF, so every posture selector in it is inert here and is accepted
//! and neutralized — in documentation mode AND in `--test` doctest mode, whose
//! doctest binaries are then built by the canonical `trustc` with the same flags.
//! Controls whose effect does not depend on verification (artifact sinks, session
//! identity, codegen and measurement controls) and an effective explicit
//! `-Ztrust-verify=on` stay refused.
//!
//! Measured on seal 7d5533b2: every shape in `ACCEPTED` after the first was refused
//! with "compiler frontend rejects semantic, evidence, or backend control".

use std::path::Path;

use run_make_support::{rfs, rustc, rustdoc};

/// ay's committed verification posture, verbatim.
const AY_POSTURE: [&str; 6] = [
    "-Ztrust-verify=on",
    "-Ztrust-policy=certify",
    "-Ztrust-verify-level=2",
    "-Ztrust-verify-profile=unix_hardened",
    "-Ztrust-verify-include-dependencies=yes",
    "-Ztrust-ir-lower=strict",
];

fn owned(args: &[&str]) -> Vec<String> {
    args.iter().map(|arg| arg.to_string()).collect()
}

fn ay_then(extra: &[&str]) -> Vec<String> {
    let mut argv = owned(&AY_POSTURE);
    argv.push("-Ztrust-verify=off".to_string());
    argv.extend(owned(extra));
    argv
}

fn main() {
    // The doctest links against the crate, built by the canonical compiler.
    rustc().input("lib.rs").crate_type("rlib").crate_name("posture").run();
    let rlib = Path::new("libposture.rlib");
    assert!(rlib.is_file());

    // Proof bytes may only be written by an ACTIVE verification; the root is accepted
    // and neutralized, so it must never come into existence.
    let proof_root = std::env::current_dir().unwrap().join("must-not-publish-proofs");
    let proof_root_flag = format!("-Ztrust-proof-artifact-root={}", proof_root.display());
    let accepted: Vec<(&str, Vec<String>)> = vec![
        ("plain off-switch", owned(&["-Ztrust-verify=off"])),
        ("verification on, then off", owned(&["-Ztrust-verify=on", "-Ztrust-verify=off"])),
        ("certify policy, then off", owned(&["-Ztrust-policy=certify", "-Ztrust-verify=off"])),
        ("proof level, then off", owned(&["-Ztrust-verify-level=2", "-Ztrust-verify=off"])),
        ("strict lowering, then off", owned(&["-Ztrust-ir-lower=strict", "-Ztrust-verify=off"])),
        ("ay's posture, then off", ay_then(&[])),
        (
            "every other verification selector, then off",
            ay_then(&[
                "-Ztrust-verify-output=json",
                "-Ztrust-memory-notes",
                proof_root_flag.as_str(),
                "-Ztrust-verify-timeout-ms=1",
                "-Ztrust-verify-worker-threads=1",
                "-Ztrust-verify-function-budget-ms=1",
                "-Ztrust-verify-function-budget-steps=1",
                "-Ztrust-verify-effort=1",
                "-Ztrust-no-adapter-yield",
                "-Ztrust-no-r1",
                "-Ztrust-bundle-foreign-crate=posture",
                "-Ztrust-ir-flip=no",
                "-Ztrust-instance-flip=no",
            ]),
        ),
    ];
    for (index, (label, shape)) in accepted.iter().enumerate() {
        let out_dir = format!("doc-{index}");
        rustdoc().input("lib.rs").crate_name("posture").out_dir(&out_dir).args(shape).run();
        assert!(
            Path::new(&out_dir).join("posture").join("fn.one.html").is_file(),
            "{label}: trustdoc accepted the posture but documented nothing",
        );

        let doctest = rustdoc()
            .input("lib.rs")
            .crate_name("posture")
            .arg("--test")
            .extern_("posture", rlib)
            .args(shape)
            .run();
        let stdout = doctest.stdout_utf8();
        assert!(
            stdout.contains("test result: ok. 1 passed"),
            "{label}: the doctest did not run and pass:\n{stdout}",
        );
    }
    assert!(!proof_root.exists(), "a neutralized proof root received proof bytes");

    let refused: Vec<(&str, Vec<String>, &str)> = vec![
        ("ay's posture with verification left on", owned(&AY_POSTURE), "-Ztrust-verify"),
        (
            "an off-switch overridden by a later `on`",
            owned(&["-Ztrust-verify=off", "-Ztrust-verify=on"]),
            "-Ztrust-verify",
        ),
        ("a TrustIR artifact sink", ay_then(&["-Ztrust-dump=ir:trust-ir-dump"]), "-Ztrust-dump"),
        (
            "a census artifact sink",
            ay_then(&["-Ztrust-body-census=body-census.jsonl"]),
            "-Ztrust-body-census",
        ),
        (
            "a diagnostic call observation selector",
            ay_then(&["-Ztrust-body-census-calls"]),
            "-Ztrust-body-census-calls",
        ),
        (
            "an authenticated session identity",
            ay_then(&["-Ztrust-verify-session=posture-session"]),
            "-Ztrust-verify-session",
        ),
        (
            "a certified-monitor selector",
            ay_then(&["-Ztrust-targo-test-monitor"]),
            "-Ztrust-targo-test-monitor",
        ),
        (
            "a trust-cg codegen control",
            ay_then(&["-Ztrust-cg-output-gate=off"]),
            "-Ztrust-cg-output-gate",
        ),
        (
            "an adversarial burn-in control",
            ay_then(&["-Ztrust-sat-perturb=enum-reshape"]),
            "-Ztrust-sat-perturb",
        ),
        ("the typeck-witness lane", ay_then(&["-Ztrust-witness=off"]), "-Ztrust-witness"),
    ];
    for (label, shape, option) in &refused {
        for doctest_mode in [false, true] {
            let mut invocation = rustdoc();
            invocation.input("lib.rs").crate_name("posture").out_dir("doc-refused").args(shape);
            if doctest_mode {
                invocation.arg("--test").extern_("posture", rlib);
            }
            invocation
                .run_fail()
                .assert_stderr_contains("compiler frontend rejects")
                .assert_stderr_contains(format!("`{option}`"));
            assert!(
                !Path::new("doc-refused").join("posture").exists(),
                "{label} (doctest mode: {doctest_mode}): refused, yet documented",
            );
        }
    }
    assert!(!Path::new("trust-ir-dump").exists(), "a refused IR sink was created");
    assert!(!Path::new("body-census.jsonl").exists(), "a refused census was written");

    // The canonical compiler that builds the doctests accepts the same effective
    // configuration: the frontends now agree with it on what `off` means.
    rfs::create_dir("canonical");
    rustc()
        .input("lib.rs")
        .crate_type("rlib")
        .crate_name("posture")
        .out_dir("canonical")
        .args(ay_then(&[]))
        .run();
}
