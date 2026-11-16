//! Trust (F3, landed 2026-09-30): the derived-MIR storage rule's mutation control, through the
//! driver binary, under the driver's fence.
//!
//! `mir_differential::compare_derived` extracts built and derived MIR into the verifier's model
//! before comparing them, and that extraction keeps an `Assert` message's kind but drops its
//! operands. What reads them is `mir_storage_dead_use`, rustc's `-Zlint-mir` storage rule over the
//! REAL derived `mir::Body`. `-Ztrust-test-mutate-derived-assert-msg` (tracked, test-only, in
//! `to_mir.rs`) plants a storage-dead message operand in that derived body.
//!
//! The driver fences the control (`trust_option_domain_error`): it needs `-Ztrust-verify=off
//! -Ztrust-ir-lower -Ztrust-ir-flip=no` and no `-Ztrust-dump` sink, so a report written from a
//! mutated differential can never exist. That leaves its log line as its only observable; the
//! rule itself is executed on real compiler-built bodies, planted and unplanted, by the cited
//! in-process test crates/trust-mir-extract/tests/derived_assert_msg_storage_rule.rs. This recipe
//! pins, through the binary:
//!   1. the unmutated control: `chain2` and `chain1` are Agreed with an exact marker channel;
//!   2. the fence: the control is refused with a dump sink, with the flip on, with verification
//!      on, and without direct lowering;
//!   3. the admitted posture: the compile succeeds, and exactly one operand (chain2's) is planted.

use run_make_support::{CompletedProcess, cmd, rfs, rustc_path, serde_json};

const MUTATE: &str = "-Ztrust-test-mutate-derived-assert-msg";

/// Compile chain.rs with `extra`; `ok` says whether the driver must accept the command line.
fn rustc(extra: &[&str], ok: bool) -> CompletedProcess {
    let mut rustc = cmd(rustc_path());
    rustc.args([
        "chain.rs",
        "--edition=2021",
        "--crate-type=lib",
        "--crate-name=chain",
        "-Copt-level=1",
        "-Coverflow-checks=on",
        "-Cdebuginfo=0",
        "-Zthreads=1",
    ]);
    rustc.args(extra);
    rustc.env("RUSTC_LOG", "trust_thir_lower::to_mir=info");
    if ok { rustc.run() } else { rustc.run_fail() }
}

fn derived<'a>(report: &'a serde_json::Value, name: &str) -> &'a serde_json::Value {
    let rows: Vec<_> =
        report["bodies"].as_array().unwrap().iter().filter(|r| r["def_path"] == name).collect();
    assert_eq!(rows.len(), 1, "missing or duplicate coverage row for {name}");
    &rows[0]["differentials"]["derived_mir"]
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return; // Stock rustc has no Trust-IR differential.
    }
    let burn_in = ["-Ztrust-verify=off", "-Ztrust-ir-lower=on", "-Ztrust-ir-flip=no"];

    // 1. The unmutated control, with the coverage report.
    let mut args = burn_in.to_vec();
    args.extend(["-Ztrust-dump=ir:control", "--out-dir", "control-out"]);
    let log = rustc(&args, true).stderr_utf8();
    assert!(!log.contains("TEST MUTATION"), "the control mutated without being armed:\n{log}");
    let control: serde_json::Value =
        serde_json::from_slice(&rfs::read("control/chain.coverage.json")).unwrap();
    for (name, lines) in [("chain2", 4), ("chain1", 2)] {
        let row = derived(&control, name);
        assert_eq!(row["verdict"], "agreed", "{name}: {row}");
        assert_eq!(row["markers_exact"], true, "{name}: {row}");
        assert_eq!(row["markers_detail"], format!("{lines} marker line(s) identical"), "{name}");
    }

    // 2. The fence.
    let refused = |extra: &[&str], message: &str| {
        let mut args = extra.to_vec();
        args.extend([MUTATE, "--out-dir", "refused-out"]);
        let out = rustc(&args, false);
        out.assert_stderr_contains(message);
        assert!(!out.stderr_utf8().contains("TEST MUTATION"), "refused, yet it mutated");
    };
    refused(
        &["-Ztrust-verify=off", "-Ztrust-ir-lower=on", "-Ztrust-ir-flip=no", "-Ztrust-dump=ir:dump"],
        "cannot be combined with any -Ztrust-dump artifact sink",
    );
    assert!(!std::path::Path::new("dump/chain.coverage.json").exists(), "a report was written");
    refused(&["-Ztrust-verify=off", "-Ztrust-ir-lower=on"], "requires -Ztrust-ir-flip=no");
    refused(&["-Ztrust-ir-lower=on", "-Ztrust-ir-flip=no"], "requires -Ztrust-verify=off");
    refused(&["-Ztrust-verify=off", "-Ztrust-ir-flip=no"], "requires -Ztrust-verify=off");

    // 3. The admitted posture: no artifact, one planted operand, chain2's.
    let mut args = burn_in.to_vec();
    args.extend([MUTATE, "--out-dir", "mutated-out"]);
    let log = rustc(&args, true).stderr_utf8();
    let planted: Vec<&str> = log.lines().filter(|l| l.contains("TEST MUTATION")).collect();
    assert_eq!(planted.len(), 1, "exactly one operand repointed:\n{log}");
    assert!(planted[0].contains("chain2"), "the repointed operand is chain2's:\n{log}");
}
