//! Trust WS7.12 (F-114, row `a.f1.codegen.rust_control.strict_gate`): the
//! Part A F1 control compiles through the trust-ir codegen frontend under the
//! DEFAULT (strict) proven-output gate.
//!
//! PROVENANCE. Measured on `5b45b83b8a`, this exact crate printed 87 == native
//! only with `-Ztrust-cg-output-gate=allow-unknown`; the default gate refused
//! it with "instruction `Call` is outside the modeled fragment", because
//! `verify_output_trust_ir.rs`'s spec side had no `Inst::Call` arm while the
//! shipping path lowers the same body through `inline_local_pure_leaf_calls`.
//! That made the whole strict lane unusable for any crate with a local helper.
//!
//! Pins:
//!  * SUBJECT — no `-Ztrust-cg-output-gate` flag at all (so the DEFAULT strict
//!    policy applies): the compile succeeds, every reachable function goes
//!    through `source -> trust_ir_of -> lower_module_to_lir`, and the
//!    `Call`-fragment refusal is absent from the diagnostics;
//!  * CONTROL — the same crate with the helper's `Call` removed (the body
//!    inlined by hand) also compiles, so a pass above is not an accident of
//!    the gate having been switched off;
//!  * GATE IS STILL LIVE — a body the gate genuinely cannot model (a loop,
//!    WS7.14) is still REFUSED under the same default policy. Without this the
//!    subject's success would not distinguish "the gate models the call" from
//!    "the gate stopped looking";
//!  * a loop whose trust-ir reaches a runtime check (`i += 1`) is refused
//!    `[unfaithful-panic]` before any gate runs (R-8 ledger item 1).

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, rustc};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

/// The Part A F1 recipe, MINUS `-Ztrust-cg-output-gate`: the default strict
/// proven-output policy is exactly what this fixture is about.
fn strict_trust_ir_frontend(input: &str, out: &str) -> run_make_support::Rustc {
    rfs::create_dir(out);
    let mut cmd = rustc();
    cmd.input(input)
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .out_dir(out)
        // A run-make recipe is a new policy boundary: bootstrap's inherited
        // deauthorization override must not decide this subject compilation.
        .env_remove(TRUST_NO_VERIFY_ENV);
    cmd
}

fn main() {
    // ── SUBJECT: a local `Call`, under the DEFAULT strict gate ────────────
    let built = strict_trust_ir_frontend("f1_rust.rs", "out-subject").run();
    let stderr = built.stderr_utf8();
    for forbidden in [
        "instruction `Call` is outside the modeled fragment",
        "could not be proven output-preserving",
        "internal compiler error",
    ] {
        assert!(
            !stderr.contains(forbidden),
            "WS7.12: the strict gate must model a module-local call (`{forbidden}`):\n{stderr}"
        );
    }
    built.assert_stderr_contains(
        "reachable function(s) completed source -> trust_ir_of -> lower_module_to_lir",
    );
    assert!(
        std::path::Path::new("out-subject").join("libparta_f1_control.rlib").exists(),
        "the strict gate must ship the rlib it proved"
    );

    // ── CONTROL: the same crate with no call at all ───────────────────────
    rfs::write(
        "no_call.rs",
        r#"#![crate_name = "parta_f1_no_call"]
#[unsafe(no_mangle)]
pub extern "C" fn parta_f1_program() -> u64 {
    (5u64 ^ 0x55) ^ 7
}
"#,
    );
    strict_trust_ir_frontend("no_call.rs", "out-control").run();

    // ── GATE IS STILL LIVE: a loop is outside the modeled fragment ────────
    // WS7.14 is the increment that models these. Until it lands, the strict
    // gate must still REFUSE one — otherwise "the subject passed" would be
    // evidence about the flag, not about the call model.
    //
    // The body must REACH the gate: no `core` callee (`wrapping_add` is an
    // upstream body the trust-ir FRONTEND refuses before any gate runs, and
    // that refusal would satisfy nothing this pin is about), only the
    // operators the converter already maps. Measured 2026-09-19: with
    // `acc.wrapping_add(i)` the crate died in the frontend's refusal census
    // (`[upstream-body]`) and the gate's own text never appeared.
    //
    // RE-PINNED 2026-09-29 (R-8 ledger item 1, plan §5): the counted loop this
    // row used (`i += 1`) now dies BEFORE the gate as well — its overflow check
    // is an `Assert`, which F1 lowers to a bare trap, so the frontend refuses it
    // `[unfaithful-panic]` under every gate policy (strict verification keeps the
    // overflow check on even with `-Coverflow-checks=off`; a constant shift keeps a
    // `ShiftInRange` check too). That refusal is pinned below, and the gate's
    // liveness moves to a loop with NO arithmetic, so no runtime check reaches it.
    // main's 9eb52da524 re-pinned this row independently (a bitwise-only
    // `count_to`); the claim is the same — an `Assert`-free loop reaches the gate
    // and is refused there — so `xor_until` carries it, asserting the gate's
    // `loop/backedge` text as well, and `count_to` keeps `i += 1` for the
    // `[unfaithful-panic]` row below.
    rfs::write(
        "loop_body.rs",
        r#"#![crate_name = "parta_f1_loop"]
#[unsafe(no_mangle)]
pub extern "C" fn xor_until(n: u64) -> u64 {
    let mut acc = 0u64;
    let mut go = n != 0;
    while go {
        acc ^= n;
        go = acc != n;
    }
    acc
}
"#,
    );
    //
    // RE-PINNED 2026-10-14 (WS7.14, batch1): the gate no longer refuses every backedge; it
    // MODELS a loop by cut-point simulation (`verify_output_trust_ir`), locating each loop
    // header's shared variables in the emitted bytes. This build of `xor_until` gives it no
    // backward-branch target whose register file holds the header's three shared variables,
    // so the gate refuses it FAIL-CLOSED there, by that name. The claim is unchanged — an
    // `Assert`-free loop reaches the gate and is refused BY THE GATE — with the gate's own
    // reason as of WS7.14.
    let refused = strict_trust_ir_frontend("loop_body.rs", "out-loop").run_fail();
    let stderr = refused.stderr_utf8();
    assert!(
        stderr.contains("function `xor_until` could not be proven output-preserving")
            && stderr.contains("could not locate loop header bb1 in the emitted bytes")
            && stderr.contains("(fail-closed)"),
        "the default gate must still refuse a shape it cannot model:\n{stderr}"
    );
    assert!(!stderr.contains("[unfaithful-panic]"), "this loop has no runtime check:\n{stderr}");
    // Trust (2026-09-30, plan §5 fail-open item 1, bridge side): nor does the
    // converter's own by-name refusal of an `Assert` fire on it.
    assert!(
        !stderr.contains("[implicit-panic-unfaithful]"),
        "the loop must reach the gate, not stop at the converter's panic refusal:\n{stderr}"
    );

    // The counted loop: refused by the frontend, not the gate, and no rlib.
    rfs::write(
        "counted_loop.rs",
        r#"#![crate_name = "parta_f1_counted_loop"]
#[unsafe(no_mangle)]
pub extern "C" fn count_to(n: u64) -> u64 {
    let mut acc = 0u64;
    let mut i = 0u64;
    while i < n {
        acc ^= i;
        i += 1;
    }
    acc
}
"#,
    );
    let refused = strict_trust_ir_frontend("counted_loop.rs", "out-counted").run_fail();
    let stderr = refused.stderr_utf8();
    for needle in ["[unfaithful-panic]", "reaches a runtime check (`Assert` NoOverflow)"] {
        assert!(stderr.contains(needle), "counted loop: missing `{needle}`:\n{stderr}");
    }
    assert!(
        !std::path::Path::new("out-counted").join("libparta_f1_counted_loop.rlib").exists(),
        "a function that can reach a trap must not ship"
    );
}
