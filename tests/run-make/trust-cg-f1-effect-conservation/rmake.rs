//! The effect-conservation gate binds the trust-ir CODEGEN frontend (F1): a body whose trust-ir
//! is not the program is never compiled from it.
//!
//! PROVENANCE. The 2026-10-01 producer review built `user.rs`'s `consume(f: dep::Fd) -> i32 {
//! f.0 & 0xff }` with `-Ztrust-cg-frontend=trust-ir -Zcodegen-backend=trust-cg`: the frontend
//! reported "1/1 reachable function(s) completed" — the body was spliced and codegen-licensed
//! with `Fd::drop` elided (the direct producer emits no `Inst::Drop`) — and only the proven-output
//! gate's struct-parameter limit stopped the object; with that gate off, the linked program
//! printed `drops observed = 0 (1 = correct)`. Measured again with this recipe's flags on this
//! tree's base (aaeed27fd6) before the gate: `1/2 reachable function(s) completed` — `consume`
//! completed; the other reachable instance is `Fd`'s drop-glue shim, which this frontend refuses
//! as `[synthesized-instance]` either way.
//!
//! Pins:
//!  * SUBJECT — `consume` does not complete: `0/2` completed. Until step 2 increment 4b the gate
//!    refused it as `[effect-not-conserved]`, naming the elided drop. Since 4b the producer
//!    places `Fd`'s drop (`crates/trust-thir-lower/src/drops.rs`), the gate finds it equal to
//!    rustc's drop elaboration, and until 4c the body reached the trust-ir -> LIR converter,
//!    which refused it (`[converter-refused]`: the drop's slot store, then `Inst::Drop` by name).
//!    Since step 2 increment 4c (drop glue as trust-ir) the drop-glue lane, active under this
//!    recipe's default strict output gate, resolves the drop to `drop_glue::<Fd>` first, and
//!    that glue needs `Fd`'s destructor, a body of crate `dep`: `[upstream-body]` (trust-ir in
//!    metadata, increment 6), naming the destructor. Either way the destructor is never
//!    silently skipped;
//!  * LOST PANIC CHECK — `lost_assert.rs`'s `div_lost`, built with the field-store mutation that
//!    drops its division and the division's `Assert`, is REFUSED as `[effect-not-conserved]`
//!    naming `EffectNotConserved(assert, …)`: `0/1` completed. Before the gate counted panic
//!    checks the frontend completed it, and the linked program returned where Rust panics (the
//!    review's end-to-end run; `lost_assert.rs` says how);
//!  * CONTROL — a crate with no lost effect (`plain.rs`) still completes every reachable
//!    function under the same flags, so the refusal is the gate's verdict on `consume`, not a
//!    frontend that stopped compiling anything.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, rustc};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

fn f1(input: &str, out: &str) -> run_make_support::Rustc {
    rfs::create_dir(out);
    let mut cmd = rustc();
    cmd.input(input)
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .out_dir(out)
        .env_remove(TRUST_NO_VERIFY_ENV);
    cmd
}

fn main() {
    // The dependency, through the ordinary backend.
    rustc()
        .input("dep.rs")
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Ztrust-verify=off")
        .out_dir("dep-out")
        .run();

    // ── SUBJECT ─────────────────────────────────────────────────────────────
    let refused = f1("user.rs", "user-out")
        .extern_("dep", "dep-out/libdep.rlib")
        .run_fail();
    let stderr = refused.stderr_utf8();
    assert!(
        stderr.contains("0/2 reachable function(s) completed"),
        "`consume` must not complete:\n{stderr}"
    );
    // Step 2 increment 4b: the drop is placed, so the gate no longer refuses `consume`...
    assert!(
        !stderr.contains("[effect-not-conserved]"),
        "the producer places `consume`'s drop; the gate must not call it elided:\n{stderr}"
    );
    // ... and (step 2 increment 4c) the drop-glue lane refuses it: `Fd`'s glue needs the
    // upstream crate's destructor body.
    assert!(stderr.contains("[upstream-body]"), "refused for an upstream destructor:\n{stderr}");
    assert!(
        stderr.lines().any(|l| l.contains("4user7consume")
            && l.contains(
                "drop of `dep::Fd` does not resolve: the destructor `<dep::Fd as \
                 std::ops::Drop>::drop` is in crate `dep`"
            )),
        "the refusal names `consume` and the upstream destructor:\n{stderr}"
    );

    // ── LOST PANIC CHECK ────────────────────────────────────────────────────
    let refused = f1("lost_assert.rs", "lost-assert-out")
        .arg("-Ztrust-ir-lower-mutate-rhs-effects")
        .run_fail();
    let stderr = refused.stderr_utf8();
    assert!(
        stderr.contains("0/1 reachable function(s) completed"),
        "`div_lost` must not complete:\n{stderr}"
    );
    assert!(stderr.contains("[effect-not-conserved]"), "refused by the gate, by class:\n{stderr}");
    let gate_line = stderr
        .lines()
        .find(|l| l.contains("8div_lost") && l.contains("tag(s):"))
        .unwrap_or_else(|| panic!("the gate's refusal names `div_lost`:\n{stderr}"));
    assert!(
        gate_line.contains("EffectNotConserved(assert, a division-by-zero check"),
        "the refusal names the lost panic check: {gate_line}"
    );

    // ── CONTROL ─────────────────────────────────────────────────────────────
    let built = f1("plain.rs", "plain-out").run();
    let stderr = built.stderr_utf8();
    assert!(
        stderr.contains("2/2 reachable function(s) completed"),
        "a crate with no lost effect still compiles through the frontend:\n{stderr}"
    );
    assert!(!stderr.contains("[effect-not-conserved]"), "{stderr}");
}
