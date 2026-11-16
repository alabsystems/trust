//! Trust (W6, docs/design/2026-08-27-two-language-direct-to-trust-ir.md): the
//! trust-ir codegen frontend never consumes a Clean-origin row below tier
//! `gate` — and on this lane (the handoff, lowered through `module_to_lir`)
//! never consumes a `Producer::Clean` row at all: since plan step 3.4 a `gate`
//! row carries the authenticated `clean-carrier-gate` carrier, which only the
//! `Compiler::compile` lane will honor (step 3.6). Measured before this fixture: zero producer or
//! tier checks existed anywhere on the codegen path, so the boundary held only
//! by unreachability, while IR-5 already re-pointed Rust->Clean call edges at
//! the appended Clean row.
//!
//! Pins:
//!  * SUBJECT — a crate whose Rust body calls a Clean `def`, compiled under
//!    verification ON (so the Clean row is recorded and the edge re-pointed)
//!    with `-Zcodegen-backend=trust-cg -Ztrust-cg-frontend=trust-ir`, is
//!    REFUSED with the named producer-gate refusal and its v7/D3 options, the
//!    frontend reports it as a refusal (never a MIR fallback), and the
//!    compiler does not ICE;
//!  * CONTROL — the same invocation on a crate with no Clean call edge
//!    completes every reachable function through the trust-ir frontend.
//!  * Trust (plan step 3.0): the census names every Clean refusal under ONE
//!    class, `[clean-below-gate]`, with the row's disclosed tier and shape —
//!    measured before: the def itself was `[producer-declined]` with no Clean
//!    reason and the caller `[converter-refused]`.
//!  * Trust (plan step 3.3): the F1 inventory no longer walks `cleanWsum`'s
//!    `clean_origin_mir` MIR, so no `[upstream-body]` row names the
//!    `core::num::<impl u64>::wrapping_add` that MIR calls (and no Rust body
//!    or trust-ir row does) — measured before: 1/4 completed with that row.
//!  * Trust (plan step 3.0, review): the census prints the `[clean-below-gate]`
//!    options once for the class, D38's MIR-frontend route among them —
//!    measured before: they were in no output at all.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, rustc};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

fn trust_ir_frontend(input: &str, out: &str) -> run_make_support::Rustc {
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
        .arg("-Ztrust-cg-output-gate=allow-unknown")
        .out_dir(out)
        // A run-make recipe is a new policy boundary: bootstrap's inherited
        // deauthorization override must not decide this subject compilation.
        .env_remove(TRUST_NO_VERIFY_ENV);
    cmd
}

fn main() {
    // ── SUBJECT: the Rust caller reaches a Clean-origin row ────────────────
    let refused = trust_ir_frontend("foo.rs", "out-subject").run_fail();
    let stderr = refused.stderr_utf8();
    for expected in [
        "Clean-origin trust-ir function",
        "is not admitted to codegen",
        "would have been inlined",
        "refuses every `Producer::Clean` body fail-closed",
        "Options: (1) keep the MIR lane",
        "this frontend never falls back to the MIR path",
    ] {
        assert!(stderr.contains(expected), "missing `{expected}` in:\n{stderr}");
    }
    for forbidden in ["internal compiler error", "panicked at", "thread 'rustc'"] {
        assert!(!stderr.contains(forbidden), "the producer gate must refuse, not ICE (`{forbidden}`):\n{stderr}");
    }
    // Trust (plan step 3.0): one class, with the tier and shape the recorder disclosed.
    for expected in [
        "refused 2 of 3 reachable function(s)",
        "2  (66.6%)  [clean-below-gate]",
        "the Clean-origin def `m::cleanWsum` (tier `gate`, shape `wrapping-binop`)",
        "reaches the Clean-origin def `m::cleanWsum` (tier `gate`, shape `wrapping-binop`)",
        // Plan step 3.4: the handoff now indexes `cleanWsum` (an authenticated `gate` row of
        // this Session's carrier ledger), so the def's own item reaches the converter, which
        // honors no Clean carrier and refuses it by name (before: "the assembled handoff
        // indexes no body for it", the handoff never indexed a Clean row).
        "(it is the function being lowered)",
        "This converter honors no Clean carrier",
    ] {
        assert!(stderr.contains(expected), "missing `{expected}` in:\n{stderr}");
    }
    // Trust (plan step 3.0, review 2026-10-05): the census prints the class's options ONCE,
    // under its `retired by:` line, D38's MIR-frontend route among them. Measured before: no
    // production path printed them (they lived only in `Display`, which the census never uses).
    for needle in [
        "No F1 lane admits a Clean-origin Function yet, whatever its tier",
        "Options: (1) build this crate on the MIR lane",
        "owner ruling D38",
        "(3) keep the Clean call outside this trust-ir-frontend unit",
    ] {
        assert_eq!(stderr.matches(needle).count(), 1, "`{needle}` once for the class in:\n{stderr}");
    }
    for forbidden in ["[producer-declined]", "[converter-refused]", "[instance-assembly]"] {
        assert!(!stderr.contains(forbidden), "a Clean refusal outside `[clean-below-gate]` (`{forbidden}`):\n{stderr}");
    }
    // Trust (plan step 3.3): no MIR-only neighbour of the Clean def in the inventory.
    for forbidden in ["[upstream-body]", "wrapping_add"] {
        assert!(!stderr.contains(forbidden), "the F1 inventory walked `clean_origin_mir` (`{forbidden}`):\n{stderr}");
    }
    assert!(
        !std::path::Path::new("out-subject").join("libclean_below_gate.rlib").exists(),
        "no object may be written for a refused trust-ir codegen unit"
    );

    // ── CONTROL: no Clean edge, same frontend, everything completes ────────
    rfs::write(
        "control.rs",
        r#"#![crate_name = "clean_below_gate_control"]
#[inline(never)]
pub fn rust_only(x: u64) -> u64 {
    x ^ 0x55
}
"#,
    );
    let completed = trust_ir_frontend("control.rs", "out-control").run();
    completed.assert_stderr_contains("reachable function(s) completed source -> trust_ir_of -> lower_module_to_lir");
    let stderr = completed.stderr_utf8();
    assert!(!stderr.contains("refused"), "control must not be refused:\n{stderr}");
}
