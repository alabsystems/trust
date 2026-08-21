//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//! **I5 — THE CONTROL FOR CROSS-AUTHORITY CALL MODELING: a WRONG caller claim
//! about a Clean-origin call must still be REFUTED.**
//!
//! `clean_origin_verify_on.rs` went green when the caller's VC lane learned
//! `pick`'s definitional summary (`result == arg0`, on the kernel gate's
//! authority — see that fixture's GREEN AS OF block for the chain). A summary
//! that merely BLESSED whatever the caller asserts would flip that fixture
//! identically — and would be a soundness hole, not a capability. This file is
//! the direction that tells the two apart: `pick(41, 7)` returns 41, the
//! caller asserts 7, and the build must FAIL.
//!
//! # Why the summary refutes this, mechanically
//!
//! The injected fact is an EQUALITY pinned to the call's dest —
//! `v == 41`, rebound from `_0 == arg0` under `arg0 := 41` — conjoined into
//! the caller's body VCs (never `fact => vc`, the polarity that would
//! false-FAIL; and never dropped, the omission that would leave `v` havocked).
//! The assert's violation formula `v != 7` is then SATISFIABLE together with
//! the pinned `v == 41` — a genuine counterexample, so the obligation is
//! REFUTED, not unknown: the trust-vcgen unit control
//! (`definitional_projection_pins_dest_to_projected_argument`) pins the same
//! fact shape at the crate level.
//!
//! Had the summary lane instead declined (an unmodeled shape, a plan
//! refusal), the call would havoc and this build would STILL fail — but as an
//! unproved coverage gap, not a refutation. Either way this fixture is red;
//! its value is that it can never go green while the flip fixture's summary
//! machinery exists, which is exactly what makes the pair a control.
//!
//! # What this fixture does NOT claim
//!
//! Nothing about proof authority (see `docs/TCB.md`), and nothing about the
//! runtime: the program is never run. It pins one property only — the
//! definitional summary carries the callee's real semantics, so it refutes
//! wrong claims instead of blessing right ones.

mod m {
    clean {
        def pick (a : UInt64) (b : UInt64) : UInt64 := a
    }
}

fn main() {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    let v = m::pick(41, 7);
    // DELIBERATELY WRONG: the projection returns its FIRST argument (41).
    // The kernel-gated summary must refute this claim, never bless it.
    assert!(v == 7, "MUST be refuted: pick projects its FIRST argument");
}
