//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//! **I5 — THE CONTROL FOR THE WRAPPINGBINOP SUMMARY LANE: a WRONG caller
//! claim about a Clean-origin wrapping call must still be REFUTED.**
//!
//! `clean_origin_wrapping_verify_on.rs` went green when the caller's VC lane
//! learned `wsum`'s definitional summary — the extractor's own single-`Ite`
//! modular reduction `_0 == ite(a + b >= 2^64, a + b - 2^64, a + b)`, on the
//! kernel gate's authority (see that fixture's GREEN AS OF block for the
//! chain). A summary that merely BLESSED whatever the caller asserts would
//! flip that fixture identically — and would be a soundness hole, not a
//! capability. This file is the direction that tells the two apart:
//! `wsum(u64::MAX, 1)` returns 0 (the wrapped value), the caller asserts 1,
//! and the build must FAIL — a strict failure, never an ICE.
//!
//! # Why the summary refutes this, mechanically
//!
//! The injected fact is an EQUALITY pinned to the call's dest — rebound under
//! `a := u64::MAX, b := 1` the modular `Ite` grounds to `s == 0` — conjoined
//! into the caller's body VCs (never `fact => vc`, the polarity that would
//! false-FAIL; and never dropped, the omission that would leave `s`
//! havocked). The assert's violation formula `s != 1` is then SATISFIABLE
//! together with the pinned `s == 0` — a genuine counterexample, so the
//! obligation is REFUTED, not unknown. The trust-vcgen unit control
//! (`definitional_wrapping_summary_pins_dest_to_the_modular_ite`) pins the
//! same fact shape — and pins that the UNBOUNDED `a + b` encoding, which
//! would instead pin `s == 2^64` and refute the flip fixture's CORRECT
//! `s == 0` claim, is never injected.
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
//! definitional summary carries the callee's real mod-2^64 semantics, so it
//! refutes wrong claims instead of blessing right ones.

mod m {
    clean {
        def wsum (a : UInt64) (b : UInt64) : UInt64 := a + b
    }
}

fn main() {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    let s = m::wsum(u64::MAX, 1);
    // DELIBERATELY WRONG: the wrapping add of u64::MAX and 1 is 0, not 1.
    // The kernel-gated summary must refute this claim, never bless it.
    assert!(s == 1, "MUST be refuted: wsum wraps modulo 2^64");
}
