//@ needs-trust-verify
//@ build-fail
//@ compile-flags: -Z trust-verify=off -Ztrust-clean-origin-mutate-emitter
//@ dont-check-compiler-stderr
//! **R2/C9 — A WRONG SELECT-VS-LITERAL EMISSION MUST FAIL THE BUILD.**
//!
//! The literal-compare twin of `clean_origin_divergence_select.rs`. Under
//! the knob, the emitted diamond's `SwitchInt` targets are swapped — the
//! polarity inversion — so the emission returns `b` below the literal where
//! the declaration says `a`. Side B is untouched; the gate refuses with its
//! own fatal, observed from the driver.
//!
//! The crate-level dual lives in the C9 control suite
//! (`control_7_select_literal_emitter_mutation.rs`); this fixture is the
//! same property from the driver.

mod m {
    clean {
        def clamp10 (a : UInt64) (b : UInt64) : UInt64 := if a < 10 then a else b
    }
    //~^^ ERROR the emitted body could not be established to agree with the declaration
}

fn main() {
    // Never reached: the gate's fatal refusal fails the build first.
    let _ = crate::m::clamp10(9, 77);
}
