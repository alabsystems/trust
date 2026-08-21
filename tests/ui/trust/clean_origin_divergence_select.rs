//@ needs-trust-verify
//@ build-fail
//@ compile-flags: -Z trust-verify=off -Ztrust-clean-origin-mutate-emitter
//@ dont-check-compiler-stderr
//! **R2/C5a — A WRONG SELECT EMISSION MUST FAIL THE BUILD.**
//!
//! The Select twin of `clean_origin_divergence_fails_build.rs`. Under the
//! knob, the emitted diamond's `SwitchInt` targets are SWAPPED — the exact
//! `SwitchTargets::static_if` polarity inversion, the one bug this shape
//! invites — so the emission computes max where the declaration says min.
//! Side B is untouched; the structural agreement (and, per probe_h, the
//! kernel itself) refuses, and the build fails with the gate's own fatal.
//!
//! The crate-level dual is `control_6_select_emitter_mutation.rs::half_2`;
//! this fixture is the same property observed from the driver.

mod m {
    clean {
        def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
    }
    //~^^ ERROR the emitted body does not agree with the declaration
}

fn main() {
    // Never reached: the gate's fatal refusal fails the build first.
    let _ = crate::m::min2(7, 41);
}
