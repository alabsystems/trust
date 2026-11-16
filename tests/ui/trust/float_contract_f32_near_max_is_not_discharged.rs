//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The SOUNDNESS half of `float_contract_f32_bound_discharges.rs`.
//!
//! `f32` magnitude bounds discharge, but only against binary32 thresholds. An
//! `f32` bound near `f32::MAX` must still be REFUSED, because the sum really is
//! infinity. Against the f64-scaled thresholds this file verified — that is the
//! measured false proof the width-aware discharge exists to prevent.
//!
//! Read honestly, this file is belt-and-braces: it would ALSO have been refused
//! before the fix, because the `f32` bound was then unreadable and the discharge
//! declined for want of any interval at all. The sharp pin is the unit test
//! `one_sided_near_max_f32_add_is_not_discharged`, which refuses with the bound
//! readable — that is the state in which the old thresholds produced the false
//! proof. What this file adds is that the end-to-end path agrees.
//!
//! The bound is spelled as the exact decimal for `2^127` rather than `3.4e38`
//! on purpose: a float literal is admitted at binary32 only when narrowing it
//! from binary64 round-trips exactly, and a power of two does. A rounded
//! decimal would be refused for the wrong reason and would test nothing.
//!
//! WHY `certify` (changed 2026-09-18). This file used to run under the default
//! policy and expect "Trust Level 0 safety verification incomplete". That was
//! using "the build fails" as a proxy for "the row is not discharged", and the
//! proxy stopped holding when the Level-0 accounting was fixed to honour
//! `proof_level()`: `FloatOverflowToInfinity` is `L1Functional`, because
//! overflow to +/-inf is DEFINED, so under the DEFAULT policy an undischarged
//! float row is now reported rather than fatal (DESIGN_PHILOSOPHY section 9,
//! and the 2026-08-02 float report's resolution, which promised exactly this
//! split). `certify` is the policy that demands full static discharge, so it is
//! the policy in which "is not discharged" is still an error — and it is the
//! honest place to assert this file's claim.
//!
//! The SOUNDNESS property is unchanged and was re-measured on the same binary:
//! under the default policy this program reports `0 proved, 1 unknown` for the
//! float row. Unproved, never proved. The false proof this file exists to
//! prevent would be a PROVED row, and that is what would break it.

pub fn near_max_f32_add(a: f32, b: f32) -> f32
//~^ ERROR Trust strict verification failed
    requires a <= 170141183460469231731687303715884105728.0
        && a >= -170141183460469231731687303715884105728.0
        && b <= 170141183460469231731687303715884105728.0
        && b >= -170141183460469231731687303715884105728.0
{
    a + b
}
