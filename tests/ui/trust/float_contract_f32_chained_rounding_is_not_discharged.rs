//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
// The first sum rounds from the exact midpoint below 2^103 to 2^103 in
// binary32. With peer=f32::MAX, the second sum then rounds to infinity.
// An f64-only interval for `rounded` incorrectly classifies it as a tiny
// addend strictly below 2^103 and drops this real overflow obligation.
//
// WHY `certify` (changed 2026-09-18). This file used to run under the default
// policy and expect "Trust Level 0 safety verification incomplete". That used
// "the build fails" as a proxy for "the row is not discharged", and the proxy
// stopped holding when the Level-0 accounting was fixed to honour
// `proof_level()`: `FloatOverflowToInfinity` is `L1Functional`, because
// overflow to +/-inf is DEFINED in Rust — no trap, no UB, no panic — so under
// the DEFAULT policy an undischarged float row is now REPORTED rather than
// fatal. That is DESIGN_PHILOSOPHY section 9 and the 2026-08-02 float report's
// resolution, which promised exactly this split.
//
// `certify` is the policy that demands full static discharge, so it is where
// "is not discharged" is still an error, and it is the honest place for this
// file's claim. The soundness property is unchanged: under either policy the
// row is UNPROVED. A false proof would be a PROVED row, and that is what would
// break this file.
pub fn rounded_midpoint_plus_peer(a: f32, peer: f32) -> f32
    //~^ ERROR Trust strict verification failed
    requires a <= 10141204197362925404659038289920.0
    && a >= 10141204197362925404659038289920.0
{
    let rounded = a + 302231454903657293676544.0f32;
    rounded + peer
}
