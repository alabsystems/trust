// FAIL-SAFE: warm replay must never suppress a real error. This crate type-checks
// but fails borrowck (returns a reference to a local). Under -Ztrust-witness=replay:<dir>
// the compile must emit the IDENTICAL borrow error and exit non-zero, exactly as a
// no-flag build does — the replay lane is an optimization, never an authority that
// can mask a diagnostic. (The crate errors, so has_errors() taints it and no
// witness is committed; replay MISSes and falls through to real analysis.)
pub fn dangling() -> &'static i32 {
    let x = 5;
    &x
}
