#![crate_type = "lib"]
// MUTANT (FALSE PROOF regression, 2026-08-14 — the explicit `panic!` shape).
//
// `f(&[200, 0, 0, 0])` panics. The verifier MUST refuse this (exit 1).
//
// Same defect as `pf_subsume_foreach_assert.rs` with the guarded `panic!()`
// spelling instead of `assert!`, which exercises the `is_panic_call` arm of the
// bridge's aggregate emission (`lower_function`: the whole-function
// panic-freedom obligation is minted ONLY for a diverging panic `Call`, never
// for a `Terminator::Assert`). That emission rule is exactly why the removed
// subsumption could never be sound: the aggregate exists precisely when a panic
// source has no counted per-site obligation of its own.
pub fn f(a: &[u8; 4]) -> u8 {
    let mut t = 0u8;
    for &x in a {
        if x == 200 {
            panic!();
        }
        t ^= x;
    }
    t
}
