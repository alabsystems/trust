#![crate_type = "lib"]
// MUTANT of proved/foreach_iter_rev.rs: the body uses non-wrapping `t + x`, which
// overflows. The verifier MUST refuse this (exit 1) — `[overflow:add]` fails with
// a verified counterexample. Guards the adapter / stack-pointer-safe-store lane:
// leaving the opaque adapter struct's stack store untracked (sound) must NOT mask
// a real overflow in the loop body.
pub fn foreach_iter_rev(s: &[i32]) -> i32 {
    let mut t = 0i32;
    for &x in s.iter().rev() {
        t = t + x;
    }
    t
}
