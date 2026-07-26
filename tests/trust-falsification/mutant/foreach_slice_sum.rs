#![crate_type = "lib"]
// MUTANT of proved/foreach_slice_sum.rs: the body uses non-wrapping `t + x`,
// which overflows (the accumulator and elements are unbounded `i32`). The verifier
// MUST refuse this (exit 1) — `[overflow:add]` fails with a verified
// counterexample. Guards the slice-iterator lane end to end: modeling the
// iterator/borrow/yielded-reference as fresh-symbolic must NOT mask a real
// overflow in the loop body.
pub fn foreach_slice_sum(s: &[i32]) -> i32 {
    let mut t = 0i32;
    for &x in s {
        t = t + x;
    }
    t
}
