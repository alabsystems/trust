#![crate_type = "lib"]
// BOUNDS-SIDE TWIN of `mutant/ep_hidden_obligation_divzero.rs`. The entry-prefix index is
// in range for the caller's `i = 3` on a `[i32; 4]`; the non-prefix `a[i + 2]` behind the
// branch is index 5 and is not. Discharging the prefix obligation must not be allowed to
// carry the second one with it.
//
// Runtime oracle (stock rustc 1.96.0, -O -C overflow-checks=on -C debug-assertions=on,
// #[inline(never)], black_box, catch_unwind, silent hook): 32 panics / 64 runs, sweep
// `a = [k, k+1, k+2, k+3]` for `k in 0..32` x `flag in {false, true}`. Every panic is
// exactly `flag == true`.
//
// The verifier MUST refuse this (exit 1, bounds violation with a counterexample).
pub fn ep_hidden_obligation_bounds(a: [i32; 4], flag: bool) -> i32 { member(a, 3, flag) }
#[inline(never)]
fn member(a: [i32; 4], i: usize, flag: bool) -> i32 {
    let first = a[i];
    if flag { first + a[i + 2] } else { first }
}
