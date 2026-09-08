#![crate_type = "lib"]
// INDEX-SIDE TWIN of `mutant/sd_shl_two_def_branch.rs`: the index has two defs and is not
// path-independent, so folding it to either one alone loses the branch that is out of
// bounds. `9usize` on a `[i32; 4]` is the faulting arm.
//
// Runtime oracle (stock rustc 1.96.0, -O -C overflow-checks=on -C debug-assertions=on,
// #[inline(never)], black_box, catch_unwind, silent hook): 64 panics / 128 runs, sweep
// `a = [k, k+1, k+2, k+3]` for `k in 0..64` x `big in {false, true}`. Every panic is
// exactly `big == true`.
//
// The verifier MUST refuse this (exit 1, bounds violation with a counterexample).
pub fn sd_array_index_two_def_branch(a: [i32; 4], big: bool) -> i32 {
    let i = if big { 9usize } else { 1usize };
    a[i]
}
