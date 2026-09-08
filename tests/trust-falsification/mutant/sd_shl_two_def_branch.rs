#![crate_type = "lib"]
// TWO DEFS, NOT PATH-INDEPENDENT. The shift amount `n` is assigned on two branches, one of
// which is 64. A resolver that picks ONE def folds `n` to 32, calls the `Assert` statically
// dead, and certifies a function that panics on half its input space. A multi-def local
// must be POISONED — answering `None`, not a value.
//
// This is the class that has bitten this campaign repeatedly (the parameter accumulator,
// `body_unique_value_def`); the corpus should hold the shape, not just the reports.
//
// Runtime oracle (stock rustc 1.96.0, -O -C overflow-checks=on -C debug-assertions=on,
// #[inline(never)], black_box, catch_unwind, silent hook): 64 panics / 128 runs, sweep
// `x in 0..64` x `big in {false, true}`. Every panic is exactly `big == true`.
//
// The verifier MUST refuse this (exit 1, shift-overflow violation with a counterexample).
pub fn sd_shl_two_def_branch(x: u64, big: bool) -> u64 {
    let n: u32 = if big { 64 } else { 32 };
    x << n
}
