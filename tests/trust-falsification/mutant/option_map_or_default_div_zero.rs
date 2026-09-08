#![crate_type = "lib"]
// `map_or` WHOSE DEFAULT ARM DIVIDES BY ZERO. `map_or` takes its default BY
// VALUE, so `100 / d` is evaluated at the call site before the combinator runs.
// IT FAULTS TWO WAYS, and both are wanted: `d == 0` divides by zero on every
// input, and `a * b == u64::MAX` overflows at `v + 1` inside the `Some` closure.
// Runtime oracle (stock rustc 1.96.0, -O -C debug-assertions=on,
// #[inline(never)], black_box, catch_unwind, silent hook): 40 panics / 108 runs,
// sweep `a x b` over {0, 1, 2, 3, u64::MAX, u64::MAX-1} squared x `d in 0..3`.
// The 40 decompose exactly: 36 are `d == 0` (the whole `a x b` grid), and 4 are
// the `v + 1` overflow — (1, u64::MAX) and (u64::MAX, 1) at `d in {1, 2}`.
//
// See `mutant/option_and_then_inner_overflow.rs` for why this lane needed
// in-gate coverage at all. This row guards the `map_or` face: unlike `and_then`
// and `map`, its wrapper writes its return slot on BOTH arms, so a summary that
// modelled only the `Some` store would lose the eager-default panic path.
//
// The verifier MUST refuse this (exit 1, division-by-zero with a counterexample).
pub fn map_or_default_div_zero(a: u64, b: u64, d: u64) -> u64 {
    a.checked_mul(b).map_or(100 / d, |v| v + 1)
}
