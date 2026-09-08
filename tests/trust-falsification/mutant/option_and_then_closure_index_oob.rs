#![crate_type = "lib"]
// BOUNDS PANIC INSIDE AN `and_then` CLOSURE. The index the closure reads is
// derived from the value the combinator threads through its return slot, so the
// violation is only visible if the wrapper's slot model carries the real
// `i + k` and not a fresh unconstrained symbol. IT FAULTS: the table has 3
// elements and the index is `j % 4`, so `j % 4 == 3` is out of bounds.
// Runtime oracle (stock rustc 1.96.0, -O -C debug-assertions=on,
// #[inline(never)], black_box, catch_unwind, silent hook): 9 panics / 34 runs,
// sweep `i in 0..8` x `k in 0..4` (32) plus (usize::MAX, 1) and (usize::MAX, 0).
// The 8 grid panics are exactly `i + k in {3, 7}`; the ninth is
// (usize::MAX, 0) at `j % 4 == 3`. (usize::MAX, 1) does NOT panic — the
// checked add is None and `and_then` short-circuits.
//
// THE MODULUS IS LOAD-BEARING. Without `% 4` the verifier would refute
// `table[i + k]` from the unbounded parameter alone and never consult what the
// combinator returned; with it, every index is in `0..=3` and only the slot
// value distinguishes the faulting case from the three safe ones. See
// `mutant/option_and_then_inner_overflow.rs` for why this lane needed in-gate
// coverage at all.
//
// The verifier MUST refuse this (exit 1, bounds violation with a counterexample).
pub fn and_then_closure_index_oob(i: usize, k: usize) -> Option<u64> {
    let table = [10u64, 20, 30];
    i.checked_add(k).and_then(|j| Some(table[j % 4]))
}
