#![crate_type = "lib"]
// FALSE-REFUTATION GUARD (index side). `a[2]` on a `[i32; 4]` lowers (rustc 1.98.0-nightly,
// `-Zmir-opt-level=0 -C overflow-checks=on`) to
//     _2 = const 2_usize;
//     _3 = Lt(copy _2, const 4_usize);
//     assert(move _3, "index out of bounds: the length is {} but the index is {}", ...)
// The condition folds to `true` and equals the terminator's `expected`. IT DOES NOT FAULT.
//
// Completeness twin of `mutant/sd_array_index_const_generic_oob.rs`: same `BoundsCheck`
// shape, opposite folded value. A `BoundsCheck` discharge rule that keys on constancy
// rather than agreement passes both; one that refuses constant bounds asserts fails here.
//
// `proved/const_array_index.rs` already holds a constant in-range index; it indexes a
// LOCAL array literal with no parameters, so it is not the twin of the mutant above. This
// row differs from that mutant in the folded constant and in nothing else.
//
// Runtime oracle (stock rustc 1.96.0, -O -C overflow-checks=on -C debug-assertions=on,
// #[inline(never)], black_box, catch_unwind, silent hook): 0 panics / 64 runs, sweep
// `a = [k, k+1, k+2, k+3]` for `k in 0..64`.
pub fn sd_array_index_const_in_range(a: [i32; 4]) -> i32 { a[2] }
