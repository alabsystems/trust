#![crate_type = "lib"]
// INDEX-SIDE TWIN of `mutant/sd_shl_const_generic_overflow.rs`: `a[I]` with `I` symbolic
// in the generic body, monomorphized to `I = 4` on a `[i32; 4]`. rustc's deny-by-default
// `unconditional_panic` lint never fires, for the same pre-monomorphization reason, so the
// crate compiles with zero warnings. The generic body is (rustc 1.98.0-nightly,
// `-Zmir-opt-level=0 -C overflow-checks=on`)
//     _2 = const I;
//     _3 = Lt(copy _2, const 4_usize);
//     assert(move _3, "index out of bounds: the length is {} but the index is {}", ...)
// so at `I = 4` the condition folds to `false` while `expected` is `true`.
//
// The naive spelling `a[4]` is REJECTED BY RUSTC and so is not a vector; this is.
//
// Runtime oracle (stock rustc 1.96.0, -O -C overflow-checks=on -C debug-assertions=on,
// #[inline(never)], black_box, catch_unwind, silent hook): 64 panics / 64 runs, sweep
// `a = [k, k+1, k+2, k+3]` for `k in 0..64`. Every element value panics.
//
// The verifier MUST refuse this (exit 1, bounds violation with a counterexample).
pub fn sd_array_index_const_generic_oob(a: [i32; 4]) -> i32 { idx_by::<4>(a) }
#[inline(never)]
fn idx_by<const I: usize>(a: [i32; 4]) -> i32 { a[I] }
