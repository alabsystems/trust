#![crate_type = "lib"]
// FALSE-REFUTATION GUARD (shift, boundary). `x << 63` is the LAST in-range shift for a
// `u64`: the lowered condition is `Lt(63, 64)`. IT DOES NOT FAULT.
//
// THE OFF-BY-ONE IS THE POINT. An evaluator using `Le` where rustc uses `Lt` — or the
// reverse — agrees with a correct one on `x << 32` and on `x << 64`, and separates from it
// only at the endpoint. `proved/sd_shl_const_in_range.rs` (interior) and
// `mutant/sd_shl_const_generic_overflow.rs` (first out-of-range) bracket this row, so the
// three together locate the comparison rather than merely exercising it.
//
// Runtime oracle (stock rustc 1.96.0, -O -C overflow-checks=on -C debug-assertions=on,
// #[inline(never)], black_box, catch_unwind, silent hook): 0 panics / 64 runs, sweep
// `x in 0..64`.
pub fn sd_shl_const_boundary(x: u64) -> u64 { x << 63 }
