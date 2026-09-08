#![crate_type = "lib"]
// FALSE-REFUTATION GUARD (shift, completeness). `x << 32` on a `u64` lowers (rustc
// 1.98.0-nightly, `-Zmir-opt-level=0 -C overflow-checks=on`) to
//     _3 = const 32_i32 as u32 (IntToInt);
//     _4 = Lt(move _3, const 64_u32);
//     assert(move _4, "attempt to shift left by `{}`, which would overflow", const 32_i32)
// The condition constant-folds path-independently to `true`, which EQUALS the terminator's
// `expected`, so the panic edge is unreachable in the function's own body and nothing is
// deferred to a caller. IT DOES NOT FAULT.
//
// It is the completeness twin of `mutant/sd_shl_const_generic_overflow.rs`: the two differ
// only in the folded constant, so a verifier that discharges shift asserts by CONSTANCY
// rather than by AGREEMENT with `expected` passes both, and one that refuses all constant
// shift asserts fails here. Only a comparison against `expected` gets both rows right.
//
// The corpus's other constant-shift acceptance, `proved/signed_shift_const.rs`, is a RIGHT
// shift on an `i32` (`a >> 2`); left-shift overflow on a `u64` is a different `Assert`
// kind and a different width, so it does not stand in for this row.
//
// Runtime oracle (stock rustc 1.96.0, -O -C overflow-checks=on -C debug-assertions=on,
// #[inline(never)], black_box, catch_unwind, silent hook): 0 panics / 64 runs, sweep
// `x in 0..64`.
pub fn sd_shl_const_in_range(x: u64) -> u64 { x << 32 }
