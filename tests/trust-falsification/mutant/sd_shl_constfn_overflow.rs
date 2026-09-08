#![crate_type = "lib"]
// THE THIRD LINT-DODGE ROUTE to a folded-to-`false` `Assert`, and the one that needs no
// generics: a `const fn` the use-site `arithmetic_overflow` lint does not fold but MIR
// const-prop does. `amount(8) == 64`, so `x << n` overflows on every input while the crate
// compiles with zero warnings.
//
// MEASURED, because "const-prop folds it" is the whole claim. In the BUILT MIR the shift
// amount is still a call return (`_2 = amount(const 8_u32)`), and the assert reads
// `Lt(copy _2, const 64_u32)` — not yet constant. The `runtime-optimized` body
// (rustc 1.98.0-nightly, `-O -C overflow-checks=on`, `-Zdump-mir`) is
//     assert(const false, "attempt to shift left by `{}`, which would overflow", const 64_u32)
// i.e. the condition arrives at the back end already folded to `false`. Reading that as
// "constant, therefore discharged" certifies a function that panics on every input.
//
// Together with `sd_shl_const_generic_overflow` and `sd_array_index_const_generic_oob`
// this is the third distinct route by which a statically-false safety condition reaches
// the verifier without rustc having rejected the program first. Three routes are known;
// nothing here claims they are the only ones, and a fourth would deserve its own row.
//
// Runtime oracle (stock rustc 1.96.0, -O -C overflow-checks=on -C debug-assertions=on,
// #[inline(never)], black_box, catch_unwind, silent hook): 64 panics / 64 runs, sweep
// `x in 0..64`.
//
// The verifier MUST refuse this (exit 1, shift-overflow violation with a counterexample).
pub fn sd_shl_constfn_overflow(x: u64) -> u64 { let n = amount(8); x << n }
const fn amount(k: u32) -> u32 { k * 8 }
