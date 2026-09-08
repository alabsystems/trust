#![crate_type = "lib"]
// A FOLDED-TO-FALSE `Assert` REACHED THROUGH MONOMORPHIZATION. `shl_by::<64>` panics on
// EVERY input, yet rustc's deny-by-default `arithmetic_overflow` lint NEVER FIRES: inside
// the generic body `N` is symbolic, and the lint runs BEFORE monomorphization. The naive
// spelling `x << 64` is a compile ERROR and therefore can never reach Trust at all — this
// const-generic route is how a folded-to-`false` `Assert` condition actually arrives, and
// it compiles with zero warnings.
//
// WHY IT IS A GATE FIXTURE. A const evaluator that admits an `Assert` because its
// condition folded to a CONSTANT — rather than because the folded constant EQUALS the
// terminator's `expected` — certifies this. The generic body is (rustc 1.98.0-nightly,
// `-Zmir-opt-level=0 -C overflow-checks=on`)
//     _3 = Lt(const N, const 64_u32);
//     assert(move _3, "attempt to shift left by `{}`, which would overflow", const N)
// so at `N = 64` the condition folds to `false` while `expected` is `true`; constancy
// alone is not discharge.
//
// Runtime oracle (stock rustc 1.96.0, -O -C overflow-checks=on -C debug-assertions=on,
// #[inline(never)], black_box, catch_unwind, silent hook): 64 panics / 64 runs, sweep
// `x in 0..64`. It panics on 100% of the swept domain and rustc emits 0 warnings.
//
// The verifier MUST refuse this (exit 1, shift-overflow violation with a counterexample).
pub fn sd_shl_const_generic_overflow(x: u64) -> u64 { shl_by::<64>(x) }
#[inline(never)]
fn shl_by<const N: u32>(x: u64) -> u64 { x << N }
