#![crate_type = "lib"]
// A PARAMETER HAS ZERO DEFS IN `body.blocks`. The shift amount arrives as an argument, so
// its entry definition is not a statement in any basic block: a def-counter that walks
// blocks sees ZERO defs for `n`. "No defs found" must NOT read as "unique def" or
// "foldable slot" — absence of a def is absence of knowledge, and `n` is unconstrained.
//
// This is the exact shape a previous audit round missed by enumerating CALLERS of one
// resolver instead of the SHAPE (any predicate counting or resolving a local's defs). The
// unconstrained shift is refutable from the parameter alone; a verifier that silently
// treats the empty def set as agreement certifies it.
//
// NOT THE FIRST ROW OF ITS CLASS, and it should not be read as one: the single-operand
// spelling `1u64 << k` has been in the corpus as `mutant/left_shift_guarded.rs` since
// before this file, and the obligation it raises is the same `Lt(k, 64)`. What this row
// adds is adjacency — it is the ZERO-DEF end of a def-count family whose two-def end is
// `mutant/sd_shl_two_def_branch.rs` and whose one-constant-def end is
// `mutant/sd_shl_const_generic_overflow.rs`, so the three can be read together.
//
// Runtime oracle (stock rustc 1.96.0, -O -C overflow-checks=on -C debug-assertions=on,
// #[inline(never)], black_box, catch_unwind, silent hook): 64 panics / 128 runs, sweep
// `n in 0..128` with `x = n as u64`. The panics are exactly `n >= 64`.
//
// The verifier MUST refuse this (exit 1, shift-overflow violation with a counterexample).
pub fn sd_shl_param_unbounded(x: u64, n: u32) -> u64 { x << n }
