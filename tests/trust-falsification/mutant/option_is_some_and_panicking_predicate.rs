#![crate_type = "lib"]
// `is_some_and` WHOSE PREDICATE CLOSURE ITSELF PANICS. The a3d
// `range_in_bounds` shape — `off.checked_add(len).is_some_and(closure)` — with
// the predicate indexing a 3-element table at `end % 8`. IT FAULTS: whenever
// the checked add succeeds and `(off + len) % 8 >= 3` the index is out of
// bounds and the predicate panics. The panic is INSIDE the closure the
// combinator calls, not in the caller's own body.
// Runtime oracle (stock rustc 1.96.0, -O -C debug-assertions=on,
// #[inline(never)], black_box, catch_unwind, silent hook): 31 panics / 51 runs,
// sweep `off in 0..12` x `len in 0..4` (48) plus the three boundary pairs
// (u64::MAX, 1), (u64::MAX, 0), (u64::MAX-1, 2). The two overflowing pairs do
// NOT panic — `checked_add` is None and `is_some_and` returns false without
// calling the predicate — while (u64::MAX, 0) does, at `end % 8 == 7`.
//
// See `mutant/option_and_then_inner_overflow.rs` for why this lane needed
// in-gate coverage at all. This row guards the `is_some_and` face specifically:
// its wrapper returns `bool`, not `Option<T>`, so it exercises a different
// return-slot shape in the direct-call summary than the `and_then`/`map` rows.
//
// The verifier MUST refuse this (exit 1, bounds violation with a counterexample).
pub fn is_some_and_panicking_predicate(off: u64, len: u64, file_len: u64) -> bool {
    let table = [1u64, 2, 3];
    off.checked_add(len)
        .is_some_and(|end| table[(end % 8) as usize] <= file_len)
}
