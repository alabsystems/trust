// CLOSED 2026-09-19. A counter over a slice:
//
//     for _ in v { n += 1; }        // v: &[u32]
//
// `total_loop_iterations` had a RANGE arm and a FIXED-ARRAY arm and nothing
// else, so a slice source yielded no trip count and a `usize` counter over it
// was refuted as an unbounded overflow.
//
// A slice's length is symbolic but has a CONSTANT upper bound whenever its
// element is provably non-ZST — and both that bound and its ZST exception were
// ALREADY in this crate's model, in `conjoin_slice_len_bounds` /
// `nonzst_slice_len_vars` (`type_ranges.rs:915`): "`size_of::<T>() >= 1` forces
// `len <= isize::MAX`; a ZST container can reach `usize::MAX`". The new arm
// reuses that lane's own predicate and constant rather than minting a second
// pair that could drift.
//
// The ZST case keeps its refusal, which is CORRECT and not incomplete:
// `[(); usize::MAX]` is a valid slice and a `usize` counter over it genuinely
// DOES overflow on the last increment. Its guard rail is
// `loop_counter_over_a_zst_slice_must_refuse.rs`.
pub fn f(v: &[u32]) -> usize {
    let mut n = 0usize;
    for _ in v {
        n += 1;
    }
    n
}
