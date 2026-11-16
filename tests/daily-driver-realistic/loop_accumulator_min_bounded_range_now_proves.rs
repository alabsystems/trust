// CLOSED 2026-09-19. A separate accumulator under a `min`-BOUNDED range:
//
//     for _ in 0..k.min(10) { n += 1; }
//
// `range_trip_count_upper_bound` required a LITERAL end, so this had no trip
// count at all (`TRUST_ACC_DEBUG=1` printed nothing) while the literal twin
// `0..10` proved. It now falls back to `bound_operand_upper_bound` — the same
// `min(a, c) <= c` recogniser the manual-counter path already used.
//
// SOUND BY THE FUNCTION'S OWN CONTRACT: it returns an UPPER bound on the
// iteration count, `min(a, c) <= c` makes `c` one, and the consumer emits
// `acc <= init + K * per_max` — so a LARGER K gives a LARGER, weaker bound.
// Over-approximating K can only cost completeness. (`max` stays out: it is a
// LOWER bound.)
//
// The self-limiting property is unchanged and its guard rail still refuses:
// `loop_accumulator_correct_refusal_bounded_addend_really_overflows.rs`.
pub fn f(k: usize) -> usize {
    let mut n = 0usize;
    for _ in 0..k.min(10) {
        n += 1;
    }
    n
}
