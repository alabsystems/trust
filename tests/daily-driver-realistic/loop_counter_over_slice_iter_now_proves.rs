// CLOSED 2026-09-19, one hop after `loop_counter_over_a_slice_now_proves.rs`.
//
//     for _ in v.iter() { n += 1; }
//
// `for _ in v` reached the slice because its desugar is `into_iter(v)`. The
// `.iter()` form desugars to `into_iter(v.iter())`, so the source trace stopped
// on the `slice::Iter` STRUCT — an Adt, not a slice — and yielded no trip count.
//
// `trace_iter_to_into_iter_arg` now hops THROUGH `<[T]>::iter`. `slice::Iter`
// yields exactly `v.len()` items, the same count `into_iter(v)` gives, so the
// hop preserves the trip count exactly — the property that function's own header
// already relied on: `slice::Iter::next` "consumes and never reseats, so every
// element it yields is an element of that collection and it yields at most `len`
// of them".
//
// The hop is gated by the same `call_dest_hop` as every other hop there, so a
// RESEATED iterator local is refused rather than traced to the first
// constructor — the `windows_reseat` hazard its sibling in container_len.rs
// records, where an ungated trace both refuted a correct program and proved a
// panicking one.
//
// ZST guard rail: `loop_counter_over_a_zst_slice_iter_must_refuse.rs`.
pub fn f(v: &[u32]) -> usize {
    let mut n = 0usize;
    for _ in v.iter() {
        n += 1;
    }
    n
}
