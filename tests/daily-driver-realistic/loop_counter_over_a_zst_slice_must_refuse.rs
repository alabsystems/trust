// GUARD RAIL for `loop_counter_over_a_slice_now_proves.rs`. Identical program
// with a ZST element. It MUST stay refused: a `[(); usize::MAX]` slice is valid,
// so the counter genuinely reaches `usize::MAX` and the last `n += 1` overflows.
//
// This is the exception that makes the `len <= isize::MAX` bound sound for
// everything else, and the reason the new trip-count arm is gated on
// `ty_is_definitely_non_zst` rather than on "is a slice".
pub fn f(v: &[()]) -> usize {
    let mut n = 0usize;
    for _ in v {
        n += 1;
    }
    n
}
