// GUARD RAIL for `loop_counter_over_slice_iter_now_proves.rs`. The `.iter()`
// form must inherit the SAME ZST exception as the direct form: `[(); usize::MAX]`
// is a valid slice, so this counter genuinely overflows on its last increment
// and the refusal is correct.
pub fn f(v: &[()]) -> usize {
    let mut n = 0usize;
    for _ in v.iter() {
        n += 1;
    }
    n
}
