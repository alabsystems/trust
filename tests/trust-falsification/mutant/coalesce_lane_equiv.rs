#![crate_type = "lib"]
// MUTANT (coalescing / lane-equivalence): the bulk lane DROPS the wrap-tail
// fixup — the exact aterm bug, where the bulk wide-run path advanced the line
// WITHOUT the `blank_wide_wrap_tail()` the single-char path performs. Distilled
// to the bounds-safety refinement: the divergence shifts the tail write off the
// masked position, so the index escapes the row the single-char lane stayed
// within and goes OUT OF BOUNDS (`(col & 7) + 1` can be 8 on a [_; 8]). Trust
// must refute the bounds obligation (exit 1), proving the check is non-vacuous:
// a fast path that silently diverges from its reference is a compile-time error.
pub fn wrap_tail_write(row: &mut [u32; 8], col: usize, bg: u32) {
    row[(col & 7) + 1] = bg; // BUG: divergent index, can be 8 -> out of bounds
}
