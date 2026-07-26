#![crate_type = "lib"]
// MUTANT of superiority/proved/bounded_copy.rs: drops the `min`, iterating to
// `src.len()` instead of `min(src.len(), dst.len())`. Now `dst[i]` can write OUT
// OF BOUNDS whenever `dst` is shorter than `src` (the loop is bounded by src's
// length, not dst's), so default mode must NOT eliminate the `dst[i]` bounds
// check — the bug stays caught at runtime, proving the elimination above is
// non-vacuous.
pub fn bounded_copy(dst: &mut [u8], src: &[u8]) {
    for i in 0..src.len() {
        dst[i] = src[i];
    }
}
