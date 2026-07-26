#![crate_type = "lib"]
// MUTANT of superiority/proved/guarded_mut_slice_bound.rs: drops the
// `i < dst.len()` guard. `dst[i] = 0` can write OUT OF BOUNDS for any i >= len, so
// default mode must NOT eliminate the bounds check (the bug stays caught at
// runtime) — proving the elimination above is non-vacuous.
pub fn guarded_mut_slice_bound(dst: &mut [u8], i: usize) {
    dst[i] = 0;
}
