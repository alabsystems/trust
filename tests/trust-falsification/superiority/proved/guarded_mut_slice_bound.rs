#![crate_type = "lib"]
// Guard-bounded MUTABLE-SLICE write (symbolic length): `i < dst.len()` makes the
// `dst[i] = 0` store provably in-bounds. Unlike `&[T]`, a `&mut [T]` re-reads its
// length via a `FakeForPtrMetadata` raw pointer (`&raw const *dst` + PtrMetadata),
// so this exercises the metadata-pointer slice-length tie AND the metadata-only
// addr_of suppression (the synthetic `&raw const` must not raise a spurious unsafe
// finding). Default mode must FULLY discharge the bounds check (superior to rustc,
// which keeps the runtime panic branch).
pub fn guarded_mut_slice_bound(dst: &mut [u8], i: usize) {
    if i < dst.len() {
        dst[i] = 0;
    }
}
