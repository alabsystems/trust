#![crate_type = "lib"]
// PROVED (Imp3, guard-connected slice index bounds): astream's `frame.rs` header reads. A
// `if buf.len() < HEADER_SIZE { return }` guard establishes `buf.len() >= HEADER_SIZE` on the
// fall-through, so a constant index `buf[i]` with `i < HEADER_SIZE` is in bounds. Before Imp3
// the guard's `buf.len()` (an `Rvalue::Len`) did not UNIFY with the index VC's slice-length
// symbol (guards.rs inlined only `PtrMetadata`, not `Rvalue::Len`), so the [slice] bound was
// ay-FAILED (counterexample `buf__slice_len = 0`). Imp3 inlines `Rvalue::Len(place)` to the
// same `{place}__slice_len` symbol, so the guard discharges the index. MUST verify (exit 0).
pub fn header_byte(buf: &[u8]) -> u8 {
    const HEADER_SIZE: usize = 12;
    if buf.len() < HEADER_SIZE {
        return 0;
    }
    buf[11] // in bounds: the guard gives buf.len() >= 12 > 11
}
