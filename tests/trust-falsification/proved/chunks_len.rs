#![crate_type = "lib"]
// `for c in s.chunks(3)` — companion to windows_len.rs for the `<[T]>::chunks(n)`
// sub-slice iterator. `chunks(3)` is total here (literal size `>= 1`, so the
// constructor's `assert!(n != 0)` is discharged); `Chunks::next` runs no user code.
// Reads `c.len()` (total `::slice::len` → fresh-symbolic) and sums with
// `wrapping_add`, proving panic-free under the default strict policy.
pub fn chunks_len(s: &[u32]) -> u32 {
    let mut t = 0u32;
    for c in s.chunks(3) {
        t = t.wrapping_add(c.len() as u32);
    }
    t
}
