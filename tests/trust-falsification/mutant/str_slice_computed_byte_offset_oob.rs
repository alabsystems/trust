// MUTANT: a `&str` range-slice at a COMPUTED byte offset. This one pins a real
// false-accept that shipped (found 2026-07-10, closed by 3f93cbb5bd), so it
// guards a soundness fix rather than a precision boundary.
//
// The byte-bounds here are proven WITHOUT `char_indices`: `s.as_bytes()` plus a
// raw `while i < bytes.len()` loop is an INDEPENDENT bounds credit, so the
// bounds VC `i + 1 <= len` discharges on its own. `str` is erased to `[u8]`
// during extraction, so once that credit exists nothing distinguishes this from
// a `&[u8]` slice and the UTF-8 char-boundary panic goes unmodeled — the
// pre-fix compiler reported `4 proved, 0 failed` (rc 0) while
// `drop_lead("fée")` panics at runtime ("byte index 2 is not a char boundary").
//
// It must now REFUTE via `[slice] FAILED`: a str `Index::index` callee carries
// the `::<__trust_str_index>` Self-identity marker across the erasure, and the
// RangeIndex body fails closed unless every explicit endpoint is provably a
// char boundary (a `char_indices()` yield, a literal 0, a provable `== len`).
//
// Contrast the twin `mutant/charindices_plus_one_boundary_oob.rs`: there the
// `i + 1` is arithmetic on a char_indices YIELD, which breaks the yield-trace,
// so the bounds credit is declined and it refutes through the BOUNDS lane
// instead. That twin cannot catch a regression of the marker; this one can,
// which is why both are gated.
#![crate_type = "lib"]

pub fn drop_lead(s: &str) -> &str {
    let bytes = s.as_bytes();
    let mut i = 0usize;
    while i < bytes.len() {
        if bytes[i] >= 0x80 {
            // `i + 1` can fall INSIDE a multi-byte char → slicing panics.
            return &s[i + 1..];
        }
        i += 1;
    }
    s
}

pub fn trigger() -> &'static str {
    // 'é' = 0xC3 0xA9 occupies bytes 1..3. First high byte is i=1, so this
    // returns `&s[2..]` — byte 2 is the continuation byte of 'é', NOT a char
    // boundary → runtime panic "byte index 2 is not a char boundary".
    drop_lead("fée")
}
