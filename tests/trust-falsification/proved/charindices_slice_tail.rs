// Trust R2 family 1 (heck `capitalize`): `&s[i..]` at a `char_indices()`-yielded
// `i` is panic-free — `i < s.len()` AND `s.is_char_boundary(i)` by the iterator
// contract, so BOTH the bounds and the str char-boundary panic are impossible.
// The corpus measurement found this exact idiom FALSE-REFUTED (heck 0.5.0,
// src/lib.rs:187). Mutant twins: charindices_plus_one_boundary_oob.rs (derived
// index), charindices_cross_string_oob.rs (wrong string).
#![crate_type = "lib"]

pub fn capitalize_tail(s: &str) -> &str {
    let mut char_indices = s.char_indices();
    if let Some((_, _c)) = char_indices.next() {
        if let Some((i, _)) = char_indices.next() {
            return &s[i..];
        }
    }
    ""
}
