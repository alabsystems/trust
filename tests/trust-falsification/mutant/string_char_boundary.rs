#![crate_type = "lib"]
// SOUNDNESS LOCK (String byte-vs-char-boundary). A `k <= s.len()` guard proves the
// BYTE bound for `&s[..k]` on an owned `String`, but String byte-slicing ALSO panics
// when `k` is not a UTF-8 char boundary: `s = "é"` is the 2-byte 0xC3 0xA9, so
// `k == 1` satisfies `1 <= 2` yet `&s[..1]` panics ("byte index 1 is not a char
// boundary"). Trust models no char-boundary obligation, so recovering the String's
// byte length here would FALSE-PROVE that panic. `is_owned_slice_container_name`
// therefore admits `Vec` ONLY — the verifier MUST fail closed for a String index.
pub fn string_char_boundary(s: &str, k: usize) -> usize {
    let owned = s.to_string();
    if k <= owned.len() { (owned[..k]).len() } else { 0 }
}
