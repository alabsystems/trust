// MUTANT twin of proved/charindices_slice_tail.rs: `i + 1` is NOT a yielded
// index — it can fall mid-char (`"a\u{e9}x"`: yield i=1, i+1=2 is inside 'é')
// and the slice PANICS on the char-boundary check. The structural fold must
// decline (arithmetic breaks the yield trace) and the VC stay refutable.
#![crate_type = "lib"]

pub fn capitalize_tail_off(s: &str) -> &str {
    let mut char_indices = s.char_indices();
    if let Some((_, _c)) = char_indices.next() {
        if let Some((i, _)) = char_indices.next() {
            return &s[i + 1..];
        }
    }
    ""
}
