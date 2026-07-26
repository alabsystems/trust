// MUTANT twin of proved/charindices_slice_tail.rs: the yield of `s` slices a
// DIFFERENT string `t` (`t = ""` panics OOB at runtime). The root-identity gate
// must decline the fold and the VC stay refutable.
#![crate_type = "lib"]

pub fn cross_tail<'a>(s: &str, t: &'a str) -> &'a str {
    let mut char_indices = s.char_indices();
    if let Some((_, _c)) = char_indices.next() {
        if let Some((i, _)) = char_indices.next() {
            return &t[i..];
        }
    }
    ""
}
