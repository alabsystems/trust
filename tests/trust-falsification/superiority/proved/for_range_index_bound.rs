#![crate_type = "lib"]
// SUPERIORITY: `for i in 0..s.len() { s[i] }` — rustc compiles this with a
// RETAINED runtime bounds check on every `s[i]`. Trust models the exclusive-range
// yield invariant (`0 <= i < s.len()` for the Range::next Some-payload) and
// statically PROVES the index in bounds, ELIMINATING the check. Default mode
// must report this fully proved (0 runtime-checked).
pub fn for_range_index_bound(s: &[u32]) -> u32 {
    let mut acc = 0u32;
    for i in 0..s.len() {
        acc ^= s[i];
    }
    acc
}
