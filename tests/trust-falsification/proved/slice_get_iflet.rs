#![crate_type = "lib"]
// `if let Some(&x) = s.get(i)` — `<[T]>::get` is TOTAL (bounds-checks, returns
// `Option<&T>`, None on out-of-range, never panics). Modeled as a fresh-symbolic
// `Option` (a tracked nested aggregate, #46), so the exhaustive if-let lowers and
// proves panic-free under the default strict policy. (Superior to indexing `s[i]`,
// which rustc bounds-checks; `get` is the safe accessor and Trust proves it.)
pub fn slice_get_iflet(s: &[u32], i: usize) -> u32 {
    if let Some(&x) = s.get(i) {
        x
    } else {
        0
    }
}
