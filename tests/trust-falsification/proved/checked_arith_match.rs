#![crate_type = "lib"]
// The idiomatic safe-overflow pattern: `match a.checked_add(b) { Some(v) => v,
// None => 0 }`. `checked_add` is TOTAL — it returns `Option<u32>` (None on
// overflow) and NEVER panics — so it is modeled as a fresh-symbolic `Undef`
// `Option<u32>` (a scalar-field aggregate the discriminant machinery tracks). The
// exhaustive match is panic-free, so the whole function proves under
// the default strict policy (strictly superior to rustc, which keeps the overflow
// check on a plain `a + b`).
pub fn checked_arith_match(a: u32, b: u32) -> u32 {
    match a.checked_add(b) {
        Some(v) => v,
        None => 0,
    }
}
