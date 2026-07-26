#![crate_type = "lib"]
// Match a MULTI-FIELD enum variant: `E::A(a, b)` reads two fields of the same
// variant (each via `Downcast(A).Field(0|1)` through the `__vA_` tagged
// representation — `place_type` resolves these variant-qualified fields correctly,
// #46). Exhaustive + `wrapping_add` (no overflow obligation), so it proves under
// the default strict policy.
pub enum E {
    A(u32, u32),
    B,
}
pub fn match_multifield_enum(e: E) -> u32 {
    match e {
        E::A(a, b) => a.wrapping_add(b),
        E::B => 0,
    }
}
