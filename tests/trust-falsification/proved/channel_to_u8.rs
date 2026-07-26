#![crate_type = "lib"]
// Guarded narrowing cast: a colour channel bounded to <= 255 fits u8.
// Since 9f4b2c8417 defined int `as` casts emit NO obligation (defined Rust
// semantics, cannot panic) — zero-obligation drop-in ACCEPTANCE fixture.
pub fn channel_to_u8(v: u32) -> u8 {
    if v <= 255 { v as u8 } else { 255 }
}
