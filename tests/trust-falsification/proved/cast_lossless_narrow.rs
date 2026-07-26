#![crate_type = "lib"]
// A lossless narrowing cast: `x & 0xFF` is in [0, 255], so `as u8` loses no
// information. HISTORY: the -full lane used to PROVE a fabricated lossy-cast
// obligation here; since 9f4b2c8417 defined int `as` casts emit NO obligation
// at all (they are defined Rust semantics and cannot panic), so this is now a
// zero-obligation drop-in ACCEPTANCE fixture (no verification headline).
pub fn cast_lossless_narrow(x: u32) -> u8 {
    (x & 0xFF) as u8
}
