#![crate_type = "lib"]
// Replacement coverage for the retired lossy-cast mutants (9f4b2c8417 made
// defined `as` truncation compile): a truncated value used as a DIVISOR.
// `(x as u8) as u32` is x % 256, which is 0 for every multiple of 256 (runtime
// oracle: x=256 → "attempt to divide by zero", rc=101). The verifier MUST
// refute the div-by-zero obligation (exit 1).
pub fn cast_trunc_div_zero(x: u32) -> u32 {
    1000 / ((x as u8) as u32)
}
