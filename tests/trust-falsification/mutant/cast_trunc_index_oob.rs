#![crate_type = "lib"]
// Replacement coverage for the retired lossy-cast mutants (9f4b2c8417 made
// defined `as` truncation compile): the truncation itself cannot panic, but
// USING the truncated value as an index can. `x as u8` is x % 256 ∈ [0, 255],
// and the array has len 100, so `a[(x as u8) as usize]` panics whenever
// x % 256 >= 100 (runtime oracle: x=100 → "index out of bounds: the len is 100
// but the index is 100", rc=101). The verifier MUST refute (exit 1).
pub fn cast_trunc_index_oob(x: u32, a: &[u8; 100]) -> u8 {
    a[(x as u8) as usize]
}
