#![crate_type = "lib"]
// Replacement coverage for the retired lossy-cast mutants (9f4b2c8417): a guard
// on the PRE-truncation value does not launder the truncated INDEX. For
// x > 300, `x as u8` (x % 256) still ranges over ALL of [0, 255], far beyond
// len 4 (runtime oracle: x=310 → "index out of bounds: the len is 4 but the
// index is 54", rc=101). Also pins the sound half of the disc/cast narrowing
// model: a source-range fact that excludes [0,255] must NOT vacuously discharge
// the post-truncation bounds VC. The verifier MUST refute (exit 1).
pub fn cast_trunc_guarded_index_oob(x: u32, a: &[u8; 4]) -> u8 {
    if x > 300 { a[(x as u8) as usize] } else { 0 }
}
