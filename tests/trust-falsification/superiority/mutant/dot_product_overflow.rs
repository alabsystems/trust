#![crate_type = "lib"]
// SOUNDNESS discriminator for the dot-product Mul-addend accumulator bound (#50). Same
// shape as `dot_product`, but u16 elements over length 1000 into a u32 accumulator: the
// per-iteration product `<= 65535*65535` is fine for u32, but the accumulator bound
// `t <= 1000 * 65535^2` vastly exceeds u32::MAX, so the accumulator add `t += prod`
// genuinely overflows and is correctly RETAINED (not statically eliminated). Proves the
// Mul-addend bound is self-limiting and non-vacuous.
pub fn dot_product_overflow(a: &[u16; 1000], b: &[u16; 1000]) -> u32 {
    let mut t: u32 = 0;
    for i in 0..1000 {
        t += (a[i] as u32) * (b[i] as u32);
    }
    t
}
