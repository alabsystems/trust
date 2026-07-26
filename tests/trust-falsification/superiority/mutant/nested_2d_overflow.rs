#![crate_type = "lib"]
// SOUNDNESS discriminator for the nested-loop (product) trip count (#50). Same shape as
// `nested_2d_sum`, but the accumulator is u8: the sum of 16 elements each up to 255 reaches
// 16*255 = 4080, which overflows u8 (MAX 255). The bound `t <= 4080` IS emitted (the product
// trip count fires), but it is self-limiting — 4080 exceeds u8::MAX, so the per-iteration
// overflow obligation stays SAT and the runtime check is correctly retained. Proves the
// product-trip-count bound is non-vacuous.
pub fn nested_2d_overflow(a: &[[u8; 4]; 4]) -> u8 {
    let mut t: u8 = 0;
    for i in 0..4 {
        for j in 0..4 {
            t += a[i][j];
        }
    }
    t
}
