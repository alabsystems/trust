#![crate_type = "lib"]
// SOUNDNESS discriminator for the in-loop multiply (#50). Same loop shape as the proved
// `element_load_loop_square`, but the square stays in `u8`: `a[i] * a[i]` can be
// 255*255 = 65025, which overflows u8 (MAX 255) — a genuine overflow. Skipping the
// switch-discriminant context `Or` must NOT make this prove: the BV mul goal's operands
// are NOT structurally bounded below the product width (same-width u8*u8), so the goal
// stays SAT and the runtime check is correctly retained. Proves the context-Or skip is
// non-vacuous (it discharges only genuinely-safe widening multiplies).
pub fn element_load_loop_u8_square(a: &[u8; 4], out: &mut [u8; 4]) {
    for i in 0..4 {
        out[i] = a[i] * a[i];
    }
}
