#![crate_type = "lib"]
// SOUNDNESS discriminator for the shift-scaled reduction bound (#50, `addend_per_iteration_bound`
// case (c)). Same shape as `shift_scaled_reduction`, but each addend is `(x as u16) << 8`: a
// single element shifts to at most `255 << 8 = 65280` (fits u16), but the SUM of just two such
// addends already exceeds u16::MAX (65280 + 65280 = 130560 > 65535), so the accumulator
// genuinely overflows on the second iteration. The bound `t <= 4 * 65280 = 261120` IS emitted
// (case (c) fires), but it is self-limiting — 261120 far exceeds u16::MAX, so the per-iteration
// overflow obligation stays SAT and the runtime check is correctly retained. Proves the
// shift-scaled `M = MAX(ELEM) * 2^k` bound is non-vacuous.
pub fn shift_scaled_overflow(a: &[u8; 4]) -> u16 {
    let mut t: u16 = 0;
    for &x in a {
        t += (x as u16) << 8;
    }
    t
}
