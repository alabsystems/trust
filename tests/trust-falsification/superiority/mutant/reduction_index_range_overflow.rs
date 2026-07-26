#![crate_type = "lib"]
// SOUNDNESS discriminator for the manual-index reduction (#50). Same shape as the proved
// `reduction_index_range`, but the trip count is K=1000 over a `[u8; 1000]`, so the
// accumulator bound `t <= 1000 * 255 = 255000` EXCEEDS u16::MAX (65535) — the reduction
// genuinely overflows. The bound IS emitted (the recognition fires) but is self-limiting:
// it leaves the per-iteration overflow obligation SAT, so the check is correctly retained
// (not vacuously eliminated). Proves the index-range bound is non-vacuous.
pub fn reduction_index_range_overflow(a: &[u8; 1000]) -> u16 {
    let mut t: u16 = 0;
    for i in 0..1000 {
        t += a[i] as u16;
    }
    t
}
