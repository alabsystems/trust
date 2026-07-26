#![crate_type = "lib"]
// SOUNDNESS REGRESSION for the manual-index reduction (#50). The index `n % 4` is always
// in [0,4), but the loop is NOT driven by that index — it runs `k` from 0 to 100_000, so
// the self-add executes 100_000 times at a repeated in-bounds index and `t` genuinely
// overflows u16. A naive "index < array_len ⟹ at most len adds" bound would FALSELY prove
// `t <= 4*255`. `index_range_reduction_bound` requires the index to be an exclusive
// `Range::next` PAYLOAD (monotonic, each value once) — `n % 4` is a `Rem`, not a range
// payload, so NO bound is emitted and the real overflow is retained. The trip count must
// come from the loop's range structurally, never from the index's value range.
pub fn reduction_repeat_index(a: &[u8; 4], n: usize) -> u16 {
    let mut t: u16 = 0;
    let mut k: u32 = 0;
    while k < 100_000 {
        t += a[n % 4] as u16;
        k += 1;
    }
    t
}
