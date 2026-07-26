#![crate_type = "lib"]
// Shift-scaled reduction (#50): a weighted sum where each element is left-shifted by a
// constant before accumulation — the canonical fixed-point / byte-packing idiom
// `t += (x as A) << k`. Each addend is `(x as u32) << 2 <= 255 << 2 = 1020`, so over the
// 4-element array `t <= 4 * 1020 = 4080 < u32::MAX`. rustc keeps the per-iteration
// add-overflow check; Trust discharges it BY DEFAULT via the accumulator bound with the
// per-iteration max `M = MAX(ELEM) * 2^k` (`addend_per_iteration_bound` case (c)). Pairs
// with the discriminating overflow mutant `shift_scaled_overflow`.
pub fn shift_scaled_reduction(a: &[u8; 4]) -> u32 {
    let mut t: u32 = 0;
    for &x in a {
        t += (x as u32) << 2;
    }
    t
}
