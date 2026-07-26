#![crate_type = "lib"]
// MUTANT + DISCRIMINATING guard: replace `wrapping_add` with `+`. Each yielded
// window's `w.len()` is a fresh-symbolic (unconstrained) usize, so `w.len() as u32`
// is an unconstrained u32 and the running sum `t + (w.len() as u32)` can overflow.
// MUST be refused (exit 1). Guards that the yielded sub-slice length is a real
// unconstrained value — if the windows model mis-resolved it (e.g. forced it to a
// small constant), the add could not overflow and the mutant would falsely prove.
pub fn windows_len(s: &[u32]) -> u32 {
    let mut t = 0u32;
    for w in s.windows(2) {
        t = t + (w.len() as u32);
    }
    t
}
