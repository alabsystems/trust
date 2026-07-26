#![crate_type = "lib"]
// Dot product / multiply-accumulate, proved BY DEFAULT (#50). Both per-iteration checks
// discharge: the widening multiply `(a[i] as u32)*(b[i] as u32)` cannot overflow u32 (each
// factor <= 255, product <= 65025) — via the interval BV-mul lane — AND the accumulator add
// `t += prod` is bounded by `t <= K * (factor1_max * factor2_max) = 4 * 65025 = 260100 <
// u32::MAX` via the Mul-addend accumulator bound (`addend_per_iteration_bound`). rustc
// retains both runtime checks; Trust eliminates both. Pairs with the genuine-overflow
// mutant `dot_product_overflow`.
pub fn dot_product(a: &[u8; 4], b: &[u8; 4]) -> u32 {
    let mut t: u32 = 0;
    for i in 0..4 {
        t += (a[i] as u32) * (b[i] as u32);
    }
    t
}
