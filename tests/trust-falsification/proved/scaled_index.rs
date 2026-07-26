#![crate_type = "lib"]
// A stride/scaled index into a fixed-size array, `a[i * 2]` on `[i32; 8]` under a
// guard `i < 4`. rustc keeps a runtime bounds check; Trust discharges it
// STATICALLY. The bounds obligation pairs the SCALED index node `i*2` with the
// guard on `i`: `i < 4 ⟹ i <= 3 ⟹ i*2 <= 6 < 8` (the multiplicative lift via
// `Int.mul_le_mul_of_nonneg_right`), contradicting the violation `i*2 >= 8`. The
// clean CIC kernel certifies it by transitive chain over the `i*2` node.
// -full kernel-Certified (task #38 multiplicative-lift extension — superior to rustc).
pub fn scaled_index(a: &[i32; 8], i: usize) -> i32 {
    if i < 4 { a[i * 2] } else { 0 }
}
