#![crate_type = "lib"]
// Subtract two i64 values widened to i128. A difference of two i64-range values
// lies in [-2^64, 2^64], far inside i128, so the raw `-` cannot overflow: -full
// PROVES the no-overflow obligation by recognizing both operands as i64->i128
// sign-extensions. The exact-geometric-predicate (orient2d) subtraction idiom.
// Pairs with mutant/i128_widened_sub.rs.
pub fn i128_widened_sub(a: i64, b: i64) -> i128 {
    (b as i128) - (a as i128)
}
