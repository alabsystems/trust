#![crate_type = "lib"]
// Guarded negation: i32::MIN is the only value whose negation overflows.
pub fn delta_invert(n: i32) -> i32 {
    if n != i32::MIN { -n } else { i32::MAX }
}
