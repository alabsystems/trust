#![crate_type = "lib"]
// The correct twin of `mutant/loop_empty_sibling_zero_trip.rs`: 200 increments fit a
// `u8`. The bound on the add comes from the loop that CONTAINS it (`c <= 200`), not
// from a product over every loop in the function.
pub fn empty_sibling() -> u8 {
    let mut c = 0u8;
    for _ in 0..0u32 {}
    for _ in 0..200u32 {
        c += 1;
    }
    c
}
