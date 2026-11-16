#![crate_type = "lib"]
// MUTANT of `proved/loop_empty_sibling_loop.rs`: 300 increments of a `u8`. The
// accumulator lane used to multiply the trip counts of EVERY loop in the function, so
// the empty sibling `0..0` made the product 0 (`c <= 0`) and this was proved.
pub fn empty_sibling() -> u8 {
    let mut c = 0u8;
    for _ in 0..0u32 {}
    for _ in 0..300u32 {
        c += 1;
    }
    c
}
