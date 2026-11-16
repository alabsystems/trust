// Loop lanes (E4/E5 invariants) over params whose later versions are range-bounded.
#![allow(unused_assignments, clippy::all)]
// FALSE invariant: x wraps when s == 255 and n >= 1.
pub fn bug_l1_wrap_invariant(mut x: u8, n: u8) -> u8 {
    let s = x;
    let mut i = 0u8;
    while i < n
        invariant x >= s
    {
        x = x.wrapping_add(1);
        i += 1;
    }
    x
}
// FALSE invariant: the cast of a negative i16 into a u16 param.
pub fn bug_l2_cast_invariant(mut x: u16, y: i16, n: u8) -> u16 {
    let mut i = 0u8;
    while i < n
        invariant y >= 0
    {
        x = y as u16;
        i += 1;
    }
    x
}
// FALSE ensures through a loop with a wrapping param update.
pub fn bug_l3_wrap_post(mut x: u8, n: u8) -> u8 ensures result >= 1 || n == 0 {
    let mut i = 0u8;
    while i < n
        invariant i <= n
    {
        x = x.wrapping_add(1);
        i += 1;
    }
    x
}
// TRUE control.
pub fn ok_l4_true_invariant(mut x: u8, n: u8) -> u8 {
    let mut i = 0u8;
    while i < n
        invariant x <= 255
    {
        x = x.wrapping_add(1);
        i += 1;
    }
    x
}
