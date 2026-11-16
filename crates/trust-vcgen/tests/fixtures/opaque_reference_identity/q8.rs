// B'' index form: q8_index(1, 2, &[0; 4]) panics with index out of bounds
// (two different recovered pointers are unequal, so i = 9).
pub fn q8_index(x: usize, y: usize, t: &[u8; 4]) -> u8 {
    let p = x as *const u8;
    let q = y as *const u8;
    let i = if p == q { 0 } else { 9 };
    t[i]
}

// q9_div(1, 2) panics with attempt to divide by zero.
pub fn q9_div(x: usize, y: usize) -> u32 {
    let p = x as *const u8;
    let q = y as *const u8;
    let d: u32 = if p == q { 1 } else { 0 };
    100 / d
}
