// The reference surface: `while` already had a clause position.
#![allow(dead_code)]
pub fn countdown(limit: u32) -> u32 {
    let mut n = limit;
    while n > 0 invariant n <= limit decreases n {
        n -= 1;
    }
    n
}
