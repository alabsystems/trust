// The reference surface: the NATIVE `loop` clause position (D2).
#![allow(dead_code)]
pub fn countdown(limit: u32) -> u32 {
    let mut n = limit;
    loop invariant n <= limit decreases n {
        if n == 0 {
            break;
        }
        n -= 1;
    }
    n
}
