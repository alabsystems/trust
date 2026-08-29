// The same loop, the same authored facts, written on `loop`.
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
