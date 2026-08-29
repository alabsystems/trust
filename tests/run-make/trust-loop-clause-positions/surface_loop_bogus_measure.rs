// A bogus termination measure on a `loop`: `0` never strictly decreases.
#![allow(dead_code)]
pub fn countdown(limit: u32) -> u32 {
    let mut n = limit;
    loop invariant n <= limit decreases 0 {
        if n == 0 {
            break;
        }
        n -= 1;
    }
    n
}
