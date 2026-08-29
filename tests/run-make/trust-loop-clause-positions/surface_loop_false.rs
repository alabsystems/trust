// A blatantly false `loop` invariant. It must produce the invariant
// obligations and they must NOT be proved.
#![allow(dead_code)]
pub fn countdown(limit: u32) -> u32 {
    let mut n = limit;
    loop invariant n == 0 {
        if n == 0 {
            break;
        }
        n -= 1;
    }
    n
}
