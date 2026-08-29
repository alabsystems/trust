// A bogus measure on the attribute surface: must produce an unproved
// termination obligation, not silence.
#![allow(dead_code)]
pub fn countdown(limit: u32) -> u32 {
    let mut n = limit;
    #[cfg_attr(trust_verify, trust::decreases(0))]
    loop {
        if n == 0 {
            break;
        }
        n -= 1;
    }
    n
}
