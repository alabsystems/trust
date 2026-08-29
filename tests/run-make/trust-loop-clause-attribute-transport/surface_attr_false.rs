// A FALSE invariant on the attribute surface: false on entry (`n == limit`),
// vacuously preserved thereafter. Must still be ASKED at both program points.
#![allow(dead_code)]
pub fn countdown(limit: u32) -> u32 {
    let mut n = limit;
    #[cfg_attr(trust_verify, trust::loop_invariant(n == 0))]
    loop {
        if n == 0 {
            break;
        }
        n -= 1;
    }
    n
}
