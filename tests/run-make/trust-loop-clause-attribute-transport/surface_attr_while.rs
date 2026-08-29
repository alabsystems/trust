// The attribute transport on `while`, so the surface is not `loop`-only.
#![allow(dead_code)]
pub fn countdown(limit: u32) -> u32 {
    let mut n = limit;
    #[cfg_attr(trust_verify, trust::loop_invariant(n <= limit))]
    #[cfg_attr(trust_verify, trust::decreases(n))]
    while n > 0 {
        n -= 1;
    }
    n
}
