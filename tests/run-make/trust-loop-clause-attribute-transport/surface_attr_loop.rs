// The same loop, the same authored facts, written on the STOCK-SURVIVING
// attribute transport. This file also compiles on stock rustc 1.97.1, where
// the `cfg_attr` is stripped before expression-attribute feature gating.
#![allow(dead_code)]
pub fn countdown(limit: u32) -> u32 {
    let mut n = limit;
    #[cfg_attr(trust_verify, trust::loop_invariant(n <= limit))]
    #[cfg_attr(trust_verify, trust::decreases(n))]
    loop {
        if n == 0 {
            break;
        }
        n -= 1;
    }
    n
}
