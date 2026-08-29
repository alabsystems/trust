// Positive owner-boundary guard: associated functions, like free functions,
// are exact contract-inventory owners. This must produce the same live loop
// obligations as `surface_attr_loop.rs`; a broad fail-closed check that
// accidentally rejected every non-free body would fail the run-make test.
#![allow(dead_code)]

pub struct Counter;

impl Counter {
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
}
