// The verified dependent of trust-proof-session-dependency-mir: it declares the
// dependency in its bundling scope, so the dependency's encoded MIR is what its
// verification reads for these two calls.

extern crate session_dep;

pub fn sum(a: u32, b: u32) -> u32 {
    session_dep::clamp_sum(a, b)
}

pub fn halves(a: u32) -> u32 {
    session_dep::quarters(a)
}
