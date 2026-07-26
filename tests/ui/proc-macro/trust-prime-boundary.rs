//@ proc-macro: trust-prime-boundary.rs
//@ run-pass
//@ compile-flags: -Z trust-verify=off

extern crate trust_prime_boundary;

use trust_prime_boundary::{assert_trust_prime_boundary, emit_collapsed_native_contract};

// All tokens emitted by this proc macro have the same call-site span. Native
// signature and loop-clause parsers must still consume their exact payloads.
emit_collapsed_native_contract!();

// Exercise source-token -> proc-macro-token conversion and textual
// round-tripping. The auxiliary macro validates punctuation identity and
// jointness before returning an empty item stream.
assert_trust_prime_boundary!('__trust_prime);
assert_trust_prime_boundary!(x');
assert_trust_prime_boundary!(x'');
assert_trust_prime_boundary!(r#type');

// Before primes used `Lifetime(sym::trust_prime)` internally, the raw-ident
// fallback could satisfy this lifetime arm. It must instead match the
// standalone-quote arm.
macro_rules! assert_prime_is_not_lifetime {
    ($name:ident '__trust_prime) => {
        compile_error!("post-state prime aliased a legal Rust lifetime");
    };
    ($name:ident') => {};
}

macro_rules! assert_two_primes {
    ($name:ident'') => {};
}

assert_prime_is_not_lifetime!(x');
assert_prime_is_not_lifetime!(r#type');
assert_two_primes!(x'');
assert_two_primes!(r#type'');

macro_rules! classify {
    ('__trust_prime) => { 0usize };
    ($name:ident') => { 1usize };
}

fn main() {
    collapsed_native_contract(1, 1);
    assert_eq!(classify!('__trust_prime), 0);
    assert_eq!(classify!(x'), 1);
    assert_eq!(classify!(r#type'), 1);

    assert_eq!(stringify!(x'), "x'");
    assert_eq!(stringify!(x''), "x''");
    assert_eq!(stringify!(r#type'), "r#type'");
    assert_eq!(stringify!('__trust_prime), "'__trust_prime");
}
