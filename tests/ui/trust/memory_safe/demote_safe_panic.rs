//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=memory-safe --crate-type=lib
//@ dont-check-compiler-stderr
//@ build-pass
//
// The explicit memory-safe policy demotes a reachable bounds panic in a safe
// function to a visible warning. It never grants proof credit, but it permits
// otherwise-correct memory-safe Rust to compile.
pub fn unguarded_index(s: &[u8], i: usize) -> u8 {
    //~^ WARN Trust Level 0 safety verification incomplete for `demote_safe_panic::unguarded_index`
    s[i]
}
