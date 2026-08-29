//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-name=t --crate-type=lib
//@ rustc-env: TRUST_R1_TRACE=1
//@ normalize-stderr: "formula=.* freevars=\{[^}]*\}" -> "formula=$$FORMULA freevars=$$FREEVARS"
//@ normalize-stderr: "sealed [0-9a-f]{64}" -> "sealed $$DIGEST"
//@ check-pass
//
// CONTROL for `caller_closure_key_space_collision.rs`: byte-for-byte the same
// program with the module renamed `t` -> `u`, so no nesting eats exactly one
// segment. Here the two producers' key spaces ARE disjoint —
//
//   RAW  = {`u::helper`, `helper`}       (`… : found Failed VC` prefixes)
//   SEAM = {`t::u::helper`, `t::helper`} (`stored flip key='…'`)
//
// — which is the OTHER observed state of the pair. The ordinary shape loses the
// lookup (a raw key never equals the same DefId's seam key); only the shadowing
// shape in the sibling fixture turns that loss into a WRONG-DefId hit.
#![allow(dead_code)]
mod u {
    pub(crate) fn helper(x: u32, d: u32) -> u32 {
        x / d
    }
    pub(crate) fn call() -> u32 {
        helper(10, 5)
    }
}
fn helper(x: u32, d: u32) -> u32 {
    x / d
}
fn call2() -> u32 {
    helper(20, 4)
}
fn go() {
    let _ = u::call();
    let _ = call2();
}
