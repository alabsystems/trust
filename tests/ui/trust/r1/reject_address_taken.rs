//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ check-fail
// `scaled`'s address is taken (returned as a fn pointer), so it is reachable via an UNCOUNTABLE
// indirect call — a downstream holder of the pointer can invoke it with any divisor. R1 must
// REFUSE even though the one direct call passes a safe divisor. The crate-wide MIR scan marks
// `scaled` address-taken (its `FnDef` appears outside a direct-`Call` func slot), so coverage is
// not Total: the div-by-zero stays a failure and the build is rejected.
fn scaled(x: u32, divisor: u32) -> u32 { //~ ERROR Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed for
    x / divisor
}
pub fn api(x: u32) -> u32 {
    scaled(x, 4)
}
pub fn leak() -> fn(u32, u32) -> u32 {
    scaled
}
