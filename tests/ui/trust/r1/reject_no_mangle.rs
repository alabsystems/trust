//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ check-fail
// A private `#[no_mangle]` helper is callable from OUTSIDE the crate by its raw symbol (via an
// `extern` block in a downstream crate), so its callers are not enumerable — coverage is not
// Total and R1 must REFUSE, even though the one in-crate caller passes a safe divisor. The new
// oracle catches this via `codegen_fn_attrs().contains_extern_indicator()` (which `reachable_set`
// also covered): the div-by-zero stays a failure and the build is rejected.
#[no_mangle]
fn scaled(x: u32, divisor: u32) -> u32 { //~ ERROR Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed for
    x / divisor
}
pub fn api(x: u32) -> u32 {
    scaled(x, 4)
}
