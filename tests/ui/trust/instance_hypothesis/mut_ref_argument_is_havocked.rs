//~ NOTE "proved":0,"failed":1,"unknown":3,"timed_out":0,"skipped":3,"runtime_checked":0,"cached":0,"total":4}
//[advisory]~^ NOTE "proved":0,"failed":0,"unknown":2,"timed_out":0,"skipped":2,"runtime_checked":2,"cached":0,"total":4}
//[strict]~^^ NOTE "proved":0,"failed":0,"unknown":3,"timed_out":0,"skipped":2,"runtime_checked":1,"cached":0,"total":4}
//[certify]~^^^ NOTE "proved":0,"failed":0,"unknown":3,"timed_out":0,"skipped":2,"runtime_checked":1,"cached":0,"total":4}
//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//@[certify] check-fail
//! OD-1 phase 1, soundness of the relative encoding: an admitted call no longer carries
//! the absent-callee `Assert(false)` marker, so the havoc must stand for everything the
//! callee may do besides panic. `x` is 0 before the call and `t.m(&mut x)` may write
//! any `u8` through its `&mut` argument; `x + 1` therefore MAY overflow. Line 1 pins it
//! `failed` (no proved row): a model that kept the pre-call fact `x == 0` would prove
//! it. The site itself is admitted (one hypothesis row).
//!
//! `g` pins the NATIVE lane's half (the overflow row of `f` is also havocked by
//! trust-vcgen's own kill set, so it alone does not show the bridge's havoc): the
//! whole-function panic-freedom aggregate is solved over the bridge's trust-ir body, and
//! `panic!` is reachable exactly when the callee wrote `x`. Its pins (lines 2-4): no panic row
//! proved (advisory: both `runtime_checked`); without the havoc store through the `&mut` the
//! aggregate read the stale `x == 0` and was PROVED (mutation measured 2026-10-04).
pub trait Tr {
    fn m(&self, x: &mut u8);
}

pub fn f<T: Tr>(t: &T) -> u8 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    //[certify]~^^^^^ ERROR Trust certify verification failed for `mut_ref_argument_is_havocked::f`: 1 instance hypothesis row(s)
    let mut x: u8 = 0;
    t.m(&mut x);
    x + 1
}

pub fn g<T: Tr>(t: &T) -> u8 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    //[certify]~^^^^^ ERROR Trust certify verification failed for `mut_ref_argument_is_havocked::g`: 1 instance hypothesis row(s)
    let mut x: u8 = 0;
    t.m(&mut x);
    if x != 0 {
        panic!("written")
    }
    x
}
