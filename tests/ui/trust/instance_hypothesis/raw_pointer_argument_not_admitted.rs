//~ NOTE "proved":0,"failed":1,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":2}
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
//! OD-1 phase 1 control: an open dispatch with a raw-pointer argument is NOT admitted
//! (design §2.3: the callee may write through it to anything). Line 1 pins the phase-0
//! shape: the fatal absent-callee row, published `failed`, and no hypothesis row.
pub trait Tr {
    fn m(&self, p: *const u8) -> u32;
}

pub fn f<T: Tr>(t: &T, p: *const u8) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    t.m(p)
}
