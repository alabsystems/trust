//~ NOTE "description":"assertion: [trust-absent-callee-assumption] call to absent callee `<T as unsafe_body_not_admitted::Tr>::m`
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
//! OD-1 phase 1 control: a body with an unsafe operation admits NO site (design §2.3,
//! D33's fence: the havoc cannot model a body whose safety invariant may depend on what
//! the callee does). The open dispatch keeps its fatal absent-callee row, published
//! `failed` (class (c) of "L0 refutation rows"), and no instance-hypothesis row is
//! minted.
pub trait Tr {
    fn m(&self) -> u32;
}

pub fn f<T: Tr>(t: &T, p: *const u32) -> u32 {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^^ ERROR Trust strict verification failed
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^^ ERROR Trust strict verification failed
    let a = t.m();
    let b = unsafe { *p };
    a.wrapping_add(b)
}
