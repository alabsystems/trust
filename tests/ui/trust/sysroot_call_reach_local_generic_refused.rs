//@ revisions: constant_full constant_assumed constant_strict panic_full panic_assumed panic_strict
//@ needs-trust-verify
//@ edition: 2024
//@ aux-build: sysroot_call_reach_local_generic_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Copt-level=0
//@[constant_strict] compile-flags: -Ztrust-policy=strict
//@[panic_strict] compile-flags: -Ztrust-policy=strict
//@ rustc-env:TRUST_CALL_REACH_DEBUG=1
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ regex-error-pattern: \[CALL_REACH\] open callee=.*count.*why=reaches .*next.*outside the sysroot.* in=sysroot_call_reach_local_generic_refused::run
//@ forbid-output: error[E0391]
//@ forbid-output: internal compiler error
//! Trust: the local callback is generic at a foundational `u32`, but its actual
//! dispatch target lives in a verify-off dependency. `Take::count` reaches it via
//! advance_by/SpecAdvanceBy/try_fold. The call walk must leave `count` OPEN and the
//! ROOT must refuse even if count is bundled and the generic next has a conditional
//! instance-hypothesis verdict. A helper's refusal alone cannot pass this test.
//!
//! The `_full` and `_strict` roots have no skip to revoke. The `_assumed` twins
//! also require the existing revocation warning. Keep the original constant-only
//! `unverified_edge_generic_instance.rs#adtimpl` and its known-red row until a new
//! compiler actually qualifies it; these additional cases do not replace it.
#![feature(register_tool)]
#![register_tool(trust)]
#![allow(dead_code)]

extern crate sysroot_call_reach_local_generic_dep as dep;

#[cfg(any(constant_full, constant_assumed, constant_strict))]
use dep::Constant as Act;
#[cfg(any(panic_full, panic_assumed, panic_strict))]
use dep::Panics as Act;

pub struct Lw<T>(T);

impl<T: Act> Iterator for Lw<T> {
    type Item = u32;

    #[inline(never)]
    fn next(&mut self) -> Option<u32> {
        //~^ WARN instance hypothesis row(s)
        Some(self.0.act())
    }
}

#[cfg_attr(any(constant_assumed, panic_assumed), trust::assume_total)]
#[inline(never)]
pub fn run() -> usize {
    //~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_generic_refused::run`
    //~| WARN Trust Level 0 safety verification incomplete for `sysroot_call_reach_local_generic_refused::run`
    //[constant_assumed]~| WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[panic_assumed]~| WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    Lw(5u32).take(1).count()
}
