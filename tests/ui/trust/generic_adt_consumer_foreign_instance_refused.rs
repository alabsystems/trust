//@ revisions: assume_default verify_default assume_certify verify_certify
//@ needs-trust-verify
//@ edition: 2024
//@ aux-build: unverified_edge_instance_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Copt-level=0
//@[assume_certify] compile-flags: -Ztrust-policy=certify
//@[verify_certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
#![feature(register_tool)]
#![register_tool(trust)]
#![allow(dead_code)]
// Trust (ADT-IMPL-DISCHARGE-1): a consumer must charge the instantiated local
// impl's edge, even though W<u32> has no foreign type leaf. The auxiliary impl
// returns a constant, but was built verify-off; no proof was established here.
// Both an ordinary verified caller and a revoked assume_total caller must
// refuse. The original unverified_edge_generic_instance fixture remains intact;
// unverified_edge_generic_instance_controls is the local-impl positive control.
extern crate unverified_edge_instance_dep as dep;
use dep::Act2;

struct W<T>(T);

impl<T: Act2> Iterator for W<T> {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        Some(self.0.a2())
    }
}

#[cfg_attr(any(assume_default, assume_certify), trust::assume_total)]
#[inline(never)]
pub fn consume() -> u32 {
    //[assume_default]~^ ERROR Trust strict verification failed for `generic_adt_consumer_foreign_instance_refused::consume`
    //[verify_default]~^^ ERROR Trust strict verification failed for `generic_adt_consumer_foreign_instance_refused::consume`
    //[assume_certify]~^^^ ERROR Trust strict verification failed for `generic_adt_consumer_foreign_instance_refused::consume`
    //[verify_certify]~^^^^ ERROR Trust strict verification failed for `generic_adt_consumer_foreign_instance_refused::consume`
    W(5u32).take(1).count() as u32
}
