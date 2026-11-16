//! **Non-exportable notice, transport control — the REFUSED importer.**
//!
//! Names `m::countdownSum` itself. The path resolves and type-checks against
//! the aux's encoded `fn_sig`; codegen then needs the body, the aux emitted no
//! linkable symbol for a Clean-origin def, and the guarded extern
//! `optimized_mir` arm runs `trust_clean_extern_readmission` first. Against
//! the pristine rlib that provider recognises the notice and refuses; against
//! the rlib whose notice was relabelled as a certificate it must refuse too.
//! This file must NEVER build.

extern crate trust_bignum;
extern crate wf_notice_aux;

fn main() {
    let out = wf_notice_aux::m::countdownSum(trust_bignum::Nat::from_u64(3));
    println!("direct={:?}", out.to_u64());
}
