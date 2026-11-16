//@ revisions: trait_impl_ref_self trait_impl_ref_self_certify trait_impl_self_field
//@ revisions: inherent_ref_self
//@ needs-trust-verify
//@ check-fail
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@[trait_impl_ref_self_certify] compile-flags: -Ztrust-policy=certify
//@ edition: 2021
//@ dont-check-compiler-stderr
#![crate_type = "lib"]
//! **The negative twin of `ensures_adt_param_json_wire_no_ice.rs`.**
//!
//! Same flags and shapes — an `ensures` on a trait impl method taking `&self`
//! (default policy and `certify`), one reading a field through `&self`, and an
//! inherent `&self` method — with a clause the body does NOT satisfy. Each must
//! stay REJECTED: exit 1 with the strict-verification error naming the method,
//! and a crate summary with nothing verified and nothing proved.
//!
//! What this pins: the fix over there only changes how a help line spells a
//! parameter type (untrimmed, so building it arms no diagnostic assertion). It
//! must not — and does not — make a trait impl method's `ensures` go unchecked:
//! the clause is still a `Postcondition` obligation of the method, and a false
//! one still fails the build on the JSON wire. There is no pass directive
//! beyond `check-fail`, so compiletest requires exit 1 exactly; an ICE (101)
//! fails this file as it fails the positive one.
//!
//! This file is fix-INSENSITIVE by construction (the strict `error:` satisfies
//! `must_produce_diag` on its own); it is the soundness control. It does not pin
//! `failed` versus `unknown`: MEASURED on stage 1 of `bd8681c2628`, the constant
//! clauses are refuted (`failed`) while the field clause is reported unproved
//! (`unknown`), and either one refuses the build. The pins are RAW annotations
//! for the reason the positive file gives.

#[cfg(any(trait_impl_ref_self, trait_impl_ref_self_certify, inherent_ref_self))]
pub struct S;

#[cfg(any(trait_impl_ref_self, trait_impl_ref_self_certify))]
pub trait Get {
    fn get(&self) -> u32;
}

#[cfg(any(trait_impl_ref_self, trait_impl_ref_self_certify))]
impl Get for S {
    fn get(&self) -> u32
        ensures result == 8
    {
        7
    }
}

#[cfg(trait_impl_self_field)]
pub struct R {
    pub x: u32,
}

#[cfg(trait_impl_self_field)]
pub trait Read {
    fn read(&self) -> u32;
}

#[cfg(trait_impl_self_field)]
impl Read for R {
    fn read(&self) -> u32
        ensures result == self.x
    {
        self.x.wrapping_add(1)
    }
}

#[cfg(inherent_ref_self)]
impl S {
    pub fn get(&self) -> u32
        ensures result == 8
    {
        7
    }
}

//[trait_impl_ref_self]~? RAW Trust strict verification failed for `<ensures_adt_param_json_wire_violated_stays_rejected::S as ensures_adt_param_json_wire_violated_stays_rejected::Get>::get`: 2 obligation(s) were not fully verified
//[trait_impl_ref_self]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"ensures_adt_param_json_wire_violated_stays_rejected","functions_analyzed":1,"functions_verified":0,"total_proved":0
//[trait_impl_ref_self_certify]~? RAW Trust strict verification failed for `<ensures_adt_param_json_wire_violated_stays_rejected::S as ensures_adt_param_json_wire_violated_stays_rejected::Get>::get`: 2 obligation(s) were not fully verified
//[trait_impl_ref_self_certify]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"ensures_adt_param_json_wire_violated_stays_rejected","functions_analyzed":1,"functions_verified":0,"total_proved":0
//[trait_impl_self_field]~? RAW Trust strict verification failed for `<ensures_adt_param_json_wire_violated_stays_rejected::R as ensures_adt_param_json_wire_violated_stays_rejected::Read>::read`: 2 obligation(s) were not fully verified
//[trait_impl_self_field]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"ensures_adt_param_json_wire_violated_stays_rejected","functions_analyzed":1,"functions_verified":0,"total_proved":0
//[inherent_ref_self]~? RAW Trust strict verification failed for `ensures_adt_param_json_wire_violated_stays_rejected::S::get`: 2 obligation(s) were not fully verified
//[inherent_ref_self]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"ensures_adt_param_json_wire_violated_stays_rejected","functions_analyzed":1,"functions_verified":0,"total_proved":0
