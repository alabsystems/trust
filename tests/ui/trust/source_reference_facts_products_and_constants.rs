//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//@ forbid-output: incomplete for `source_reference_facts_products_and_constants::
//! Positive twin of the source reference facts (`docs/TCB.md`, "Source reference
//! facts"; `docs/DECISION_QUEUE.md`, 2026-11-07). Every function here must verify
//! with no runtime-checked row; the pinned summaries fail if one is no longer
//! verified or reported at all.
//!
//! trust-mc's operand-consumption gate (trust-mc c88bca8d7, in Trust's pin since
//! 8862c94337b) proves a load through an erased reference parameter in a CALL
//! SUMMARY, or the transport of an erased reference VALUE, only from live
//! `SourceReferenceFacts`. Before 2026-11-07 the compiler claimed only
//! `&bool`/`&int` parameters, so:
//!
//! * `a_is_zero` and `pair_is_zero` (a reference to a local struct / a tuple of
//!   integers, read through the trait default method's call summary) kept their
//!   assertion as runtime-checked: the gate declined the summary
//!   (`UnsupportedDirectCallSummary`). A DIRECT load through such a reference
//!   was already proved without facts, so it pins nothing and is not here;
//! * `use_good` (`f(&Good)`, the promoted borrow of a fieldless struct, lowered
//!   to a stamped `Undef(Ptr)`) kept it too: the call argument had no transport
//!   fact (`CallArgumentTransport, OperandConsumption`).
//!
//! The negative twins (`source_reference_facts_products_refused.rs`,
//! `source_reference_facts_maybe_uninit.rs`, `source_reference_facts_union_ref.rs`,
//! `source_reference_facts_callee_writes.rs`) must stay non-proved.

pub trait Score {
    fn score(&self) -> u8;
    fn is_zero(&self) -> bool {
        self.score() == 0
    }
}

pub struct A(pub u8);

impl Score for A {
    fn score(&self) -> u8 {
        self.0
    }
}

pub fn a_is_zero(a: &A) -> bool {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (instance discharge) out of 2 obligation(s)
    a.is_zero()
}

impl Score for (u8, u8) {
    fn score(&self) -> u8 {
        self.0 ^ self.1
    }
}

pub fn pair_is_zero(p: &(u8, u8)) -> bool {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (instance discharge) out of 2 obligation(s)
    p.is_zero()
}

pub trait Tr {
    fn m(&self) -> u32;
}

pub struct Good;

impl Tr for Good {
    fn m(&self) -> u32 {
        1
    }
}

pub fn f<T: Tr>(t: &T) -> u32 {
    t.m()
}

pub fn use_good() -> u32 {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (instance discharge) out of 2 obligation(s)
    f(&Good)
}
