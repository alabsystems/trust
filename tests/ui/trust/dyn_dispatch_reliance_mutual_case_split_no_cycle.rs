//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! REGRESSION: an INDIRECT case-split cycle (A's target is B, B's target is A)
//! must decline, not abort the compilation.
//!
//! This is the fixture for `RELIANCE_IN_PROGRESS`, and it is the one mutant in
//! this family whose failure mode is not "a wrong verdict" but "no verdict at
//! all".
//!
//! The shape: verifying `<A as Step>::step` finds one in-bundle coercion
//! (`&B -> &dyn Step`), so its case split is `{B}` and it FORCES
//! `trust_proof_results` for `<B as Step>::step`. Verifying that in turn finds
//! `&A -> &dyn Step`, case-splits on `{A}`, and forces `<A as Step>::step` —
//! which is the query already on the stack. That is an E0391 query cycle, and a
//! cycle ABORTS compilation; it does not degrade to a conservative answer.
//!
//! The `def_id == root_def_id` self-check cannot see this: in A's frame the
//! target is B, and in B's frame the target is A. Neither is ever equal to its
//! own root. Only a re-entrancy set spanning the whole resolution catches it.
//!
//! Expected: both impls FAIL (each case split declines on re-entry, so each keeps
//! its `dyn` obligation, and then each sees the other unproved). What is being
//! asserted is not the failure text but that a VERDICT IS REACHED — if this file
//! ever ICEs or reports a query cycle, the guard has regressed.
//!
//! The mutual recursion here also never terminates at runtime. That is
//! deliberate and harmless: panic-freedom is a SAFETY property and divergence
//! satisfies it vacuously, which is precisely why neither certificate may ever
//! be extended to total correctness.
#![allow(dead_code)]

pub trait Step {
    fn step(&self, n: u32) -> u32;
}

pub struct A;
pub struct B;

impl Step for A {
    fn step(&self, n: u32) -> u32 {
        let next: &dyn Step = &B;
        next.step(n.wrapping_sub(1))
        //~^^^ ERROR Trust strict verification failed
    }
}

impl Step for B {
    fn step(&self, n: u32) -> u32 {
        let next: &dyn Step = &A;
        next.step(n.wrapping_sub(1))
        //~^^^ ERROR Trust strict verification failed
    }
}
