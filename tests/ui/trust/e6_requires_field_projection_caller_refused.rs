//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! E6 — the OTHER half of field-projected `requires`: THE BURDEN TRANSFERS.
//!
//! A precondition that only ever discharged the callee's own obligation would
//! be an assumption, not a contract. The point of authoring
//! `requires c.patch_size != 0` on the production function is that every caller
//! then owes it — by name, at its own call site, against its own actual.
//!
//! `guarded` in `e6_requires_field_projection.rs` proves the positive half:
//! a dominating `c.patch_size != 0` discharges the transferred obligation.
//! This file is the negative half. `unguarded` calls the same function with its
//! own unconstrained parameter, so `c.patch_size != 0` is not derivable at the
//! call site and the caller must be REFUSED.
//!
//! Both halves are required. A projection that could not be rebound at the call
//! site would leave the callee's `c*.0` FREE in `¬P[σ]`, which is trivially SAT — so the
//! call would be reported as a violation whether or not the caller guards it,
//! and the positive file alone cannot tell that apart from a working transfer.
//! Conversely, a projection rebound to the WRONG place would let this file pass.

pub struct VitConfig {
    pub patch_size: usize,
    pub image_size: usize,
}

pub fn grid_of(c: &VitConfig) -> usize
    requires c.patch_size != 0
{
    c.image_size / c.patch_size
}

// NO guard. The transferred burden cannot be discharged here.
pub fn unguarded(c: &VitConfig) -> usize {
//~^ ERROR Trust strict verification failed for `e6_requires_field_projection_caller_refused::unguarded`
    grid_of(c)
}
