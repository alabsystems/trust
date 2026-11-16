//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ edition: 2024
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! PD-18 (docs/DECISION_QUEUE.md, "OPEN / PROPOSED 2026-09-30"): at a `become` return
//! block the clause's exit read happens BEFORE the tail callee runs. Here the callee sets
//! `detached` back to true, so neither clause may prove. Measured 2026-09-30: both stay
//! Unknown, in the primed and the unprimed spelling. A change that makes either PROVE is a
//! false proof.
#![feature(explicit_tail_calls)]
#![allow(incomplete_features)]

pub struct Storage {
    pub detached: bool,
}

#[inline(never)]
pub fn reattach(s: &mut Storage) {
    s.detached = true;
}

pub fn abort_then_reattach(s: &mut Storage)
//~^ NOTE Trust verification: 0 proved, 0 failed, 2 unknown
    ensures !s'.detached
{
    s.detached = false;
    become reattach(s);
}

pub fn abort_then_reattach_unprimed(s: &mut Storage)
//~^ NOTE Trust verification: 0 proved, 0 failed, 2 unknown
    ensures !s.detached
{
    s.detached = false;
    become reattach(s);
}
