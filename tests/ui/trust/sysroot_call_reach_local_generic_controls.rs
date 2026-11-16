//@ revisions: forced_walk local_item nongeneric closure
//@ needs-trust-verify
//@ edition: 2024
//@ aux-build: sysroot_call_reach_local_generic_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Copt-level=0
//@ rustc-env:TRUST_CALL_REACH_DEBUG=1
//@[local_item] check-fail
//@[forced_walk] check-fail
//@[nongeneric] check-fail
//@[closure] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[forced_walk] regex-error-pattern: \[CALL_REACH\] closed\(walk\) callee=.*count.* in=sysroot_call_reach_local_generic_controls::run
//@[nongeneric] regex-error-pattern: \[CALL_REACH\] closed\(walk\) callee=.*count.* in=sysroot_call_reach_local_generic_controls::run
//@[closure] regex-error-pattern: \[CALL_REACH\] closed\(walk\) callee=.*count.* in=sysroot_call_reach_local_generic_controls::run
//@[local_item] regex-error-pattern: \[CALL_REACH\] closed\(prefilter\) callee=.*count.* in=sysroot_call_reach_local_generic_controls::run
//@ forbid-output: error[E0391]
//@ forbid-output: internal compiler error
//! Trust: actual full-verification controls for the local call-walk leaf; NO root
//! is skipped. In `forced_walk`, the foreign data-only associated Item makes the
//! conservative type prefilter decline, but `next::<u32>` calls only a LOCAL impl
//! and returns None. Its generic instance must settle and close by WALK, not by
//! a type-argument shortcut. `local_item` pins the ordinary prefilter route;
//! `nongeneric` preserves the non-generic local-body leaf. `closure` invokes a
//! local closure inside generic `next`: its parent arguments instantiate at u32,
//! and its callback dispatch reaches the same LOCAL impl as `forced_walk`.
//!
//! The `local_item` default-policy success claimed no new proof grade (it refuses
//! since the 2026-11-12 re-pin below). The existing
//! `unverified_edge_generic_instance_controls.rs` independently pins the same
//! local-dispatch skip controls in default AND strict, with warning-sensitive
//! annotations; keep both complete revisions unchanged.
//!
//! Trust (CONSUMER-FOREIGN-ITEM-REFUSAL-1, 2026-11-10): the walk still closes in
//! `forced_walk`, `nongeneric` and `closure` (the patterns above), but `run`'s one
//! row, the whole-function panic-freedom aggregate, stays runtime-checked (trust-mc
//! refuses `Take::count`'s `Alloca`), and since ADT-IMPL-DISCHARGE-1
//! (`40ffba3e8d`, on main 2026-11-03) the default policy no longer tolerates it:
//! `Take<Lw<..>>::count` is a closure-driving consumer whose local `Lw` names, in
//! its `Iterator` impl, the verify-off dependency's `Plain` as `Item`, which the
//! consumer classifier (`ty_names_unverified_code`) charges as code no verdict
//! covers, the class "a std routine instantiated at a type from such a dependency".
//! Measured A/B on one stage 1: with that classifier's local-ADT arm reverted, all
//! four revisions build exit 0; restored, these three refuse and `local_item`
//! (`Item = u32`) still builds. Precise admission of a foreign, drop-free data
//! `Item` through a walk-closed consumer is recorded, not taken
//! (`docs/DECISION_QUEUE.md`, CONSUMER-FOREIGN-ITEM-REFUSAL-1).
//!
//! Trust (POISON-EVICTION-FALSE-PROOF-1, 2026-11-12): RE-PINNED. `local_item` now
//! refuses too, and `forced_walk`/`closure` refuse for an earlier reason. In the three
//! generic-`Lw` revisions the bundle's `<Lw<u32> as Iterator>::try_fold` is poisoned by
//! its absent call to `<Lw<u32> as Iterator>::next`, and `spec_advance_by` calls it. The
//! poison loop used to evict it, and the withdrawn call then closed by walk. The loop
//! now keeps a member that a retained call still names (MEASURED with
//! `TRUST_MEMBER_PANIC_CENSUS=1` on this branch's stage 1: `try_fold … called by
//! spec_advance_by`), and that generic absent callee keeps the default policy
//! fail-closed before the consumer charge is reached. The walk still closes (the
//! patterns above). `nongeneric` has no generic `try_fold` instance and still pins
//! CONSUMER-FOREIGN-ITEM-REFUSAL-1's note. The lost `local_item` admission is
//! docs/DECISION_QUEUE.md POISON-EVICTION-KEEP-1.
#![allow(dead_code)]

extern crate sysroot_call_reach_local_generic_dep as dep;

pub trait Local {
    fn observe(&self) -> u32;
}

impl Local for u32 {
    #[inline(never)]
    fn observe(&self) -> u32 {
        *self / 2
    }
}

#[cfg(any(forced_walk, local_item, closure))]
pub struct Lw<T>(T);

#[cfg(any(forced_walk, local_item, closure))]
impl<T: Local> Iterator for Lw<T> {
    #[cfg(any(forced_walk, closure))]
    type Item = dep::Plain;
    #[cfg(local_item)]
    type Item = u32;

    #[inline(never)]
    fn next(&mut self) -> Option<Self::Item> {
        #[cfg(not(closure))]
        let _ = self.0.observe();
        // Trust: keep the closure's GENERIC parent and local callback, without
        // storing a foreign value in Option/Map or exercising their Alloca lane.
        #[cfg(closure)]
        {
            let observe = |value: &T| value.observe();
            let _ = observe(&self.0);
        }
        None
    }
}

#[cfg(any(forced_walk, local_item, closure))]
#[inline(never)]
pub fn run() -> usize {
    //[forced_walk,local_item,closure]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_generic_controls::run`
    //[forced_walk,local_item,closure]~| NOTE a generic absent callee — keeps the function fail-closed
    Lw(5u32).take(1).count()
}

#[cfg(nongeneric)]
pub struct Lw(u32);

#[cfg(nongeneric)]
impl Iterator for Lw {
    type Item = dep::Plain;

    #[inline(never)]
    fn next(&mut self) -> Option<Self::Item> {
        let _ = self.0.observe();
        None
    }
}

#[cfg(nongeneric)]
#[inline(never)]
pub fn run() -> usize {
    //[nongeneric]~^ ERROR Trust strict verification failed for `sysroot_call_reach_local_generic_controls::run`
    //[nongeneric]~| NOTE but this function ALSO carries a fail-closed panic source
    Lw(5u32).take(1).count()
}
