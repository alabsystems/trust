//~ NOTE "outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
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
//! OD-1 open shapes (2026-10-04; docs/DECISION_QUEUE.md "OD-1" item 14): a NON-admitted
//! call through a closure type parameter is class (c) of "L0 refutation rows", exactly
//! like a non-admitted `<T as Tr>::m`: the caller picks `F`, so "panic-free for every
//! instantiation" is constructively false. Here the rust-call argument tuple
//! `(&mut u32,)` hands the callee a `&mut` by value, which the one-level havoc does not
//! cover, so the site is refused. Before this change its row read `runtime_checked`: the
//! bridge spells this call's fatal marker "indirect call `..` through an untypeable
//! callable receiver", and the Level-0 refutation reader only parsed the "call to absent
//! callee" spelling, so the witness set named the callee but never matched the row
//! (`--allow-l0-gaps` would conditional-pass it). Line 1 pins the stamped row.
pub fn bump<F: FnMut(&mut u32)>(f: &mut F, x: &mut u32) {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust strict verification failed
    f(x)
}
