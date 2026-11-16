//~ NOTE "description":"assertion: [trust-absent-callee-assumption] call to absent callee `propagated_call_not_admitted_controls::writes_through::<T>` (body not in the lowered bundle) may panic"
//~| NOTE "description":"assertion: [trust-absent-callee-assumption] call to absent callee `propagated_call_not_admitted_controls::indexes::<T>` (body not in the lowered bundle) may panic"
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
//! OD-1 open shapes controls (2026-10-04): a still-generic call to a hypothesis-carrying
//! helper is lowered under the propagated hypotheses only when every conjunct of
//! `via_call_admits` holds. Each refusal keeps the phase-1 shape: the propagated
//! hypothesis row AND the call's own absent-callee row (line 1 pins both calls' rows).
//! (1) `caller_nested` hands `writes_through` a `&mut &mut u32`, and `writes_through`
//! writes the `u32` behind the INNER reference (its own rows prove everything else, so
//! only the argument predicate refuses): a one-level havoc of the outer pointee would
//! leave that `u32` stale; (2) `caller_index` calls
//! `indexes`, whose OWN body is not proved (`a[i]` for any `i`, published `failed`),
//! so the instance-relative bar refuses it. Neither row is stamped `failed`: the
//! helpers' failures are not open-dispatch refutations (contrast
//! `propagated_open_dispatch_refutation_is_failed.rs`).
pub trait Tr {
    fn m(&self) -> u32;
}

pub fn writes_through<T: Tr>(t: &T, r: &mut &mut u32) -> u32 {
    //[certify]~^ ERROR Trust certify verification failed for `propagated_call_not_admitted_controls::writes_through`: 1 instance hypothesis row(s)
    **r = 7;
    t.m()
}

pub fn caller_nested<T: Tr>(t: &T, r: &mut &mut u32) -> u32 {
    //[strict]~^ ERROR Trust strict verification failed
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^ ERROR Trust certify verification failed for `propagated_call_not_admitted_controls::caller_nested`: 1 instance hypothesis row(s)
    //[certify]~^^^^ ERROR Trust strict verification failed
    writes_through(t, r)
}

pub fn indexes<T: Tr>(t: &T, i: usize) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^^ ERROR Trust certify verification failed for `propagated_call_not_admitted_controls::indexes`: 1 instance hypothesis row(s)
    //[certify]~^^^^^ ERROR Trust strict verification failed
    let a = [1u32, 2];
    t.m() & a[i]
}

pub fn caller_index<T: Tr>(t: &T) -> u32 {
    //[strict]~^ ERROR Trust strict verification failed
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^^ ERROR Trust certify verification failed for `propagated_call_not_admitted_controls::caller_index`: 1 instance hypothesis row(s)
    //[certify]~^^^^ ERROR Trust strict verification failed
    indexes(t, 1)
}
