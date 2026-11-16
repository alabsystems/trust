//~ NOTE [trust-instance-hypothesis] call to `<impl Fn(u32) -> bool as core::ops::function::Fn<(u32,)>>::call` in `dyn_closure_capture_generic_twin_discharge::generic_twin::{closure#0}`
//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: ERROR
//@[advisory] check-pass
//@[strict] check-fail
//@[certify] check-fail
//! The `impl Fn` twin of `dyn_closure_capture_of_pub_fn_param_is_failed.rs`. Its closure's
//! call on the captured `impl Fn` is an `assumption:instance-hypothesis` row
//! (OD-1-T6-CALLABLE), not the class (c) `failed` row the `&dyn` spellings keep: the
//! callee is the caller's choice, so the obligation moves to each concrete instance.
//! This file pins that the move is CHARGED, not dropped: `twin_bad` names
//! `generic_twin::<{closure}>` at a callable that panics, and the discharge of the
//! closure's site at that instance is not established (a warning on advisory, an error
//! on strict and certify). A downstream instance is charged only if that crate is verified
//! (not measured here; the `inventory-incomplete` disclosure). Certify refuses the row.

pub fn generic_twin(names: &[&str], pid_alive: impl Fn(u32) -> bool) -> usize {
    names.iter().filter(|n| pid_alive(n.len() as u32)).count()
    //[certify]~^ ERROR Trust certify verification failed for `dyn_closure_capture_generic_twin_discharge::generic_twin::{closure#0}`: 1 instance hypothesis row(s)
}

pub fn twin_bad(names: &[&str]) -> usize {
    //[advisory]~^ WARN Trust instance discharge not established for `dyn_closure_capture_generic_twin_discharge::twin_bad`
    //[strict]~^^ ERROR Trust instance discharge not established for `dyn_closure_capture_generic_twin_discharge::twin_bad`
    //[certify]~^^^ ERROR Trust instance discharge not established for `dyn_closure_capture_generic_twin_discharge::twin_bad`
    generic_twin(names, |_| panic!("the caller's choice"))
}
