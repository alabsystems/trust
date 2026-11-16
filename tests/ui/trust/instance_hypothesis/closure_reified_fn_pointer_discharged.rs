//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=human --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//@[certify] check-fail
//! OD-1-T6-CALLABLE review (2026-10-11; docs/DECISION_QUEUE.md "OD-1-T6-CALLABLE"): a
//! hypothesis-carrying carrier REIFIED into a fn pointer by a generic body is discharged
//! at every concrete instance of that body.
//!
//! A `Via` record is minted for a CALL terminator only, and the glue walk of a reached
//! local generic (`glue::discharge_glue_of_instance`) skipped every carrier it mentioned
//! ("a carrier's calls are its `Via` records"). A closure coerced to a fn pointer
//! (`MentionedItem::Closure`, `f`) or a fn item handed on as a value (`c::<T>`, `h`) is
//! no call, so its sites were charged at no instance: before this fix `g_bad` and
//! `h_bad` published no `instance discharge` row at all (only the crate-wide inventory
//! row disclosed the gap). Now each concrete namer gets the discharge of the reified
//! carrier's site: `failed` at the panicking impl (a warning on advisory, an error on
//! strict and certify), and a row (not `failed`) at the panic-free one (`g_good`).
//!
//! R43-ZERO-ROW-PARITY (2026-10-13): `g_good`, `g_bad` and `h_bad` no longer carry ZERO-ROW-GATE's
//! "strict verification failed" error. Their one call (`f::<T>()`, `h::<T>()`) goes to a generic
//! body that only builds a fn pointer (no panic-capable terminator), which the R43 parametric
//! premises discharge. `g_bad` and `h_bad` stay refused under strict and certify by the
//! instance-discharge error above, the refusal this file pins; `g_good` is accepted.

pub trait Tr {
    fn go(x: u32) -> u32;
}

pub struct Bad;
impl Tr for Bad {
    fn go(x: u32) -> u32 {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `<closure_reified_fn_pointer_discharged::Bad as closure_reified_fn_pointer_discharged::Tr>::go`
    //[strict]~^^ ERROR Trust Level 0 safety verification incomplete for `<closure_reified_fn_pointer_discharged::Bad as closure_reified_fn_pointer_discharged::Tr>::go`
    //[strict]~| ERROR Trust strict verification failed for `<closure_reified_fn_pointer_discharged::Bad as closure_reified_fn_pointer_discharged::Tr>::go`
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `<closure_reified_fn_pointer_discharged::Bad as closure_reified_fn_pointer_discharged::Tr>::go`
    //[certify]~| ERROR Trust strict verification failed for `<closure_reified_fn_pointer_discharged::Bad as closure_reified_fn_pointer_discharged::Tr>::go`
        if x > 1 {
            panic!("bad");
        }
        x
    }
}

pub struct Good;
impl Tr for Good {
    fn go(x: u32) -> u32 {
        x
    }
}

// A closure carrying an admitted site, reified into a fn pointer by its parent.
pub fn f<T: Tr>() -> fn(u32) -> u32 {
    |x| T::go(x)
    //[advisory]~^ WARN Trust verification advisory for `closure_reified_fn_pointer_discharged::f::{closure#0}`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `closure_reified_fn_pointer_discharged::f::{closure#0}`: 1 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust certify verification failed for `closure_reified_fn_pointer_discharged::f::{closure#0}`: 1 instance hypothesis row(s)
}

pub fn g_bad() -> fn(u32) -> u32 {
//[advisory]~^ WARN Trust instance discharge not established for `closure_reified_fn_pointer_discharged::g_bad`: 1 instance(s)
//[advisory]~| NOTE of `closure_reified_fn_pointer_discharged::f::<closure_reified_fn_pointer_discharged::Bad>::{closure#0}` (named at
//[strict]~^^^ ERROR Trust instance discharge not established for `closure_reified_fn_pointer_discharged::g_bad`: 1 instance(s)
//[certify]~^^^^ ERROR Trust instance discharge not established for `closure_reified_fn_pointer_discharged::g_bad`: 1 instance(s)
    f::<Bad>()
}

pub fn g_good() -> fn(u32) -> u32 {
    f::<Good>()
}

// A carrier fn item handed on as a fn-pointer value (no call of it in `h`).
pub fn c<T: Tr>(x: u32) -> u32 {
//[advisory]~^ WARN Trust verification advisory for `closure_reified_fn_pointer_discharged::c`: 1 instance hypothesis row(s)
//[strict]~^^ WARN Trust verification advisory for `closure_reified_fn_pointer_discharged::c`: 1 instance hypothesis row(s)
//[certify]~^^^ ERROR Trust certify verification failed for `closure_reified_fn_pointer_discharged::c`: 1 instance hypothesis row(s)
    T::go(x)
}

pub fn h<T: Tr>() -> fn(u32) -> u32 {
    c::<T>
}

pub fn h_bad() -> fn(u32) -> u32 {
//[advisory]~^ WARN Trust instance discharge not established for `closure_reified_fn_pointer_discharged::h_bad`: 1 instance(s)
//[advisory]~| NOTE of `closure_reified_fn_pointer_discharged::c::<closure_reified_fn_pointer_discharged::Bad>` (named at
//[strict]~^^^ ERROR Trust instance discharge not established for `closure_reified_fn_pointer_discharged::h_bad`: 1 instance(s)
//[certify]~^^^^ ERROR Trust instance discharge not established for `closure_reified_fn_pointer_discharged::h_bad`: 1 instance(s)
    h::<Bad>()
}
