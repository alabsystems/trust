//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//@[certify] check-fail
//! OD-1 item 19 (2026-10-06, vtable-only discharge): an instance of the hypothesis
//! carrier `<W<T> as Run>::run` that no body NAMES, created only by the vtable an
//! unsizing coercion to `dyn Run` builds. Before the fix none of these instances had a
//! discharge row and `coerce_bad`, `through_generic_bad` and
//! `through_type_parameter_bad` passed strict (each `Bad*::m` was refused only as its
//! own root). Now each is charged a `failed` discharge row, an error on strict and
//! certify, from the body's recorded mentioned items:
//! * `coerce_bad`: the body's own concrete coercion `&W<Bad>` -> `&dyn Run`;
//! * `through_generic_bad`: `mk::<Bad2>` builds the vtable at a still-generic type
//!   (`W<U>`), charged at the instance the body names;
//! * `through_type_parameter_bad`: `boxed::<W<Bad3>>` unsizes its bare type
//!   parameter, which is `W<Bad3>` at this instance.
//! * `coerce_declared_first_bad`: the same coercion in a body declared before the
//!   carrier impl (verified first; the carrier is demanded from the discharge).
//! Controls: `coerce_good` (a `proved` discharge row, no error), a non-generic impl
//! (`Plain`) and an array-to-slice coercion (no vtable carrier, no row).
pub trait Tr {
    fn m(&self) -> u32;
}

pub struct Good;
pub struct Bad;
pub struct Bad2;
pub struct Bad3;
pub struct Bad4;

// Declared BEFORE the carrier impl: no call edge orders the carrier first, so the
// discharge demands its verification (or, where that could cycle, is `unknown`).
pub fn coerce_declared_first_bad(w: &W<Bad4>) -> &dyn Run {
    //[advisory]~^ WARN Trust instance discharge not established for `vtable_only_instance_discharge::coerce_declared_first_bad`
    //[strict]~^^ ERROR Trust instance discharge not established for `vtable_only_instance_discharge::coerce_declared_first_bad`
    //[strict]~^^^ NOTE [an instance created by the vtable of `W<Bad4>` as `dyn Run`] [failed]
    //[certify]~^^^^ ERROR Trust instance discharge not established for `vtable_only_instance_discharge::coerce_declared_first_bad`
    w
}

impl Tr for Good {
    fn m(&self) -> u32 {
        1
    }
}

impl Tr for Bad {
    fn m(&self) -> u32 {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `<vtable_only_instance_discharge::Bad as vtable_only_instance_discharge::Tr>::m`
    //[strict]~^^ ERROR Trust Level 0 safety verification incomplete for `<vtable_only_instance_discharge::Bad as vtable_only_instance_discharge::Tr>::m`
    //[strict]~^^^ ERROR Trust strict verification failed for `<vtable_only_instance_discharge::Bad as vtable_only_instance_discharge::Tr>::m`
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `<vtable_only_instance_discharge::Bad as vtable_only_instance_discharge::Tr>::m`
    //[certify]~^^^^^ ERROR Trust strict verification failed for `<vtable_only_instance_discharge::Bad as vtable_only_instance_discharge::Tr>::m`
        panic!("bad")
    }
}

impl Tr for Bad2 {
    fn m(&self) -> u32 {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `<vtable_only_instance_discharge::Bad2 as vtable_only_instance_discharge::Tr>::m`
    //[strict]~^^ ERROR Trust Level 0 safety verification incomplete for `<vtable_only_instance_discharge::Bad2 as vtable_only_instance_discharge::Tr>::m`
    //[strict]~^^^ ERROR Trust strict verification failed for `<vtable_only_instance_discharge::Bad2 as vtable_only_instance_discharge::Tr>::m`
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `<vtable_only_instance_discharge::Bad2 as vtable_only_instance_discharge::Tr>::m`
    //[certify]~^^^^^ ERROR Trust strict verification failed for `<vtable_only_instance_discharge::Bad2 as vtable_only_instance_discharge::Tr>::m`
        panic!("bad2")
    }
}

impl Tr for Bad3 {
    fn m(&self) -> u32 {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `<vtable_only_instance_discharge::Bad3 as vtable_only_instance_discharge::Tr>::m`
    //[strict]~^^ ERROR Trust Level 0 safety verification incomplete for `<vtable_only_instance_discharge::Bad3 as vtable_only_instance_discharge::Tr>::m`
    //[strict]~^^^ ERROR Trust strict verification failed for `<vtable_only_instance_discharge::Bad3 as vtable_only_instance_discharge::Tr>::m`
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `<vtable_only_instance_discharge::Bad3 as vtable_only_instance_discharge::Tr>::m`
    //[certify]~^^^^^ ERROR Trust strict verification failed for `<vtable_only_instance_discharge::Bad3 as vtable_only_instance_discharge::Tr>::m`
        panic!("bad3")
    }
}

impl Tr for Bad4 {
    fn m(&self) -> u32 {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `<vtable_only_instance_discharge::Bad4 as vtable_only_instance_discharge::Tr>::m`
    //[strict]~^^ ERROR Trust Level 0 safety verification incomplete for `<vtable_only_instance_discharge::Bad4 as vtable_only_instance_discharge::Tr>::m`
    //[strict]~^^^ ERROR Trust strict verification failed for `<vtable_only_instance_discharge::Bad4 as vtable_only_instance_discharge::Tr>::m`
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `<vtable_only_instance_discharge::Bad4 as vtable_only_instance_discharge::Tr>::m`
    //[certify]~^^^^^ ERROR Trust strict verification failed for `<vtable_only_instance_discharge::Bad4 as vtable_only_instance_discharge::Tr>::m`
        panic!("bad4")
    }
}

pub trait Run {
    fn run(&self) -> u32;
}

pub struct W<T>(pub T);

impl<T: Tr> Run for W<T> {
    fn run(&self) -> u32 {
    //[advisory]~^ WARN Trust verification advisory for `<vtable_only_instance_discharge::W<T> as vtable_only_instance_discharge::Run>::run`
    //[strict]~^^ WARN Trust verification advisory for `<vtable_only_instance_discharge::W<T> as vtable_only_instance_discharge::Run>::run`
    //[certify]~^^^ ERROR Trust certify verification failed for `<vtable_only_instance_discharge::W<T> as vtable_only_instance_discharge::Run>::run`
        self.0.m()
    }
}

pub struct Plain;

impl Run for Plain {
    fn run(&self) -> u32 {
        7
    }
}

fn mk<U: Tr + 'static>(u: U) -> Box<dyn Run> {
    Box::new(W(u))
}

fn boxed<U: Run + 'static>(u: U) -> Box<dyn Run> {
    Box::new(u)
}

pub fn coerce_bad(w: &W<Bad>) -> &dyn Run {
    //[advisory]~^ WARN Trust instance discharge not established for `vtable_only_instance_discharge::coerce_bad`
    //[strict]~^^ ERROR Trust instance discharge not established for `vtable_only_instance_discharge::coerce_bad`
    //[strict]~^^^ NOTE [an instance created by the vtable of `W<Bad>` as `dyn Run`] [failed]
    //[certify]~^^^^ ERROR Trust instance discharge not established for `vtable_only_instance_discharge::coerce_bad`
    w
}

pub fn coerce_good(w: &W<Good>) -> &dyn Run {
    w
}

pub fn through_generic_bad() -> Box<dyn Run> {
    //[advisory]~^ WARN Trust instance discharge not established for `vtable_only_instance_discharge::through_generic_bad`
    //[strict]~^^ ERROR Trust instance discharge not established for `vtable_only_instance_discharge::through_generic_bad`
    //[strict]~^^^ NOTE [an instance created by the vtable of `W<Bad2>` as `dyn Run`] [failed]
    //[certify]~^^^^ ERROR Trust instance discharge not established for `vtable_only_instance_discharge::through_generic_bad`
    //[advisory]~^^^^^ WARN Trust Level 0 safety verification incomplete for `vtable_only_instance_discharge::through_generic_bad`
    //[strict]~^^^^^^ WARN Trust Level 0 safety verification incomplete for `vtable_only_instance_discharge::through_generic_bad`
    //[strict]~^^^^^^^ WARN Trust verification advisory for `vtable_only_instance_discharge::through_generic_bad`
    //[certify]~^^^^^^^^ ERROR Trust Level 0 safety verification incomplete for `vtable_only_instance_discharge::through_generic_bad`
    //[certify]~^^^^^^^^^ ERROR Trust strict verification failed for `vtable_only_instance_discharge::through_generic_bad`
    // Re-pinned 2026-10-15 (the merge of 2026-10-14): refused exactly like
    // `through_type_parameter_bad` below, on its `failed` discharge row alone (`1 proved,
    // 1 failed, 1 skipped`: its own row proved, the discharge row failed, the skipped row the
    // discharged global-alloc premise). The unproved row it used to carry beside the
    // discharge row, and the "incomplete"/"advisory"/"strict verification failed" lines that
    // row raised, are gone (measured on the merged stage 1).
    // Re-pinned AGAIN 2026-11-03 (the 1.101 port): at the merged trust-mc pin its
    // own row is `runtime_checked` once more, so those lines are back (see
    // `through_type_parameter_bad` below). The refusal never moved.
    mk(Bad2)
}

pub fn through_type_parameter_bad() -> Box<dyn Run> {
    //[advisory]~^ WARN Trust instance discharge not established for `vtable_only_instance_discharge::through_type_parameter_bad`
    //[strict]~^^ ERROR Trust instance discharge not established for `vtable_only_instance_discharge::through_type_parameter_bad`
    //[strict]~^^^ NOTE [an instance created by the vtable of `W<Bad3>` as `dyn Run`] [failed]
    //[certify]~^^^^ ERROR Trust instance discharge not established for `vtable_only_instance_discharge::through_type_parameter_bad`
    //[advisory]~^^^^^ WARN Trust Level 0 safety verification incomplete for `vtable_only_instance_discharge::through_type_parameter_bad`
    //[strict]~^^^^^^ WARN Trust Level 0 safety verification incomplete for `vtable_only_instance_discharge::through_type_parameter_bad`
    //[strict]~^^^^^^^ WARN Trust verification advisory for `vtable_only_instance_discharge::through_type_parameter_bad`
    //[certify]~^^^^^^^^ ERROR Trust Level 0 safety verification incomplete for `vtable_only_instance_discharge::through_type_parameter_bad`
    //[certify]~^^^^^^^^^ ERROR Trust strict verification failed for `vtable_only_instance_discharge::through_type_parameter_bad`
    // Re-pinned 2026-11-03 (the 1.101 port, merged trust-mc): both bad calls'
    // own panic-freedom aggregates publish beside their `failed` discharge
    // rows and are `runtime_checked`, not proved (measured transport rows on
    // the merged stage 1), so the Level 0 incomplete lines are present for
    // both. The refusals are unchanged; the reporting is more complete.
    boxed(W(Bad3))
}

pub fn control_plain(p: &Plain) -> &dyn Run {
    p
}

pub fn control_slice(a: &[u8; 4]) -> &[u8] {
    a
}
