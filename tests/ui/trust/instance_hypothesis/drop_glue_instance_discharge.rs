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
//@ forbid-output: this function has no obligation of its own
//! OD-1 item 19 (2026-10-06, vtable-only discharge): an instance of the hypothesis
//! carrier `<D<T> as Drop>::drop` that no body NAMES, run only by DROP GLUE. Before the
//! fix none had a discharge row (each body was refused only by its drop-glue
//! obligation, which says nothing about the instance). Now each is charged a `failed`
//! discharge row naming the glue:
//! * `drop_bad`: the body's own drop of `D<Bad>`;
//! * `drop_inside_vec`: the drop glue of `Vec<D<Bad2>>` (the walk follows a generic
//!   type argument behind the raw buffer);
//! * `drop_handed_to_dependency`: `core::mem::drop(D(Bad3))` hands the value to a
//!   dependency generic, which is charged the type's drop glue;
//! * `drop_through_generic`: `hold::<Bad4>` drops `D<U>` at a still-generic type,
//!   charged at the instance the body names.
//! * `drop_nested_same_adt`: `Option<Option<D<Bad5>>>` (an ADT nested in itself at
//!   SMALLER arguments is walked, not mistaken for polymorphic recursion).
//! Controls: `drop_good` (a `proved` discharge row; the body keeps its pre-existing
//! drop-glue refusal), `control_reference_only` (a reference owns nothing: no row).
//! (Polymorphic recursion, once a "cut, no row" control here, is an `unknown` row since
//! the item 19 review: `drop_glue_finite_nesting_discharge.rs`.)
pub trait Tr {
    fn m(&self) -> u32;
}

pub struct Good;
pub struct Bad;
pub struct Bad2;
pub struct Bad3;
pub struct Bad4;
pub struct Bad5;

impl Tr for Good {
    fn m(&self) -> u32 {
        1
    }
}

impl Tr for Bad {
    fn m(&self) -> u32 {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `<drop_glue_instance_discharge::Bad as drop_glue_instance_discharge::Tr>::m`
    //[strict]~^^ ERROR Trust Level 0 safety verification incomplete for `<drop_glue_instance_discharge::Bad as drop_glue_instance_discharge::Tr>::m`
    //[strict]~^^^ ERROR Trust strict verification failed for `<drop_glue_instance_discharge::Bad as drop_glue_instance_discharge::Tr>::m`
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `<drop_glue_instance_discharge::Bad as drop_glue_instance_discharge::Tr>::m`
    //[certify]~^^^^^ ERROR Trust strict verification failed for `<drop_glue_instance_discharge::Bad as drop_glue_instance_discharge::Tr>::m`
        panic!("bad")
    }
}

impl Tr for Bad2 {
    fn m(&self) -> u32 {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `<drop_glue_instance_discharge::Bad2 as drop_glue_instance_discharge::Tr>::m`
    //[strict]~^^ ERROR Trust Level 0 safety verification incomplete for `<drop_glue_instance_discharge::Bad2 as drop_glue_instance_discharge::Tr>::m`
    //[strict]~^^^ ERROR Trust strict verification failed for `<drop_glue_instance_discharge::Bad2 as drop_glue_instance_discharge::Tr>::m`
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `<drop_glue_instance_discharge::Bad2 as drop_glue_instance_discharge::Tr>::m`
    //[certify]~^^^^^ ERROR Trust strict verification failed for `<drop_glue_instance_discharge::Bad2 as drop_glue_instance_discharge::Tr>::m`
        panic!("bad2")
    }
}

impl Tr for Bad3 {
    fn m(&self) -> u32 {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `<drop_glue_instance_discharge::Bad3 as drop_glue_instance_discharge::Tr>::m`
    //[strict]~^^ ERROR Trust Level 0 safety verification incomplete for `<drop_glue_instance_discharge::Bad3 as drop_glue_instance_discharge::Tr>::m`
    //[strict]~^^^ ERROR Trust strict verification failed for `<drop_glue_instance_discharge::Bad3 as drop_glue_instance_discharge::Tr>::m`
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `<drop_glue_instance_discharge::Bad3 as drop_glue_instance_discharge::Tr>::m`
    //[certify]~^^^^^ ERROR Trust strict verification failed for `<drop_glue_instance_discharge::Bad3 as drop_glue_instance_discharge::Tr>::m`
        panic!("bad3")
    }
}

impl Tr for Bad4 {
    fn m(&self) -> u32 {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `<drop_glue_instance_discharge::Bad4 as drop_glue_instance_discharge::Tr>::m`
    //[strict]~^^ ERROR Trust Level 0 safety verification incomplete for `<drop_glue_instance_discharge::Bad4 as drop_glue_instance_discharge::Tr>::m`
    //[strict]~^^^ ERROR Trust strict verification failed for `<drop_glue_instance_discharge::Bad4 as drop_glue_instance_discharge::Tr>::m`
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `<drop_glue_instance_discharge::Bad4 as drop_glue_instance_discharge::Tr>::m`
    //[certify]~^^^^^ ERROR Trust strict verification failed for `<drop_glue_instance_discharge::Bad4 as drop_glue_instance_discharge::Tr>::m`
        panic!("bad4")
    }
}

impl Tr for Bad5 {
    fn m(&self) -> u32 {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `<drop_glue_instance_discharge::Bad5 as drop_glue_instance_discharge::Tr>::m`
    //[strict]~^^ ERROR Trust Level 0 safety verification incomplete for `<drop_glue_instance_discharge::Bad5 as drop_glue_instance_discharge::Tr>::m`
    //[strict]~^^^ ERROR Trust strict verification failed for `<drop_glue_instance_discharge::Bad5 as drop_glue_instance_discharge::Tr>::m`
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `<drop_glue_instance_discharge::Bad5 as drop_glue_instance_discharge::Tr>::m`
    //[certify]~^^^^^ ERROR Trust strict verification failed for `<drop_glue_instance_discharge::Bad5 as drop_glue_instance_discharge::Tr>::m`
        panic!("bad5")
    }
}

pub struct D<T: Tr>(pub T);

impl<T: Tr> Drop for D<T> {
    fn drop(&mut self) {
    //[advisory]~^ WARN Trust verification advisory for `<drop_glue_instance_discharge::D<T> as core::ops::drop::Drop>::drop`
    //[strict]~^^ WARN Trust verification advisory for `<drop_glue_instance_discharge::D<T> as core::ops::drop::Drop>::drop`
    //[certify]~^^^ ERROR Trust certify verification failed for `<drop_glue_instance_discharge::D<T> as core::ops::drop::Drop>::drop`
        let _ = self.0.m();
    }
}

fn hold<U: Tr>(u: U) {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::hold`
    //[strict]~^^ WARN Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::hold`
    //[strict]~^^^ ERROR Trust strict verification failed for `drop_glue_instance_discharge::hold`
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::hold`
    //[certify]~^^^^^ ERROR Trust strict verification failed for `drop_glue_instance_discharge::hold`
    let _d = D(u);
}

pub fn drop_bad() {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::drop_bad`
    //[advisory]~^^ WARN Trust instance discharge not established for `drop_glue_instance_discharge::drop_bad`
    //[strict]~^^^ WARN Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::drop_bad`
    //[strict]~^^^^ ERROR Trust instance discharge not established for `drop_glue_instance_discharge::drop_bad`
    //[strict]~^^^^^ NOTE [an instance created by the drop glue of `D<Bad>`] [failed]
    //[strict]~^^^^^^ ERROR Trust strict verification failed for `drop_glue_instance_discharge::drop_bad`
    //[certify]~^^^^^^^ ERROR Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::drop_bad`
    //[certify]~^^^^^^^^ ERROR Trust instance discharge not established for `drop_glue_instance_discharge::drop_bad`
    //[certify]~^^^^^^^^^ ERROR Trust strict verification failed for `drop_glue_instance_discharge::drop_bad`
    let _d = D(Bad);
}

pub fn drop_good() {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::drop_good`
    //[strict]~^^ WARN Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::drop_good`
    //[strict]~^^^ ERROR Trust strict verification failed for `drop_glue_instance_discharge::drop_good`
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::drop_good`
    //[certify]~^^^^^ ERROR Trust strict verification failed for `drop_glue_instance_discharge::drop_good`
    let _d = D(Good);
}

pub fn drop_inside_vec(v: Vec<D<Bad2>>) {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::drop_inside_vec`
    //[advisory]~^^ WARN Trust instance discharge not established for `drop_glue_instance_discharge::drop_inside_vec`
    //[strict]~^^^ WARN Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::drop_inside_vec`
    //[strict]~^^^^ ERROR Trust instance discharge not established for `drop_glue_instance_discharge::drop_inside_vec`
    //[strict]~^^^^^ NOTE [an instance created by the drop glue of `std::vec::Vec<D<Bad2>>`] [failed]
    //[strict]~^^^^^^ ERROR Trust strict verification failed for `drop_glue_instance_discharge::drop_inside_vec`
    //[certify]~^^^^^^^ ERROR Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::drop_inside_vec`
    //[certify]~^^^^^^^^ ERROR Trust instance discharge not established for `drop_glue_instance_discharge::drop_inside_vec`
    //[certify]~^^^^^^^^^ ERROR Trust strict verification failed for `drop_glue_instance_discharge::drop_inside_vec`
    let _ = v;
}

pub fn drop_handed_to_dependency() {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::drop_handed_to_dependency`
    //[advisory]~^^ WARN Trust instance discharge not established for `drop_glue_instance_discharge::drop_handed_to_dependency`
    //[strict]~^^^ WARN Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::drop_handed_to_dependency`
    //[strict]~^^^^ ERROR Trust instance discharge not established for `drop_glue_instance_discharge::drop_handed_to_dependency`
    //[strict]~^^^^^ NOTE [an instance created by the drop glue of `D<Bad3>`] [failed]
    //[strict]~^^^^^^ ERROR Trust strict verification failed for `drop_glue_instance_discharge::drop_handed_to_dependency`
    //[certify]~^^^^^^^ ERROR Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::drop_handed_to_dependency`
    //[certify]~^^^^^^^^ ERROR Trust instance discharge not established for `drop_glue_instance_discharge::drop_handed_to_dependency`
    //[certify]~^^^^^^^^^ ERROR Trust strict verification failed for `drop_glue_instance_discharge::drop_handed_to_dependency`
    core::mem::drop(D(Bad3))
}

pub fn drop_through_generic() {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::drop_through_generic`
    //[advisory]~^^ WARN Trust instance discharge not established for `drop_glue_instance_discharge::drop_through_generic`
    //[strict]~^^^ WARN Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::drop_through_generic`
    //[strict]~^^^^ ERROR Trust instance discharge not established for `drop_glue_instance_discharge::drop_through_generic`
    //[strict]~^^^^^ NOTE [an instance created by the drop glue of `D<Bad4>`] [failed]
    //[strict]~^^^^^^ ERROR Trust strict verification failed for `drop_glue_instance_discharge::drop_through_generic`
    //[certify]~^^^^^^^ ERROR Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::drop_through_generic`
    //[certify]~^^^^^^^^ ERROR Trust instance discharge not established for `drop_glue_instance_discharge::drop_through_generic`
    //[certify]~^^^^^^^^^ ERROR Trust strict verification failed for `drop_glue_instance_discharge::drop_through_generic`
    hold(Bad4)
}

pub fn drop_nested_same_adt(o: Option<Option<D<Bad5>>>) {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::drop_nested_same_adt`
    //[advisory]~^^ WARN Trust instance discharge not established for `drop_glue_instance_discharge::drop_nested_same_adt`
    //[strict]~^^^ WARN Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::drop_nested_same_adt`
    //[strict]~^^^^ ERROR Trust instance discharge not established for `drop_glue_instance_discharge::drop_nested_same_adt`
    //[strict]~^^^^^ NOTE [an instance created by the drop glue of `std::option::Option<std::option::Option<D<Bad5>>>`] [failed]
    //[strict]~^^^^^^ ERROR Trust strict verification failed for `drop_glue_instance_discharge::drop_nested_same_adt`
    //[certify]~^^^^^^^ ERROR Trust Level 0 safety verification incomplete for `drop_glue_instance_discharge::drop_nested_same_adt`
    //[certify]~^^^^^^^^ ERROR Trust instance discharge not established for `drop_glue_instance_discharge::drop_nested_same_adt`
    //[certify]~^^^^^^^^^ ERROR Trust strict verification failed for `drop_glue_instance_discharge::drop_nested_same_adt`
    let _ = o;
}

pub fn control_reference_only(_d: &D<Bad>) {}

// ZERO-ROW-GATE (2026-10-10): this rail must refuse for its OWN reason; a refusal by the
// zero-row gate (whose note is forbidden here) would mean the gate under test regressed
// into discharging and the zero-row gate masked it.
