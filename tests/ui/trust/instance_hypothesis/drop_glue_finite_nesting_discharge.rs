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
//! OD-1 item 19 review (2026-10-06): the drop-glue walk never SKIPS an ADT nested in
//! itself. Before the fix an ADT met again at arguments that "contained" an
//! ancestor's was cut as polymorphic recursion, and two FINITE shapes were cut with
//! it, so `erase_const` and `erase_projection` passed strict with no discharge row:
//! * `erase_const`: a const-only ADT (`C<0>` holding `C<1>`; no type argument, so the
//!   containment test was vacuously true) — now a `failed` row;
//! * `erase_projection`: `S<u8>` holding `S<(u8, D<Bad2>)>` through a projection that
//!   then stops — now a `failed` row.
//! * `polymorphic_recursion_size`: real polymorphic recursion (`PolyBox<T>` holding
//!   `PolyBox<(T, T)>`) handed to a dependency generic is no longer cut: past
//!   `GLUE_GROWTH_CAP` growing repeats the glue is an `unknown` row (fail-closed; the
//!   walk still ends at once, no hang).
//! Control: `control_erase_const_good` (the const shape at `Good`: no error).
pub trait Tr {
    fn m(&self) -> u32;
}

pub struct Good;
pub struct Bad;
pub struct Bad2;

impl Tr for Good {
    fn m(&self) -> u32 {
        1
    }
}

impl Tr for Bad {
    fn m(&self) -> u32 {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `<drop_glue_finite_nesting_discharge::Bad as drop_glue_finite_nesting_discharge::Tr>::m`
    //[strict]~^^ ERROR Trust Level 0 safety verification incomplete for `<drop_glue_finite_nesting_discharge::Bad as drop_glue_finite_nesting_discharge::Tr>::m`
    //[strict]~^^^ ERROR Trust strict verification failed for `<drop_glue_finite_nesting_discharge::Bad as drop_glue_finite_nesting_discharge::Tr>::m`
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `<drop_glue_finite_nesting_discharge::Bad as drop_glue_finite_nesting_discharge::Tr>::m`
    //[certify]~^^^^^ ERROR Trust strict verification failed for `<drop_glue_finite_nesting_discharge::Bad as drop_glue_finite_nesting_discharge::Tr>::m`
        panic!("bad")
    }
}

impl Tr for Bad2 {
    fn m(&self) -> u32 {
    //[advisory]~^ WARN Trust Level 0 safety verification incomplete for `<drop_glue_finite_nesting_discharge::Bad2 as drop_glue_finite_nesting_discharge::Tr>::m`
    //[strict]~^^ ERROR Trust Level 0 safety verification incomplete for `<drop_glue_finite_nesting_discharge::Bad2 as drop_glue_finite_nesting_discharge::Tr>::m`
    //[strict]~^^^ ERROR Trust strict verification failed for `<drop_glue_finite_nesting_discharge::Bad2 as drop_glue_finite_nesting_discharge::Tr>::m`
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `<drop_glue_finite_nesting_discharge::Bad2 as drop_glue_finite_nesting_discharge::Tr>::m`
    //[certify]~^^^^^ ERROR Trust strict verification failed for `<drop_glue_finite_nesting_discharge::Bad2 as drop_glue_finite_nesting_discharge::Tr>::m`
        panic!("bad2")
    }
}

pub struct D<T: Tr>(pub T);

impl<T: Tr> Drop for D<T> {
    fn drop(&mut self) {
    //[advisory]~^ WARN Trust verification advisory for `<drop_glue_finite_nesting_discharge::D<T> as core::ops::drop::Drop>::drop`
    //[strict]~^^ WARN Trust verification advisory for `<drop_glue_finite_nesting_discharge::D<T> as core::ops::drop::Drop>::drop`
    //[certify]~^^^ ERROR Trust certify verification failed for `<drop_glue_finite_nesting_discharge::D<T> as core::ops::drop::Drop>::drop`
        self.0.m();
    }
}

// A const-only ADT nested in itself at another const: finite.
pub struct C<const N: usize> {
    pub arr: [D<Bad>; N],
    pub child: Option<Box<C<1>>>,
}

pub fn erase_const(c: Box<C<0>>) -> Box<dyn core::any::Any> {
    //[advisory]~^ WARN Trust instance discharge not established for `drop_glue_finite_nesting_discharge::erase_const`
    //[strict]~^^ ERROR Trust instance discharge not established for `drop_glue_finite_nesting_discharge::erase_const`
    //[strict]~^^^ NOTE [an instance created by the drop glue of `C<0>`] [failed]
    //[certify]~^^^^ ERROR Trust instance discharge not established for `drop_glue_finite_nesting_discharge::erase_const`
    c
}

pub struct CGood<const N: usize> {
    pub arr: [D<Good>; N],
    pub child: Option<Box<CGood<1>>>,
}

pub fn control_erase_const_good(c: Box<CGood<0>>) -> Box<dyn core::any::Any> {
    c
}

// An ADT nested in itself at growing arguments that a projection ends: finite.
pub trait Step {
    type Next: Step;
}
pub struct Stop;
impl Step for u8 {
    type Next = (u8, D<Bad2>);
}
impl Step for (u8, D<Bad2>) {
    type Next = Stop;
}
impl Step for Stop {
    type Next = Stop;
}

pub struct S<T: Step> {
    pub v: T,
    pub child: Option<Box<S<<T as Step>::Next>>>,
}

pub fn erase_projection(s: Box<S<u8>>) -> Box<dyn core::any::Any> {
    //[advisory]~^ WARN Trust instance discharge not established for `drop_glue_finite_nesting_discharge::erase_projection`
    //[strict]~^^ ERROR Trust instance discharge not established for `drop_glue_finite_nesting_discharge::erase_projection`
    //[strict]~^^^ NOTE [an instance created by the drop glue of `S<u8>`] [failed]
    //[certify]~^^^^ ERROR Trust instance discharge not established for `drop_glue_finite_nesting_discharge::erase_projection`
    s
}

// Polymorphic recursion: infinite drop glue, handed to a dependency generic.
pub struct PolyBox<T> {
    pub v: T,
    pub next: Option<Box<PolyBox<(T, T)>>>,
}

pub fn polymorphic_recursion_size(p: &PolyBox<D<Good>>) -> usize {
    //[advisory]~^ WARN Trust instance discharge not established for `drop_glue_finite_nesting_discharge::polymorphic_recursion_size`
    //[strict]~^^ ERROR Trust instance discharge not established for `drop_glue_finite_nesting_discharge::polymorphic_recursion_size`
    //[strict]~^^^ NOTE the instances created by the drop glue of `PolyBox<D<Good>>`
    //[certify]~^^^^ ERROR Trust instance discharge not established for `drop_glue_finite_nesting_discharge::polymorphic_recursion_size`
    core::mem::size_of_val(p)
}
