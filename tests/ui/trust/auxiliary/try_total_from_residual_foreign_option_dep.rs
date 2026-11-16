//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ edition: 2021
//@ no-prefer-dynamic
//! A dependency that implements core's REAL `FromResidual` for the std carrier
//! `Option<T>`, with its own residual type `Res`. The orphan rule permits it because
//! `Res` is local to this crate. The body panics. A user `Try` type whose residual is
//! `Res` is what makes `?` reach this impl in an `Option`-returning function. Built
//! with verification off, as `targo` builds every dependency, so the impl body is
//! absent from the caller's bundle (TRY-TOTAL-ANCHOR-1).

#![feature(try_trait_v2, try_trait_v2_residual)]

use std::ops::{ControlFlow, FromResidual, Residual, Try};

pub struct Res;

pub struct MyTry(pub u32, pub bool);

impl FromResidual<Res> for MyTry {
    fn from_residual(_: Res) -> Self {
        MyTry(0, false)
    }
}

impl Try for MyTry {
    type Output = u32;
    type Residual = Res;
    fn from_output(o: u32) -> Self {
        MyTry(o, true)
    }
    fn branch(self) -> ControlFlow<Res, u32> {
        if self.1 { ControlFlow::Continue(self.0) } else { ControlFlow::Break(Res) }
    }
}

pub struct MyTry2<O>(pub Option<O>);

impl<O> Residual<O> for Res {
    type TryType = MyTry2<O>;
}

impl<O> FromResidual<Res> for MyTry2<O> {
    fn from_residual(_: Res) -> Self {
        MyTry2(None)
    }
}

impl<O> Try for MyTry2<O> {
    type Output = O;
    type Residual = Res;
    fn from_output(o: O) -> Self {
        MyTry2(Some(o))
    }
    fn branch(self) -> ControlFlow<Res, O> {
        match self.0 {
            Some(o) => ControlFlow::Continue(o),
            None => ControlFlow::Break(Res),
        }
    }
}

// The real `core::ops::FromResidual`, a residual type local to this crate, the std
// carrier `Option<T>`: orphan-legal, and not core's impl.
impl<T> FromResidual<Res> for Option<T> {
    fn from_residual(_: Res) -> Self {
        panic!("boom option from_residual")
    }
}

// A plain function with the same body, under no `?`-desugar identity: the control.
pub fn boom_option() -> Option<u32> {
    panic!("boom option ctl")
}
