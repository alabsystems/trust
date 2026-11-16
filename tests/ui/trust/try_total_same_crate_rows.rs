//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Per-function rows for the same-crate shapes of TRY-TOTAL-ANCHOR-1.
//!
//! The crate fails in every revision whatever the fix does, because each panicking
//! impl below is its own verified root and is refused. So this file pins the ROWS of
//! the functions that CALL those impls, not the exit code.
//!
//! * `q` is the `?` operator on a user `Try` type whose residual is the local `Res`,
//!   inside an `Option`-returning function. Its early-return arm calls core's real
//!   `FromResidual<Res>` impl for `Option<u32>`, which this crate wrote and which
//!   panics. `d` calls that impl directly. `trust_try_total_marker` marked both
//!   calls total because the TARGET is a std `Option`; it never looked at the
//!   residual.
//! * `a` and `b` call this crate's own `user::Try::branch` and
//!   `user::FromResidual::from_residual` (stable Rust, ordinary traits), whose
//!   rendered paths end the way the `?`-desugar methods' do. The marker matched them
//!   by that text, and the compiler's `compiler_total_out` lane admitted them.
//!
//! BEFORE (stage 1 of main + wave 7, `scratchpad/stage1-w14`, each revision's own
//! flags plus `--cfg <revision> --emit=metadata`, measured 2026-10-05): `q` (2 proved),
//! `d` (`trivially panic-free`), `a` and `b` (1 proved each) have no diagnostic in
//! either revision while the four panicking impls are refused, so none of the
//! annotations on `q`, `d`, `a` or `b` fires.
//!
//! AFTER (predicted): the marker requires core's `branch`/`from_residual` lang item in
//! a real sysroot crate, and for `from_residual` a residual that is the same std
//! carrier as the target. The annotations are what the BEFORE compiler prints for a
//! twin of this file in which every marked call is replaced by the same call through
//! a trait whose name no recognizer matches (`Tri::branch`, `FromResid::from_residual`,
//! with a `FromResid<Res> for Option<T>` impl and a hand-desugared `?`). Under the
//! default policy `a` and `b` become `runtime_checked` (warnings: the callee's panic
//! is reachable and keeps its runtime check), while `q` and `d` keep an absent-callee
//! row for the generic impl and are refused.

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

// Orphan-legal: core's real `FromResidual`, the local residual `Res`, std's `Option<T>`.
impl<T> FromResidual<Res> for Option<T> {
    fn from_residual(_: Res) -> Self {
        //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `try_total_same_crate_rows::<impl core::ops::try_trait::FromResidual<try_total_same_crate_rows::Res> for core::option::Option<T>>::from_residual`: 2 obligation(s) were not proved
        //[default,certify]~| ERROR Trust strict verification failed for `try_total_same_crate_rows::<impl core::ops::try_trait::FromResidual<try_total_same_crate_rows::Res> for core::option::Option<T>>::from_residual`: 2 obligation(s) were not fully verified
        panic!("boom option from_residual")
    }
}

pub fn q(t: MyTry) -> Option<u32> {
    //[default,certify]~^ ERROR Trust strict verification failed for `try_total_same_crate_rows::q`: 1 obligation(s) were not fully verified
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `try_total_same_crate_rows::q`: 1 obligation(s) were not proved
    let v = t?;
    Some(v)
}

pub fn d() -> Option<u32> {
    //[default,certify]~^ ERROR Trust strict verification failed for `try_total_same_crate_rows::d`: 1 obligation(s) were not fully verified
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `try_total_same_crate_rows::d`: 1 obligation(s) were not proved
    <Option<u32> as FromResidual<Res>>::from_residual(Res)
}

pub mod user {
    pub trait Try {
        fn branch(self) -> u32;
    }

    impl Try for Option<u32> {
        fn branch(self) -> u32 {
            //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `<core::option::Option<u32> as try_total_same_crate_rows::user::Try>::branch`: 2 obligation(s) were not proved
            //[default,certify]~| ERROR Trust strict verification failed for `<core::option::Option<u32> as try_total_same_crate_rows::user::Try>::branch`: 2 obligation(s) were not fully verified
            panic!("boom branch")
        }
    }

    pub trait FromResidual<R> {
        fn from_residual(r: R) -> Self;
    }

    impl FromResidual<u8> for Option<u32> {
        fn from_residual(_r: u8) -> Self {
            //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `<core::option::Option<u32> as try_total_same_crate_rows::user::FromResidual<u8>>::from_residual`: 2 obligation(s) were not proved
            //[default,certify]~| ERROR Trust strict verification failed for `<core::option::Option<u32> as try_total_same_crate_rows::user::FromResidual<u8>>::from_residual`: 2 obligation(s) were not fully verified
            panic!("boom from_residual")
        }
    }
}

pub fn a(x: Option<u32>) -> u32 {
    //[default]~^ WARN Trust verification advisory for `try_total_same_crate_rows::a`: 1 obligation(s) were not fully verified
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `try_total_same_crate_rows::a`: 1 obligation(s) were not proved
    //[certify]~| ERROR Trust strict verification failed for `try_total_same_crate_rows::a`: 1 obligation(s) were not fully verified
    user::Try::branch(x)
}

pub fn b(r: u8) -> Option<u32> {
    //[default]~^ WARN Trust verification advisory for `try_total_same_crate_rows::b`: 1 obligation(s) were not fully verified
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `try_total_same_crate_rows::b`: 1 obligation(s) were not proved
    //[certify]~| ERROR Trust strict verification failed for `try_total_same_crate_rows::b`: 1 obligation(s) were not fully verified
    <Option<u32> as user::FromResidual<u8>>::from_residual(r)
}
