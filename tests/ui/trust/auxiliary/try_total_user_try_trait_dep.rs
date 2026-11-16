//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ edition: 2021
//@ no-prefer-dynamic
//! A dependency with its OWN traits whose method paths end the way the `?`-desugar
//! methods' do: `try_total_user_try_trait_dep::Try::branch` and
//! `try_total_user_try_trait_dep::FromResidual::from_residual`. Both are implemented
//! for the std carrier `Option<u32>` with a panicking body (stable Rust: the traits
//! are ordinary user traits, not core's lang items). `Tri` and `FromResid` are the
//! same bodies under names no suffix test matches: the controls. Built with
//! verification off, as `targo` builds every dependency, so each body is absent from
//! the caller's bundle (TRY-TOTAL-ANCHOR-1).

pub trait Try {
    fn branch(self) -> u32;
}

impl Try for Option<u32> {
    fn branch(self) -> u32 {
        panic!("boom branch")
    }
}

pub trait FromResidual<R> {
    fn from_residual(r: R) -> Self;
}

impl FromResidual<u8> for Option<u32> {
    fn from_residual(_r: u8) -> Self {
        panic!("boom from_residual")
    }
}

pub trait Tri {
    fn branch(self) -> u32;
}

impl Tri for Option<u32> {
    fn branch(self) -> u32 {
        panic!("boom ctl branch")
    }
}

pub trait FromResid<R> {
    fn from_residual(r: R) -> Self;
}

impl FromResid<u8> for Option<u32> {
    fn from_residual(_r: u8) -> Self {
        panic!("boom ctl from_residual")
    }
}
