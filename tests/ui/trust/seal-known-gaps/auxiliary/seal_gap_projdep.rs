//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `r6_const_f1_rigid_alias_of_foreign_trait_with_local_impl_owns_nothing.rs`
//! (review 6 of the review-14 build): it only DECLARES traits, and has one impl
//! of its own, whose constant swaps. Sound.
#![forbid(unsafe_code)]
pub trait Proj { type Out; }
pub trait Proj2<P> { type Out; }
pub trait Sw { type Item; const SW: fn(&mut Self::Item, &mut Self::Item); }
pub struct By<P>(core::marker::PhantomData<P>);
impl<P> Sw for By<P> { type Item = P; const SW: fn(&mut P, &mut P) = core::mem::swap::<P>; }
