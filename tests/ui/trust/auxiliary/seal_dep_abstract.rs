//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_abstract.rs` and `_abstract_holds.rs`:
//! a trait whose constant and method swap two values of its associated type,
//! implemented for every `By<P>` with `Item = P`. Safe, and sound.
#![forbid(unsafe_code)]

use std::marker::PhantomData;

pub trait Sw {
    type Item;
    const SW: fn(&mut Self::Item, &mut Self::Item);
    fn sw(a: &mut Self::Item, b: &mut Self::Item);
}
pub struct By<P>(PhantomData<P>);
impl<P> Sw for By<P> {
    type Item = P;
    const SW: fn(&mut P, &mut P) = std::mem::swap::<P>;
    fn sw(a: &mut P, b: &mut P) {
        std::mem::swap(a, b)
    }
}
