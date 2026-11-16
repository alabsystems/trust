//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_abstract_sig.rs` and `_abstract_sig_holds.rs`:
//! a trait whose method swaps two values of its associated type, and a driver
//! that runs it; and a trait whose items HAND BACK a swap (a fn pointer, a boxed
//! `dyn Fn`, a constant of an `Fn`-bounded associated type). Safe, and sound.
#![forbid(unsafe_code)]

use std::marker::PhantomData;

pub trait Sw {
    type Item;
    fn sw(a: &mut Self::Item, b: &mut Self::Item);
}
pub struct By<P>(PhantomData<P>);
impl<P> Sw for By<P> {
    type Item = P;
    fn sw(a: &mut P, b: &mut P) {
        std::mem::swap(a, b)
    }
}
/// Runs the method its type argument picks.
pub fn run<K: Sw>(a: &mut K::Item, b: &mut K::Item) {
    K::sw(a, b)
}

pub trait Hand {
    type Item: 'static;
    type Op: Fn(&mut Self::Item, &mut Self::Item) + Copy;
    const OP: Self::Op;
    fn swapper() -> fn(&mut Self::Item, &mut Self::Item);
    fn boxed() -> Box<dyn Fn(&mut Self::Item, &mut Self::Item)>;
}
impl<P: 'static> Hand for By<P> {
    type Item = P;
    type Op = fn(&mut P, &mut P);
    const OP: fn(&mut P, &mut P) = std::mem::swap::<P>;
    fn swapper() -> fn(&mut P, &mut P) {
        std::mem::swap::<P>
    }
    fn boxed() -> Box<dyn Fn(&mut P, &mut P)> {
        Box::new(|a, b| std::mem::swap(a, b))
    }
}
