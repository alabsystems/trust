//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ edition: 2021
//@ no-prefer-dynamic
//! DYN-ARG-PROVENANCE-1 review (2026-10-06): an UPSTREAM closed ADT (`UpV`, no
//! fields) whose upstream impl of an upstream, open trait with no blanket impl
//! (`Visitor<T>`: `Self` is concrete, so the impl is not a blanket one) dispatches on
//! the argument it is handed. A crate that hands `&UpV` to a private body together
//! with a forwarded `&dyn Open2` reaches a downstream `Open2` impl inside THIS
//! crate's body, where the dependent crate has no row.

pub trait Open2 {
    fn o2(&self) -> u32;
}

pub trait Visitor<T: ?Sized> {
    fn visit(&self, t: &T) -> u32;
}

pub struct UpV;

impl<T: ?Sized + Open2> Visitor<T> for UpV {
    fn visit(&self, t: &T) -> u32 {
        t.o2()
    }
}

/// A non-generic UPSTREAM fn item: handed to a private body as its callable, it runs
/// this crate's dispatch on the argument it is given, with no row in the dependent.
pub fn dispatch_open2(t: &(dyn Open2 + 'static)) -> u32 {
    t.o2()
}
