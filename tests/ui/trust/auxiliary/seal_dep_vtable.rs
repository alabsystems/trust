//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_vtable_params.rs`, `_vtable_params_holds.rs`
//! and `clean_island_seal_async_shim_holds.rs`: a unit type made a `dyn` of a
//! trait generic at the fn's parameter, one that measures and one that swaps;
//! and an `async` closure in generic code, called through `FnOnce`. Safe.
#![forbid(unsafe_code)]

pub trait Show<X> {
    fn show(&self, x: &X) -> usize;
}
pub struct P;
impl<X> Show<X> for P {
    fn show(&self, _x: &X) -> usize {
        1
    }
}
pub fn obj<X>() -> &'static dyn Show<X> {
    &P
}

pub trait Swp<X> {
    fn swp(&self, a: &mut X, b: &mut X);
}
pub struct Q;
impl<X> Swp<X> for Q {
    fn swp(&self, a: &mut X, b: &mut X) {
        std::mem::swap(a, b)
    }
}
pub fn swapper<X>() -> &'static dyn Swp<X> {
    &Q
}

pub fn later<T>(x: Option<T>) -> bool {
    let c = async |_v: T| 1u8;
    x.map(c).is_some()
}
