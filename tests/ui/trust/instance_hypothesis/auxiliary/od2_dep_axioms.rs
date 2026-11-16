//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ edition: 2021
//@ no-prefer-dynamic
//! OD-1 phase 2 review fix (2026-10-05): a verify-off dependency that marks its
//! GENERICS `#[trust::assume_total]` and reaches the open dispatch on its
//! parameter where the site inventory does not look (a closure, a `dyn`, a
//! sysroot generic, drop glue). Every claim here is false at `DepBad`/`DropBad`.
#![feature(register_tool)]
#![register_tool(trust)]

pub trait Tr {
    fn m(&self) -> u32;
}

#[trust::assume_total]
pub fn direct<X: Tr>(x: &X) -> u32 {
    x.m()
}

#[trust::assume_total]
pub fn closure<X: Tr>(x: &X) -> u32 {
    let c = |y: &X| y.m();
    c(x)
}

#[trust::assume_total]
pub fn dyn_unsize<X: Tr>(x: &X) -> u32 {
    let d: &dyn Tr = x;
    d.m()
}

#[trust::assume_total]
pub fn std_generic<X: Tr>(x: Option<&X>) -> u32 {
    x.map(Tr::m).unwrap_or(0)
}

#[trust::assume_total]
pub fn drop_glue<X>(x: X) {
    drop(x)
}

/// Not generic: a dependency's axiom on it is still the documented
/// `AssumedTotalCalleeAssumption` hole, unchanged by the fix.
#[trust::assume_total]
pub fn plain() -> u32 {
    7
}

pub struct DepBad;

impl Tr for DepBad {
    fn m(&self) -> u32 {
        panic!("boom")
    }
}

pub struct DropBad;

impl Drop for DropBad {
    fn drop(&mut self) {
        panic!("drop boom")
    }
}
