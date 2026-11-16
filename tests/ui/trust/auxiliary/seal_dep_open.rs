//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_open.rs` and `_open_holds.rs`: generic
//! code that a LIBRARY's generic fn names at a type that holds a sealed value
//! whatever the library's own parameter stands for. Constants whose value
//! swaps or overwrites, a fn that hands one out, a blanket impl's method that
//! swaps; and fns that only measure. Safe, and sound: what a caller does
//! with what it is handed is its own.
#![forbid(unsafe_code)]

use std::marker::PhantomData;

/// A table of fns at a type.
pub struct Tab<T>(PhantomData<T>);
impl<T> Tab<T> {
    /// Swaps two values: a constant that only NAMES `mem::swap`.
    pub const SWAP: fn(&mut T, &mut T) = std::mem::swap::<T>;
    /// How large a value is: names `T`, runs nothing on one.
    pub const SIZE: usize = std::mem::size_of::<T>();
}
impl<T: 'static> Tab<T> {
    /// A `&dyn Fn` of a closure that swaps.
    pub const DSWAP: &'static dyn Fn(&mut T, &mut T) = &|a: &mut T, b: &mut T| std::mem::swap(a, b);
}

/// A trait whose default constant names a fn that overwrites a value.
pub trait Ops: Sized {
    const PUT: fn(&mut Self, Self) = put::<Self>;
}
impl<T> Ops for T {}

/// Overwrites `slot` with `v`.
pub fn put<T>(slot: &mut T, v: T) {
    *slot = v;
}

/// Hands out `mem::swap` as a fn pointer, and runs nothing.
pub fn swapper<T>() -> fn(&mut T, &mut T) {
    std::mem::swap::<T>
}

/// Hands out a fn that only measures.
pub fn measurer<T>() -> fn(&T) -> usize {
    measure::<T>
}

/// How large a value is.
pub fn measure<T>(_: &T) -> usize {
    std::mem::size_of::<T>()
}

/// A trait whose only impl, for every type, swaps.
pub trait SwapTr {
    fn swap_tr(a: &mut Self, b: &mut Self);
}
impl<X> SwapTr for X {
    fn swap_tr(a: &mut X, b: &mut X) {
        std::mem::swap(a, b)
    }
}

/// A trait whose only impl, for every type, measures.
pub trait Size {
    fn size(&self) -> usize;
}
impl<X> Size for X {
    fn size(&self) -> usize {
        std::mem::size_of::<X>()
    }
}

/// A trait whose only impl, for every type, overwrites what it is handed
/// with a default value.
pub trait Visit<X> {
    fn visit(&self, x: &mut X);
}
impl<S, X: Default> Visit<X> for S {
    fn visit(&self, x: &mut X) {
        *x = X::default();
    }
}
