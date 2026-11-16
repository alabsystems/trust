//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_values.rs` and `_values_holds.rs`:
//! items that hand out a fn as a VALUE (a constant's value, a fn pointer a
//! fn returns, a closure, a boxed `dyn Fn`), which runs where the caller
//! calls it. Safe, and sound: what the caller does with the fn is its own.
#![forbid(unsafe_code)]

use std::marker::PhantomData;

/// A table of fns at a type.
pub struct Tab<T>(PhantomData<T>);
impl<T> Tab<T> {
    /// Swaps two values: a constant that only NAMES `mem::swap`.
    pub const SWAP: fn(&mut T, &mut T) = std::mem::swap::<T>;
}

/// A trait whose default constant names a fn that overwrites a value.
pub trait Ops: Sized {
    const PUT: fn(&mut Self, Self) = put::<Self>;
}

/// Overwrites `a` with `b`.
pub fn put<T>(a: &mut T, b: T) {
    *a = b;
}

/// Hands out `mem::swap` as a fn pointer, and runs nothing.
pub fn swapper<T>() -> fn(&mut T, &mut T) {
    std::mem::swap::<T>
}

/// Hands out a closure that swaps, and runs nothing.
pub fn closure_swapper<T>() -> impl Fn(&mut T, &mut T) {
    |a: &mut T, b: &mut T| std::mem::swap(a, b)
}

/// Hands out a boxed `dyn Fn` that swaps, and runs nothing.
pub fn boxed_swapper<T: 'static>() -> Box<dyn Fn(&mut T, &mut T)> {
    Box::new(|a: &mut T, b: &mut T| std::mem::swap(a, b))
}

/// Hands out a fn pointer that only measures what a `&` lets it see.
pub fn measure<T>() -> fn(&T) -> usize {
    std::mem::size_of_val::<T>
}

/// Measures what it is handed a `&mut` to, and writes nothing.
pub fn peek_len<T>(x: &mut T) -> usize {
    std::mem::size_of_val(x)
}

/// Hands out `peek_len` as a fn pointer.
pub fn reader<T>() -> fn(&mut T) -> usize {
    peek_len::<T>
}
