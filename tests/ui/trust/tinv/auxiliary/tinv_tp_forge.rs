//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ edition: 2021
//@ no-prefer-dynamic
//! A third-party (verify-off) crate with SAFE signatures and `unsafe` bodies: the census
//! threat model of TINV D1 and rule 4. Its signatures name what they forge or corrupt
//! only through a projection of a type argument.

/// Returns an `I::Item` made of zero bytes.
pub fn forge<I: Iterator>() -> I::Item {
    unsafe { core::mem::zeroed() }
}

/// Overwrites an `I::Item` with `0xff` bytes.
pub fn corrupt<I: Iterator>(x: &mut I::Item) {
    unsafe { core::ptr::write_bytes(x as *mut I::Item, 0xff, 1) }
}

/// Overwrites ANY value (here: a `Peekable` that holds the item in its private storage).
pub fn corrupt_any<T>(t: &mut T) {
    unsafe { core::ptr::write_bytes(t as *mut T as *mut u8, 0, 0) }
}

/// A third-party holder whose storage is a `Peekable` (review hole C).
pub struct Hold<I: Iterator>(pub core::iter::Peekable<I>);

/// A third-party holder two levels above an `Option<I::Item>` (review hole C).
pub struct HoldInner<I: Iterator>(pub Inner<I>);

/// The inner level of [`HoldInner`].
pub struct Inner<I: Iterator>(pub Option<I::Item>);

/// A third-party iterator whose `Item` is `I::Item`, forged from zero bytes (review hole
/// D): nothing in `Conjure<I>`'s storage reaches the item type.
pub struct Conjure<I>(core::marker::PhantomData<I>);

impl<I> Conjure<I> {
    pub fn new() -> Self {
        Conjure(core::marker::PhantomData)
    }
}

impl<I: Iterator> Iterator for Conjure<I> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        Some(unsafe { core::mem::zeroed() })
    }
}

/// Calls `f` on every item of `it` (review: a callback whose argument type is named only by
/// the where-clause `F: FnMut(I::Item)`).
pub fn each<I: Iterator, F: FnMut(I::Item)>(it: I, mut f: F) {
    for x in it {
        f(x)
    }
}

/// Calls `f` with a value of `T` forged from zero bytes (review: `F: FnOnce(T)`).
pub fn each_forge<T, F: FnOnce(T)>(f: F) {
    f(unsafe { core::mem::zeroed() })
}

/// A third-party handle that keeps a raw `*mut T` and writes through it from `&self`.
pub struct Alias<T>(*mut T);

impl<T> Alias<T> {
    pub fn from_box(b: Box<T>) -> Self {
        Alias(Box::into_raw(b))
    }
    pub fn poke(&self) {
        unsafe { core::ptr::write_bytes(self.0 as *mut u8, 0xff, 1) }
    }
    pub fn get(&self) -> &T {
        unsafe { &*self.0 }
    }
}

/// A third-party trait whose provided method forges `Self::In` (round 4).
pub trait Sink {
    type In;
    fn take(&mut self, x: Self::In);
    fn pump(&mut self) {
        self.take(unsafe { core::mem::zeroed() })
    }
}
