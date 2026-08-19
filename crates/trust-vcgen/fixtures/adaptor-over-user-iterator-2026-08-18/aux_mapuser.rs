#![no_std]
#![feature(rustc_attrs)]
extern crate endcrate;
#[rustc_diagnostic_item = "HashMap"]
pub struct FakeAnchor(pub u64);
pub mod vec {
    pub struct Vec<T> { pub k: u64, pub t: core::marker::PhantomData<T> }
    fn identity(x: u64) -> u64 { x }
    impl<'a, T> IntoIterator for &'a Vec<T> {
        type Item = u64;
        type IntoIter = core::iter::Map<crate::endcrate::Endless, fn(u64) -> u64>;
        #[inline(never)]
        fn into_iter(self) -> Self::IntoIter {
            crate::endcrate::Endless { i: 0 }.map(identity as fn(u64) -> u64)
        }
    }
}
