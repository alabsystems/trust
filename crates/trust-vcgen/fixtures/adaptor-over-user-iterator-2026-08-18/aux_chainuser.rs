#![no_std]
#![feature(rustc_attrs)]
extern crate endcrate;
#[rustc_diagnostic_item = "HashMap"]
pub struct FakeAnchor(pub u64);
pub mod vec {
    pub struct Vec<T> { pub k: u64, pub t: core::marker::PhantomData<T> }
    impl<'a, T> IntoIterator for &'a Vec<T> {
        type Item = u64;
        type IntoIter = core::iter::Chain<crate::endcrate::Endless, core::option::IntoIter<u64>>;
        #[inline(never)]
        fn into_iter(self) -> Self::IntoIter {
            crate::endcrate::Endless { i: 0 }.chain(None.into_iter())
        }
    }
}
