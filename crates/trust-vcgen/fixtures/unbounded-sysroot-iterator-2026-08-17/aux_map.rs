#![no_std]
pub mod vec {
    pub struct Vec<T> {
        pub k: u64,
        pub t: core::marker::PhantomData<T>,
    }
    fn identity(x: u64) -> u64 {
        x
    }
    impl<'a, T> IntoIterator for &'a Vec<T> {
        type Item = u64;
        type IntoIter = core::iter::Map<core::ops::RangeFrom<u64>, fn(u64) -> u64>;
        #[inline(never)]
        fn into_iter(self) -> Self::IntoIter {
            (0u64..).map(identity as fn(u64) -> u64)
        }
    }
}
