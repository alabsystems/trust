#![no_std]
pub mod vec {
    pub struct Vec<T> {
        pub k: u64,
        pub t: core::marker::PhantomData<T>,
    }
    impl<'a, T> IntoIterator for &'a Vec<T> {
        type Item = u64;
        type IntoIter = core::ops::RangeFrom<u64>;
        #[inline(never)]
        fn into_iter(self) -> core::ops::RangeFrom<u64> {
            core::ops::RangeFrom { start: 0u64 }
        }
    }
}
