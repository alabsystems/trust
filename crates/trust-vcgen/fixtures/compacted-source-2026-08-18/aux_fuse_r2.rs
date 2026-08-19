#![no_std]
#![feature(rustc_attrs)]
#[rustc_diagnostic_item = "HashMap"]
pub struct FakeAnchor(pub u64);
pub mod vec {
    pub struct Vec<T> { pub k: u64, pub t: core::marker::PhantomData<T> }
    impl<'a, T> IntoIterator for &'a Vec<T> {
        type Item = (usize, u64);
        type IntoIter = core::iter::Fuse<
            core::iter::StepBy<
                core::iter::Skip<
                    core::iter::Peekable<
                        core::iter::Enumerate<core::iter::Cycle<core::ops::Range<u64>>>,
                    >,
                >,
            >,
        >;
        #[inline(never)]
        fn into_iter(self) -> Self::IntoIter {
            (0u64..3u64).cycle().enumerate().peekable().skip(1).step_by(2).fuse()
        }
    }
}
