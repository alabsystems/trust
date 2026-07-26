//@ check-pass
//@ compile-flags: --crate-type=lib

#![allow(dead_code)]

// Regression test for an associated type bound that must preserve the
// implied outlives fact from `&'a S`: `S: 'a`.

trait IntoIteratorLike {
    type Item;
}

trait ArrayLength<T> {}

trait FromIteratorLike<T> {}

unsafe trait GenericSequence<T>: Sized + IntoIteratorLike {
    type Length: ArrayLength<T>;
    type Sequence: GenericSequence<T, Length = Self::Length> + FromIteratorLike<T>;

    fn generate<F>(f: F) -> Self::Sequence
    where
        F: FnMut(usize) -> T;
}

unsafe impl<'a, T: 'a, S: GenericSequence<T>> GenericSequence<T> for &'a S
where
    &'a S: IntoIteratorLike,
{
    type Length = S::Length;
    type Sequence = S::Sequence;

    fn generate<F>(f: F) -> Self::Sequence
    where
        F: FnMut(usize) -> T,
    {
        S::generate(f)
    }
}

unsafe impl<'a, T: 'a, S: GenericSequence<T>> GenericSequence<T> for &'a mut S
where
    &'a mut S: IntoIteratorLike,
{
    type Length = S::Length;
    type Sequence = S::Sequence;

    fn generate<F>(f: F) -> Self::Sequence
    where
        F: FnMut(usize) -> T,
    {
        S::generate(f)
    }
}
