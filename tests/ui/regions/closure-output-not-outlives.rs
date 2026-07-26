//@ check-pass
//@ compile-flags: -Ztrust-verify=off
//@ edition: 2021
#![allow(dead_code)]

// Regression test for the `generic-array` 0.14.7 shape: reference impls of a
// trait with a `FnMut(...) -> T` method predicate must be able to prove that the
// self type implied by `&'a S`/`&'a mut S` is valid for `'a`.
trait GenericSequence<T>: Sized + IntoIterator {
    type Sequence: GenericSequence<T> + FromIterator<T>;

    fn generate<F>(f: F) -> Self::Sequence
    where
        F: FnMut(usize) -> T;
}

impl<'a, T: 'a, S: GenericSequence<T>> GenericSequence<T> for &'a S
where
    &'a S: IntoIterator,
{
    type Sequence = S::Sequence;

    fn generate<F>(f: F) -> Self::Sequence
    where
        F: FnMut(usize) -> T,
    {
        S::generate(f)
    }
}

impl<'a, T: 'a, S: GenericSequence<T>> GenericSequence<T> for &'a mut S
where
    &'a mut S: IntoIterator,
{
    type Sequence = S::Sequence;

    fn generate<F>(f: F) -> Self::Sequence
    where
        F: FnMut(usize) -> T,
    {
        S::generate(f)
    }
}

fn main() {}
