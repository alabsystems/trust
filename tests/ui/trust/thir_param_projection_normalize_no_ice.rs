//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Awarnings
//@ dont-check-compiler-stderr
//@ build-pass
//! Regression for param-bearing types reaching THIR-to-TrustIR's
//! `fully_monomorphized` normalization helpers while the body is still generic.
//!
//! These are the three shapes that previously reached
//! `type_of_const_param(..)` with an empty caller-bounds environment and caused
//! a hard compiler ICE (not a recoverable normalization error):
//!
//! - `&<[T; N] as Index<usize>>::Output` in the fat-shape classifier;
//! - `Option<<IntoIter<T, N> as Iterator>::Item>` in aggregate field checks;
//! - `<Simd<u8, N> as SimdPartialEq>::Mask` in the same generic shape lane.
//!
//! Param-bearing inputs must now stay un-normalized and flow through the
//! existing conservative shape/mismatch gates. This fixture needs only to
//! build under the live Trust pipeline; any return of the old ICE is a failure.

#![feature(portable_simd)]

use std::array::IntoIter;
use std::ops::Index;
use std::simd::cmp::SimdPartialEq;
use std::simd::Simd;

pub struct ProjectedField<T>(pub T);

pub enum ProjectedVariant<T> {
    Some(T),
    None,
}

#[inline(never)]
pub fn index_output<T, const N: usize>(value: &<[T; N] as Index<usize>>::Output) -> usize {
    std::mem::size_of_val(value)
}

#[inline(never)]
pub fn iterator_item<T, const N: usize>(
    value: Option<<IntoIter<T, N> as Iterator>::Item>,
) -> ProjectedField<Option<<IntoIter<T, N> as Iterator>::Item>> {
    ProjectedField(value)
}

#[inline(never)]
pub fn iterator_item_variant<T, const N: usize>(
    value: <IntoIter<T, N> as Iterator>::Item,
) -> ProjectedVariant<<IntoIter<T, N> as Iterator>::Item> {
    ProjectedVariant::Some(value)
}

#[inline(never)]
pub fn simd_mask<const N: usize>(mask: <Simd<u8, N> as SimdPartialEq>::Mask) -> usize {
    std::mem::size_of_val(&mask)
}

pub fn exercise_index<T, const N: usize>(array: &[T; N]) -> usize {
    index_output::<T, N>(&array[0])
}

pub fn exercise_iterator_item<T, const N: usize>(value: T) {
    let _ = iterator_item::<T, N>(Some(value));
}

pub fn exercise_iterator_variant<T, const N: usize>(value: T) {
    let _ = iterator_item_variant::<T, N>(value);
}

pub fn exercise_simd<const N: usize>(lhs: Simd<u8, N>, rhs: Simd<u8, N>) -> usize {
    simd_mask::<N>(lhs.simd_eq(rhs))
}

fn main() {}
