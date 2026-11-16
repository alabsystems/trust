//! Ordinary Rust inputs; no layout, active union field or semantic premise.
#![feature(type_alias_impl_trait)]
#![allow(dead_code)]

pub type Hidden = impl Copy;
#[define_opaque(Hidden)]
pub fn define_hidden() -> Hidden {
    0_u8
}

pub trait Pick {
    type Out;
}
pub struct Input<T>(pub std::marker::PhantomData<T>);
impl<T> Pick for Input<T> {
    type Out = u8;
}
pub struct Warm<T: Pick, R> {
    pub back: *const R,
    pub selected: T::Out,
}
pub struct A<T>(pub T);
pub struct B<T>(pub A<T>);
pub struct C<T>(pub B<T>);
pub struct D<T>(pub C<T>);

// The shallow holder depends on the active root and cannot be a closed type
// fact. Only its independently completed associated-type reader may be reused.
pub struct Reuse {
    pub shallow: Warm<Input<u64>, Reuse>,
    pub deep: D<Warm<Input<u64>, Reuse>>,
}
pub fn case_reuse(_: &Reuse) {}

pub struct UnsafeSibling {
    pub shallow: Warm<Input<u64>, UnsafeSibling>,
    pub deep: D<Warm<Input<u64>, UnsafeSibling>>,
    pub unsafe_last: Hidden,
}
pub fn case_unsafe_sibling(_: &UnsafeSibling) {}

pub struct WrongArgs {
    pub shallow: Warm<Input<u64>, WrongArgs>,
    pub deep: D<Warm<Input<Hidden>, WrongArgs>>,
}
pub fn case_wrong_args(_: &WrongArgs) {}

pub const fn nonleaf_length() -> usize {
    let mut n = 0;
    while n < 2 {
        n += 1;
    }
    n
}
pub struct Nonleaf;
impl Pick for Nonleaf {
    type Out = [u8; nonleaf_length()];
}
pub struct NonleafRoot {
    pub shallow: Warm<Nonleaf, NonleafRoot>,
    pub deep: D<Warm<Nonleaf, NonleafRoot>>,
}
pub fn case_nonleaf_rhs(_: &NonleafRoot) {}

pub const LEAF_LENGTH: usize = 2;
pub struct LeafInput;
impl Pick for LeafInput {
    type Out = [u8; LEAF_LENGTH];
}
pub struct LeafEpoch {
    pub shallow: Warm<LeafInput, LeafEpoch>,
    pub deep: D<Warm<LeafInput, LeafEpoch>>,
}
pub fn case_epoch_leaf(_: &LeafEpoch) {}

pub struct Growing<T> {
    pub next: *const Growing<(T,)>,
    pub marker: std::marker::PhantomData<T>,
}
impl<T> Pick for Growing<T> {
    type Out = u8;
}
pub struct GrowingRoot {
    pub shallow: Warm<Growing<u8>, GrowingRoot>,
    pub deep: D<Warm<Growing<u8>, GrowingRoot>>,
}
pub fn case_growing(_: &GrowingRoot) {}
