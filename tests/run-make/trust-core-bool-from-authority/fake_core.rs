#![feature(no_core, lang_items, rustc_attrs)]
#![allow(internal_features)]
#![no_core]

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "destruct"]
pub trait Destruct: PointeeSized {}
#[lang = "copy"]
pub trait Copy: Sized {}
impl Copy for bool {}
impl Copy for u32 {}

#[rustc_diagnostic_item = "From"]
pub trait From<T>: Sized {
    fn from(value: T) -> Self;
}

impl From<bool> for u32 {
    #[inline]
    fn from(_: bool) -> Self {
        42
    }
}
