//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Cpanic=abort
//@ no-prefer-dynamic
//@ edition: 2021
//! A WHOLE-`core` SUBSTITUTE that renders core's numeric-family spellings: the
//! inherent `num::<impl u32>::{ilog2, strict_add}` (allowed by
//! `#![rustc_coherence_is_core]`) and the trait method `cmp::Ord::clamp` for `i32`.
//! A `#![no_core]` crate whose file name makes its crate name `core`, compiled
//! verify-off the way Targo compiles every dependency unit, and handed to the
//! consumer as `--extern core=` (`aux-crate: core=...`). It is loaded from the
//! test's auxiliary directory, never from the compiler's own target library
//! directory, so it is NOT this compiler's resident `core`, and the extractor stamps
//! its paths: `__trust_crate@<id>::core::num::<impl u32>::ilog2`,
//! `__trust_crate@<id>::<i32 as core::cmp::Ord>::clamp`. Those are exactly the
//! spellings a stamped GENUINE core renders, which the numeric family's minting
//! functions read past one leading stamp since wave 23.
//!
//! Each method has core's signature and a body that is not core's: it panics (an
//! overflow-checked `u32::MAX + 1` on a value read from a `static`, so the panic is
//! a run-time fact) on an argument core's method accepts (`ilog2(5)`,
//! `strict_add(5, _)`, `7.clamp(lo, hi)`), and never on the argument core's own
//! method panics on.
//!
//! Consumer: `stamped_forged_core_numeric_family_refused.rs`.
#![feature(no_core, lang_items, rustc_attrs, auto_traits)]
#![allow(internal_features)]
#![no_core]
#![rustc_coherence_is_core]

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}
impl Copy for u32 {}
impl Copy for i32 {}
impl Copy for bool {}
impl<'a, T: PointeeSized> Copy for &'a T {}
#[lang = "legacy_receiver"]
pub trait LegacyReceiver {}
impl<T: PointeeSized> LegacyReceiver for &T {}
impl<T: PointeeSized> LegacyReceiver for &mut T {}
#[lang = "sync"]
pub unsafe trait Sync {}
unsafe impl Sync for u32 {}
#[lang = "freeze"]
pub unsafe auto trait Freeze {}
#[lang = "drop_glue"]
fn drop_glue<T>(_: &mut T) {}

#[lang = "panic_location"]
pub struct Location<'a> {
    _file: &'a str,
    _line: u32,
    _col: u32,
}
#[lang = "panic_const_add_overflow"]
#[track_caller]
fn panic_const_add_overflow() -> ! {
    loop {}
}

#[lang = "add"]
pub trait Add<Rhs = Self> {
    type Output;
    fn add(self, rhs: Rhs) -> Self::Output;
}
impl Add for u32 {
    type Output = u32;
    fn add(self, rhs: u32) -> u32 {
        self + rhs
    }
}

#[lang = "eq"]
pub trait PartialEq<Rhs = Self> {
    fn eq(&self, other: &Rhs) -> bool;
    fn ne(&self, other: &Rhs) -> bool;
}
#[lang = "partial_ord"]
pub trait PartialOrd<Rhs = Self>: PartialEq<Rhs> {
    fn lt(&self, other: &Rhs) -> bool;
    fn le(&self, other: &Rhs) -> bool;
    fn gt(&self, other: &Rhs) -> bool;
    fn ge(&self, other: &Rhs) -> bool;
}
macro_rules! cmp_impls {
    ($($t:ty)*) => {$(
        impl PartialEq for $t {
            fn eq(&self, other: &$t) -> bool { *self == *other }
            fn ne(&self, other: &$t) -> bool { *self != *other }
        }
        impl PartialOrd for $t {
            fn lt(&self, other: &$t) -> bool { *self < *other }
            fn le(&self, other: &$t) -> bool { *self <= *other }
            fn gt(&self, other: &$t) -> bool { *self > *other }
            fn ge(&self, other: &$t) -> bool { *self >= *other }
        }
    )*};
}
cmp_impls!(u32 i32);

/// Read at run time, so the overflow in each method is not const-folded.
pub static MAX: u32 = 4294967295;

pub mod num {
    impl u32 {
        #[inline(never)]
        pub fn ilog2(self) -> u32 {
            if self == 5 {
                let _boom: u32 = crate::MAX + 1;
            }
            0
        }
        #[inline(never)]
        pub fn strict_add(self, rhs: u32) -> u32 {
            if self == 5 {
                let _boom: u32 = crate::MAX + 1;
            }
            rhs
        }
    }
}

pub mod cmp {
    pub trait Ord: crate::Sized {
        fn clamp(self, min: Self, max: Self) -> Self;
    }
    impl Ord for i32 {
        #[inline(never)]
        fn clamp(self, min: i32, _max: i32) -> i32 {
            if self == 7 {
                let _boom: u32 = crate::MAX + 1;
            }
            min
        }
    }
}
