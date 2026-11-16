//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Cpanic=abort
//@ no-prefer-dynamic
//! A WHOLE-`core` IMPOSTOR: a `#![no_core]` crate whose file name makes its crate
//! name `core`, compiled verify-off the way Targo compiles every dependency unit,
//! and handed to the consumer as `--extern core=` (`aux-crate: core=...`). It is
//! NOT this compiler's resident `core`: it is loaded from the test's auxiliary
//! directory, never from the compiler's own target library directory.
//!
//! In a `#![no_core]` consumer graph the real `core` is never loaded, so nothing
//! contests the anchors this crate declares:
//!
//! * the `Range` LANG ITEM (`#[lang = "Range"]`) — the anchor
//!   `step_by_constructor::candidate` used to decide "this callee lives in the
//!   actual core crate";
//! * the `Iterator` DIAGNOSTIC ITEM, on a trait whose PROVIDED `step_by` panics
//!   (overflow-checked `u32::MAX + 1` on a value read from a `static`, so it is a
//!   run-time fact, not a constant);
//! * a `StepBy` at `iter::adapters::step_by` — which renders as
//!   `core::iter::adapters::step_by::StepBy`, the exact string `step_by_range`
//!   compares, because the crate's NAME is `core`.
//!
//! The consumer is
//! `step_by_constructor_no_core_range_lang_item_impostor_refuted.rs`; see there.
//! In a graph that loads the real `core` (any `#![no_std]` or std crate) rustc
//! refuses both anchors itself (E0152 duplicate lang item `Range`; "duplicate
//! diagnostic item ... `Iterator`"), so only a whole-`core` substitution reaches
//! the predicate.
#![feature(no_core, lang_items, rustc_attrs)]
#![allow(internal_features)]
#![no_core]

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}
impl Copy for u32 {}
impl Copy for usize {}
impl Copy for bool {}
#[lang = "legacy_receiver"]
pub trait LegacyReceiver {}
impl<T: PointeeSized> LegacyReceiver for &T {}
impl<T: PointeeSized> LegacyReceiver for &mut T {}
#[lang = "sync"]
pub unsafe trait Sync {}
unsafe impl Sync for u32 {}
#[lang = "drop_glue"]
fn drop_glue<T>(_: &mut T) {}

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

#[lang = "panic_location"]
pub struct Location<'a> {
    _file: &'a str,
    _line: u32,
    _col: u32,
}
// `#[track_caller]` as in real core: codegen lowers an overflow `Assert` to a
// call of this lang item that passes the caller `&Location`, so without it the
// call has one argument more than the function (an LLVM "Calling a function
// with bad signature!" abort on an assertions-enabled LLVM).
#[lang = "panic_const_add_overflow"]
#[track_caller]
fn panic_const_add_overflow() -> ! {
    loop {}
}

/// Read at run time, so the overflow below is not const-propagated away.
pub static MAX: u32 = 4294967295;

pub mod ops {
    #[lang = "Range"]
    pub struct Range<Idx> {
        pub start: Idx,
        pub end: Idx,
    }
}

pub mod iter {
    pub mod adapters {
        pub mod step_by {
            pub struct StepBy<I> {
                pub iter: I,
                pub step_minus_one: usize,
            }
        }
    }

    use self::adapters::step_by::StepBy;

    #[rustc_diagnostic_item = "Iterator"]
    pub trait Iterator {
        /// PROVIDED, exactly like the real `Iterator::step_by`, so the call
        /// resolves to THIS body (`instance.def_id() == callee`). It PANICS on
        /// every call: `u32::MAX + 1`, overflow-checked.
        #[inline(never)]
        fn step_by(self, step: usize) -> StepBy<Self>
        where
            Self: crate::Sized,
        {
            let _boom: u32 = crate::MAX + 1;
            StepBy { iter: self, step_minus_one: step }
        }
    }

    impl Iterator for crate::ops::Range<u32> {}
}
