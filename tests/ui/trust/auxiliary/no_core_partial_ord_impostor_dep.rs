//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A `#![no_core]` dependency, compiled verify-off the way Targo compiles every
//! dependency unit, that CLAIMS core's `partial_ord` LANG ITEM and core's `Ord`
//! DIAGNOSTIC ITEM for traits of its own, whose DEFAULT comparators (`lt`,
//! `cmp`, `max`) PANIC on every call: an overflow-checked `255u8 + 1` on a value
//! read from a `static`, so the overflow is a run-time fact.
//!
//! It must declare the sized-family lang items itself, because it has no core.
//! That is also why it can own these anchors only in a `#![no_core]` graph: in any
//! graph that loads the real `core` (every `#![no_std]` or std crate) rustc
//! refuses it (E0152 duplicate lang item `sized`/`partial_ord`; "duplicate
//! diagnostic item ... `Ord`"). The consumer is
//! `partialord_sublane_no_core_lang_item_impostor_refuted.rs`.
#![feature(no_core, lang_items, rustc_attrs)]
#![allow(internal_features, unconditional_panic, arithmetic_overflow)]
#![no_core]

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}
impl Copy for u8 {}
impl Copy for usize {}
impl Copy for bool {}
impl Copy for u32 {}
#[lang = "legacy_receiver"]
pub trait LegacyReceiver {}
impl<T: PointeeSized> LegacyReceiver for &T {}
#[lang = "sync"]
pub unsafe trait Sync {}
unsafe impl Sync for u8 {}

#[lang = "add"]
pub trait Add<Rhs = Self> {
    type Output;
    fn add(self, rhs: Rhs) -> Self::Output;
}
impl Add for u8 {
    type Output = u8;
    fn add(self, rhs: u8) -> u8 {
        self + rhs
    }
}

#[lang = "panic_location"]
pub struct Location<'a> {
    _file: &'a str,
    _line: u32,
    _col: u32,
}

#[lang = "drop_glue"]
fn drop_glue<T>(_: &mut T) {}
// `#[track_caller]` as in real core: codegen lowers an overflow `Assert` to a
// call of this lang item that passes the caller `&Location`, so without it the
// call has one argument more than the function (an LLVM "Calling a function
// with bad signature!" abort on an assertions-enabled LLVM).
#[lang = "panic_const_add_overflow"]
#[track_caller]
fn panic_const_add_overflow() -> ! {
    loop {}
}

/// Read at run time, so the overflow in the default bodies is not const-folded.
pub static BIG: u8 = 255;

#[lang = "partial_ord"]
pub trait PartialOrd<Rhs: PointeeSized = Self>: PointeeSized {
    fn partial_cmp(&self, other: &Rhs) -> u8;
    #[inline(never)]
    fn lt(&self, _other: &Rhs) -> bool {
        let _boom: u8 = BIG + 1;
        false
    }
}

#[rustc_diagnostic_item = "Ord"]
pub trait Ord: PointeeSized {
    #[inline(never)]
    fn cmp(&self, _other: &Self) -> u8 {
        BIG + 1
    }
    #[inline(never)]
    fn max(self, other: Self) -> Self
    where
        Self: Sized + Copy,
    {
        let _boom: u8 = BIG + 1;
        other
    }
}
