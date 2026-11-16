//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Cpanic=abort
//@ no-prefer-dynamic
//@ edition: 2021
//! A WHOLE-`core` SUBSTITUTE owning the diagnostic items that four typed
//! call-credit identities in `trust_verify.rs` read as "this is core's type or
//! trait": `Cell` (`cell_set_call_payload_needs_no_drop`), `Option` and `Result`
//! (`moved_value_arg_call_operands_need_no_drop`), and `IntoIterator`
//! (`callee_is_total_std_into_iter`, slice/array receiver arm). A `#![no_core]`
//! crate whose file name makes its crate name `core`, compiled verify-off the way
//! Targo compiles every dependency unit, and handed to the consumer as
//! `--extern core=` (`aux-crate: core=...`). It is loaded from the test's
//! auxiliary directory, never from the compiler's own target library directory,
//! so it is NOT this compiler's resident `core`.
//!
//! In a `#![no_core]` consumer graph the real `core` is never loaded, so rustc's
//! duplicate-diagnostic-item check never fires and this crate owns all four.
//!
//! Each method the consumer calls has the signature of core's method and a body
//! that is not core's: an overflow-checked `u32::MAX + 1` on a value read from a
//! `static`, so the panic is a run-time fact, not a constant. The premises those
//! identities rest on (`Cell::set` is a swap plus a drop, the moved-value methods
//! are a match plus a move, `<&[T]>::into_iter` builds a pointer pair) are claims
//! about core's bodies, which is why the identity has to be core's own.
//!
//! Consumers: `typed_call_arms_core_substitution_impostor_refuted.rs`; the
//! resident control is `typed_call_arms_resident_core_keeps_credit.rs`.
#![feature(no_core, lang_items, rustc_attrs, auto_traits)]
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
// `#[track_caller]` as in real core: codegen lowers an overflow Assert to a
// call of this lang item that passes the caller `&Location`, so without it the
// call has one argument more than the function (an LLVM "Calling a function
// with bad signature!" abort on an assertions-enabled LLVM).
#[lang = "panic_const_add_overflow"]
#[track_caller]
fn panic_const_add_overflow() -> ! {
    loop {}
}

/// Read at run time, so the overflow in each method is not const-folded.
pub static MAX: u32 = 4294967295;

pub mod cell {
    #[rustc_diagnostic_item = "Cell"]
    pub struct Cell<T> {
        pub value: T,
    }
    impl<T> Cell<T> {
        #[inline(never)]
        pub fn set(&self, _val: T) {
            let _boom: u32 = crate::MAX + 1;
        }
    }
}

pub mod option {
    #[rustc_diagnostic_item = "Option"]
    pub enum Option<T> {
        None,
        Some(T),
    }
    impl<T> Option<T> {
        #[inline(never)]
        pub fn unwrap_or(self, default: T) -> T {
            let _boom: u32 = crate::MAX + 1;
            default
        }
        #[inline(never)]
        pub fn ok_or<E>(self, err: E) -> crate::result::Result<T, E> {
            let _boom: u32 = crate::MAX + 1;
            crate::result::Result::Err(err)
        }
    }
}

pub mod result {
    #[rustc_diagnostic_item = "Result"]
    pub enum Result<T, E> {
        Ok(T),
        Err(E),
    }
    impl<T, E> Result<T, E> {
        #[inline(never)]
        pub fn unwrap_or(self, default: T) -> T {
            let _boom: u32 = crate::MAX + 1;
            default
        }
        #[inline(never)]
        pub fn ok(self) -> crate::option::Option<T> {
            let _boom: u32 = crate::MAX + 1;
            crate::option::Option::None
        }
    }
}

pub mod iter {
    pub struct Iter<'a> {
        pub rest: &'a [u32],
    }
    #[rustc_diagnostic_item = "IntoIterator"]
    pub trait IntoIterator {
        type Item;
        type IntoIter;
        fn into_iter(self) -> Self::IntoIter;
    }
    impl<'a> IntoIterator for &'a [u32] {
        type Item = &'a u32;
        type IntoIter = Iter<'a>;
        #[inline(never)]
        fn into_iter(self) -> Iter<'a> {
            let _boom: u32 = crate::MAX + 1;
            Iter { rest: self }
        }
    }
}
