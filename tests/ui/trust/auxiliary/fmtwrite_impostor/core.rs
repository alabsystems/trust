//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Cpanic=abort
//@ no-prefer-dynamic
//@ edition: 2021
//! A WHOLE-`core` SUBSTITUTE that owns core's FORMATTING anchors: a `#![no_core]`
//! crate whose file name makes its crate name `core`, compiled verify-off the way
//! Targo compiles every dependency unit, and handed to the consumer as
//! `--extern core=` (`aux-crate: core=...`). It is NOT this compiler's resident
//! `core`: it is loaded from the test's auxiliary directory, never from the
//! compiler's own target library directory.
//!
//! It declares, by DIAGNOSTIC ITEM, `FmtWrite` (`fmt::Write`), `Formatter`,
//! `Debug` and `Display` — every anchor the writer-relative class
//! (`trust_verify/fmt_writer_relative.rs`) used to identify core's formatting
//! machinery. Its `Formatter` exposes its writer as a public field, so a
//! formatting impl can make the virtual `<dyn fmt::Write>::write_str` call the
//! class exempts.
//!
//! It also declares `FmtArgumentsFromStr` on an `Arguments::from_str`, and gives
//! its `fmt::Write` a PROVIDED `write_fmt` that PANICS on every call (an
//! overflow-checked `255u8 + 1` read from a `static`). That is the body the
//! static-str `write_fmt` reduction (`trust_verify/static_str_write_fmt.rs`, and
//! its `dyn` twin in `dyn_dispatch_reliance.rs`) took for core's default
//! `write_fmt` and reduced to the receiver's own `write_str`.
//!
//! No graph that loads the real `core` lets a crate own these items (measured on
//! stage-1 `trustc` at `4e5d01f0041`: a `#![no_std]` crate declaring
//! `#[rustc_diagnostic_item = "FmtWrite"]` fails with "duplicate diagnostic item
//! ... first defined in crate `core`"; a `#![no_core]` one that declares the
//! lang items a trait needs collides with core's `sized`, E0152). Whole-`core`
//! substitution is the one graph that reaches the predicates. `#![compiler_builtins]`
//! is what makes it possible: without it rustc injects the sysroot's
//! `compiler_builtins` into the `#![no_std]` consumer, which loads the real
//! `core` and collides (E0152, duplicate `sized`).
//!
//! The consumers are
//! `fmt_writer_relative_fmtwrite_core_substitution_impostor_refuted.rs` and
//! `static_str_write_fmt_fmtwrite_core_substitution_impostor_refuted.rs`.
#![feature(no_core, lang_items, rustc_attrs, compiler_builtins, auto_traits)]
#![allow(internal_features)]
#![compiler_builtins]
#![no_std]
#![no_core]

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy: Sized {}
impl Copy for bool {}
impl Copy for char {}
impl Copy for u8 {}
impl Copy for usize {}
impl<'a, T: PointeeSized> Copy for &'a T {}
#[lang = "legacy_receiver"]
pub trait LegacyReceiver {}
impl<T: PointeeSized> LegacyReceiver for &T {}
impl<T: PointeeSized> LegacyReceiver for &mut T {}
#[lang = "sync"]
pub unsafe trait Sync {}
unsafe impl Sync for u8 {}
#[lang = "freeze"]
pub unsafe auto trait Freeze {}
#[lang = "unsize"]
pub trait Unsize<T: PointeeSized>: PointeeSized {}
#[lang = "coerce_unsized"]
pub trait CoerceUnsized<T: PointeeSized> {}
impl<'a, 'b: 'a, T: PointeeSized + Unsize<U>, U: PointeeSized> CoerceUnsized<&'a U> for &'b T {}
impl<'a, 'b: 'a, T: PointeeSized + Unsize<U>, U: PointeeSized> CoerceUnsized<&'a mut U>
    for &'b mut T
{
}
#[lang = "dispatch_from_dyn"]
pub trait DispatchFromDyn<T> {}
impl<'a, T: PointeeSized + Unsize<U>, U: PointeeSized> DispatchFromDyn<&'a U> for &'a T {}
impl<'a, T: PointeeSized + Unsize<U>, U: PointeeSized> DispatchFromDyn<&'a mut U> for &'a mut T {}
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
// `#[track_caller]` as in real core: codegen lowers an overflow `Assert` to a
// call of this lang item that passes the caller `&Location`, so without it the
// call has one argument more than the function (an LLVM "Calling a function
// with bad signature!" abort on an assertions-enabled LLVM).
#[lang = "panic_const_add_overflow"]
#[track_caller]
fn panic_const_add_overflow() -> ! {
    loop {}
}
/// Read at run time, so the overflow in `write_fmt` is not const-folded.
pub static BIG: u8 = 255;

#[lang = "drop_glue"]
fn drop_glue<T>(_: &mut T) {}

pub enum Option<T> {
    None,
    Some(T),
}
pub enum Result<T, E> {
    Ok(T),
    Err(E),
}

pub mod result {
    pub use crate::Result;
}

pub mod prelude {
    pub mod rust_2021 {
        pub use crate::{Copy, Option, Result, Sized};
    }
}

pub mod fmt {
    pub struct Error;
    pub type Result = crate::Result<(), Error>;

    pub struct Arguments<'a> {
        pub s: &'a str,
    }
    impl<'a> Arguments<'a> {
        #[rustc_diagnostic_item = "FmtArgumentsFromStr"]
        pub fn from_str(s: &'static str) -> Arguments<'a> {
            Arguments { s }
        }
    }

    #[rustc_diagnostic_item = "FmtWrite"]
    pub trait Write {
        fn write_str(&mut self, s: &str) -> Result;
        fn write_char(&mut self, c: char) -> Result;
        /// PROVIDED, like the real `Write::write_fmt`, so a call resolves to THIS
        /// body. It PANICS on every call.
        #[inline(never)]
        fn write_fmt(&mut self, args: Arguments<'_>) -> Result {
            let _boom: u8 = crate::BIG + 1;
            self.write_str(args.s)
        }
    }

    #[rustc_diagnostic_item = "Formatter"]
    pub struct Formatter<'a> {
        pub buf: &'a mut (dyn Write + 'a),
    }

    #[rustc_diagnostic_item = "Debug"]
    pub trait Debug {
        fn fmt(&self, f: &mut Formatter<'_>) -> Result;
    }

    #[rustc_diagnostic_item = "Display"]
    pub trait Display {
        fn fmt(&self, f: &mut Formatter<'_>) -> Result;
    }
}
