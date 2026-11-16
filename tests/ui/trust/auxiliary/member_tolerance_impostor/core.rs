//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Cpanic=abort -Zalways-encode-mir
//@ no-prefer-dynamic
//! A WHOLE-`core` IMPOSTOR for the bundled std-member runtime-checked disposition
//! (`std_member_tolerance_identity_impostor_refuted.rs`): a `#![no_core]` crate
//! whose file name makes its crate name `core`, compiled verify-off the way Targo
//! compiles every dependency unit, handed to the consumer as `--extern core=`
//! (`aux-crate: core=...`). It is NOT this compiler's resident `core`.
//!
//! The body is `step_by_range_impostor/core.rs` (the lang items a `#![no_core]`
//! graph needs, and the overflow-checked `Add` it panics through) plus two
//! functions whose rendered paths are `core::bump` and `core::boom` — the spelling
//! the removed string test (`member_path_is_foundational_std_member`) read as
//! "foundational std":
//!
//! * `bump(x) = x + 1` carries an `Overflow(Add)` Assert, which the bundled-member
//!   admission lane refuses as `AssertKindOutsideLane`;
//! * `boom(x)` overflows (`MAX + x`) for every `x > 0` — a run-time panic path of
//!   this crate's own code, not std's.
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
// with bad signature!" abort on an assertions-enabled LLVM; 7ad4f7fb782).
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

/// `x + 1`, overflow-checked: an `Overflow(Add)` Assert in an IMPOSTOR body.
#[inline(never)]
pub fn bump(x: u32) -> u32 {
    x + 1
}

/// Overflows for every `x > 0`: `MAX` is read from a `static`, so it is a run-time
/// fact, and the Assert is this impostor's own code.
#[inline(never)]
pub fn boom(x: u32) -> u32 {
    MAX + x
}
