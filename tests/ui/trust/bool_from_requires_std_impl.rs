//@ revisions: default certify memsafe
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memsafe] compile-flags: -Ztrust-policy=memory-safe
//@[default] check-fail
//@[certify] check-fail
//@[memsafe] check-pass
//@ dont-check-compiler-stderr
//! The `bool -> integer` fact `0 <= dest <= 1` is std's `From<bool>` impl only: a
//! callee defined in a real sysroot crate (its compiler-minted key) whose rendering
//! is EXACTLY `<{int} as core::convert::From<bool>>::from` (NUM-METHOD-ANCHOR-1).
//!
//! `call_facts::is_bool_from_call` accepted `From<bool>` plus `as core::` ANYWHERE.
//! `conv::<From<bool>, <T as core::ops::Not>::Output>(flag)` below — a user struct
//! named `From`, a user `conv` returning 7 — renders
//! `…::conv::<…::From<bool>, <T as core::ops::bit::Not>::Output>`, so
//! `semantic_guard` pinned `x` to `{0, 1}` and `arr[x as usize]` (len 2) read `bounds
//! proved`; the program panics with index 7 (`scratchpad/scout13/inv-boolfrom`).
//!
//! BEFORE (`scratchpad/stage1-w11fix`, each revision's flags plus `-Zui-testing
//! -Zdeduplicate-diagnostics=no -A unused --emit=metadata`, 2026-10-04): every
//! revision exits 0 with no diagnostic at all, so no annotation below fires.
//!
//! AFTER (predicted, then measured): `conv` is keyed to this crate, so it is
//! not std's. The annotations (and the per-revision pass modes: the memory-safe
//! policy reports an unproved bounds row as a warning) were derived on the BEFORE
//! compiler from a twin of this file with the struct renamed `Frum` (nothing else
//! changed), which the BEFORE recognizer already refuses: checked the way
//! compiletest checks, it matches all three revisions. The std controls `std_from`
//! and `std_u32_from` stay proved before and after: they call
//! `<usize as core::convert::From<bool>>::from` / `<u32 as …>::from`, keyed `core`.
//! Measured on the stage 1 of `4463aeeb6d` (2026-10-04): every annotation below fires in
//! every revision and nothing else is reported. `lie`'s `bounds` row reads failed under
//! default and certify (memory-safe: the panic is skipped as an assumption).

/// A user type named `From`.
pub struct From<X>(pub X);

/// Returns 7 whatever it is given.
pub fn conv<A, B>(_b: bool) -> u32 {
    7
}

/// `conv::<From<bool>, <T as core::ops::Not>::Output>` contains `From<bool>` and
/// `as core::`; its result was pinned to `{0, 1}`.
pub fn lie<T: core::ops::Not>(flag: bool) -> u8 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `bool_from_requires_std_impl::lie`: 1 obligation(s) were not proved
    //[default,certify]~^^ ERROR Trust strict verification failed for `bool_from_requires_std_impl::lie`: 1 obligation(s) were not fully verified
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `bool_from_requires_std_impl::lie`: 1 obligation(s) were not proved
    let x = conv::<From<bool>, <T as core::ops::Not>::Output>(flag);
    let arr = [1u8; 2];
    arr[x as usize]
}

// std's `From<bool>` keeps the `{0, 1}` fact.
pub fn std_from(flag: bool) -> u8 {
    let arr = [1u8; 2];
    arr[usize::from(flag)]
}

pub fn std_u32_from(flag: bool) -> u8 {
    let arr = [1u8; 2];
    arr[u32::from(flag) as usize]
}
