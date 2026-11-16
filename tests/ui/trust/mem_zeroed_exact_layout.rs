//@ needs-trust-verify
//@ only-macos
//@ edition: 2024
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//! G1 (2026-10-27): `mem::zeroed::<T>()` for a struct `T` is admitted exactly when
//! rustc's exact validity check accepts an all-zero `T` on its real layout
//! (`rustc_const_eval::util::check_validity_requirement_exact`, called by
//! `trust_verify::zero_valid_zeroed_call_blocks`). The structural verdict alone refuted
//! every struct, because the extracted type erases niches.
//!
//! `zeroed_sigaction` and `zeroed_plain` lose their FAILED `[unsafe:zeroed]` row. Each
//! keeps the one row outside this change: the runtime-checked absent-callee row of the
//! call to `core::mem::zeroed::<T>` itself, which the strict lane still counts. A struct
//! with a reference field, a `NonZero` field or a `fn` field, an enum whose tags exclude
//! zero, an array of references and a generic `T` keep the `[unsafe:zeroed]` row.
//! The per-function counts below pin both.
//!
//! G1 review finding 4 (2026-10-27): rustc's check accepts ANY bytes for a union, so it
//! called `union RefOrWord { r: &'static u8, x: usize }` zero-valid although a later
//! `.r` read is a null reference. A union, or a type holding one inline, is now left out
//! of the admission (`trust_verify::zeroed_type_is_union_free`) and keeps the
//! `[unsafe:zeroed]` row: `zeroed_union` and `zeroed_struct_holding_union` (whose union
//! is harmless — the fail-closed cost of not asking the union-read question here).

#![feature(rustc_private)]

extern crate libc;

use core::num::NonZeroU32;

#[repr(C)]
pub struct Plain {
    pub a: u32,
    pub b: *const u8,
    pub c: [u16; 3],
    pub d: Option<&'static u8>,
}

pub struct WithRef {
    pub a: u32,
    pub r: &'static u8,
}

pub struct WithNonZero {
    pub n: NonZeroU32,
}

pub struct WithFn {
    pub f: fn(),
}

pub union RefOrWord {
    pub r: &'static u8,
    pub x: usize,
}

pub union IntOrFloat {
    pub i: u32,
    pub f: f32,
}

#[repr(C)]
pub struct HoldsUnion {
    pub n: u32,
    pub u: IntOrFloat,
}

#[repr(u8)]
pub enum OneTwo {
    One = 1,
    Two = 2,
}

/// The agy `ignored` shape: proves.
pub fn zeroed_sigaction() -> libc::sigaction {
    //~^ NOTE Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 1 obligation(s)
    //~^^ WARN Trust Level 0 safety verification incomplete for `mem_zeroed_exact_layout::zeroed_sigaction`: 1 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `mem_zeroed_exact_layout::zeroed_sigaction`: 1 obligation(s) were not fully verified
    // SAFETY: an all-zero `sigaction` is a valid value.
    unsafe { core::mem::zeroed() }
}

/// Every field accepts zero: proves.
pub fn zeroed_plain() -> Plain {
    //~^ NOTE Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 1 obligation(s)
    //~^^ WARN Trust Level 0 safety verification incomplete for `mem_zeroed_exact_layout::zeroed_plain`: 1 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `mem_zeroed_exact_layout::zeroed_plain`: 1 obligation(s) were not fully verified
    // SAFETY: every field accepts all-zero bytes.
    unsafe { core::mem::zeroed() }
}

pub fn zeroed_with_ref() -> WithRef {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `mem_zeroed_exact_layout::zeroed_with_ref`: 2 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `mem_zeroed_exact_layout::zeroed_with_ref`: 2 obligation(s) were not fully verified
    // SAFETY: deliberately wrong (negative control).
    unsafe { core::mem::zeroed() }
}

pub fn zeroed_with_nonzero() -> WithNonZero {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `mem_zeroed_exact_layout::zeroed_with_nonzero`: 2 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `mem_zeroed_exact_layout::zeroed_with_nonzero`: 2 obligation(s) were not fully verified
    // SAFETY: deliberately wrong (negative control).
    unsafe { core::mem::zeroed() }
}

pub fn zeroed_with_fn() -> WithFn {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `mem_zeroed_exact_layout::zeroed_with_fn`: 2 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `mem_zeroed_exact_layout::zeroed_with_fn`: 2 obligation(s) were not fully verified
    // SAFETY: deliberately wrong (negative control).
    unsafe { core::mem::zeroed() }
}

pub fn zeroed_enum() -> OneTwo {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `mem_zeroed_exact_layout::zeroed_enum`: 2 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `mem_zeroed_exact_layout::zeroed_enum`: 2 obligation(s) were not fully verified
    // SAFETY: deliberately wrong (negative control).
    unsafe { core::mem::zeroed() }
}

pub fn zeroed_ref_array() -> [&'static u8; 2] {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `mem_zeroed_exact_layout::zeroed_ref_array`: 2 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `mem_zeroed_exact_layout::zeroed_ref_array`: 2 obligation(s) were not fully verified
    // SAFETY: deliberately wrong (negative control).
    unsafe { core::mem::zeroed() }
}

/// A generic `T` is never admitted by the compiler's check (it names only fully
/// monomorphic calls).
pub fn zeroed_generic<T>() -> T {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `mem_zeroed_exact_layout::zeroed_generic`: 2 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `mem_zeroed_exact_layout::zeroed_generic`: 2 obligation(s) were not fully verified
    // SAFETY: deliberately unknown (negative control).
    unsafe { core::mem::zeroed() }
}

/// A union: rustc's check accepts any bytes for it, so the admission leaves it out.
pub fn zeroed_union() -> RefOrWord {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `mem_zeroed_exact_layout::zeroed_union`: 2 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `mem_zeroed_exact_layout::zeroed_union`: 2 obligation(s) were not fully verified
    // SAFETY: deliberately a union with a reference field (negative control).
    unsafe { core::mem::zeroed() }
}

/// A struct holding a union inline: left out too (fail-closed).
pub fn zeroed_struct_holding_union() -> HoldsUnion {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)
    //~^^ ERROR Trust Level 0 safety verification incomplete for `mem_zeroed_exact_layout::zeroed_struct_holding_union`: 2 obligation(s) were not proved
    //~^^^ ERROR Trust strict verification failed for `mem_zeroed_exact_layout::zeroed_struct_holding_union`: 2 obligation(s) were not fully verified
    // SAFETY: deliberately a struct holding a union (negative control).
    unsafe { core::mem::zeroed() }
}
