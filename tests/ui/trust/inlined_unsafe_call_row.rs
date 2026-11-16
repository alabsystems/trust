//@ needs-trust-verify
//@ edition: 2021
//@ revisions: neo slice rawref asref
//@ revisions: asref_param char utf8 wop
//@ revisions: unchecked_add_guarded
//@ revisions: neo_o2plain slice_o2plain rawref_o2plain asref_o2plain asref_param_o2plain
//@ revisions: char_o2plain utf8_o2plain wop_o2plain rawref_tuple_o2plain unchecked_add_guarded_o2plain
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[neo_o2plain] compile-flags: -Copt-level=2
//@[slice_o2plain] compile-flags: -Copt-level=2
//@[rawref_o2plain] compile-flags: -Copt-level=2
//@[asref_o2plain] compile-flags: -Copt-level=2
//@[asref_param_o2plain] compile-flags: -Copt-level=2
//@[char_o2plain] compile-flags: -Copt-level=2
//@[utf8_o2plain] compile-flags: -Copt-level=2
//@[wop_o2plain] compile-flags: -Copt-level=2
//@[rawref_tuple_o2plain] compile-flags: -Copt-level=2
//@[unchecked_add_guarded_o2plain] compile-flags: -Copt-level=2
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
#![allow(dead_code)]
#![cfg_attr(any(neo, neo_o2plain), feature(transmute_neo))]
//! Trust (O2-inline, 2026-09-24): AN UNSAFE OPERATION'S ROW MUST SURVIVE THE
//! OPTIMIZER — `[unsafe:inlined-unsafe-call]` and
//! `[unsafe:folded-invalid-constant]`
//! (`compiler/rustc_mir_transform/src/trust_verify/inlined_unsafe_evidence.rs`).
//!
//! At `-O` the MIR inliner copies a sysroot `unsafe fn` into the caller, which
//! deletes the `Call` terminator its row (modeled or `[unsafe:unmodeled-call]`)
//! was keyed on, and GVN then folds what is left into a constant. Every `_opt`
//! revision below compiled with rc=0 and NO error on the stage-1 `trustc` of
//! 2026-09-24 (`a8c853de6f`, this file with `--cfg <rev>`); its `-O0` twin was
//! refused. The runtime witnesses are the same shapes built as binaries
//! (session probes `wave1/O2-inline/n_*.rs`):
//!
//! | revisions | shape | `-O2` before |
//! |---|---|---|
//! | `neo`, `neo_opt` | `transmute_neo::<usize, Box<u32>>(4)` fed to `f(Box<u32>)` | rc=0; binary SIGSEGV (139) |
//! | `slice`, `slice_opt` | `slice::from_raw_parts(NonNull::dangling().as_ptr(), 4)` | rc=0; binary SIGSEGV (139) |
//! | `rawref`, `rawref_opt` | `&*NonNull::dangling().as_ptr()` as `&'static u32` (GVN: `const {0x4 as &u32}`) | rc=0; binary SIGSEGV (139) |
//! | `asref`, `asref_opt` | `NonNull::dangling().as_ref()` | rc=0; binary SIGSEGV (139) |
//! | `asref_param`, `asref_param_opt` | `p.as_ref()` of a `NonNull` PARAMETER, returned `&'static` | rc=0 |
//! | `char`, `char_opt` | `char::from_u32_unchecked(x)`, called with `0xD800` | rc=0 (invalid `char`) |
//! | `utf8`, `utf8_opt` | `str::from_utf8_unchecked(b)` of an arbitrary `&[u8]` | rc=0 |
//! | `wop`, `wop_opt` | `&*ptr::without_provenance::<u32>(8)` (GVN: `const {0x8 as &u32}`) | rc=0 |
//! | `rawref_tuple_opt` | the `rawref` reborrow folded into a TUPLE constant | rc=0 |
//!
//! The `-O0` twins are the controls that the rows' premise holds: each was
//! refused before this change by the row the call or deref carries unoptimized,
//! and must stay refused.
//!
//! No block here carries a `// SAFETY:` comment, on purpose: since SAFETY-ASSUME-1
//! (2026-10-17) a clippy-placed one DECLARES its block, and the unmodeled rows under
//! test become one `assumption:safety-comment` row (`safety_comment_assumption.rs`).
//!
//! # `-O` parity (2026-09-25): `_opt` is now an EXPLICIT `-Zmir-opt-level=2`
//!
//! A verifying session no longer runs the MIR inliner or GVN at a plain `-O`: with
//! no explicit `-Zmir-opt-level` it runs the `-O0` MIR pipeline at every
//! `-Copt-level` (`rustc_session::trust_default_mir_opt_level_by_flags`). So every
//! `_opt` revision states `-Zmir-opt-level=2` itself — that is the only session
//! that still inlines and folds, and these rows are what cover it. Each
//! `_o2plain` twin is the same program at a plain `-Copt-level=2`: it pins the new
//! default, where the unsafe call is still a `Call` and is refused by the SAME row
//! as its `-O0` twin (measured on the stage-1 build of this change: all ten
//! refused, at the annotated line). `rawref_tuple_o2plain` has no `-O0` twin; it
//! is refused by the `rawref` deref's row, the tuple never being folded.
//!
//! # `unchecked_add_guarded`, `unchecked_add_guarded_opt` — a pinned parity change
//!
//! `a.unchecked_add(b)` under `a < 100 && b < 100` is refused at `-O0`
//! (`[unsafe:unmodeled-call]`: Trust has no model of `u8::unchecked_add`), and
//! compiled at `-O2` (rc=0) only because inlining replaced the unmodeled call
//! with its `AddUnchecked` statement, whose overflow row IS provable. The new
//! row charges every inlined unsafe callee, so `-O2` now refuses it exactly as
//! `-O0` does. The honest way to make both verify is a MODEL for the unchecked
//! arithmetic methods at the call site (the precondition is the intrinsic's own),
//! not an exemption from this row: an exemption keyed on "the inlined body
//! carries a provable row" would also pass an `unsafe fn` whose body does
//! unchecked arithmetic AND relies on a library invariant.

#[allow(unused_imports)]
use core::ptr::NonNull;

// -- neo ------------------------------------------------------------------
#[cfg(any(neo, neo_o2plain))]
#[inline(never)]
pub fn mk() -> Box<u32> {
    //[neo,neo_o2plain]~^ ERROR safety verification incomplete
    //[neo,neo_o2plain]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    // UNSOUND, deliberately: 4 is not an allocation; this is the defect under test.
    unsafe { core::mem::transmute_neo::<usize, Box<u32>>(4) }
}
#[cfg(any(neo, neo_o2plain))]
#[inline(never)]
pub fn f(b: Box<u32>) -> u32 {
    let v = *b;
    core::mem::forget(b);
    v
}
#[cfg(any(neo, neo_o2plain))]
pub fn g() -> u32 {
    f(mk())
}

// -- slice ----------------------------------------------------------------
#[cfg(any(slice, slice_o2plain))]
#[inline(never)]
pub fn mk() -> &'static [u32] {
    //[slice,slice_o2plain]~^ ERROR safety verification incomplete
    //[slice,slice_o2plain]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    // UNSOUND, deliberately: a dangling pointer is not valid for 4 reads.
    unsafe { core::slice::from_raw_parts(NonNull::<u32>::dangling().as_ptr(), 4) }
}
#[cfg(any(slice, slice_o2plain))]
#[inline(never)]
pub fn f(b: &[u32]) -> u32 {
    if b.len() > 0 { b[0] } else { 0 }
}
#[cfg(any(slice, slice_o2plain))]
pub fn g() -> u32 {
    f(mk())
}

// -- rawref ---------------------------------------------------------------
#[cfg(any(rawref, rawref_o2plain))]
#[inline(never)]
pub fn mk() -> &'static u32 {
    //[rawref,rawref_o2plain]~^ ERROR safety verification incomplete
    //[rawref,rawref_o2plain]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    // UNSOUND, deliberately: a dangling pointer is not dereferenceable.
    unsafe { &*(NonNull::<u32>::dangling().as_ptr()) }
}
#[cfg(any(rawref, rawref_o2plain))]
#[inline(never)]
pub fn h() -> u32 {
    *mk()
}

// -- asref ----------------------------------------------------------------
#[cfg(any(asref, asref_o2plain))]
#[inline(never)]
pub fn mk() -> &'static u32 {
    //[asref,asref_o2plain]~^ ERROR safety verification incomplete
    //[asref,asref_o2plain]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    // UNSOUND, deliberately: a dangling pointer is not dereferenceable.
    unsafe { NonNull::<u32>::dangling().as_ref() }
}
#[cfg(any(asref, asref_o2plain))]
#[inline(never)]
pub fn h() -> u32 {
    *mk()
}

// -- asref_param (no constant to fold: only the inlined scope survives) -----
#[cfg(any(asref_param, asref_param_o2plain))]
pub fn mk(p: NonNull<u32>) -> &'static u32 {
    //[asref_param,asref_param_o2plain]~^ ERROR safety verification incomplete
    //[asref_param,asref_param_o2plain]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    // UNSOUND, deliberately: the caller's pointer is not known to be live for 'static.
    unsafe { p.as_ref() }
}

// -- char -----------------------------------------------------------------
#[cfg(any(char, char_o2plain))]
pub fn mk(x: u32) -> char {
    //[char,char_o2plain]~^ ERROR safety verification incomplete
    //[char,char_o2plain]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    // UNSOUND, deliberately: `x` may be a surrogate or out of range.
    unsafe { char::from_u32_unchecked(x) }
}
#[cfg(any(char, char_o2plain))]
pub fn g() -> char {
    mk(0xD800)
}

// -- utf8 -----------------------------------------------------------------
#[cfg(any(utf8, utf8_o2plain))]
pub fn mk(b: &[u8]) -> &str {
    //[utf8,utf8_o2plain]~^ ERROR safety verification incomplete
    //[utf8,utf8_o2plain]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    // UNSOUND, deliberately: `b` is not known to be UTF-8.
    unsafe { core::str::from_utf8_unchecked(b) }
}

// -- wop ------------------------------------------------------------------
#[cfg(any(wop, wop_o2plain))]
pub fn mk() -> &'static u32 {
    //[wop,wop_o2plain]~^ ERROR safety verification incomplete
    //[wop,wop_o2plain]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    // UNSOUND, deliberately: address 8 is not an allocation.
    unsafe { &*core::ptr::without_provenance::<u32>(8) }
}
#[cfg(any(wop, wop_o2plain))]
pub fn h() -> u32 {
    *mk()
}

// -- rawref_tuple (the folded reference inside an aggregate constant) -------
#[cfg(rawref_tuple_o2plain)]
#[inline(never)]
pub fn mk() -> (&'static u32, u8) {
    //[rawref_tuple_o2plain]~^ ERROR safety verification incomplete
    //[rawref_tuple_o2plain]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    // UNSOUND, deliberately: a dangling pointer is not dereferenceable.
    unsafe { (&*(NonNull::<u32>::dangling().as_ptr()), 1) }
}

// -- unchecked_add_guarded (parity: refused at -O0, now also at -O2) --------
#[cfg(any(unchecked_add_guarded, unchecked_add_guarded_o2plain))]
pub fn add(a: u8, b: u8) -> u8 {
    //[unchecked_add_guarded,unchecked_add_guarded_o2plain]~^ ERROR safety verification incomplete
    //[unchecked_add_guarded,unchecked_add_guarded_o2plain]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    if a < 100 && b < 100 {
        // Claim, deliberately not a SAFETY comment: both operands are below 100.
        unsafe { a.unchecked_add(b) }
    } else {
        0
    }
}
