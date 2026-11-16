//@ needs-trust-verify
//@ edition: 2021
//@ revisions: safe_std_o2plain slice_get_o2plain valid_consts_o2plain
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Copt-level=2
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
#![allow(dead_code)]
//! Trust (O2-inline, 2026-09-24): what `[unsafe:inlined-unsafe-call]` and
//! `[unsafe:folded-invalid-constant]`
//! (`compiler/rustc_mir_transform/src/trust_verify/inlined_unsafe_evidence.rs`)
//! must NOT charge. Every revision compiled rc=0 at `-O2` on the stage-1
//! `trustc` of 2026-09-24 (`a8c853de6f`) and must keep compiling. The refusals
//! are `inlined_unsafe_call_row.rs`.
//!
//! * `safe_std_opt`, `slice_get_opt` — safe std API inlined into user code.
//!   Whatever `unsafe fn` std calls INSIDE it is called by a sysroot def (the
//!   inlined safe function), not by the user: the row keys on the CALLER of the
//!   inlined callee, never on the callee alone.
//! * `zst_ref_opt` — `&*NonNull::<()>::dangling().as_ptr()` folds to
//!   `const {0x1 as &()}`, a VALID reference (zero-sized, aligned, non-null):
//!   the folded-constant row charges an invalid value, never a folded one.
//! * `valid_consts_opt` — references into a static, a string literal, `Some` of
//!   a static reference and a byte-string tuple are `mir::Const::Val` values the
//!   validator must accept.
//!
//! -O parity (2026-09-25): a verifying session runs the MIR inliner and GVN only
//! under an EXPLICIT `-Zmir-opt-level=2` now (the default is the `-O0` pipeline at
//! every `-Copt-level`), so the `_opt` revisions state it; they are the controls
//! for the sessions that still inline. The `_o2plain` twins pin the plain
//! `-Copt-level=2` default, where nothing is inlined and the safe std calls stay
//! calls. `zst_ref` has NO plain twin, on purpose: without GVN the user's raw
//! `&*NonNull::<()>::dangling().as_ptr()` stays a raw-pointer deref, and that is
//! refused at plain `-O2` exactly as at `-O0` (measured on the stage-1 build of
//! this change, and on the build before it at `-O0`). It passed at `-O2` only
//! because GVN folded it into a constant the folded-constant validator accepts.

// -- safe_std_opt ---------------------------------------------------------
#[cfg(safe_std_o2plain)]
pub fn swap(a: &mut u32, b: &mut u32) {
    core::mem::swap(a, b)
}
#[cfg(safe_std_o2plain)]
pub fn copied(x: Option<&u32>) -> Option<u32> {
    x.copied()
}
#[cfg(safe_std_o2plain)]
pub fn len(x: &str) -> usize {
    x.len()
}
#[cfg(safe_std_o2plain)]
pub fn first_mut(x: &mut [u32]) -> Option<&mut u32> {
    x.first_mut()
}
#[cfg(safe_std_o2plain)]
pub fn utf8_len(x: char) -> u32 {
    x.len_utf8() as u32
}

// -- slice_get_opt --------------------------------------------------------
#[cfg(slice_get_o2plain)]
pub fn get(v: &[u32], i: usize) -> u32 {
    match v.get(i) {
        Some(x) => *x,
        None => 0,
    }
}

// -- valid_consts_opt -----------------------------------------------------
#[cfg(valid_consts_o2plain)]
static X: u32 = 3;
#[cfg(valid_consts_o2plain)]
pub fn a() -> &'static u32 {
    &X
}
#[cfg(valid_consts_o2plain)]
pub fn b() -> &'static str {
    "hello"
}
#[cfg(valid_consts_o2plain)]
pub fn c() -> Option<&'static u32> {
    Some(&X)
}
#[cfg(valid_consts_o2plain)]
pub fn d() -> (&'static [u8], u8) {
    (b"ab", 1)
}
