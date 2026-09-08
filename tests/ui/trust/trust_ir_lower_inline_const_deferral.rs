//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-IC): a local INLINE const (`const { 7u32 }`) defers to the
//! finalizer and gets its real value patched in.
//!
//! THE INVERSION THIS FIXES: `InlineConstArgs::new` appends the const's own TYPE
//! as a non-region arg unconditionally, so the deferral gate's all-regions test
//! could never pass for an inline const — the deferral lane was DEAD CODE for
//! every inline const in the language, while the GENERIC-parent case sailed
//! through the symbolic lane. The non-generic, fully-evaluable case was the one
//! that refused.
//!
//! The finalizer REBUILDS what it cannot store: the type from the recorded flags
//! (`pointer_width` disambiguates `usize`/`u64` at 64 bits) and the args as
//! `InlineConstArgs::new(parent-identity, ty)` — sound because the hook admits
//! only a non-generic parent, re-checked at the finalizer, never assumed.
//!
//! NEGATIVE CONTROL: `char`'s flag encoding collides with `u32` (both
//! bits=32/unsigned), so the finalizer could not rebuild the type — a char
//! inline const keeps the deferred refusal rather than risking a mistyped
//! constant.

pub fn a() -> u32 {
    const { 7u32 }
}
pub fn b() -> bool {
    const { true }
}
pub fn c() -> f64 {
    const { 1.5f64 }
}
pub fn d() -> u32 {
    const { 3u32 + 4 }
}
pub fn e() -> usize {
    const { 9usize }
}
pub fn f() -> i64 {
    const { -5i64 }
}
// NEGATIVE CONTROL: stays refused (flag-encoding collision with u32).
pub fn neg_char() -> char {
    const { 'a' }
}
// Control: a generic parent takes the symbolic lane, unchanged.
pub fn g<T>() -> u32 {
    const { 7u32 }
}
pub fn main() {}
