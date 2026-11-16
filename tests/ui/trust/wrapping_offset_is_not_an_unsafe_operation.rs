//@ revisions: past_end deref
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[past_end] check-pass
//@[deref] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! `<*const T>::wrapping_add` / `wrapping_offset` are SAFE methods: computing a
//! pointer outside its allocation with them is defined behaviour. The
//! separation engine tracks them like `add` (provenance and byte offset
//! propagate) but must not charge the in-bounds obligation `add` carries.
//!
//! Measured 2026-09-24 on stage 1 `4e9fe36bf`, BEFORE: `past_end` was refused —
//! `[hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)` from
//! an `[unsafe:sep:offset]` row on a pointer nobody dereferences. `deref`, which
//! reads through the unchecked wrapping pointer, must stay refused.

#[cfg(past_end)]
pub fn past_end(s: &[u8]) -> *const u8 {
    s.as_ptr().wrapping_add(s.len().wrapping_add(10))
}

#[cfg(deref)]
pub fn deref(s: &[u8], i: usize) -> u8 { //[deref]~ ERROR safety verification incomplete
    //[deref]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    unsafe { *s.as_ptr().wrapping_add(i) }
}
