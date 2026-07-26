// Pointer demo for coverage-agenda target #2 (raw pointers + smart-pointer family).
//   b   : a transparent Box<u32> wrapper that never dereferences -> grounds.
//   np  : a transparent NonNull<u32> -> bare *const u32 (no deref) -> grounds.
//   bare: a bare *const u32 returned unchanged (no deref) -> grounds.
//   deref: reads *p through the pointer -> MUST stay fail-closed (no pointee value model).
use std::ptr::NonNull;

#[inline(never)]
pub fn b(x: Box<u32>) -> u32 {
    // The Box wrapper is transparent; this returns the wrapped value via deref.
    // (Reading through the box IS a deref — stays honest about the loaded value.)
    *x
}

#[inline(never)]
pub fn np(p: NonNull<u32>) -> *const u32 {
    // No dereference: just reinterpret the non-null pointer as a *const u32.
    p.as_ptr() as *const u32
}

#[inline(never)]
pub fn bare(p: *const u32) -> *const u32 {
    // Identity on a bare raw pointer: no dereference at all.
    p
}

#[inline(never)]
pub fn deref(p: *const u32) -> u32 {
    // Reads the pointee value through the pointer: NO value semantics for *p,
    // so any contract over the loaded value must stay UNDISCHARGED.
    unsafe { *p }
}
