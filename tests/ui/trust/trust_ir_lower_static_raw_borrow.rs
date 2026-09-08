//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
// The `static_mut_refs` lint is incidental to this fixture's subject (the
// DIRECT lowering of static borrows); under ui-test defaults its warnings
// count as unexpected diagnostics, and the fixture landed without a sweep.
#![allow(static_mut_refs)]
//! Trust (wave-SR): `&raw mut STATIC` / `&mut STATIC` on a local `static mut`
//! is the static's own `GlobalAddr` (THIR spells the place as
//! `Deref { StaticRef }` over a `*mut T` constant); a deref of that pointer is
//! the global `Load`/`Store`. Every body here carried
//! `Borrow(&mut non-local place)` / `Borrow(non-local place)` before the wave;
//! `strict` turns that into a compile error, so this file is the mutation
//! check.
static mut COUNTER: u32 = 3;
fn addr() -> *mut u32 {
    &raw mut COUNTER
}
fn bump_via_ref() -> u32 {
    let r: &mut u32 = unsafe { &mut COUNTER };
    *r += 1;
    *r
}
fn read_via_ref() -> u32 {
    let r: &u32 = unsafe { &COUNTER };
    *r
}
fn main() {
    let p = addr();
    let a = bump_via_ref();
    let b = read_via_ref();
    std::process::exit(!(a == 4 && b == 4 && !p.is_null()) as i32);
}
