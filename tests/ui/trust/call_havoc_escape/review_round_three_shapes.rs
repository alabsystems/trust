//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! CALL-HAVOC-ESCAPE-1, the third review round (docs/KNOWN_HAZARDS.md; TINV-18
//! correction, 2026-10-06): three channels the fine-grained exposure analysis missed,
//! each closed by the coarse rule (`path_defs::escape_havoc`: only a protected,
//! pointer-free, `Unpin` `&mut` parameter that never leaves the body is exempt). Every
//! `+ 200` below really overflows when the caller shown in the comment runs it (the
//! nullary callee stores 255 first), and each is defined behaviour under Stacked and
//! Tree Borrows, so each overflow row must be REFUTED, never proved.
//!
//! * `stored_through_a_mut`: `&mut x` is stored THROUGH a `&mut` to another local,
//!   then that local's pointee is stashed; `poke` writes `x` through the stash.
//! * `not_unpin_param`: a `&mut S` with `S: !Unpin` (PhantomPinned) has no protector
//!   and no uniqueness; the caller's raw pointer writes `s.v` during `poke`.
//! * `recursive_mut_field`: `n: &mut L` where `L` holds `Option<&mut L>` (a by-name
//!   `Datatype` marker after extraction); the creator stashed a raw child of the inner
//!   `&mut` before moving it into `next`.

use core::marker::PhantomPinned;

static mut STASH: *mut u8 = core::ptr::null_mut();

fn stash(r: &mut u8) {
    unsafe { STASH = r }
}

#[inline(never)]
fn poke() {
    unsafe {
        if !STASH.is_null() {
            *STASH = 255
        }
    }
}

// `stored_through_a_mut(true)` overflows: 255 + 200.
pub fn stored_through_a_mut(c: bool) -> u8 {
    //~^ NOTE [overflow:add] FAILED (ay-in-process); counterexample:
    let (mut x, mut y, mut z) = (0u8, 0u8, 0u8);
    let mut r: &mut u8 = &mut y;
    let mut r2: &mut u8 = &mut z;
    {
        let pp = if c { &mut r } else { &mut r2 };
        *pp = &mut x;
    }
    stash(&mut *r);
    if x < 50 {
        poke();
        x + 200
    } else {
        0
    }
}

pub struct S {
    v: u8,
    _pin: PhantomPinned,
}

static mut PS: *mut S = core::ptr::null_mut();

#[inline(never)]
fn poke_pinned() {
    unsafe {
        (*PS).v = 255;
    }
}

// Caller: `let mut s = S { v: 0, _pin: PhantomPinned }; unsafe { PS = &raw mut s;
// not_unpin_param(&mut *PS); }`.
pub fn not_unpin_param(s: &mut S) -> u8 {
    //~^ NOTE [overflow:add] FAILED (ay-in-process); counterexample:
    if s.v < 50 {
        poke_pinned();
        return s.v + 200;
    }
    0
}

pub fn drive_not_unpin_param() -> u8 {
    let mut s = S { v: 0, _pin: PhantomPinned };
    unsafe {
        PS = &raw mut s;
        not_unpin_param(&mut *PS)
    }
}

pub struct L<'a> {
    v: u8,
    next: Option<&'a mut L<'a>>,
}

static mut PL: *mut L<'static> = core::ptr::null_mut();

#[inline(never)]
fn poke_list() {
    unsafe {
        (*PL).v = 255;
    }
}

// Caller: `let mut b = L { v: 0, next: None }; let rb = &mut b; PL = rb as *mut _
// (cast to 'static); let mut a = L { v: 0, next: Some(rb) }; recursive_mut_field(&mut a)`.
pub fn recursive_mut_field(n: &mut L<'_>) -> u8 {
    //~^ NOTE [overflow:add] FAILED (ay-in-process); counterexample:
    if let Some(inner) = &n.next {
        if inner.v < 50 {
            poke_list();
            return inner.v + 200;
        }
    }
    0
}
