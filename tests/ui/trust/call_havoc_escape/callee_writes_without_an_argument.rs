//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! CALL-HAVOC-ESCAPE-1 (docs/KNOWN_HAZARDS.md; TINV-18 correction, 2026-10-06): a call
//! whose arguments hand the callee no pointer still writes caller memory the callee
//! reaches WITHOUT an argument. Every `+ 200` below really overflows (the callee stores
//! 255 first), and each function is defined behaviour under Stacked and Tree Borrows,
//! so each overflow row must be REFUTED, never proved.
//!
//! * `stash_then_slice_call` / `stash_then_nullary_call`: an earlier call received
//!   `&mut x` and parked a raw child of it in a static; the later call writes through
//!   it. Before the fix both rows were PROVED (kernel-certified) on stage 1 of
//!   `81f257193d`; the nullary one goes back to before TINV-18.
//! * `raw_then_slice_call` / `raw_then_nullary_call`: the caller reads through a raw
//!   pointer a callee returned (`&raw mut G` is in the callee); the later call writes
//!   `G`. The vcgen kill list kept `p*` across the call; end to end the row was
//!   already refuted on `81f257193d` (the read is re-versioned elsewhere), so these
//!   pin the row, not a former false proof.
//! * `atomic_store`: `A.store(255, ..)` hands only constants (`&AtomicU8`, `Ordering`).

use std::sync::atomic::{AtomicU8, Ordering};

static mut P: *mut u8 = core::ptr::null_mut();

fn stash(r: &mut u8) {
    unsafe {
        P = r as *mut u8;
    }
}

#[inline(never)]
fn poke_through_stash(b: &[u8]) -> usize {
    unsafe {
        *P = 255;
    }
    b.len()
}

#[inline(never)]
fn poke_through_stash_nullary() {
    unsafe {
        *P = 255;
    }
}

pub fn stash_then_slice_call(buf: &[u8]) -> u8 {
    //~^ NOTE [overflow:add] FAILED (ay-in-process); counterexample:
    let mut x: u8 = 0;
    stash(&mut x);
    if x < 50 {
        let _n = poke_through_stash(buf);
        return x + 200;
    }
    0
}

pub fn stash_then_nullary_call() -> u8 {
    //~^ NOTE [overflow:add] FAILED (ay-in-process); counterexample:
    let mut x: u8 = 0;
    stash(&mut x);
    if x < 50 {
        poke_through_stash_nullary();
        return x + 200;
    }
    0
}

static mut G: u8 = 0;

fn gptr() -> *mut u8 {
    &raw mut G
}

#[inline(never)]
fn poke_static(b: &[u8]) -> usize {
    unsafe {
        G = 255;
    }
    b.len()
}

#[inline(never)]
fn poke_static_nullary() {
    unsafe {
        G = 255;
    }
}

pub fn raw_then_slice_call(buf: &[u8]) -> u8 {
    //~^ NOTE [overflow:add] FAILED (ay-in-process); counterexample:
    let p = gptr();
    unsafe {
        if *p < 50 {
            let _n = poke_static(buf);
            return *p + 200;
        }
    }
    0
}

pub fn raw_then_nullary_call() -> u8 {
    //~^ NOTE [overflow:add] FAILED (ay-in-process); counterexample:
    let p = gptr();
    unsafe {
        if *p < 50 {
            poke_static_nullary();
            return *p + 200;
        }
    }
    0
}

static A: AtomicU8 = AtomicU8::new(0);

pub fn atomic_store() -> u8 {
    //~^ NOTE [overflow:add] FAILED (ay-in-process); counterexample:
    let p = A.as_ptr();
    unsafe {
        if *p < 50 {
            A.store(255, Ordering::Relaxed);
            return *p + 200;
        }
    }
    0
}
