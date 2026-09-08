//@ check-fail
//@ compile-flags: -Ztrust-verify=off
//@ edition: 2021
// ignore-tidy-linelength
//
// Trust: the `core::cell` twin. A `OnceCell` can only be a `static mut` (it is
// `!Sync`), and its re-entry PANICS (`reentrant init`) rather than deadlocking —
// the message says so. A `set` inside the initializer is a re-entry too: the
// outer `try_init`'s own `try_insert` then fails and panics.

#![allow(dead_code, static_mut_refs)]

use std::cell::OnceCell;

static mut C: OnceCell<u32> = OnceCell::new();

fn value() -> u32 {
    unsafe { *C.get_or_init(|| value() + 1) }
    //~^ ERROR the initializer of `C` can wait on `C` itself: a `core::cell::OnceCell` initializer that re-enters its own cell panics (reentrant init)
}

static mut D: OnceCell<u32> = OnceCell::new();

fn seed() -> u32 {
    unsafe {
        *D.get_or_init(|| {
            let _ = D.set(7);
            //~^ ERROR the initializer of `D` can wait on `D` itself
            8
        })
    }
}

fn main() {
    let _ = value();
    let _ = seed();
}
