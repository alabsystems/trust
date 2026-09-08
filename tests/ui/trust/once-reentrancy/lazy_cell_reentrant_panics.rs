//@ check-fail
//@ compile-flags: -Ztrust-verify=off
//@ edition: 2021
// ignore-tidy-linelength
//
// Trust: `LazyCell` marks itself poisoned while its initializer runs, so a
// re-entrant `*L` panics. Like `OnceCell`, it is `!Sync` and so only ever a
// `static mut`.

#![allow(dead_code, static_mut_refs)]

use std::cell::LazyCell;

static mut L: LazyCell<u32> = LazyCell::new(|| unsafe { *L + 1 });
//~^ ERROR the initializer of `L` can wait on `L` itself: a `core::cell::LazyCell` initializer that re-enters its own cell panics (reentrant init)

fn main() {
    let _ = unsafe { *L };
}
