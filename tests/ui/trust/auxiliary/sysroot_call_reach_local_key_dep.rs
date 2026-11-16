//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ edition: 2021
//@ no-prefer-dynamic
//! An ordinary dependency, compiled the way `targo` compiles every dependency
//! unit: `-Ztrust-verify=off`, so nothing here is verified. Two lazily
//! initialized `thread_local!` keys whose initializer panics on first access:
//! the accessor `LocalKey::try_with` / `initialize_with` call through
//! `(self.inner)(..)` runs that initializer inside the std call.

use std::cell::{Cell, RefCell};

thread_local! {
    pub static BOMB: Cell<u32> = Cell::new(boom());
    pub static RBOMB: RefCell<u32> = RefCell::new(boom());
    // A key whose initializer cannot panic: its accessor is still this crate's
    // unverified code (the `dep_ok_*` revisions pin D8's capability cost).
    pub static OK: Cell<u32> = const { Cell::new(1) };
}

#[inline(never)]
pub fn boom() -> u32 {
    panic!("dependency thread_local initializer")
}
