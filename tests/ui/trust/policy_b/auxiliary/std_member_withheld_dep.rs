//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! A dependency compiled with verification OFF, the way Targo compiles every
//! dependency unit: nothing here carries a Trust verdict. Each value panics in
//! THIS crate's code on one input, reached from a caller only through std: an
//! iterator's `next` behind `&mut dyn Iterator`, an `io::Error` payload's `Drop`,
//! and a `Waker` whose vtable `drop` panics (`std_member_runtime_check_withheld.rs`).
use std::fmt;
use std::task::{RawWaker, RawWakerVTable, Waker};

/// `next` panics when the countdown reaches 7.
pub struct It(pub u32);
impl Iterator for It {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        if self.0 == 7 {
            panic!("DEP NEXT PANIC (unverified crate)")
        }
        if self.0 == 0 {
            None
        } else {
            self.0 -= 1;
            Some(self.0)
        }
    }
}

/// An `io::Error` payload whose `Drop` panics on 7.
pub struct DropBomb(pub u32);
impl Drop for DropBomb {
    fn drop(&mut self) {
        if self.0 == 7 {
            panic!("DEP DROP PANIC (unverified crate)")
        }
    }
}
impl fmt::Debug for DropBomb {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("d")
    }
}
impl fmt::Display for DropBomb {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("d")
    }
}
impl std::error::Error for DropBomb {}
pub fn drop_err(n: u32) -> std::io::Error {
    std::io::Error::other(DropBomb(n))
}

fn w_clone(p: *const ()) -> RawWaker {
    RawWaker::new(p, &VTABLE)
}
fn w_wake(_: *const ()) {}
fn w_wake_by_ref(_: *const ()) {}
fn w_drop(p: *const ()) {
    if p as usize == 7 {
        panic!("DEP WAKER DROP PANIC (unverified crate)")
    }
}
static VTABLE: RawWakerVTable = RawWakerVTable::new(w_clone, w_wake, w_wake_by_ref, w_drop);
/// A `Waker` whose vtable `drop` panics on 7.
pub fn waker(n: usize) -> Waker {
    // SAFETY: the vtable functions ignore the data pointer except to compare it.
    unsafe { Waker::from_raw(RawWaker::new(n as *const (), &VTABLE)) }
}
