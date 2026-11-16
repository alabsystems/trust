//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: panicking_allocator_dep.rs
//@ revisions: box_custom vecdeque_custom box_global vecdeque_global
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[box_custom] check-fail
//@[vecdeque_custom] check-fail
//@[box_global] check-pass
//@[vecdeque_global] check-pass
//! **A std container's drop is total only over the `Global` allocator (Trust,
//! 2026-09-27).**
//!
//! `tcx_drop_is_total` credits an audited std container (`Box`, `Vec`, `VecDeque`, …)
//! when every TYPE ARGUMENT's drop is total. For the allocator argument that is the
//! wrong property. The container's drop frees through `A::deallocate`, which is user
//! code for a caller-supplied `A`, while `A`'s own drop glue is usually empty.
//! Measured on stage 1: dropping a `Box<u8, PanicOnFree>` or a
//! `VecDeque<u8, PanicOnFree>` built `certify` rc=0 with its row PROVED, and the
//! certified artifact panicked in `PanicOnFree::deallocate` (exit 101). The clone
//! authority had the same unguarded recursion, where an allocating container's clone
//! calls `A::allocate`. Its measured shapes (`Box`/`Vec` clone over a panicking
//! `allocate`) were already refused by other rows, so that side is closed by the same
//! argument, not by a witness. Both now require every allocator argument to be `Global`
//! (`std_container_allocators_are_global` in `crates/trust-mir-extract/src/convert.rs`).
//!
//! * `box_custom`, `vecdeque_custom`: the DISCRIMINATING negatives. Each was rc=0
//!   before the fix. The annotation is the one that discriminates: if the credit
//!   applied, `consume` would verify and the annotation would go unmatched.
//! * `box_global`, `vecdeque_global`: POSITIVE, the credit this must not take away.
#![feature(allocator_api)]

extern crate panicking_allocator_dep;

#[cfg(any(box_custom, vecdeque_custom))]
use panicking_allocator_dep::PanicOnFree;
#[cfg(any(vecdeque_custom, vecdeque_global))]
use std::collections::VecDeque;

#[cfg(box_custom)]
pub fn consume(b: Box<u8, PanicOnFree>) {
    //[box_custom]~^ ERROR Trust Level 0 safety verification incomplete for `std_container_allocator_must_be_global::consume`
    drop(b);
}

#[cfg(vecdeque_custom)]
pub fn consume(v: VecDeque<u8, PanicOnFree>) {
    //[vecdeque_custom]~^ ERROR Trust Level 0 safety verification incomplete for `std_container_allocator_must_be_global::consume`
    drop(v);
}

#[cfg(box_global)]
pub fn consume(b: Box<u8>) {
    drop(b);
}

#[cfg(vecdeque_global)]
pub fn consume(v: VecDeque<u8>) {
    drop(v);
}
