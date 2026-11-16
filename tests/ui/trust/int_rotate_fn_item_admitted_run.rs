//@ revisions: total slice
//@[total] run-pass
//@[slice] run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off
//@[slice] error-pattern: assertion failed: mid <= self.len()
//@ ignore-emscripten no processes
//! The run twin of `int_rotate_fn_item_admitted.rs` (ROTATE-ITEM-NAME-1), built with
//! verification OFF.
//!
//! * `total`: core's integer `rotate_left` / `rotate_right` handed over as items, over
//!   rotation counts up to `u32::MAX`, never panic. `fold(1u32, u32::rotate_left)` over
//!   `[0, 31, 32, 1000, u32::MAX]` is 64.
//! * `slice`: the slice's `rotate_left` handed over the same way panics when `mid >
//!   len` — why the fn-item deny-list keeps it.
//!
//! Measured 2026-10-09 on the stage 1 of `46e9afaf95` (`scratchpad/stage1-w21before`):
//! `total` builds and exits 0; `slice` builds and its binary panics "assertion failed:
//! mid <= self.len()" (exit 101).

#![feature(fn_traits)]

use std::hint::black_box;

#[cfg(total)]
fn main() {
    let v = black_box([0u32, 31, 32, 1000, u32::MAX]);
    assert_eq!(v.iter().copied().fold(1u32, u32::rotate_left), 64);
    assert_eq!(
        v.iter().copied().fold(1u32, u32::rotate_right),
        v.iter().copied().fold(1u32, |a, b| a.rotate_right(b))
    );
    assert_eq!(
        v.iter().copied().fold(3i64, i64::rotate_right),
        v.iter().copied().fold(3i64, |a, b| a.rotate_right(b))
    );
    assert_eq!(
        v.iter().copied().fold(3u8, u8::rotate_left),
        v.iter().copied().fold(3u8, |a, b| a.rotate_left(b))
    );
    assert_eq!(
        core::ops::FnOnce::call_once(u32::rotate_left, (black_box(1u32), black_box(u32::MAX))),
        1u32 << 31
    );
}

#[cfg(slice)]
fn main() {
    let mut a = [1u8, 2];
    core::ops::FnOnce::call_once(<[u8]>::rotate_left, (&mut a[..], black_box(5usize)));
}
