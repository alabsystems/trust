//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to subtract with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! A `&mut v` handed to a USER `IndexMut` impl on std's `Vec` may resize `v`
//! (STD-RECEIVER-ANCHOR-1), so the two `v.len()` around `v[K(())] = 1` are not
//! one length.
//!
//! `guards::local_mut_borrows_may_resize` counts a `&mut` reborrow consumed as the
//! receiver of a length-preserving call as harmless, which keeps the `.len()` tie
//! alive across the `v[i] = x` write idiom. It recognized `Index::index` /
//! `IndexMut::index_mut` by the TRAIT path (`callee_is_std_ops_method`). A generic
//! local impl is not renamed to its impl path by the producer (the rename would be
//! many-to-one across instantiations), so the call below renders
//! `<alloc::vec::Vec<u32> as core::ops::index::IndexMut<…::K<()>>>::index_mut` —
//! std's trait on std's `Vec`, but the body is this file's, and it truncates `v`.
//! A dependency's non-generic impl renders the same way.
//!
//! BEFORE (`scratchpad/stage1-w11fix`, the stage 1 of `38e6c69b1c`, whose
//! compiler and trust-vcgen this branch's base `43dc4c407d` does not change;
//! 2026-10-04): `user_len`'s `overflow:sub` row read
//! proved (Certified, `clean-kernel`) and `TRUST_ELIDE_DEBUG=1` printed `elided 1
//! kernel-certified overflow checks` in `user_len` under the default, strict,
//! certify, memory-safe and advisory policies. Only advisory builds the crate (the
//! others refuse the call's absent-callee row), and this source built with exactly
//! these flags exits 0 and the binary prints `18446744073709551615` and exits 0.
//! Built `-Ztrust-verify=off`, it panics `attempt to subtract with overflow`.
//!
//! AFTER (predicted, then measured): the receiver gate is
//! `unwrap_panic::is_std_container_index_call` — std's `Index`/`IndexMut` trait,
//! std's self type AND std's index argument (`usize` or a `core::ops::range`
//! type) — so `&mut v` here may resize, no tie is minted, the row is not proved,
//! the check stays, and the run panics. The crate-level `vcgen` pin is
//! `crates/trust-vcgen/src/generate/std_receiver_anchor_tests.rs` and
//! `crates/trust-vcgen/tests/std_receiver_anchor_realmir.rs` (the same function
//! from real extracted MIR). Measured on the stage 1 of `ee3f51541d` (2026-10-04):
//! nothing is elided in `user_len`, and the run panics `attempt to subtract with
//! overflow` (exit 101).

use std::ops::{Index, IndexMut};

pub struct K<T>(pub T);

impl<T> Index<K<T>> for Vec<u32> {
    type Output = u32;
    fn index(&self, _k: K<T>) -> &u32 {
        &0
    }
}

impl<T> IndexMut<K<T>> for Vec<u32> {
    // Empties the `Vec` it is handed, then returns a fresh cell.
    fn index_mut(&mut self, _k: K<T>) -> &mut u32 {
        self.truncate(0);
        Box::leak(Box::new(0u32))
    }
}

#[inline(never)]
fn user_len(mut v: Vec<u32>) -> usize {
    if v.len() == 0 {
        return 0;
    }
    v[K(())] = 1;
    v.len() - 1
}

fn main() {
    println!("{}", user_len(std::hint::black_box(vec![7])));
}
