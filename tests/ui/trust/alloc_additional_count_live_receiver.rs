//@ needs-trust-verify
//@ edition: 2021
//@ only-64bit
//@ revisions: reserve reserve_exact extend_reserve extend collect_into fresh ordinary_reserve
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[reserve] check-fail
//@[reserve_exact] check-fail
//@[extend_reserve] check-fail
//@[extend] check-fail
//@[collect_into] check-fail
//@[fresh] check-pass
//@[ordinary_reserve] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! Trust (ALLOC-RECEIVER-1, 2026-10-08): an allocation count that is ADDED to a
//! live receiver is charged with what the receiver already holds.
//!
//! `reserve(additional)`, `reserve_exact`, `Extend::extend_reserve`, a counted
//! `extend` and a counted `collect_into` ask RawVec for `(len + additional) *
//! size_of::<T>()` bytes, not `additional * size_of::<T>()`. Their
//! `[unbounded_allocation]` rows charged `stride * additional` alone, and until
//! 2026-10-08 the 256 MiB byte budget (`stride * count >= 2^28`) was the only atom
//! that refused the difference. The first draft of its deletion (ALLOC-BYTE-1,
//! `a6bd18e667d`) therefore PROVED every check-fail revision below, and each of them
//! panics at run time.
//!
//! # The witness (verify off, any 64-bit host)
//!
//! One existing `MaybeUninit<[u8; 1 << 35]>` element — a 32 GiB VIRTUAL allocation
//! that is never touched (`Vec::with_capacity(1)` then `set_len(1)`) — and then
//! `grow(&mut v, 2^28 - 1)`: `(1 + 2^28 - 1) * 2^35 = 2^63 > isize::MAX`, so RawVec
//! panics "capacity overflow" (`library/alloc/src/raw_vec/mod.rs`), rc=101. MEASURED
//! by the ALLOC-BYTE-1 review for `reserve`, `reserve_exact` and `extend` (re-run
//! 2026-10-08), and on 2026-10-08 for `extend_reserve` and `collect_into` (each a
//! verify-off build by stage 1 of this change, rc=101).
//!
//! # The rails
//!
//! * The five check-fail revisions: one live element bounds nothing, but a live
//!   receiver's length IS bounded on a 64-bit target — the
//!   `MAX_LIVE_USER_ADDRESS_SPACE_BYTES` modeled-fact axiom (`docs/TCB.md`), the
//!   premise the bounded-source skip already rests on, and no new one — so the row
//!   asks `stride * (count + held) >= isize::MAX` with `held = 2^56 / stride + 1`
//!   (`2^21 + 1` here), and `n < 2^28` does not discharge it. The pinned witness
//!   `n = 266338303` is `2^28 - 2^21 - 1`, the first count that line admits: with
//!   the receiver uncharged (the first draft) the row was PROVED, and with the byte
//!   budget (before it) the witness was `n = 1`.
//! * `fresh` — CONTROL: `Vec::with_capacity(n)` under the same guard is a FRESH
//!   request, `(2^28 - 1) * 2^35 < isize::MAX`, genuinely safe, and stays proved.
//! * `ordinary_reserve` — CONTROL: `Vec::<u64>::reserve(n)` under `n < 2^20` on a
//!   64-bit target fits whatever a live `Vec<u64>` can hold, and stays proved.
//!
//! A 32-bit target judges every receiver row as possibly full (no axiom bounds a
//! live length below its object limit there); no ui lane runs a non-host pointer
//! width, so that half is pinned by `crates/trust-vcgen/src/generate/
//! alloc_width_receiver_tests.rs`.

#![cfg_attr(extend_reserve, feature(extend_one))]
#![cfg_attr(collect_into, feature(iter_collect_into))]

use std::mem::MaybeUninit;

#[cfg(reserve)]
pub fn grow(v: &mut Vec<MaybeUninit<[u8; 1 << 35]>>, n: usize) {
    //[reserve]~^ NOTE [unbounded_allocation] FAILED (ay-in-process); counterexample: _3 = true, _4 = 268435456, _5 = 28, _6 = true, n = 266338303
    if n < (1usize << 28) {
        v.reserve(n);
    }
}

#[cfg(reserve_exact)]
pub fn grow_exact(v: &mut Vec<MaybeUninit<[u8; 1 << 35]>>, n: usize) {
    //[reserve_exact]~^ NOTE [unbounded_allocation] FAILED (ay-in-process); counterexample: _3 = true, _4 = 268435456, _5 = 28, _6 = true, n = 266338303
    if n < (1usize << 28) {
        v.reserve_exact(n);
    }
}

#[cfg(extend_reserve)]
pub fn grow_through_extend(v: &mut Vec<MaybeUninit<[u8; 1 << 35]>>, n: usize) {
    //[extend_reserve]~^ NOTE [unbounded_allocation] FAILED (ay-in-process); counterexample: _3 = true, _4 = 268435456, _5 = 28, _6 = true, n = 266338303
    if n < (1usize << 28) {
        <Vec<MaybeUninit<[u8; 1 << 35]>> as Extend<MaybeUninit<[u8; 1 << 35]>>>::extend_reserve(
            v, n,
        );
    }
}

#[cfg(extend)]
pub fn ext(v: &mut Vec<MaybeUninit<[u8; 1 << 35]>>, n: usize) {
    //[extend]~^ NOTE [unbounded_allocation] FAILED (ay-in-process); counterexample: _3 = true, _4 = 268435456, _5 = 28, _6 = true, n = 266338303
    if n < (1usize << 28) {
        v.extend(std::iter::repeat_with(MaybeUninit::uninit).take(n));
    }
}

#[cfg(collect_into)]
pub fn into(v: &mut Vec<MaybeUninit<[u8; 1 << 35]>>, n: usize) {
    //[collect_into]~^ NOTE [unbounded_allocation] FAILED (ay-in-process); counterexample: _3 = true, _4 = 268435456, _5 = 28, _6 = true, n = 266338303
    if n < (1usize << 28) {
        std::iter::repeat_with(MaybeUninit::uninit).take(n).collect_into(v);
    }
}

#[cfg(fresh)]
pub fn fresh(n: usize) -> Vec<MaybeUninit<[u8; 1 << 35]>> {
    if n < (1usize << 28) { Vec::with_capacity(n) } else { Vec::new() }
}

#[cfg(ordinary_reserve)]
pub fn room(v: &mut Vec<u64>, n: usize) {
    if n < (1usize << 20) {
        v.reserve(n);
    }
}
