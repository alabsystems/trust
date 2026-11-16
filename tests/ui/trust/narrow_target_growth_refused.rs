//@ needs-trust-verify
//@ only-32bit
//@ edition: 2021
//@ revisions: vec_push vec_insert deque_push heap_push string_push collect_widen set_extend
//@ revisions: map_extend box_collect to_uppercase wc_const_u128 wc_guarded_u128 rc_collect
//@ revisions: scalar_std no_std_core certify advisory
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[vec_push] check-fail
//@[vec_insert] check-fail
//@[deque_push] check-fail
//@[heap_push] check-fail
//@[string_push] check-fail
//@[collect_widen] check-fail
//@[set_extend] check-fail
//@[map_extend] check-fail
//@[box_collect] check-fail
//@[to_uppercase] check-fail
//@[wc_const_u128] check-fail
//@[wc_guarded_u128] check-fail
//@[rc_collect] check-fail
//@[scalar_std] check-fail
//@[no_std_core] check-fail
//@[certify] check-fail
//@[advisory] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
#![cfg_attr(no_std_core, no_std)]
#![allow(dead_code, unused_imports)]
//! Trust (2026-10-02): a verifying build for a target whose pointers are narrower
//! than 64 bits is refused under every fail-closed policy
//! (`compiler/rustc_mir_transform/src/trust_verify/narrow_target.rs`;
//! docs/KNOWN_HAZARDS.md, "CLOSED 2026-10-02 — on a target narrower than 64 bits,
//! the default policy's 64-bit allocation premises accepted programs that panic").
//!
//! The push-growth class, the vanilla std-callee class and vcgen's allocation
//! ceilings excuse std growth and layout panics on a 64-bit argument: a live
//! buffer would need more than 2^62 bytes. On a 32-bit target `isize::MAX` is
//! 2^31 - 1. Every revision from `vec_push` to `rc_collect` is a shape measured to
//! panic on `wasm32-unknown-unknown` (std run verify-off under node, 2026-10-02)
//! with a live input a 32-bit process holds — a full 1 GiB collection for the
//! pushes, a 256 MiB `&[u8]` for the widening collects, 512 MiB for the hash-table
//! extends and `to_uppercase`, no allocation at all for the two `with_capacity`
//! revisions of `u128`.
//!
//! What the rule costs, pinned: `scalar_std` (a function that touches no
//! collection) and `no_std_core` (a `#![no_std]` crate without `alloc`) are refused
//! too — the refusal is per target, because the 64-bit premises were audited for
//! the allocation lanes, not for every lane. `certify` refuses as the default does;
//! `advisory` reports it as a warning and builds.
//!
//! This fixture runs only when the ui suite targets a 32-bit triple
//! (`./x.py test tests/ui/trust/narrow_target_growth_refused.rs --target
//! wasm32-unknown-unknown`); on a 64-bit target the rule is constant-false and
//! `vec_zst_growth_refused.rs`'s `push_sized`/`insert_sized` stay check-pass.
//! The host suite pins the rule itself without a 32-bit std:
//! `narrow_target_refused_minicore.rs` cross-checks a `#![no_core]` crate for
//! `i686` and `wasm32` (refused) and for two 64-bit controls (accepted).

#[cfg(not(no_std_core))]
use std::collections::{BinaryHeap, HashMap, HashSet, VecDeque};

#[cfg(any(vec_push, certify, advisory))]
pub fn f(v: &mut Vec<u8>) {
    v.push(1);
}

#[cfg(vec_insert)]
pub fn f(v: &mut Vec<u32>, i: usize, x: u32) {
    if i <= v.len() {
        v.insert(i, x);
    }
}

#[cfg(deque_push)]
pub fn f(d: &mut VecDeque<u8>) {
    d.push_back(1);
}

#[cfg(heap_push)]
pub fn f(h: &mut BinaryHeap<u8>) {
    h.push(1);
}

#[cfg(string_push)]
pub fn f(s: &mut String, t: &str) {
    s.push_str(t);
}

#[cfg(collect_widen)]
pub fn f(s: &[u8]) -> Vec<u64> {
    s.iter().map(|&b| b as u64).collect()
}

#[cfg(set_extend)]
pub fn f(h: &mut HashSet<u8>, s: &[u8]) {
    h.extend(s.iter().copied());
}

#[cfg(map_extend)]
pub fn f(m: &mut HashMap<u8, u8>, s: &[u8]) {
    m.extend(s.iter().map(|&b| (b, b)));
}

#[cfg(box_collect)]
pub fn f(s: &[u8]) -> Box<[u64]> {
    s.iter().copied().map(u64::from).collect()
}

#[cfg(to_uppercase)]
pub fn f(a: &str) -> String {
    a.to_uppercase()
}

#[cfg(wc_const_u128)]
pub fn f() -> usize {
    Vec::<u128>::with_capacity(200_000_000).capacity()
}

#[cfg(wc_guarded_u128)]
pub fn f(n: usize) -> usize {
    if n < (1 << 28) { Vec::<u128>::with_capacity(n).capacity() } else { 0 }
}

#[cfg(rc_collect)]
pub fn f(s: &[u8]) -> std::rc::Rc<[u64]> {
    s.iter().copied().map(u64::from).collect()
}

#[cfg(any(scalar_std, no_std_core))]
pub fn f(x: u32) -> u32 {
    x / 2
}
