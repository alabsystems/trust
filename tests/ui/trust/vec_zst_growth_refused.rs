//@ needs-trust-verify
//@ edition: 2021
//@ revisions: insert_zst push_zst deque_push_zst heap_push_zst unit_struct_push push_sized insert_sized
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[insert_zst] check-fail
//@[push_zst] check-fail
//@[deque_push_zst] check-fail
//@[heap_push_zst] check-fail
//@[unit_struct_push] check-fail
//@[push_sized] check-pass
//@[insert_sized] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
#![allow(dead_code)]
//! Trust (2026-09-29): a std `Vec`/`VecDeque`/`BinaryHeap` of ZERO-SIZED
//! elements is not foundational (`std_growable_sequence_of_zero_sized_elements`,
//! `compiler/rustc_mir_transform/src/trust_verify.rs`; docs/TCB.md, "`insert`
//! inherits `push`'s growth class", CORRECTED 2026-09-29).
//!
//! The vanilla-sysroot class tolerates the growth panic push-like calls share
//! ("capacity overflow" at `len == capacity`) because a SIZED element exhausts
//! memory — an allocation-failure abort — long before that. For a zero-sized
//! element the capacity is `usize::MAX`, no byte is allocated, and a caller may
//! soundly hand in a `Vec<()>` of length `usize::MAX`, so the panic is
//! reachable: `insert_zst` (probe r09) built rc=0 on main (`0.10.0+g4715fe060`,
//! source of `7eddcd160b`) and panicked "capacity overflow" (exit 101) when its
//! driver passed `v` with `set_len(usize::MAX)`.
//!
//! `insert_zst`, `push_zst`, `deque_push_zst` and `heap_push_zst` each built rc=0
//! on main. `unit_struct_push` (a LOCAL zero-sized type) was refused on main
//! already — a local type was never foundational — and stays refused.
//! `push_sized` / `insert_sized` are the controls: the ruled class for a sized
//! element is unchanged (both build, as on main).

#[cfg(insert_zst)]
pub fn f(v: &mut Vec<()>, i: usize) {
    //[insert_zst]~^ ERROR Trust
    if i <= v.len() {
        v.insert(i, ());
    }
}

#[cfg(push_zst)]
pub fn f(v: &mut Vec<()>) {
    //[push_zst]~^ ERROR Trust
    v.push(());
}

#[cfg(deque_push_zst)]
pub fn f(d: &mut std::collections::VecDeque<()>) {
    //[deque_push_zst]~^ ERROR Trust
    d.push_back(());
}

#[cfg(heap_push_zst)]
pub fn f(h: &mut std::collections::BinaryHeap<()>) {
    //[heap_push_zst]~^ ERROR Trust
    h.push(());
}

#[cfg(unit_struct_push)]
#[derive(Clone, Copy)]
pub struct Marker;

#[cfg(unit_struct_push)]
pub fn f(v: &mut Vec<Marker>) {
    //[unit_struct_push]~^ ERROR Trust
    v.push(Marker);
}

#[cfg(push_sized)]
pub fn f(v: &mut Vec<u32>, x: u32) {
    v.push(x);
}

#[cfg(insert_sized)]
pub fn f(v: &mut Vec<u32>, i: usize, x: u32) {
    if i <= v.len() {
        v.insert(i, x);
    }
}
