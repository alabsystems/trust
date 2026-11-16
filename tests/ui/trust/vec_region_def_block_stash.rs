//@ revisions: f1 f1b same_crate atomic vv_push option_map drop_wrapper scope_wrapper
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: vec_region_stash_dep.rs
//@ aux-build: vec_region_stash_atomic_dep.rs
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
#![allow(unused_unsafe)]
//! VEC-REGION-DEF-BLOCK-STASH-1 (docs/KNOWN_HAZARDS.md, docs/DECISION_QUEUE.md): the
//! certify verdicts of the bodies whose run witness is `vec_region_def_block_stash_run.rs`.
//!
//! Each revision verifies ONE function (one function's machine rows alone run to
//! ~250 KB under certify, and compiletest keeps 512 KiB of output). Each lends its
//! `Vec` `v`, in `v`'s definition block, to code that keeps the pointer, reads
//! `v.len() == 0`, lets a call that names no `Vec` clear `v` through the kept pointer,
//! and computes `v.len() - 1`:
//!
//! * `f1`           — a verify-off dependency's `stash(&mut v)` / `clear_it()`;
//! * `f1b`          — the same, plus a later charged `v.remove(0)`: the shape that
//!   reached the false proof BEFORE wave 25 (the charged mutator switched the region
//!   facts on);
//! * `same_crate`   — `stash` / `clear_it` in this crate;
//! * `atomic`       — a sound dependency API (`AtomicPtr`, `unsafe fn clear_stashed`);
//! * `vv_push`      — `vv.push(&mut v)`, then the dependency's `stash_first(&mut vv)`;
//! * `option_map`   — `Some(&mut v).map(stash)`;
//! * `drop_wrapper` — `drop(W(&mut v))`, `W`'s `Drop` calling `stash(self.0)`;
//! * `scope_wrapper`— `{ let _w = W(&mut v); }`.
//!
//! The `v.len() - 1` row must not be certified: on `vec![1, 2, 3]` it overflows.
//!
//! BEFORE (measured 2026-10-13 on `scratchpad/stage1-w25f`, the stage 1 of wave 25 with
//! its review fixes, tree of `a971311ee2`; each revision built with exactly these flags
//! plus `--cfg <revision> -Zui-testing -Zdeduplicate-diagnostics=no -A unused
//! --emit=metadata --error-format=json` against the two aux crates built as their
//! headers say): every revision exits 1, and its `f`'s strict-failure error carries
//! `summary: 0 trusted, 1 certified, ...` (`2 certified` for `f1b`, whose `remove` index
//! row is certified over the same false length): the `overflow:sub` row is `proved` with
//! clean-kernel `Certified` evidence. Certify refused each build only on OTHER rows (the
//! dependency's `[trust-absent-callee-assumption]` row, or the same-crate callees' own
//! unsafe rows), so the annotations below did not fire. On the stage 1 before wave 25
//! (`scratchpad/stage1-w25probe`) every revision but `f1b` already read `0 certified`.
//!
//! AFTER (predicted; the lane builds no stage 1): no region for `v`, no length fact, and
//! the row is not proved, so `f`'s summary reads `0 trusted, 0 certified`. Every
//! revision still exits 1.

#[cfg(any(f1, f1b, vv_push, option_map, drop_wrapper, scope_wrapper))]
extern crate vec_region_stash_dep as dep;

#[cfg(atomic)]
extern crate vec_region_stash_atomic_dep as dep;

#[cfg(f1)]
pub fn f(w: Vec<u8>) -> usize {
    //[f1]~^ NOTE summary: 0 trusted, 0 certified,
    let mut v = w;
    dep::stash(&mut v);
    if v.len() == 0 {
        return 0;
    }
    dep::clear_it();
    v.len() - 1
}

#[cfg(f1b)]
pub fn f(w: Vec<u8>) -> usize {
    //[f1b]~^ NOTE summary: 0 trusted, 0 certified,
    let mut v = w;
    dep::stash(&mut v);
    if v.len() == 0 {
        return 0;
    }
    dep::clear_it();
    let r = v.len() - 1;
    if r > 1000 {
        v.remove(0);
    }
    r
}

#[cfg(same_crate)]
static mut P: *mut Vec<u8> = std::ptr::null_mut();

#[cfg(same_crate)]
#[inline(never)]
pub fn stash(v: &mut Vec<u8>) {
    unsafe {
        P = v as *mut Vec<u8>;
    }
}

#[cfg(same_crate)]
#[inline(never)]
pub fn clear_it() {
    unsafe {
        (*P).clear();
    }
}

#[cfg(same_crate)]
pub fn f(w: Vec<u8>) -> usize {
    //[same_crate]~^ NOTE summary: 0 trusted, 0 certified,
    let mut v = w;
    stash(&mut v);
    if v.len() == 0 {
        return 0;
    }
    clear_it();
    v.len() - 1
}

#[cfg(atomic)]
pub fn f(w: Vec<u8>) -> usize {
    //[atomic]~^ NOTE summary: 0 trusted, 0 certified,
    let mut v = w;
    dep::stash(&mut v);
    if v.len() == 0 {
        return 0;
    }
    // SAFETY: `v` is the `Vec` last stashed, live, and not borrowed here.
    unsafe {
        dep::clear_stashed();
    }
    v.len() - 1
}

#[cfg(vv_push)]
pub fn f(w: Vec<u8>) -> usize {
    //[vv_push]~^ NOTE summary: 0 trusted, 0 certified,
    let mut vv: Vec<&mut Vec<u8>> = Vec::new();
    let mut v = w;
    vv.push(&mut v);
    dep::stash_first(&mut vv);
    if v.len() == 0 {
        return 0;
    }
    dep::clear_it();
    v.len() - 1
}

#[cfg(option_map)]
pub fn f(w: Vec<u8>) -> usize {
    //[option_map]~^ NOTE summary: 0 trusted, 0 certified,
    let mut v = w;
    Some(&mut v).map(dep::stash);
    if v.len() == 0 {
        return 0;
    }
    dep::clear_it();
    v.len() - 1
}

#[cfg(any(drop_wrapper, scope_wrapper))]
pub struct W<'a>(pub &'a mut Vec<u8>);

#[cfg(any(drop_wrapper, scope_wrapper))]
impl Drop for W<'_> {
    fn drop(&mut self) {
        dep::stash(self.0)
    }
}

#[cfg(drop_wrapper)]
pub fn f(w: Vec<u8>) -> usize {
    //[drop_wrapper]~^ NOTE summary: 0 trusted, 0 certified,
    let mut v = w;
    drop(W(&mut v));
    if v.len() == 0 {
        return 0;
    }
    dep::clear_it();
    v.len() - 1
}

#[cfg(scope_wrapper)]
pub fn f(w: Vec<u8>) -> usize {
    //[scope_wrapper]~^ NOTE summary: 0 trusted, 0 certified,
    let mut v = w;
    {
        let _w = W(&mut v);
    }
    if v.len() == 0 {
        return 0;
    }
    dep::clear_it();
    v.len() - 1
}
