//@ revisions: dep_o0 dep_o3 same_crate atomic vv_push option_map drop_wrapper scope_wrapper
//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: vec_region_stash_dep.rs
//@ aux-build: vec_region_stash_atomic_dep.rs
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@[dep_o3] compile-flags: -Copt-level=3
//@ error-pattern: attempt to subtract with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
#![allow(unused_unsafe)]
//! VEC-REGION-DEF-BLOCK-STASH-1 (docs/KNOWN_HAZARDS.md, docs/DECISION_QUEUE.md): the run
//! witness. Each revision builds ONE function (so one spelling cannot mask another) of
//! the shape
//!
//! ```ignore (illustrative)
//! let mut v = w;
//! <lend `&mut v` to code that keeps the pointer>;
//! if v.len() == 0 { return 0; }
//! <clear `v` through the kept pointer, from a call that names no `Vec`>;
//! v.len() - 1
//! ```
//!
//! and calls it with `vec![1, 2, 3]`: the clear empties `v`, so `v.len() - 1` must panic
//! "attempt to subtract with overflow" exactly as rustc's binary does.
//!
//! * `dep_o0`, `dep_o3` — a verify-off dependency's `stash(&mut v)` keeps the pointer in a
//!   `static mut`; its `clear_it()` clears through it (`-Copt-level=0` and `3`);
//! * `same_crate`       — the same two functions in this crate;
//! * `atomic`           — a sound dependency API: a safe `stash` into an `AtomicPtr` and an
//!   `unsafe fn clear_stashed` whose contract the caller meets;
//! * `vv_push`          — `vv.push(&mut v)` (a std callee), then the dependency's
//!   `stash_first(&mut vv)` keeps `vv[0]`;
//! * `option_map`       — `Some(&mut v).map(stash)` (std hands the borrow to `stash`);
//! * `drop_wrapper`     — `drop(W(&mut v))`, `W`'s `Drop` calling `stash(self.0)`;
//! * `scope_wrapper`    — `{ let _w = W(&mut v); }`, the same glue run by MIR `Drop`.
//!
//! The definition block's `&mut v` was `Closed` (or its single later use an activation),
//! so the `Vec` region of `v` started after it; the clear names neither `v` nor the
//! borrow, so both `len` reads stated `_n == L0` over one fresh length, `v.len() - 1` was
//! proved and clean-kernel Certified, and the advisory build ELIDED its overflow check.
//!
//! BEFORE (measured 2026-10-13 on the stage 1 of wave 25 with its review fixes,
//! `scratchpad/stage1-w25f`, tree of `a971311ee2`; each revision built with exactly these
//! flags plus `--cfg <revision> -A unused -Zui-testing -Zdeduplicate-diagnostics=no
//! --error-format=json` against the two aux crates built as their headers say):
//! every revision built with exit 0 and `TRUST_ELIDE: elided 1` for its `f`, and every
//! binary printed `f = 18446744073709551615` and exited 0; the error pattern never
//! appeared. Stock rustc 1.97.1 panics with it (exit 101) on every revision.
//!
//! AFTER (predicted; the lane builds no stage 1): a definition-block borrow handed to
//! anything but a sysroot inherent callee, handed only references to `v` and otherwise
//! pointer-free data, leaves no region for `v`, so no length fact is minted, the row is
//! not proved, nothing is elided, and each binary panics with the pattern (exit 101).
//! The certify verdicts are pinned by `vec_region_def_block_stash.rs`; vcgen's half on
//! real MIR by `trust-vcgen/src/generate/vec_region_twophase_tests.rs`.

#[cfg(any(dep_o0, dep_o3, vv_push, option_map, drop_wrapper, scope_wrapper))]
extern crate vec_region_stash_dep as dep;

#[cfg(atomic)]
extern crate vec_region_stash_atomic_dep as dep;

#[cfg(any(dep_o0, dep_o3))]
#[inline(never)]
pub fn f(w: Vec<u8>) -> usize {
    let mut v = w;
    dep::stash(&mut v);
    if v.len() == 0 {
        return 0;
    }
    dep::clear_it();
    v.len() - 1
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
#[inline(never)]
pub fn f(w: Vec<u8>) -> usize {
    let mut v = w;
    stash(&mut v);
    if v.len() == 0 {
        return 0;
    }
    clear_it();
    v.len() - 1
}

#[cfg(atomic)]
#[inline(never)]
pub fn f(w: Vec<u8>) -> usize {
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
#[inline(never)]
pub fn f(w: Vec<u8>) -> usize {
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
#[inline(never)]
pub fn f(w: Vec<u8>) -> usize {
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
#[inline(never)]
pub fn f(w: Vec<u8>) -> usize {
    let mut v = w;
    drop(W(&mut v));
    if v.len() == 0 {
        return 0;
    }
    dep::clear_it();
    v.len() - 1
}

#[cfg(scope_wrapper)]
#[inline(never)]
pub fn f(w: Vec<u8>) -> usize {
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

fn main() {
    println!("f = {}", f(std::hint::black_box(vec![1u8, 2, 3])));
}
