//@ revisions: narrow_dst widen_dst widen_src ref_dst nested_ref narrow_ref call_dst param_call
//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
#![allow(unused_unsafe)]
//! UNION-SIBLING-WRITE-1 (docs/KNOWN_HAZARDS.md, docs/DECISION_QUEUE.md; the wave-24
//! review of VC-NARROW-CAST-FALSE-REFUTE-1): the run witness. A union's fields overlap,
//! so a write to `u.b` rewrites `u.a`; vcgen's place names took `u.0` and `u.1` for
//! disjoint storage, so a fact about `u.0` survived a write of `u.1`. Each revision
//! builds ONE function on the advisory lane, which elides an overflow `Assert` whose row
//! is kernel-certified, and calls it at its witness:
//!
//! * `narrow_dst` — `u.a = x as u8; u.b = -56; if x < 0x80 { u.a + 0x7f }` at `x = 0`
//!   (`u.a` reads 200): the narrowing cast's identity `x <= 255 => u.0 == x`
//!   (VC-NARROW-CAST-FALSE-REFUTE-1, commit `51eac007f3`) was carried past the write;
//! * `widen_dst` — `u.a = x as u64; u.b = -1; if x < 0x80 { u.a + 0x7f }` at `x = 0`
//!   (`u.a` reads `u64::MAX`): a widening cast's `u.0 == x`, the same staleness BEFORE
//!   that commit;
//! * `widen_src` — `let b = u.a as u64; u.b = f32::from_bits(5); if u.a < 0x80 { b +
//!   (u64::MAX - 0x7f) }` at `u.a = 200`: the guard reads the sibling-rewritten `u.a`.
//!
//! Each must panic "attempt to add with overflow" exactly as vanilla Rust does.
//!
//! BEFORE (measured 2026-10-12 on the stage 1 of `51eac007f3`, `scratchpad/stage1-w24`,
//! each revision built with exactly these flags plus `--cfg <revision>` and
//! `TRUST_ELIDE_DEBUG=1`): every revision built rc=0 with `TRUST_ELIDE: elided 1` (or
//! more) for its function, and its binary printed the wrapped value and exited 0
//! (`narrow_dst` 71, `widen_dst` 126, `widen_src` 72). Built `-Ztrust-verify=off`, and by
//! stock `rustc` 1.97.1, each panics with the error pattern (exit 101).
//!
//! AFTER (measured 2026-10-12 on the stage 1 of `046ef49e3e`, `scratchpad/stage1-w24r`): a
//! write through a union field adds the union value's own name to every write oracle
//! (`path_defs::union_write_cover_name`), which rebinds each sibling through the prefix
//! relation. `narrow_dst` and `widen_dst` print `elided 0`; `widen_src` prints `elided 1`
//! (the constant `u64::MAX - 0x7f` subtraction, a true row); every revision panics with the
//! error pattern (exit 101), also at `-Copt-level=3`.
//!
//! UNION-SIBLING-WRITE-2 (the review of INTERVAL-WRITE-LOCKSTEP-2, 2026-10-12): the same
//! sibling write THROUGH A POINTER. The cover above was taken on the syntactic place, so
//! a store `*r = x` through `r = &mut u.b` (named `u.1` by the referent fold, but with no
//! `Field` projection on `(*r)`) had none, a pointer into a union field put only `u.1` on
//! the havoc list of a call it is handed to, and a callee's write `(*r).b = v` spelled in
//! the caller's names dropped the root that covered `u.a`. Each revision writes `u.a = 5`,
//! then `x` into `u.b` through a pointer, then reads `u.a + (u64::MAX - 5)` at `x = 7`:
//!
//! * `ref_dst` — `let r = &mut u.b; *r = x`;
//! * `nested_ref` — the union nested in a struct, `&mut s.u.b`;
//! * `narrow_ref` — `narrow_dst` with `-56` stored through `&mut u.b` (at `x = 0`);
//! * `call_dst` — `set(&mut u.b, x)`, a local callee storing through its `&mut`;
//! * `param_call` — `set_b(p, x)` on a `p: &mut W` parameter, a local callee writing
//!   `(*r).b`, whose write set the compiler installs (the refined call havoc).
//!
//! BEFORE (measured 2026-10-12 on the stage 1 of `0f03df468d`, built from this tree's
//! `crates/trust-vcgen/src` = `2ff337db8b`): each revision built rc=0 with `TRUST_ELIDE:
//! elided` 1 or 2 for its function and printed the wrapped value (`narrow_ref` 71,
//! every other revision 1), exit 0; the same on the stage 1 of `046ef49e3e`
//! (`scratchpad/stage1-w24r`). Built `-Ztrust-verify=off`, each panics with the error
//! pattern. AFTER (the fixed stage 1): each panics with it, exit 101, eliding only the true
//! constant subtraction. Detail: `docs/KNOWN_HAZARDS.md` UNION-SIBLING-WRITE-2.

use std::hint::black_box;

pub union V { pub a: u8, pub b: i8 }
pub union U { pub a: u32, pub b: f32 }
pub union V2 { pub a: u64, pub b: i64 }

#[cfg(narrow_dst)]
#[inline(never)]
pub fn sibling(x: u32) -> u64 {
    let mut u = V { a: 0 };
    u.a = x as u8;
    u.b = -56;
    if x < 0x80 { ((unsafe { u.a }) + 0x7f) as u64 } else { 0 }
}

#[cfg(widen_dst)]
#[inline(never)]
pub fn sibling(x: u32) -> u64 {
    let mut u = V2 { a: 0 };
    u.a = x as u64;
    u.b = -1;
    if x < 0x80 { (unsafe { u.a }) + 0x7f } else { 0 }
}

#[cfg(widen_src)]
#[inline(never)]
pub fn sibling(x: u32) -> u64 {
    let mut u = U { a: x };
    let b = unsafe { u.a } as u64;
    u.b = f32::from_bits(5);
    if unsafe { u.a } < 0x80 { b + (u64::MAX - 0x7f) } else { 0 }
}

pub union W { pub a: u64, pub b: u64 }
pub struct SW { pub k: u64, pub u: W }

#[cfg(ref_dst)]
#[inline(never)]
pub fn sibling(x: u32) -> u64 {
    let mut u = W { a: 0 };
    u.a = 5;
    let r: &mut u64 = unsafe { &mut u.b };
    *r = x as u64;
    (unsafe { u.a }) + (u64::MAX - 5)
}

#[cfg(nested_ref)]
#[inline(never)]
pub fn sibling(x: u32) -> u64 {
    let mut s = SW { k: 1, u: W { a: 0 } };
    s.u.a = 5;
    let r: &mut u64 = unsafe { &mut s.u.b };
    *r = x as u64;
    (unsafe { s.u.a }) + (u64::MAX - 5)
}

#[cfg(narrow_ref)]
#[inline(never)]
pub fn sibling(x: u32) -> u64 {
    let mut u = V { a: 0 };
    u.a = x as u8;
    let r: &mut i8 = unsafe { &mut u.b };
    *r = -56;
    if x < 0x80 { ((unsafe { u.a }) + 0x7f) as u64 } else { 0 }
}

#[cfg(call_dst)]
#[inline(never)]
fn set(r: &mut u64, v: u64) {
    *r = v;
}

#[cfg(call_dst)]
#[inline(never)]
pub fn sibling(x: u32) -> u64 {
    let mut u = W { a: 0 };
    u.a = 5;
    set(unsafe { &mut u.b }, x as u64);
    (unsafe { u.a }) + (u64::MAX - 5)
}

#[cfg(param_call)]
#[inline(never)]
fn set_b(r: &mut W, v: u64) {
    r.b = v;
}

#[cfg(param_call)]
#[inline(never)]
pub fn sibling_in(p: &mut W, x: u32) -> u64 {
    p.a = 5;
    set_b(p, x as u64);
    (unsafe { p.a }) + (u64::MAX - 5)
}

#[cfg(param_call)]
#[inline(never)]
pub fn sibling(x: u32) -> u64 {
    let mut w = W { a: 0 };
    sibling_in(black_box(&mut w), x)
}

fn main() {
    #[cfg(any(narrow_dst, widen_dst, narrow_ref))]
    println!("{}", sibling(black_box(0)));
    #[cfg(widen_src)]
    println!("{}", sibling(black_box(200)));
    #[cfg(any(ref_dst, nested_ref, call_dst, param_call))]
    println!("{}", sibling(black_box(7)));
}
