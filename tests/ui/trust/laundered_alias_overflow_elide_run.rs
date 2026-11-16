//@ revisions: cast local_ref cast_const wrapping_add direct cell_direct cell_cast_store
//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
#![allow(unused_mut, unused_unsafe, unused_assignments)]
//! LAUNDERED-ALIAS-ELIDE-1 / LAUNDERED-ALIAS-STORE (docs/KNOWN_HAZARDS.md,
//! docs/DECISION_QUEUE.md): the run witness. Each revision builds ONE function (so one
//! spelling cannot mask another) of the shape
//!
//! ```ignore (illustrative)
//! let mut len = m;
//! let p = &raw mut len;
//! let q = <a copy of p>;
//! unsafe { let x = *q; *p = n; if *q > 7 { return 0; } x + 1 }
//! ```
//!
//! and calls it at `(usize::MAX, 3)`: `x` is `usize::MAX`, so `x + 1` must panic
//! "attempt to add with overflow" exactly as vanilla Rust does.
//!
//! * `cast`         — `q = p as *const usize`;
//! * `local_ref`    — `let p: *mut usize = &mut len`, then `q = p as *const usize`;
//! * `cast_const`   — `q = p.cast_const()`;
//! * `wrapping_add` — `q = p.wrapping_add(0)`;
//! * `direct`       — `q = p.wrapping_add(0)`, and the write is `len = n` itself.
//! * `cell_direct`  — LAUNDERED-ALIAS-CELL-1 (wave-24 review, 2026-10-12): the storage
//!   is a `Cell<usize>` whose address escapes by the SHARED borrow `Cell::as_ptr(&c)`;
//!   `q = c.as_ptr() as *const usize`, and the write is `c = Cell::new(n)` itself.
//! * `cell_cast_store` — the same `Cell`, stored WHOLE through `&c as *const
//!   Cell<usize> as *mut Cell<usize>` (interior mutation; `invalid_reference_casting`
//!   allowed). The wave-24 `Rvalue::Cast` arm folds that pointer to `c`.
//!
//! vcgen spelled the store by `p`'s referent (`len`) and every read through `q` by the
//! opaque `q*`, so both reads of `*q` shared one version, the guard bounded `x`, the
//! `x + 1` row was proved and kernel-certified, and the advisory lane elided its
//! overflow check (`TRUST_ELIDE: elided 1`).
//!
//! BEFORE (measured 2026-10-11 on the stage 1 of `1213387e6d`,
//! `scratchpad/stage1-w24probe`, each revision built with exactly these flags plus
//! `--cfg <revision>`): `local_ref`, `cast_const`, `wrapping_add` and `direct` built
//! with exit 0 and `TRUST_ELIDE: elided 1` for `laundered`, and their binaries printed
//! `0` and exited 0; the error pattern never appeared. `cast` built with exit 0 but its
//! native verifier reported `timed_out=4` in all five builds on the shared host (load
//! averages 9.5 to 30), so its rows were runtime-checked, nothing was elided, and it
//! panicked; the scout's build of the same body on the same stage 1 (`lv3.rs`,
//! `timed_out=0`) elided the check and printed `0`. The same source built
//! `-Ztrust-verify=off`, and by stock `rustc` 1.97.1, panics "attempt to add with
//! overflow" (exit 101) in every revision.
//!
//! AFTER (built and measured 2026-10-12 on the stage 1 of `51eac007f3`, wave-24
//! integration): the referent fold resolves the `as` casts (`cast`, `local_ref`: `*q` is
//! `len`), and a write into escaped storage in a body that reads through an unresolved
//! raw pointer havocs the whole-function list (`cast_const`, `wrapping_add`, `direct`:
//! `q*` gets a new version at the write). No row is proved, nothing is elided, and those
//! five revisions panic with the error pattern.
//!
//! `cell_direct` and `cell_cast_store` were NOT closed by that fix: on the same stage 1
//! each built with `TRUST_ELIDE: elided 1` for `laundered`, and its binary printed `0`
//! and exited 0 (also at `-Copt-level=1` and `3` for `cell_direct`); `cell_cast_store`
//! panicked BEFORE the wave-24 `Cast` arm (its store was opaque). Stock `rustc` 1.97.1
//! and `-Ztrust-verify=off` panic. The escaped-storage roots counted only write-capable
//! borrows (`&mut`, `&raw`); now they also count every shared borrow of a place that may
//! hold an `UnsafeCell` inline (`path_defs::laundered_alias_roots`). AFTER (measured
//! 2026-10-12 on the stage 1 of `046ef49e3e`, `scratchpad/stage1-w24r`): both print
//! `elided 0` and panic with the error pattern (`cell_direct` also at `-Copt-level=1`, `3`).

use std::hint::black_box;

#[cfg(cast)]
#[inline(never)]
pub fn laundered(m: usize, n: usize) -> usize {
    let mut len = m;
    let p = &raw mut len;
    let q: *const usize = p as *const usize;
    unsafe {
        let x = *q;
        *p = n;
        if *q > 7 {
            return 0;
        }
        x + 1
    }
}

#[cfg(local_ref)]
#[inline(never)]
pub fn laundered(m: usize, n: usize) -> usize {
    let mut len = m;
    let p: *mut usize = &mut len;
    let q = p as *const usize;
    unsafe {
        let x = *q;
        *p = n;
        if *q > 7 {
            return 0;
        }
        x + 1
    }
}

#[cfg(cast_const)]
#[inline(never)]
pub fn laundered(m: usize, n: usize) -> usize {
    let mut len = m;
    let p = &raw mut len;
    let q = p.cast_const();
    unsafe {
        let x = *q;
        *p = n;
        if *q > 7 {
            return 0;
        }
        x + 1
    }
}

#[cfg(wrapping_add)]
#[inline(never)]
pub fn laundered(m: usize, n: usize) -> usize {
    let mut len = m;
    let p = &raw mut len;
    let q = p.wrapping_add(0);
    unsafe {
        let x = *q;
        *p = n;
        if *q > 7 {
            return 0;
        }
        x + 1
    }
}

#[cfg(direct)]
#[inline(never)]
pub fn laundered(m: usize, n: usize) -> usize {
    let mut len = m;
    let p = &raw mut len;
    let q = p.wrapping_add(0);
    unsafe {
        let x = *q;
        len = n;
        if *q > 7 {
            return 0;
        }
        x + 1
    }
}

#[cfg(cell_direct)]
#[inline(never)]
pub fn laundered(m: usize, n: usize) -> usize {
    let mut c = std::cell::Cell::new(m);
    let q = c.as_ptr() as *const usize;
    let nc = std::cell::Cell::new(n);
    unsafe {
        let x = *q;
        c = nc;
        if *q > 7 {
            return 0;
        }
        x + 1
    }
}

#[cfg(cell_cast_store)]
#[inline(never)]
#[allow(invalid_reference_casting)]
pub fn laundered(m: usize, n: usize) -> usize {
    let c = std::cell::Cell::new(m);
    let q = c.as_ptr();
    let w = &c as *const std::cell::Cell<usize> as *mut std::cell::Cell<usize>;
    let nc = std::cell::Cell::new(n);
    unsafe {
        let x = *q;
        *w = nc;
        if *q > 7 {
            return 0;
        }
        x + 1
    }
}

fn main() {
    println!("{}", laundered(black_box(usize::MAX), black_box(3)));
}
