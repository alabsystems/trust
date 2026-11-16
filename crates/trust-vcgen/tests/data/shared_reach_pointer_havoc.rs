// Counter-programs for the havoc of memory a SHARED reference reaches through a raw
// pointer (the r8c union's `shared_reach_pointer_names`, 2026-09-30; at landing,
// 2026-10-08, CALL-HAVOC-ESCAPE-2's `generate::path_defs::stored_ref_pointee_names`,
// on the whole-function havoc list so an opaque store takes it too). A shared reference
// freezes the bytes it covers; it does not freeze what a raw pointer stored in them
// points to. The pointer is `Copy`, so `w.p` can be read out and written through,
// and that write is defined under Stacked Borrows and Tree Borrows alike (its
// provenance is whatever the pointer was minted with). Every counter-program below
// indexes after the pointee was set to `usize::MAX` and panics natively (`index out
// of bounds: the len is 4 but the index is 18446744073709551615`, -O0 and -O3, with
// `-C overflow-checks=on`); the r8c union review measured the first two and the
// closure body as kernel-certified PROVED on the compiler's entry, and
// `shared_struct_with_raw_ptr`'s `[slice]` row as PROVED, kernel-rechecked, on the
// installed `321aaeda7` lane.
//
// The `*_keeps_*` bodies are PRECISION controls: a frozen field BESIDE the raw
// pointer (or beside a `Box`) keeps its fact across a call that can write through
// the pointer, so the havoc must name the pointer's pointee, never the shared
// reference's base name. They do not panic.
//
// Fixtures: tests/fixtures/shared_reach_pointer_havoc_<fn>_mir.json (a closure body
// `f::{closure#0}` is saved as `f_closure0`), dumped from this file by Trust `main`
// stage 1 a7ea88986d with
//   rustc --edition 2024 --crate-type lib -Ztrust-verify-profile=unix_hardened \
//         -Ztrust-policy=advisory -Ztrust-dump=mir:<dir> \
//         crates/trust-vcgen/tests/data/shared_reach_pointer_havoc.rs
// run from the repository root (so `span.file` is already repo-relative; nothing
// in the dumps was edited).
#![allow(unused_mut, dead_code, unused_unsafe)]

#[inline(never)]
pub fn poke_usize(p: *mut usize) {
    unsafe {
        *p = usize::MAX;
    }
}

#[inline(never)]
pub fn observe(x: &usize) -> usize {
    *x
}

pub struct PW {
    pub p: *mut usize,
}

// A callee writes through the raw pointer read out of the shared reference. No
// `&raw` anywhere: `poke_usize(w.p)` passes a copy of the field.
pub fn shared_struct_with_raw_ptr(s: &[u8], w: &PW) -> u8 {
    let i = unsafe { *w.p };
    if i < s.len() {
        poke_usize(w.p);
        s[unsafe { *w.p }]
    } else {
        0
    }
}

// The same write done in the body, through `&raw const *w.p` cast to `*mut`.
pub fn shared_struct_raw_const_pointee(s: &[u8], w: &PW) -> u8 {
    let i = unsafe { *w.p };
    if i < s.len() {
        let q = unsafe { &raw const *w.p } as *mut usize;
        unsafe {
            *q = usize::MAX;
        }
        s[unsafe { *w.p }]
    } else {
        0
    }
}

pub struct PC {
    pub p: *const usize,
}

// A `*const` field, cast to `*mut` and written directly (no `&raw` at all).
pub fn shared_env_cast_write(t: &[u8], env: &PC) -> u8 {
    let i = unsafe { *env.p };
    if i < t.len() {
        let q = env.p as *mut usize;
        unsafe {
            *q = usize::MAX;
        }
        t[unsafe { *env.p }]
    } else {
        0
    }
}

// The pointer two shared references deep (`w**.0`).
pub fn shared_shared_struct_with_raw_ptr(s: &[u8], w: &&PW) -> u8 {
    let i = unsafe { *w.p };
    if i < s.len() {
        poke_usize(w.p);
        s[unsafe { *w.p }]
    } else {
        0
    }
}

// An OWNED tuple that carries the shared reference (`w.1*.0`).
pub fn owned_tuple_carrying_a_shared_ref(s: &[u8], w: (u8, &PW)) -> u8 {
    let i = unsafe { *w.1.p };
    if i < s.len() {
        poke_usize(w.1.p);
        s[unsafe { *w.1.p }]
    } else {
        0
    }
}

pub struct BW {
    pub b: Box<usize>,
}

// A `Box` behind a shared reference: its pointee is written through a pointer
// derived from it (`&raw const *w.b as *mut usize`).
pub fn shared_struct_box_field(s: &[u8], w: &BW) -> u8 {
    let i = *w.b;
    if i < s.len() {
        poke_usize(&raw const *w.b as *mut usize);
        s[*w.b]
    } else {
        0
    }
}

// A closure body (`Fn`, so `_1: &{closure}`) whose capture is a `*const usize`:
// the pointer is read out of the shared environment and written through.
pub fn closure_body_raw_const_deref(s: &[u8], mut n: usize) -> u8 {
    let p = &raw const n;
    let f = move |t: &[u8]| -> u8 {
        let i = unsafe { *p };
        if i < t.len() {
            let q = unsafe { &raw const *p } as *mut usize;
            unsafe {
                *q = usize::MAX;
            }
            t[unsafe { *p }]
        } else {
            0
        }
    };
    f(s)
}

pub struct PN {
    pub p: *mut usize,
    pub n: usize,
}

// PRECISION: `w.n` sits beside the raw pointer in the frozen bytes; the call that
// can write `*w.p` cannot write `w.n`, so `w.n < 8` still bounds `s[w.n]`.
pub fn shared_sibling_keeps_its_fact(s: &[u8; 8], w: &PN) -> u8 {
    if w.n < 8 {
        poke_usize(w.p);
        s[w.n]
    } else {
        0
    }
}

pub struct BN {
    pub b: Box<usize>,
    pub n: usize,
}

// PRECISION: the same beside a `Box`, across a call handed a reference into it.
pub fn shared_box_sibling_keeps_its_fact(s: &[u8; 8], w: &BN) -> u8 {
    if w.n < 8 {
        let _ = observe(&w.b);
        s[w.n]
    } else {
        0
    }
}
