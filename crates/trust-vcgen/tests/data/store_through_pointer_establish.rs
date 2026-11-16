// Counter-programs for the ESTABLISH POINT of a store through a pointer
// (`generate::block_defs::def_subject_establish_stmt`). A store `*x = v` emits the
// block def `x* == v`; the lanes that thread block defs into successors version each
// def at the statement that establishes it, so the stored value and the value `*x`
// held BEFORE the store are distinct symbols. Until 2026-09-30 every establish
// search was keyed on the subject's BASE (`x`, for the borrow `x = &..`), which a
// store through `x` never writes: the store's def had no establish point, was
// threaded BARE, and shared its symbol with the bare read of `*x` before the store.
// `let i = *m; if i < s.len() { *m = usize::MAX; s[*m] }` then carried `i == m*` and
// `m* == usize::MAX` together, the guard read `usize::MAX < s.len()`, and the
// `[slice]` row was kernel-certified PROVED. The r8c union review measured the
// closure shapes (a `Fn` closure's captured `*mut usize` written directly, and
// through `&raw mut *p`).
//
// Every `store_*` body panics natively (`index out of bounds: the len is 4 but the
// index is 18446744073709551615`, -O0 and -O3, `-C overflow-checks=on`). The
// `*_proves` bodies are PRECISION controls: the stored value itself bounds the index,
// which needs the versioned store def to connect to the read after it.
//
// Fixtures: tests/fixtures/store_through_pointer_establish_<fn>_mir.json (a closure
// body `f::{closure#0}` is saved as `f_closure0`), dumped from this file by Trust
// `main` stage 1 a7ea88986d with
//   rustc --edition 2024 --crate-type lib -Ztrust-verify-profile=unix_hardened \
//         -Ztrust-policy=advisory -Ztrust-dump=mir:<dir> \
//         crates/trust-vcgen/tests/data/store_through_pointer_establish.rs
// run from the repository root (so `span.file` is already repo-relative; nothing
// in the dumps was edited).
#![allow(unused_mut, dead_code, unused_unsafe)]

pub struct PW {
    pub p: *mut usize,
}

// A raw-pointer parameter, stored through directly.
pub fn store_through_raw_param(s: &[u8], m: *mut usize) -> u8 {
    let i = unsafe { *m };
    if i < s.len() {
        unsafe {
            *m = usize::MAX;
        }
        s[unsafe { *m }]
    } else {
        0
    }
}

// A `&mut` parameter, stored through directly.
pub fn store_through_mut_ref_param(s: &[u8], r: &mut usize) -> u8 {
    let i = *r;
    if i < s.len() {
        *r = usize::MAX;
        s[*r]
    } else {
        0
    }
}

// A raw pointer behind a SHARED reference, stored through directly.
pub fn store_through_shared_ref_field(s: &[u8], w: &PW) -> u8 {
    let i = unsafe { *w.p };
    if i < s.len() {
        unsafe {
            *w.p = usize::MAX;
        }
        s[unsafe { *w.p }]
    } else {
        0
    }
}

// The same behind `&mut`.
pub fn store_through_mut_ref_field(s: &[u8], w: &mut PW) -> u8 {
    let i = unsafe { *w.p };
    if i < s.len() {
        unsafe {
            *w.p = usize::MAX;
        }
        s[unsafe { *w.p }]
    } else {
        0
    }
}

// Through `&raw mut *w.p`.
pub fn store_through_raw_mut_reborrow(s: &[u8], w: &PW) -> u8 {
    let i = unsafe { *w.p };
    if i < s.len() {
        let q = unsafe { &raw mut *w.p };
        unsafe {
            *q = usize::MAX;
        }
        s[unsafe { *w.p }]
    } else {
        0
    }
}

// A closure body (`Fn`, `_1: &{closure}`) storing through its captured `*mut usize`.
pub fn store_through_closure_capture(s: &[u8], mut n: usize) -> u8 {
    let p = &raw mut n;
    let f = move |t: &[u8]| -> u8 {
        let i = unsafe { *p };
        if i < t.len() {
            unsafe {
                *p = usize::MAX;
            }
            t[unsafe { *p }]
        } else {
            0
        }
    };
    f(s)
}

// The same through `&raw mut *p`.
pub fn store_through_closure_capture_reborrow(s: &[u8], mut n: usize) -> u8 {
    let p = &raw mut n;
    let f = move |t: &[u8]| -> u8 {
        let i = unsafe { *p };
        if i < t.len() {
            let q = unsafe { &raw mut *p };
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

// PRECISION: the stored value bounds the index.
pub fn stored_value_through_raw_param_proves(s: &[u8; 8], m: *mut usize) -> u8 {
    unsafe {
        *m = 3;
    }
    s[unsafe { *m }]
}

// PRECISION: the same through a `&mut` parameter.
pub fn stored_value_through_mut_ref_param_proves(s: &[u8; 8], r: &mut usize) -> u8 {
    *r = 3;
    s[*r]
}
