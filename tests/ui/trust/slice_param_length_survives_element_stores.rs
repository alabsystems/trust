//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! A `&mut [T]` parameter keeps its length across stores to its ELEMENTS, so a
//! guard relating it to another length still holds inside the loop.
//!
//! MEASURED OVER-REFUSAL, 2026-09-29, on the ordinary-Rust sweep (u02, u03, t01,
//! r29): each function below was refuted with `w__slice_len = 0`. An element store
//! through `w` is an opaque store, which havocs the base name `w`, and the
//! path-definition fixpoint applied the DESTINATION relation to that havoc list —
//! including its derived slice-length channel — so the store severed every fact
//! about `w`'s length at the loop header. A slice's length lives in the pointer, not
//! in the memory a store writes; the havoc lists now kill without that channel
//! (`path_defs::formula_survives_havoc`), and every name whose length CAN be reseated
//! is in them by its own derived spelling. The refusing twins reseat `w` in the
//! loop: `slice_param_length_survives_element_stores_refused.rs`.

pub fn fill(v: &[u32], w: &mut [u32]) {
    if v.len() == w.len() {
        for i in 0..v.len() {
            w[i] = 0;
        }
    }
}

pub fn copy_same(v: &[u32], w: &mut [u32]) {
    if v.len() == w.len() {
        for i in 0..v.len() {
            w[i] = v[i];
        }
    }
}

pub fn copy_shorter(v: &[u32], w: &mut [u32]) {
    if v.len() <= w.len() {
        for i in 0..v.len() {
            w[i] = v[i];
        }
    }
}

pub fn copy_enumerate(v: &[u32], w: &mut [u32]) {
    if v.len() == w.len() {
        for (i, &x) in v.iter().enumerate() {
            w[i] = x;
        }
    }
}
