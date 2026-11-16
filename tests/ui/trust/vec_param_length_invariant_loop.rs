//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! Indexing a `&mut Vec` / `&Vec` parameter inside `for i in 0..v.len()` proves
//! when nothing in the body can change the vector's length.
//!
//! MEASURED OVER-REFUSAL, 2026-09-29, on the ordinary-Rust sweep (c59, c59g, c59h,
//! c87, f05): each function below was refuted with the length at 0. The tie
//! `n == len(v)` was a path fact, and the `index_mut` call and the element store
//! in the loop body havoc the name the length lives under, so the loop header
//! dropped it. It is now also a GLOBAL fact when every use of the parameter is a
//! std `len`, `index`, `index_mut`, `deref` or `deref_mut`
//! (`value_facts::build_invariant_vec_len_tie_facts`).
//!
//! `vec_param_length_invariant_loop_refused.rs` holds bodies that CAN change the
//! length, which really panic.

pub fn zero(v: &mut Vec<u32>) {
    for i in 0..v.len() {
        v[i] = 0;
    }
}

pub fn zero_hoisted(v: &mut Vec<u32>) {
    let n = v.len();
    for i in 0..n {
        v[i] = 0;
    }
}

pub fn halve(v: &mut Vec<u32>) {
    for i in 0..v.len() {
        v[i] /= 2;
    }
}

pub fn smallest(v: &Vec<u32>) -> u32 {
    let mut m = u32::MAX;
    for i in 0..v.len() {
        if v[i] < m {
            m = v[i];
        }
    }
    m
}
