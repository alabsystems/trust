//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The refusing twins of `slice_param_length_survives_element_stores.rs`: each
//! loop RESEATS `w` onto a shorter slice, so the length the guard related is stale,
//! and each panics on two equal-length slices of length 2.

pub fn reseated_directly(v: &[u32], mut w: &mut [u32]) { //~ ERROR failed for `slice_param_length_survives_element_stores_refused::reseated_directly`
    if v.len() == w.len() {
        for i in 0..v.len() {
            w = &mut std::mem::take(&mut w)[1..];
            w[i] = 0;
        }
    }
}

fn shrink(w: &mut &mut [u32]) {
    let t = std::mem::take(w);
    *w = &mut t[1..];
}

pub fn reseated_by_a_callee(v: &[u32], mut w: &mut [u32]) { //~ ERROR failed for `slice_param_length_survives_element_stores_refused::reseated_by_a_callee`
    if v.len() == w.len() {
        for i in 0..v.len() {
            shrink(&mut w);
            w[i] = 0;
        }
    }
}
