//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The refusing twins of `vec_param_length_invariant_loop.rs`: each body changes
//! the vector's length inside the loop, so the length read before the loop is
//! stale, and each panics on a two-element vector.

pub fn clears(v: &mut Vec<u32>) { //~ ERROR failed for `vec_param_length_invariant_loop_refused::clears`
    for i in 0..v.len() {
        v[i] = 0;
        v.clear();
    }
}

pub fn truncates_hoisted(v: &mut Vec<u32>) { //~ ERROR failed for `vec_param_length_invariant_loop_refused::truncates_hoisted`
    let n = v.len();
    for i in 0..n {
        v.truncate(i);
        v[i] = 0;
    }
}

fn shrink(v: &mut Vec<u32>) {
    v.pop();
}

pub fn through_a_helper(v: &mut Vec<u32>) { //~ ERROR failed for `vec_param_length_invariant_loop_refused::through_a_helper`
    for i in 0..v.len() {
        shrink(v);
        v[i] = 0;
    }
}

pub fn replaced(v: &mut Vec<u32>) { //~ ERROR failed for `vec_param_length_invariant_loop_refused::replaced`
    for i in 0..v.len() {
        let _ = std::mem::take(v);
        v[i] = 0;
    }
}

// NOT a panicking program in safe Rust: two live `&mut Vec` arguments cannot alias.
// It stays refused ON PURPOSE. The invariant-length fact counts only the uses of
// `v`, and `w.clear()` could shrink the same vector if the arguments aliased; whether
// two `&mut` arguments may be trusted disjoint is `docs/DECISION_QUEUE.md` D15 (D96 since
// the 2026-10-14 merge), adopted only disclosed and demoted. A green here means that
// premise was used without the disclosure. It was: the merged tree's `Vec` region over
// `v` (`vec_region.rs`) proved both rows kernel-certified, nothing disclosed, until D101
// (2026-10-15) gave an `&mut` root no region beside another argument that can write.
pub fn second_mut_vec_argument(v: &mut Vec<u32>, w: &mut Vec<u32>) { //~ ERROR failed for `vec_param_length_invariant_loop_refused::second_mut_vec_argument`
    for i in 0..v.len() {
        w.clear();
        v[i] = 0;
    }
}
