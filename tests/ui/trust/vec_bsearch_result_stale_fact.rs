//@ needs-trust-verify
//@ edition: 2021
//@ revisions: fresh_let ok_index result_reassigned ok_reassigned_index reused_other_vec stale_overflow
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[fresh_let] check-pass
//@[ok_index] check-pass
//@[result_reassigned] check-fail
//@[ok_reassigned_index] check-fail
//@[reused_other_vec] check-fail
//@[stale_overflow] check-fail
//! **A `binary_search` result fact must not outlive the result's value (W4 fix
//! round 1, Trust 2026-09-25).**
//!
//! VEC-INSERT seeds `Ok(i) => i < len` and `Err(i) => i <= len` on the payload NAME
//! `r@0.0` / `r@1.0` (`trust-vcgen/src/generate/vec_region.rs`,
//! `slice_binary_search_result_definitions`). It did so with no stability gate on
//! `r`, and the place-name algebra did not count `@` (the `Downcast` spelling) as a
//! projection separator, so no later write of `r` — `r = Err(big)`, `r = Ok(big)`,
//! `r = w.binary_search(..)` — killed the fact. The four check-fail revisions are the
//! adversarial probes r12, r12b, r12c and r12d.
//!
//! # Before (stage 1 `0.10.0+g0a25d1c42`, the unfixed VEC-INSERT branch)
//!
//! All four check-fail revisions built rc=0 with the violated row `proved`
//! (kernel-certified), and each panics at runtime: `result_reassigned` with
//! "insertion index (is 100) should be <= len (is 3)" at `f(&mut vec![1,2,3], 9,
//! 100)`; `ok_reassigned_index` with "index out of bounds: the len is 3 but the
//! index is 100"; `reused_other_vec` with "insertion index (is 10) should be <= len
//! (is 3)" at `v = [1,2,3]`, `w = 1..=10`, `x = 20`. `stale_overflow` involves no
//! `Vec` at all: its `j + 1` overflow row was proved, and the verified build (which
//! drops a proved overflow check) returned a wrapped `0` where the unverified build
//! panics "attempt to add with overflow". `origin/main` (`0.10.0+gc2e3daed7`), which
//! has no `binary_search` facts, refuses all four.
//!
//! # After
//!
//! Two independent closures, each pinned in `vec_region_bsearch_tests.rs`: the facts
//! are seeded only when the call is the result's ONE definition and the result is
//! stable (never `&mut`-borrowed or partially written), and a whole write of `r` now
//! kills any fact over `r@v.k` (`@` is a separator in `place_names_overlap`,
//! `place_root` and the two ancestor tests). The check-fail revisions are refused
//! on their own row; the check-pass controls show the lane still fires for a
//! stable result, `match`-bound or `let`-bound.

// A stable, `let`-bound result: one definition, never written again.
#[cfg(fresh_let)]
pub fn insert_sorted(v: &mut Vec<i64>, value: i64) -> bool {
    let r = v.binary_search(&value);
    match r {
        Ok(_) => false,
        Err(pos) => {
            v.insert(pos, value);
            true
        }
    }
}

// `Ok(i)` from the `Vec`'s own search indexes the same `Vec` (probe a06).
#[cfg(ok_index)]
pub fn lookup(v: &Vec<u32>, x: u32) -> u32 {
    if let Ok(i) = v.binary_search(&x) { v[i] } else { 0 }
}

// r12: the result is overwritten with an arbitrary `Err(big)` inside the `Err` arm.
#[cfg(result_reassigned)]
pub fn reassigned(v: &mut Vec<u32>, x: u32, big: usize) -> u32 {
    //[result_reassigned]~^ NOTE [slice] FAILED
    let mut r = v.binary_search(&x);
    match r {
        Err(_) => {
            r = Err(big);
            if let Err(p) = r {
                v.insert(p, x);
            }
            1
        }
        Ok(_) => 0,
    }
}

// r12b: the index twin — `r = Ok(big)` then `v[j]` on a `&Vec`.
#[cfg(ok_reassigned_index)]
pub fn reassigned_index(v: &Vec<u32>, x: u32, big: usize) -> u32 {
    //[ok_reassigned_index]~^ NOTE [slice] FAILED
    let mut r = v.binary_search(&x);
    match r {
        Ok(_) => {
            r = Ok(big);
            if let Ok(j) = r { v[j] } else { 0 }
        }
        Err(_) => 0,
    }
}

// r12c: the natural shape — one `mut r` reused for a second search over a LONGER
// `Vec`; the call that rebinds `r` must kill the first search's fact.
#[cfg(reused_other_vec)]
pub fn reused(v: &mut Vec<u32>, w: &Vec<u32>, x: u32) -> u32 {
    //[reused_other_vec]~^ NOTE unsupported MIR `vec-panic-method-index-unmodeled`
    // Since DECISION_QUEUE D101 (2026-10-15) an `&mut Vec` parameter beside another
    // argument that is not a pure value (here a `&Vec`) gets no `Vec` region, so the
    // call keeps the fail-honest Unknown instead of the region's refuted row: still
    // refused, no longer refuted (measured on the stage 1 of that change).
    let mut r = v.binary_search(&x);
    match r {
        Err(_) => {
            r = w.binary_search_by(|e| e.cmp(&x));
            if let Err(p) = r {
                v.insert(p, x);
            }
            1
        }
        Ok(_) => 0,
    }
}

// r12d: no `Vec` at all — the stale `Ok(i) => i < len` fact discharged `j + 1`.
#[cfg(stale_overflow)]
pub fn stale_overflow(xs: &[u32], x: u32, big: usize) -> usize {
    //[stale_overflow]~^ NOTE [overflow:add] FAILED
    let mut r = xs.binary_search(&x);
    match r {
        Ok(_) => {
            r = Ok(big);
            if let Ok(j) = r { j + 1 } else { 0 }
        }
        Err(_) => 0,
    }
}
