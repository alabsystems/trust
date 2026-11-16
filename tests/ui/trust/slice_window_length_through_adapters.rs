//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
#![crate_type = "lib"]
//! A `for` loop over `windows(n)` / `chunks_exact(n)` knows each item's length
//! through the core adapters between the constructor and the loop.
//!
//! MEASURED OVER-REFUSAL, 2026-09-29, on the 659-program ordinary-Rust sweep:
//! vcgen's slice-chunking tracer (`container_len::trace_slice_iter_item`)
//! walked copies and `into_iter` only, so every function below was refuted with
//! `w__slice_len = 0` — a counterexample, fatal on the default lane — although
//! the item has length exactly `n`. It now follows the item-preserving adapters
//! (`rev`, `skip`, `step_by`, `take`, `filter`, ...) and, by field path,
//! `enumerate`'s `(index, item)` and `zip`'s `(left, right)`.
//!
//! `slice_window_length_through_adapters_refused.rs` holds the out-of-bounds
//! twins, which really panic. `zip` is pinned only there: its length facts hold
//! (`zip_wrong_side` is refuted with the right side's length), but the native lane
//! does not lower a `Zip` of two `ChunksExact` yet, so a correct zipped loop still
//! fails the build on that gap.

pub fn sorted(v: &[u32]) -> bool {
    for (_, w) in v.windows(2).enumerate() {
        if w[0] > w[1] {
            return false;
        }
    }
    true
}

pub fn first_descent(v: &[u32]) -> Option<usize> {
    for (i, w) in v.windows(2).enumerate() {
        if w[0] > w[1] {
            return Some(i);
        }
    }
    None
}

pub fn sorted_backwards(v: &[u32]) -> bool {
    for w in v.windows(2).rev() {
        if w[0] > w[1] {
            return false;
        }
    }
    true
}

pub fn sorted_after_first(v: &[u32]) -> bool {
    for w in v.windows(2).skip(1) {
        if w[0] > w[1] {
            return false;
        }
    }
    true
}

pub fn odd_bytes(v: &[u8]) -> u8 {
    let mut x = 0u8;
    for (_, c) in v.chunks_exact(2).enumerate() {
        x ^= c[1];
    }
    x
}

pub fn even_bytes_backwards(v: &[u8]) -> u8 {
    let mut x = 0u8;
    for c in v.chunks_exact(2).rev() {
        x ^= c[0];
    }
    x
}
