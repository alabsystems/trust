//@ needs-trust-verify
// `aux-crate`, not `aux-build`: the aux's crate name IS this crate's name (its file
// stem is this file's), which is what puts a duplicate crate name in the graph.
//@ aux-crate: dep=args_fingerprint_full_range.rs
//@ revisions: full partial
//@ compile-flags: --crate-type lib -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[full] check-pass
//@[partial] check-fail
//! ARGS-FINGERPRINT-READ-1 (2026-10-07) — A CALLEE'S OWN GENERIC ARGUMENTS ARE READ
//! PAST THE DUPLICATE-CRATE-NAME ARGUMENT FINGERPRINT.
//!
//! In a crate graph with a duplicate crate NAME the extractor appended
//! `::<__trust_args@HEX>` to every generic callee (until round 2, below). trust-vcgen's
//! `collection_range::method_generic_args` read that tag as the method's turbofish,
//! so a `drain(..)` (which cannot fail `slice::range`) was refuted as
//! `Call::drain::panic-freedom-unverified`, `splice(.., _)` / `extract_if(.., _)` /
//! `VecDeque::range(..)` / `String::drain(..)` minted their fail-honest rows and
//! `as_chunks::<4>` was charged as a zero chunk size. Found on clean `parallel.rs:152`.
//! (The same tag hid a generic fn's self call from `termination::direct_call_identity`;
//! that is pinned at the trust-vcgen level, `args_fingerprint_dupname_realmir.rs`,
//! because such a self call is ALSO an absent callee in this graph — KNOWN_HAZARDS
//! ARGS-FINGERPRINT-READ-1, OPEN — which the default policy refuses on its own.)
//!
//! `full`: no call here can panic; the crate must verify. `partial`: the same `drain`
//! with a range that CAN panic must stay refused — stripping the tag must not widen
//! the carve-out.
//!
//! MEASURED 2026-10-07, each revision built by hand with its flags plus
//! `--emit=metadata -Ztrust-verify-output=json`, the aux with its own:
//!
//! * BEFORE, the preview3 stage 1 (main `7be75e9a80`): `full` exits 1 —
//!   `dq_drain_full` and `vec_drain_full` failed `Call::drain::panic-freedom-unverified`;
//!   `vec_splice_full`, `dq_range_full` and `chunks4` unknown
//!   (`vec-range-method-bounds-unmodeled`, `vecdeque-range-bounds-unmodeled`,
//!   `slice-const-chunk-size-zero`). `partial` exits 1, `vec_drain_to` failed.
//! * AFTER, the stage 1 of this change: `full` exits 0 (0 failed; neither of its 2
//!   unknown rows is one named here). `partial` exits 1, `vec_drain_to` failed.
//! * ROUND 2 (same day): reading past the tag was refuted for TYPE paths (a crate
//!   named `core` renders the real `RangeFull`'s spelling; pinned by
//!   `forged_core_range_full/drain_range_full_from_forged_core.rs`). The producer now
//!   tags a call only when an argument names a crate whose name does not identify it;
//!   here none does (`u32`, `core`, `alloc`), so these calls are untagged and `full`
//!   still passes for that reason, while a tagged `RangeFull` is declined.
#![feature(slice_as_chunks)]
#![allow(stable_features)]
// Loads the same-named aux (an unused `--extern` is never loaded) without calling
// it: a call would add an absent-callee row unrelated to this test.
extern crate dep;

use std::collections::VecDeque;

#[cfg(full)]
pub fn dq_drain_full(mut q: VecDeque<u32>) -> usize {
    q.drain(..).count()
}

#[cfg(full)]
pub fn vec_drain_full(v: &mut Vec<u32>) -> usize {
    v.drain(..).count()
}

#[cfg(full)]
pub fn vec_splice_full(v: &mut Vec<u32>) -> usize {
    v.splice(.., [1u32, 2]).count()
}

#[cfg(full)]
pub fn dq_range_full(q: &VecDeque<u32>) -> usize {
    q.range(..).count()
}

#[cfg(full)]
pub fn chunks4(v: &[u8]) -> usize {
    v.as_chunks::<4>().0.len()
}

#[cfg(partial)]
pub fn vec_drain_to(v: &mut Vec<u32>, n: usize) -> usize {
    v.drain(..n).count()
}
