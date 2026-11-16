//@ needs-trust-verify
//@ edition: 2021
//@ revisions: vec_split_off vec_drain vec_extend_from_within int_rotate
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[vec_split_off] dont-require-annotations: ERROR
//@[vec_drain] dont-require-annotations: ERROR
//@[vec_extend_from_within] dont-require-annotations: ERROR
//@[vec_split_off] check-fail
//@[vec_drain] check-fail
//@[vec_extend_from_within] check-fail
//@[int_rotate] check-pass
//@[int_rotate] forbid-output: panic-freedom-unverified
//! **A container's ELEMENT type does not make its bounds-panicking mutator an
//! "integer method" (W4 fix round 2, Trust 2026-09-26).**
//!
//! `is_bounds_panicking_slice_mutator` gives `split_off`/`drain`/`rotate_*`/
//! `extend_from_within`/... their fail-closed `Call::<m>::panic-freedom-unverified`
//! row, and excludes the TOTAL integer `rotate_left`/`rotate_right` by their path
//! (`core::num::<impl u32>::rotate_left`). It used to test that exclusion on the
//! WHOLE rendered callee, generic arguments included, so a `Vec` whose element is a
//! sysroot fn item — `Vec::<fn(u32) -> u32 {core::num::<impl u32>::count_ones}>::
//! split_off` — or any type from a module called `num` was taken for an integer
//! method, got no row, and was admitted by the vanilla-sysroot tolerance.
//!
//! # Before (stage 1 `0.10.0+g6a3460983` and `origin/main` `0.10.0+gc2e3daed7`)
//!
//! `vec_split_off`, `vec_drain` and `vec_extend_from_within` built rc=0 with one
//! runtime-checked absent-callee row, and panic when driven past the length
//! (adversarial probes p01, p02, p08: `f(5)` on a one-element `Vec`,
//! "`at` split index (is 5) should be <= len (is 1)", "range end index 5 out of
//! range for slice of length 1"). (A user element type from a module called `num`
//! hit the same exclusion, but a user type is not foundational, so the tolerance
//! never admitted it — that shape is pinned at the recognizer only, in
//! `container_mutator_path_tests.rs`.)
//!
//! # After
//!
//! The exclusion reads the receiver SPINE (`callee_without_turbofish_args`), which no
//! generic argument can reach; the integer rotate keeps its marker (spine
//! `core::num::::rotate_left`), pinned by `int_rotate`.
//!
//! `vec_drain` pins the refusal's ERROR, not the row's NOTE (W4 salvage rebase onto
//! `origin/main` `296873da69`, 2026-09-29). The `Call::drain::panic-freedom-unverified`
//! row is still minted (`-Ztrust-verify-output=both`: `unsupported MIR
//! Call::drain::panic-freedom-unverified`, `unknown`) and it alone refuses the body:
//! main's stage 1 `0.10.0+g296873da6`, which lacks it, builds `vec_drain` rc=0. But
//! main's native full verifier now prints its OWN reason on that unknown row, and for
//! this body the reason is the lowering stopping at `.count()`'s bundled
//! `Iterator::count::{closure#0}` (an `Overflow(Add)` Assert), so the human note no
//! longer carries the row's description. `vec_split_off`/`vec_extend_from_within`
//! have no such member and keep their NOTE.

#[cfg(vec_split_off)]
pub fn vec_split_off(n: usize) -> usize {
    //[vec_split_off]~^ NOTE panic-freedom-unverified
    let mut v = vec![u32::count_ones];
    v.split_off(n).len()
}

#[cfg(vec_drain)]
pub fn vec_drain(a: usize, b: usize) -> usize {
    //[vec_drain]~^ ERROR Trust Level 0 safety verification incomplete for
    let mut v = vec![u32::count_ones];
    v.drain(a..b).count()
}

#[cfg(vec_extend_from_within)]
pub fn vec_extend_from_within(a: usize, b: usize) -> usize {
    //[vec_extend_from_within]~^ NOTE panic-freedom-unverified
    let mut v = vec![u32::count_ones];
    v.extend_from_within(a..b);
    v.len()
}

// The TOTAL integer rotate is still not a slice mutator: `forbid-output` refuses the
// `Call::rotate_left::panic-freedom-unverified` row the recognizer would mint.
//
// Trust (POISON-EVICTION-FALSE-PROOF-1, 2026-11-12): this revision used to be refused by
// ZERO-ROW-GATE. The rotate's bundled std body was evicted for its absent intrinsic, the
// call then took no row by the total-method name list, and no registry discharged it.
// The poison loop now keeps a member that a retained call still names, so the body stays
// and its `[trust-absent-callee-assumption]` row for
// `core::intrinsics::rotate_left::<u32>` is this function's one obligation. The default
// policy grades it runtime-checked and builds with this advisory. It is not a proof:
// `-Ztrust-policy=certify` refuses it. `zero_obligation_undischarged_call_fails_closed.rs`
// keeps the zero-row gate's witness, on `wrapping_pow`.
#[cfg(int_rotate)]
//[int_rotate]~v WARN Trust verification advisory for `slice_mutator_fnitem_element::int_rotate`
pub fn int_rotate(x: u32, n: u32) -> u32 {
    x.rotate_left(n)
}
