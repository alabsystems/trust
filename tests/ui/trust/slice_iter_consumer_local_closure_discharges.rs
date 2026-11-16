//@ revisions: default strict certify memory_safe
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json
//@ compile-flags: -Copt-level=0 --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memory_safe] compile-flags: -Ztrust-policy=memory-safe
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: HELP
//@ forbid-output: native-verification-gap
//@ forbid-output: "outcome":"unknown"
//@ forbid-output: this function has no obligation of its own
//! ZERO-ROW-GATE recovery item 2, SLICE-ITER-CONSUMER (docs/DECISION_QUEUE.md;
//! docs/TCB.md "SLICE_ITER_CONSUMER"): a body whose only call is
//! `<core::slice::Iter<'_, T> as Iterator>::all` or `::fold` with a LOCAL closure
//! that is already registered panic-free publishes the proved `no_obligations` row,
//! and every fail-closed lane accepts it.
//!
//! BEFORE (origin/main `20665862d7`): each caller below published one `unknown`
//! `native-verification-gap` row and the default, strict and certify lanes refused
//! it ("this function has no obligation of its own, but it is not vacuously
//! verified"): the consumer call was the one undischarged callee (`arm=NONE`). These
//! are the six ALab bodies' shapes (a3d_solve `fit_optimality::inputs_finite` and
//! its `{closure#1}`, astream_effects `demo::oracle`).
//!
//! AFTER: `collect_slice_iter_consumer_total_calls` admits the call from `TyCtxt`
//! (the `Iterator` trait and the `SliceIter` ADT by diagnostic item in a resident
//! sysroot crate, the resolved impl method, no drop glue, a local closure in the
//! registry), so the call gate and the publisher both say vacuously clean. The
//! refusals are pinned by `slice_iter_consumer_refusals.rs`.

pub fn all_finite(xs: &[f64]) -> bool {
    xs.iter().all(|x| x.is_finite())
}

pub fn array_all_finite(center: [f64; 3]) -> bool {
    center.iter().all(|v| v.is_finite())
}

// The nested shape: the outer closure's only call is the inner consumer, so the
// outer closure is itself a zero-row body that this lane must admit first.
pub fn rows_finite(kept: &[[f64; 3]]) -> bool {
    kept.iter().all(|p| p.iter().all(|v| v.is_finite()))
}

// `(&mut it).all(..)` autorefs: `Self` is still `slice::Iter`, the same call.
pub fn by_ref_all(xs: &[f64]) -> bool {
    let mut it = xs.iter();
    (&mut it).all(|x| x.is_finite())
}

pub fn fold_hash(bytes: &[u8], head: u64) -> u64 {
    bytes.iter().fold(head, |d, &b| d.wrapping_mul(1_099_511_628_211).wrapping_add(b as u64))
}
