//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//! A `Zip` is a total receiver only when every field is a scalar or a recognized
//! slice iterator (ITER-RECV-1).
//!
//! `ty_is_slice_iterator_receiver`'s `Zip` arm required every ITERATOR-SHAPED field
//! to be slice-backed, and `ty_is_iterator_shaped` called only an ADT (or a pointer
//! to one) iterator-shaped. A generic inner `&mut I` reaches the bridge as
//! `Ref { Unsupported }`, so it was skipped as "scalar state", and the `into_iter`/
//! `next` calls below were summarized as total: both functions read `unreach
//! proved` only and were Clean-kernel certified. Measured 2026-10-04 on the BEFORE
//! compiler: this file's functions built as a certify-policy rlib (exit 0), linked
//! into a `-Ztrust-verify=off` binary and driven with an inner `Iterator` whose
//! second `next` indexes a 1-entry table, `zip_count` panics `index out of bounds:
//! the len is 1 but the index is 1` (exit 101).
//!
//! BEFORE (stage 1 of `38e6c69b1c`, `scratchpad/stage1-w11fix`, 2026-10-04; each
//! revision's flags with `--emit=metadata`): both revisions built exit 0 with no
//! Trust diagnostic. The annotations below did not fire.
//!
//! AFTER (predicted, then measured): every `Zip` field must be an `Int`,
//! `PtrSizedInt` or `Bool`, or a recognized slice iterator, so `&mut I` fails the
//! arm and the calls fall to the absent-callee path. The annotations are what the
//! BEFORE compiler prints for a twin of this file whose inner is
//! `Take<&'b mut I>` (an ADT, which the old arm already refused, still generic over
//! `I`): `[trust-absent-callee-assumption]` on the `Zip`'s `into_iter`/`next`,
//! default a WARN and an ERROR per function, certify two ERRORs.
//! Measured on the stage 1 of `4463aeeb6d` (2026-10-04): every annotation below fires in
//! every revision and nothing else is reported. `zip_count` and `zip_first` gain a
//! runtime-checked row; the two-slice controls still read `unreach proved` only.
//!
//! The controls carry no annotation and read `unreach proved` in both revisions,
//! BEFORE and in the twin: a `Zip` of two slice iterators, as a receiver and as
//! `a.iter().zip(b.iter())` in a loop.

pub fn zip_count<'a, 'b, I: Iterator<Item = u8>>(z: core::iter::Zip<core::slice::Iter<'a, u8>, &'b mut I>) -> usize {
    //[default]~^ WARN Trust Level 0 safety verification incomplete for `zip_with_generic_inner_is_not_total::zip_count`
    //[default]~^^ ERROR Trust strict verification failed for `zip_with_generic_inner_is_not_total::zip_count`
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `zip_with_generic_inner_is_not_total::zip_count`
    //[certify]~^^^^ ERROR Trust strict verification failed for `zip_with_generic_inner_is_not_total::zip_count`
    let mut n = 0usize;
    for _p in z {
        n = n.wrapping_add(1);
    }
    n
}

pub fn zip_first<'a, 'b, I: Iterator<Item = u8>>(mut z: core::iter::Zip<core::slice::Iter<'a, u8>, &'b mut I>) -> u8 {
    //[default]~^ WARN Trust Level 0 safety verification incomplete for `zip_with_generic_inner_is_not_total::zip_first`
    //[default]~^^ ERROR Trust strict verification failed for `zip_with_generic_inner_is_not_total::zip_first`
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `zip_with_generic_inner_is_not_total::zip_first`
    //[certify]~^^^^ ERROR Trust strict verification failed for `zip_with_generic_inner_is_not_total::zip_first`
    match z.next() {
        Some((a, _b)) => *a,
        None => 0,
    }
}

pub fn zip_two_slices<'a>(mut z: core::iter::Zip<core::slice::Iter<'a, u8>, core::slice::Iter<'a, u8>>) -> u8 {
    match z.next() {
        Some((a, _b)) => *a,
        None => 0,
    }
}

pub fn zip_slices_loop(a: &[u8], b: &[u8]) -> usize {
    let mut n = 0usize;
    for (_x, _y) in a.iter().zip(b.iter()) {
        n = n.wrapping_add(1);
    }
    n
}
