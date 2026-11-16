//@ revisions: default strict certify memsafe
//@ needs-trust-verify
//@ edition: 2021
//@ aux-crate: alloc=alloc.rs
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memsafe] compile-flags: -Ztrust-policy=memory-safe
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The check-fail twin of `seq_requires_resident_alloc_run.rs` (SEQ-RESIDENCY-1): a
//! `Vec` that carries std's diagnostic item, from a dependency named `alloc` in a
//! no_std graph, is not std's `Vec`. The two `w.len()` in `h` are not one length, and
//! `w.len() - 1` is not proved; likewise the view in `view` and the index in `k`.
//!
//! BEFORE (the stage 1 of `ee3f51541d`, whose compiler and trust-vcgen equal
//! `integ/wave12`'s `fc62d8ba05`, 2026-10-04; each revision's flags with
//! `--emit=metadata`): every revision exits 1, but only on each call's absent-callee
//! row (`assert`, runtime-checked; `auxiliary/alloc.rs` is built verify-off). `h`'s
//! and `view`'s `overflow:sub` rows read proved (`1 certified`, Clean-kernel) with
//! `TRUST_ELIDE_DEBUG=1` printing `elided 1 kernel-certified overflow checks` in each,
//! and `k`'s `slice` row read proved (ay-in-process). Each Level 0 diagnostic counted 1
//! obligation not proved (a warning except under certify), and the strict ones counted
//! 1 not fully verified for `h` and `view` (2 for `k`, whose ay proof is not
//! Certified), so in every revision each function had an annotation below unmatched.
//!
//! AFTER (measured on the stage 1 built from this change): the forged type lowers to a
//! stamped `Ty::Adt`, the deref hop and the view equation are refused, and the
//! `overflow:sub`/`slice` row reads failed (ay-in-process; memory-safe: skipped), so
//! each count is 2 and nothing is elided.
#![no_std]

extern crate alloc;

pub fn h(w: &alloc::vec::Vec<u32>) -> usize {
    //[default,strict,certify]~^ ERROR Trust Level 0 safety verification incomplete for `seq_requires_resident_alloc::h`: 2 obligation(s) were not proved
    //[default,strict,certify]~^^ ERROR Trust strict verification failed for `seq_requires_resident_alloc::h`: 2 obligation(s) were not fully verified
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `seq_requires_resident_alloc::h`: 2 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `seq_requires_resident_alloc::h`
    if w.len() == 0 {
        return 0;
    }
    w.len() - 1
}

// The view and index shapes ride the same forged `Ty::Seq`.
pub fn view(w: &alloc::vec::Vec<u32>) -> usize {
    //[default,strict,certify]~^ ERROR Trust Level 0 safety verification incomplete for `seq_requires_resident_alloc::view`: 2 obligation(s) were not proved
    //[default,strict,certify]~^^ ERROR Trust strict verification failed for `seq_requires_resident_alloc::view`: 2 obligation(s) were not fully verified
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `seq_requires_resident_alloc::view`: 2 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `seq_requires_resident_alloc::view`
    if w.len() == 0 {
        return 0;
    }
    let s: &[u32] = w;
    s.len() - 1
}

pub fn k(w: &alloc::vec::Vec<u32>, i: usize) -> u32 {
    //[default,strict,certify]~^ ERROR Trust Level 0 safety verification incomplete for `seq_requires_resident_alloc::k`: 2 obligation(s) were not proved
    //[default,strict,certify]~^^ ERROR Trust strict verification failed for `seq_requires_resident_alloc::k`: 2 obligation(s) were not fully verified
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `seq_requires_resident_alloc::k`: 2 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `seq_requires_resident_alloc::k`
    if i < w.len() { w[i] } else { 0 }
}
