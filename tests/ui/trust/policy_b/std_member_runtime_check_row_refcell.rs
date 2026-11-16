//@ needs-trust-verify
//@ revisions: strict default certify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ compile-flags: -Copt-level=0 --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@[strict] check-pass
//@[default] check-pass
//@[certify] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The bundled std-member runtime-checked disposition publishes a ROW, and the
//! function carrying it is never counted verified (2026-09-29).
//!
//! `filter().count()` bundles core's `<usize as Sum>::sum::{closure#0}` (an
//! inherited `Overflow(Add)` Assert the admission lane refuses as
//! `AssertKindOutsideLane`) beside a `RefCell::borrow_mut`, whose own "already
//! borrowed" panic lives inside the same bundle. Before: the refusal discarded
//! the bundle, the lowering-failure tolerance reported the count's Assert as the
//! only gap, and `r` was counted verified — `functions_verified` 2 of 2 with NO
//! `runtime_checked` row (MEASURED on stage-1 `f6773df328e`, m3 debug std and
//! release-like std, strict and default); a verify-off `main` holding a `borrow()`
//! then calling `r` panicked "RefCell already borrowed" (exit 101). With m3's
//! debug std even the `count()`-free twin was counted verified (`BorrowRefMut`'s
//! own guarded Assert was tolerated the same way).
//!
//! After: the bundle is kept, each kept member owes `r` one `runtime_checked` row
//! (solver `trust-std-member-runtime-check`), and `r` is not counted verified —
//! `functions_verified` 1 of 2 (the closure). strict and default pass
//! CONDITIONALLY (policy B: rustc's own runtime checks, vanilla semantics) with
//! the advisory; `certify` refuses it by name.
use std::cell::RefCell;

pub enum Tag {
    A,
    B,
}

pub fn r(t: Tag, v: &[u32; 3], c: &RefCell<u32>) {
    let k = v.iter().filter(|x| **x > 1).count();
    let n = match t {
        Tag::A => 1usize,
        Tag::B => 2usize,
    };
    if k == 7 || n == 7 {
        return;
    }
    *c.borrow_mut() = 1;
}

// Re-pinned 2026-10-15 (the merge of 2026-10-14): the member's internal Assert is now
// carried by the counted panic-freedom aggregate the soundness line mints for a call into
// a bundled body (docs/KNOWN_HAZARDS.md, "A may-panic MARKER is only as good as its
// CARRIER"), one `runtime_checked` row from `trust-full-verifier`, instead of the
// per-member `trust-std-member-runtime-check` row. Same grade, same invariant: the
// function is never counted verified, the non-certify lanes warn and `certify` refuses.
//[strict,default]~? RAW Trust verification advisory for `std_member_runtime_check_row_refcell::r`: 1 obligation(s) were not fully verified
//[strict,default]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"std_member_runtime_check_row_refcell","functions_analyzed":2,"functions_verified":1,
//[strict,default,certify]~? RAW "outcome":"runtime_checked","solver":"trust-full-verifier"

//[certify]~? RAW error: Trust Level 0 safety verification incomplete for `std_member_runtime_check_row_refcell::r`
//[certify]~? RAW error: Trust strict verification failed for `std_member_runtime_check_row_refcell::r`
