//@ needs-trust-verify
//@ revisions: strict default nocount
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ compile-flags: -Copt-level=0 --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@[nocount] compile-flags: -Ztrust-policy=strict
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[nocount] forbid-output: trust-std-member-runtime-check
//! The runtime-checked disposition reaches the CALLER of a conditional verdict
//! too (2026-09-29): Design 2's probes p03 and p26.
//!
//! `p` does `filter().count()` (core's `<usize as Sum>::sum::{closure#0}`, an
//! inherited `Overflow(Add)` Assert the admission lane refuses) and then
//! `a.copy_from_slice(s)`, which panics when the lengths differ; `q` calls `p`.
//! Before (stage-1 `f6773df328e`, m3 debug std and release-like std, strict and
//! default): the refusal discarded `p`'s bundle, the lowering-failure tolerance
//! fired for `p` AND for `q`, and the crate summary read `functions_verified` 3 of
//! 3 — a verify-off `main` calling `p(Tag::A, &[1, 2, 3], &mut [0u32; 2], &[1, 2,
//! 3])` panicked on the length mismatch (exit 101), as did one calling `q`.
//!
//! After: `p`'s bundle is kept and it owes `runtime_checked` rows; `q`'s bundle
//! keeps `p` (a local member) and with it the same std members, so `q` owes them
//! too. Neither is counted verified — `functions_verified` 1 of 3 (the closure).
//! Both still pass, exactly as the `count()`-free twin does: `copy_from_slice` is
//! the same `runtime_checked` sysroot call there (policy B), so the invariant
//! pinned is "never counted verified", not a refusal.
//!
//! `nocount` is the control (unchanged): `functions_verified` 0 of 2, no
//! runtime-checked std-member row.
pub enum Tag {
    A,
    B,
}

#[cfg(not(nocount))]
pub fn p(t: Tag, v: &[u32; 3], a: &mut [u32], s: &[u32]) -> u32 {
    let k = v.iter().filter(|x| **x > 1).count();
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    if k == 7 {
        return b;
    }
    a.copy_from_slice(s);
    b
}

#[cfg(nocount)]
pub fn p(t: Tag, _v: &[u32; 3], a: &mut [u32], s: &[u32]) -> u32 {
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    if b == 7 {
        return b;
    }
    a.copy_from_slice(s);
    b
}

pub fn q(t: Tag, a: &mut [u32], s: &[u32]) -> u32 {
    let r = match t {
        Tag::A => Tag::B,
        Tag::B => Tag::A,
    };
    p(r, &[1, 2, 3], a, s)
}

//[strict,default]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"std_member_runtime_check_copy_from_slice","functions_analyzed":3,"functions_verified":1,
// Re-pinned 2026-10-15 (the merge of 2026-10-14): the member's internal Assert is now
// carried by the counted panic-freedom aggregate the soundness line mints for a call into
// a bundled body (docs/KNOWN_HAZARDS.md, "A may-panic MARKER is only as good as its
// CARRIER"), one `runtime_checked` row from `trust-full-verifier`, instead of the
// per-member `trust-std-member-runtime-check` row. Same grade, same invariant: the
// function is never counted verified, the non-certify lanes warn and `certify` refuses.
//[strict,default]~? RAW Trust verification advisory for `std_member_runtime_check_copy_from_slice::p`: 1 obligation(s) were not fully verified
//[strict,default]~? RAW Trust verification advisory for `std_member_runtime_check_copy_from_slice::q`: 1 obligation(s) were not fully verified
//[nocount]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"std_member_runtime_check_copy_from_slice","functions_analyzed":2,"functions_verified":0,
