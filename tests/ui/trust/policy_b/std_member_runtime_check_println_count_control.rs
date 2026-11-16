//@ needs-trust-verify
//@ revisions: strict default
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ compile-flags: -Copt-level=0 --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! CONTROL for the bundled std-member runtime-checked disposition (2026-09-29):
//! the ordinary programs the removed lowering-failure tolerance existed for still
//! build under strict and the default policy.
//!
//! Each body bundles a core member whose internal Assert the admission lane
//! refuses — `<usize as Sum>::sum::{closure#0}` behind `filter().count()`, core's
//! Unicode case-conversion lookup behind `to_uppercase` — and each used to reach
//! the policy-B tolerance on the lowering-FAILURE path. That path is gone: the
//! bundle is now kept and the refused member owes a `runtime_checked` row. The
//! Track R design's hold criterion is that none of `filter().count()` alone,
//! `to_uppercase()`, `format!("{k}")` or `println!("{}", count)` flips to REFUSED.
//! Measured check-pass with m3's debug std and with a release-like std, before
//! and after. Not counted verified either way (`functions_verified` 3 of 7 — the
//! three filter closures).
pub fn show(v: &[u32; 3]) {
    println!("{}", v.iter().filter(|x| **x > 1).count());
}

pub fn upper(s: &str) -> String {
    s.to_uppercase()
}

pub fn fmt_count(v: &[u32; 3]) -> String {
    let k = v.iter().filter(|x| **x > 1).count();
    format!("{k}")
}

pub fn count_only(v: &[u32; 3]) -> usize {
    v.iter().filter(|x| **x > 1).count()
}

// Re-pinned 2026-10-15 (the merge of 2026-10-14, DECISION_QUEUE D103(d)): 4 of 7.
// `count_only` is now counted verified: `filter().count()` over a slice iterator is decided
// total by the drive-only consumer lane (its closure's own verdict, and a counter that cannot
// pass the slice's length), so std's `Sum` body leaves the bundle and the body publishes
// `no_obligations`. `show`, `upper` and `fmt_count` stay unverified, and nothing flips to
// REFUSED, which is what this control is for.
//~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"std_member_runtime_check_println_count_control","functions_analyzed":7,"functions_verified":4,
