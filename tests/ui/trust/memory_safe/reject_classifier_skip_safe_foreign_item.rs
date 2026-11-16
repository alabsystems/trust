//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=memory-safe --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail
//! A LOCAL foreign item is not a local body. `memory_safe_assumption_uncharged_edges`
//! leaves a call out of its edge list when it resolves to a local item "held to the
//! same rule by induction", and it decided that with `did.is_local()` alone, which a
//! `safe fn` declared in an `extern` block of THIS crate also satisfies: a `DefId`
//! of this crate with no body, held to no rule at all.
//!
//! MEASURED on stage-1 `f2e5ebbc0f` (the r14 review's P1): the classifier skips
//! `skipped_calls_safe_foreign` (`&raw const s.a` -> `AddressOfField`), and
//! memory-safe recorded it as an authenticated `assumption:addr-of-field` row —
//! rc=0, no error, no warning. A binary whose `main` is skipped the same way and
//! passes a null pointer built rc=0 and died with SIGSEGV (rc=139) in `atoi`. The
//! same body without the raw borrow is refused (the native lane fails a
//! `hardened_unsafe_operation` row for the foreign call). The edge test now also
//! asks for a body here (`local_item_is_held_to_this_rule`).
unsafe extern "C" {
    pub safe fn atoi(p: *const u8) -> i32;
}

pub struct S {
    pub a: u32,
    pub b: u32,
}

pub fn skipped_calls_safe_foreign(s: &S, p: *const u8) -> i32 {
    //~^ ERROR Trust full verification skipped `reject_classifier_skip_safe_foreign_item::skipped_calls_safe_foreign`
    //~| NOTE `atoi` in bb
    let _q = &raw const s.a;
    atoi(p)
}

/// Control: a skipped body whose call resolves to a local function WITH a body
/// stays an admissible memory-safe assumption.
fn halve(x: u32) -> u32 {
    x / 2
}

pub fn skipped_calls_local_body(s: &S) -> u32 {
    let _q = &raw const s.a;
    halve(s.b)
}
