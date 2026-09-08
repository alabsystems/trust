//@ check-pass
//@ compile-flags: --crate-type=lib -Ztrust-ir-lower -Ztrust-verify=off
//@ forbid-output: final Trust-IR module validation failed
// wave-FP: a FN POINTER type in a call's generic args — the last row of
// the measured `encode_site_args` vocabulary gap that is a WIDENING
// rather than a design decision
// (reports/encode-site-args-vocabulary-2026-09-01.md). What remains after
// this wave — Dynamic, Closure, Coroutine, CoroutineClosure — all carry
// def-ids plus their own args (upvar tuples, witness types), which is a
// design question, not a missing arm.
//
// TWO ENCODING DECISIONS, both stated rather than assumed:
//
// 1. THE BINDER IS ERASED before encoding
//    (`instantiate_bound_regions_with_erased`, the wave-VALR treatment
//    this file already applies to fn-pointer signatures elsewhere).
//    trust-ir carries no lifetime sort, so a late-bound region cannot
//    survive into any mapped type under ANY treatment; the comparator
//    erases regions on both sides before pinning identity, so the
//    erasure is the honest normalization and the rebuild uses a dummy
//    binder.
//
// 2. THE HEADER IS STORED AS OBSERVABLE FACTS — the ABI as its stable
//    `ExternAbi` token string (`FromStr` round-trips it), plus safety,
//    C-variadicity and the splatted-arg index — NOT as rustc's packed
//    `flags` byte, which is an internal encoding an upstream merge could
//    renumber under a PINNED lineage digest. All of it is framed, so two
//    fn pointers differing only in ABI or safety cannot digest equal.
//
// Tag 15 in both lineage encoders, appended: 12/13 stay reserved as the
// arg-stream lifetime/const markers and 14 is wave-FD's fn item.

fn takes<F>(_f: F) -> i64 {
    0
}

// `F` is a plain safe fn pointer.
pub fn call_with_fn_ptr(f: fn(i64) -> i64) -> i64 {
    takes(f)
}

// An UNSAFE fn pointer: the safety flag must ride the encoding, since it
// is part of the type's identity.
pub fn call_with_unsafe_fn_ptr(f: unsafe fn(i64) -> i64) -> i64 {
    takes(f)
}

// A non-Rust ABI: the token string is what makes this distinguishable.
pub fn call_with_extern_fn_ptr(f: extern "C" fn(i64) -> i64) -> i64 {
    takes(f)
}

// A fn pointer whose own signature mentions a reference — the binder this
// wave erases is exactly the one such a signature introduces.
pub fn call_with_ref_sig_fn_ptr(f: fn(&i64) -> i64) -> i64 {
    takes(f)
}

fn main() {}
