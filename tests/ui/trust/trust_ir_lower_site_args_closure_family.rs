//@ check-pass
//@ edition: 2024
//@ compile-flags: --crate-type=lib -Ztrust-ir-lower -Ztrust-verify=off
//@ forbid-output: final Trust-IR module validation failed
// wave-CL: closures, coroutine-closures, coroutines and coroutine
// witnesses in a call's generic args — the last 78 refusals of the
// measured `encode_site_args` vocabulary gap (Closure 46, Coroutine 24,
// CoroutineClosure 8; reports/encode-site-args-vocabulary-2026-09-01.md).
//
// A CORRECTION TO MY OWN EARLIER READING, recorded because it cost a
// cycle: two waves ago I wrote these off as "a design decision, not a
// widening", on the reasoning that a closure's args carry upvar tuples
// and witness types. They do — and every one of those is itself a TYPE,
// which `encode_ty` already recurses through. All four rustc kinds are
// `(DefId, GenericArgs)`, structurally identical to `FnDef` and `Adt`, so
// there was no identity question to settle at all. The lesson is the
// campaign's own: read the shape before classifying the work.
//
// The kind is carried EXPLICITLY (`SiteClosureKind`, a kind byte after
// tag 16) rather than inferred from the DefId, so the encoding states the
// type it means and two kinds can never digest equal. An arg the encoder
// still cannot spell declines the site exactly as before — which is now
// only `Dynamic`, the one genuine design question left (its
// `BoundExistentialPredicates` are not types).

fn takes<F>(_f: F) -> i64 {
    0
}

// A capturing CLOSURE: its args carry the upvar tuple, which is what the
// earlier reading mistook for an identity question.
pub fn call_with_closure(n: i64) -> i64 {
    let c = move |x: i64| x + n;
    takes(c)
}

// A non-capturing closure — a different upvar tuple (empty), so a
// different instantiation of the same shape.
pub fn call_with_zst_closure() -> i64 {
    takes(|x: i64| x + 1)
}

// An ASYNC block is a coroutine; passing it by value puts a
// `ty::Coroutine` (and its witness) in the call's generic args.
pub fn call_with_coroutine() -> i64 {
    takes(async { 7i64 })
}

// An async CLOSURE is a coroutine-closure — the third kind.
pub fn call_with_coroutine_closure() -> i64 {
    takes(async |x: i64| x + 1)
}

fn main() {}
