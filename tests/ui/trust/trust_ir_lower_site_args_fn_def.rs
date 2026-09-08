//@ check-pass
//@ compile-flags: --crate-type=lib -Ztrust-ir-lower -Ztrust-verify=off
//@ forbid-output: final Trust-IR module validation failed
// wave-FD: a FN ITEM type in a call's generic args. `ty::FnDef` is a
// `DefId` plus its args — structurally identical to `ty::Adt`, which
// wave-AA had just taught the encoder to spell positionally — so this is
// that rule applied to the other shape that has it, not a new encoding
// argument. Measured as 6 of the remaining
// `Callee(MIR site args unencodable)` refusals once the ADT rows closed
// (reports/encode-site-args-vocabulary-2026-09-01.md).
//
// TAG DISCIPLINE, and the one trap here: `SiteTy::FnDef` takes tag 14,
// NOT 12. Tags 12 and 13 are permanently reserved as the *arg-stream*
// markers for a lifetime and a const (wave-AA), so a TYPE tag may never
// take either — an argument that is itself a fn item would otherwise be
// indistinguishable from a region marker inside an ADT's arg stream.

fn helper(x: i64) -> i64 {
    x + 1
}

fn generic_helper<T>(_t: T) -> i64 {
    0
}

fn takes<F>(_f: F) -> i64 {
    0
}

// `F` infers to the FN ITEM type of `helper` — a `ty::FnDef` in the
// call's generic args, which is the site that could not be pinned.
pub fn call_with_fn_item() -> i64 {
    takes(helper)
}

// A fn item that is ITSELF generic: its args ride the same positional
// encoding one level down.
pub fn call_with_generic_fn_item() -> i64 {
    takes(generic_helper::<i64>)
}

// A fn item nested inside another ADT arg — the ENCODER must carry it
// (probe-verified: zero encoder refusals for this file). The body itself
// stops later at an unrelated lane (`EnumCtor(unit payload unsupported)`
// for the `Some(..)` construction), which is the honest outcome: this
// wave widens callee-identity encoding, not enum construction.
pub fn call_with_nested_fn_item() -> i64 {
    takes(Some(helper))
}

fn main() {}
