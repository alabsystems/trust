//@ check-pass
//@ compile-flags: --crate-type=lib -Ztrust-ir-lower -Ztrust-verify=off
//@ forbid-output: final Trust-IR module validation failed
// wave-DY: trait objects in a call's generic args — the LAST row of the
// measured `encode_site_args` vocabulary gap
// (reports/encode-site-args-vocabulary-2026-09-01.md), and the only one
// that was genuinely a design question rather than a missing arm: a
// `ty::Dynamic`'s payload is not types but PREDICATES.
//
// Decomposed, each predicate is still made of what this encoder already
// spells: a principal trait is a `DefId` + args, a projection adds a term
// (a type or a const), and an auto trait is a bare `DefId`. All three are
// identity-bearing, so all three are framed — an object that differs only
// in an auto trait, or only in a projected associated type, is a
// different type and must not digest equal. The LIST ORDER is preserved
// too: rustc keeps an object's predicates canonical, so order carries
// identity.
//
// The object's REGION is erased, and each predicate's binder with it, on
// the standing argument every other binder in this encoder rests on
// (wave-VALR): trust-ir has no lifetime sort, so a region cannot survive
// into any mapped type under ANY treatment, and the comparator erases
// regions on both sides before pinning callee identity.
//
// Tag 17 in both lineage encoders, appended: 12/13 remain the arg-stream
// lifetime/const markers, 14 fn item, 15 fn pointer, 16 closure family.

fn takes<T: ?Sized>(_t: &T) -> i64 {
    0
}

pub trait Speak {
    fn speak(&self) -> i64;
}

pub trait Produce {
    type Item;
    fn make(&self) -> Self::Item;
}

// A bare principal trait.
pub fn call_with_dyn(d: &dyn Speak) -> i64 {
    takes(d)
}

// Principal + AUTO TRAIT: the auto trait is part of the identity, so it
// is framed rather than dropped.
pub fn call_with_dyn_send(d: &(dyn Speak + Send)) -> i64 {
    takes(d)
}

// A PROJECTION predicate — `Produce<Item = i64>` binds an associated
// type, which rides the encoding as a term.
pub fn call_with_dyn_projection(d: &dyn Produce<Item = i64>) -> i64 {
    takes(d)
}

// A trait object beside TWO auto traits — a longer predicate list, so a
// different identity. Order is preserved by the encoding because rustc
// keeps the list canonical.
pub fn call_with_two_autos(d: &(dyn Speak + Send + Sync)) -> i64 {
    takes(d)
}

fn main() {}
