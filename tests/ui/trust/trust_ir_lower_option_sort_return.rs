//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off --crate-type=lib
// wave-OS1a: the one-sort agreement's first increment
// (docs/design/2026-08-31-os1-option-one-sort-entry.md). A body whose
// declared return is an opaque-lane Option and whose DIRECT TAIL is a bare
// `None` ctor — with the whole-body witness that NO other expr carries the
// return type and NO explicit `return` exists — signs the return at the
// shared opaque-alias sort and mints the pinned tail ctor AT that sort:
// ONE spelling at both ends, which is what #189 demands. `param_opaque`
// keeps the body symbolic (never spliced/sampled; the MIR oracle's
// Option-typed signature is incomparable by construction — a skip class,
// not a divergence channel). Any fence miss keeps the ABI-lie refusal
// verbatim (see `some_tail` below).

pub struct It;
impl Iterator for It {
    type Item = std::vec::IntoIter<String>;
    // The measured corpus shape (issue-42552's `next`).
    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}

// NEGATIVE — a `Some(..)` tail over an OPAQUE payload is not the fenced
// shape (its payload value would need the sort minting a later increment
// designs); the ABI-lie refusal stands and this body must NOT lower.
// (A CONCRETE registrable payload — `Option<IntoIter<String>>` — is not in
// the ABI-lie population at all and lowers first-class; measured while
// writing this fixture.)
pub fn some_tail(b: bool) -> Option<impl std::fmt::Debug> {
    if b { Some(7i64) } else { None }
}
