//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//! **I8 negative — one `.clean` unit included twice.**
//! The crate's Clean environment is a single header-first batch, so a second
//! inclusion could never be right: it would either declare every name twice
//! (a Clean-level rejection) or — because `SourceMap::load_file` dedups by
//! path, giving both islands the SAME `content_span` — trip the verify
//! pass's collapsed-span ambiguity error, whose macro-oriented wording would
//! mislead. The loader therefore refuses EAGERLY, at the second item's own
//! span, pointing at the first (ruling v7/D3), with options.
//!
//! The second inclusion goes through `#[path]`, which also pins that
//! `#[path]` rides the same resolution function `mod` uses.

clean mod clean_unit_dup_shared;

#[path = "clean_unit_dup_shared.clean"]
clean mod clean_unit_dup_other;
//~^ ERROR is included twice in this crate

fn main() {}
