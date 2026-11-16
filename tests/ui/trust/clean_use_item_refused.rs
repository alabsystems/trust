//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE

//! **Ruling R1, candidate (c): `clean use <crate>;` is refused by name.**
//!
//! R1 chose `by <crate>.<theorem>` over two alternatives. Candidate (b), the
//! Rust path separator, is refused at the citation parser
//! (`clean_citation_rust_path_spelling_refused.rs`). Candidate (c) — an item
//! that brings a dependency's Clean declarations into scope under BARE names —
//! was, until this fixture, refused only as the generic "expected item", which
//! says nothing about the rule and offers nothing to do instead.
//!
//! The substance of the refusal, not just its wording: a bare name in scope
//! makes "add a theorem to a library" a breaking change for every dependent,
//! and puts a dependency's names back into the space an ordinary clause
//! identifier resolves in — the capture family the round-2 clause guard closed
//! and that `ClauseIdentifierDisposition` gates. See
//! `docs/design-notes/2026-09-18-cross-crate-proof-citation.md` §10.
//!
//! Vanilla Rust rejects an item beginning `ident use`, so claiming this shape
//! changes the meaning of no valid Rust program.

clean use spec;
//~^ ERROR `clean use` is not a Trust item

fn main() {}
