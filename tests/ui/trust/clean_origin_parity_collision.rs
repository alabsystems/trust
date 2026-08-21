//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **I5 CONTROL 1 (b) — THE PARITY FIXTURE, COLLISION HALF.**
//! (`docs/design/2026-08-04-two-language-compiler-architecture.md` §7.)
//!
//! The acceptance criterion this half owns:
//!
//! > a same-module Rust `fn f` must collide with `E0428`
//!
//! Why this is the sharp half. Parity is not "the name resolves"; it is "the
//! two spellings denote the SAME entity". The observable consequence of
//! sameness, inside one module, is a duplicate-definition error. If a Clean
//! `def f` and a Rust `fn f` can coexist in one module, then `crate::m::f` and
//! `Crate.m.f` are two different things wearing one name — and whichever one a
//! call site got would be an accident of lookup order.
//!
//! ============================================================================
//! **FLIPPED 2026-08-19.** This file was `check-pass` and WRONG-GREEN BY DESIGN:
//! it passed precisely because the defect was live. It is now `check-fail` with
//! the `E0428` its own instructions demanded, and the Rust `fn f` was NOT
//! deleted, NOT renamed, and NOT moved to another module — every one of those
//! would have made it pass for the reason it was written to rule out.
//!
//! The collision cost no extra code, exactly as predicted: `define_local`
//! routes through the duplicate detection that already exists, and it fires
//! only because the child is planted into the ENCLOSING module rather than
//! under the island's own def. `def_collector` calls the mint BEFORE
//! `with_owner` for that reason — `with_owner_tables` swaps `current_owner`, so
//! a child minted inside would be filed under the island's table, invisible to
//! the module, silently failing parity and never tripping `E0428` at all. One
//! placement decision satisfies both halves of parity, and getting it wrong
//! breaks both silently.
//! ============================================================================

mod m {
    clean {
        def f (a : UInt64) : UInt64 := a
    }

    // Collides with the Clean-origin `f` above, which I5 mints into THIS module.
    pub fn f(a: u64) -> u64 { a }
    //~^ ERROR the name `f` is defined multiple times
}

fn main() {
    let _ = m::f(1);
}
