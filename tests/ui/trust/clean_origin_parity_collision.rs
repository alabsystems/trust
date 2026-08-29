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
//! THE FLIP HAPPENED. THIS FIXTURE NOW PINS THE `E0428`.
//!
//! It used to carry `check-pass` and say so: the island declared no children,
//! nothing was planted into the module's value namespace, and there was nothing
//! for `pub fn f` to collide with — WRONG-GREEN BY DESIGN, with the instruction
//! "WHEN I5 LANDS, THIS FILE MUST FLIP TO check-fail WITH E0428".
//!
//! 7b5c5535b3 ("the mint is wired") landed that. MEASURED 2026-08-19: the
//! `E0428` fires, and its secondary span reads "previous definition of the
//! value `f` here" pointing at the `def f` line inside the island. **The
//! acceptance criterion this half owns is met.** The `check-pass` directive is
//! therefore gone, and the collision is pinned positively — a compiler that
//! stopped planting the child would fail this file rather than quietly pass it.
//!
//! The mechanism, as predicted and now exercised: the mint calls
//! `Resolver::define_local` (`rustc_resolve/src/build_reduced_graph.rs`,
//! `trust_mint_clean_island_decls`), which routes through
//! `plant_decl_into_local_module` where duplicate detection lives — and only
//! because the child is planted into the ENCLOSING MODULE rather than under the
//! island's own def. That same placement is what makes the `DefPath` `m::f`
//! line up with the Clean path `Crate.m.f`.
//!
//! Do not keep this file green by deleting the Rust `fn f`, by renaming either
//! `f`, or by moving one of them to another module — every one of those makes
//! the fixture pass for the reason it was written to rule out.
//!
//! THE CALL IN `main` IS NOT THIS FIXTURE'S SUBJECT, and it now pins nothing.
//! It used to carry a privacy expectation (`E0603`) and a comptime-context one
//! ("comptime fns can only be called at compile time"), on the strength of a
//! mint that planted its decls module-private and always-const. The mint now
//! plants `Visibility::Public` and `Constness::Const { always: false }`
//! (`rustc_resolve/src/build_reduced_graph.rs`,
//! `trust_mint_clean_island_decls`), so neither diagnostic exists any more.
//! MEASURED 2026-08-22 on stage2 ec4783d80 — here, where the `E0428` is the
//! only diagnostic emitted, and on the same island with the colliding `fn f`
//! removed, where the call compiles clean. Those two mint decisions are shared
//! with `clean_origin_call_parity.rs`, and that file owns them.
//!
//! Never spell the annotation sigil literally in this prose: compiletest scans
//! EVERY line with a bare regex (`src/tools/compiletest/src/errors.rs:141`), so
//! a quoted sigil in a comment becomes a real, unsatisfiable expectation.
//! ============================================================================

mod m {
    clean {
        def f (a : UInt64) : UInt64 := a
    }

    // MUST collide with the Clean-origin `f` above. It does.
    pub fn f(a: u64) -> u64 { a }
    //~^ ERROR the name `f` is defined multiple times
}

fn main() {
    let _ = m::f(1);
}
