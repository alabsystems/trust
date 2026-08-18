//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-pass
//@ dont-check-compiler-stderr
//! I1 — the failing test, written first (decision of record
//! `docs/design/2026-08-04-two-language-compiler-architecture.md` §6).
//!
//! WHAT THIS PINS: §4.1.1's "all declaration headers are collected before any
//! body is elaborated, so resolution is source-order-independent". An EARLIER
//! `clean { }` island names a `def` and a `theorem` that are declared in a
//! LATER island. In Rust, `mod cites_later` before `mod declared_later` is not
//! a forward reference at all — items are resolved from a whole-crate symbol
//! table. Clean is the other authoritative language, so it gets the same
//! treatment, and the two spellings must not disagree about which names exist.
//!
//! ============================================================================
//! THIS FIXTURE WAS WRITTEN RED, AS THE ACCEPTANCE CRITERION FOR I1, AND IS NOW
//! **GREEN**. Header-first checking landed: `declare_all` elaborates every
//! declaration's signature across every island before any body is elaborated,
//! so `later_always` and `later_always_refl` are in scope when the earlier
//! island is checked, and the bodies are then registered in dependency order so
//! each one is checked against a REAL kernel-checked definition.
//!
//! THE PROHIBITIONS STILL BIND. Do not "keep" it green by weakening the
//! directives, by deleting it, or by moving `mod declared_later` above
//! `mod cites_later` — reordering the modules makes it pass for the reason it
//! was written to rule out, and makes it prove nothing. And it is still not
//! sufficient on its own: see the control note at the bottom.
//! ============================================================================
//!
//! WHY IT FAILED BEFORE I1 — the mechanism, read out of the code rather than
//! assumed. Retained because it is what the fixture discriminates against, and
//! a regression would look exactly like this again:
//!
//!   * `trust_check_clean_islands` collects every `ItemKind::CleanIsland` span
//!     and sorts it by `(span.lo(), span.hi())`
//!     (`compiler/rustc_mir_transform/src/trust_verify.rs:7253`);
//!   * it then feeds each island's TEXT, one island at a time, into a single
//!     stateful `CleanIslandSession::check(&text)`
//!     (`trust_verify.rs:7307` -> `crates/trust-certify/src/clean_island.rs:716`);
//!   * inside that, each declaration is elaborated AND kernel-registered by one
//!     atomic `elaborate_decl_and_register_with_context_and_warning` call, in
//!     parse order (`clean_island.rs:1031-1034`). There is no declare/elaborate
//!     seam anywhere on this path.
//!
//! So when the first island is checked, `later_always` and `later_always_refl`
//! are simply not in the `Environment`, and the kernel rejects with
//!
//!     error: Clean island declaration rejected: UnknownIdent("later_always")
//!
//! (`clean_island.rs:1074`, `{err:?}`-formatted). Source order was load-bearing;
//! it is not any more. `declare_all` now precedes `elaborate_bodies` across the
//! WHOLE crate — see `crates/trust-certify/src/clean_island_batch.rs` and
//! `CleanIslandSession::check_all`, which the driver calls once with every
//! island's text instead of feeding them one at a time.
//!
//! The proof term is a forward reference on purpose, and so is the statement:
//!
//!   * `later_always_refl` appears in a VALUE position, where auto-bound
//!     implicits are disabled (`in_term_body`,
//!     `clean-elab/src/infer/elab_core.rs:1252-1284`), so an unresolved name is
//!     a loud `unknown identifier` and cannot be silently absorbed;
//!   * `later_always` appears in the STATEMENT, which is a header position
//!     where `relaxedAutoImplicit` (on by default) WOULD quietly turn an
//!     unresolved name into an implicit binder. `set_option autoImplicit false`
//!     is therefore mandatory here, not decorative: without it this fixture
//!     could go green while the header graph silently invented a binder instead
//!     of resolving a cross-island dependency. An I1 graph builder has the same
//!     exposure and needs the same guard.
//!
//! DELIBERATELY NOT EXERCISED: `namespace` / `open` / `set_option` state that
//! straddles an island boundary. `FileContext` scoping stays lexical even in a
//! source-order-independent world, and replaying bodies against a snapshotted
//! context is a distinct hazard (depth-keyed `local instance` retirement in
//! particular). It deserves its own fixture; conflating it with this one would
//! make a failure ambiguous.
//!
//! THIS FIXTURE ALONE IS NOT SUFFICIENT. It would also go green if I1 simply
//! stopped kernel-checking islands. Its control is
//! `clean_symbol_graph_forward_reference_cycle.rs`, which must stay REJECTED.
//! Read that file before believing this one.

mod cites_later {
    clean {
        set_option autoImplicit false

        theorem earlier_uses_later (p : Nat -> Prop) : later_always p = later_always p :=
            later_always_refl p
    }
}

mod declared_later {
    clean {
        def later_always (p : Nat -> Prop) : Prop := forall (n : Nat), p n

        theorem later_always_refl (p : Nat -> Prop) : later_always p = later_always p := rfl
    }
}

fn main() {}
