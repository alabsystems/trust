//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **I5 CONTROL 1 (a) — THE PARITY FIXTURE, CALL HALF.**
//! (`docs/design/2026-08-04-two-language-compiler-architecture.md` §7.)
//!
//! The increment's acceptance criterion, verbatim:
//!
//! > **the parity fixture** — `crate::m::f` and `Crate.m.f` must yield the SAME
//! > `DefId`; a same-module Rust `fn f` must collide with `E0428`; a
//! > different-module one must not.
//!
//! This file is the call half. Its siblings are
//! `clean_origin_parity_collision.rs` (the `E0428` half) and
//! `clean_origin_parity_no_collision.rs` (the control on that half). All three
//! must be read together: the collision half alone would go green if islands
//! declared names *badly*, and this half alone would go green if they declared
//! names *without* the kernel gate.
//!
//! ============================================================================
//! **GREEN AS OF 2026-08-19.** This fixture was RED BY DESIGN and pinned the
//! blocked state; the tilde-ERROR annotation has been DELETED, which is exactly
//! the fix its own instructions called for. It is now `run-pass`, so it does not
//! merely resolve `f` — it links and RUNS the emitted Clean-origin body.
//!
//! What unblocked it, in the order the obstacles were actually hit:
//!
//!   * `fn_sig` is now `feedable` AND HAS A FEEDER. It had been probed and
//!     reverted twice before, correctly both times: an unused `feedable` is an
//!     upstream edit for nothing. The signature became constructible only once
//!     I4 landed, because `carrier_signature_for` yields argument carriers,
//!     result carrier and arity — so `def f (a : UInt64) : UInt64` is exactly
//!     `fn(u64) -> u64`, derived from discharged total carriers rather than
//!     guessed for a HIR-less def.
//!   * the whole-crate island check runs at
//!     `Resolver::visit_ast_fragment_with_placeholders`, root `AstFragment::Crate`
//!     only — the window §6c names, one call level in from
//!     `collect_invocations`, so `rustc_expand` keeps zero Trust deps. An island
//!     introduced by a later macro expansion mints nothing and falls back to the
//!     ordinary `E0425`, which is the fail-closed answer.
//!   * the planted visibility is `Public`, NOT `Restricted(m)`. Measured:
//!     `Restricted` produced `E0603: function `f` is private` right here. It is
//!     a parity question, not a convenience one — Clean resolves from a
//!     whole-crate header-first table, so `Crate.m.f` is nameable everywhere;
//!     `Restricted(m)` would make `crate::m::f` nameable only inside `m`, and
//!     the two spellings would then disagree about WHERE THE SAME ENTITY EXISTS.
//!     That disagreement is the precise thing this fixture exists to rule out.
//!
//! THREE ICE SITES had to be guarded to get here, all the same shape: a pass
//! that walks `DefKind::Fn` and reaches `typeck`, which `span_bug!`s on a def
//! with a synthetic HIR owner and no body — `trust_verify.rs`'s backing
//! inventory, `trust_r1_oracle.rs`'s call-graph scan, and the MIR pipeline
//! itself. The third only fires with verification ON, which is why running this
//! file with verification on is a separate measurement and not a formality.
//! ============================================================================
//!
//! WHAT THE `E0425` MUST BECOME. Not a bare "not found" — ruling v7/D3: *"we
//! state the rules but if somebody doesn't follow the rules, then provide
//! feedback via the compiler on how to fix the situation (provide options)."*
//! `f` is visible in the island the user just wrote, so an unadorned "cannot
//! find function" is a lie by omission. LANDED: a refusal now carries
//! `MintRefusal::note` naming which precondition was missing (`KernelChecked` /
//! audited-empty axiom closure / total carrier) and the options for supplying
//! it, threaded onto the unresolved-path diagnostic in
//! `rustc_resolve/src/late/diagnostics.rs`. `f` here satisfies all of them, so
//! this file exercises the GRANT path; the refusal notes are exercised by
//! `crates/trust-clean-origin/tests/control_1_mint_preconditions.rs`.

mod m {
    clean {
        def f (a : UInt64) : UInt64 := a
    }
}

fn main() {
    // MUST resolve to the same `DefId` the Clean path `Crate.m.f` denotes.
    let g = crate::m::f(6u64);
    println!("{g}");
    assert_eq!(g, 6, "the emitted body must be the projection the Clean `def` denotes");
}
