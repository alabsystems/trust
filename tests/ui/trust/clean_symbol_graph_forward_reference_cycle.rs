//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//@ dont-check-compiler-stderr
//! I1 — THE CONTROL THAT MUST FAIL, TODAY AND FOREVER (decision of record
//! `docs/design/2026-08-04-two-language-compiler-architecture.md` §6).
//!
//! This is the file that makes `clean_symbol_graph_forward_reference.rs` mean
//! something. That fixture asks the compiler to accept a name declared in a
//! LATER island. The cheapest way to make it pass is to stop checking, or to
//! seed the environment with header-shaped constants that have no bodies. Both
//! shortcuts also accept THIS file. So: if the forward-reference fixture ever
//! goes green while this one does too, I1 has not landed — it has been faked,
//! and the compiler now proves `0 = 1`.
//!
//! WHAT THIS PINS: a two-phase (`declare_all` then `elaborate_bodies`)
//! environment must break genuine cycles. Two properties, one file:
//!
//! (A) THE PROOF CYCLE — the soundness control, and the sharp one.
//!     `false_via_a` and `false_via_b` state the SAME false proposition and
//!     each is "proved" by the other. If the declare phase installs a header as
//!     a typed constant with no body, that constant IS an assumption, and both
//!     bodies then typecheck against each other. The environment ends up
//!     holding a kernel-registered proof of `0 = 1`, from which everything
//!     follows. This is exactly the trap the binding rule guards:
//!
//!         a parse-time (or declare-time) success must NEVER imply a
//!         kernel-checked declaration.
//!
//!     Whatever `declare_all` puts in the environment must be invisible to
//!     `check_citation*`, `environment()`, `island_definition_value` and
//!     `unfold_island_application`, and must never be usable as a proof term.
//!     Note also that synthesizing the header as an `axiom`/valueless `opaque`
//!     stub is independently barred: `strict_leaf_policy_error`
//!     (`crates/trust-certify/src/clean_island.rs:912-922`) rejects both.
//!
//! (B) THE DEFINITIONAL CYCLE — the totality control.
//!     `ping` and `pong` are mutually recursive with no decreasing measure.
//!     Their HEADERS are both `Nat -> Nat` and are perfectly consistent; the
//!     cycle exists only in the bodies. That is the point: it proves
//!     `elaborate_bodies` still checks after `declare_all` succeeded, rather
//!     than trusting a header graph that saw nothing wrong.
//!
//! A HANG IS ALSO A FAILURE OF THIS CONTROL. If the cycle is discovered by the
//! kernel diverging in `whnf` rather than by the graph refusing to schedule it,
//! this test stops being a rejection and becomes a timeout. The dependency
//! graph must detect the cycle structurally, before elaboration.
//!
//! WHY IT FAILS, AND WHY THE REASON IS NOW THE RIGHT ONE:
//! before I1 the rejection was the ordinary source-order one — the earlier
//! island was checked against a session that had never seen the later island,
//! so all four declarations failed as
//! `Clean island declaration rejected: UnknownIdent(...)`. That was a REJECTION
//! FOR THE WRONG REASON: it said "I have not read that file yet", not "these
//! declarations justify each other".
//!
//! I1 landed header-first checking, so both names are in scope and the cycle is
//! what is left. The rejection is now the cycle, named, with both island spans:
//!
//!     error: Clean declarations form a dependency cycle: false_via_a -> false_via_b -> false_via_a
//!       --> ...:78:9                                    <- the earlier island
//!     ...
//!     88 |         theorem false_via_b : 0 = 1 := false_via_a
//!        |         ------- `false_via_b` closes the cycle    <- the later island
//!
//! and the same for `ping -> pong -> ping`. It is found STRUCTURALLY, before
//! any body is registered, so the kernel is never handed a mutual proof — which
//! is also why this cannot degrade into the hang described above.
//!
//! THE INLINE ANNOTATIONS ARE THE POINT. They are what stops this file from
//! silently reverting to a rejection for the wrong reason: `check-fail` alone is
//! satisfied by ANY error, including the four unresolved-name errors that would
//! come back the moment header-first checking broke. Do not remove them, and do
//! not re-add `dont-require-annotations: ERROR`.
//!
//! `set_option autoImplicit false` is present so that a future header-graph
//! builder cannot make this file "resolve" by absorbing `false_via_b` / `pong`
//! into implicit binders instead of reporting a cross-island dependency
//! (`relaxedAutoImplicit` is on by default and accepts any alphabetic name).

mod earlier {
    clean {
        set_option autoImplicit false

        theorem false_via_a : 0 = 1 := false_via_b

        def ping (n : Nat) : Nat := pong n
    }
    //~^^^^ ERROR Clean declarations form a dependency cycle: false_via_a -> false_via_b
    //~^^^ ERROR Clean declarations form a dependency cycle: ping -> pong -> ping
}

// NOTE on annotation placement, learned the hard way: tilde-comment markers
// (slash-slash-tilde) must sit OUTSIDE
// the `clean { }` braces. `//` is NOT a Clean comment (Lean uses `--`), so the lexer
// reads it as the subtype separator and the annotation becomes ISLAND SOURCE — which
// then fails to parse and emits a THIRD, unannotated error, failing the fixture under
// compiletest. The sibling `clean_symbol_graph_axiom_disclosed.rs` gets this right;
// this file did not until it was measured.

mod later {
    clean {
        set_option autoImplicit false

        theorem false_via_b : 0 = 1 := false_via_a

        def pong (n : Nat) : Nat := ping n
    }
}

fn main() {}
