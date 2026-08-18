//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! I1 — the axiom-disclosure pair, HALF ONE (assumption-bearing). Its control
//! is `clean_symbol_graph_axiom_disclosed_control.rs`, which proves the SAME
//! proposition with a real term and must report `Certified`. Read both or
//! neither: a disclosure that produces the same output as a real proof is
//! inert, and an inert disclosure is worse than none because it reads as a
//! safeguard.
//!
//! WHAT THIS PINS (binding soundness rule, may not be weakened):
//!
//!     A theorem proved through an `axiom` / `sorry` / `trusted` is
//!     ASSUMPTION-BEARING. It must NEVER report `Certified`, and the
//!     assumptions must be disclosed BY NAME.
//!
//! `le_self` is TRUE and easy to prove — the control does prove it. Here it is
//! discharged by `assumed_le`, a user assumption. Nothing about the proposition
//! is in doubt; what is in doubt is whether the compiler will tell you that its
//! strongest verdict was stamped on a term whose justification bottoms out in
//! something a user asserted. This is the cleanest false-`Certified` available
//! (decision of record §4), which is why it gets a dedicated fixture instead of
//! a line in someone's summary.
//!
//! HOW THE PAIR DIFFERS TODAY — the thing that makes the disclosure non-inert.
//! The two files produce structurally different output, not the same row with a
//! different adjective:
//!
//!   THIS FILE          : 2 ERROR rows, `assumed_le` named in one of them,
//!                        and ZERO `Clean island kernel-checked: N
//!                        declaration(s) registered (...)` note rows.
//!   THE CONTROL        : ZERO error rows, and exactly ONE
//!                        `... registered (le_self)` note row.
//!
//! That note is today's `Certified` signal, and the link is mechanical, not
//! editorial: the note is emitted only when the island was not rejected
//! (`compiler/rustc_mir_transform/src/trust_verify.rs:7324-7335`), and a
//! `theorem` leaf survives rejection only when
//! `cert_meter::grade(env, ty, proof)` returns `Grade::Certified`
//! (`crates/trust-certify/src/clean_island.rs:975-995`).
//!
//! MECHANISM TODAY. Two independent refusals fire, and both are wanted:
//!
//!   1. `strict_leaf_policy_error` rejects `ElabResult::Axiom` outright
//!      (`clean_island.rs:912-922`) — strict islands do not host assumptions.
//!   2. The theorem is still elaborated (the axiom IS registered in the
//!      environment even though its policy check failed), and
//!      `cert_meter::grade` returns
//!      `Grade::Trusted { closure: ["assumed_le"] }` via
//!      `CertificationIssue::NonFoundationalAxiom`
//!      (`crates/trust-cert-meter/src/lib.rs:57-82`). The refusal prints the
//!      closure, so the assumption is disclosed by name. THAT NAME IS THE
//!      POINT OF THIS FIXTURE — an anonymous "depends on trust provenance"
//!      would not satisfy the rule.
//!
//! IF I1 CHANGES THE DISPOSITION, CHANGE IT DELIBERATELY. The decision of
//! record has `KernelStatus` carry an `AxiomClosure`, and I5 mints a `DefId`
//! only for a decl that is `KernelChecked` with an EMPTY closure — which
//! implies an axiom-bearing decl may one day be admitted (as PROOF-only,
//! assumption-bearing) rather than rejected. If that lands, this fixture flips
//! to the `check-pass` directive with an inline NOTE annotation naming
//! `assumed_le` and stating the
//! row is assumption-bearing. That flip is a reviewed change of disposition and
//! belongs in the commit that makes it, with the reasoning attached.
//!
//! WHAT MAY NEVER CHANGE, under any disposition:
//!   * `assumed_le` is named in the output;
//!   * no row for `le_self` says `Certified`;
//!   * this file's output is DISTINGUISHABLE from the control's. If a future
//!     refactor makes them identical, the disclosure has become inert and the
//!     pair must be repaired, not deleted.
//!
//! The inline diagnostic annotations live OUTSIDE the island braces, following
//! `clean_island_no_verify_trusted.rs`: `//` is not a Clean comment (Lean line
//! comments are `--`), and the Clean lexer reads `//` as the subtype separator
//! token, so an annotation inside the braces is island source.

clean {
    axiom assumed_le : forall (n : Nat), Nat.le n n

    theorem le_self (n : Nat) : Nat.le n n := assumed_le n
}
//~^^^^ ERROR Clean island declaration `assumed_le` is an axiom
//~^^^ ERROR Clean island proof `le_self` failed the strict certification audit because it depends on trust provenance: assumed_le

fn main() {}
