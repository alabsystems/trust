//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! I1 — the axiom-disclosure pair, HALF TWO (the `Certified` control). Its
//! partner is `clean_symbol_graph_axiom_disclosed.rs`. Neither file means
//! anything alone.
//!
//! SAME theorem name, SAME proposition (`le_self : forall n, Nat.le n n`), one
//! difference: the proof is a real kernel term (`Nat.le.refl n`, the
//! constructor) instead of a user `axiom`. It must be accepted AND it must be
//! reported as `Certified`.
//!
//! WHAT THIS PINS: that the assumption disclosure in the partner file is not
//! inert. A disclosure only carries information if the assumption-free case
//! produces a DIFFERENT row. If both files ever produce the same output, the
//! safeguard has decayed into decoration and the pair must be repaired — not
//! deleted, and not "fixed" by relaxing this side.
//!
//! HOW `Certified` IS OBSERVED TODAY. There is no row that literally prints the
//! word, so the observable is the island note:
//!
//!     note: Clean island kernel-checked: 1 declaration(s) registered (le_self)
//!
//! and the link to `Certified` is mechanical rather than editorial. That note is
//! emitted only when the island was not rejected
//! (`compiler/rustc_mir_transform/src/trust_verify.rs:7324-7335`), a `theorem`
//! leaf reaches `outcome.registered` only when `strict_leaf_policy_error`
//! returns `None`, and for a proof judgment that requires
//! `cert_meter::grade(env, ty, proof) == Grade::Certified`
//! (`crates/trust-certify/src/clean_island.rs:975-995`,
//! `crates/trust-cert-meter/src/lib.rs:57-82`). `Grade::Trusted` and
//! `Grade::Rejected` both become build errors, so "registered" is exactly
//! "kernel-checked with an empty trust closure".
//!
//! FOR THE I1 IMPLEMENTER: the decision of record makes this explicit rather
//! than derived — `KernelStatus` carries an `AxiomClosure`, and empty-closure
//! versus non-empty is what separates `Certified` from assumption-bearing. When
//! the note grows an explicit verdict word, update the annotation below to
//! assert it directly and say so in the partner file too. Deriving `Certified`
//! from the ABSENCE of an error, as this fixture must today, is the weaker
//! form; strengthening it is an improvement, weakening it is not.
//!
//! `Nat.le` / `Nat.le.refl` are the prelude spellings already exercised by
//! `tests/two-language-battery/lane-c-combo/c1_cited_min2.rs` and
//! `tests/e6-fragment-probe/probes/d13_deferred_import_citation.rs`, so a
//! failure here is about the verdict, not about whether the term parses.
//!
//! The inline annotation lives OUTSIDE the island braces: `//` is not a Clean
//! comment (Lean line comments are `--`) and the Clean lexer reads it as the
//! subtype separator token, so an annotation inside the braces is island source.

clean {
    theorem le_self (n : Nat) : Nat.le n n := Nat.le.refl n
}
//~^^ NOTE Clean island kernel-checked: 1 declaration(s) registered (le_self)

fn main() {}
