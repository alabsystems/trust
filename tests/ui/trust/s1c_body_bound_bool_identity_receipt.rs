//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ check-pass
//! Retired-TrustWP regression control: this Bool identity is proved through the
//! active TrustMC/body-aware VC and Clean-kernel authority. No TrustWP request,
//! carrier, receipt, or private authority variant exists in the compiler.
//!
//! The strict build USED TO still fail on separate fresh rows that remained
//! Unknown, and this fixture was `check-fail` to pin exactly that. It no longer
//! is, and the change is a STRICT IMPROVEMENT in the compiler rather than a
//! weakening of this test.
//!
//! `6d70feb1633` ("vcgen: a postcondition read the RETURN JOIN, so control flow
//! refuted correct code") added the last-resort certification lane
//! `certify_propositional_closure_contradiction` together with
//! `NormalizedConjuncts::propositional_view`, written expressly for "the exact
//! shape a multi-atom or `Bool`-sorted `#[ensures]` clause produces". Before it,
//! `certify_linear_int_fragment` could not reach a Bool-sorted VC at all — it has
//! no `And`/`Or`/`Bool` atom arm and the normalized view filters out every bool
//! reification conjunct — so the row came back Unknown and strict policy aborted
//! the build.
//!
//! `result == flag` is TRUE on every input of `fn(flag) { flag }`. The pass is
//! not vacuous — the adjacent strict-greater-than mutant remains a failing
//! control.
pub fn bool_identity(flag: bool) -> bool ensures result == flag { flag }
