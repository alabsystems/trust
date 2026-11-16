//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ check-pass
//! Regression control for the Bool identity postcondition. The retired TrustWP
//! receipt/carrier lane stays gone. Since dcf68b84b9f the router may discharge a
//! postcondition through native trust-wp as the designated deductive ALTERNATIVE to
//! trust-mc, and 573e62daa69 admits this fresh-Bool body. That evidence carries the
//! unique trust-wp request's lineage, which the compiler's strict-acceptance check
//! accepts only for that alternative. Before it did, this file reported a
//! self-contradictory "not fully verified" advisory for a row the router had
//! accepted as proved.
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
