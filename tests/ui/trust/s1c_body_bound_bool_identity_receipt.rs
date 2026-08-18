//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ check-pass
//! Task #23 Slice 1 receipt control: unlike the integer Ge fixture, this Bool
//! identity has no Clean arithmetic/source proof for the original placeholder
//! marker. The compiler-authenticated typed proposition names the return `_0`;
//! the body-bound finalizer normalizes it to `result` and derives
//! `let result = flag in result == flag`.
//!
//! Since the TCB closure work (docs/design/2026-07-25-tcb-closure-plan.md
//! step 1) that derived claim is re-derived in the Clean kernel rather than
//! taken from the adapter: `flag = flag` is closed by `Eq.refl`, so the marker
//! seals `BodyBoundKernelCertified` and the report names the kernel re-check.
//! The live Trust-WP receipt is still required to enter the lane — it is what
//! binds the claim to this row — so this fixture remains the receipt control it
//! always was; the reason line is what changed.
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
//! So the old expectation encoded a VERIFIER INCOMPLETENESS, not a "bad code must
//! fail" assertion: `result == flag` is TRUE on every input of `fn(flag) { flag }`.
//! The postcondition is now discharged by a genuine zero-trust Clean-kernel
//! certificate, and the fixture asserts that. The pass is not vacuous — false
//! mutants of this identical shape are still refuted, and the family's refutation
//! control lives in its own fixture, which continues to fail as designed.
pub fn bool_identity(flag: bool) -> bool ensures result == flag { flag }
