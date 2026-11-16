//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! ONE-PATH-FALSE NEGATIVE TWIN of
//! `source_clause_conditional_postcondition_frontier.rs`.
//!
//! The clause is BYTE-IDENTICAL to the frontier's (`a <= 1000000 ==> result >=
//! a`) and the body differs in one arm only: the last arm returns `0` instead of
//! `a`. So paths 1 and 2 still satisfy the clause —
//!
//!   * `a >= 1000000` returns `1000000`; the antecedent holds only at
//!     `a == 1000000`, where `result == a`;
//!   * `b >= a` returns `b >= a`;
//!
//! — and only path 3 violates it: it returns `0` while `a > 0` and
//! `a <= 1000000`.
//!
//! WHY THIS FIXTURE EXISTS. The sibling `..._false_twin.rs` strengthens the
//! consequent instead, which makes the clause false on two of three paths and
//! (measured) leaves EVERY row unknown — 0 proved, 3 unknown — so it would stay
//! red even if the source-clause composition rule were deleted outright. This
//! file keeps the non-violating paths in the shape the frontier proves, so it
//! sits exactly where the frontier does and moves with it.
//!
//! MEASURED on stage1 built from this branch at `8113b3a0a81` (2026-09-17):
//! exit 1, "1 proved, 0 failed, 2 unknown, 0 timed out, 0 runtime-checked out of
//! 3 obligation(s)" — byte-for-byte the frontier's counts, with the marker
//! reporting the same defeat:
//!
//! ```text
//! the `ensures` clause #0 (`trust-contract:false_one_path::pick_zero:ensures:0`)
//!   was not discharged because 1 of its 2 body row(s) did not qualify:
//!   `vc:false_one_path__pick_zero:postcondition:1` … is UNKNOWN, not proved — …
//! ```
//!
//! WHAT THAT MEANS, stated honestly and NOT more strongly. On this toolchain the
//! false clause and the true one are refused by the SAME mechanism (an unknown
//! body row), so this file does not today discriminate "false" from "too hard".
//! What it does pin, and what no other fixture here pins, is the direction any
//! future fix must take: the frontier is closed by making `postcondition:1`
//! prove, and a fix that makes it prove for `pick` must NOT make it prove for
//! `pick_zero`, where it is false. This is the file that goes red if it does.
//!
//! WHAT IS PINNED: only that it is not a pass. `FAILED` versus `UNKNOWN` is
//! deliberately unpinned, for the same reason as the sibling — the loop-elided
//! over-approximation gap can demote a real refutation to unknown, and pinning
//! the stronger verdict would make an improvement in refutation reach look like
//! a regression. Both are fail-closed; a pass is not.
//!
//! AMENDMENT 2026-09-18 — THIS FILE'S JOB CHANGED, ITS ASSERTION DID NOT. The
//! cause of the frontier was found (the `goto`-only JOIN of the inner `if` was
//! emitted as ONE row whose path-guard conjunct is an `Or`, and that row alone
//! got no trust-mc PDR receipt), and vcgen now emits one flat row per
//! enumerated return path. `..._frontier.rs` is therefore a `check-pass`
//! POSITIVE now, and the counts quoted above no longer describe it: this body
//! has three paths, so the clause has three body rows, not two.
//!
//! The sentence above that anticipated exactly this — *"a fix that makes it
//! prove for `pick` must NOT make it prove for `pick_zero`, where it is
//! false"* — is now the file's entire purpose, and it is no longer hypothetical.
//! The per-path row for the `b < a` path pins the return slot to the body's
//! genuine stored value `0`, so the negated clause stays satisfiable on it.
//! Measured at the formula level in
//! `crates/trust-vcgen/src/generate/per_path_postcondition_tests.rs`
//! (`one_path_false_twin_still_pins_the_genuine_value`), semantically in
//! `early_return_postcondition_tests::one_of_three_paths_false_is_refuted_on_exactly_that_path`,
//! and END TO END on this source, on a stage1 built from the tree that landed
//! the split (2026-09-18, `-Ztrust-verify-output=both`):
//!
//! ```text
//! note: Trust verification: 2 proved, 0 failed, 2 unknown, ... out of 4 obligation(s)
//!   vc:…__pick_zero:postcondition:0   proved   trust-full-verifier
//!   vc:…__pick_zero:postcondition:1   unknown  trust-full-verifier   <- the `b < a` path
//!   vc:…__pick_zero:postcondition:2   proved   trust-full-verifier
//!   obligation:…__pick_zero:postcondition:0  unknown  trust-exact-source-clause-discharge
//! ```
//!
//! EXACTLY ONE of the three per-path rows is unknown, and it is the violating
//! path's own row — its two true siblings prove. That is the split isolating the
//! bad path rather than dissolving it into a disjunction that any one true arm
//! could satisfy, and it is the single strongest piece of evidence that the
//! split is sound. (The same twin in the early-`return` spelling,
//! `..._early_return_false.rs`, measures 2 proved / 2 unknown on the same build.)
//!
//! IF THIS FILE GOES GREEN, the split is crediting a path it must refuse. That
//! is a false proof, and it outranks every capability this lane bought.

pub fn pick_zero(a: u32, b: u32) -> u32
    //~^ ERROR Trust strict verification failed for
    ensures a <= 1000000 ==> result >= a
{
    if a >= 1000000 {
        1000000
    } else if b >= a {
        b
    } else {
        0
    }
}
