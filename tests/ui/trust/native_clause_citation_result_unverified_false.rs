//@ revisions: off on
//@ needs-trust-verify
//@[off] compile-flags: -Ztrust-verify=off
//@[on] compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@[on] normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! TG3 (COMPILE-TIME-FACTS-1, 2026-11-05) SUPERSEDES the history below: the
//! unverified-lane allowance it describes is gone. With verification off the
//! kernel-only lane E6-imports the cited functions' bodies, so the `off`
//! revision now judges every `result` clause exactly as `on` does — the
//! "NOT checked" note is never printed, and a false `result` citation is a hard
//! error in both revisions. The two revisions stay so that this parity is pinned.
//!
//! CLOSE NEGATIVE TWIN of `native_clause_citation_result_unverified`: what the
//! unverified-lane allowance does NOT cover, and that the verified lane accepts
//! nothing new.
//!
//! BOTH revisions require EVERY error to be annotated — there is deliberately
//! no `dont-require-annotations: ERROR` in either — so the `off` revision pins
//! both directions at once: the three refusals below are still hard errors with
//! verification off, and `false_result_claim` is NOT one (it carries the "NOT
//! checked" note instead — the honest cost of a lane that imports no body, and
//! the reason the note exists). The `on` revision pins that the very same
//! clause IS a hard error wherever a proof claim is made, down to the
//! whole-function `Trust strict verification failed` rows the two false
//! citations leave behind.
//!
//!   * `false_result_claim` — a `>=` theorem cited on a strict `>` clause over
//!     `result`. `off`: not judged, and says so. `on`: hard error, unchanged.
//!   * `false_result_free_claim` — the same false citation WITHOUT `result`. Its
//!     goal needs no body, so it is judged — and refused — in BOTH lanes. The
//!     allowance is for a goal this lane cannot build, never for a mismatch it
//!     can see.
//!   * `missing_theorem`, `cites_a_definition` — body-independent facts about
//!     the citation itself stay enforced on a `result` clause in both lanes.
//!
//! An axiom- or `sorry`-backed theorem is not exercised here because a strict
//! island refuses it at registration and taints the session (every citation in
//! the file would then report the taint); `trust-certify`
//! `cited_theorem_audit_is_body_independent_and_never_a_statement_match` pins
//! that the body-independent audit never vouches for one, and
//! `clean_island_sorry_result_citation_unverified` pins the end-to-end verify-off
//! behaviour (a hard publish-audit error, and NO "NOT checked" note).

clean {
    def not_a_theorem (x : UInt64) : UInt64 := x

    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => @Nat.le.refl (UInt64.toNat x)
}

pub fn false_result_claim(x: u64) -> u64
//[on]~^ ERROR Trust strict verification failed for `native_clause_citation_result_unverified_false::false_result_claim`
    ensures result > x by u64_ge_refl
    //~^ ERROR citation `u64_ge_refl` failed the strict Clean statement/certification audit
{
    x
}

pub fn false_result_free_claim(x: u64) -> u64
//[on]~^ ERROR Trust strict verification failed for `native_clause_citation_result_unverified_false::false_result_free_claim`
    ensures x > x by u64_ge_refl
    //~^ ERROR citation `u64_ge_refl` failed the strict Clean statement/certification audit
{
    x
}

pub fn missing_theorem(x: u64) -> u64
    ensures result >= x by no_such_theorem
    //~^ ERROR cited theorem `no_such_theorem` is not registered
{
    x
}

pub fn cites_a_definition(x: u64) -> u64
    ensures result >= x by not_a_theorem
    //~^ ERROR cited declaration `not_a_theorem` is
{
    x
}

fn main() {
    let _ = false_result_claim(1);
    let _ = false_result_free_claim(2);
    let _ = missing_theorem(3);
    let _ = cites_a_definition(4);
}
