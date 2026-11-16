//@ needs-trust-verify
//@ revisions: true_clause false_clause
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! NEGATIVE CONTROL for the joint Rust+Lean cited lane (2026-09-15), the pair of
//! `tests/two-language-programs/r36_joint_cited_lean_theorem`.
//!
//! `pb_max_r` forwards to the Clean island definition `pb_max`, so `result` in
//! its postcondition denotes `pb_max lhs rhs` and a cited theorem is audited
//! against the clause OVER THAT TERM. `pb_max_ge_left` proves
//! `lhs <= pb_max lhs rhs`; the clause below states `result >= rhs`, i.e.
//! `rhs <= pb_max lhs rhs` — a proposition the theorem does NOT prove (it
//! happens to be true; that is irrelevant, the audit checks the proof term
//! against THIS statement). The citation must be REFUSED as a statement
//! mismatch, and the strict build must fail. Nothing in this file may compile
//! to a green verdict: a name match on `pb_max` would be exactly the false
//! PROVE this control exists to catch.
//!
//! Trust (2026-09-28): the two revisions, since callers of a select-shaped island
//! `def` got its definitional summary (`_0 == ite(rhs < lhs, lhs, rhs)`,
//! `clean_origin_select_call_summary.rs`).
//! * `true_clause` is the original control. Its clause is TRUE, so the solver
//!   lane now PROVES the postcondition row from the summary. The citation is
//!   still refused as a statement mismatch, and that hard error still fails the
//!   build, which is the property this control exists for. Before the summary,
//!   the postcondition also stayed unproved, because `pb_max`'s result was
//!   havocked.
//! * `false_clause` cites the same theorem for a FALSE clause (`result <= rhs`,
//!   false for `lhs > rhs`). The citation is refused, AND the postcondition must
//!   stay unproved, so the summary cannot bless a wrong claim.

clean {
    def pb_max (lhs : UInt64) (rhs : UInt64) : UInt64 := if rhs < lhs then lhs else rhs
    theorem pb_max_ge_left (lhs rhs : UInt64) : lhs <= pb_max lhs rhs := by
      unfold pb_max
      split <;> omega
}

#[cfg(true_clause)]
pub fn pb_max_r(lhs: u64, rhs: u64) -> u64
    ensures result >= rhs by pb_max_ge_left
    //[true_clause]~^ ERROR citation `pb_max_ge_left` failed the strict Clean statement/certification audit
{
    pb_max(lhs, rhs)
}

#[cfg(false_clause)]
pub fn pb_max_r(lhs: u64, rhs: u64) -> u64
    ensures result <= rhs by pb_max_ge_left
    //[false_clause]~^ ERROR citation `pb_max_ge_left` failed the strict Clean statement/certification audit
{
    //[false_clause]~^^^^ ERROR Trust strict verification failed for
    pb_max(lhs, rhs)
}

fn main() {
    let _ = pb_max_r(1, 2);
}
