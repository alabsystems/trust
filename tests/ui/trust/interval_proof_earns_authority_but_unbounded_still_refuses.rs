//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@ check-fail
//! THE RAIL FOR THE 2026-09-20 INTERVAL-AUTHORITY CHANGE.
//!
//! An interval-lane `Proved` may now reach the ay re-derivation that mints S1
//! eligibility, so a BOUNDED allocation verifies where it used to report
//! "[unbounded_allocation] UNKNOWN (interval): Proved label lacked exact
//! kernel/native proof authority" — that is sweep `s20`,
//! `(0..n.min(8) as u32).collect()`.
//!
//! THIS one has no bound at all. `n` is an unconstrained `u32`, so the
//! allocation really is unbounded and the row must REFUSE. If it ever passes,
//! the change has stopped plumbing an existing proof to the mint and started
//! weakening the authority gate — which is the whole difference between the two.
//!
//! Note what is NOT claimed by its sibling verifying: nothing became provable
//! that was not already proved. The row's own violation formula was already
//! `unsat` under this tree's `ay` with `unsat_admission=strict-proof`; it simply
//! never reached the mint, because a provenance refactor's `continue` routed
//! past the producer.
pub fn build(n: u32) -> Vec<u32> {
    (0..n).collect()
}
