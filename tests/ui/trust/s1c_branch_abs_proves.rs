//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-pass
//! B1 ACCEPTANCE (branched `ensures`, discharged end-to-end): a BRANCHED
//! `ensures` function — the class the single-block body-bound witness can
//! never serve — is PROVED with every obligation discharged, def-site clause
//! marker included.
//!
//! trust-vcgen emits one body-aware Postcondition VC per return branch, each
//! carrying the clause-link metadata; the `-x` branch's return slot is pinned
//! by the wrap-exact machine negation (`BvToInt(BvSub(IntToBv(0,w),
//! IntToBv(x,w)))`) rather than being silently dropped — the earlier drop left
//! the slot FREE and turned a provable row into a spuriously satisfiable
//! query. The native typed CHC/PDR lane proves each per-branch query (the
//! signed Int↔BV bridge atoms of the negation encoding are eliminated into
//! pure QF_BV by an equisatisfiable, fail-closed rewrite), its sealed
//! candidates are consumed through the fresh-exact replay into
//! `FreshExactDirectChcPdr` receipts, and `ExactSourceClauseDischarge` seals
//! the marker to EXACTLY those per-branch rows under the unchanged strict bar
//! (`KernelCertified | FreshExactDirectChcPdr` — never `SolverRevalidated`,
//! which is a replay-integrity token, not an independent body proof).
//!
//! The refutation tripwire through this same seam
//! (s1c_branch_false_ensures_refuted) MUST stay failing: `ensures result > 0`
//! on this body is false at x = 0, and no lane that proves this fixture may
//! ever prove that one.
pub fn abs_like(x: i32) -> i32 ensures result >= 0 {
    if x == i32::MIN { i32::MAX } else if x < 0 { -x } else { x }
}
