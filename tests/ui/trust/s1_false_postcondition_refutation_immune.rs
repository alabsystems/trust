//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ check-fail
//! Sealed-authority S1 (SolverReplayAuthority, SMT lane) — REFUTATION IMMUNITY.
//!
//! The load-bearing soundness test for the S1 mint: the property whose absence
//! reverted the prior native-authority attempts (#18/#19) twice. `result > x`
//! is FALSE for the returned `x` (`x > x` never holds), so the postcondition's
//! violation formula `x <= x` is SATISFIABLE. The gate's own fresh in-process
//! ay re-solve (`revalidate_vc_unsat_strict`) returns `Failed`, so the
//! `revalidate_all_solver_proofs` pass mints NOTHING — a bare `Proved` label on
//! a false postcondition can never be laundered into a `SolverRevalidated`
//! authority. The obligation stays refuted and the build MUST fail. A passing
//! compile here would be a catastrophic false proof.
pub fn gt_refl(x: u64) -> u64 //~ ERROR strict verification failed
    ensures result > x
{
    x
}
