//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-fail
//! B1 REFUTATION BRANCH (load-bearing falsification — the false-proof
//! tripwire THROUGH the branched-ensures discharge seam): `ensures result > 0`
//! on the abs body is FALSE at x = 0 (the final `else` branch returns x
//! itself, and ¬(0 > 0) is satisfiable). The x = 0 branch VC must NOT prove —
//! the typed CHC lane refutes it (or fail-closes to Unknown), so:
//!   * the def-site marker is never re-keyed Proved;
//!   * `ExactSourceClauseDischarge` never seals the marker — the discharge
//!     requires EVERY clause-linked per-branch row Proved with
//!     `KernelCertified | FreshExactDirectChcPdr` authority, and a Failed or
//!     Unknown postcondition row aborts the whole group;
//!   * clause-link metadata on the rows carries no authority by construction —
//!     a stamp without the proofs is irrelevant.
//! The build MUST fail. A passing compile here would be a catastrophic false
//! proof through the branched-ensures seam.
pub fn abs_like_pos(x: i32) -> i32 ensures result > 0 { if x == i32::MIN { i32::MAX } else if x < 0 { -x } else { x } }
//~^ ERROR strict verification failed
