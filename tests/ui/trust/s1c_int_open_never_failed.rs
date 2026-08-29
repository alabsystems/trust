//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-pass
//! Machine-domain regression: `result >= 0` for unsigned `u64` must never be
//! refuted through an unbounded-Int compatibility interpretation. The active
//! MACHINE-faithful body-aware VC
//! (`vc:nonneg:postcondition:0`, `¬(result >= 0) ∧ result = x` over unsigned
//! u64) is proved by the native typed-CHC lane and independently re-solved
//! strict-UNSAT by the sealed-authority gate, and the S1 §5 per-row
//! reconciliation seals the def-site marker to that establishing authority.
//! Historical TrustWP decoding has no verdict role.
pub fn nonneg(x: u64) -> u64 ensures result >= 0 { x }
//~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown
