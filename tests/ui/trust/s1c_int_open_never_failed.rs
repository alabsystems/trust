//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-pass
//! Task #23 Slice 1, amendment 8 (valuation-independence pin): a claim that is
//! Int-OPEN but u64-TRUE must NEVER be refuted. `result >= 0` body-binds to
//! `let result = x in result >= 0`; over the sibling's unbounded Int the
//! inlined `x >= 0` is neither provable nor valuation-independently false, so
//! the sibling returns neither Verified nor Failed — that half of the pin is
//! unchanged, and is now enforced structurally by check-pass (any spurious
//! sibling refutation would fail the build).
//!
//! The build itself now PASSES: the MACHINE-faithful body-aware VC
//! (`vc:nonneg:postcondition:0`, `¬(result >= 0) ∧ result = x` over unsigned
//! u64) is proved by the native typed-CHC lane and independently re-solved
//! strict-UNSAT by the sealed-authority gate, and the S1 §5 per-row
//! reconciliation (`install_ensures_marker_reconciliation_authorities`) seals
//! the def-site marker — which carries the compiler's body-bound witness, the
//! predicate being inside the arithmetic-free fragment — to that establishing
//! authority. The row the sibling could not decide is therefore established
//! by the body-aware lane, never by the Int-open bare claim.
pub fn nonneg(x: u64) -> u64 ensures result >= 0 { x }
//~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown
