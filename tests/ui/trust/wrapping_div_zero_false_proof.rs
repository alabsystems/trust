//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//@ dont-require-annotations: ERROR
//! REGRESSION GUARD for a false proof that was live on main and is now FIXED.
//! All three functions below must be REFUSED. If any of them starts verifying
//! again, this fixture goes red.
//!
//! ## THE DEFECT THAT WAS FIXED
//!
//! `u32::wrapping_div` panics on a zero divisor — it wraps only on
//! `MIN / -1`. std says so, and it is observable:
//!
//!     fn victim(a: u32, b: u32) -> u32 { a.wrapping_div(b) }
//!     victim(10, 0)
//!     -> thread 'main' panicked: attempt to divide by zero   (exit 101)
//!
//! Trust reported `wrapping` and `wrapping_rem_` below with NO
//! diagnostics at all, while the SAME division written directly — `plain` — was
//! correctly refused. So the refusal was not missing because the divisor is
//! hard; it was missing because of HOW the callee was modeled.
//!
//! ## ROOT CAUSE, AND THE FIX
//!
//! An `Assert` inside a BUNDLED callee body mints no proof obligation for the
//! caller. `core::num::<impl u32>::wrapping_div`'s bundled body does contain the
//! correct `Assert { rhs != 0 }` — it can be dumped with
//! `-Ztrust-dump=native-bundle` — yet the lowered module carries only the
//! function-admission row. The panic is modeled and then not required of anyone.
//!
//! Note what this is NOT: `wrapping_div` and `wrapping_rem` are DELIBERATELY
//! excluded from the bridge's total-call list
//! (`crates/trust-ir-bridge/src/lower.rs`, whose comment says outright that they
//! "PANIC on a zero divisor"). The exclusion is correct and present. They
//! false-prove anyway, through the bundling lane rather than the total list.
//!
//! THE FIX: the native-bundle lane now DECLINES to bundle the primitive-integer
//! division spellings that panic on a zero divisor, so the call becomes an
//! absent callee and mints the fail-closed
//! `[trust-absent-callee-assumption] ... may panic` row. That strictly ADDS an
//! obligation — the opposite direction from the bundling declines that had to be
//! reverted this week. The authority is not new:
//! `is_total_primitive_int_arith_method` already withheld exactly these
//! spellings, saying they "PANIC on a zero divisor".
//!
//! ## THE COST, PINNED BELOW SO IT IS NOT INVISIBLE
//!
//! Declining the bundle makes the callee ABSENT, and an absent-callee assumption
//! cannot be discharged even when the divisor is provably non-zero — the body is
//! no longer there to relate the assumption to it. So `safe_literal_divisor`
//! below, which genuinely cannot panic, is now refused as well.
//!
//! That is a capability loss, not a soundness one, and it is the right side of
//! the trade: the previous behaviour "proved" these bodies only because NOTHING
//! demanded the assert, so the old proof was worthless. A verifier that refuses
//! a safe program is strictly better than one that accepts an unsafe one.
//!
//! The better fix — bundle the body AND mint a public obligation for its asserts
//! — is a change to the native-bundle planner, which rebuilds
//! `module.proof_obligations` from the compiler's obligation list rather than
//! from the bridge's. When that lands, `safe_literal_divisor` should become
//! provable and this fixture will say so by going red on that one function.
//!
//! ## WHY THIS FIXTURE EXISTS RATHER THAN A REPORT
//!
//! This defect is invisible to `TRUST_NO_BUNDLE_STD=1`, the usual lever for
//! simulating "decline std bundling": that flag makes every std callee absent,
//! so `wrapping_div` correctly fails closed and the bug disappears from view.
//! An over-approximation that hides exactly the dangerous case is worse than no
//! tool, so the guard has to be a fixture that runs on the real lane.
//!
//! Related: `reports/false-proof-pattern-2026-08-11.md`.

#![crate_type = "lib"]

/// CONTROL — the same division, written directly. This one IS correctly
/// refused today, which is what proves the divisor is not the difficulty.
pub fn plain(a: u32, d: u32) -> u32 { //~ ERROR Trust strict verification failed for `wrapping_div_zero_false_proof::plain`
    a / d
}

/// Panics when `b == 0`. Must be refused; currently reports nothing.
pub fn wrapping(a: u32, b: u32) -> u32 { //~ ERROR Trust strict verification failed for `wrapping_div_zero_false_proof::wrapping`
    a.wrapping_div(b)
}

/// Same defect through the remainder spelling.
pub fn wrapping_rem_(a: u32, b: u32) -> u32 { //~ ERROR Trust strict verification failed for `wrapping_div_zero_false_proof::wrapping_rem_`
    a.wrapping_rem(b)
}

/// THE COST OF THE FIX, pinned. This genuinely cannot panic — the divisor is a
/// non-zero literal — and it is refused anyway, because the callee is now absent
/// and its assumption cannot be related to the divisor. If a future planner
/// change makes this provable, THIS annotation is the one that should fail.
pub fn safe_literal_divisor(a: u32) -> u32 { //~ ERROR Trust strict verification failed for `wrapping_div_zero_false_proof::safe_literal_divisor`
    a.wrapping_div(7)
}
