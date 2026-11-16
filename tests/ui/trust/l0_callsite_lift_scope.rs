//@ revisions: l0_transitive l0_transitive_memory_safe l0_derived
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-verify-level=0
//@[l0_transitive_memory_safe] compile-flags: -Ztrust-policy=memory-safe
//@[l0_transitive] check-pass
//@[l0_transitive_memory_safe] check-fail
//@[l0_derived] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@[l0_derived] dont-require-annotations: WARN
//! What lifts a body to level 1 at `-Ztrust-verify-level=0`: a call-site
//! `Precondition` row of ITS OWN (docs/KNOWN_HAZARDS.md, "at
//! `-Ztrust-verify-level=0` a direct call was charged nothing for its callee's
//! `requires`"; docs/DECISION_QUEUE.md, L0-REQ). The direct case is pinned by
//! `l0_callsite_requires_charged.rs`; this file pins the scope of the lift.
//!
//! * `l0_transitive`, `l0_transitive_memory_safe` — a body whose own calls owe
//!   nothing keeps level 0, even when a callee of its callee carries a `requires`.
//!   The summary DB the compiler builds for a caller also holds the summaries the
//!   transitive-trace closure registers for the callees OF an attached callee body
//!   (`add1` here, reached through `w`), and the first form of the lift asked
//!   whether ANY summary in that DB declared a precondition. MEASURED on the stage 1
//!   of `6011b74bad` (the first build of the lift): `p` was lifted and got the
//!   level-1 termination charge ("termination is ASSUMED"), `pf` gained an UNKNOWN
//!   `[float_overflow_to_infinity]` row and two warnings, and under memory-safe `pf`
//!   was refused, though neither calls anything that owes a `requires`. Wave 8's
//!   stage 1 (no lift) gave `p` and `pf` "1 proved … out of 1" and no diagnostic,
//!   which is what these revisions expect now. `pd` is the control: the same
//!   recursion calling `add1` DIRECTLY owes its `requires`, so it is verified as
//!   at level 1 and carries the D9 termination charge.
//! * `l0_derived` — a crate with no `requires` at all is lifted too where a body
//!   calls a contract-less std callee Trust DERIVES a precondition for: the
//!   `step_by` constructor (`step != 0`) and a bundled member's entry div/rem (the
//!   `Wrapping<u8>` `/`). Those rows are minted at the body's own call, so the body
//!   is verified as at level 2: `stepped` and `wrapping_div` are refused on a
//!   FAILED `[precond]` row, and `stepped_ok` builds with warnings only. Wave 8's
//!   stage 1 (no lift) refused all three at level 0 with "native typed-TrustIr
//!   lowering did not complete" and no `[precond]` row. The same file at level 2
//!   gives the output this revision expects (measured on the stage 1 of
//!   `6011b74bad`).
//!
//! The `.stderr` output is not checked; the pins are the annotations, and in the
//! two transitive revisions every warning must be annotated, so the lift of `p`
//! or `pf` fails them.

#[cfg(l0_derived)]
use std::num::Wrapping;

#[cfg(any(l0_transitive, l0_transitive_memory_safe))]
pub fn add1(x: u32) -> u32
//[l0_transitive_memory_safe]~^ ERROR Trust memory-safe verification failed for
    requires x < 100
{
    x + 1
}

#[cfg(any(l0_transitive, l0_transitive_memory_safe))]
pub fn w(y: u32) -> u32 {
    if y < 100 { add1(y) } else { 0 }
}

#[cfg(any(l0_transitive, l0_transitive_memory_safe))]
pub fn p(b: bool) -> u32 {
    if b { p(b) } else { w(3) }
}

#[cfg(any(l0_transitive, l0_transitive_memory_safe))]
pub fn pd(b: bool) -> u32 {
    //[l0_transitive,l0_transitive_memory_safe]~^ WARN termination is ASSUMED
    if b { pd(b) } else { add1(3) }
}

#[cfg(any(l0_transitive, l0_transitive_memory_safe))]
pub fn pf(f: &f64) -> f64 {
    let _ = w(3);
    *f * 1e300
}

#[cfg(l0_derived)]
pub fn stepped(v: &[usize]) -> usize {
    //[l0_derived]~^ ERROR Trust strict verification failed for
    //[l0_derived]~| ERROR Trust Level 0 safety verification incomplete for
    //[l0_derived]~| NOTE [precond] FAILED
    (0..10usize).step_by(v.len()).count()
}

#[cfg(l0_derived)]
pub fn stepped_ok() -> usize {
    (0..10usize).step_by(2).count()
}

#[cfg(l0_derived)]
pub fn wrapping_div(a: Wrapping<u8>, b: Wrapping<u8>) -> Wrapping<u8> {
    //[l0_derived]~^ ERROR Trust strict verification failed for
    //[l0_derived]~| NOTE [precond] FAILED
    a / b
}
