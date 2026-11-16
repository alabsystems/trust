//@ revisions: on off certify certify_off
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[off] compile-flags: -Ztrust-no-adapter-yield
//@[certify] compile-flags: -Ztrust-policy=certify -Cpanic=abort
//@[certify_off] compile-flags: -Ztrust-policy=certify -Cpanic=abort -Ztrust-no-adapter-yield
//@[on] check-pass
//@[certify] check-pass
//@[off] check-fail
//@[certify_off] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! ZERO-ROW-GATE AMENDMENT (2026-10-10, docs/DECISION_QUEUE.md ZERO-ROW-GATE): "the parent emits nothing" below is
//! superseded. The parent `all_zero` has zero obligations of its own, but its
//! `Iterator::all` call is discharged by no authenticated registry (the adapter-yield
//! premise discharges the closure's row, not the call), so it publishes an `unknown`
//! row and is refused in every revision. The closure-level on/off differential is
//! unchanged and still pinned on the closure.
//!
//! D2 tier 1 (2026-09-24): `ADAPTER_YIELD` over a constant-bounded integer
//! `Range`, under the default policy AND under `-Ztrust-policy=certify`.
//!
//! A row discharged under a modeled fact keeps its engine authority: the Clean
//! kernel re-checks `premise ⇒ safe`, so the row is `Certified` for that
//! implication and `certify` accepts it (docs/TCB.md, `ADAPTER_YIELD`). The
//! parent `all_zero` has no row of its own, so under `certify` this file is
//! green exactly when the closure's row is certified; with the premise off it
//! is an error in both policies.
//!
//! BEFORE (stage-1 snapshot 4e9fe36bf = the `off`/`certify_off` revisions):
//! rc=1 in both policies, `[bounds] FAILED (ay-in-process); counterexample:
//! … i = 8` on the closure; the parent emits nothing.
//!
//! 2026-09-28: "no row of its own" used to be an ACCIDENT. The `all` call was
//! modelled as may-panic, and nothing requested that marker (`docs/KNOWN_HAZARDS.md`,
//! "A may-panic MARKER is only as good as its CARRIER"), so a `u128` `count()` passed
//! the same way. Once the marker got its carrier, the parent carried a
//! runtime-checked row, and `certify` refused it. It is green again for a stated
//! reason. The compiler credits the `all` call as total because the closure's OWN
//! verdict discharged its panic-freedom
//! (`collect_verified_callable_consumer_total_calls`, `docs/TCB.md`). The premise the
//! closure used was installed for this one call. In `certify_off` there is no
//! premise, so the closure's row fails, the call is not credited, and the parent is
//! refused as well.

// ZERO-ROW-GATE (2026-10-10) refused this zero-row body in every revision. Re-pinned
// 2026-10-15 (the merge of 2026-10-14, DECISION_QUEUE D103): with the closure proved
// (`on`, `certify`) the gate now reads the drive-only consumer lane's decision for the
// `all` call (VERIFIED-CALLABLE-ZERO-ROW-PARITY) and the body builds; with the premise
// off the bundled `all` carries a `runtime_checked` aggregate instead, which `off`
// reports and `certify_off` refuses (its own annotations below).
pub fn all_zero(a: &[u8; 8]) -> bool {
    //[certify_off]~^ ERROR Trust Level 0 safety verification incomplete for `range_all_certify::all_zero`
    //[certify_off]~^^ ERROR Trust strict verification failed for `range_all_certify::all_zero`
    (0..8).all(|i| a[i] == 0)
    //[on]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    //[on]~| NOTE Trust modeled fact ADAPTER_YIELD: core `Iterator::all` over `0..8` invokes this closure only on items it yields; assumed: item parameter `_2` has value in [0, 8)
    //[certify]~^^^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    //[certify]~^^^^ NOTE Trust modeled fact ADAPTER_YIELD: core `Iterator::all` over `0..8`
    //[off]~^^^^^ ERROR Trust Level 0 safety verification incomplete for `range_all_certify::all_zero::{closure#0}`: 1 obligation(s) were not proved
    //[off]~^^^^^^ ERROR Trust strict verification failed for `range_all_certify::all_zero::{closure#0}`: 1 obligation(s) were not fully verified
    //[off]~^^^^^^^ NOTE [bounds] FAILED
    //[certify_off]~^^^^^^^^ ERROR Trust Level 0 safety verification incomplete for `range_all_certify::all_zero::{closure#0}`: 1 obligation(s) were not proved
    //[certify_off]~^^^^^^^^^ ERROR Trust strict verification failed for `range_all_certify::all_zero::{closure#0}`: 1 obligation(s) were not fully verified
    //[certify_off]~^^^^^^^^^^ NOTE [bounds] FAILED
}
