// Trust (assumption ledger, Stage 1): the explicit crate-under-check strict lane
// stays fail-closed on a coroutine body — a hard build error. Since the audit
// merge 722ce062d0 the abort is the explicit executor-protocol rejection
// (`abort_on_coroutine_protocol_assumption`): supported user data-safety
// obligations are verified and reported first, then the unproved
// executor-protocol premise is rejected — the exact contract pinned by
// tests/run-make/trust-assumption-rows/rmake.rs ("strict mode must reject the
// visible protocol premise"). The abort fires during the check build (the
// verify pass runs on optimized MIR at metadata time), hence check-fail.
//
// RE-PINNED 2026-08-15 for upstream 983bc1a3b6 (merged here as f1182b2285), which
// REMOVED the whole-function panic-freedom subsumption as a false proof. THE ABORT
// ITSELF IS UNCHANGED — same message, same span, same exit 1 — which is the whole
// contract this test names; only the accompanying report grew. The coroutine's
// `assertion:panic-freedom:0` aggregate is the item's sole row, so the deleted lane
// discharged it from an EMPTY conjunction; it is now an authority-less
// `trust-assert-refute` Proved label, reported runtime-checked (NOT proved), which
// adds the two warnings. STRONGER-OR-EQUAL: strictly more unproved surface is
// reported and the fail-closed error is untouched.
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ edition: 2021
//@ compile-flags: --crate-type=lib
//@ check-fail
//@ dont-check-compiler-stderr
pub async fn tick(x: u32) -> u32 { x } //~ ERROR coroutine executor-protocol premise is unproved
//~^ WARN Trust Level 0 safety verification incomplete for `full_lane_abort_unchanged::tick::{closure#0}`: 1 obligation(s) were not proved
//~^^ WARN Trust verification advisory
