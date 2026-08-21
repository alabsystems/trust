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
// RE-PINNED 2026-08-20 (D2). `ca53846043` broke this test and did not measure it
// ("NOT MEASURED: the end-to-end fixture flips"). The ERROR — the whole contract
// this file names — is RESTORED and unchanged: same message, same span, exit 1.
//
// The two WARN pins below were DELETED because they described an obligation
// inventory that no longer exists, not because the disclosure weakened. They
// read "1 obligation(s) were not proved", which was the state when the
// coroutine body's SOLE row was the `assertion:panic-freedom:0` aggregate and
// it carried no authority. `ca53846043` made the ResumedAfter* sentinels real
// refutable rows and gave the aggregate a genuine (ex-falso) discharge, so the
// count is structurally no longer 1 and no correct behaviour reproduces it.
//
// STRICTLY STRONGER, MEASURED: the disclosure is now larger and pinned here by
// the added RAW assumption line. This body's summary reads "2 conditionally
// discharged (NOT proved), … 1 skipped out of 3 obligation(s)" — the word
// "proved" does not appear — plus a note naming the entry assumption, plus the
// ASSUMPTION row, plus the fail-closed ERROR. Before D2 the same body reported
// "2 proved … of which 2 kernel-certified by the clean CIC kernel" and exit 0.
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
//~? RAW Trust: ASSUMPTION [coroutine]
