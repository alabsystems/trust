// Trust (assumption ledger, Stage 1): the explicit crate-under-check strict lane
// stays fail-closed on a coroutine body — a hard build error. Since the audit
// merge 722ce062d0 the abort is the explicit executor-protocol rejection
// (`abort_on_coroutine_protocol_assumption`): supported user data-safety
// obligations are verified and reported first, then the unproved
// executor-protocol premise is rejected — the exact contract pinned by
// tests/run-make/trust-assumption-rows/rmake.rs ("strict mode must reject the
// visible protocol premise"). The abort fires during the check build (the
// verify pass runs on optimized MIR at metadata time), hence check-fail.
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ edition: 2021
//@ compile-flags: --crate-type=lib
//@ check-fail
//@ dont-check-compiler-stderr
pub async fn tick(x: u32) -> u32 { x } //~ ERROR coroutine executor-protocol premise is unproved
