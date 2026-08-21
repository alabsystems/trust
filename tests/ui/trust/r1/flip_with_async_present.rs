//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
// R1 REGRESSION PIN: the crate-wide caller scan must survive an `async fn`.
//
// An `async fn`'s coroutine body (`helper::{closure#0}`) has its elaborated MIR
// stolen at ANALYSIS phase — computing the coroutine's layout forces
// `optimized_mir(coroutine)`, whose first act is that steal. When the scan read
// every fn-like body through the elaborated `Steal`, the coroutine came back
// stolen and POISONED the whole crate: R1 was silently disabled for every crate
// containing an `async fn`. The scan now routes coroutine bodies by IDENTITY
// through `optimized_mir`, the steal consumer.
//
// DISCRIMINATION, updated for the strict coroutine policy (the ay-0.4.0-era pin
// set stopped discharging the compiler-generated ResumedAfterReturn/Panic/Drop
// sentinels, so strict policy now REFUSES every coroutine body as
// conditional-on-executor — a deliberate fail-closed ruling, not a bug). This
// test therefore expects EXACTLY ONE error: the coroutine executor-protocol
// premise on `helper`.
//
// MEASURED 2026-08-15: that refusal aborts the run before `scaled` is verified,
// so THIS file can no longer observe the R1 arm — under strict, an R1-poisoned
// compiler is silent about `scaled` rather than emitting a second error. The
// live R1 discrimination therefore moved to the advisory sibling
// `flip_with_async_present_advisory.rs`, where `scaled` is actually reached.
// Keep this file as the strict-refusal pin; keep that one as the R1 pin.
fn scaled(x: u32, divisor: u32) -> u32 {
    x / divisor
}

#[inline]
pub fn api(x: u32) -> u32 {
    scaled(x, 4)
}

// The poison trigger: mere PRESENCE of a coroutine body in the crate. Its own
// strict-lane refusal is the expected error below — and must stay the ONLY one.
//
// RE-PIN 2026-08-20 (D2), STRICTLY STRONGER. The ERROR — the strict coroutine
// refusal this file pins — is RESTORED and still the only error. `ca53846043`
// had suppressed it by publishing a CONTRACT row in the fail-closed lane, and
// never measured the flip.
//
// The two WARN pins were deleted and REPLACED by the RAW assumption pin below,
// which is a tighter guarantee. Their "1 obligation(s)" counts described the
// inventory from when the coroutine body's sole row was the authority-less
// panic-freedom aggregate; sentinels are now separate rows, so no correct
// behaviour reproduces that count. Measured for this body now: "2 conditionally
// discharged (NOT proved), … 1 skipped out of 3 obligation(s)" — the word
// "proved" does not appear — plus the assumption row pinned below.
//
// RE-PIN 2026-08-15, STRICTLY STRONGER: the two WARN rows are new, and they
// disclose a proof this compiler deliberately no longer mints. The coroutine
// body's ONLY obligation row is the synthesized whole-function
// `assertion:panic-freedom:0` aggregate. Upstream 1ab7ee48f2 and then
// 983bc1a3b6 deleted `apply_whole_function_panic_freedom_subsumption`, which
// used to hand that row a `WholeFunctionPanicFreedomSubsumption` authority off
// a conjunction over the function's OTHER rows — and here there are none, so
// that conjunction was empty and the discharge vacuous: precisely the false
// proof 1ab7ee48f2 closes. The row is now Proved-but-authorityless, so
// `permits_static_proved_transport_for` (collapsed to `is_static_proof_for`)
// refuses it and both policy lanes report it unproved. The ERROR is unchanged
// and still the only error: no refutation lost, no verdict downgraded — a
// vacuous proof was withdrawn and the gap is now stated out loud.
pub async fn helper(x: u32) -> u32 {
    //~^ ERROR coroutine executor-protocol premise is unproved
    x
}
//~? RAW Trust: ASSUMPTION [coroutine]
