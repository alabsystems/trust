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
// premise on `helper`. `scaled`'s `x / divisor` obligation must still be
// DISCHARGED by R1 caller coverage (`api` establishes `divisor = 4 != 0`) — on
// a compiler where the async fn still poisons the scan, R1 is disabled and
// `scaled` produces a SECOND error, failing the exact-annotation match.
fn scaled(x: u32, divisor: u32) -> u32 {
    x / divisor
}

#[inline]
pub fn api(x: u32) -> u32 {
    scaled(x, 4)
}

// The poison trigger: mere PRESENCE of a coroutine body in the crate. Its own
// strict-lane refusal is the expected error below — and must stay the ONLY one.
pub async fn helper(x: u32) -> u32 {
    //~^ ERROR coroutine executor-protocol premise is unproved
    x
}
