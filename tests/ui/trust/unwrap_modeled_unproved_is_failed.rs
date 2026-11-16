//~ NOTE "failed":1,"unknown":0,"timed_out":0,"skipped":0,"runtime_checked":1
//@ revisions: advisory strict
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//! An unproved std unwrap is published `failed` whether or not the engine
//! modelled its receiver (DECISION_QUEUE "UF-1", 2026-10-03). `x.unwrap()` on a
//! parameter gets the SOLVABLE `Call::unwrap::panic-freedom` obligation (the
//! parameter's entry tag is free, so it is not proved); an unmodelled shape gets
//! the fail-closed `Call::unwrap::panic-freedom-unverified` row instead. On
//! stage-1 aa965027e2 the first was published `runtime_checked` and the second
//! `failed`, so modelling a receiver made its unproved unwraps MORE permissive
//! under `--allow-l0-gaps`. Line 1 pins the published counts: the unwrap row is
//! `failed`; the remaining runtime-checked row is the body's aggregate
//! panic-freedom row, which is not an unwrap obligation. Advisory still compiles
//! (drop-in Rust); strict refuses, as before.
pub fn param_unwrap(x: Option<u32>) -> u32 {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete
    //[strict]~| ERROR Trust strict verification failed
    x.unwrap()
}
