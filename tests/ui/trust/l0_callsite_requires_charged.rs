//@ revisions: l0 l0_memory_safe l0_advisory l0_dep l0_certify
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: l0_callsite_requires_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-verify-level=0
//@[l0_memory_safe] compile-flags: -Ztrust-policy=memory-safe
//@[l0_advisory] compile-flags: -Ztrust-policy=advisory
//@[l0_certify] compile-flags: -Ztrust-policy=certify
//@[l0] check-fail
//@[l0_memory_safe] check-fail
//@[l0_advisory] check-pass
//@[l0_dep] check-fail
//@[l0_certify] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//[l0_certify]~? ERROR -Ztrust-policy=certify requires -Ztrust-verify-level=1 or 2
//! At `-Ztrust-verify-level=0` a DIRECT call is charged its callee's `requires`,
//! on every policy (docs/KNOWN_HAZARDS.md, "at `-Ztrust-verify-level=0` a direct
//! call was charged nothing for its callee's `requires`").
//!
//! `add1` and `div` are verified UNDER their `requires`: the clause is assumed at
//! entry (`DefinitionEntryAssumption`) and the overflow / divide-by-zero check it
//! proves is elided, so the call-site `Precondition` row is the only thing that
//! keeps a caller inside the clause. That row is `L1Functional`. Before the fix
//! the level filter dropped it for a caller with no contract and no extracted
//! precondition (`p`, `z`: no parameters) at level 0, so nothing charged the
//! call. MEASURED on stage 1 of `782780ea0d`: this file's `l0` revision built
//! exit 0, as did the same shapes under certify at level 0, and a verify-off
//! `main` linked to the certify rlib printed `p() = 0` (`z()` panicked "attempt
//! to divide by zero" under a panic-free verdict).
//!
//! The fix (`effective_max_level`, `trust_verify.rs`) lifts a caller that owes a
//! callee `requires` to L1 on every policy, so it is verified exactly as at the
//! default level 2 for these bodies: the full summary DB, and the call-site rows
//! that survive the filter.
//!
//! Revisions:
//! * `l0` — the strict default: `p` and `z` are refused on a FAILED `[precond]`
//!   row. `q` (`add1(5)`) is the control and stays clean.
//! * `l0_memory_safe` — the same two refusals. `add1` and `div` are refused
//!   before and after (memory-safe does not admit their entry assumption).
//! * `l0_advisory` — nothing fails the build, but the row is minted and FAILED.
//! * `l0_dep` — the callee in another crate (`auxiliary/l0_callsite_requires_dep.rs`,
//!   verified at level 2): its exported contract set is charged at level 0 too.
//!   `dep_p` was refused before for the absent-callee row alone, with no
//!   `[precond]` row.
//! * `l0_certify` — certify at level 0 is refused before any session exists
//!   (docs/DECISION_QUEUE.md "L0-CERTIFY"): it built this file exit 0 before.
//!
//! The `.stderr` output is not checked; the pins are the annotations. They were
//! predicted from this file compiled with the BEFORE compiler at
//! `-Ztrust-verify-level=1`, the level the fix gives every body here (each one
//! owes a callee `requires` or has a contract), and MEASURED on the stage 1 of
//! `6011b74bad` (2026-10-03).

#[cfg(l0_dep)]
extern crate l0_callsite_requires_dep;

pub fn add1(x: u32) -> u32
//[l0_memory_safe]~^ ERROR Trust memory-safe verification failed for
    requires x < 100
{
    x + 1
}

pub fn div(a: u32, b: u32) -> u32
//[l0_memory_safe]~^ ERROR Trust memory-safe verification failed for
    requires b != 0
{
    a / b
}

pub fn p() -> u32 {
    //[l0,l0_dep]~^ ERROR Trust strict verification failed for
    //[l0,l0_dep]~| NOTE [precond] FAILED
    //[l0_memory_safe]~^^^ ERROR Trust memory-safe verification failed for
    //[l0_memory_safe]~| NOTE [precond] FAILED
    //[l0_advisory]~^^^^^ NOTE [precond] FAILED
    add1(u32::MAX)
}

pub fn z() -> u32 {
    //[l0,l0_dep]~^ ERROR Trust strict verification failed for
    //[l0,l0_dep]~| NOTE [precond] FAILED
    //[l0_memory_safe]~^^^ ERROR Trust memory-safe verification failed for
    //[l0_memory_safe]~| NOTE [precond] FAILED
    //[l0_advisory]~^^^^^ NOTE [precond] FAILED
    div(1, 0)
}

pub fn q() -> u32 {
    add1(5)
}

#[cfg(l0_dep)]
pub fn dep_p() -> u32 {
    //[l0_dep]~^ WARN Trust Level 0 safety verification incomplete for
    //[l0_dep]~| ERROR Trust strict verification failed for
    //[l0_dep]~| NOTE [precond] FAILED
    l0_callsite_requires_dep::dep_add1(u32::MAX)
}
