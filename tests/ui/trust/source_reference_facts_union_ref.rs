//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-fail
//! Falsification twin of the C1 source reference facts (`docs/TCB.md`, "Source
//! reference facts"). Must stay NON-proved.
//!
//! A `&u32` fabricated from an integer is not a parameter, and the function that
//! fabricates it is not borrow-provenance-clean, so no claim may reach the solve
//! for `*r`.
//!
//! What each function exercises (measured with `TRUST_SOURCE_REFERENCE_TRACE=1`
//! on stage-1, 2026-11-06):
//!
//! * `load_fabricated` (through a union) does NOT reach the facts seam: lowering
//!   refuses the union field projection first, so it pins only the end-to-end
//!   non-proved verdict. The clean-set exclusion itself is pinned by the bridge
//!   unit test `unclean_function_records_nothing`.
//! * `load_transmuted` (through `transmute`) reaches the seam: its bundle is
//!   built and the trace prints `claimed=0`, the root being unclean.
//! * `pass_transmuted` hands the fabricated reference to the clean `load`. The
//!   member's parameter and load ARE claimed (`claimed=2`, all of them `load`'s),
//!   and a callee parameter fact is a REQUIREMENT on the actual at the call site,
//!   never an assumption, so the caller stays non-proved.

union Fabricate {
    addr: usize,
    reference: &'static u32,
}

pub fn load_fabricated(a: usize, d: u32) -> u32 {
    //~^ NOTE Trust verification: 1 proved, 1 failed, 2 unknown, 0 timed out, 0 runtime-checked out of 4 obligation(s)
    //~| ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust full verification failed
    let r = unsafe { Fabricate { addr: a }.reference };
    if d == 0 { 0 } else { *r % d }
}

fn load(r: &u32, d: u32) -> u32 {
    if d == 0 { 0 } else { *r % d }
}

pub fn load_transmuted(a: usize, d: u32) -> u32 {
    //~^ NOTE Trust verification: 1 proved, 1 failed, 2 unknown, 0 timed out, 0 runtime-checked out of 4 obligation(s)
    //~| ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    let r: &u32 = unsafe { std::mem::transmute(a) };
    if d == 0 { 0 } else { *r % d }
}

pub fn pass_transmuted(a: usize, d: u32) -> u32 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 2 unknown, 0 timed out, 0 runtime-checked out of 3 obligation(s)
    //~| ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    let r: &u32 = unsafe { std::mem::transmute(a) };
    load(r, d)
}
