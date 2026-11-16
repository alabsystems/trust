//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-fail
//! Falsification twin of the C1 source reference facts (`docs/TCB.md`, "Source
//! reference facts"; `docs/DECISION_QUEUE.md`, 2026-11-06). Must stay NON-proved.
//!
//! `&MaybeUninit<u32>` and `&u32` are the same `Ptr` loaded as `U32` in trust-ir.
//! The parameter is an ADT pointee, so it is never claimed; the `&u32` that
//! `assume_init_ref` returns is a reference the body made itself, so a load
//! through it is withdrawn at reconciliation (measured with
//! `TRUST_SOURCE_REFERENCE_TRACE=1` on stage-1, 2026-11-06:
//! `claimed=1 parameters=0 loads=0 withdrawn=1`). Telling the solve that load is
//! initialized would assume the unsafe precondition the caller must prove.
//!
//! Both functions also fail for reasons that do not depend on that withdrawal
//! (a `[hardened_unsafe_operation]` row and a runtime-checked absent-callee
//! assertion), so this twin pins only the end-to-end non-proved verdict. The
//! withdrawal itself is pinned by the bridge unit tests
//! `a_load_through_a_call_result_reference_is_withdrawn` and
//! `a_load_through_a_loaded_reference_is_withdrawn`, which fail if the rule is
//! removed.

use std::mem::MaybeUninit;

pub fn read_uninit(m: &MaybeUninit<u32>, d: u32) -> u32 {
    //~^ NOTE Trust verification: 1 proved, 1 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 3 obligation(s)
    //~| ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    let v = unsafe { *m.assume_init_ref() };
    if d == 0 { 0 } else { v % d }
}

pub fn read_uninit_ptr(m: &MaybeUninit<u32>) -> u32 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)
    //~| ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    unsafe { m.as_ptr().read() }
}
