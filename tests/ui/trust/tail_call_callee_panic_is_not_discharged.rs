//@ needs-trust-verify
//@ edition: 2021
//@ revisions: default certify tailcount
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[default] check-fail
//@[certify] check-fail
//@[tailcount] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! NEW-TAILCALL (docs/KNOWN_HAZARDS.md, "CLOSED 2026-09-27 — a `become` tail
//! call was never examined by the panic-freedom call gates"): `become f(x)` is a
//! CALL, and the callee's panics reach our caller exactly as they would behind
//! an ordinary call.
//!
//! The gates that decide "every call of this body is discharged" — the refute
//! lane's catch-all discharge (`all_calls_discharge_panic_free`), the
//! zero-obligation / postcondition-only registration gate and the R40 blessing
//! candidacy — each matched `Terminator::Call` alone, and `become` extracts to
//! `Terminator::TailCall`. A body whose only call was a tail call therefore
//! passed them VACUOUSLY: `tail` below published its whole-function
//! panic-freedom catch-all `proved` (solver `trust-assert-refute`) and was
//! REGISTERED panic-free, so `calls_tail` was proved on that registration too,
//! while `plain` — the same call without `become` — was refused.
//!
//! Pinned to edition 2021. Under 2015 `panic!("boom")` lowers to the generic
//! `std::panicking::begin_panic::<&str>`, and measured on the unfixed stage 1
//! built from `1505108872` no caller of `boom` then reached the call gate at all
//! (`[ASSERT_P2] ... pf_idxs=[]`): that compiler refused `tail` for an unrelated
//! reason, and the `default`/`certify` revisions stopped exercising the gate this
//! file is about.
//!
//! Revisions:
//! * `default` — `tail` and `calls_tail` now report what `plain` reports
//!   (runtime-checked, a warning under the default policy). On the unfixed
//!   compiler both reported only a "1 proved" note, so their annotations fail
//!   it.
//! * `certify` — the same four functions under `-Ztrust-policy=certify`: every
//!   one of them is REFUSED. On the unfixed compiler `tail` and `calls_tail`
//!   were accepted ("1 proved").
//! * `tailcount` — the panic-callee EXEMPTION. The refute lane walks the
//!   tail-call projection, where `become m::panic(x)` (a user function that is
//!   merely NAMED `panic`) is a refutation target; its candidate is PROVED, and
//!   it stood in for the SKIPPED `assert!` (its guard reads a loop-carried
//!   value) in the "one proved candidate per target block" count, so that
//!   reachable `assert!` was exempted. On the unfixed compiler `f`'s catch-all
//!   was published proved AND kernel-certified (the disjunction the kernel
//!   re-checked is the tail call's candidate alone), a binary calling `f(7)`
//!   built rc 0 under `-Ztrust-policy=certify`, and it panicked. A gate that
//!   merely examines the tail call does not close this — `m::panic` is
//!   registered panic-free, so it discharges — the exemption must be refused
//!   for such a body. Two rules now refuse it: the per-block exemption
//!   (NEW-EXEMPT-SPLIT, docs/KNOWN_HAZARDS.md, "the panic-callee exemption
//!   counted candidates, not blocks"), under which the skipped `assert!` block
//!   is a declined target block, and `panic_callee_exemption_holds`' refusal of
//!   any body with a tail call the refutation lane reads as a target.
//!   `f_control` (no tail call) is the unchanged control.
#![feature(explicit_tail_calls)]
#![expect(incomplete_features)]

#[cfg(any(default, certify))]
fn boom(x: u32) -> u32 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for
    //[default,certify]~| ERROR Trust strict verification failed for
    if x > 5 {
        panic!("boom");
    }
    x
}

#[cfg(any(default, certify))]
pub fn tail(x: u32) -> u32 {
    //[default]~^ WARN Trust Level 0 safety verification incomplete for
    //[default]~| WARN Trust verification advisory for
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for
    //[certify]~| ERROR Trust strict verification failed for
    become boom(x)
}

/// CONTROL: the same call without `become`, refused before and after.
#[cfg(any(default, certify))]
pub fn plain(x: u32) -> u32 {
    //[default]~^ WARN Trust Level 0 safety verification incomplete for
    //[default]~| WARN Trust verification advisory for
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for
    //[certify]~| ERROR Trust strict verification failed for
    boom(x)
}

/// Discharged, on the unfixed compiler, by `tail`'s false registration.
#[cfg(any(default, certify))]
pub fn calls_tail(x: u32) -> u32 {
    //[default]~^ WARN Trust Level 0 safety verification incomplete for
    //[default]~| WARN Trust verification advisory for
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for
    //[certify]~| ERROR Trust strict verification failed for
    tail(x)
}

#[cfg(tailcount)]
mod m {
    // Named like a panic entrypoint, and panic-free: it registers.
    pub fn panic(x: u32) -> u32 {
        x
    }
}

#[cfg(tailcount)]
pub fn f(x: u32) -> u32 {
    //[tailcount]~^ WARN Trust Level 0 safety verification incomplete for
    //[tailcount]~| WARN Trust verification advisory for
    if x > 10 && x < 5 {
        become m::panic(x)
    }
    let mut i = 0u32;
    let mut s = 0u32;
    while i != 3 {
        s ^= x;
        i = i.wrapping_add(1);
    }
    assert!(s != 7);
    x
}

/// CONTROL: the same body without the tail call, refused before and after.
#[cfg(tailcount)]
pub fn f_control(x: u32) -> u32 {
    //[tailcount]~^ WARN Trust Level 0 safety verification incomplete for
    //[tailcount]~| WARN Trust verification advisory for
    let mut i = 0u32;
    let mut s = 0u32;
    while i != 3 {
        s ^= x;
        i = i.wrapping_add(1);
    }
    assert!(s != 7);
    x
}
