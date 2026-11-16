//@ revisions: copy_then_write mut_param_copy pointee_copy pointee_entry contracted_loop_without_backedge
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Review round 43 (2026-10-02), each PROVED and kernel-certified at default flags
//! before, each refuted by a run.
//! `copy_then_write` / `mut_param_copy` / `pointee_copy`: `let e = y; y = 5; e`
//! returns the OLD `y`, but the return pins took `y`'s last assignment (after the
//! copy) or stamped the bare pin at the return point, so `ensures result == 5`
//! held. `pointee_entry`: `result == *x` over `let e = *x; *x = 0; e` is false
//! whether `*x` means the entry or the final pointee (docs/DECISION_QUEUE.md D17),
//! and the same pins proved it. `contracted_loop_without_backedge`: the outer `loop` has no back
//! edge of its own, and the uncontracted inner `while` inherited its scope stamp,
//! so `invariant k == 0` was checked at the inner loop head (k is 200 at the
//! outer one).
#![allow(unused_assignments, unused_variables)]

#[cfg(copy_then_write)]
pub fn f(a: u8) -> u8 //[copy_then_write]~ ERROR verification
    ensures result == 5
{
    let mut y = a;
    let e = y;
    y = 5;
    std::hint::black_box(y);
    e
}

#[cfg(mut_param_copy)]
pub fn f(mut x: u8) -> u8 //[mut_param_copy]~ ERROR verification
    ensures result == 5
{
    let e = x;
    x = 5;
    std::hint::black_box(x);
    e
}

#[cfg(pointee_copy)]
pub fn f(x: &mut u8) -> u8 //[pointee_copy]~ ERROR verification
    ensures result == 5
{
    let e = *x;
    *x = 5;
    e
}

#[cfg(pointee_entry)]
pub fn f(x: &mut u8) -> u8 //[pointee_entry]~ ERROR verification
    ensures result == *x
{
    let e = *x;
    *x = 0;
    e
}

#[cfg(contracted_loop_without_backedge)]
pub fn f(n: u8) -> u8 { //[contracted_loop_without_backedge]~ ERROR verification
    let mut k: u8 = 200;
    let mut j: u8 = 0;
    loop
        invariant k == 0
    {
        k = 0;
        while j < n {
            j += 1;
        }
        break;
    }
    k
}
