//@ needs-trust-verify
//@ edition: 2021
//@ revisions: drain weak_contract stale_after_reassign
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[drain] check-fail
//@[weak_contract] check-fail
//@[stale_after_reassign] check-fail
//@[stale_after_reassign] compile-flags: -Ztrust-policy=certify
//! **OPEN: a callee's proved postcondition is lost inside a loop body (Trust,
//! 2026-09-28).**
//!
//! `left - take(chunk, left)` needs only the fact `take`'s `ensures` gives at
//! this call: `t <= left`. No loop invariant is involved. It is refuted, with an
//! ungrounded witness, under the default policy. The semantic-guard walk
//! collapses every block it revisits on a loop's second pass to `true`, so the
//! block that subtracts loses the fact its one predecessor, the call,
//! establishes. `drain` is correct Rust, and this fixture pins the refutation as
//! it stands, so a fix must flip it to `check-pass`.
//!
//! Two fixes were built and refused by trust-vcgen's own suite. Both the meet at
//! the join and single-predecessor adoption PROVED a panicking program
//! (`escaped_local_seam_realmir::a7_the_temp_admission_refuses_every_non_carrier_spelling`).
//! Version tokens are static, and the collapse is what keeps a previous
//! iteration's fact away from a token the current iteration redefines. See the
//! comment at the P0-2 collapse in `semantic_guard.rs` and
//! `reports/2026-09-28-two-language-probe-sweep.md`.
//!
//! The two NEGATIVES are what any fix must keep refuted:
//! * `weak_contract`: `ensures result <= want` is true of the body but does not
//!   bound `t` by `left`;
//! * `stale_after_reassign`: `left` is halved between the call and the
//!   subtraction, so `t <= left` is about the OLD `left`.
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14): on the merged stage 1 the
//! default policy no longer refutes `stale_after_reassign` — its `[overflow:sub]` row
//! (which does panic: `left = 3, chunk = 3`) is published `runtime_checked` from the
//! native lane, which the default policy reports and builds (the overflow check stays
//! in the binary). The in-process SAT query is still found (`t` is unconstrained once
//! the loop drops the call's fact) but no longer surfaces as FAILED. Lost refutation
//! power, recorded; not a proof. The negative is therefore pinned under `certify`,
//! where a `runtime_checked` row is fatal and only a PROOF would build: what this
//! negative must catch.

#[cfg(any(drain, stale_after_reassign))]
pub fn take(want: u64, avail: u64) -> u64
    ensures result <= avail
{
    if want < avail { want } else { avail }
}

#[cfg(drain)]
pub fn drain(total: u64, chunk: u64) -> u64 {
    //[drain]~^ ERROR Trust
    let mut left = total;
    while left > 0 {
        let t = take(chunk, left);
        left = left - t;
    }
    left
}

#[cfg(weak_contract)]
pub fn take(want: u64, avail: u64) -> u64
    ensures result <= want
{
    if want < avail { want } else { avail }
}

#[cfg(weak_contract)]
pub fn drain(total: u64, chunk: u64) -> u64 {
    //[weak_contract]~^ ERROR Trust
    let mut left = total;
    while left > 0 {
        let t = take(chunk, left);
        left = left - t;
    }
    left
}

#[cfg(stale_after_reassign)]
pub fn drain(total: u64, chunk: u64) -> u64 {
    //[stale_after_reassign]~^ ERROR Trust
    let mut left = total;
    while left > 0 {
        let t = take(chunk, left);
        left = left / 2;
        left = left - t;
    }
    left
}
