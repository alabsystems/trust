//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=strict --crate-type lib
//@ check-pass
//! Trust (postcondition composition): a callee's `ensures` must be ASSUMED at
//! the caller, not merely CHECKED on the callee.
//!
//! Before this lane, `clamp_low` verified and `triple` failed with
//! `arithmetic overflow (Mul)`: the caller learned nothing about `y` from the
//! call, and the `y < 100` guard leaves `y` unbounded BELOW, so `y * 3`
//! underflows at large negative `y`. The obligation is genuinely unprovable
//! without the postcondition — see
//! `postcondition_composition_upper_bound_only.rs`, which keeps this exact
//! body and weakens the `ensures` to the upper half, and still fails.
//!
//! The caller-side assumption is minted only when THIS compilation has already
//! discharged the callee's own postcondition obligation
//! (`callee_postconditions_are_reusable` in `trust_verify.rs`); the companion
//! `postcondition_composition_needs_proved_ensures.rs` is the negative half.
//!
//! # 2026-09-18 — THE ONE MEASURED COST OF THE a7 PER-PATH SPLIT
//!
//! `clamp_low` is the a7 three-arm chain, and its `Return` block's second
//! predecessor is the `goto`-only JOIN of the inner `if` — reached by two guard
//! paths. The a7 lane makes such a predecessor emit one FLAT row per path
//! instead of one `Or` of two, so this function's obligation count moved
//! 3 -> 4. That part is bookkeeping. The part that is NOT is recorded here,
//! because it is a CAPABILITY LOSS and it must be a decision rather than a
//! surprise:
//!
//! ```text
//! BEFORE (merged `Or` row, measured with POSTCONDITION_PATH_SPLIT_CAP = 1):
//!   vc:…:clamp_low:postcondition:0  proved  trust-full-verifier  trust-mc / Sound / SoundAnalysis
//!   vc:…:clamp_low:postcondition:1  proved  ay-in-process        clean-kernel / Certified / KernelRechecked
//!   obligation:…:clamp_low:postcondition:0  proved  trust-exact-source-clause-discharge
//!
//! AFTER (three flat per-path rows):
//!   vc:…:clamp_low:postcondition:0..2  proved  trust-full-verifier  trust-mc / Sound / SoundAnalysis
//!   obligation:…:clamp_low:postcondition:0  proved  trust-exact-source-clause-discharge
//! ```
//!
//! The disjunctive row got NO trust-mc PDR receipt (that is the a7 defect), fell
//! through to the `ay` lane, and THAT result was re-checked by the Clean CIC
//! kernel — so this function used to carry one `Certified` row. Every flat
//! per-path row is proved by trust-mc PDR directly, which answers first, so the
//! kernel re-check never runs and the `of which 1 kernel-certified` note leaves
//! this function's report (it stays on `triple`, whose safety row is unaffected).
//!
//! The user-visible verdict is UNCHANGED — `4 proved / 4`, the source clause
//! still discharges, and `triple` still composes — and the direction is
//! fail-closed: `Trusted` is a WEAKER claim than `Certified`, never a stronger
//! one. But it is a real loss of one kernel-certified row, traded for making the
//! same clause's rows provable at all on the `if`-expression spelling (the a7
//! frontier fixture). Whether the router should still attempt the kernel
//! re-check on a row trust-mc has already proved is an OWNER decision, recorded
//! as RULING C in `docs/STRICT_VERIFICATION_FRAGMENT.md` §19.3. Do not "fix"
//! this by reverting the note into the expected output.
//!
//! # 2026-09-20 — RULING C IS CLOSED, AND ITS STATED MECHANISM WAS WRONG
//!
//! **"the kernel re-check never runs" is false.** `certify_all` calls
//! `trust_certify::certify_vc` on EVERY `Proved` row whatever engine proved it,
//! and `ResultProofAuthority::KernelCertified` is minted from nothing but that
//! call. Measured on packed `trustc 1.99.0-dev (379912412 2026-09-19)` with
//! `TRUST_CERTIFY_TRACE=1`: all three split rows ENTER the producer and MISS it.
//! Who answered first never mattered; the producer could not reach the shape.
//!
//! Nor was the shape reachable before the split. At
//! `POSTCONDITION_PATH_SPLIT_CAP = 1` the FLAT `x < 0` row is uncertified too —
//! only the merged `Or` row certified, because
//! `certify_disjunctive_contradiction` is the one lane that distributes the
//! negated range conjunction and it returns `None` at its
//! `or_candidates.is_empty()` gate on a flat pool. So the split did not break a
//! working lane: it replaced the one shape the producer could reach with three
//! of a shape it could not.
//!
//! `trust_certify::certify_singleton_disjunction_retry` re-presents a flat
//! violation to that same engine as a ONE-ARM disjunction (`Or([F])` is `F`, and
//! `build_or_prop` emits a one-element list as the arm's own proposition, so the
//! kernel term carries no wrapper). All THREE per-path rows now certify — more
//! than the one the merged shape carried — so the note below reads
//! `of which 3 kernel-certified`, and the a7 capability is kept whole.
//! Measurements and the negative twins:
//! `crates/trust-vcgen/tests/per_path_postcondition_kernel_recheck.rs`.

pub fn clamp_low(x: i32) -> i32
    ensures result >= 0 && result <= 1000000
{
    if x < 0 {
        0
    } else if x > 1000000 {
        1000000
    } else {
        x
    }
}

pub fn triple(x: i32) -> i32 {
    let y = clamp_low(x);
    if y < 100 { y * 3 } else { 0 }
}
