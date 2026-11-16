//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Trust (postcondition composition, slice 2 — the VACUITY guard).
//!
//! Byte-for-byte the caller of
//! `postcondition_composition_preconditioned_at_call_site.rs`, including the
//! `if x > 0` arm that DISCHARGES the callee's `requires`. Only the `ensures`
//! changes: it is weakened to a clause that says nothing about how negative the
//! result can be.
//!
//! So the antecedent is discharged, the guarded fact fires, the caller really
//! does learn `y <= 1000000` — and `y * 3` is STILL a real underflow at large
//! negative `y`, so it must still FAIL.
//!
//! Without this file the positive test cannot tell "the caller USED the
//! postcondition" from "the caller-side lane stopped emitting the obligation".
//! Composition that proves regardless of what the clause SAYS is not
//! composition, it is suppression — and a guarded lane can suppress in one more
//! way than an unguarded one, because it touches the injection site itself.
//!
//! POLICY RE-PINNED 2026-09-16 — HISTORICAL. Superseded by the 2026-09-17 block
//! at the end of this comment: the row it describes is no longer runtime-checked.
//! It is kept because it records why the file sits on the `certify` lane.
//! This file measures whether the caller DISCHARGES
//! its obligation, and it read that off the DEFAULT lane's exit code. That stopped
//! being the same question on 2026-09-14, when policy B landed as ruled
//! (docs/design/2026-07-25-completeness-gap-policy-ruling.md): an unproved
//! arithmetic row that keeps rustc's runtime check is now REPORTED and the build
//! SUCCEEDS. The row here is exactly that — `[overflow:mul] runtime-checked:
//! compiler retained the existing overflow check because the proof is not yet
//! static` — so the default lane stopped failing while the obligation stayed
//! exactly as unproved as before.
//!
//! `-Ztrust-policy=certify` is the lane where full static discharge IS the
//! contract, so that is where this question belongs and that is what the flag
//! above now selects. Nothing about the property changed and nothing was blessed:
//! the same row, still unproved, still named in the same two errors.
//!
//! The vacuity guard survives the move, which is the thing to check before
//! trusting it. If the caller-side lane stopped EMITTING the obligation, the
//! body would report zero obligations, certify would have nothing to refuse, and
//! this file would go red on the missing errors — the same way it would have on
//! the default lane. What the move gives up is detecting a row that silently
//! becomes runtime-checked-and-tolerated, and the `NOTE` pin below is there so
//! that is not given up either: it asserts the row EXISTS and is unproved,
//! independently of which policy decides the exit code.
//!
//! RE-BLESSED 2026-09-17 — THE ROW BECAME A REFUTATION, AND THE GUARD HELD IN THE
//! MODEL. `first-party/ay` moved to c187eb99d and the solver now decides the query
//! it used to decline. Measured on stage1 `trustc` with exactly the flags above,
//! the row reads
//!
//!     [overflow:mul] FAILED (ay-in-process); counterexample:
//!     _4 = true, _5 = -715827883, _6 = true, x = 1
//!
//! where it read `[overflow:mul] runtime-checked` before. The VC handed to the
//! solver is byte-identical across the move — A/B in
//! reports/2026-09-17-nine-ui-reds-follow-the-ay-pin-move.md — so only the answer
//! changed.
//!
//! THE CHECK THIS FILE EXISTS TO SURVIVE. Unlike its unguarded sibling
//! `postcondition_composition_preconditioned_needs_discharge.rs`, this caller
//! DISCHARGES the callee's `requires x > 0`. A counterexample that reached the
//! `Mul` on a path where that precondition did NOT hold would mean the guarded
//! assumption had been dropped and the verdict would be WRONG — a verifier defect,
//! not a stale pin. It was checked against the body's own MIR rather than assumed:
//! `_4` is the `x > 0` guard, `_5` is what `positive_part` returns, `_6` is
//! `y < 100`. The model sets `x = 1` and `_4 = true`, so it enters the guarded arm
//! and the precondition holds. The guard survived. The verdict stands.
//!
//! What the model then exploits is exactly the weakening under test: the clause
//! bounds the result only from ABOVE, and `-715827883 <= 1000000`, so
//! `_5 = -715827883` is consistent with everything the caller is entitled to
//! assume. `-715827883 * 3` is `-2147483649`, one past `i32::MIN`. It is not an
//! execution of THIS file's concrete callee body, which returns a positive value
//! for `x > 0` — modular verification reads a callee as its contract, and the
//! contract is what a vacuity guard must be measured against.
//!
//! WHICH BOUNDARY THIS NOW DEMONSTRATES — AND WHAT THIS FILE ALONE CANNOT SHOW.
//! Before, the file said "the obligation survives as an unproved row, so the
//! injection site did not suppress it". The row is now a REFUTATION with a
//! witness rather than a retained runtime check, which is a strictly more
//! informative negative result.
//!
//! It is tempting to read that as "the clause was injected AND USED — the model
//! had to satisfy `result <= 1000000` to be produced at all". That reading was
//! written here on 2026-09-17 and DISPROVED the same day, by deletion: removing
//! `ensures result <= 1000000` from `positive_part` outright drops the callee's
//! own report from `3 proved ... out of 4` to `0 proved ... out of 1`, and the
//! caller's output is BYTE-IDENTICAL — same counterexample `_4 = true,
//! _5 = -715827883, _6 = true, x = 1`, same `Level 0 summary`, same
//! `1 trusted, 1 certified, 1 failed`. The witness satisfies an upper-bound-only
//! clause VACUOUSLY, so nothing local distinguishes "clause injected but too
//! weak" from "clause never injected". That is precisely the confusion this
//! file's own header warns about: a dropped clause and a never-emitted
//! obligation look identical from a summary line.
//!
//! THE DISCRIMINATION IS RELATIONAL, NOT LOCAL. What shows injection is
//! load-bearing is the contrast with the positive companion
//! `postcondition_composition_preconditioned_at_call_site.rs` — same guard, but a
//! STRONG `ensures result > 0` — which reports `3 proved, 0 failed` and exits 0.
//! Strong clause proves, weak clause refutes, no clause refutes: the first-vs-second
//! pair is the measurement, and neither file carries it alone. Move one and the
//! other stops meaning anything.
//!
//! Measured today the default lane emits the same two errors as `certify`, so
//! `-Ztrust-policy=certify` is no longer load-bearing and is kept deliberately: if
//! the solver weakens back to a retained runtime check it keeps the build red while
//! the pinned note below goes red on the changed text.
//!
//! RE-PINNED 2026-09-28 (MEASURED on the Track B stage 1). The D5-A
//! call-destination screen now lets a solver model over a same-crate call
//! result stand only where an injected clause DETERMINES that result with no
//! `requires` guard (`trust_vcgen::generate::summary_pins_result`). Here
//! the guarded `x > 0 -> result <= 1000000` bounds `y` only from above, so the `[overflow:mul]` model picks a
//! value the contract admits but no execution of `positive_part` returns (MEASURED
//! shape: `p_falsefail::dead_else_s`). The row is therefore HELD — `UNKNOWN`
//! naming `positive_part`, a fail-closed gap with no runtime-check tolerance — where it
//! read `FAILED`. It still does not prove and the build still fails, which is
//! the whole of what this file asks.

pub fn positive_part(x: i32) -> i32
    requires x > 0
    ensures result <= 1000000
{
    if x > 1000000 { 1000000 } else { x }
}

pub fn triple(x: i32) -> i32 {
//~^ ERROR Trust Level 0 safety verification incomplete for `postcondition_composition_preconditioned_upper_bound_only::triple`
//~| ERROR Trust strict verification failed for `postcondition_composition_preconditioned_upper_bound_only::triple`
//~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `postcondition_composition_preconditioned_upper_bound_only::positive_part`
    if x > 0 {
        let y = positive_part(x);
        if y < 100 { y * 3 } else { 0 }
    } else {
        0
    }
}
