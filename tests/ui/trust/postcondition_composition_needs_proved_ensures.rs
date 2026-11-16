//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Trust (postcondition composition — the LAUNDERING channel, kept shut).
//!
//! A caller may assume a callee's `ensures` ONLY IF the callee's own
//! postcondition obligation was discharged. Assuming a DECLARED-but-unproved
//! `ensures` is not a completeness nicety, it is a false-PROVE generator: the
//! callee writes any proposition it likes and every caller inherits it.
//!
//! `bad`'s `ensures` is false — `bad(0) == 0`, not `>= 1000` — so its own
//! postcondition rows come back unproved. This file pins BOTH halves of the
//! consequence:
//!
//!  * `bad` itself must fail (the first expected error), and
//!  * `caller` must STILL fail its `Mul` obligation (the second).
//!
//! The second is the load-bearing one, and it is why the body is shaped this
//! way rather than as a plain `y * 3`. If `caller` had inherited `y >= 1000`,
//! the guard `y < 100` would be contradictory and the `y * 3` obligation would
//! prove VACUOUSLY — a green row about an unreachable path, with no symptom
//! anywhere. A `check-fail` on `bad` alone would not have seen that; the
//! `caller` error is the assertion that the fact never travelled.
//!
//! POLICY RE-PINNED 2026-09-16. This file measures whether the caller DISCHARGES
//! its obligation, and it read that off the DEFAULT lane's exit code. That stopped
//! being the same question on 2026-09-14, when policy B landed as ruled
//! (docs/design/2026-07-25-completeness-gap-policy-ruling.md): an unproved
//! arithmetic row that keeps rustc's runtime check is REPORTED and the build
//! SUCCEEDS. `-Ztrust-policy=certify` is the lane where full static discharge IS
//! the contract, so that is where this question belongs and that is what the flag
//! above selects.
//!
//! OUTCOME RE-PINNED 2026-09-17, after `first-party/ay` moved to c187eb99d
//! (reports/2026-09-17-nine-ui-reds-follow-the-ay-pin-move.md establishes by A/B
//! that the VC formula is byte-identical across that move and only the solver's
//! ANSWER changed). The `Mul` row used to read `runtime-checked`: the solver
//! declined the query, so the compiler kept rustc's check. The stronger solver
//! DECIDES it now, and the row comes back refuted, with a model.
//!
//! That is a sharper demonstration of this file's claim, not a weaker one. The
//! model picks a large negative value for the call result while `bad`'s clause
//! demands `result >= 1000` — a choice available to the solver only because the
//! clause never reached the caller. Had it travelled, `y >= 1000` and the guard
//! `y < 100` would be jointly unsatisfiable and this row would have come back
//! PROVED, vacuously, on an unreachable path: exactly the silent green the body
//! is shaped to catch. `runtime-checked` said only "the caller could not show
//! it"; a refutation carrying that model says "the caller did not have the
//! fact", which is what this file actually asserts.
//!
//! The refutation is true of the PROGRAM too, which is worth stating separately
//! because it does not follow automatically. `bad` is the identity, so
//! `caller(-715827883)` really reaches `y * 3` and really overflows (measured
//! 2026-09-17 against stage1 with debug assertions on: it panics). The model the
//! compiler prints is NOT that execution — it pairs `x = 0` with a freely chosen
//! call result, because modular verification leaves a callee's return
//! unconstrained once its clause is unusable. That model is not an execution,
//! so since D5-A (2026-09-24) the row is reported `UNKNOWN` — "generic solver
//! counterexample withheld: query depends on the unmodeled return of same-crate
//! `…::bad`" — rather than `FAILED`. The verdict that matters is unchanged:
//! `caller` is still refused, because a held refutation is a fail-closed gap
//! with no runtime-check tolerance.
//!
//! One consequence for whoever reads the flags line next: a held row fails the
//! DEFAULT lane as well, so `certify` is not what makes this file red. It is
//! still the right lane to ask the question in, and it is still what keeps the
//! `[assert]` row's retained runtime check from being tolerated silently.

pub fn bad(x: i32) -> i32
//~^ ERROR Trust strict verification failed for `postcondition_composition_needs_proved_ensures::bad`
    ensures result >= 1000
{
    x
}

pub fn caller(x: i32) -> i32 {
//~^ ERROR Trust Level 0 safety verification incomplete for `postcondition_composition_needs_proved_ensures::caller`
//~| ERROR Trust strict verification failed for `postcondition_composition_needs_proved_ensures::caller`
//~| NOTE [overflow:mul] UNKNOWN
    let y = bad(x);
    if y < 100 { y * 3 } else { 0 }
}
