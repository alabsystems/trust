//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Trust (postcondition composition — the LAUNDERING channel, ATTRIBUTE
//! spelling, kept shut).
//!
//! A caller may assume a callee's `ensures` ONLY IF the callee's own
//! postcondition obligation was DISCHARGED. Assuming a declared-but-unproved
//! `ensures` is not a completeness nicety, it is a false-PROVE generator: the
//! callee writes any proposition it likes and every caller inherits it. Making
//! the `#[core::contracts::ensures]` spelling compose must not open a second
//! door onto that room, so both lanes are pinned here.
//!
//! Each `ensures` below is FALSE (`bad(0) == 0`, `bad_pre(5) == 5`, neither is
//! `>= 1000`), so each callee's own postcondition rows come back unproved and
//! neither clause may travel.
//!
//!  * `bad`/`caller` — precondition-FREE, the lane that already worked.
//!  * `bad_pre`/`caller_pre` — PRECONDITIONED, and the load-bearing half: this
//!    is the lane the attribute fix newly opens. Its caller DISCHARGES the
//!    antecedent (`if x > 0`), so the guard is satisfied and the only thing left
//!    standing between this file and a false prove is the callee's own verdict.
//!
//! Both callers are shaped `if y < 100 { y * 3 }` rather than a plain `y * 3`
//! for the same reason: had either inherited `y >= 1000`, the guard would be
//! contradictory and the `Mul` would prove VACUOUSLY — a green row about an
//! unreachable path, with no symptom anywhere. The caller errors, not the callee
//! errors, are the assertion that the fact never travelled.
//!
//! POLICY RE-PINNED 2026-09-16. This file read its answer off the DEFAULT lane's
//! exit code, which stopped being the same question on 2026-09-14, when policy B
//! landed as ruled (docs/design/2026-07-25-completeness-gap-policy-ruling.md): an
//! unproved arithmetic row that keeps rustc's runtime check is REPORTED and the
//! build SUCCEEDS. `-Ztrust-policy=certify` is the lane where full static
//! discharge IS the contract, so that is where this question belongs and that is
//! what the flag above selects.
//!
//! OUTCOME RE-PINNED 2026-09-17, after `first-party/ay` moved to c187eb99d
//! (reports/2026-09-17-nine-ui-reds-follow-the-ay-pin-move.md establishes by A/B
//! that the VC formula is byte-identical across that move and only the solver's
//! ANSWER changed). Both callers' `Mul` rows were `runtime-checked`; the stronger
//! solver decides them now and both came back refuted, with models (held as
//! `UNKNOWN` since D5-A — see below).
//!
//! Both models say the thing this file is trying to say, and say it positively.
//! Each picks a large negative value for the call result while the clause on the
//! callee demands `*ret >= 1000` — a choice open to the solver only because the
//! clause never reached the caller. Had either clause travelled, `y >= 1000`
//! against the guard `y < 100` would have been unsatisfiable and that row would
//! have come back PROVED, vacuously, on an unreachable path: the silent green
//! both bodies are shaped to catch. `runtime-checked` only ever said "the caller
//! could not show it"; these models say "the caller did not have the fact".
//!
//! The preconditioned half is now the sharper of the two, which is the right way
//! round given it is the lane the attribute fix opened. Its model pins `x = 1`,
//! so the antecedent `x > 0` IS established at the call site and the guard rode
//! with the assumption correctly — and the clause still did not travel. Its other
//! two rows prove (one kernel-certified), so the failure is isolated to the one
//! obligation that depends on the undischarged clause. Compare
//! `postcondition_composition_attribute_needs_discharge.rs`, where the antecedent
//! is NOT established and the call-site precondition row is itself refuted.
//!
//! One honest limit on the word `counterexample`, so nobody carries it into a bug
//! report. For `caller` the refutation is true of the program: `bad` is the
//! identity, so `caller(-715827883)` really overflows (measured 2026-09-17
//! against stage1 with debug assertions on: it panics). For `caller_pre` it is
//! not — `bad_pre` is also the identity, so `x > 0` and `y < 100` confine `y` to
//! `1..=99` and the largest value `caller_pre` ever produces is 297, with no
//! overflow at any input. That "refutation" was of the MODULAR ENCODING, in
//! which an unusable clause leaves the callee's return free — the false
//! refutation D5-A (2026-09-24) closed: a model that chooses an unmodeled
//! same-crate call result is not an execution, so both rows now read `UNKNOWN`
//! ("generic solver counterexample withheld: query depends on the unmodeled
//! return of same-crate `…::bad`"). Both callers are still refused: a held
//! refutation is a fail-closed gap with no runtime-check tolerance.
//!
//! The `NOTE` pins below carry this at row level on both halves, independently of
//! which policy decides the exit code: the obligation exists, it did not prove,
//! and the undischarged clause did not travel.
#![feature(contracts)]
#![allow(incomplete_features)]

#[core::contracts::ensures(move |ret: &i32| *ret >= 1000)]
pub fn bad(x: i32) -> i32 {
//~^ ERROR Trust strict verification failed for `postcondition_composition_attribute_needs_proved_ensures::bad`
    x
}

pub fn caller(x: i32) -> i32 {
//~^ ERROR Trust Level 0 safety verification incomplete for `postcondition_composition_attribute_needs_proved_ensures::caller`
//~| ERROR Trust strict verification failed for `postcondition_composition_attribute_needs_proved_ensures::caller`
//~| NOTE [overflow:mul] UNKNOWN
    let y = bad(x);
    if y < 100 { y * 3 } else { 0 }
}

#[core::contracts::ensures(move |ret: &i32| *ret >= 1000)]
pub fn bad_pre(x: i32) -> i32
//~^ ERROR Trust strict verification failed for `postcondition_composition_attribute_needs_proved_ensures::bad_pre`
    requires x > 0
{
    x
}

pub fn caller_pre(x: i32) -> i32 {
//~^ ERROR Trust Level 0 safety verification incomplete for `postcondition_composition_attribute_needs_proved_ensures::caller_pre`
//~| ERROR Trust strict verification failed for `postcondition_composition_attribute_needs_proved_ensures::caller_pre`
//~| NOTE [overflow:mul] UNKNOWN
    if x > 0 {
        let y = bad_pre(x);
        if y < 100 { y * 3 } else { 0 }
    } else {
        0
    }
}
