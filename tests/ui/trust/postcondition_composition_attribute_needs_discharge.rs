//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Trust (postcondition composition — the ATTRIBUTE spelling's FALSE-PROVE
//! MACHINE, kept shut).
//!
//! The attribute half of
//! `postcondition_composition_preconditioned_needs_discharge.rs`, and it is the
//! load-bearing companion of
//! `postcondition_composition_attribute_at_call_site.rs`: the lane that file
//! opens is the same guarded lane, so it must be checked with the same negative.
//!
//! `positive_part` promises `*ret > 0` — but only for `x > 0`. Its body is the
//! identity, so the promise is FALSE for every `x <= 0`. `triple` calls it with
//! its own unconstrained parameter, so `x > 0` is not derivable at the call site
//! and the caller must learn NOTHING about `y`.
//!
//! There is a runtime witness: `triple(i32::MIN)` calls `positive_part(i32::MIN)`
//! (out of contract, so the promise does not apply), gets `i32::MIN` back, takes
//! the `y < 100` arm, and `y * 3` UNDERFLOWS. A caller that inherited `y > 0`
//! unconditionally would report the `Mul` obligation PROVED for a program that
//! panics.
//!
//! RE-MEASURED 2026-09-17. This file used to say that `VcKind::Precondition` is
//! hardcoded `L1Functional`, that `triple` declares no contract so it verifies at
//! `L0Safety`, and that the call-site precondition row is therefore FILTERED OUT
//! before any solver sees it. The last third of that is no longer true and should
//! not be repeated. The row is emitted, routed and DECIDED: the compiler reports
//! `[precond] FAILED (ay-in-process); counterexample: x = 0`. What the level
//! actually governs is which GATE counts the row — the Level 0 error counts 2
//! obligations not proved and omits the precondition, while the strict/certify
//! error counts all 3 and includes it. The row is outside the L0 gate, not
//! outside the solver.
//!
//! The distinction decides what is guarding this file. At L0 the thing standing
//! between here and the false prove is still the guard riding with the
//! assumption, exactly as before, because the L0 gate does not fail on a
//! precondition row. What is new is that the violation is now VISIBLE and stated
//! directly rather than argued only through the `Mul` row — and it is a true
//! refutation: `triple(0)` really does call `positive_part(0)`, and `0 > 0` is
//! false, so that call really is out of contract. Both rows are pinned below.
//!
//! POLICY RE-PINNED 2026-09-16. This file read its answer off the DEFAULT lane's
//! exit code, which stopped being the same question on 2026-09-14, when policy B
//! landed as ruled (docs/design/2026-07-25-completeness-gap-policy-ruling.md): an
//! unproved arithmetic row that keeps rustc's runtime check is REPORTED and the
//! build SUCCEEDS. `-Ztrust-policy=certify` is the lane where full static
//! discharge IS the contract, so that is where this question belongs and that is
//! what the flag above selects. It still earns its place: the `[assert]` row
//! stays `runtime-checked`, and certify is what refuses to tolerate it.
//!
//! OUTCOME RE-PINNED 2026-09-17, after `first-party/ay` moved to c187eb99d
//! (reports/2026-09-17-nine-ui-reds-follow-the-ay-pin-move.md establishes by A/B
//! that the VC formula is byte-identical across that move and only the solver's
//! ANSWER changed). The `Mul` row was `runtime-checked` and is now refuted with a
//! model, and the precondition row described above appeared with it.
//!
//! Here the `Mul` refutation is true of the PROGRAM and not only of the modular
//! encoding, which is worth recording because it does not follow automatically —
//! a model of an over-approximating encoding may assign a value the program can
//! never produce. The runtime witness in the paragraph above is real, measured
//! 2026-09-17 against stage1 with debug assertions on: `positive_part(i32::MIN)`
//! returns `i32::MIN` (a declared `requires` is not enforced at runtime, so an
//! out-of-contract call simply runs) and `triple(i32::MIN)` then panics in
//! `y * 3`. What the printed model itself shows is the other half of the claim —
//! it pairs `x = 0` with a freely chosen call result, which is the caller having
//! learned NOTHING about `y`, which is the property this file exists to pin.
//!
//! The two `NOTE` pins below carry that at row level, independently of which
//! policy decides the exit code: the obligation exists, it did not prove, and the
//! guarded clause did not travel.
//!
//! RE-PINNED 2026-09-28 (MEASURED on the Track B stage 1). The D5-A
//! call-destination screen now lets a solver model over a same-crate call
//! result stand only where an injected clause DETERMINES that result with no
//! `requires` guard (`trust_vcgen::generate::summary_pins_result`). Here
//! the clause arrives as `x > 0 -> *ret > 0` and this caller never establishes `x > 0`, so the `[overflow:mul]` model picks a
//! value the contract admits but no execution of `positive_part` returns (MEASURED
//! shape: `e9_requires_hypothesis_callee_reuse::use_outside_sub`, whose model
//! `r = 4` for `rmax(0, 5)` had the guard false). The row is therefore HELD — `UNKNOWN`
//! naming `positive_part`, a fail-closed gap with no runtime-check tolerance — where it
//! read `FAILED`. It still does not prove and the build still fails, which is
//! the whole of what this file asks.
#![feature(contracts)]
#![allow(incomplete_features)]

#[core::contracts::ensures(move |ret: &i32| *ret > 0)]
pub fn positive_part(x: i32) -> i32
    requires x > 0
{
    x
}

pub fn triple(x: i32) -> i32 {
//~^ ERROR Trust Level 0 safety verification incomplete for `postcondition_composition_attribute_needs_discharge::triple`
//~| ERROR Trust strict verification failed for `postcondition_composition_attribute_needs_discharge::triple`
//~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `postcondition_composition_attribute_needs_discharge::positive_part`
//~| NOTE [precond] FAILED
    let y = positive_part(x);
    if y < 100 { y * 3 } else { 0 }
}
