//@ revisions: off on
//@ needs-trust-verify
//@[off] compile-flags: -Ztrust-verify=off
//@[on] compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@[on] normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! TG3 (COMPILE-TIME-FACTS-1, 2026-11-05) SUPERSEDES the history below: the
//! unverified-lane allowance it describes is gone. With verification off the
//! kernel-only lane E6-imports the cited functions' bodies, so the `off`
//! revision now judges every `result` clause exactly as `on` does — the
//! "NOT checked" note is never printed, and a false `result` citation is a hard
//! error in both revisions. The two revisions stay so that this parity is pinned.
//!
//! CLOSE NEGATIVE TWIN of `native_clause_citation_result_unverified_nat_lift`
//! (d1, 2026-09-28): what running the ∀-`result` fallback in the discharge
//! rung's mode must NOT buy, and the diagnostics it must no longer get wrong.
//!
//! BOTH revisions require EVERY error to be annotated — there is deliberately no
//! `dont-require-annotations: ERROR` — so each row pins both directions at once.
//! Every citation message HEAD is pinned, not just "an error occurred": before
//! the fix every row below printed the same false carrier message ("the argument
//! is a `u16` term") in BOTH lanes (MEASURED, critique probes q1/q4/q5 and
//! report variants d/f/h/i, pack 4d9a20e3daf), so a pin on the head is what makes
//! the `on` revision discriminate too (B2).
//!
//!   * `missing_cast`, `narrowing` — type errors. Still refused in BOTH lanes,
//!     now with the lift table's own refusal as the PRIMARY message (before, it
//!     rode along as a secondary note in `on` and was absent in `off`).
//!   * `signed_to_nat` — GUARD-WIDENING DETECTOR: an `i64` has no `Nat`. A fix
//!     that relaxed fragment refusals with verification off (instead of fixing
//!     the mode) would turn this `off` error into a "NOT checked" note.
//!   * `wrong_theorem_result_free` — a mismatch on a clause with no `result` is
//!     judged in both lanes; the allowance is for a goal the lane cannot build.
//!   * `mutant` — the body disagrees with the theorem. `off`: NOT checked, and
//!     says so (the honest cost, as for `false_result_claim` in the unlifted
//!     twin). `on`: the error now LEADS with the postcondition goal the theorem
//!     failed, not with the ∀-`result` reading (B2).
//!   * `missing_theorem`, `cites_a_definition` — body-independent facts about
//!     the citation stay hard errors in both lanes, with their own messages.
//!   * `signed_seeded` — `x as int` over `i32` names the seeded lift model. The
//!     fallback must seed it (into a clone) before grading: unseeded, the goal
//!     does not type and `off` would hard-error "does not typecheck" instead of
//!     answering "NOT checked". `on`: the theorem does not prove the
//!     postcondition, a hard error led by that goal.
//!
//! `on` rows other than the citation's own also carry the per-function
//! strict-verification errors the unproved postcondition leaves behind; those
//! were MEASURED for every `spec_ge`/`spec_nonneg` shape here except
//! `signed_to_nat`, where they are INFERRED from the same shape over `u16`.
//! The program-call residual is `native_clause_citation_call_unverified_residual`,
//! which must pass UNCHANGED.

clean {
    def spec_ge (n : Nat) : Bool :=
        @Decidable.decide (Nat.le 512 n) (Nat.decLe 512 n)
    def dec_ge (n : UInt16) : Bool :=
        @Decidable.decide (LE.le (UInt16.ofNat 512) n) (instDecidableUInt16Le (UInt16.ofNat 512) n)
    theorem dec_is_spec : forall (n : UInt16),
        Eq (dec_ge n) (spec_ge (UInt16.toNat n)) :=
        fun n => Eq.refl (dec_ge n)
    theorem dec_refl : forall (n : UInt16), Eq (dec_ge n) (dec_ge n) :=
        fun n => Eq.refl (dec_ge n)
    theorem nat_refl : forall (n : Nat), Eq (spec_ge n) (spec_ge n) :=
        fun n => Eq.refl (spec_ge n)

    def spec_nonneg (n : Int) : Bool :=
        @Decidable.decide (Int.le 0 n) (Int.decLe 0 n)
    theorem taut_bool : forall (b : Bool), Eq b b := fun b => Eq.refl b
}

pub fn missing_cast(x: u16) -> bool
//[on]~^ ERROR Trust Level 0 safety verification incomplete for `native_clause_citation_result_unverified_nat_lift_false::missing_cast`
//[on]~| ERROR Trust strict verification failed for `native_clause_citation_result_unverified_nat_lift_false::missing_cast`
    ensures result == spec_ge(x) by dec_is_spec
    //~^ ERROR citation `dec_is_spec` cannot be validated because this clause is outside the exact statement fragment: `x` is a `u16` term at a `nat` position
{
    512 <= x
}

pub fn narrowing(x: u16) -> bool
//[on]~^ ERROR Trust Level 0 safety verification incomplete for `native_clause_citation_result_unverified_nat_lift_false::narrowing`
//[on]~| ERROR Trust strict verification failed for `native_clause_citation_result_unverified_nat_lift_false::narrowing`
    ensures result == dec_ge(x as nat) by dec_refl
    //~^ ERROR citation `dec_refl` cannot be validated because this clause is outside the exact statement fragment: `x as nat` is a `nat` term where the declared carrier is `UInt16`
{
    512 <= x
}

pub fn signed_to_nat(x: i64) -> bool
//[on]~^ ERROR Trust Level 0 safety verification incomplete for `native_clause_citation_result_unverified_nat_lift_false::signed_to_nat`
//[on]~| ERROR Trust strict verification failed for `native_clause_citation_result_unverified_nat_lift_false::signed_to_nat`
    ensures result == spec_ge(x as nat) by dec_is_spec
    //~^ ERROR is an `i64`, which can be negative and has no `Nat` value
{
    x >= 512
}

pub fn wrong_theorem_result_free(x: u16) -> bool
//[on]~^ ERROR Trust Level 0 safety verification incomplete for `native_clause_citation_result_unverified_nat_lift_false::wrong_theorem_result_free`
//[on]~| ERROR Trust strict verification failed for `native_clause_citation_result_unverified_nat_lift_false::wrong_theorem_result_free`
    ensures dec_ge(x) == spec_ge(x as nat) by nat_refl
    //~^ ERROR citation `nat_refl` failed the strict Clean statement/certification audit
{
    512 <= x
}

pub fn mutant(x: u16) -> bool
//[on]~^ ERROR Trust Level 0 safety verification incomplete for `native_clause_citation_result_unverified_nat_lift_false::mutant`
//[on]~| ERROR Trust strict verification failed for `native_clause_citation_result_unverified_nat_lift_false::mutant`
    ensures result == spec_ge(x as nat) by dec_is_spec
    //~^ ERROR citation `dec_is_spec` failed the strict Clean statement/certification audit against this postcondition with `result` bound to the imported definition of `mutant`
{
    513 <= x
}

pub fn missing_theorem(x: u16) -> bool
//[on]~^ ERROR Trust Level 0 safety verification incomplete for `native_clause_citation_result_unverified_nat_lift_false::missing_theorem`
//[on]~| ERROR Trust strict verification failed for `native_clause_citation_result_unverified_nat_lift_false::missing_theorem`
    ensures result == spec_ge(x as nat) by no_such_thm
    //~^ ERROR cited theorem `no_such_thm` is not registered
{
    512 <= x
}

pub fn cites_a_definition(x: u16) -> bool
//[on]~^ ERROR Trust Level 0 safety verification incomplete for `native_clause_citation_result_unverified_nat_lift_false::cites_a_definition`
//[on]~| ERROR Trust strict verification failed for `native_clause_citation_result_unverified_nat_lift_false::cites_a_definition`
    ensures result == spec_ge(x as nat) by spec_ge
    //~^ ERROR cited declaration `spec_ge` is
{
    512 <= x
}

pub fn signed_seeded(x: i32) -> bool
//[on]~^ ERROR Trust Level 0 safety verification incomplete for `native_clause_citation_result_unverified_nat_lift_false::signed_seeded`
//[on]~| ERROR Trust strict verification failed for `native_clause_citation_result_unverified_nat_lift_false::signed_seeded`
    ensures result == spec_nonneg(x as int) by taut_bool
    //~^ ERROR citation `taut_bool` failed the strict Clean statement/certification audit against this postcondition with `result` bound to the imported definition of `signed_seeded`
{
    0 <= x
}

fn main() {
    let _ = missing_cast(1);
    let _ = narrowing(2);
    let _ = signed_to_nat(3);
    let _ = wrong_theorem_result_free(4);
    let _ = mutant(5);
    let _ = missing_theorem(6);
    let _ = cites_a_definition(7);
    let _ = signed_seeded(8);
}
