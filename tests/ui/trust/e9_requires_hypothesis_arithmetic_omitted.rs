//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//@ dont-require-annotations: NOTE
//! A1 — N-A3, THE FALSE-ACCEPT GUARD, and P-A2, the disclosure.
//!
//! This function declares TWO preconditions. Exactly one of them may become a
//! kernel hypothesis.
//!
//! `b <= a` is carried. `a + b > 10` is NOT, and the reason is not
//! conservatism: in Clean, `+` on `UInt64` WRAPS, while callers are charged the
//! non-wrapping reading. At `a = u64::MAX, b = 1` the charged reading is
//! satisfied and the Clean reading is refuted, so `F_R ⇏ P_R` — carrying it
//! would hand the cited theorem an assumption that does not follow from what
//! callers establish. That is the one false accept this increment can produce,
//! so the eligibility filter is an arithmetic-free ALLOW-list with no deny-list
//! to fall out of sync, and every refusal is an OMISSION. Omission is always
//! the sound direction: `(∀p, Q) ⇒ (∀p, H → Q)`, so a dropped hypothesis makes
//! the theorem HARDER, never easier.
//!
//! What must be visible in the output, because a silent omission is how an
//! author stops being able to predict the goal (v6/D1 — report what was
//! graded):
//!
//!   * the conditional-discharge note, naming `b <= a` as hypothesis `h0`;
//!   * a note saying `a + b > 10` was not carried, NAMING the operator `+`.
//!
//! The crates-level twin that measures both halves is
//! `trust_spec_elab::requires_hypothesis_tests::an_omitted_clause_is_disclosed_not_dropped`
//! (plus `e_allow_admits_exactly_the_arithmetic_free_fragment` for the whole
//! allow-list). Since OR-A1 increment 1a the conditional discharge over the
//! carried `b <= a` is CREDITABLE (at `Trusted`), so the citation is no longer a
//! hard error. Nothing is credited: the solver and the exact-source-clause lane
//! already proved every postcondition row, and a conditional credit never
//! replaces a proof (H2). The two Level-0/strict errors are about an obligation
//! the citation does not own — MEASURED on stage 1 (ora1-land, 2026-09-28): the one
//! unproved row is `vc:…:custom:2`, the `a + b > 10` clause's own
//! `SpecUnverifiable` row (unmodeled fixed-width machine arithmetic).

clean {
    theorem rmax_le_left : forall (a : UInt64) (b : UInt64),
        Nat.le (UInt64.toNat b) (UInt64.toNat a) ->
        Nat.le (UInt64.toNat (if a < b then b else a)) (UInt64.toNat a) :=
        fun a b h => Decidable.casesOn
            (motive := fun (d : Decidable (LT.lt a b)) =>
                Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                    d (fun _ => a) (fun _ => b))) (UInt64.toNat a))
            (instDecidableUInt64Lt a b)
            (fun _ => @Nat.le.refl (UInt64.toNat a))
            (fun _ => h)
}

pub fn rmax_guarded(a: u64, b: u64) -> u64
//~^ ERROR Trust Level 0 safety verification incomplete for
//~| ERROR Trust strict verification failed for
    requires b <= a
    requires a + b > 10
    ensures result <= a by rmax_le_left
    //~^ NOTE kernel-discharges this postcondition UNDER this function's `requires`
    //~| NOTE these preconditions assumed: h0 = `b <= a` (`requires` #0)
    //~| NOTE not carried as a hypothesis, so the goal is correspondingly harder: `a + b > 10` (`requires` #1)
    //~| NOTE requires-link: kernel-canonical
{
    if a < b { b } else { a }
}

fn main() {}
