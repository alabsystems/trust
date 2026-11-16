//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//@ dont-require-annotations: NOTE
//! A1 — N-A6 (`mut` by-value binder), N-A7 (a body that shadows a parameter),
//! and the CALLER twin, all against one control in one crate.
//!
//! Every function here cites the same theorem for the same clause, so the only
//! thing that varies between them is the property under test. The control
//! `rmax_plain` is what makes each result attributable: it gets the conditional-
//! discharge note, so a missing note below is about the binder, not about the
//! theorem, the island, or the clause.
//!
//! **N-A6 — a `mut` by-value parameter disqualifies a clause.** `G1` uses ONE
//! binder for a parameter in both the hypothesis (its ENTRY value) and the
//! conclusion (its value at return). Rust forbids reassigning a non-`mut`
//! binding, so for a plain binding those are provably the same value; for a
//! `mut` binding they are not, and `fn f(mut a: u32) requires a <= 5 ensures
//! a <= 5` would be "proved" from a hypothesis about a value the body has
//! already overwritten. `rmax_mut` therefore gets NO conditional-discharge note,
//! and the gate is the same `trust_fn_collapsible_by_value_params` the `p'`
//! collapse already rides.
//!
//! **N-A7 — a body-local shadow must NOT withhold the goal.** `rmax_shadow`
//! rebinds `a` with a `let` inside the body. Nothing about the KERNEL goal
//! changes: its binders come from the signature and its hypothesis comes from
//! the query-owned proposition, never from a MIR debug name. This is the whole
//! reason the witness search was split into a body-independent core
//! (`contract_formulas_have_ground_witness`); if the solver lane's shadowing
//! outcome were being consulted, this note would disappear.
//!
//! **THE CALLER TWIN.** `violate` calls `rmax_plain(0, 5)`, which violates
//! `b <= a`. It must still be refused. Since owner ruling OR-A1 (increment 1a)
//! the conditional discharge of `rmax_plain` is CREDITABLE (at `Trusted`, on the
//! kernel-canonical link) — the citation is valid — and this twin is what shows
//! that accepting it did not stop charging its callers. (MEASURED on stage 1 (ora1-land, 2026-09-28):
//! no row of `rmax_plain` carries a `clean-kernel-requires-*` label, because the
//! solver already proved its postcondition rows and a conditional credit never
//! replaces a proof.)

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

/// CONTROL. Plain immutable by-value binders: the precondition is carried and
/// the conditional discharge is reported.
pub fn rmax_plain(a: u64, b: u64) -> u64
    requires b <= a
    ensures result <= a by rmax_le_left
    //~^ NOTE kernel-discharges this postcondition UNDER this function's `requires`
    //~| NOTE these preconditions assumed: h0 = `b <= a` (`requires` #0)
    //~| NOTE requires-link: kernel-canonical
{
    if a < b { b } else { a }
}

/// N-A6. Identical but for `mut a`. The clause names a binding whose entry value
/// and return value may differ, so it is never offered as a hypothesis.
pub fn rmax_mut(mut a: u64, b: u64) -> u64
    requires b <= a
    ensures result <= a by rmax_le_left
    //~^ ERROR failed the strict Clean statement/certification audit
{
    if a < b { a = b; }
    a
}

/// N-A7. A body-local `let` shadow of a parameter. The goal is built from the
/// SIGNATURE and the query-owned proposition, so the note must still appear.
pub fn rmax_shadow(a: u64, b: u64) -> u64
    requires b <= a
    ensures result <= a by rmax_le_left
    //~^ NOTE kernel-discharges this postcondition UNDER this function's `requires`
    //~| NOTE these preconditions assumed: h0 = `b <= a` (`requires` #0)
    //~| NOTE requires-link: kernel-canonical
{
    let a = a;
    if a < b { b } else { a }
}

/// THE CALLER TWIN. `b <= a` is false for `(0, 5)`, so this call must be
/// refused however the callee's postcondition was discharged.
pub fn violate() -> u64 {
//~^ ERROR Trust strict verification failed for
    rmax_plain(0, 5)
}

fn main() {}
