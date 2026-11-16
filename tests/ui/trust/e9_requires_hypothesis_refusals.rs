//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: HELP
//! OR-A1 (owner ruling 2026-09-27), increment 1a — what a conditional citation
//! must NOT be credited for, even though the kernel certifies a conditional goal
//! or is asked to.
//!
//! **H3 — a contradictory HIGH-ARITY precondition mints nothing.**
//! `contradictory` carries `a < b` AND `b < a`, so the conditional goal is
//! provable by ex falso and `hi_absurd` proves it (`Nat.lt_asymm`, constructive
//! and axiom-free). Five constrained `u64` parameters push the bounded witness
//! search past its budget (7 candidates each, 7^5 = 16807 > 4096), so it returns
//! `NotRun` — and the solver lane, which assumes a `requires` only on `Found`,
//! does not assume these either. A conditional credit that accepted `NotRun`
//! would be LOOSER than the lane beside it: a vacuous `Trusted` postcondition.
//! So nothing is credited, the note says why, and the citation stays a hard
//! error.
//!
//! **A hypothesis NOT implied by the `requires` is refused.** `strong` is probe
//! r5's shape: the theorem consumes `5 < k` while the function declares only
//! `k > 0`, so it states neither conditional goal (MEASURED on r5: "states
//! neither goal", hard error) — and the solver refutes the postcondition
//! (`strong(1) = 1`).
//!
//! MEASURED on stage 1 (ora1-land, 2026-09-28). `contradictory` also carries the
//! Level-0 error (the review's S9): its clause names the island definition
//! `succ_isl`, so its two postcondition rows are unsupported — exactly the rows
//! a vacuous credit would have taken — and they stay unproved.

clean {
    def succ_isl (n : Nat) : Nat := Nat.succ n
    theorem hi_absurd : forall (a : UInt64) (b : UInt64) (c : UInt64) (d : UInt64)
        (e : UInt64),
        Nat.lt (UInt64.toNat a) (UInt64.toNat b) ->
        Nat.lt (UInt64.toNat b) (UInt64.toNat a) ->
        Nat.lt 5 (UInt64.toNat c) ->
        Nat.lt 5 (UInt64.toNat d) ->
        Nat.lt 5 (UInt64.toNat e) ->
        Eq (UInt64.toNat a) (succ_isl (UInt64.toNat a)) :=
        fun a b c d e h0 h1 h2 h3 h4 =>
            False.elim (Nat.lt_asymm (UInt64.toNat a) (UInt64.toNat b) h0 h1)
    theorem too_strong : forall (k : UInt64),
        Nat.lt 5 (UInt64.toNat k) -> Nat.lt 5 (UInt64.toNat k) :=
        fun k h => h
}

pub fn contradictory(a: u64, b: u64, c: u64, d: u64, e: u64) -> u64
//~^ ERROR Trust strict verification failed for
//~| ERROR Trust Level 0 safety verification incomplete for
    requires a < b
    requires b < a
    requires c > 5
    requires d > 5
    requires e > 5
    ensures (result as nat) == succ_isl(a as nat) by hi_absurd
    //~^ NOTE kernel-discharges this postcondition UNDER this function's `requires`
    //~| NOTE the carried preconditions were not checked for satisfiability
    //~| ERROR citation `hi_absurd`
{
    a
}

pub fn strong(k: u64) -> u64
//~^ ERROR Trust strict verification failed for
    requires k > 0
    ensures result > 5 by too_strong
    //~^ NOTE a SECOND goal was also tried for `too_strong`
    //~| NOTE the cited theorem states neither goal
    //~| ERROR citation `too_strong`
{
    k
}

fn main() {}
