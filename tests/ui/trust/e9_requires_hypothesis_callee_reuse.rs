//@ revisions: default l0
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@[l0] compile-flags: -Ztrust-verify-level=0
//@ check-fail
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//! OR-A1 review, round 2 (owner ruling B1, 2026-09-28): a CONDITIONAL credit is
//! REUSED by callers, and that reuse is modular composition — pinned here, with
//! the negative controls that make it sound.
//!
//! THE CALLEE. `rmax`'s second `ensures` names the island definition `cap`, so
//! no solver lane can represent it; its only proof is the cited theorem
//! `rmax_cap_le`, which proves it UNDER `requires b <= a` (the kernel-canonical
//! link). That row is credited `EnsuresCitationUnderRequiresDischarge`,
//! `Trusted`. The first `ensures` is also cited conditionally, but the solver
//! already proved it, so it keeps that proof (H2). With the credit, every row of
//! `rmax` is accounted (`trusted + certified == total`), which is what
//! `callee_postconditions_are_reusable` reads before a caller may assume
//! `rmax`'s `ensures` — so the credit is what makes `rmax` REUSABLE. On the
//! pinned-seed pack `4d9a20e3daf` (no OR-A1) the same file reports
//! `TRUST_COMPOSE … verdict=verdict:not-accounted` for every caller below.
//!
//! (a) POSITIVE COMPOSITION. `use_inside` has a STRONGER `requires` (`b < a`),
//! calls `rmax(a, b)` and claims `result <= a`; `use_inside_sub` subtracts the
//! result from `a`, which is underflow-free only because `rmax`'s `ensures`
//! reached it; `use_inside_sub_nc` has NO contract and establishes `3 <= a` on
//! its own path. Their rows are proved by the CALLER's own engines at those
//! engines' authority, with no requires-link marker at the caller (the
//! per-function report of the caller carries none). That authority can be
//! `Certified`: `use_inside_sub_nc`'s underflow row is kernel-certified — the
//! kernel re-checked the CALLER's VC, whose premise is the reused `pre → post`
//! of `rmax(a, 3)`, `3 <= a → result <= a`; `result <= a` is the callee clause
//! the solver proved and the kernel certified. The conditionally credited
//! clause (the one naming `cap`) never reaches a caller VC; what the credit
//! bought the callers is the reuse GATE, not a premise.
//!
//! (b) NEGATIVE CONTROLS — the injection must be `requires → ensures`. Each one
//! discriminates exactly one thing.
//! `use_outside` discriminates the `pre → post` GUARD. It calls `rmax(0, 5)`,
//! OUTSIDE `b <= a`, and claims `result < 1`, which is FALSE
//! (`rmax(0, 5) == 5`). An UNGUARDED injection of `result <= a` (here
//! `result <= 0`) would prove it (measured on a stand-in, below); the guarded
//! `(5 <= 0) → result <= 0` does not, so its postcondition rows stay UNKNOWN at
//! both levels (and its call-site precondition row FAILS: it has a contract, so
//! it is charged `rmax`'s `requires` at both levels).
//! `use_outside_sub` discriminates the GUARD on a caller with no contract: the same
//! call, `3 - rmax(0, 5)` — a REAL underflow an unguarded injection would prove
//! safe (stand-in, below). Its underflow row is HELD `UNKNOWN` naming `rmax`
//! (2026-09-28; it was `FAILED` on a model of `rmax`'s CONTRACT, `r = 4`, while
//! `rmax(0, 5)` is 5): the D5-A screen pins a result only where an injected
//! clause DETERMINES it unguarded (`summary_pins_result`). Its own call-site
//! precondition row FAILS too, a separate row, at both levels.
//!
//! REVISION `l0` (`-Ztrust-verify-level=0`). The call-site `Precondition` row is
//! `L1Functional`; until 2026-10-03 a caller with no contract and no extracted
//! precondition stayed at L0, so here `use_outside_sub` was NOT charged `rmax`'s
//! `requires` (the "level-0 guard-only path"). That path is gone for every caller
//! owing a callee `requires`: `effective_max_level` lifts it to L1, so `l0` reads
//! as `default` (MEASURED on the stage 1 of `6011b74bad`, 2026-10-03; before the fix
//! this file gave identical output at levels 1 and 2; KNOWN_HAZARDS "… charged nothing").
//!
//! MEASURED on stage 1 (ora1-land merged with main), re-blessed on cb/track-b's (both
//! 2026-09-28; held underflow, `[precond]` still FAILED). That an unguarded injection proves
//! `use_outside`'s claim and `use_outside_sub`'s subtraction is measured with a
//! stand-in, not this file: a callee with no `requires` and
//! `ensures result <= a`, whose `ensures` therefore reaches callers with no
//! antecedent — there `result < 1` at `(0, 5)` is proved and kernel-certified
//! and `3 - r`'s underflow row is proved, at the default level and at level 0;
//! here both stay unproved. No compiler with the guard removed was built.

clean {
    def cap (n : Nat) : Nat := n
    theorem rmax_cap_le : forall (a : UInt64) (b : UInt64),
        Nat.le (UInt64.toNat b) (UInt64.toNat a) ->
        Nat.le (cap (UInt64.toNat (if a < b then b else a))) (UInt64.toNat a) :=
        fun a b h => Decidable.casesOn
            (motive := fun (d : Decidable (LT.lt a b)) =>
                Nat.le (cap (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                    d (fun _ => a) (fun _ => b)))) (UInt64.toNat a))
            (instDecidableUInt64Lt a b)
            (fun _ => @Nat.le.refl (UInt64.toNat a))
            (fun _ => h)
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

pub fn rmax(a: u64, b: u64) -> u64
//~^ NOTE 5 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (requires) out of 6 obligation(s)
//~| NOTE 2 obligation(s) were discharged by a cited theorem proved UNDER this function's own `requires` (2 requires-link: kernel-canonical)
    requires b <= a
    ensures result <= a by rmax_le_left
    ensures cap(result as nat) <= (a as nat) by rmax_cap_le
{
    if a < b { b } else { a }
}

pub fn use_inside(a: u64, b: u64) -> u64
//~^ NOTE 4 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (requires) out of 5 obligation(s)
//~| NOTE of which 1 kernel-certified
    requires b < a
    ensures result <= a
{
    rmax(a, b)
}

pub fn use_inside_sub(a: u64, b: u64) -> u64
//~^ NOTE 3 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (requires) out of 4 obligation(s)
    requires b < a
{
    let r = rmax(a, b);
    a - r
}

pub fn use_inside_sub_nc(a: u64) -> u64 {
//~^ NOTE 3 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 3 obligation(s)
//~| NOTE of which 2 kernel-certified
    if a > 3 {
        let r = rmax(a, 3);
        a - r
    } else {
        0
    }
}

// RE-PIN 2026-11-15: 1 failed / 2 unknown -> 2 failed / 1 unknown. The clause `result < 1` is
// FALSE of this body: `rmax(0, 5)` returns 5. The 2026-11-14 trust-wp pins decide unsigned
// Select on the body path, so the body-aware WP lane, which reads `rmax`'s own body, refutes
// the source clause row. `use_outside` declares no `requires`, so the bare clause IS its public
// claim (WP-BODY-NO-REQUIRES-1 withholds only where one is declared). Measured on a stage 1 of
// main 3f5d1e29d27 and of the landing tree.
pub fn use_outside() -> u64
//~^ ERROR Trust strict verification failed for
//~| NOTE 1 proved, 2 failed, 1 unknown, 0 timed out, 0 runtime-checked out of 4 obligation(s)
//~| NOTE [precond] FAILED
//~| NOTE [postcond] FAILED
    ensures result < 1
{
    rmax(0, 5)
}

pub fn use_outside_sub() -> u64 {
//~^ ERROR Trust Level 0 safety verification incomplete for
//~| ERROR Trust strict verification failed for
//~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `e9_requires_hypothesis_callee_reuse::rmax`
//~| NOTE 0 proved, 1 failed,
//~| NOTE [precond] FAILED
// (both revisions since 2026-10-03: level 0 lifts a caller owing `rmax`'s `requires`)
    let r = rmax(0, 5);
    3 - r
}

fn main() {}
