//@ probe-shape: ConstantUint
//@ probe-expect: discharged
//@ probe-note: RECLASSIFIED 2026-08-23 (ill-typed-goal gate): the elaborated goal was
//@ probe-note: ALWAYS ill-typed -- a variable-less atom defaults to the Nat domain, so the
//@ probe-note: UInt64 island call sat under an `Eq Nat`. The defeq route used to reach the
//@ probe-note: judgment and fail as not-defeq; both routes now type the goal FIRST and fail
//@ probe-note: closed at the clause with the carrier named in the diagnostic. Same verdict
//@ probe-note: direction, earlier and honest about WHERE the boundary is.
//@ probe-note: Explicit UInt64.ofNat, to test whether the literal's default type is
//@ probe-note: the obstacle. It is not sufficient on its own.
//@ probe-note:
//@ probe-note: UPDATED 2026-08-26, E6/E9 widening increment 8
//@ probe-note: (typed-call argument/result carriers): DISCHARGES, for
//@ probe-note: exactly the reason f06 does — and this row's original question is now
//@ probe-note: answered in full. The literal's default type was never the obstacle: f06 and
//@ probe-note: f07 differ only in how the island spells 42 and BOTH close. The obstacle was
//@ probe-note: the ATOM's domain defaulting to `Nat` with no variable to type it.
clean { def c42 (x : UInt64) : UInt64 := UInt64.ofNat 42 }
pub fn answer() -> u64
    ensures result == c42(0)
{
    42
}
