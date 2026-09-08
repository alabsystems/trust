//@ probe-shape: ConstantUint
//@ probe-expect: discharged
//@ probe-note: RECLASSIFIED 2026-08-23 (ill-typed-goal gate): the elaborated goal was
//@ probe-note: ALWAYS ill-typed -- a variable-less atom defaults to the Nat domain, so the
//@ probe-note: UInt64 island call sat under an `Eq Nat`. The defeq route used to reach the
//@ probe-note: judgment and fail as not-defeq; both routes now type the goal FIRST and fail
//@ probe-note: closed at the clause with the carrier named in the diagnostic. Same verdict
//@ probe-note: direction, earlier and honest about WHERE the boundary is.
//@ probe-note: Zero-arity def, called with an empty argument list from the clause.
//@ probe-note:
//@ probe-note: UPDATED 2026-08-26, E6/E9 widening increment 8
//@ probe-note: (typed-call argument/result carriers): DISCHARGES. The
//@ probe-note: zero-arity def called with an empty argument list is the purest form of the
//@ probe-note: wall this increment removes — no arguments, no variables, nothing but two
//@ probe-note: constants whose declared carriers agree. The relation carrier now comes from
//@ probe-note: the SELF mint's recorded return domain and the island's declared `UInt64`
//@ probe-note: codomain is checked against it.
clean { def c42 : UInt64 := UInt64.ofNat 42 }
pub fn answer() -> u64
    ensures result == c42()
{
    42
}
