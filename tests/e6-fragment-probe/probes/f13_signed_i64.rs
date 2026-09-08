//@ probe-shape: Projection
//@ probe-expect: clause-outside-fragment
//@ probe-note: THE BODY has been admissible all along (Projection), and since E6
//@ probe-note: widening increment 4 (2026-08-23) the i64 CLAUSE side elaborates too —
//@ probe-note: f25 is the probe that shows the signed lane discharging. What keeps THIS
//@ probe-note: probe out is the island definition's carrier: `ident_i` is Int -> Int,
//@ probe-note: and the clause applies it to a BitVec 64 value, so the elaborated goal
//@ probe-note: does not typecheck. For one binary (increment 4, before the goal gate)
//@ probe-note: this probe DISCHARGED: the defeq route judged the proof term against the
//@ probe-note: goal expression without deriving the goal's own typing, both sides
//@ probe-note: beta-reduce to `x`, and the kernel accepted Eq.refl at an ill-typed
//@ probe-note: proposition. The same acceptance reproduced at u64 with the SAME island,
//@ probe-note: so the hole predated the widening; the widening only made it reachable
//@ probe-note: from iN clauses. Both discharge routes now infer the goal's type first
//@ probe-note: and fail closed here, with the fix in the message (restate the island
//@ probe-note: def over the clause's carrier).
clean { def ident_i (x : Int) : Int := x }
pub fn idi(x: i64) -> i64
    ensures result == ident_i(x)
{
    x
}
