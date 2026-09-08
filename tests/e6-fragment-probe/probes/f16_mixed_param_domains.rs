//@ probe-shape: Projection
//@ probe-expect: discharged
//@ probe-note: One u64 and one bool parameter. Uniformity is required across ALL
//@ probe-note: parameters even when the extra one is irrelevant to the clause.
//@ probe-note:
//@ probe-note: UPDATED 2026-08-26, E6/E9 widening increment 8
//@ probe-note: (typed-call argument/result carriers): DISCHARGES. The
//@ probe-note: refusal here was the same wrong-authority bug in its second form: `s : bool`
//@ probe-note: is a parameter the body IGNORES, but the self-call `f(x, s)` spliced in for
//@ probe-note: `result` put it in the atom, and an atom typed by ALL its variables read
//@ probe-note: `u64` beside `bool` as a mixed comparison. `s` was never an operand of the
//@ probe-note: comparison — it is an ARGUMENT of a call whose declaration says it takes a
//@ probe-note: `Bool` there — and the elaborator now types call arguments by the callee's
//@ probe-note: declared parameter carriers instead. A genuinely mixed comparison
//@ probe-note: (`x == s`, with no callee between them) is still refused; f64 is that pin.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub fn f(x: u64, s: bool) -> u64
    ensures result == ident_isl(x)
{
    x
}
