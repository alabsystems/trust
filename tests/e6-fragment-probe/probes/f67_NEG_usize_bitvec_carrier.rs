//@ probe-shape: Projection
//@ probe-expect: clause-outside-fragment
//@ probe-note: CLOSE NEGATIVE TWIN of `f15`: the same function, the island definition
//@ probe-note: restated over `BitVec 64` — same WIDTH as a 64-bit `usize`, different
//@ probe-note: CARRIER. `BitVec 64` is what `Domain::USize`'s docs would lead a reader to
//@ probe-note: write, and it is the carrier the statement-only lanes (runtime monitors,
//@ probe-note: zero-authority denotation rows) use. The E9 discharge lanes bind `usize`
//@ probe-note: at the carrier the function's E6 IMPORT carries (`UInt64`), because a
//@ probe-note: `result`-mentioning goal applies that import to the binders and an
//@ probe-note: admitted call is checked against its declared carriers, never coerced.
//@ probe-note: So this must stay refused: admitting `usize` binders admitted the clause
//@ probe-note: at ONE carrier, not at every 64-bit one. The refusal is one of the
//@ probe-note: elaborator's "checked against the callee's declared type and never
//@ probe-note: coerced" carrier checks, or behind them the ill-typed-goal gate; all of
//@ probe-note: them read `ClauseOutsideFragment`.
//@ probe-note:
//@ probe-note: This row reads `clause-outside-fragment` both BEFORE the usize change (the
//@ probe-note: bare-`usize` refusal) and AFTER it (the carrier refusal), so it is pinned
//@ probe-note: across the increment; what changes is the reason, which `run.py` records.
clean { def ident_bv (x : BitVec 64) : BitVec 64 := x }
pub fn f(x: usize) -> usize
    ensures result == ident_bv(x)
{
    x
}
