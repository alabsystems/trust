//@ probe-shape: ComparisonBool
//@ probe-expect: discharged
//@ probe-note: The NEGATIVE-literal end of the literal-operand widening. A signed literal
//@ probe-note: extracts as `ConstValue::Int(i128)` with NO width, so the recognizer
//@ probe-note: carries it by MAGNITUDE and the mint routes it through
//@ probe-note: `Domain::negative_numeral`, which range-checks against 2^(w-1) and emits
//@ probe-note: the two's-complement pattern. Carrying a wrapped `u128` instead would make
//@ probe-note: `-1` and `u128::MAX` the same operand — and at a signed carrier that is
//@ probe-note: not a near miss, it is the opposite end of the order.
//@ probe-note:
//@ probe-note: The island call here is the plain identity, not a restatement of the
//@ probe-note: bound, and that is a measurement, not a shortcut: the uncited defeq route
//@ probe-note: owns only clauses that CALL an island definition, and a hand-written
//@ probe-note: island stating the same bound as
//@ probe-note: `decide (Nat.le (key64 (BitVec.ofNat 64 18446744073709551615)) (key64 x))`
//@ probe-note: is NOT defeq to the mint (measured 2026-08-24), while the `Nat.zero`
//@ probe-note: spelling in f34 is. So a large numeral does not elaborate to the kernel
//@ probe-note: literal the mint builds — an island-authoring gap worth its own increment,
//@ probe-note: and one this probe would otherwise have hidden behind a red expectation.
clean { def ident_w (x : BitVec 64) : BitVec 64 := x }
pub fn ge_neg_one(x: i64) -> bool
    ensures result == (x >= -1) && x == ident_w(x)
{ x >= -1 }
