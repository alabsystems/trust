//@ probe-shape: Projection
//@ probe-expect: clause-outside-fragment
//@ probe-note: ASYMMETRY WORTH FIXING: the BODY is admissible (Projection), but the
//@ probe-note: clause side has no signed domain, so the discharge fails late rather
//@ probe-note: than the function being refused up front.
clean { def ident_i (x : Int) : Int := x }
pub fn idi(x: i64) -> i64
    ensures result == ident_i(x)
{ x }
