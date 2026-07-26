//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: A bool match is not one of the five shapes, though it is semantically
//@ probe-note: an identity — a candidate for a cheap recognizer widening.
clean { def ident_b (x : Bool) : Bool := x }
pub fn f(x: bool) -> bool
    ensures result == ident_b(x)
{ match x { true => true, false => false } }
