//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. The dotted path is DEPTH 1. `c.inner.degree`
//@ probe-note: names a scalar too, but reaching it means projecting an aggregate FIELD
//@ probe-note: out of an aggregate parameter, and nothing in this increment can name
//@ probe-note: the intermediate value. Both sides refuse for the same reason: the
//@ probe-note: parameter's field `inner` is not a scalar, so the struct contributes no
//@ probe-note: rows, and `atom_var_name` does not recognize a nested projection.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub struct Inner { pub degree: u64 }
pub struct Outer { pub inner: Inner }
pub fn deep_degree(c: Outer) -> u64
    ensures result == ident_isl(c.inner.degree)
{ c.inner.degree }
