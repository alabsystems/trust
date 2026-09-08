//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. A `&Cst` parameter's field is NOT in the
//@ probe-note: fragment: the pointee is not provably unchanged between entry and exit
//@ probe-note: (the two-state `&mut` reading is a separate lane, and even a shared
//@ probe-note: reference would need that argument made), and the MIR read carries a
//@ probe-note: `Deref` the recognizer refuses. Flipping this green without a post-state
//@ probe-note: story is how `ensures` starts describing entry values it cannot bind.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub struct Cst { pub degree: u64, pub coeff: u64 }
pub fn degree_of_ref(c: &Cst) -> u64
    ensures result == ident_isl(c.degree)
{ c.degree }
