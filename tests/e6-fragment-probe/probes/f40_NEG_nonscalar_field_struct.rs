//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. ALL-OR-NOTHING per struct: one field outside
//@ probe-note: the supported scalar vocabulary refuses the WHOLE parameter, even though
//@ probe-note: the field the clause names (`degree`) is a perfectly ordinary `u64`.
//@ probe-note:
//@ probe-note: That is not timidity. The clause-side flattening (HIR types) and the
//@ probe-note: mint-side flattening (extracted-IR types) are two independent
//@ probe-note: computations of one list, and a per-field FILTER would be two filters
//@ probe-note: that must agree field by field — a disagreement would emit the same
//@ probe-note: number of binders in a different ORDER, and a theorem about one field
//@ probe-note: would silently discharge a clause about another. With no filter there is
//@ probe-note: nothing to disagree about.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub struct Cst { pub degree: u64, pub terms: [u64; 2] }
pub fn degree_of_mixed(c: Cst) -> u64
    ensures result == ident_isl(c.degree)
{ c.degree }
