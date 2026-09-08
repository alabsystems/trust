//@ probe-shape: FieldProjection
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red — and it names the fact the veripb client records
//@ probe-note: as unstatable in its aggregate form: "SATURATE leaves the degree alone"
//@ probe-note: is `(satC c).degree = c.degree`.
//@ probe-note:
//@ probe-note: A PARAMETER-side dotted path is an opaque atom the clause may quantify
//@ probe-note: over. `result` is not: it denotes the return value only through the E6
//@ probe-note: import, so `result.degree` would have to project a field OF THE MINTED
//@ probe-note: TERM — a `reflect_struct` field access, i.e. the aggregate carrier this
//@ probe-note: increment deliberately does not build.
//@ probe-note:
//@ probe-note: `degree_of` is fully E6-ADMITTED here, so the refusal is not the
//@ probe-note: admission gate standing in: the clause reaches `rewrite_result_to` and is
//@ probe-note: refused there BY NAME, rather than drifting out as an unbound variable
//@ probe-note: with an unhelpful message. d15 shows the fact stated the way that works —
//@ probe-note: over a function that RETURNS the field.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub struct Cst { pub degree: u64, pub coeff: u64 }
pub fn degree_of(c: Cst) -> u64
    ensures result.degree == ident_isl(c.degree)
{ c.degree }
