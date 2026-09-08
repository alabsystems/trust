//@ probe-shape: FieldProjection
//@ probe-expect: discharged
//@ probe-note: E6/E9 INCREMENT 7 BASELINE — the first clause that mentions an
//@ probe-note: AGGREGATE. `c.degree` is one opaque scalar atom: the compiler emits a
//@ probe-note: binding row per scalar field of every parameter, and the body mint takes
//@ probe-note: one binder per row (`fun degree coeff => degree`). No struct reaches the
//@ probe-note: kernel, so this needs no reflected carrier — only a name.
//@ probe-note:
//@ probe-note: `c.coeff` is bound even though the clause never mentions it: the
//@ probe-note: flattening is canonicalized on the STRUCT, not on the clause, so the
//@ probe-note: minted arity cannot depend on what any one clause happens to say.
clean { def ident_isl (x : UInt64) : UInt64 := x }
pub struct Cst { pub degree: u64, pub coeff: u64 }
pub fn degree_of(c: Cst) -> u64
    ensures result == ident_isl(c.degree)
{ c.degree }
