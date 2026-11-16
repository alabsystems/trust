//@ probe-shape: FieldProjection
//@ probe-expect: discharged
//@ probe-note: THE PAYOFF SHAPE, transplantable as written. This is the veripb client's
//@ probe-note: own geometry: a normalized PB constraint carrying its right-hand side as
//@ probe-note: a scalar field, at the REAL width — `i64`, the two's-complement
//@ probe-note: `BitVec 64` carrier with the `key64` sign-flip order key, exactly the
//@ probe-note: encoding `trust_surface.rs` already states its saturation theorems over.
//@ probe-note:
//@ probe-note: `saturated_degree` is the machine image of "SATURATE leaves the degree
//@ probe-note: alone", which the client's own doc comment records as a fact the clause
//@ probe-note: fragment could not state: `(satC c).degree = c.degree`. Stated over a
//@ probe-note: function that RETURNS the field, it is now sayable and kernel-discharged.
//@ probe-note:
//@ probe-note: Both routes are exercised on the same struct. The CITED ones read exactly
//@ probe-note: like the client's nine existing citations: `result` binds to the E6
//@ probe-note: import (here `fun degree coeff => degree`), the import is a reducible
//@ probe-note: definition, and the island theorem is stated over the value it unfolds
//@ probe-note: to — so no theorem ever has to name `trust_import_*`.
//@ probe-note:
//@ probe-note: What is still NOT here, so nobody plans against it: the client's real
//@ probe-note: `Constraint` carries `terms: Vec<Term>` beside `degree`, and it is passed
//@ probe-note: by REFERENCE. Both are refused (f40, f39).
clean {
    def key64 (v : BitVec 64) : Nat :=
        Nat.xor (BitVec.toNat v) 9223372036854775808

    def degree_isl (d : BitVec 64) (c : BitVec 64) : BitVec 64 := d

    theorem sat_preserves_degree : forall (d : BitVec 64) (c : BitVec 64), Eq d d :=
        fun d c => rfl

    theorem sat_degree_le : forall (d : BitVec 64) (c : BitVec 64),
        Nat.le (key64 d) (key64 d) :=
        fun d c => @Nat.le.refl (key64 d)
}

pub struct Constraint {
    pub degree: i64,
    pub coeff: i64,
}

/// CITED — the equality. `(satC c).degree = c.degree`, at the projection.
pub fn saturated_degree(c: Constraint) -> i64
    ensures result == c.degree by sat_preserves_degree
{ c.degree }

/// CITED — the order fact, over the signed sign-flip key rather than Clean's
/// unsigned `BitVec` order (which would give the program's signed `<=` an
/// unsigned meaning at `i64::MIN`).
pub fn saturated_degree_le(c: Constraint) -> i64
    ensures result <= c.degree by sat_degree_le
{ c.degree }

/// UNCITED — the definitional-equality route, for a clause that CALLS an island
/// definition. No theorem at all: `fun degree coeff => degree` and
/// `degree_isl` are the same term.
pub fn saturated_degree_defeq(c: Constraint) -> i64
    ensures result == degree_isl(c.degree, c.coeff)
{ c.degree }
