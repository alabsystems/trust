//@ probe-shape: FieldProjection
//@ probe-expect: discharged
//@ probe-note: The CITED half of increment 7 — a dotted path in a clause closed by an
//@ probe-note: island THEOREM rather than by definitional equality. This is the lane the
//@ probe-note: veripb client's nine existing citations use, now reachable for a fact
//@ probe-note: about a struct's field.
//@ probe-note:
//@ probe-note: NOTE THE SHAPE, because it is not the obvious one: the clause must NOT
//@ probe-note: call an island definition. The cited lane installs no island-definition
//@ probe-note: facets (only the uncited defeq lane does), so `isl(c.degree) <= c.degree
//@ probe-note: by thm` is refused with "no diagnostic E6 facet record exists". What
//@ probe-note: works is the client's own spelling: mention `result`, which binds to the
//@ probe-note: E6 import, and state the theorem over the value that import unfolds to.
//@ probe-note: Here the import is `fun degree coeff => degree`, so the goal
//@ probe-note: `Nat.le (toNat (import d k)) (toNat d)` reduces to `Nat.le (toNat d)
//@ probe-note: (toNat d)` and `Nat.le.refl` closes it.
clean {
    theorem degree_le_self : forall (d : UInt64) (k : UInt64),
        Nat.le (UInt64.toNat d) (UInt64.toNat d) :=
        fun d k => Nat.le.refl (UInt64.toNat d)
}
pub struct Cst { pub degree: u64, pub coeff: u64 }
pub fn degree_bound(c: Cst) -> u64
    ensures result <= c.degree by degree_le_self
{ c.degree }
