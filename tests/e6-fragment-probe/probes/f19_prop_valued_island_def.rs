//@ probe-shape: none
//@ probe-expect: unproved
//@ probe-note: A Prop-VALUED island definition cannot appear in a clause at all:
//@ probe-note: "unsupported contract predicate expression `le_isl(result, x)`".
//@ probe-note: This closes off the obvious ergonomic escape from the encoding
//@ probe-note: problem — you cannot define your own predicate in Lean and use it as
//@ probe-note: the clause. Clauses relate the Rust result to island defs only
//@ probe-note: through the comparison grammar, so the compiler's ENCODING is always
//@ probe-note: in the goal. That is why f01 matters and why there is no way around it
//@ probe-note: short of fixing the encoding match itself.
clean {
    def le_isl (a : UInt64) (b : UInt64) : Prop := Nat.le (UInt64.toNat a) (UInt64.toNat b)
    theorem le_isl_refl : forall (x : UInt64), le_isl x x :=
        fun x => Nat.le.refl (UInt64.toNat x)
}
pub fn keep(x: u64) -> u64
    ensures le_isl(result, x) by le_isl_refl
{ x }
