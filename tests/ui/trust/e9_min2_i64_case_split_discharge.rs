//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-require-annotations: NOTE
//! E9: THE CANONICAL min2 DISCHARGE AT THE SIGNED CARRIER (E6 widening
//! increment 4) — the i64 twin of `e9_min2_case_split_discharge`. `min2_i64`
//! is E6-admitted via the select recognizer at `Domain::Signed(I64)`: the
//! exact two's-complement `BitVec 64` carrier whose comparisons — in the
//! minted body AND in the elaborated goal — go through the sign-flip order
//! keys `Nat.xor (BitVec.toNat v) 2^63` (signed order mapped bijectively to
//! Nat order; the mint deliberately does NOT reuse Clean's unsigned `BitVec`
//! order instances, which would give the program's signed `<` an unsigned
//! meaning at `i64::MIN`). The island names the key ONCE (`key64`) and states
//! the theorem through it; kernel delta-reduction bridges the helper to the
//! mint's inlined keys. The proof is a REAL case split on the minted
//! `Nat.decLt` decision. Both discharge flavors are exercised: the
//! result-bound self postcondition on `min2_i64` (the acceptance shape for
//! carrying compiler-checked contracts on i64 kernel functions) and a
//! result-free call clause on `caller`.
clean {
    def key64 (v : BitVec 64) : Nat :=
        Nat.xor (BitVec.toNat v) 9223372036854775808
    theorem min2_i64_le_left : forall (x : BitVec 64) (y : BitVec 64),
        Nat.le (key64 (if Nat.lt (key64 x) (key64 y) then x else y)) (key64 x) :=
        fun x y => Decidable.casesOn
            (motive := fun (d : Decidable (Nat.lt (key64 x) (key64 y))) =>
                Nat.le (key64 (Decidable.casesOn (motive := fun _ => BitVec 64)
                    d (fun _ => y) (fun _ => x))) (key64 x))
            (Nat.decLt (key64 x) (key64 y))
            (fun h => Iff.mp (Nat.not_lt (key64 x) (key64 y)) h)
            (fun h => Nat.le.refl (key64 x))
}
pub fn min2_i64(a: i64, b: i64) -> i64
    ensures result <= a by min2_i64_le_left
{ if a < b { a } else { b } }

pub fn caller(x: i64, y: i64) -> i64 ensures min2_i64(x, y) <= x by min2_i64_le_left { x }

fn main() {}
