//@ probe-shape: Select
//@ probe-expect: discharged
//@ probe-note: ITEM 10 PHASE 2 FLAGSHIP — a function's OWN postcondition, discharged by
//@ probe-note: an island theorem that names the function itself.
//@ probe-note:
//@ probe-note: This is the shape item 10 exists for. The author does not restate the body
//@ probe-note: in Lean and hope the restatement matches the compiler's encoding (the trap
//@ probe-note: f01 and d11 document); the theorem is stated ABOUT `min2`, through the E6
//@ probe-note: kernel import the compiler minted from `min2`'s own MIR. There is one
//@ probe-note: definition of what `min2` means, and both languages point at it.
//@ probe-note:
//@ probe-note: Two gates must both fire, which is why this is stronger than d13:
//@ probe-note:   * the clause mentions `result`, so `elaborate_ensures` requires `min2`
//@ probe-note:     itself to be E6-ADMITTED (a result-free clause discharges on any body);
//@ probe-note:   * the cited theorem is in a DEFERRED island, so it cannot be resolved
//@ probe-note:     until after the program mint.
//@ probe-note: The second gate is why the discharge happens post-walk. Both conditions
//@ probe-note: are satisfiable only at the authoritative whole-crate stage, and that is
//@ probe-note: exactly where the adjudication now runs.
clean {
    theorem min2_self_thm : forall (a : UInt64) (b : UInt64),
        Nat.le (UInt64.toNat (trust_import_probe__min2 a b)) (UInt64.toNat a) :=
        fun a b => Decidable.casesOn
            (motive := fun (d : Decidable (LT.lt a b)) =>
                Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                    d (fun _ => b) (fun _ => a))) (UInt64.toNat a))
            (instDecidableUInt64Lt a b)
            (fun h => Iff.mp (Nat.not_lt (UInt64.toNat a) (UInt64.toNat b)) h)
            (fun h => Nat.le.refl (UInt64.toNat a))
}

pub fn min2(a: u64, b: u64) -> u64
    ensures result <= a by min2_self_thm
{
    if a < b { a } else { b }
}
