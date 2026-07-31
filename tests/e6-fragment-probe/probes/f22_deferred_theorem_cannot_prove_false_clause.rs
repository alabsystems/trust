//@ probe-shape: Select
//@ probe-expect: unproved
//@ probe-note: ITEM 10 PHASE 2, RED — the post-walk discharge must not accept a
//@ probe-note: theorem that does not prove the goal.
//@ probe-note:
//@ probe-note: `min2_import_thm` is the SAME valid theorem d13 cites, and it kernel-
//@ probe-note: checks. The clause here is strictly stronger and FALSE: at a == b the
//@ probe-note: body returns a, so `min2(x, y) < x` fails. A `<=` theorem cannot prove a
//@ probe-note: `<` goal, so the citation must come back
//@ probe-note: StatementOrCertificationRejected and the row must stay unproved.
//@ probe-note:
//@ probe-note: This is the false-accept guard for the whole lane. The pending/quarantine
//@ probe-note: machinery decides only WHEN a citation is adjudicated; if it ever changed
//@ probe-note: WHAT counts as a discharge, this probe flips to discharged and the runner
//@ probe-note: fails. Deferral must buy a retry against a complete environment and
//@ probe-note: nothing else.
clean {
    theorem min2_import_thm : forall (a : UInt64) (b : UInt64),
        Nat.le (UInt64.toNat (trust_import_probe__min2 a b)) (UInt64.toNat a) :=
        fun a b => Decidable.casesOn
            (motive := fun (d : Decidable (LT.lt a b)) =>
                Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                    d (fun _ => b) (fun _ => a))) (UInt64.toNat a))
            (instDecidableUInt64Lt a b)
            (fun h => Iff.mp (Nat.not_lt (UInt64.toNat a) (UInt64.toNat b)) h)
            (fun h => Nat.le.refl (UInt64.toNat a))
}

pub fn min2(a: u64, b: u64) -> u64 {
    if a < b { a } else { b }
}

pub fn caller(x: u64, y: u64) -> u64
    ensures min2(x, y) < x by min2_import_thm
{
    x
}
