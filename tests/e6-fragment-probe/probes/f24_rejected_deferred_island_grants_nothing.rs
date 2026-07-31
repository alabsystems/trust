//@ probe-shape: Select
//@ probe-expect: unproved
//@ probe-note: ITEM 10 PHASE 2, RED — the load-bearing one.
//@ probe-note:
//@ probe-note: The first deferred island holds a VALID theorem that really does prove the
//@ probe-note: clause; on its own it discharges (that is d13). The second deferred island
//@ probe-note: is broken. Both are checked post-walk, in authored order, against the same
//@ probe-note: stateful session — so the rejection lands AFTER the good declaration has
//@ probe-note: already registered, and the session is tainted with a partial environment.
//@ probe-note:
//@ probe-note: A tainted session must grant NOTHING. `environment()` returns None, the
//@ probe-note: quarantined body discharges nothing, and its withheld verdict is published
//@ probe-note: as the honest unproved result beside the island error. If this probe ever
//@ probe-note: reports discharged, the post-walk lane is minting positive evidence out of
//@ probe-note: a partially-registered environment — the exact failure the pre-walk island
//@ probe-note: phase and every other island consumer already fail closed against.
//@ probe-note:
//@ probe-note: Ordering matters and is deliberate: put the broken island FIRST and the
//@ probe-note: test is vacuous, because nothing valid would have registered.
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

clean {
    theorem broken_thm : forall (a : UInt64),
        Nat.le (UInt64.toNat (trust_import_probe__min2 a a)) (UInt64.toNat a) :=
        this_constant_does_not_exist
}

pub fn min2(a: u64, b: u64) -> u64 {
    if a < b { a } else { b }
}

pub fn caller(x: u64, y: u64) -> u64
    ensures min2(x, y) <= x by min2_import_thm
{
    x
}
