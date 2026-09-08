//@ probe-shape: Select
//@ probe-expect: discharged
//@ probe-note: ITEM 11 — a clause names a program function by a MODULE-QUALIFIED
//@ probe-note: spelling (`g::min2`) because its bare name is owned by more than one
//@ probe-note: item and is therefore evicted as ambiguous. This is the veripb client
//@ probe-note: shape, measured 2026-08-26 on `veripb-core-proved`: `guard::narrow`
//@ probe-note: is admissible=true / recognize=GuardedNarrow, but three def-paths end
//@ probe-note: in `::narrow` (the free function plus the two `CoeffDomain::narrow`
//@ probe-note: trait-impl methods), so the ONLY spellable key the facet table used to
//@ probe-note: hold for it was evicted and the contract could not be written at all.
//@ probe-note:
//@ probe-note: The fix is a KEYING fix, not an admission fix. `SessionFnFacets` now
//@ probe-note: keys every record and admission by the def-path AND by every proper
//@ probe-note: module-path suffix of it (`trust_spec_elab::spec_spellings`), under the
//@ probe-note: same collision-eviction rule the bare name already had. A longer suffix
//@ probe-note: is strictly more discriminating, so `g::min2` names exactly one item
//@ probe-note: while `min2` stays evicted — see the d17 negative, which pins that the
//@ probe-note: bare spelling did NOT get loosened to pick a winner.
//@ probe-note:
//@ probe-note: `other::min2` exists purely to create the bare-name collision; it is
//@ probe-note: never cited.
//@ probe-note:
//@ probe-note: MEASURED 2026-08-26 on the pre-fix stage2: `clause-outside-fragment`,
//@ probe-note: reason "no diagnostic E6 facet record exists for `g::min2`". This probe
//@ probe-note: is therefore RED until the keying fix is in the built compiler; it is
//@ probe-note: the pin for that fix, not a regression.
clean {
    theorem min2_import_thm : forall (a : UInt64) (b : UInt64),
        Nat.le (UInt64.toNat (trust_import_probe__g__min2 a b)) (UInt64.toNat a) :=
        fun a b => Decidable.casesOn
            (motive := fun (d : Decidable (LT.lt a b)) =>
                Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                    d (fun _ => b) (fun _ => a))) (UInt64.toNat a))
            (instDecidableUInt64Lt a b)
            (fun h => Iff.mp (Nat.not_lt (UInt64.toNat a) (UInt64.toNat b)) h)
            (fun h => Nat.le.refl (UInt64.toNat a))
}

pub mod g {
    pub fn min2(a: u64, b: u64) -> u64 {
        if a < b { a } else { b }
    }
}

pub mod other {
    pub fn min2(a: u64, b: u64) -> u64 {
        a
    }
}

pub fn caller(x: u64, y: u64) -> u64
    ensures g::min2(x, y) <= x by min2_import_thm
{
    x
}
