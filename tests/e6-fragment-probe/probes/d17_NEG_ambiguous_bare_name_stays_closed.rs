//@ probe-shape: Select
//@ probe-expect: unproved
//@ probe-flags: -O
//@ probe-note: NEGATIVE. `min2` is owned by BOTH `g::min2` and `other::min2`,
//@ probe-note: so the BARE spelling is evicted from the facet table and stays
//@ probe-note: fail-closed. d16 is the paired POSITIVE: byte-identical except
//@ probe-note: that its clause writes the module-qualified `g::min2`, and it
//@ probe-note: discharges. The two differ in exactly one token, so the
//@ probe-note: ambiguity is the sole obstacle here.
//@ probe-note:
//@ probe-note: REPAIRED TWICE, and the history is the point. Born with a
//@ probe-note: malformed island, it failed on a REJECTED ISLAND before ever
//@ probe-note: reaching the ambiguity. The first repair swapped that for a
//@ probe-note: theorem about an unrelated `dummyB`, so the citation was
//@ probe-note: refused on STATEMENT MISMATCH instead -- one wrong reason for
//@ probe-note: another, and deleting `other::min2` (removing the very
//@ probe-note: ambiguity this probe is named for) still left it passing.
//@ probe-note: Measured both times. It now cites d16's real theorem over
//@ probe-note: `trust_import_probe__g__min2`, so the ONLY thing standing
//@ probe-note: between it and `discharged` is the evicted bare name.
//@ probe-note:
//@ probe-note: The check that keeps it honest: delete `pub mod other` and
//@ probe-note: this probe MUST flip to `discharged`. If it does not, it has
//@ probe-note: gone back to failing for some other reason.
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
    ensures min2(x, y) <= x by min2_import_thm
{
    x
}
