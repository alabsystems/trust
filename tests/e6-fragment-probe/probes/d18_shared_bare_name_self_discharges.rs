//@ probe-shape: Select
//@ probe-expect: discharged
//@ probe-flags: -O
//@ probe-note: THE PAIRED POSITIVE FOR d17 — a contract on a function whose BARE
//@ probe-note: name is shared by two items, discharging its OWN postcondition.
//@ probe-note:
//@ probe-note: d16/d17 are about the spelling an author writes for a CALLEE. This
//@ probe-note: probe is about the identity the compiler uses for the CONTRACTED
//@ probe-note: FUNCTION ITSELF — the key that binds `result` to that function's
//@ probe-note: imported defining equation. Until 2026-08-26 the ensures lane derived
//@ probe-note: that identity from `tcx.item_name`, i.e. the BARE name, which re-enters
//@ probe-note: the ambiguity keyspace `record_fn_facets` deliberately evicts. Here
//@ probe-note: `g::min2` and `other::min2` both claim `min2`, so the bare key is
//@ probe-note: evicted, `elaborate_ensures` bailed BEFORE building a goal, and the
//@ probe-note: citation was checked against the (generally false) forall-over-`result`
//@ probe-note: reading. NOTHING an author could write fixed it: the contract lives on
//@ probe-note: `g::min2` and the compiler already knows which item that is.
//@ probe-note:
//@ probe-note: The fix keys the ensures-discharge lane on the CANONICAL def-path
//@ probe-note: (`trust_spec_elab::self_fn_spelling`) — the same string
//@ probe-note: `record_fn_facets` keys the record by, and one that is never something
//@ probe-note: an author wrote. Eviction is untouched: d17 pins that an ambiguous BARE
//@ probe-note: spelling in a clause still fails closed.
//@ probe-note:
//@ probe-note: MEASURED on the pre-fix stage2 (2087f5b4220, 2026-08-26): admissible=true
//@ probe-note: recognize=Some(Select) for BOTH `probe::g::min2` and `probe::other::min2`,
//@ probe-note: the island kernel-checks, and the citation is still refused — the body is
//@ probe-note: admitted and the theorem is good, only the self KEY was wrong. This probe
//@ probe-note: is therefore RED until the def-path keying fix is in the built compiler;
//@ probe-note: it is the pin for that fix, not a regression.
//@ probe-note:
//@ probe-note: `other::min2` exists purely to create the bare-name collision; it carries
//@ probe-note: no contract and is never cited.
clean {
    theorem min2_self_thm : forall (a : UInt64) (b : UInt64),
        Nat.le (UInt64.toNat (trust_import_probe__g__min2 a b)) (UInt64.toNat a) :=
        fun a b => Decidable.casesOn
            (motive := fun (d : Decidable (LT.lt a b)) =>
                Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                    d (fun _ => b) (fun _ => a))) (UInt64.toNat a))
            (instDecidableUInt64Lt a b)
            (fun h => Iff.mp (Nat.not_lt (UInt64.toNat a) (UInt64.toNat b)) h)
            (fun h => @Nat.le.refl (UInt64.toNat a))
}

pub mod g {
    pub fn min2(a: u64, b: u64) -> u64
        ensures result <= a by min2_self_thm
    {
        if a < b { a } else { b }
    }
}

pub mod other {
    pub fn min2(a: u64, b: u64) -> u64 {
        a
    }
}
