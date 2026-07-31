//@ probe-shape: Select
//@ probe-expect: island-only
//@ probe-note: ITEM 10, PHASE 1 — an island theorem stated over the Rust function
//@ probe-note: itself, via its E6 kernel import, rather than restating the body and
//@ probe-note: hoping the restatement matches the compiler's encoding.
//@ probe-note:
//@ probe-note: BEFORE: this file did not compile. `trust_check_clean_islands` runs
//@ probe-note: before `trust_mint_program_admissions`, so `trust_import_probe__min2`
//@ probe-note: did not exist when the island was elaborated; the declaration died on
//@ probe-note: an unknown constant AND tainted the session, which then could not mint
//@ probe-note: discharge evidence for anything else in the crate.
//@ probe-note:
//@ probe-note: NOW: an island whose text names the `trust_import_` namespace is
//@ probe-note: DEFERRED — before `check` is called, because `check` taints on
//@ probe-note: rejection — and elaborated in a second phase after the mint. A failure
//@ probe-note: there is a hard error, so deferral cannot become a way for an unchecked
//@ probe-note: declaration to reach the environment.
//@ probe-note:
//@ probe-note: `island-only` is the honest expectation for phase 1. The theorem CHECKS,
//@ probe-note: but it cannot yet DISCHARGE a clause: the in-walk discharge lanes run
//@ probe-note: during the body walk, which precedes the mint, and they mint into their
//@ probe-note: own per-body environment clone. Making a citation over an imported
//@ probe-note: constant discharge is item 10's second increment. The second island
//@ probe-note: below intentionally omits `trust_import_`: it pins that the whole
//@ probe-note: stateful suffix is deferred, so authored declaration order is preserved.
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
    theorem min2_import_thm_again : forall (a : UInt64) (b : UInt64),
        Nat.le (UInt64.toNat (trust_import_probe__min2 a b)) (UInt64.toNat a) :=
        min2_import_thm
}

pub fn min2(a: u64, b: u64) -> u64 {
    if a < b { a } else { b }
}
