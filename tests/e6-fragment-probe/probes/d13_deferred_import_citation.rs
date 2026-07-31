//@ probe-shape: Select
//@ probe-expect: discharged
//@ probe-note: ITEM 10, PHASE 2 — a clause cited to a theorem that lives in a DEFERRED
//@ probe-note: island now discharges. This file was the phase-2 NEGATIVE probe; the
//@ probe-note: objection it recorded is unchanged and still holds. Read that objection
//@ probe-note: before touching this lane, because it rules out the obvious design:
//@ probe-note:
//@ probe-note:   The deferred theorem must NOT become in-walk proof authority by replaying
//@ probe-note:   its text into a per-body environment clone. Threading the session's real
//@ probe-note:   FileContext is necessary but NOT sufficient: the walk holds only the
//@ probe-note:   program admissions accumulated so far, while the authoritative check runs
//@ probe-note:   after the complete optimized-MIR inventory exists. So the same island
//@ probe-note:   text can elaborate to a DIFFERENT term in-walk than the term the
//@ probe-note:   authoritative check produces. Two implementations tried it; both compiled
//@ probe-note:   and both went green on this whole corpus.
//@ probe-note:
//@ probe-note: What changed is not the objection but the PLACEMENT. Parity cannot be
//@ probe-note: established inside the walk at any level of care, so the ISLAND no longer
//@ probe-note: moves into the walk — the DISCHARGE moves out of it. An unresolved citation
//@ probe-note: is recorded as pending, the body's entire authority-dependent output is
//@ probe-note: quarantined, and the adjudication runs where the authoritative citation
//@ probe-note: sweep already runs. Parity then holds by construction, item by item:
//@ probe-note: context and Environment are the session's own (not a clone), the facet
//@ probe-note: table is composed from the complete accumulation, program admissions are
//@ probe-note: minted, and the eager walk has finished.
//@ probe-note:
//@ probe-note: The pre-publication barrier this probe demanded is what makes that legal:
//@ probe-note: no report, envelope, cache entry, or proof-authorized MIR rewrite is
//@ probe-note: published for a pending body until it has been adjudicated. The body stays
//@ probe-note: credited in the coverage inventory and its SOLE envelope is withheld, never
//@ probe-note: amended by a second one.
//@ probe-note:
//@ probe-note: f22/f23/f24 are the negatives that keep this honest: a theorem that does
//@ probe-note: not prove the goal, a name that exists nowhere, and a REJECTED deferred
//@ probe-note: suffix whose partial environment must grant nothing.
//@ probe-note:
//@ probe-note: Note the clause is result-free — a forall-params statement about `min2`,
//@ probe-note: which is true, proved by a real kernel theorem. d14 is the stronger shape
//@ probe-note: where the clause mentions `result` and the self-admission gate also fires.
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
    ensures min2(x, y) <= x by min2_import_thm
{
    x
}
