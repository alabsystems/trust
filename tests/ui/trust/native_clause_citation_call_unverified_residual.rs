//@ revisions: off on
//@ needs-trust-verify
//@[off] compile-flags: -Ztrust-verify=off
//@[on] compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! TG3 (COMPILE-TIME-FACTS-1, 2026-11-05) CLOSES the residual this file was
//! written to expose: with verification off, the kernel-only lane E6-imports
//! every program function a cited clause calls (`ident`, `min2`) as well as the
//! cited function's own body, so both revisions now accept exactly these
//! clauses. The two revisions stay to pin that parity; the history below is
//! the pre-TG3 state.
//!
//! THE MEASURED RESIDUAL of the unverified-lane citation allowance
//! (`native_clause_citation_result_unverified`): a cited clause that CALLS a
//! program function is still a HARD ERROR under `-Ztrust-verify=off`, even
//! though the verified lane discharges it. This fixture exists to make that
//! gap visible instead of leaving it as prose — the `off` revision pins today's
//! refusal, the `on` revision pins that these are exactly the clauses the
//! verified lane accepts, and the delta between the two revisions IS the
//! residual.
//!
//! WHY it is a different verdict arm. With verification off there is no body
//! walk, so nothing is E6-admitted and `SessionFnFacets` is empty. A clause
//! naming `ident`/`min2` therefore fails `first_call_facet_error` ("no
//! diagnostic E6 facet record exists for `ident`") BEFORE any statement
//! comparison, which is `CitationVerdict::ClauseOutsideFragment`. The
//! unverified-lane allowance intercepts only
//! `StatementOrCertificationRejected` on a `result`-mentioning clause — a
//! mismatch the lane provably cannot judge — and deliberately does NOT
//! string-match a fail-closed fragment refusal into an allowance. So
//! `result_and_call` below carries `result` and is still refused: the guard is
//! the verdict arm, not the word `result`.
//!
//! These are the capstone's own clause shapes (`e9_one_program_two_languages`
//! s2/s5/s6, `e9_min2_case_split_discharge`), so this is what a converted crate
//! hits in its everyday `targo --unverified` loop. Widening the allowance to
//! this arm is a separate increment; until then, changing either revision here
//! is a deliberate act.

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => @Nat.le.refl (UInt64.toNat x)

    theorem min2_le_left : forall (x : UInt64) (y : UInt64),
        Nat.le (UInt64.toNat (if x < y then x else y)) (UInt64.toNat x) :=
        fun x y => Decidable.casesOn
            (motive := fun (d : Decidable (LT.lt x y)) =>
                Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                    d (fun _ => y) (fun _ => x))) (UInt64.toNat x))
            (instDecidableUInt64Lt x y)
            (fun h => Iff.mp (Nat.not_lt (UInt64.toNat x) (UInt64.toNat y)) h)
            (fun h => @Nat.le.refl (UInt64.toNat x))
}

pub fn ident(x: u64) -> u64 { x }
pub fn min2(a: u64, b: u64) -> u64 { if a < b { a } else { b } }

// Capstone s2/s6: a `result`-FREE clause over a program call.
pub fn call_only(x: u64) -> u64
    ensures ident(x) >= ident(x) by u64_ge_refl
{
    x
}

// Capstone s5 / `e9_min2_case_split_discharge`.
pub fn call_min2(x: u64, y: u64) -> u64
    ensures min2(x, y) <= x by min2_le_left
{
    x
}

// `result` AND a call: mentioning `result` does not buy the allowance, because
// the refusal is a fragment refusal and not a statement mismatch.
pub fn result_and_call(x: u64) -> u64
    ensures result >= ident(x) by u64_ge_refl
{
    x
}

fn main() {
    let _ = call_only(1);
    let _ = call_min2(2, 3);
    let _ = result_and_call(4);
}
