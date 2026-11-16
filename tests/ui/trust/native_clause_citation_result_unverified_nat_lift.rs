//@ revisions: off on
//@ needs-trust-verify
//@[off] compile-flags: -Ztrust-verify=off
//@[on] compile-flags: -Ztrust-verify=on
//@ check-pass
//@ only-64bit
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! TG3 (COMPILE-TIME-FACTS-1, 2026-11-05) SUPERSEDES the history below: the
//! unverified-lane allowance it describes is gone. With verification off the
//! kernel-only lane E6-imports the cited functions' bodies, so the `off`
//! revision now judges every `result` clause exactly as `on` does — the
//! "NOT checked" note is never printed, and a false `result` citation is a hard
//! error in both revisions. The two revisions stay so that this parity is pinned.
//!
//! d1 (2026-09-28): a cited `ensures` that uses the explicit lift (`x as nat`,
//! spec surface §12.3) must BUILD with verification off, exactly as its unlifted
//! twin `native_clause_citation_result_unverified` does.
//!
//! It did not (MEASURED on pack 4d9a20e3daf, raw `trustc` and `targo
//! --unverified check`): `off` failed with "citation `dec_is_spec` cannot be
//! validated because this clause is outside the exact statement fragment:
//! admitted `spec_ge` declares parameter 0 at carrier `Nat`, but the argument is
//! a `u16` term", while `on` certified the same citation. The E9 sweep reads a
//! cited `ensures` in two rungs: the postcondition DISCHARGE (`result` bound to
//! the imported body) ran at `ClauseMode::ProofLift`, and the ∀-`result`
//! FALLBACK ran at `Strict`, where `x as nat` does not exist. With verification
//! off no body is imported, the discharge cannot bind `result`, and the Strict
//! fallback refused the lift as a FRAGMENT error — which the unverified-lane
//! allowance (a statement-mismatch arm, by design) does not relax. The fix runs
//! the fallback in the discharge rung's mode; the allowance is unchanged.
//!
//! Rows, each MEASURED failing `off` before the fix (critique probes p4/p5 and
//! the report's repro) and MEASURED certifying `on`:
//!   * `ge512` — the report's repro (`apdf-lzw-width`'s shape);
//!   * `ident16` — a lift of `result` itself (`(result as nat) == …`), whose
//!     pre-fix `off` message was "unsupported term shape" instead: a fix keyed
//!     on the carrier message would miss it;
//!   * `small` — the same over `usize`, which the discharge binder table
//!     resolves to `u64` on this (64-bit) target.
//! `ge512_bridge` is the result-FREE control: it needs no body, so it is judged
//! — and discharged — in BOTH lanes, before and after (MEASURED, probe c).
//! `first` (two lifted arguments over `u64`) is INFERRED from the uncited
//! `nat_lift_defeq_discharge` and the `ident16` row, not measured.
//!
//! The close negative twin — type errors, missing/non-theorem citations, the
//! body mutant, the guard-widening detectors — is
//! `native_clause_citation_result_unverified_nat_lift_false`; the program-call
//! residual stays pinned, unchanged, by
//! `native_clause_citation_call_unverified_residual`.

clean {
    def spec_ge (n : Nat) : Bool :=
        Decidable.decide (Nat.le 512 n) (Nat.decLe 512 n)
    def dec_ge (n : UInt16) : Bool :=
        Decidable.decide (LE.le (UInt16.ofNat 512) n) (instDecidableUInt16Le (UInt16.ofNat 512) n)
    theorem dec_is_spec : forall (n : UInt16),
        Eq (dec_ge n) (spec_ge (UInt16.toNat n)) :=
        fun n => Eq.refl (dec_ge n)

    def spec_id (n : Nat) : Nat := n
    theorem toNat_id : forall (x : UInt16), Eq (UInt16.toNat x) (spec_id (UInt16.toNat x)) :=
        fun x => Eq.refl (UInt16.toNat x)

    def spec_small (n : Nat) : Bool :=
        Decidable.decide (Nat.lt n 4096) (Nat.decLt n 4096)
    def dec_small (n : UInt64) : Bool :=
        Decidable.decide (LT.lt n (UInt64.ofNat 4096)) (instDecidableUInt64Lt n (UInt64.ofNat 4096))
    theorem dec_small_is_spec : forall (n : UInt64),
        Eq (dec_small n) (spec_small (UInt64.toNat n)) :=
        fun n => Eq.refl (dec_small n)

    def first_nat (a : Nat) (b : Nat) : Nat := a
    theorem first_is_spec : forall (a : UInt64) (b : UInt64),
        Eq (UInt64.toNat a) (first_nat (UInt64.toNat a) (UInt64.toNat b)) :=
        fun a b => Eq.refl (UInt64.toNat a)
}

// The report's repro, verbatim.
pub fn ge512(x: u16) -> bool
    ensures result == spec_ge(x as nat) by dec_is_spec
    //~^ NOTE citation `dec_is_spec` kernel-discharges this postcondition statement
{
    512 <= x
}

// A lift of `result` (critique p5).
pub fn ident16(x: u16) -> u16
    ensures (result as nat) == spec_id(x as nat) by toNat_id
    //~^ NOTE citation `toNat_id` kernel-discharges this postcondition statement
{
    x
}

// `usize`, the dominant integer type of a converted crate (critique p4).
pub fn small(x: usize) -> bool
    ensures result == spec_small(x as nat) by dec_small_is_spec
    //~^ NOTE citation `dec_small_is_spec` kernel-discharges this postcondition statement
{
    x < 4096
}

// Two lifted arguments over `u64` (INFERRED; see the header).
pub fn first(a: u64, b: u64) -> u64
    ensures (result as nat) == first_nat(a as nat, b as nat) by first_is_spec
    //~^ NOTE citation `first_is_spec` kernel-discharges this postcondition statement
{
    a
}

// A `result`-FREE lifted clause needs no body: judged in both lanes.
pub fn ge512_bridge(x: u16) -> bool
    ensures dec_ge(x) == spec_ge(x as nat) by dec_is_spec
    //~^ NOTE citation `dec_is_spec` kernel-discharges this postcondition statement
{
    512 <= x
}

fn main() {
    let _ = ge512(600);
    let _ = ident16(7);
    let _ = small(9);
    let _ = first(3, 4);
    let _ = ge512_bridge(10);
}
