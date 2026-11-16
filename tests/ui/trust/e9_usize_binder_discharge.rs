//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ only-64bit
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! E9 POSITIVE: `usize`/`isize` clause binders discharge in BOTH E9 lanes.
//!
//! Before this fixture every clause on a `usize` function was refused with
//! "unsupported clause variable type `usize` (supported: nat, u8, …, usize64,
//! …)" — in the cited lane as a hard "outside the exact statement fragment"
//! error, in the uncited island-defeq lane as "was not discharged by
//! definitional equality". The clause elaborator refuses a bare `usize` on
//! purpose (the name does not say which carrier it means); the compiler now
//! resolves the row from the compilation TARGET's pointer width before either
//! lane sees it (`trust_fn_discharge_binder_types`).
//!
//! THE CARRIER A USER WRITES. `usize` binds exactly as the fixed-width unsigned
//! integer of the target's width — `UInt64` here — and `isize` exactly as the
//! signed one (`BitVec 64` under the sign-flip order key, as `i64`). That is the
//! carrier the function's E6 kernel import is minted at, which is what makes a
//! `result`-mentioning clause typecheck against it. `USize`, `Nat` and (for
//! `usize`) `BitVec 64` are different carriers and are never coerced to; the
//! close negative twin `e9_usize_binder_carrier_mismatch` pins each refusal.
//!
//! `only-64bit`: the theorems below are stated at 64 bits and MUST NOT close
//! these clauses on a narrower target (there the same clause quantifies over
//! `UInt32`/`UInt16`). No ui lane here runs a non-host pointer width, so that
//! width negative control is pinned where it can run: `trust-spec-elab`
//! `discharge_binders_resolve_pointer_sized_names_at_the_target_width_only` and
//! `trust-certify`
//! `usize_discharge_binders_take_the_import_carrier_at_the_target_width`.
//!
//! Each function also pins the per-function `of which N kernel-certified by the
//! clean CIC kernel` note, not only the clause-level discharge note. The sweep
//! emits its own note from a lane that installs no authority, so pinning only
//! that one would stay green if the AUTHORITY-bearing in-walk discharge still
//! read the target-blind binder table.

clean {
    def id_us (n : UInt64) : UInt64 := n

    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => @Nat.le.refl (UInt64.toNat x)

    theorem i64_le_refl : forall (x : BitVec 64),
        Nat.le (Nat.xor (BitVec.toNat x) 9223372036854775808)
               (Nat.xor (BitVec.toNat x) 9223372036854775808) :=
        fun x => @Nat.le.refl (Nat.xor (BitVec.toNat x) 9223372036854775808)
}

// UNCITED island defeq, `result`-mentioning — the measured repro (e6 fragment
// probe `f15`, gates probe `p6`).
pub fn keep(n: usize) -> usize
//~^ NOTE of which 2 kernel-certified by the clean CIC kernel
    ensures result == id_us(n)
    //~^ NOTE island definition `id_us` kernel-discharges this postcondition by definitional equality
{
    n
}

// CITED, result-free — the measured repro (gates probe `p10`, with the theorem
// restated at the carrier `usize` actually takes).
pub fn refl(n: usize) -> usize
//~^ NOTE of which 2 kernel-certified by the clean CIC kernel
    ensures n >= n by u64_ge_refl
    //~^ NOTE citation `u64_ge_refl` kernel-discharges this postcondition statement
{
    n
}

// CITED, `result`-mentioning — the measured repro (probe-proof `29-cited-usize`).
// This is the form that needs the binder and the import to AGREE on a carrier.
pub fn keep_cited(x: usize) -> usize
//~^ NOTE of which 2 kernel-certified by the clean CIC kernel
    ensures result >= x by u64_ge_refl
    //~^ NOTE citation `u64_ge_refl` kernel-discharges this postcondition statement
{
    x
}

// `isize`, cited.
pub fn keep_signed(n: isize) -> isize
//~^ NOTE of which 2 kernel-certified by the clean CIC kernel
    ensures result <= n by i64_le_refl
    //~^ NOTE citation `i64_le_refl` kernel-discharges this postcondition statement
{
    n
}

fn main() {
    let _ = keep(1);
    let _ = refl(2);
    let _ = keep_cited(3);
    let _ = keep_signed(-4);
}
