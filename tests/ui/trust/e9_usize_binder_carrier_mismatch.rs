//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ only-64bit
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! CLOSE NEGATIVE TWIN of `e9_usize_binder_discharge`: admitting `usize` clause
//! binders admitted NOTHING except the clause read at the target's own
//! fixed-width carrier. Every function below differs from a passing function in
//! that fixture by ONE thing, and every one must stay a hard error.
//!
//!   * `wrong_carrier` — the theorem is stated over `BitVec 64`. Same width,
//!     different carrier; a clause is never coerced. (This is gates probe `p10`
//!     verbatim: it is what a reader of `Domain::USize`'s docs would write.)
//!   * `wrong_width` — the theorem is stated over `UInt32`. This is the HOST-side
//!     half of the width control: a proof at one width must not close a `usize`
//!     clause at another. The other half (a 64-bit theorem on a 32-bit target)
//!     is pinned by the `trust-spec-elab`/`trust-certify` unit tests named in the
//!     positive fixture, because no ui lane here runs a non-host pointer width.
//!   * `wrong_signedness` — the signed theorem on the unsigned clause.
//!   * `island_wrong_carrier` — the uncited defeq lane, island def over
//!     `BitVec 64`. It is refused by the carrier the island RETURNS, because the
//!     relation is typed (at `UInt64`, from `result`) before any argument is;
//!     until E9-RESULT-CARRIER-1 the first refusal reached was its parameter's.
//!   * `island_diverges` — MUTATION CONTROL: right carrier, wrong definition. If
//!     this discharged, the positive fixture's `keep` would prove nothing.
//!
//! Each refusal on a clause that NAMES a pointer-sized binder also carries the
//! note giving the carrier that binder took and what to write instead (v7/D3).
//!
//! EVERY error is annotated here — there is deliberately no
//! `dont-require-annotations: ERROR` — so an unexpected extra refusal, or one
//! of these turning into a different class, fails the test. The ERROR
//! annotations pin the REASON and not the message prefix: on the parent commit
//! every function below is refused with the same prefix and the reason
//! "unsupported clause variable type `usize`", so a prefix-only pin would pass
//! without the fix. Measured both ways on 2026-09-17 (stage1 with the change,
//! stage2 built from the parent commit).

clean {
    def idbv (n : BitVec 64) : BitVec 64 := n
    def bump_us (n : UInt64) : UInt64 := UInt64.add n 1

    theorem bv64_le_refl : forall (x : BitVec 64),
        Nat.le (BitVec.toNat x) (BitVec.toNat x) :=
        fun x => Nat.le.refl (BitVec.toNat x)

    theorem u32_ge_refl : forall (x : UInt32),
        Nat.le (UInt32.toNat x) (UInt32.toNat x) :=
        fun x => Nat.le.refl (UInt32.toNat x)

    theorem i64_le_refl : forall (x : BitVec 64),
        Nat.le (Nat.xor (BitVec.toNat x) 9223372036854775808)
               (Nat.xor (BitVec.toNat x) 9223372036854775808) :=
        fun x => Nat.le.refl (Nat.xor (BitVec.toNat x) 9223372036854775808)
}

pub fn wrong_carrier(n: usize) -> usize
    ensures n <= n by bv64_le_refl
    //~^ ERROR citation `bv64_le_refl` failed the strict Clean statement/certification audit
    //~| NOTE on this 64-bit target `n: usize` binds as `u64` (Clean carrier `UInt64`)
{
    n
}

pub fn wrong_width(n: usize) -> usize
    ensures n >= n by u32_ge_refl
    //~^ ERROR citation `u32_ge_refl` failed the strict Clean statement/certification audit
{
    n
}

pub fn wrong_signedness(n: usize) -> usize
    ensures n <= n by i64_le_refl
    //~^ ERROR citation `i64_le_refl` failed the strict Clean statement/certification audit
{
    n
}

pub fn island_wrong_carrier(n: usize) -> usize
//~^ ERROR Trust Level 0 safety verification incomplete for `e9_usize_binder_carrier_mismatch::island_wrong_carrier`
//~| ERROR Trust strict verification failed for `e9_usize_binder_carrier_mismatch::island_wrong_carrier`
    ensures result == idbv(n)
    //~^ ERROR definition `idbv` was not discharged by definitional equality: admitted `idbv` declares its result at carrier `BitVec 64`, but the comparison is at carrier `UInt64`
    //~| NOTE on this 64-bit target `n: usize` binds as `u64` (Clean carrier `UInt64`)
{
    n
}

pub fn island_diverges(n: usize) -> usize
//~^ ERROR Trust Level 0 safety verification incomplete for `e9_usize_binder_carrier_mismatch::island_diverges`
//~| ERROR Trust strict verification failed for `e9_usize_binder_carrier_mismatch::island_diverges`
    ensures result == bump_us(n)
    //~^ ERROR the Clean island definition `bump_us` was not discharged by definitional equality: the two sides are not definitionally equal
{
    n
}

fn main() {
    let _ = wrong_carrier(1);
    let _ = wrong_width(2);
    let _ = wrong_signedness(3);
    let _ = island_wrong_carrier(4);
    let _ = island_diverges(5);
}
