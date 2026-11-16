//@ revisions: default strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! BV-LANE-1 (KNOWN_HAZARDS, "the signed-BV certify lane certified any row
//! containing a bounded `BvAdd`/`BvSub`"): trust-certify's signed-BV overflow
//! lane took the first bounded `BvAdd`/`BvSub` ANYWHERE in a row's violation,
//! refuted its OWN synthesized "this add overflows" system, and minted the
//! certificate under the row's identity. A false `i128` postcondition over a body
//! the verifier does not model (`wrapping_add`, `wrapping_sub`, `max`) reaches
//! that lane with a satisfiable violation such as
//! `0 <= a,b < 10 ∧ ¬¬(_0 = a + b)`, and came out Certified/KernelRechecked. Every
//! `i128` function below built exit 0 under all three policies on the wave-10
//! stage 1 (`stage1-w10`, the stage 1 of `1ab78ed8e8`), and a binary
//! whose `main` returned `p(1, 2)` (`not_the_sum`'s shape) as its exit code
//! exited 3, the value the certified `ensures result != a + b` excludes.
//!
//! The lane now discharges a row only when the row ASSERTS the exact signed
//! overflow predicate of that add/sub as top-level conjuncts, so each false
//! `ensures` below is an unproved row and the build fails. The `i64` twin
//! (`p64`) was refused before only by accident (the bound reader misread the
//! type-range literal `BitVec{2^63, 64}` as positive); the reader now decodes
//! it, and the twin pins that the gate, not the misread, refuses it.
//!
//! Controls (unannotated ERRORs would fail the test): the genuine guarded `i128`
//! add `g` and the `i64 → i128` widened sub `ws` keep their overflow rows
//! kernel-certified by this lane on every policy.

pub fn off_by_one(a: i128, b: i128) -> i128
//~^ ERROR Trust strict verification failed
    requires a >= 0 && a < 10 && b >= 0 && b < 10
    ensures result == a + b + 1
{
    a.wrapping_add(b)
}

pub fn strictly_greater(a: i128, b: i128) -> i128
//~^ ERROR Trust strict verification failed
    requires a >= 0 && a < 10 && b >= 0 && b < 10
    ensures result > a + b
{
    a.wrapping_add(b)
}

pub fn not_the_sum(a: i128, b: i128) -> i128
//~^ ERROR Trust strict verification failed
    requires a >= 0 && a < 10 && b >= 0 && b < 10
    ensures result != a + b
{
    a.wrapping_add(b)
}

pub fn diff(a: i128, b: i128) -> i128
//~^ ERROR Trust strict verification failed
    requires a >= 0 && a < 10 && b >= 0 && b < 10
    ensures result == a - b + 5
{
    a.wrapping_sub(b)
}

pub fn mx(a: i128, b: i128) -> i128
//~^ ERROR Trust strict verification failed
    requires a >= 0 && a < 10 && b >= 0 && b < 10
    ensures result == a + b
{
    a.max(b)
}

// The clause only MENTIONS the add, in a disjunct; it is false at every input
// in range.
pub fn far(a: i128, b: i128) -> i128
//~^ ERROR Trust strict verification failed
    requires a >= 0 && a < 10 && b >= 0 && b < 10
    ensures result == 7 || a + b > 100
{
    a.wrapping_add(b)
}

pub fn p64(a: i64, b: i64) -> i64
//~^ ERROR Trust strict verification failed
    requires a >= 0 && a < 10 && b >= 0 && b < 10
    ensures result != a + b
{
    a.wrapping_add(b)
}

pub fn g(a: i128, b: i128) -> i128 {
    //~^ NOTE of which 1 kernel-certified by the clean CIC kernel
    if a > -1000 && a < 1000 && b > -1000 && b < 1000 { a + b } else { 0 }
}

pub fn ws(a: i64, b: i64) -> i128 {
    //~^ NOTE of which 1 kernel-certified by the clean CIC kernel
    (b as i128) - (a as i128)
}
