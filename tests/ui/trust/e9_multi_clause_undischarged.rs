//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! Partial-citation counterpart of `e9_multi_clause_discharge`: `x >= x` keeps
//! its `by u64_ge_refl`, `x <= x` carries no citation.
//!
//! MEASURED at HEAD (stage2 ec4783d80), this compiles clean, rc 0:
//! "4 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 4
//! obligation(s)", "of which 2 kernel-certified by the clean CIC kernel". The
//! JSON lane splits the work across two row kinds: the two clause-surface rows
//! (at the clause lines) are proved by `trust-exact-source-clause-discharge`
//! and carry NO proof evidence, while the two `vc:` rows (both at the BODY
//! line) are proved by `ay-in-process` on the `clean-kernel` backend, graded
//! KernelRechecked with an Empty axiom closure. Either way the UNCITED
//! `x <= x` comes out proved. So the old claim here, that partial
//! citation discharges nothing, is false: a reflexivity clause is closed by the
//! kernel with or without the `by` token, and the pass/fail delta this pair was
//! built on no longer exists for a clause of that shape.
//!
//! That is a stronger kernel, not a weakened gate. Measured on this same binary,
//! uncited clauses that are not tautologies stay unproved and fail strict
//! verification: `x != x`, `x < x`, `x >= 5`, and `result > x` on a body
//! returning `x`. Rebuilding the partial-citation tripwire needs a clause the
//! kernel cannot close on its own; this file no longer supplies one.

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

pub fn two(x: u64) -> u64
    ensures x >= x by u64_ge_refl
    ensures x <= x
{ x }

fn main() {}
