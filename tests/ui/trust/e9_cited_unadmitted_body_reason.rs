//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ dont-require-annotations: ERROR
//! DIAGNOSTIC fixture: a cited `result`-binding clause on a function whose body
//! has no E6 kernel import must say THAT, not print a kernel term dump.
//!
//! `result` has a kernel denotation only when the specified function is
//! E6-admitted. When it is not, the postcondition goal cannot be built, and the
//! sweep falls back to grading the clause with `result` universally quantified
//! — a generally false statement no honest theorem proves. The only thing
//! reported used to be that fallback's raw `TypeMismatch { expected: Pi(..) }`
//! dump; the actual cause ("ensures discharge requires the specified function
//! to be E6-admitted; it is not") was visible only in
//! `-Ztrust-dump=spec-clean`. The refusal now LEADS with the cause, says which
//! E6 facet or body shape kept the function out of the import, lists options
//! (v7/D3), and keeps the kernel detail as a trailing note.
//!
//! Nothing here is a verdict change: both functions were refused before and are
//! refused now, and the message HEAD is unchanged, so every existing
//! "citation .. failed the strict Clean statement/certification audit" pin
//! still matches (`e9_arbitrary_body_result_undischarged` has this file's first
//! body). Option (2) of the help text is real and is pinned green by
//! `e9_arbitrary_body_result_free_discharge`. (The pin is quoted without its
//! annotation marker on purpose: compiletest parses a marker out of ANY line,
//! prose included, and would mint a second, unsatisfiable expectation.)
//!
//! `dont-require-annotations: ERROR` tolerates only secondary
//! strict-verification errors; the refusal under test is pinned explicitly.

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
    theorem u32_le_refl : forall (x : UInt32),
        Nat.le (UInt32.toNat x) (UInt32.toNat x) :=
        fun x => Nat.le.refl (UInt32.toNat x)
}

// A let-chained xor body: pure and total, but not a kernel-importable shape.
pub fn busy(x: u64) -> u64
    ensures result >= x by u64_ge_refl
    //~^ ERROR the postcondition goal could not be built (ensures discharge requires the specified function
    //~| HELP options: (1) reduce the body to an E6-importable shape
{
    let a = x ^ 3;
    let b = a ^ 3;
    b
}

// A loop body: the clause is TRUE and the solver lanes prove it, yet the `by`
// citation is still a hard error, because a citation is a claim the kernel must
// be able to check. The message has to say why it could not.
pub fn drain(limit: u32) -> u32
    ensures result <= limit by u32_le_refl
    //~^ ERROR the postcondition goal could not be built (ensures discharge requires the specified function
{
    let mut n = limit;
    while n > 0
        invariant n <= limit
        decreases n
    {
        n -= 1;
    }
    n
}

fn main() {
    let _ = (busy(1), drain(3));
}
