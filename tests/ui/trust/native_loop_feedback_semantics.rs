//@ revisions: both_legs one_leg
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Cstrip=none
//@[both_legs] build-pass
//@[one_leg] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! Source-to-verdict E4 -> E5 feedback gate. Without the invariant, the first
//! pass cannot prove `remaining` decreases: at a loop head it permits the
//! spurious combination `phase > 0 && remaining == 0`. Once both E4 initiation
//! and consecution rows are Clean-kernel certified, `remaining >= phase` rules
//! that state out and the regenerated E5 row closes on the second pass. This
//! stays inside the admitted linear-Int certificate fragment; native proof
//! labels alone deliberately cannot mint feedback authority.
//!
//! The `one_leg` revision proves initiation but falsifies consecution by
//! retaining `phase` after assigning zero. Its still-useful pre-state predicate
//! must not be admitted from only one E4 proof, so the termination row remains
//! unproved and strict verification fails closed. (Post ay-0.9.0, the solver's
//! refutation of the encoded VC carries no producer fidelity attestation and is
//! demoted, so the unproved rows read UNKNOWN rather than FAILED.)
//!
//! COUNTS RE-PINNED 2026-09-16 for `688d2058fd`, which stopped the human summary
//! line counting a definition-entry `requires` row as PROVED. Both revisions'
//! `requires phase <= 1` row moves from the `proved` bucket into a new
//! `assumed (requires)` one — same rows, same denominator (4), an ASSUMPTION the
//! caller owes rather than a proof this body earned. So `both_legs` reads
//! `3 proved` and `one_leg` reads `1 proved`. Nothing else in either revision
//! moved: `of which 2 kernel-certified`, `[termination] UNKNOWN` and the strict
//! ERROR are byte-identical, which is what says the recategorisation is the only
//! change.

#[cfg(both_legs)]
pub fn feedback_closes(mut phase: u32) //[both_legs]~ NOTE Trust verification: 3 proved, 0 failed, 0 unknown
//[both_legs]~| NOTE of which 2 kernel-certified
    requires phase <= 1
{
    let mut remaining = 1u32;
    while phase > 0 invariant remaining >= phase decreases remaining {
        remaining = 0;
        phase = 0;
    }
}

#[cfg(one_leg)]
pub fn one_leg_is_not_authority(phase: u32) //[one_leg]~ NOTE Trust verification: 1 proved, 0 failed, 2 unknown
//[one_leg]~| NOTE [termination] UNKNOWN
//[one_leg]~| ERROR Trust strict verification failed for
    requires phase <= 1
{
    let mut remaining = 1u32;
    while phase > 0 invariant remaining >= phase decreases remaining {
        remaining = 0;
    }
}

fn main() {}
