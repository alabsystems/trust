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
//! unproved and strict verification fails closed.

#[cfg(both_legs)]
pub fn feedback_closes(mut phase: u32) //[both_legs]~ NOTE Trust verification: 4 proved, 0 failed, 0 unknown
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
pub fn one_leg_is_not_authority(phase: u32) //[one_leg]~ NOTE Trust verification: 2 proved, 2 failed, 0 unknown
//[one_leg]~| NOTE [termination] FAILED
//[one_leg]~| ERROR Trust strict verification failed for
    requires phase <= 1
{
    let mut remaining = 1u32;
    while phase > 0 invariant remaining >= phase decreases remaining {
        remaining = 0;
    }
}

fn main() {}
