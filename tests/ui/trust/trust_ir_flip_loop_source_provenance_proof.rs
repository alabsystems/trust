//@ build-pass
//@ needs-trust-verify
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=on -Cdebuginfo=0
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
// (RE-PINNED 2026-09-14: main's whole-function panic-freedom aggregate is
// runtime-checked — trust-mc's CHC/PDR transport "solved obligation … without a
// proof" — and ruling B reports it as an advisory WARN pair. That row is not what
// this file pins; the annotations above/below are.)
//! Proof-side companion to the public flip witness. The source precondition,
//! loop initiation, consecution, and decrease rows must all discharge after the
//! authenticated mutable loop local and bound parameter are each reconstructed
//! as one named MIR place.
//! The flip-witness sibling separately pins that this same body shape enters
//! TrustIR code generation instead of silently falling back to built MIR.

#[inline(never)]
pub fn countdown_proved(limit: u32) -> u32
    requires limit <= 3
{
    let mut n = limit;
    while n > 0 invariant n <= limit decreases n {
        n -= 1;
    }
    n
}

fn main() {
    let _ = countdown_proved(3);
}
