//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// INVALID root 3 (full-population frontier, wave-full-0831 — the
// UnreachableBlock pair): an enum-match arm whose discriminant is already
// claimed by an EARLIER FLAT arm is DEAD — rustc only warns
// `unreachable_patterns` and keeps it in THIR, but `seen_discr` gives the
// Switch case to the first arm and a flat arm's entry has no miss edge,
// so lowering the later arm minted an ORPHAN block (UnreachableBlock in
// `validate_module`, tests/ui/consts/const-pattern-variant.rs +
// const-pattern-not-const-evaluable.rs). The case build now SKIPS such an
// arm — never minting its blocks — which is exact, not a dedup gamble:
// first-match-wins plus the earlier claimant's irrefutability proves the
// body cannot run. The skip is keyed on the earlier arm being FLAT: a
// GUARDED first arm keeps its same-disc successor live through the
// wave-NP fallthrough edge (#187's reason dedup is unsound there).
#![allow(unreachable_patterns)]

#[derive(PartialEq, Eq)]
pub enum Cake {
    BlackForest,
    Marmor,
}

const GOO: Cake = Cake::Marmor;
const WORKS: Cake = Cake::Marmor;

// The trio shape: GOO and WORKS expand to the SAME variant; the WORKS arm
// is shadowed by the flat GOO arm and must be skipped, not orphaned.
pub fn shadowed_const_arm(c: Cake) -> i64 {
    match c {
        Cake::BlackForest => 1,
        GOO => 2,
        WORKS => 3,
        _ => 4,
    }
}

// Negative control: the first same-disc arm is GUARDED, so the second is
// LIVE (guard-false falls through). The skip must NOT fire here — this is
// exactly the case that makes blind dedup a wrong answer, not a cleanup.
pub fn guarded_first_stays_live(c: Cake, g: bool) -> i64 {
    match c {
        Cake::Marmor if g => 10,
        Cake::Marmor => 20,
        Cake::BlackForest => 30,
    }
}

// The payload spelling of the same hazard: a duplicate payload-binding
// single-variant arm (NOT an or-pattern, so G5 does not refuse it) was an
// orphan block too; it heals under the same key.
pub enum P {
    A(i64),
    B,
}

pub fn shadowed_payload_arm(p: P) -> i64 {
    match p {
        P::A(x) => x,
        P::A(y) => y + 100,
        P::B => 0,
    }
}

fn main() {
    assert_eq!(shadowed_const_arm(Cake::Marmor), 2);
    assert_eq!(guarded_first_stays_live(Cake::Marmor, false), 20);
    assert_eq!(shadowed_payload_arm(P::A(7)), 7);
}
