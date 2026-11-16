//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off --crate-type=lib
// INVALID-cluster root 2 (full-population frontier, wave-full-0831): a
// NICHE tag encoding whose untagged variant plus niche interval does NOT
// cover every variant — an UNINHABITED variant (`V2 { f: Infallible }`)
// gets no encoding from rustc's layout because no value of it exists —
// DECLINES the layout descriptor fail-closed instead of emitting the
// faithful-but-validator-refused claim ('the niche interval plus the
// untagged variant to cover every variant', 3 of the 16 full-population
// INVALID modules). The enum then registers without layout evidence or
// falls to the opaque lane, where the wave-EMO split lowers its matches:
// the bodies keep their coverage, the module stays valid, and no claim is
// minted either way. Until trust-ir's validator models uninhabited
// variants, this is the sound boundary.
#![allow(unreachable_patterns)]

pub enum Infallible {}

pub enum E1 {
    V1 { f: bool },
    V2 { f: Infallible },
    V3,
    V4,
}

pub fn classify(e: &E1) -> i64 {
    match e {
        E1::V1 { .. } => 1,
        E1::V3 => 3,
        E1::V4 => 4,
        _ => 0,
    }
}
