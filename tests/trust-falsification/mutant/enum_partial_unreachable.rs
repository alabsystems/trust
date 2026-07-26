#![crate_type = "lib"]
#![feature(core_intrinsics)]
#![allow(internal_features, dead_code)]

// SOUNDNESS MUTANT for build #76 (typed-CHC enum exhaustiveness).
// The selector IS a genuine enum discriminant (so steps 1-3 of the gate pass:
// otherwise→Unreachable, single-assignment Discriminant temp, enum type), BUT
// the match is NON-EXHAUSTIVE: variant `C` is not covered. cases={A,B} != full
// tag set {A,B,C}, so step (4) MUST reject and the otherwise guard stays
// `(selector ∉ cases)` — SAT for selector=C. The `unreachable_unchecked` is real
// UB when e==C, so the obligation MUST stay refuted (fail-closed). If build #76
// ever conjoins `selector ∈ cases` here, it would FALSELY prove reachable UB.
pub enum E {
    A,
    B,
    C,
}

pub fn classify(e: E) -> u8 {
    match e {
        E::A => 10,
        E::B => 20,
        _ => unsafe { std::intrinsics::unreachable() },
    }
}
