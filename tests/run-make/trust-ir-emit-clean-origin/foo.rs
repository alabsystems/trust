//! Trust (IR-1): one file, two languages, ONE trust-ir Module.
//! The island def is the Clean producer's row; the Rust fn is the THIR
//! producer's row. `cleanWsum` is also the bounded W2 carrier-gate target:
//! actual TrustIR Add over UInt64, independently reflected and kernel-checked.
//! See ../trust-ir-emit for the base artifact-lane contract.

mod m {
    clean {
        def cleanWsum (a : UInt64) (b : UInt64) : UInt64 := a + b

        inductive Tri where
          | one : Tri
          | two : Tri
          | three : Tri

        def triRank (t : Tri) : UInt64 :=
          match t with
          | Tri.one => 1
          | Tri.two => 2
          | Tri.three => 3
    }
}

/// The Rust half, named distinctively (same discipline as battery lane E).
pub fn rust_half(x: u64) -> u64 {
    x
}

/// IR-5: the same-crate call edge under test — assemble mints a fail-closed
/// declaration for it, and the link pass must re-point it at the carrier-gated
/// appended definition. This is not the still-open G5 cross-crate contract.
pub fn calls_clean(x: u64) -> u64 {
    m::cleanWsum(x, 1)
}
