//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@ edition: 2021
//@ dont-check-compiler-stderr
//@ check-pass
#![crate_type = "lib"]
//! #189: a `for` loop must not havoc an opaque-carrier local at its PLACEHOLDER type.
//!
//! An opaque-carrier local's DECLARED type is the placeholder `Ty::Unit`, while its
//! VALUE is spelled at the real mapped sort — the wave-ER bind ledgers exactly that
//! disagreement in `opaque_carrier_value_spellings`. The split is sound only while
//! nothing manufactures a value FROM the declared type.
//!
//! `try_lower_foreach_summary`'s havoc loop did: it read `local_ty` and emitted
//! `Inst::Undef { ty }`, rebinding the local to a genuinely `()`-typed SSA value that
//! carries no ledger row — so every launder gate was structurally blind to it and the
//! `()` shipped to whatever typed sink consumed the local. That is BOTH observed faces
//! of #189, from one mint:
//!
//!     implicit Return          -> ReturnTypeMismatch  { expected: "struct.N", actual: "()" }
//!     struct-literal InsertField -> OperandTypeMismatch { op: "insert_field", role: "value" }
//!
//! Measured on the unpatched sealed toolchain (trust-6500fd4d), both bodies below fail;
//! with the fix both compile. It is NOT `Vec`-specific — the `String` case fails
//! identically, because the defect is about opaque carriers, not about one container.
//!
//! THE FLAG POSTURE IS LOAD-BEARING. Under plain `-Ztrust-verify=on` this defect is
//! MASKED: the per-body verifier raises a fatal before `trust_ir_crate_finalize` runs,
//! so the run reports "native typed-TrustIr lowering did not complete" and the module
//! is never validated. A strict-policy run therefore proves nothing here, and an
//! earlier investigation concluded from exactly that mistake that the minimal case did
//! not reproduce #189. It does. Keep `-Ztrust-verify=off -Ztrust-ir-lower=on`.
//!
//! WHAT THE FIX IS NOT. It does not mint a different placeholder, and it does not
//! relax the validator or exempt `Ty::Unit` at `insert_field`. It REFUSES the foreach
//! summary when the carrier ledger disagrees with the declared type — the #188
//! template: when a value cannot be truthfully typed, make the contradiction
//! unrepresentable rather than paper over it. These bodies consequently stop being
//! lowered and, under `-Ztrust-verify=on`, still fail closed as unmodelled. That is
//! an unblock, not a green verified build, and the distinction matters.
//!
//! The refusal is narrow, which the negative controls below pin: a `while` loop, a
//! push with no loop at all, and a non-carrier local are unaffected and still lower.

pub struct Tables {
    pub scale: f32,
    pub lower: Vec<f32>,
}

/// The Return face — the value reaches the implicit `Return` at the carrier sort.
pub fn ret_face() -> Vec<f32> {
    let mut b = Vec::new();
    for _ in 0..1 {
        b.push(1.0f32);
    }
    b
}

/// The InsertField face — the same value reaches a struct-literal field operand.
pub fn field_face() -> Tables {
    let mut b = Vec::new();
    for _ in 0..4 {
        b.push(1.0f32);
    }
    Tables { scale: 0.01, lower: b }
}

/// Not `Vec`-specific: `String` is an opaque carrier too and failed identically.
pub fn string_face() -> String {
    let mut s = String::new();
    for _ in 0..4 {
        s.push('x');
    }
    s
}

// ── negative controls: the refusal must stay narrow ──────────────────────────

/// A `while` loop takes no foreach summary, so it is untouched and still lowers.
pub fn while_control() -> Vec<f32> {
    let mut b = Vec::new();
    let mut i = 0;
    while i < 3 {
        b.push(1.0f32);
        i += 1;
    }
    b
}

/// Mutation with no loop at all — never reached the havoc path.
pub fn no_loop_control() -> Vec<f32> {
    let mut b = Vec::new();
    b.push(1.0f32);
    b
}

/// A non-carrier local mutated in a `for` loop: no ledger row, so the guard is
/// keyed off and this must keep taking the ordinary summary path.
pub fn non_carrier_control() -> u32 {
    let mut n = 0u32;
    for _ in 0..4 {
        n = n.wrapping_add(1);
    }
    n
}
