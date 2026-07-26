// trust-clean/fingerprint.rs: 128-bit VC fingerprinting
//
// Uses SipHash-2-4 (Rust's default hasher) for 128-bit fingerprints.
// This is NOT a cryptographic hash — it provides collision resistance
// sufficient for VC identity. Deterministic: same logical formula
// always produces the same fingerprint regardless of MIR location.
//
// Mirrors rustc_data_structures::Fingerprint in concept but is
// self-contained (no rustc dependency in this crate).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;
use std::hash::{Hash, Hasher};

use serde::{Deserialize, Serialize};
use trust_types::VerificationCondition;

use crate::canonical::canonical_vc_bytes;

/// A 128-bit fingerprint of a verification condition's logical content.
///
/// Two VCs with the same logical formula produce the same fingerprint,
/// even if they differ in source location or function name. This is
/// the stable identity used to detect stale certificates after code changes.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Fingerprint {
    hi: u64,
    lo: u64,
}

impl Fingerprint {
    /// Create a fingerprint from two 64-bit halves.
    #[must_use]
    pub fn new(hi: u64, lo: u64) -> Self {
        Fingerprint { hi, lo }
    }

    /// The high 64 bits.
    #[must_use]
    pub fn hi(self) -> u64 {
        self.hi
    }

    /// The low 64 bits.
    #[must_use]
    pub fn lo(self) -> u64 {
        self.lo
    }

    /// Convert to a 16-byte array (big-endian).
    #[must_use]
    pub fn to_bytes(self) -> [u8; 16] {
        let mut out = [0u8; 16];
        out[..8].copy_from_slice(&self.hi.to_be_bytes());
        out[8..].copy_from_slice(&self.lo.to_be_bytes());
        out
    }

    /// Reconstruct from a 16-byte array (big-endian).
    #[must_use]
    pub fn from_bytes(bytes: [u8; 16]) -> Self {
        let hi = u64::from_be_bytes(bytes[..8].try_into().expect("8 bytes"));
        let lo = u64::from_be_bytes(bytes[8..].try_into().expect("8 bytes"));
        Fingerprint { hi, lo }
    }
}

impl fmt::Debug for Fingerprint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Fingerprint({:016x}{:016x})", self.hi, self.lo)
    }
}

impl fmt::Display for Fingerprint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:016x}{:016x}", self.hi, self.lo)
    }
}

/// Compute a 128-bit fingerprint of a verification condition.
///
/// The fingerprint is computed over the canonical byte representation
/// of the VC's logical formula and kind. Source location and function
/// name are deliberately excluded — they are not part of the logical
/// identity. This means code reformatting or function renaming does
/// not invalidate certificates.
///
/// Uses SipHash-1-3 via Rust's `DefaultHasher` for determinism. The
/// hash is seeded with fixed keys (0, 0) so fingerprints are stable
/// across process invocations. This is NOT cryptographic — it provides
/// collision resistance sufficient for VC identity tracking.
#[must_use]
pub fn compute_vc_fingerprint(vc: &VerificationCondition) -> Fingerprint {
    let canonical = canonical_vc_bytes(vc);
    fingerprint_bytes(&canonical)
}

/// Compute a fingerprint directly from canonical bytes.
///
/// Exposed for testing and for cases where the caller already has
/// the canonical representation.
#[must_use]
pub fn fingerprint_bytes(bytes: &[u8]) -> Fingerprint {
    // Use SipHash with fixed keys for determinism across runs.
    // std::hash::DefaultHasher is SipHash-1-3 with fixed keys.
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    bytes.hash(&mut hasher);
    let lo = hasher.finish();

    // For the high bits, feed a discriminant byte first to get a
    // different hash lane. This gives us 128 independent bits from
    // two 64-bit SipHash runs with different prefixes.
    let mut hasher2 = std::collections::hash_map::DefaultHasher::new();
    0xFFu8.hash(&mut hasher2);
    bytes.hash(&mut hasher2);
    let hi = hasher2.finish();

    Fingerprint::new(hi, lo)
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    fn make_overflow_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "test_func".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    fn make_divzero_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_func".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    #[test]
    fn same_vc_same_fingerprint() {
        let vc1 = make_overflow_vc(Formula::Bool(true));
        let vc2 = make_overflow_vc(Formula::Bool(true));
        assert_eq!(
            compute_vc_fingerprint(&vc1),
            compute_vc_fingerprint(&vc2),
            "identical VCs must produce identical fingerprints"
        );
    }

    #[test]
    fn different_formula_different_fingerprint() {
        let vc1 = make_overflow_vc(Formula::Bool(true));
        let vc2 = make_overflow_vc(Formula::Bool(false));
        assert_ne!(
            compute_vc_fingerprint(&vc1),
            compute_vc_fingerprint(&vc2),
            "different formulas must produce different fingerprints"
        );
    }

    #[test]
    fn different_kind_different_fingerprint() {
        let vc1 = make_overflow_vc(Formula::Bool(true));
        let vc2 = make_divzero_vc(Formula::Bool(true));
        assert_ne!(
            compute_vc_fingerprint(&vc1),
            compute_vc_fingerprint(&vc2),
            "different VC kinds must produce different fingerprints"
        );
    }

    #[test]
    fn location_independent() {
        // Same formula and kind but different source locations
        let vc1 = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "func_a".into(),
            location: SourceSpan {
                file: "a.rs".to_string(),
                line_start: 1,
                col_start: 0,
                line_end: 1,
                col_end: 10,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let vc2 = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "func_b".into(),
            location: SourceSpan {
                file: "b.rs".to_string(),
                line_start: 99,
                col_start: 0,
                line_end: 99,
                col_end: 20,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        assert_eq!(
            compute_vc_fingerprint(&vc1),
            compute_vc_fingerprint(&vc2),
            "fingerprint must be independent of source location and function name"
        );
    }

    #[test]
    fn complex_formula_deterministic() {
        let formula = Formula::And(vec![
            Formula::Le(
                Box::new(Formula::Int(0)),
                Box::new(Formula::Add(
                    Box::new(Formula::Var("a".into(), Sort::Int)),
                    Box::new(Formula::Var("b".into(), Sort::Int)),
                )),
            ),
            Formula::Le(
                Box::new(Formula::Add(
                    Box::new(Formula::Var("a".into(), Sort::Int)),
                    Box::new(Formula::Var("b".into(), Sort::Int)),
                )),
                Box::new(Formula::Int((1i128 << 64) - 1)),
            ),
        ]);
        let vc1 = make_overflow_vc(formula.clone());
        let vc2 = make_overflow_vc(formula);
        assert_eq!(
            compute_vc_fingerprint(&vc1),
            compute_vc_fingerprint(&vc2),
            "complex formula must produce deterministic fingerprints"
        );
    }

    #[test]
    fn fingerprint_roundtrip_bytes() {
        let vc = make_overflow_vc(Formula::Int(42));
        let fp = compute_vc_fingerprint(&vc);
        let bytes = fp.to_bytes();
        let recovered = Fingerprint::from_bytes(bytes);
        assert_eq!(fp, recovered, "fingerprint must survive byte roundtrip");
    }

    #[test]
    fn fingerprint_display_hex() {
        let fp = Fingerprint::new(0xDEAD_BEEF_CAFE_BABE, 0x0123_4567_89AB_CDEF);
        let s = format!("{fp}");
        assert_eq!(s, "deadbeefcafebabe0123456789abcdef");
    }

    #[test]
    fn fingerprint_debug_format() {
        let fp = Fingerprint::new(0, 1);
        let s = format!("{fp:?}");
        assert!(s.starts_with("Fingerprint("));
    }
}
