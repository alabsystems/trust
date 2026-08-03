// trust-clean/canonical.rs: Deterministic VC serialization
//
// Produces a canonical byte representation of a VerificationCondition's
// logical content. This is the input to fingerprinting and is stored
// alongside proof certificates so clean can verify the theorem statement.
//
// The canonical form includes the VC kind and formula but deliberately
// excludes source location and function name — those are not part of
// the logical identity. This means code reformatting or function renaming
// does not invalidate certificates.
//
// Serialization is deterministic: the same logical VC always produces
// the same byte sequence regardless of HashMap iteration order, pointer
// values, or other sources of non-determinism. We achieve this by using
// a structured binary encoding rather than serde_json (which may reorder
// map keys depending on the serializer configuration).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{BinOp, Formula, Sort, Ty, VcKind, VerificationCondition};

/// Magic bytes identifying the canonical VC format.
const MAGIC: &[u8; 4] = b"tVC1";

/// Serialize a VerificationCondition into canonical bytes.
///
/// The output includes only the VC kind and formula (the logical content).
/// Source location and function name are excluded. This makes fingerprints
/// stable across code movement and renaming.
#[must_use]
pub fn canonical_vc_bytes(vc: &VerificationCondition) -> Vec<u8> {
    let mut buf = Vec::with_capacity(256);
    buf.extend_from_slice(MAGIC);
    encode_vc_kind(&vc.kind, &mut buf);
    encode_formula(&vc.formula, &mut buf);
    buf
}

/// Encode a VcKind into canonical bytes.
fn encode_vc_kind(kind: &VcKind, buf: &mut Vec<u8>) {
    match kind {
        VcKind::ArithmeticOverflow { op, operand_tys } => {
            buf.push(0x01);
            encode_binop(op, buf);
            encode_ty(&operand_tys.0, buf);
            encode_ty(&operand_tys.1, buf);
        }
        VcKind::ShiftOverflow { op, operand_ty, shift_ty } => {
            buf.push(0x0D);
            encode_binop(op, buf);
            encode_ty(operand_ty, buf);
            encode_ty(shift_ty, buf);
        }
        VcKind::DivisionByZero => buf.push(0x02),
        VcKind::RemainderByZero => buf.push(0x03),
        VcKind::IndexOutOfBounds => buf.push(0x04),
        VcKind::SliceBoundsCheck => buf.push(0x05),
        VcKind::Assertion { message } => {
            buf.push(0x06);
            encode_str(message, buf);
        }
        VcKind::Precondition { callee } => {
            buf.push(0x07);
            encode_str(callee, buf);
        }
        VcKind::Postcondition => buf.push(0x08),
        VcKind::CastOverflow { from_ty, to_ty } => {
            buf.push(0x0E);
            encode_ty(from_ty, buf);
            encode_ty(to_ty, buf);
        }
        VcKind::NegationOverflow { ty } => {
            buf.push(0x0F);
            encode_ty(ty, buf);
        }
        VcKind::Unreachable => buf.push(0x09),
        VcKind::DeadState { state } => {
            buf.push(0x0A);
            encode_str(state, buf);
        }
        VcKind::Deadlock => buf.push(0x0B),
        VcKind::Temporal { property, .. } => {
            buf.push(0x0C);
            encode_str(property, buf);
        }
        // Trust: Liveness and fairness canonical encoding.
        // Tags 0xF0-0xFF reserved for temporal/liveness extensions.
        VcKind::Liveness { property, .. } => {
            buf.push(0xF0);
            encode_str(&property.name, buf);
            encode_str(&property.predicate, buf);
        }
        VcKind::Fairness { constraint } => {
            buf.push(0xF1);
            encode_str(constraint.action(), buf);
        }
        // Trust: Protocol composition verification
        VcKind::ProtocolViolation { protocol, violation } => {
            buf.push(0x10);
            encode_str(protocol, buf);
            encode_str(violation, buf);
        }
        VcKind::TaintViolation { source_label, sink_kind, path_length } => {
            buf.push(0x11);
            encode_str(source_label, buf);
            encode_str(sink_kind, buf);
            buf.extend_from_slice(&(*path_length as u64).to_le_bytes());
        }
        VcKind::RefinementViolation { spec_file, action } => {
            buf.push(0x12);
            encode_str(spec_file, buf);
            encode_str(action, buf);
        }
        VcKind::ResilienceViolation { service, failure_mode, reason } => {
            buf.push(0x13);
            encode_str(service, buf);
            encode_str(failure_mode, buf);
            encode_str(reason, buf);
        }
        VcKind::NonTermination { context, measure } => {
            buf.push(0x14);
            encode_str(context, buf);
            encode_str(measure, buf);
        }
        // Trust: tags 0x20..=0x23 are permanently retired. This encoding is a
        // certificate identity, so a byte that once meant one proposition must
        // never come to mean another; a future VcKind takes the next unused tag
        // rather than reclaiming the gap.
        // Data race and memory ordering canonical encoding.
        VcKind::DataRace { variable, thread_a, thread_b } => {
            buf.push(0x24);
            encode_str(variable, buf);
            encode_str(thread_a, buf);
            encode_str(thread_b, buf);
        }
        VcKind::InsufficientOrdering { variable, actual, required } => {
            buf.push(0x25);
            encode_str(variable, buf);
            encode_str(actual, buf);
            encode_str(required, buf);
        }
        // Translation validation.
        VcKind::TranslationValidation { pass, check } => {
            buf.push(0x26);
            encode_str(pass, buf);
            encode_str(check, buf);
        }
        // Floating-point operation VCs.
        VcKind::FloatDivisionByZero => {
            buf.push(0x29);
        }
        VcKind::FloatOverflowToInfinity { .. } => {
            buf.push(0x2a);
        }
        // Rvalue safety VCs.
        VcKind::InvalidDiscriminant { place_name } => {
            buf.push(0x27);
            encode_str(place_name, buf);
        }
        VcKind::AggregateArrayLengthMismatch { expected, actual } => {
            buf.push(0x28);
            buf.extend_from_slice(&(*expected as u64).to_le_bytes());
            buf.extend_from_slice(&(*actual as u64).to_le_bytes());
        }
        // Unsafe operation VCs.
        VcKind::UnsafeOperation { desc } => {
            buf.push(0x2b);
            encode_str(desc, buf);
        }
        _ => {
            buf.push(0xFF); /* unknown Ty variant */
        }
    }
}

/// Encode a Formula into canonical bytes.
///
/// Each variant gets a unique tag byte followed by its fields. This is a
/// recursive tree encoding — no framing needed because the structure is
/// self-delimiting (each node knows how many children to expect).
fn encode_formula(formula: &Formula, buf: &mut Vec<u8>) {
    match formula {
        // Literals
        Formula::Bool(b) => {
            buf.push(0x10);
            buf.push(u8::from(*b));
        }
        Formula::Int(n) => {
            buf.push(0x11);
            buf.extend_from_slice(&n.to_le_bytes());
        }
        Formula::UInt(n) => {
            buf.push(0x11);
            buf.extend_from_slice(&n.to_le_bytes());
        }
        Formula::BitVec { value, width } => {
            buf.push(0x12);
            buf.extend_from_slice(&value.to_le_bytes());
            buf.extend_from_slice(&width.to_le_bytes());
        }

        // Variables
        Formula::Var(name, sort) => {
            buf.push(0x13);
            encode_str(name.as_str(), buf);
            encode_sort(sort, buf);
        }

        // Boolean connectives
        Formula::Not(inner) => {
            buf.push(0x20);
            encode_formula(inner, buf);
        }
        Formula::And(children) => {
            buf.push(0x21);
            encode_u32(children.len() as u32, buf);
            for child in children {
                encode_formula(child, buf);
            }
        }
        Formula::Or(children) => {
            buf.push(0x22);
            encode_u32(children.len() as u32, buf);
            for child in children {
                encode_formula(child, buf);
            }
        }
        Formula::Implies(lhs, rhs) => {
            buf.push(0x23);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
        }

        // Comparisons
        Formula::Eq(lhs, rhs) => {
            buf.push(0x30);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
        }
        Formula::Lt(lhs, rhs) => {
            buf.push(0x31);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
        }
        Formula::Le(lhs, rhs) => {
            buf.push(0x32);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
        }
        Formula::Gt(lhs, rhs) => {
            buf.push(0x33);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
        }
        Formula::Ge(lhs, rhs) => {
            buf.push(0x34);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
        }

        // Integer arithmetic
        Formula::Add(lhs, rhs) => {
            buf.push(0x40);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
        }
        Formula::Sub(lhs, rhs) => {
            buf.push(0x41);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
        }
        Formula::Mul(lhs, rhs) => {
            buf.push(0x42);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
        }
        Formula::Div(lhs, rhs) => {
            buf.push(0x43);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
        }
        Formula::Rem(lhs, rhs) => {
            buf.push(0x44);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
        }
        Formula::Neg(inner) => {
            buf.push(0x45);
            encode_formula(inner, buf);
        }

        // Bitvector arithmetic
        Formula::BvAdd(lhs, rhs, w) => {
            buf.push(0x50);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
            encode_u32(*w, buf);
        }
        Formula::BvSub(lhs, rhs, w) => {
            buf.push(0x51);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
            encode_u32(*w, buf);
        }
        Formula::BvMul(lhs, rhs, w) => {
            buf.push(0x52);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
            encode_u32(*w, buf);
        }
        Formula::BvUDiv(lhs, rhs, w) => {
            buf.push(0x53);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
            encode_u32(*w, buf);
        }
        Formula::BvSDiv(lhs, rhs, w) => {
            buf.push(0x54);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
            encode_u32(*w, buf);
        }
        Formula::BvURem(lhs, rhs, w) => {
            buf.push(0x55);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
            encode_u32(*w, buf);
        }
        Formula::BvSRem(lhs, rhs, w) => {
            buf.push(0x56);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
            encode_u32(*w, buf);
        }
        Formula::BvAnd(lhs, rhs, w) => {
            buf.push(0x57);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
            encode_u32(*w, buf);
        }
        Formula::BvOr(lhs, rhs, w) => {
            buf.push(0x58);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
            encode_u32(*w, buf);
        }
        Formula::BvXor(lhs, rhs, w) => {
            buf.push(0x59);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
            encode_u32(*w, buf);
        }
        Formula::BvNot(inner, w) => {
            buf.push(0x5A);
            encode_formula(inner, buf);
            encode_u32(*w, buf);
        }
        Formula::BvShl(lhs, rhs, w) => {
            buf.push(0x5B);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
            encode_u32(*w, buf);
        }
        Formula::BvLShr(lhs, rhs, w) => {
            buf.push(0x5C);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
            encode_u32(*w, buf);
        }
        Formula::BvAShr(lhs, rhs, w) => {
            buf.push(0x5D);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
            encode_u32(*w, buf);
        }

        // Bitvector comparisons
        Formula::BvULt(lhs, rhs, w) => {
            buf.push(0x60);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
            encode_u32(*w, buf);
        }
        Formula::BvULe(lhs, rhs, w) => {
            buf.push(0x61);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
            encode_u32(*w, buf);
        }
        Formula::BvSLt(lhs, rhs, w) => {
            buf.push(0x62);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
            encode_u32(*w, buf);
        }
        Formula::BvSLe(lhs, rhs, w) => {
            buf.push(0x63);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
            encode_u32(*w, buf);
        }

        // Bitvector conversions
        Formula::BvToInt(inner, w, signed) => {
            buf.push(0x70);
            encode_formula(inner, buf);
            encode_u32(*w, buf);
            buf.push(u8::from(*signed));
        }
        Formula::IntToBv(inner, w) => {
            buf.push(0x71);
            encode_formula(inner, buf);
            encode_u32(*w, buf);
        }
        Formula::BvExtract { inner, high, low } => {
            buf.push(0x72);
            encode_formula(inner, buf);
            encode_u32(*high, buf);
            encode_u32(*low, buf);
        }
        Formula::BvConcat(lhs, rhs) => {
            buf.push(0x73);
            encode_formula(lhs, buf);
            encode_formula(rhs, buf);
        }
        Formula::BvZeroExt(inner, w) => {
            buf.push(0x74);
            encode_formula(inner, buf);
            encode_u32(*w, buf);
        }
        Formula::BvSignExt(inner, w) => {
            buf.push(0x75);
            encode_formula(inner, buf);
            encode_u32(*w, buf);
        }

        // Conditional
        Formula::Ite(cond, then, else_) => {
            buf.push(0x80);
            encode_formula(cond, buf);
            encode_formula(then, buf);
            encode_formula(else_, buf);
        }

        // Quantifiers
        Formula::Forall(bindings, body) => {
            buf.push(0x90);
            encode_u32(bindings.len() as u32, buf);
            for (name, sort) in bindings {
                encode_str(name.as_str(), buf);
                encode_sort(sort, buf);
            }
            encode_formula(body, buf);
        }
        Formula::Exists(bindings, body) => {
            buf.push(0x91);
            encode_u32(bindings.len() as u32, buf);
            for (name, sort) in bindings {
                encode_str(name.as_str(), buf);
                encode_sort(sort, buf);
            }
            encode_formula(body, buf);
        }

        // Arrays
        Formula::Select(array, index) => {
            buf.push(0xA0);
            encode_formula(array, buf);
            encode_formula(index, buf);
        }
        Formula::Store(array, index, value) => {
            buf.push(0xA1);
            encode_formula(array, buf);
            encode_formula(index, buf);
            encode_formula(value, buf);
        }
        _ => {
            buf.push(0xFF); /* unknown Ty variant */
        }
    }
}

/// Encode a Sort into canonical bytes.
fn encode_sort(sort: &Sort, buf: &mut Vec<u8>) {
    match sort {
        Sort::Bool => buf.push(0x01),
        Sort::Int => buf.push(0x02),
        Sort::BitVec(w) => {
            buf.push(0x03);
            encode_u32(*w, buf);
        }
        Sort::Array(idx, elem) => {
            buf.push(0x04);
            encode_sort(idx, buf);
            encode_sort(elem, buf);
        }
        _ => {
            buf.push(0xFF); /* unknown Ty variant */
        }
    }
}

/// Encode a BinOp into canonical bytes.
fn encode_binop(op: &BinOp, buf: &mut Vec<u8>) {
    let tag: u8 = match op {
        BinOp::Add => 0,
        BinOp::Sub => 1,
        BinOp::Mul => 2,
        BinOp::Div => 3,
        BinOp::Rem => 4,
        BinOp::Eq => 5,
        BinOp::Ne => 6,
        BinOp::Lt => 7,
        BinOp::Le => 8,
        BinOp::Gt => 9,
        BinOp::Ge => 10,
        BinOp::BitAnd => 11,
        BinOp::BitOr => 12,
        BinOp::BitXor => 13,
        BinOp::Shl => 14,
        BinOp::Shr => 15,
        BinOp::Cmp => 16,
        _ => 0xFF, /* unknown BinOp */
    };
    buf.push(tag);
}

/// Encode a Ty into canonical bytes.
fn encode_ty(ty: &Ty, buf: &mut Vec<u8>) {
    match ty {
        Ty::Bool => buf.push(0x01),
        Ty::Int { width, signed: false } => {
            buf.push(0x03);
            encode_u32(*width, buf);
        }
        Ty::Int { width, signed } => {
            buf.push(0x02);
            encode_u32(*width, buf);
            buf.push(u8::from(*signed));
        }
        Ty::Float { width } => {
            buf.push(0x04);
            encode_u32(*width, buf);
        }
        Ty::Ref { mutable, inner } => {
            buf.push(0x05);
            buf.push(u8::from(*mutable));
            encode_ty(inner, buf);
        }
        Ty::Slice { elem } => {
            buf.push(0x06);
            encode_ty(elem, buf);
        }
        Ty::Array { elem, len } => {
            buf.push(0x07);
            encode_ty(elem, buf);
            buf.extend_from_slice(&len.to_le_bytes());
        }
        Ty::Tuple(fields) => {
            buf.push(0x08);
            encode_u32(fields.len() as u32, buf);
            for field in fields {
                encode_ty(field, buf);
            }
        }
        Ty::Adt { name, fields, variants, .. } => {
            buf.push(0x09);
            encode_str(name.as_str(), buf);
            encode_u32(fields.len() as u32, buf);
            for (fname, fty) in fields {
                encode_str(fname, buf);
                encode_ty(fty, buf);
            }
            // Trust: PHASE 4 — append variant structure ADDITIVELY so an ENUM is
            // canonically distinguished from a struct over the same union fields.
            // A STRUCT (`variants` empty) emits a single `0` count → byte-identical
            // to the pre-P4 encoding (no fingerprint churn). An ENUM emits its
            // discriminant-tagged constructor list.
            encode_u32(variants.len() as u32, buf);
            for v in variants {
                encode_str(&v.name, buf);
                // Discriminant: encode the i128 as its two u64 halves (lo, hi) so
                // signed tags round-trip without loss.
                let bits = v.discriminant as u128;
                encode_u32((bits & 0xFFFF_FFFF) as u32, buf);
                encode_u32(((bits >> 32) & 0xFFFF_FFFF) as u32, buf);
                encode_u32(((bits >> 64) & 0xFFFF_FFFF) as u32, buf);
                encode_u32(((bits >> 96) & 0xFFFF_FFFF) as u32, buf);
                encode_u32(v.fields.len() as u32, buf);
                for (fname, fty) in &v.fields {
                    encode_str(fname, buf);
                    encode_ty(fty, buf);
                }
            }
        }
        Ty::Unit => buf.push(0x0A),
        Ty::Never => buf.push(0x0B),
        _ => {
            buf.push(0xFF); /* unknown Ty variant */
        }
    }
}

/// Encode a length-prefixed UTF-8 string.
fn encode_str(s: &str, buf: &mut Vec<u8>) {
    encode_u32(s.len() as u32, buf);
    buf.extend_from_slice(s.as_bytes());
}

/// Encode a u32 in little-endian.
fn encode_u32(n: u32, buf: &mut Vec<u8>) {
    buf.extend_from_slice(&n.to_le_bytes());
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    #[test]
    fn canonical_deterministic_simple() {
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        };
        let bytes1 = canonical_vc_bytes(&vc);
        let bytes2 = canonical_vc_bytes(&vc);
        assert_eq!(bytes1, bytes2, "canonical encoding must be deterministic");
    }

    #[test]
    fn canonical_starts_with_magic() {
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        let bytes = canonical_vc_bytes(&vc);
        assert_eq!(&bytes[..4], b"tVC1", "must start with magic bytes");
    }

    #[test]
    fn canonical_ignores_location() {
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
            formula: Formula::Int(42),
            contract_metadata: None,
            obligation: None,
        };
        let vc2 = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "func_b".into(),
            location: SourceSpan {
                file: "z.rs".to_string(),
                line_start: 999,
                col_start: 5,
                line_end: 999,
                col_end: 50,
            },
            formula: Formula::Int(42),
            contract_metadata: None,
            obligation: None,
        };
        assert_eq!(
            canonical_vc_bytes(&vc1),
            canonical_vc_bytes(&vc2),
            "canonical form must ignore source location and function name"
        );
    }

    #[test]
    fn canonical_different_kinds_differ() {
        let vc1 = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        };
        let vc2 = VerificationCondition {
            kind: VcKind::RemainderByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        };
        assert_ne!(
            canonical_vc_bytes(&vc1),
            canonical_vc_bytes(&vc2),
            "different VC kinds must produce different canonical bytes"
        );
    }

    #[test]
    fn canonical_complex_formula() {
        // Encodes a real-world-like overflow VC formula
        let formula = Formula::Not(Box::new(Formula::And(vec![
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
        ])));
        let vc = VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "midpoint".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        };
        let bytes = canonical_vc_bytes(&vc);
        // Must start with magic
        assert_eq!(&bytes[..4], b"tVC1");
        // Must be non-trivially sized (complex formula)
        assert!(
            bytes.len() > 50,
            "complex formula should produce substantial bytes, got {}",
            bytes.len()
        );
        // Must be deterministic
        assert_eq!(bytes, canonical_vc_bytes(&vc));
    }
}
