//! Type and operation mapping between trust-types and trust_cg LIR.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_cg_lower::instructions::{
    AtomicOrdering as LirAtomicOrdering, AtomicRmwOp, FloatCC, IntCC, Opcode,
};
use trust_cg_lower::types::Type as LirType;
use trust_types::{AtomicOpKind, AtomicOrdering, BinOp, Ty, UnOp};

use crate::BridgeError;

/// Convert a trust-types `Ty` to an trust_cg LIR `Type`.
///
/// Supports scalar types, references/pointers (as I64), tuples, ADTs with
/// known fields, arrays, and slices.
///
/// Trust (2026-09-28): a type LIR cannot DESCRIBE is a type error, not a
/// guess. LIR carries an array's length and every byte extent in `u32`
/// (`trust_cg_lower::types::Type::bytes`, which saturates), and a stack slot
/// is sized from that extent. So a type whose array length does not fit `u32`,
/// or whose natural extent (`Type::checked_bytes`, checked on every
/// intermediate) exceeds it, is refused here — exactly as trust-cg's own
/// `translate_type_*` refuses to build one — rather than mapped to a carrier
/// that is SMALLER than the object: `[u8; 1 << 32]` used to map to
/// `Array(I8, 0)` (a 0-byte slot) and `[u16; 1 << 31]` to a slot one byte
/// short, and a whole-array write (the MIR `Repeat` fill) then wrote past the
/// slot. This is the carrier's own representability, not a size limit: every
/// type that fits the carrier maps exactly as before.
pub fn map_type(ty: &Ty) -> Result<LirType, BridgeError> {
    let lir = map_type_unchecked(ty)?;
    if lir.checked_bytes().is_none() {
        return Err(BridgeError::UnsupportedType(format!(
            "{ty:?}: its byte extent does not fit the u32 LIR type carrier"
        )));
    }
    Ok(lir)
}

/// [`map_type`] without the extent check, which [`map_type`] applies ONCE to
/// the whole result (`checked_bytes` already checks every intermediate), so a
/// nested type is walked once, not once per level.
fn map_type_unchecked(ty: &Ty) -> Result<LirType, BridgeError> {
    match ty {
        Ty::Bool => Ok(LirType::B1),
        Ty::Int { width: 8, .. } => Ok(LirType::I8),
        Ty::Int { width: 16, .. } => Ok(LirType::I16),
        Ty::Int { width: 32, .. } => Ok(LirType::I32),
        Ty::Int { width: 64, .. } => Ok(LirType::I64),
        Ty::Int { width: 128, .. } => Ok(LirType::I128),
        Ty::Float { width: 32 } => Ok(LirType::F32),
        Ty::Float { width: 64 } => Ok(LirType::F64),
        Ty::Unit => Err(BridgeError::UnsupportedType(
            "Unit is zero-sized and has no scalar LIR representation".to_string(),
        )),
        Ty::Bv(w) => match w {
            8 => Ok(LirType::I8),
            16 => Ok(LirType::I16),
            32 => Ok(LirType::I32),
            64 => Ok(LirType::I64),
            128 => Ok(LirType::I128),
            _ => Err(BridgeError::UnsupportedType(format!("Bv({w})"))),
        },
        // A pointer to a slice is a FAT pointer, two words `{ data, len }`, the
        // same carrier as the slice value below. Trust (ticket 216 cg-bridge,
        // review 5): it was an `I64` here, so a tuple or ADT holding one laid it
        // out in ONE word and its length had no lane.
        Ty::Ref { inner, .. } | Ty::RawPtr { pointee: inner, .. }
            if matches!(inner.as_ref(), Ty::Slice { .. }) =>
        {
            map_type_unchecked(inner)
        }
        // Every other reference and raw pointer is thin: I64 (pointer-sized).
        // The pointee may be zero-sized or otherwise not value-lowerable.
        Ty::Ref { .. } | Ty::RawPtr { .. } => Ok(LirType::I64),
        // Tuples map to LIR Struct with each field mapped.
        Ty::Tuple(fields) => {
            let lir_fields: Vec<LirType> =
                fields.iter().map(map_type_unchecked).collect::<Result<_, _>>()?;
            Ok(LirType::Struct(lir_fields))
        }
        Ty::Adt { name, fields, .. } if fields.is_empty() => Err(BridgeError::UnsupportedType(
            format!("fieldless ADT `{name}` has no trustworthy LIR layout"),
        )),
        // ADTs with fields map to LIR Struct. The discriminant (if any) is not
        // modeled here; downstream passes handle variant layout.
        Ty::Adt { fields, .. } => {
            let lir_fields: Vec<LirType> =
                fields.iter().map(|(_, ty)| map_type_unchecked(ty)).collect::<Result<_, _>>()?;
            Ok(LirType::Struct(lir_fields))
        }
        // Arrays map to LIR Array, whose length carrier is `u32`: a longer
        // array is a type LIR cannot describe (never a truncated length).
        Ty::Array { elem, len } => {
            let lir_elem = map_type_unchecked(elem)?;
            let lir_len = u32::try_from(*len).map_err(|_| {
                BridgeError::UnsupportedType(format!(
                    "array length {len} does not fit the u32 LIR length carrier"
                ))
            })?;
            Ok(LirType::Array(Box::new(lir_elem), lir_len))
        }
        // Slices are fat pointers: { ptr: I64, len: I64 }. The element is
        // mapped (and must be describable) but is not part of the carrier.
        Ty::Slice { elem } => {
            let _ = map_type(elem)?;
            Ok(LirType::Struct(vec![LirType::I64, LirType::I64]))
        }
        Ty::Never => Err(BridgeError::UnsupportedType(
            "Never has no value-level LIR representation".to_string(),
        )),
        #[allow(unreachable_patterns)]
        other => Err(BridgeError::UnsupportedType(format!("{other:?}"))),
    }
}

// ---------------------------------------------------------------------------
// BinOp mapping: trust-types BinOp -> Opcode
// ---------------------------------------------------------------------------

/// Convert a trust-types `BinOp` to an trust_cg LIR `Opcode`.
///
/// The `signed` parameter controls whether division/remainder use signed
/// or unsigned variants. For comparisons, it controls signed vs unsigned
/// condition codes.
pub fn map_binop(op: BinOp, signed: bool) -> Result<Opcode, BridgeError> {
    match op {
        BinOp::Add => Ok(Opcode::Iadd),
        BinOp::Sub => Ok(Opcode::Isub),
        BinOp::Mul => Ok(Opcode::Imul),
        BinOp::Div if signed => Ok(Opcode::Sdiv),
        BinOp::Div => Ok(Opcode::Udiv),
        BinOp::Rem if signed => Ok(Opcode::Srem),
        BinOp::Rem => Ok(Opcode::Urem),
        BinOp::Eq => Ok(Opcode::Icmp { cond: IntCC::Equal }),
        BinOp::Ne => Ok(Opcode::Icmp { cond: IntCC::NotEqual }),
        BinOp::Lt if signed => Ok(Opcode::Icmp { cond: IntCC::SignedLessThan }),
        BinOp::Lt => Ok(Opcode::Icmp { cond: IntCC::UnsignedLessThan }),
        BinOp::Le if signed => Ok(Opcode::Icmp { cond: IntCC::SignedLessThanOrEqual }),
        BinOp::Le => Ok(Opcode::Icmp { cond: IntCC::UnsignedLessThanOrEqual }),
        BinOp::Gt if signed => Ok(Opcode::Icmp { cond: IntCC::SignedGreaterThan }),
        BinOp::Gt => Ok(Opcode::Icmp { cond: IntCC::UnsignedGreaterThan }),
        BinOp::Ge if signed => Ok(Opcode::Icmp { cond: IntCC::SignedGreaterThanOrEqual }),
        BinOp::Ge => Ok(Opcode::Icmp { cond: IntCC::UnsignedGreaterThanOrEqual }),
        BinOp::BitAnd => Ok(Opcode::Band),
        BinOp::BitOr => Ok(Opcode::Bor),
        BinOp::BitXor => Ok(Opcode::Bxor),
        BinOp::Shl => Ok(Opcode::Ishl),
        BinOp::Shr if signed => Ok(Opcode::Sshr),
        BinOp::Shr => Ok(Opcode::Ushr),
        BinOp::Cmp => {
            Err(BridgeError::UnsupportedOp("three-way Cmp not yet supported in LIR".to_string()))
        }
        _ => Err(BridgeError::UnsupportedOp(format!("{op:?}"))),
    }
}

/// Convert a trust-types floating-point `BinOp` to an trust_cg LIR `Opcode`.
pub fn map_float_binop(op: BinOp) -> Result<Opcode, BridgeError> {
    match op {
        BinOp::Add => Ok(Opcode::Fadd),
        BinOp::Sub => Ok(Opcode::Fsub),
        BinOp::Mul => Ok(Opcode::Fmul),
        BinOp::Div => Ok(Opcode::Fdiv),
        BinOp::Eq => Ok(Opcode::Fcmp { cond: FloatCC::Equal }),
        BinOp::Ne => Ok(Opcode::Fcmp { cond: FloatCC::NotEqual }),
        BinOp::Lt => Ok(Opcode::Fcmp { cond: FloatCC::LessThan }),
        BinOp::Le => Ok(Opcode::Fcmp { cond: FloatCC::LessThanOrEqual }),
        BinOp::Gt => Ok(Opcode::Fcmp { cond: FloatCC::GreaterThan }),
        BinOp::Ge => Ok(Opcode::Fcmp { cond: FloatCC::GreaterThanOrEqual }),
        _ => Err(BridgeError::UnsupportedOp(format!("{op:?}"))),
    }
}

pub(crate) fn map_atomic_ordering(
    ordering: &AtomicOrdering,
) -> Result<LirAtomicOrdering, BridgeError> {
    match ordering {
        AtomicOrdering::Relaxed => Ok(LirAtomicOrdering::Relaxed),
        AtomicOrdering::Acquire => Ok(LirAtomicOrdering::Acquire),
        AtomicOrdering::Release => Ok(LirAtomicOrdering::Release),
        AtomicOrdering::AcqRel => Ok(LirAtomicOrdering::AcqRel),
        AtomicOrdering::SeqCst => Ok(LirAtomicOrdering::SeqCst),
        _ => Err(BridgeError::UnsupportedOp(format!("unknown atomic ordering: {ordering:?}"))),
    }
}

/// Derive a sound failure ordering for a compare-exchange from its success
/// ordering. The failure ordering models the load executed when the exchange
/// fails: it may never be `Release`/`AcqRel` and must not be stronger than the
/// success ordering. We apply the standard weakening (`Release -> Relaxed`,
/// `AcqRel -> Acquire`, everything else maps to itself), which is always a
/// valid, no-stronger-than-success failure ordering.
pub(crate) fn cmpxchg_failure_ordering(success: LirAtomicOrdering) -> LirAtomicOrdering {
    match success {
        LirAtomicOrdering::Release => LirAtomicOrdering::Relaxed,
        LirAtomicOrdering::AcqRel => LirAtomicOrdering::Acquire,
        other => other,
    }
}

pub(crate) fn map_atomic_rmw_op(kind: AtomicOpKind) -> Result<AtomicRmwOp, BridgeError> {
    match kind {
        AtomicOpKind::Exchange => Ok(AtomicRmwOp::Xchg),
        AtomicOpKind::FetchAdd => Ok(AtomicRmwOp::Add),
        AtomicOpKind::FetchSub => Ok(AtomicRmwOp::Sub),
        AtomicOpKind::FetchAnd => Ok(AtomicRmwOp::And),
        AtomicOpKind::FetchOr => Ok(AtomicRmwOp::Or),
        AtomicOpKind::FetchXor => Ok(AtomicRmwOp::Xor),
        AtomicOpKind::FetchNand | AtomicOpKind::FetchMin | AtomicOpKind::FetchMax => Err(
            BridgeError::UnsupportedOp(format!("atomic op kind has no LIR equivalent: {kind:?}")),
        ),
        _ => Err(BridgeError::UnsupportedOp(format!("unsupported atomic RMW op kind: {kind:?}"))),
    }
}

/// Convert a trust-types `UnOp` to an trust_cg LIR `Opcode`.
///
/// Type-blind: `UnOp::Not` maps to the full-width bitwise `Bnot`, which is wrong for a `bool`
/// (a one-bit complement). A caller that can see a `Ty::Bool` operand must lower it as
/// `Bxor(x, Iconst B1 1)` instead, as `lower.rs` does for `Rvalue::UnaryOp`.
pub fn map_unop(op: UnOp) -> Result<Opcode, BridgeError> {
    match op {
        UnOp::Not => Ok(Opcode::Bnot),
        UnOp::Neg => Ok(Opcode::Ineg),
        UnOp::PtrMetadata => {
            Err(BridgeError::UnsupportedOp("PtrMetadata not yet supported in LIR".to_string()))
        }
        _ => Err(BridgeError::UnsupportedOp(format!("{op:?}"))),
    }
}

// ---------------------------------------------------------------------------
// Type projection helpers
// ---------------------------------------------------------------------------

/// Get the type of a struct/tuple/ADT field by index.
pub(crate) fn field_type(ty: &Ty, field_idx: usize) -> Result<Ty, BridgeError> {
    match ty {
        Ty::Tuple(fields) => fields.get(field_idx).cloned().ok_or_else(|| {
            BridgeError::UnsupportedOp(format!(
                "tuple field index {field_idx} out of range (len {})",
                fields.len()
            ))
        }),
        Ty::Adt { fields, .. } => {
            fields.get(field_idx).map(|(_, ty)| ty.clone()).ok_or_else(|| {
                BridgeError::UnsupportedOp(format!(
                    "ADT field index {field_idx} out of range (len {})",
                    fields.len()
                ))
            })
        }
        other => Err(BridgeError::UnsupportedOp(format!(
            "field projection on non-aggregate type: {other:?}"
        ))),
    }
}

/// Get the pointee type for a dereference projection.
pub(crate) fn deref_type(ty: &Ty) -> Result<Ty, BridgeError> {
    match ty {
        Ty::Ref { inner, .. } => Ok(*inner.clone()),
        Ty::RawPtr { pointee, .. } => Ok(*pointee.clone()),
        other => Err(BridgeError::UnsupportedOp(format!("deref on non-pointer type: {other:?}"))),
    }
}

/// Get the element type for an array or slice.
pub(crate) fn element_type(ty: &Ty) -> Result<Ty, BridgeError> {
    match ty {
        Ty::Array { elem, .. } => Ok(*elem.clone()),
        Ty::Slice { elem } => Ok(*elem.clone()),
        other => Err(BridgeError::UnsupportedOp(format!(
            "index/element on non-sequence type: {other:?}"
        ))),
    }
}

/// Get the type after a downcast projection on an ADT.
///
/// For now, downcasts return the same ADT type — proper variant-aware
/// layout is deferred to a future pass.
pub(crate) fn downcast_type(ty: &Ty, _variant_idx: usize) -> Result<Ty, BridgeError> {
    match ty {
        Ty::Adt { .. } => Ok(ty.clone()),
        other => Err(BridgeError::UnsupportedOp(format!("downcast on non-ADT type: {other:?}"))),
    }
}

// Trust: #828 — drop elaboration is only required for non-trivially-Copy MIR types.
// Immutable references (&T) are Copy; mutable references (&mut T) are not.
pub(crate) fn is_trivially_copy_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Bool
            | Ty::Int { .. }
            | Ty::Float { .. }
            | Ty::Unit
            | Ty::Never
            | Ty::Bv(_)
            | Ty::RawPtr { .. }
            | Ty::Ref { mutable: false, .. }
    )
}

/// Why a `Switch` case constant cannot be encoded for its selector.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SwitchCaseEncodingError {
    /// The selector is 128 bits wide. LIR `Switch` cases are `i64` and the
    /// trust-cg switch lowering compares only the selector's low 64 bits, so a
    /// case table over a 128-bit selector would dispatch on a truncated value.
    WideSelector,
    /// The selector's LIR type is not an integer carrier the switch lowering
    /// compares (a float, an aggregate, ...).
    NonIntegerSelector(LirType),
    /// A boolean selector was given a case value other than 0 or 1.
    BoolCaseOutOfRange(i128),
    /// Two distinct source case constants denote the SAME selector value once
    /// reduced to the selector's width (e.g. `-1` and `255` on an 8-bit
    /// selector). Which arm the source meant is not recoverable here.
    Duplicate { first: i128, second: i128, encoded: i64 },
}

impl std::fmt::Display for SwitchCaseEncodingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WideSelector => f.write_str(
                "switch on a 128-bit selector: LIR `Switch` cases are i64 and the switch \
                 lowering compares only the low 64 bits, so the dispatch would ignore the \
                 high half (lower it as an explicit compare chain instead)",
            ),
            Self::NonIntegerSelector(ty) => {
                write!(f, "switch selector of LIR type {ty:?} is not an integer carrier")
            }
            Self::BoolCaseOutOfRange(value) => {
                write!(f, "boolean switch selector has case value {value} (only 0 and 1 exist)")
            }
            Self::Duplicate { first, second, encoded } => write!(
                f,
                "switch case values {first} and {second} denote the same selector value \
                 ({encoded}) at the selector's width"
            ),
        }
    }
}

/// Encode one integer `Switch` case constant for a selector of LIR type
/// `selector`, in EXACTLY the form trust-cg's switch lowering compares against.
///
/// `raw` is the case's value as a mathematical integer; any representative of
/// its residue class at the selector's width is accepted — a MIR `SwitchInt`
/// carries the zero-extended bit pattern (`i8 -3` arrives as `253`), while a
/// trust-ir `Switch` carries the signed value (`-3`). Both denote one selector
/// value, and the trust-ir interpreter reads the constant the same way (it
/// wraps it to the selector's type before comparing).
///
/// The encoding is dictated by the consumer, trust-cg-lower's ISel, whose own
/// trust-ir adapter applies the same rule (`normalize_switch_case_value`):
///
/// * **8/16-bit selectors are ZERO-extended** before every compare and before
///   jump-table indexing (`clean_switch_selector` emits `UXTB`/`UXTH`; x86-64
///   selects `MOVZX`). The case constant must therefore be the zero-extended
///   pattern in `[0, 2^bits)`. A sign-extended `-3` materializes as
///   `0xFFFF_FFFD` and can never equal the zero-extended selector `0xFD`, so the
///   arm is unreachable and control falls to the default: a silent miscompile.
/// * **32/64-bit selectors are compared at native width**, and the jump table's
///   index arithmetic SIGN-extends a 32-bit selector, so the case constant must
///   be the two's-complement value in `[-2^(bits-1), 2^(bits-1))`. A raw
///   `0xFFFF_FFFF` (a `u32::MAX`, or MIR's spelling of `i32 -1`) makes
///   `selector - min_case` set bit 32 and routes the case to the default.
/// * **Booleans** carry only 0 and 1.
/// * **128-bit selectors are refused**: see [`SwitchCaseEncodingError::WideSelector`].
pub(crate) fn encode_switch_case(
    raw: i128,
    selector: &LirType,
) -> Result<i64, SwitchCaseEncodingError> {
    let bits: u32 = match selector {
        LirType::B1 => {
            return match raw {
                0 | 1 => Ok(raw as i64),
                other => Err(SwitchCaseEncodingError::BoolCaseOutOfRange(other)),
            };
        }
        LirType::I8 => 8,
        LirType::I16 => 16,
        LirType::I32 => 32,
        LirType::I64 => 64,
        LirType::I128 => return Err(SwitchCaseEncodingError::WideSelector),
        other => return Err(SwitchCaseEncodingError::NonIntegerSelector(other.clone())),
    };
    let modulus = 1_i128 << bits;
    let residue = raw.rem_euclid(modulus);
    let encoded =
        if bits <= 16 || residue < (1_i128 << (bits - 1)) { residue } else { residue - modulus };
    // In range by construction: [0, 2^16) or [-2^63, 2^63).
    Ok(encoded as i64)
}

/// [`encode_switch_case`] over a whole case list, refusing two case constants
/// that collide at the selector's width. Order is preserved.
pub(crate) fn encode_switch_cases(
    raws: impl IntoIterator<Item = i128>,
    selector: &LirType,
) -> Result<Vec<i64>, SwitchCaseEncodingError> {
    let mut encoded: Vec<(i128, i64)> = Vec::new();
    for raw in raws {
        let value = encode_switch_case(raw, selector)?;
        if let Some(&(first, _)) = encoded.iter().find(|(_, seen)| *seen == value) {
            return Err(SwitchCaseEncodingError::Duplicate { first, second: raw, encoded: value });
        }
        encoded.push((raw, value));
    }
    Ok(encoded.into_iter().map(|(_, value)| value).collect())
}

#[cfg(test)]
mod switch_case_encoding_tests {
    use trust_cg_lower::types::Type as LirType;

    use super::{SwitchCaseEncodingError, encode_switch_case, encode_switch_cases};

    #[test]
    fn narrow_selectors_take_the_zero_extended_pattern() {
        // Signed trust-ir spelling and zero-extended MIR spelling agree.
        assert_eq!(encode_switch_case(-3, &LirType::I8), Ok(253));
        assert_eq!(encode_switch_case(253, &LirType::I8), Ok(253));
        assert_eq!(encode_switch_case(-128, &LirType::I8), Ok(128));
        assert_eq!(encode_switch_case(-1, &LirType::I8), Ok(255));
        assert_eq!(encode_switch_case(7, &LirType::I8), Ok(7));
        assert_eq!(encode_switch_case(-300, &LirType::I16), Ok(65236));
        assert_eq!(encode_switch_case(-1, &LirType::I16), Ok(65535));
        assert_eq!(encode_switch_case(0xFFFF, &LirType::I16), Ok(65535));
    }

    #[test]
    fn wide_selectors_take_the_twos_complement_value() {
        assert_eq!(encode_switch_case(0xFFFF_FFFF, &LirType::I32), Ok(-1));
        assert_eq!(encode_switch_case(-1, &LirType::I32), Ok(-1));
        assert_eq!(encode_switch_case(0x8000_0000, &LirType::I32), Ok(i64::from(i32::MIN)));
        assert_eq!(encode_switch_case(0x7FFF_FFFF, &LirType::I32), Ok(i64::from(i32::MAX)));
        assert_eq!(encode_switch_case(-100_000, &LirType::I32), Ok(-100_000));
        assert_eq!(encode_switch_case(i128::from(u64::MAX), &LirType::I64), Ok(-1));
        assert_eq!(encode_switch_case(i128::from(i64::MIN), &LirType::I64), Ok(i64::MIN));
        assert_eq!(encode_switch_case(-3, &LirType::I64), Ok(-3));
    }

    #[test]
    fn booleans_carry_only_zero_and_one() {
        assert_eq!(encode_switch_case(0, &LirType::B1), Ok(0));
        assert_eq!(encode_switch_case(1, &LirType::B1), Ok(1));
        assert_eq!(
            encode_switch_case(2, &LirType::B1),
            Err(SwitchCaseEncodingError::BoolCaseOutOfRange(2))
        );
    }

    #[test]
    fn unencodable_selectors_are_refused() {
        assert_eq!(
            encode_switch_case(1, &LirType::I128),
            Err(SwitchCaseEncodingError::WideSelector)
        );
        assert_eq!(
            encode_switch_case(1, &LirType::F64),
            Err(SwitchCaseEncodingError::NonIntegerSelector(LirType::F64))
        );
    }

    #[test]
    fn colliding_case_constants_are_refused_and_order_is_kept() {
        assert_eq!(encode_switch_cases([-3, 7, 0], &LirType::I8), Ok(vec![253, 7, 0]));
        assert_eq!(
            encode_switch_cases([-1, 255], &LirType::I8),
            Err(SwitchCaseEncodingError::Duplicate { first: -1, second: 255, encoded: 255 })
        );
        assert_eq!(
            encode_switch_cases([0xFFFF_FFFF, -1], &LirType::I32),
            Err(SwitchCaseEncodingError::Duplicate { first: 0xFFFF_FFFF, second: -1, encoded: -1 })
        );
    }
}
