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
pub fn map_type(ty: &Ty) -> Result<LirType, BridgeError> {
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
        // References and raw pointers are represented as I64 (pointer-sized).
        // The pointee may be zero-sized or otherwise not value-lowerable.
        Ty::Ref { .. } | Ty::RawPtr { .. } => Ok(LirType::I64),
        // Tuples map to LIR Struct with each field mapped.
        Ty::Tuple(fields) => {
            let lir_fields: Vec<LirType> = fields.iter().map(map_type).collect::<Result<_, _>>()?;
            Ok(LirType::Struct(lir_fields))
        }
        Ty::Adt { name, fields, .. } if fields.is_empty() => Err(BridgeError::UnsupportedType(
            format!("fieldless ADT `{name}` has no trustworthy LIR layout"),
        )),
        // ADTs with fields map to LIR Struct. The discriminant (if any) is not
        // modeled here; downstream passes handle variant layout.
        Ty::Adt { fields, .. } => {
            let lir_fields: Vec<LirType> =
                fields.iter().map(|(_, ty)| map_type(ty)).collect::<Result<_, _>>()?;
            Ok(LirType::Struct(lir_fields))
        }
        // Arrays map to LIR Array.
        Ty::Array { elem, len } => {
            let lir_elem = map_type(elem)?;
            Ok(LirType::Array(Box::new(lir_elem), *len as u32))
        }
        // Slices are fat pointers: { ptr: I64, len: I64 }.
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
