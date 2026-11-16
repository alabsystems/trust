// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Lossless compiler-observed constant storage, not an executable value model.
//!
//! Consumers must explicitly refuse these records until they implement checked
//! allocation/provenance semantics. In particular equal bytes do not establish
//! pointer equality, and a static initializer is not its current runtime value.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::{
    AssertMessage, CallableDefPathHash, CalleeIdentity, ConstValue, Operand, Rvalue, Statement,
    Terminator, Ty, VerifiableBody,
};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstantMemoryImage {
    pub schema_version: u32,
    pub owner: ConstantImageOwner,
    pub target: ConstantImageTarget,
    /// The faithfully extracted type is diagnostic data, not admission evidence.
    pub ty: Ty,
    /// Compiler stable hash of the concrete, region-erased original Rust type.
    pub ty_fingerprint: [u64; 2],
    pub layout: ConstantImageLayout,
    pub root: ConstantImageRoot,
    /// IDs are assigned to actual compiler allocation identities within ONE
    /// extraction of `owner`. They are not global IDs or hashes of byte contents.
    /// Each image retains its complete reachable node closure. Repeated nodes
    /// across operands retain the same ID; equal-byte distinct allocations do not.
    pub nodes: BTreeMap<u32, ConstantImageNode>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstantImageOwner {
    pub def_path: String,
    pub def_path_hash: CallableDefPathHash,
    pub mir_phase: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstantImageTarget {
    pub triple: String,
    pub data_layout: String,
    pub pointer_size_bytes: u64,
    pub little_endian: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstantImageLayout {
    pub size_bytes: u64,
    pub align_bytes: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConstantImageRoot {
    ScalarBits { bits: u128, size_bytes: u64 },
    Pointer(ConstantImagePointer),
    Indirect { allocation_id: u32, offset_bytes: u64 },
    Slice { allocation_id: u32, metadata: u64 },
    ZeroSized,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstantImagePointer {
    pub allocation_id: u32,
    pub offset_bytes: u64,
    /// Preserve both distinct compiler CTFE provenance flags, not a derived
    /// claim that the referenced runtime storage is immutable.
    pub immutable: bool,
    pub shared_ref: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstantImageRelocation {
    pub offset_bytes: u64,
    pub pointer: ConstantImagePointer,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstantImageMemory {
    pub layout: ConstantImageLayout,
    pub mutable: bool,
    /// `None` is uninitialized. Never replace it with an initialized zero.
    /// Pointer bytes retain their target-relative offset bits, not an address.
    pub bytes: Vec<Option<u8>>,
    pub relocations: Vec<ConstantImageRelocation>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstantImageDefinition {
    pub def_path: String,
    pub def_path_hash: CallableDefPathHash,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConstantImageNode {
    Memory(ConstantImageMemory),
    Static {
        definition: ConstantImageDefinition,
        declared_mutable: bool,
        freeze: bool,
        thread_local: bool,
        foreign: bool,
        /// An initializer image is deliberately nested under the static's
        /// identity, not presented as the current contents of mutable storage.
        initializer: ConstantImageMemory,
    },
    Function {
        definition: ConstantImageDefinition,
        /// Distinguish the full compiler InstanceKind AND its substitutions;
        /// a definition alone cannot distinguish call-once/drop/function shims.
        instance_fingerprint: [u64; 2],
        instance_debug: String,
        callee_identity: CalleeIdentity,
    },
}

impl ConstValue {
    /// Reject images even when malformed external data nests one inside the
    /// older scalar-fields carrier. Iterative traversal avoids recursive stack
    /// growth; no value or authority is inferred from either carrier's fields.
    #[must_use]
    pub fn contains_memory_image(&self) -> bool {
        let mut pending = Vec::new();
        let mut value = self;
        loop {
            match value {
                Self::MemoryImage(_) => return true,
                Self::StructScalarFieldsRef { fields, .. } => pending.extend(fields),
                Self::Bool(_)
                | Self::Int(_)
                | Self::Uint(..)
                | Self::Float(_)
                | Self::FloatBits { .. }
                | Self::Unit
                | Self::Str { .. }
                | Self::OpaqueConst(_)
                | Self::OpaqueScalar { .. }
                | Self::ConstParam { .. }
                | Self::UnitVariantRef { .. }
                | Self::EmptyClosureRef { .. }
                | Self::CallableItem { .. } => {}
            }
            let Some(next) = pending.pop() else { return false };
            value = next;
        }
    }

    /// Whether any `ConstValue::OpaqueScalar` occurs in `self` (including inside
    /// `StructScalarFieldsRef`). Iterative traversal avoids recursive stack growth.
    #[must_use]
    pub fn contains_opaque_scalar(&self) -> bool {
        let mut pending = Vec::new();
        let mut value = self;
        loop {
            match value {
                Self::OpaqueScalar { .. } => return true,
                Self::StructScalarFieldsRef { fields, .. } => pending.extend(fields),
                Self::Bool(_)
                | Self::Int(_)
                | Self::Uint(..)
                | Self::Float(_)
                | Self::FloatBits { .. }
                | Self::Unit
                | Self::Str { .. }
                | Self::OpaqueConst(_)
                | Self::ConstParam { .. }
                | Self::UnitVariantRef { .. }
                | Self::EmptyClosureRef { .. }
                | Self::CallableItem { .. }
                | Self::MemoryImage(_) => {}
            }
            let Some(next) = pending.pop() else { return false };
            value = next;
        }
    }
}

impl Operand {
    #[must_use]
    pub fn contains_memory_image(&self) -> bool {
        match self {
            Self::Constant(value) => value.contains_memory_image(),
            Self::Copy(_) | Self::Move(_) | Self::Symbolic(_) | Self::Unsupported { .. } => false,
        }
    }

    #[must_use]
    pub fn contains_opaque_scalar(&self) -> bool {
        match self {
            Self::Constant(value) => value.contains_opaque_scalar(),
            Self::Copy(_) | Self::Move(_) | Self::Symbolic(_) | Self::Unsupported { .. } => false,
        }
    }
}

impl Rvalue {
    #[must_use]
    pub fn contains_memory_image(&self) -> bool {
        match self {
            Self::Use(op) | Self::UnaryOp(_, op) | Self::Cast(op, _) | Self::Repeat(op, _) => {
                op.contains_memory_image()
            }
            Self::BinaryOp(_, lhs, rhs)
            | Self::CheckedBinaryOp(_, lhs, rhs)
            | Self::UncheckedBinaryOp(_, lhs, rhs)
            | Self::PtrOffset { ptr: lhs, count: rhs } => {
                lhs.contains_memory_image() || rhs.contains_memory_image()
            }
            Self::Aggregate(_, operands) | Self::Unsupported { operands, .. } => {
                operands.iter().any(Operand::contains_memory_image)
            }
            Self::Ref { .. }
            | Self::Discriminant(_)
            | Self::Len(_)
            | Self::AddressOf(..)
            | Self::CopyForDeref(_) => false,
        }
    }

    #[must_use]
    pub fn contains_opaque_scalar(&self) -> bool {
        match self {
            Self::Use(op) | Self::UnaryOp(_, op) | Self::Cast(op, _) | Self::Repeat(op, _) => {
                op.contains_opaque_scalar()
            }
            Self::BinaryOp(_, lhs, rhs)
            | Self::CheckedBinaryOp(_, lhs, rhs)
            | Self::UncheckedBinaryOp(_, lhs, rhs)
            | Self::PtrOffset { ptr: lhs, count: rhs } => {
                lhs.contains_opaque_scalar() || rhs.contains_opaque_scalar()
            }
            Self::Aggregate(_, operands) | Self::Unsupported { operands, .. } => {
                operands.iter().any(Operand::contains_opaque_scalar)
            }
            Self::Ref { .. }
            | Self::Discriminant(_)
            | Self::Len(_)
            | Self::AddressOf(..)
            | Self::CopyForDeref(_) => false,
        }
    }
}

impl Statement {
    #[must_use]
    pub fn contains_memory_image(&self) -> bool {
        match self {
            Self::Assign { rvalue, .. } => rvalue.contains_memory_image(),
            Self::Intrinsic { args: operands, .. } | Self::Unsupported { operands, .. } => {
                operands.iter().any(Operand::contains_memory_image)
            }
            Self::CopyNonOverlapping { src, dst, count, .. } => {
                src.contains_memory_image()
                    || dst.contains_memory_image()
                    || count.contains_memory_image()
            }
            Self::StorageLive(_)
            | Self::StorageDead(_)
            | Self::SetDiscriminant { .. }
            | Self::Deinit { .. }
            | Self::Retag { .. }
            | Self::PlaceMention(_)
            | Self::Coverage
            | Self::ConstEvalCounter
            | Self::Nop => false,
        }
    }

    #[must_use]
    pub fn contains_opaque_scalar(&self) -> bool {
        match self {
            Self::Assign { rvalue, .. } => rvalue.contains_opaque_scalar(),
            Self::Intrinsic { args: operands, .. } | Self::Unsupported { operands, .. } => {
                operands.iter().any(Operand::contains_opaque_scalar)
            }
            Self::CopyNonOverlapping { src, dst, count, .. } => {
                src.contains_opaque_scalar()
                    || dst.contains_opaque_scalar()
                    || count.contains_opaque_scalar()
            }
            Self::StorageLive(_)
            | Self::StorageDead(_)
            | Self::SetDiscriminant { .. }
            | Self::Deinit { .. }
            | Self::Retag { .. }
            | Self::PlaceMention(_)
            | Self::Coverage
            | Self::ConstEvalCounter
            | Self::Nop => false,
        }
    }
}

impl Terminator {
    #[must_use]
    pub fn contains_memory_image(&self) -> bool {
        match self {
            Self::SwitchInt { discr, .. } => discr.contains_memory_image(),
            Self::Assert { cond, msg, .. } => {
                cond.contains_memory_image() || msg.contains_memory_image()
            }
            Self::Call { args, .. } | Self::TailCall { args, .. } => {
                args.iter().any(Operand::contains_memory_image)
            }
            Self::Goto(_)
            | Self::Return
            | Self::Drop { .. }
            | Self::Opaque { .. }
            | Self::Unreachable
            | Self::Resume => false,
        }
    }

    #[must_use]
    pub fn contains_opaque_scalar(&self) -> bool {
        match self {
            Self::SwitchInt { discr, .. } => discr.contains_opaque_scalar(),
            Self::Assert { cond, msg, .. } => {
                cond.contains_opaque_scalar() || msg.contains_opaque_scalar()
            }
            Self::Call { args, .. } | Self::TailCall { args, .. } => {
                args.iter().any(Operand::contains_opaque_scalar)
            }
            Self::Goto(_)
            | Self::Return
            | Self::Drop { .. }
            | Self::Opaque { .. }
            | Self::Unreachable
            | Self::Resume => false,
        }
    }
}

impl AssertMessage {
    #[must_use]
    pub fn contains_memory_image(&self) -> bool {
        // There are no operand-valued message fields today. Keep the match
        // exhaustive so a future payload cannot bypass body preflight silently.
        match self {
            Self::BoundsCheck
            | Self::Overflow(_)
            | Self::OverflowNeg
            | Self::DivisionByZero
            | Self::RemainderByZero
            | Self::ResumedAfterReturn
            | Self::ResumedAfterPanic
            | Self::ResumedAfterDrop
            | Self::MisalignedPointerDereference
            | Self::NullPointerDereference
            | Self::InvalidEnumConstruction
            | Self::Custom(_) => false,
        }
    }

    #[must_use]
    pub fn contains_opaque_scalar(&self) -> bool {
        match self {
            Self::BoundsCheck
            | Self::Overflow(_)
            | Self::OverflowNeg
            | Self::DivisionByZero
            | Self::RemainderByZero
            | Self::ResumedAfterReturn
            | Self::ResumedAfterPanic
            | Self::ResumedAfterDrop
            | Self::MisalignedPointerDereference
            | Self::NullPointerDereference
            | Self::InvalidEnumConstruction
            | Self::Custom(_) => false,
        }
    }
}

impl VerifiableBody {
    /// Scan ALL blocks, including dead blocks and assignments hidden by a
    /// relation/summary. Consumers must refuse before simplification can erase
    /// unsupported inputs. Owning-crate matches above are deliberately exhaustive.
    #[must_use]
    pub fn contains_memory_image(&self) -> bool {
        self.blocks.iter().any(|block| {
            block.stmts.iter().any(Statement::contains_memory_image)
                || block.terminator.contains_memory_image()
        })
    }

    /// Scan ALL blocks, including dead blocks, for any `ConstValue::OpaqueScalar`.
    #[must_use]
    pub fn contains_opaque_scalar(&self) -> bool {
        self.blocks.iter().any(|block| {
            block.stmts.iter().any(Statement::contains_opaque_scalar)
                || block.terminator.contains_opaque_scalar()
        })
    }
}

#[cfg(test)]
mod tests;
