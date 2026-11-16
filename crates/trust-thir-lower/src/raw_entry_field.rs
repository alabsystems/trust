// Copyright 2026 Andrew Yates. SPDX-License-Identifier: MIT OR Apache-2.0
//! Selected integer-field reads from an unchanged, possibly retyped raw entry
//! address. This records address identity, never memory validity or borrow rights.

use super::*;

pub(super) enum RawFieldLayoutError {
    Unavailable,
    Disagrees,
    Overflow,
    Path,
}

impl RawFieldLayoutError {
    pub(super) fn assign_tag(self) -> &'static str {
        match self {
            Self::Unavailable => "Assign(raw entry field layout unavailable)",
            Self::Disagrees => "Assign(raw entry field layout disagrees)",
            Self::Overflow => "Assign(raw entry field offset overflow)",
            Self::Path => "Assign(raw entry field path disagrees)",
        }
    }

    fn read_tag(self) -> &'static str {
        match self {
            Self::Unavailable => "Field(raw entry layout unavailable)",
            Self::Disagrees => "Field(raw entry layout disagrees)",
            Self::Overflow => "Field(raw entry offset overflow)",
            Self::Path => "Field(raw entry path disagrees)",
        }
    }
}

impl<'a, 'tcx> LowerCx<'a, 'tcx> {
    /// Select an integer sibling through an existing reference without loading
    /// a possibly-uninitialized aggregate. Storage-free parents keep their
    /// established lowering. A recognized blocked parent owns every refusal.
    pub(super) fn lower_storage_ref_field_read(
        &mut self,
        leaf: ExprId,
        mut ptr_expr: ExprId,
        deref: ExprId,
        chain: &[(ExprId, u32)],
    ) -> Option<Result<ValueId, &'static str>> {
        loop {
            match &self.thir.exprs[ptr_expr].kind {
                ExprKind::Scope { value, .. } => ptr_expr = *value,
                ExprKind::ValueExpr { source } => ptr_expr = *source,
                _ => break,
            }
        }
        let ty::Ref(_, pointee, _) = self.thir.exprs[ptr_expr].ty.kind() else {
            return None;
        };
        let ExprKind::VarRef { id } = &self.thir.exprs[ptr_expr].kind else {
            return None;
        };
        let base = self.local_value(*id)?;
        if *pointee != self.thir.exprs[deref].ty || !self.ref_param_ptrs.contains(&base) {
            return None;
        }
        // Do not register arbitrary new parents merely to probe this lane:
        // that could change established storage-free registration order. An
        // existing table is read-only; an unregistered parent is selected only
        // by an actual direct union field, without layout or destructor calls.
        // Registration still requires the separate source-bound storage witness;
        // custom-Drop/unproved unions keep their established confinement.
        if self.registered_struct_id(*pointee).is_none() {
            let ty::Adt(def, args) = pointee.kind() else { return None };
            if !def.is_struct() || !def.non_enum_variant().fields.iter().any(|field| {
                matches!(field.ty(self.tcx, *args).skip_normalization().kind(), ty::Adt(inner, _)
                    if inner.is_union())
            }) {
                return None;
            }
        }
        // Query the exact borrowed pending tables, never a cloned module or a
        // scalar-size guess. Unknown by-value schemas cannot establish freedom.
        let parent = self.map_ty(*pointee);
        if trust_ir::ByValueStorageQuery::new(
            &self.pending_tys,
            &self.pending_structs,
            &[],
            &self.pending_enums,
            &self.pending_closure_tys,
        )
        .is_storage_free(&parent)
        {
            return None;
        }
        let leaf_ty = self.thir.exprs[leaf].ty;
        if !matches!(leaf_ty.kind(), ty::Int(_) | ty::Uint(_))
            || self.place_projects_through_packed(leaf)
        {
            return Some(Err("Field(storage reference unsupported type/alignment)"));
        }
        let offset = match self.raw_entry_field_offset(leaf, deref, chain) {
            Ok(offset) => offset,
            Err(_) => return Some(Err("Field(storage reference layout disagrees)")),
        };
        let displacement = self.fresh();
        self.push_node(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(offset as i128) })
                .with_result(displacement),
        );
        let pointer = self.fresh();
        self.push_node(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I8,
                base,
                indices: vec![displacement],
                inbounds: false,
            })
            .with_result(pointer),
        );
        let result = self.fresh();
        let ty = self.map_ty(leaf_ty);
        self.push_node(
            InstrNode::new(Inst::Load { ty, ptr: pointer, volatile: false, align: None })
                .with_result(result),
        );
        Some(Ok(result))
    }

    pub(super) fn raw_entry_memory_value(&self, value: ValueId) -> bool {
        !self.is_borrow_ptr(value)
            && (self.raw_ptr_param_ptrs.contains(&value)
                || self.raw_retyped_entry_ptrs.contains(&value))
    }

    /// Pure recognition before emission. Only wrappers, local reads and proven
    /// thin raw-to-raw casts qualify. Calls, GEPs, integer-derived pointers and
    /// local borrows cannot cause an effectful probe to run and then fall back.
    pub(super) fn raw_entry_field_pointer_expr(&self, mut expr: ExprId) -> bool {
        loop {
            match &self.thir.exprs[expr].kind {
                ExprKind::Scope { value, .. } => expr = *value,
                ExprKind::ValueExpr { source } => expr = *source,
                ExprKind::VarRef { id } => {
                    return matches!(self.thir.exprs[expr].ty.kind(), ty::RawPtr(..))
                        && self.local_value(*id).is_some_and(|v| self.raw_entry_memory_value(v));
                }
                ExprKind::Cast { source } => {
                    let source_ty = self.thir.exprs[*source].ty;
                    let dest_ty = self.thir.exprs[expr].ty;
                    if !matches!(source_ty.kind(), ty::RawPtr(..))
                        || !matches!(dest_ty.kind(), ty::RawPtr(..))
                        || self.thin_ref_ret_ty(source_ty).is_none()
                        || self.thin_ref_ret_ty(dest_ty).is_none()
                    {
                        return false;
                    }
                    expr = *source;
                }
                _ => return false,
            }
        }
    }

    /// Shared with raw-entry stores: every link uses its actual instantiated
    /// Rust struct layout and the existing IR declaration agreement check.
    pub(super) fn raw_entry_field_offset(
        &mut self,
        leaf: ExprId,
        deref: ExprId,
        chain: &[(ExprId, u32)],
    ) -> Result<u64, RawFieldLayoutError> {
        let mut holder = self.thir.exprs[deref].ty;
        let mut offset = 0u64;
        for &(field_expr, field) in chain {
            let (off, source) =
                self.field_byte_offset(holder, field).ok_or(RawFieldLayoutError::Unavailable)?;
            let sid = self.struct_id_for_interior_offset(holder, field, off, source);
            if !self.struct_interior_offset_admissible(sid, field, off, source) {
                return Err(RawFieldLayoutError::Disagrees);
            }
            offset = offset.checked_add(off).ok_or(RawFieldLayoutError::Overflow)?;
            holder = self.thir.exprs[field_expr].ty;
        }
        if chain.is_empty() || holder != self.thir.exprs[leaf].ty || offset > i64::MAX as u64 {
            return Err(RawFieldLayoutError::Path);
        }
        Ok(offset)
    }

    pub(super) fn lower_raw_entry_field_read(
        &mut self,
        leaf: ExprId,
        ptr_expr: ExprId,
        deref: ExprId,
        chain: &[(ExprId, u32)],
    ) -> Result<ValueId, &'static str> {
        let leaf_ty = self.thir.exprs[leaf].ty;
        if !matches!(leaf_ty.kind(), ty::Int(_) | ty::Uint(_))
            || self.place_projects_through_packed(leaf)
        {
            return Err("Field(raw entry unsupported type/alignment)");
        }
        let offset = self
            .raw_entry_field_offset(leaf, deref, chain)
            .map_err(RawFieldLayoutError::read_tag)?;
        let base = self.lower_expr(ptr_expr).ok_or("Field(raw entry pointer no value)")?;
        if !matches!(self.thir.exprs[ptr_expr].ty.kind(), ty::RawPtr(pointee, _)
            if *pointee == self.thir.exprs[deref].ty)
            || !self.raw_entry_memory_value(base)
        {
            return Err("Field(raw entry pointer origin/type)");
        }
        let displacement = self.fresh();
        self.push_node(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(offset as i128) })
                .with_result(displacement),
        );
        let pointer = self.fresh();
        self.push_node(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I8,
                base,
                indices: vec![displacement],
                inbounds: false,
            })
            .with_result(pointer),
        );
        let result = self.fresh();
        let ty = self.map_ty(leaf_ty);
        self.push_node(
            InstrNode::new(Inst::Load { ty, ptr: pointer, volatile: false, align: None })
                .with_result(result),
        );
        Ok(result)
    }
}
