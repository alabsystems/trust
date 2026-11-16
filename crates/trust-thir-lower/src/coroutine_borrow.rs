// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Stable storage for shared borrows of a yield-free coroutine's owned captures.
//!
//! The coroutine signature is a register aggregate, not rustc's suspended-frame
//! layout. Move each borrowed capture into its own entry slot and read that slot
//! thereafter. This needs no invented field offsets and never gives the borrow a
//! second copy of a drop-bearing owner. Coroutine drop placement is still refused
//! by the existing planner and checked independently by effect conservation.

use super::*;

impl<'a, 'tcx> LowerCx<'a, 'tcx> {
    fn coroutine_capture_borrow_index(
        &self,
        result_ty: RustcTy<'tcx>,
        mut arg: ExprId,
    ) -> Option<usize> {
        if self.coroutine_frame_ptr || self.coroutine_env_fields.is_none() {
            return None;
        }
        let param = self.thir.params.raw.first()?;
        if param.pat.is_some() {
            return None;
        }
        let ty::Coroutine(def, args) = param.ty.kind() else { return None };
        // Only transparent place wrappers: an inner dereference can denote a
        // different owner and must go through the ordinary reborrow machinery.
        loop {
            match self.thir.exprs[arg].kind {
                ExprKind::Scope { value, .. } => arg = value,
                ExprKind::ValueExpr { source } => arg = source,
                _ => break,
            }
        }
        let ExprKind::UpvarRef { closure_def_id, var_hir_id } = self.thir.exprs[arg].kind else {
            return None;
        };
        if closure_def_id != *def {
            return None;
        }
        let variable_ty = self.thir.exprs[arg].ty;
        let ty::Ref(_, pointee, rustc_hir::Mutability::Not) = result_ty.kind() else {
            return None;
        };
        if *pointee != variable_ty || self.fat_shape(result_ty, &mut Vec::new()) != FatShape::Thin {
            return None;
        }
        let captures = self.tcx.closure_captures(def.as_local()?);
        let mut matching =
            captures.iter().enumerate().filter(|(_, cap)| cap.get_root_variable() == var_hir_id.0);
        let (index, capture) = matching.next()?;
        if matching.next().is_some()
            || !capture.place.projections.is_empty()
            || !matches!(
                capture.info.capture_kind,
                ty::UpvarCapture::ByValue | ty::UpvarCapture::ByUse
            )
        {
            return None;
        }
        // Type equality alone cannot distinguish owning a pointer from borrowing
        // its pointee. Require both the capture kind above and the actual field type.
        let upvars = args.as_coroutine().upvar_tys();
        let fields = self.coroutine_env_fields.as_ref()?;
        if fields.len() != upvars.len()
            || captures.len() != upvars.len()
            || upvars.get(index).copied()? != variable_ty
        {
            return None;
        }
        fields.get(index)?;
        Some(index)
    }

    pub(super) fn coroutine_capture_home(&self, index: usize) -> Option<ValueId> {
        self.coroutine_capture_homes
            .iter()
            .find_map(|(field, ptr)| (*field == index).then_some(*ptr))
    }

    /// Establish homes before lowering any control flow. Lazy allocation at the
    /// first textual borrow would leave reads in earlier-lowered loop/branch
    /// blocks observing the original aggregate after a later mutation.
    pub(super) fn prepare_coroutine_capture_homes(&mut self) {
        if self.coroutine_env_fields.is_none() {
            return;
        }
        let borrowed: Vec<usize> =
            self.thir
                .exprs
                .iter()
                .filter_map(|expr| {
                    let ExprKind::Borrow {
                        borrow_kind:
                            rustc_middle::mir::BorrowKind::Shared
                            | rustc_middle::mir::BorrowKind::Fake(_),
                        arg,
                    } = expr.kind
                    else {
                        return None;
                    };
                    self.coroutine_capture_borrow_index(expr.ty, arg)
                })
                .collect();
        for index in borrowed {
            if self.coroutine_capture_home(index).is_some() {
                continue;
            }
            let field_ty = self.coroutine_env_fields.as_ref().unwrap()[index].clone();
            let initial = self.fresh();
            self.push_node(
                InstrNode::new(Inst::ExtractField {
                    ty: field_ty.clone(),
                    aggregate: ValueId::new(0),
                    field: index as u32,
                })
                .with_result(initial),
            );
            let ptr = self.fresh();
            self.push_node(
                InstrNode::new(Inst::Alloca { ty: field_ty.clone(), count: None, align: None })
                    .with_result(ptr),
            );
            self.push_node(InstrNode::new(Inst::Store {
                ty: field_ty,
                ptr,
                value: initial,
                volatile: false,
                align: None,
            }));
            self.coroutine_capture_homes.push((index, ptr));
        }
    }

    pub(super) fn try_lower_coroutine_capture_borrow(
        &mut self,
        result_ty: RustcTy<'tcx>,
        arg: ExprId,
    ) -> Option<ValueId> {
        let index = self.coroutine_capture_borrow_index(result_ty, arg)?;
        let ptr = self.coroutine_capture_home(index)?;
        // Only shared access, and no claim that this address outlives the call.
        // The return, raw-pointer and aggregate escape guards retain their gates.
        if !self.borrow_ptrs.contains(&ptr) {
            self.borrow_ptrs.push(ptr);
        }
        Some(ptr)
    }
}
