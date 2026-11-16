// Copyright 2026 Andrew Yates. SPDX-License-Identifier: MIT OR Apache-2.0
//! A thin raw mutability coercion preserves an existing address. It grants no
//! borrow, write, escape, pointer-to-integer, initialization or validity rights.

use super::*;

impl<'a, 'tcx> LowerCx<'a, 'tcx> {
    pub(super) fn lower_mut_to_const_raw_pointer(
        &mut self,
        destination: RustcTy<'tcx>,
        source: ExprId,
    ) -> Result<ValueId, &'static str> {
        let refused = pointer_coercion_refusal_tag(PointerCoercion::MutToConstPointer);
        let source_ty = self.monomorphize(self.thir.exprs[source].ty);
        let destination_ty = self.monomorphize(destination);
        // Check rustc's actual instantiated types before mapping: Ptr alone
        // cannot distinguish references, a changed pointee, or an unknown DST.
        if !matches!((source_ty.kind(), destination_ty.kind()),
            (ty::RawPtr(from, rustc_hir::Mutability::Mut),
             ty::RawPtr(to, rustc_hir::Mutability::Not)) if from == to)
            || self.thin_ref_ret_ty(source_ty) != Some(Ty::Ptr)
            || self.thin_ref_ret_ty(destination_ty) != Some(Ty::Ptr)
        {
            return Err(refused);
        }
        if self.map_ty(source_ty) != Ty::Ptr || self.map_ty(destination_ty) != Ty::Ptr {
            return Err(refused);
        }
        // Evaluate exactly once. A raw spelling of a ledgered borrow still
        // cannot cross this boundary, just as in the explicit PtrToPtr lane.
        let operand = self.lower_expr(source).ok_or(refused)?;
        if self.is_borrow_ptr(operand) {
            return Err(refused);
        }
        let result = self.fresh();
        self.push_node(
            InstrNode::new(Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: Ty::Ptr,
                operand,
            })
            .with_result(result),
        );
        // Only preserve the pre-existing memory-only incoming-address class.
        // In particular, do not enroll this result in raw_ptr_param_ptrs or
        // any borrow/write ledger; arbitrary raw values gain no access rights.
        if self.raw_entry_memory_value(operand) {
            self.raw_retyped_entry_ptrs.push(result);
        }
        Ok(result)
    }
}
