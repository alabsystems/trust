//! Transport real Rust unit to owned value positions without changing its call-return ABI.
use super::*;

impl<'a, 'tcx> LowerCx<'a, 'tcx> {
    /// Real unit literals/constants, and completed canonical unit calls, can
    /// supply the singleton value of an already-owned unit destination.
    pub(super) fn owned_unit_rhs_value(
        &mut self,
        lhs: ExprId,
        rhs: ExprId,
        local: LocalVarId,
        unsupported_mark: usize,
        instruction_mark: (BlockId, usize),
    ) -> Option<ValueId> {
        if self.sealed
            || self.unsupported.len() != unsupported_mark
            || !self.is_promoted(local)
            || self.promoted_slot(local).is_none()
            || self.promoted_ty(local) != Some(Ty::Unit)
        {
            return None;
        }
        let lhs_ty = self.monomorphize(self.thir.exprs[lhs].ty);
        let rhs_ty = self.monomorphize(self.thir.exprs[rhs].ty);
        if primitive_storage::image(lhs_ty) != Some(Ty::Unit)
            || primitive_storage::image(rhs_ty) != Some(Ty::Unit)
        {
            return None;
        }
        // Reuse the existing effect-free, exact-source literal/CTFE admission.
        // It refuses unbound locals, blocks, assignments and computed calls.
        if let Some(value) = self.try_lower_unit_arg(rhs, unsupported_mark) {
            return Some(value);
        }
        if self.cur_id == instruction_mark.0 && self.cur.len() <= instruction_mark.1 {
            return None;
        }
        let mut source = rhs;
        loop {
            match self.thir.exprs[source].kind {
                ExprKind::Scope { value, .. } => source = value,
                ExprKind::ValueExpr { source: value } => source = value,
                _ => break,
            }
        }
        let ExprKind::Call { fun, .. } = self.thir.exprs[source].kind else { return None };
        let fun = self.peel_scope_use(fun);
        if !matches!(self.thir.exprs[fun].kind, ExprKind::ZstLiteral { .. }) {
            // A computed function expression has evaluation of its own.
            return None;
        }
        let function_ty = self.monomorphize(self.thir.exprs[fun].ty);
        let ty::FnDef(site, _) = function_ty.kind() else { return None };
        let node = self.cur.last()?;
        let Inst::Call { callee, .. } = &node.inst else { return None };
        if !node.results.is_empty() { return None; }
        // A nested argument call cannot stand in for an un-emitted outer call.
        // Use the existing canonical callee ledger; do not resolve or emit again.
        if !self.callees.iter().any(|row| {
            row.func_id == *callee
                && row.site_def_id == *site
                && row.concrete_key.is_some()
                && !row.force_havoc
        }) {
            return None;
        }
        let value = self.fresh();
        self.push_node(
            InstrNode::new(Inst::Const { ty: Ty::Unit, value: Constant::PhantomData })
                .with_result(value),
        );
        Some(value)
    }

    /// Read an actual unit lane from a real tuple through the ordinary ExtractField.
    /// An opaque Unit spelling or a struct/enum/pointer holder is not this route.
    pub(super) fn primitive_unit_tuple_field(
        &mut self,
        holder: ExprId,
        field: u32,
        source: RustcTy<'tcx>,
        mapped: &Ty,
    ) -> bool {
        if *mapped != Ty::Unit
            || primitive_storage::image(self.monomorphize(source)) != Some(Ty::Unit)
        {
            return false;
        }
        let holder_ty = self.monomorphize(self.thir.exprs[holder].ty);
        let ty::Tuple(fields) = holder_ty.kind() else { return false };
        fields.get(field as usize).is_some_and(|field_ty| {
            primitive_storage::image(self.monomorphize(*field_ty)) == Some(Ty::Unit)
        })
    }
}
