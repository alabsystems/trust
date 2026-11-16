//! An irrefutable `ref mut` arm borrows the existing float place, never its value.
use super::*;

impl<'a, 'tcx> LowerCx<'a, 'tcx> {
    /// `None` declines without effects; `Some` owns the complete recognized arm.
    pub(super) fn try_lower_owned_float_ref_mut_match(
        &mut self,
        span: rustc_span::Span,
        scrutinee: ExprId,
        arms: &[ArmId],
        mapped: &Ty,
    ) -> Option<Option<ValueId>> {
        if !float_storage::admits(mapped) {
            return None;
        }
        let [arm_id] = arms else { return None };
        let arm = &self.thir.arms[*arm_id];
        if arm.guard.is_some() {
            return None;
        }
        let PatKind::Binding {
            var,
            ty: binding_ty,
            mode: rustc_hir::BindingMode(
                rustc_hir::ByRef::Yes(rustc_hir::Pinnedness::Not, rustc_hir::Mutability::Mut),
                _,
            ),
            subpattern: None,
            is_primary: true,
            ..
        } = &arm.pattern.kind else { return None };
        let ty::Ref(_, pointee, rustc_hir::Mutability::Mut) = binding_ty.kind() else {
            return None;
        };
        if *pointee != self.thir.exprs[scrutinee].ty {
            return None;
        }
        let (binding, body) = (*var, arm.body);
        // Scope preserves this place; a cast, block, field, dereference or
        // ValueExpr has its own semantics and cannot borrow a local's home.
        let local = self.index_place_local(scrutinee)?;
        if self.is_promoted(binding) || self.promote_wanted.contains(&binding) {
            self.unsupported.push((format!("{span:?}"), "FloatMatch(ref-mut binding needs storage)"));
            return Some(None);
        }
        let slot = match (self.is_promoted(local), self.promoted_slot(local), self.promoted_ty(local)) {
            (true, Some(slot), Some(ty)) if &ty == mapped => slot,
            _ => {
                self.unsupported.push((format!("{span:?}"), "FloatMatch(ref-mut local lacks owned storage)"));
                return Some(None);
            }
        };
        // The same home and local borrow ledgers as `&mut local`. In particular,
        // no caller/global/interior lifetime permission is attached to this slot.
        if !self.borrow_ptrs.contains(&slot) {
            self.borrow_ptrs.push(slot);
        }
        if !self.mut_borrow_ptrs.contains(&slot) {
            self.mut_borrow_ptrs.push(slot);
        }
        self.set_local(binding, slot, Ty::Ptr);
        Some(self.lower_expr(body))
    }
}
