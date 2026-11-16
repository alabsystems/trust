//! First materialization of an owned shared temporary, scanned as producer code.

use rustc_middle::thir::{ExprId, ExprKind};
use rustc_middle::ty::TypeVisitableExt;
use trust_ir::{Constant, Inst, InstrNode, Ty, ValueId};

use super::{Observed, RootKind, TempRoot};
use crate::LowerCx;

impl<'a, 'tcx> LowerCx<'a, 'tcx> {
    /// The planner, rather than the lowered spelling, identifies the exact owned object.
    /// Only the shared borrow of a whole tracked temporary can materialize its home here;
    /// a field, an existing place, a raw borrow, or another root cannot borrow this admission.
    pub(crate) fn owns_shared_drop_temporary(&self, borrow: ExprId, operand: ExprId) -> bool {
        let Some(&r) = self.drops.temp_borrows.get(&borrow.as_u32()) else {
            return false;
        };
        if self.drops.temp_exprs.get(&operand.as_u32()) != Some(&r) {
            return false;
        }
        let Some(plan) = self.drops.plan.as_ref() else {
            return false;
        };
        let root = &plan.roots[r];
        root.ty == self.thir.exprs[operand].ty
            && !root.ty.has_non_region_param()
            && matches!(
                &root.kind,
                RootKind::Temp(TempRoot {
                    observed: Observed::Shared,
                    borrow: Some(b),
                    ..
                }) if *b == borrow
            )
            && matches!(
                self.thir.exprs[borrow].kind,
                ExprKind::Borrow { borrow_kind: rustc_middle::mir::BorrowKind::Shared, arg }
                    if arg == operand
            )
    }

    pub(crate) fn record_owned_shared_temporary(&mut self, value: ValueId, slot: ValueId, ty: Ty) {
        self.drops.owned_shared_temps.push((value, slot, ty));
    }

    /// Materialize a drop-bearing temporary once and lend its actual field.
    /// `Some(None)` means this owned projection was refused; no snapshot lane
    /// may then retry it and silently discard the root's destruction.
    pub(crate) fn try_lower_owned_temp_field_borrow(
        &mut self,
        borrow: ExprId,
        mut place: ExprId,
    ) -> Option<Option<ValueId>> {
        let span = self.thir.exprs[borrow].span;
        let mut fields = Vec::new();
        let mut unsupported_projection = false;
        let mut root_expression = place;
        loop {
            match self.thir.exprs[place].kind {
                ExprKind::Scope { value, .. } => place = value,
                ExprKind::Field { lhs, name, variant_index } => {
                    unsupported_projection |= variant_index.as_usize() != 0;
                    fields.push((place, name.as_u32()));
                    place = lhs;
                    root_expression = lhs;
                }
                ExprKind::Index { lhs, .. } => {
                    unsupported_projection = true;
                    place = lhs;
                    root_expression = lhs;
                }
                ExprKind::Deref { arg } if fields.is_empty() => {
                    let mut inner = arg;
                    while let ExprKind::Scope { value, .. } = self.thir.exprs[inner].kind {
                        inner = value;
                    }
                    if let ExprKind::Borrow { arg, .. } = self.thir.exprs[inner].kind {
                        place = arg;
                        root_expression = arg;
                    } else {
                        return None;
                    }
                }
                _ => break,
            }
        }
        if fields.is_empty() {
            return None;
        }
        // Existing places belong to their caller/local, not to a new temporary.
        if matches!(
            self.thir.exprs[place].kind,
            ExprKind::VarRef { .. }
                | ExprKind::UpvarRef { .. }
                | ExprKind::Deref { .. }
                | ExprKind::StaticRef { .. }
        ) {
            return None;
        }
        let root_rty = self.thir.exprs[place].ty;
        let env = rustc_middle::ty::TypingEnv::non_body_analysis(self.tcx, self.body_def);
        if !crate::cycle_safe_needs_drop(self.tcx, env, root_rty) {
            return None;
        }
        let reject = |cx: &mut Self, reason: &'static str| {
            cx.unsupported.push((format!("{span:?}"), reason));
            Some(None)
        };
        let Some(&root_index) = self
            .drops
            .temp_exprs
            .get(&root_expression.as_u32())
            .or_else(|| self.drops.temp_exprs.get(&place.as_u32()))
        else {
            return reject(self, "Borrow(temporary field root is unplanned)");
        };
        let planned = self.drops.plan.as_ref().is_some_and(|plan| {
            let root = &plan.roots[root_index];
            root.ty == root_rty
                && matches!(
                    &root.kind,
                    RootKind::Temp(TempRoot { observed: Observed::Shared, borrow: None, .. })
                )
        });
        if !planned
            || unsupported_projection
            || !matches!(
                self.thir.exprs[borrow].kind,
                ExprKind::Borrow { borrow_kind: rustc_middle::mir::BorrowKind::Shared, .. }
            )
        {
            return reject(self, "Borrow(temporary projection has no shared field home)");
        }
        if root_rty.has_non_region_param() || self.drops.partial_homes.contains_key(&root_index) {
            return reject(self, "Borrow(temporary field home is ambiguous)");
        }
        let mark = self.unsupported.len();
        let root_ty = self.map_ty(root_rty);
        let borrow_ty = self.map_ty(self.thir.exprs[borrow].ty);
        if self.unsupported.len() != mark {
            return reject(self, "Borrow(temporary field root type is unrepresentable)");
        }
        if borrow_ty != Ty::Ptr {
            return reject(self, "Borrow(temporary field reference is not thin)");
        }
        let Some((root_size, root_align)) = self.emitted_field_size_align(&root_ty) else {
            return reject(self, "Borrow(temporary root layout is unavailable)");
        };
        // Every offset must agree with BOTH Rust's layout and the exact
        // registered Trust type. No canonical C tuple layout is substituted.
        let mut parent_rty = root_rty;
        let mut parent_ty = root_ty.clone();
        let mut offset = 0u64;
        for (field_expr, field) in fields.into_iter().rev() {
            let child_rty = self.thir.exprs[field_expr].ty;
            let child_ty = self.map_ty(child_rty);
            let Some(layout) = crate::cycle_safe_layout_of(self.tcx, env, parent_rty) else {
                return reject(self, "Borrow(temporary field layout is unavailable)");
            };
            if field as usize >= layout.fields.count() {
                return reject(self, "Borrow(temporary field index is invalid)");
            }
            let field_offset = layout.fields.offset(field as usize).bytes();
            let agrees = match &parent_ty {
                Ty::Struct(id) => {
                    self.pending_structs.iter().find(|s| s.id == *id).is_some_and(|s| {
                        s.size == Some(layout.size.bytes())
                            && s.align == Some(layout.align.bytes())
                            && s.fields
                                .get(field as usize)
                                .is_some_and(|f| f.ty == child_ty && f.offset == Some(field_offset))
                    })
                }
                Ty::Tuple(types) => {
                    types.get(field as usize) == Some(&child_ty)
                        && self.pending_ty_ids.get(&parent_ty).is_some_and(|id| {
                            self.pending_tuple_layouts.iter().any(|d| {
                                d.tuple_type == *id
                                    && d.size == layout.size.bytes()
                                    && d.align == layout.align.bytes()
                                    && d.field_offsets.get(field as usize) == Some(&field_offset)
                            })
                        })
                }
                _ => false,
            };
            if !agrees || self.unsupported.len() != mark {
                return reject(self, "Borrow(temporary field layout disagrees)");
            }
            let Some(next) = offset.checked_add(field_offset) else {
                return reject(self, "Borrow(temporary field offset overflow)");
            };
            offset = next;
            parent_rty = child_rty;
            parent_ty = child_ty;
        }
        let Some((field_size, field_align)) = self.emitted_field_size_align(&parent_ty) else {
            return reject(self, "Borrow(temporary field layout is unavailable)");
        };
        if field_align == 0
            || root_align % field_align != 0
            || offset % field_align != 0
            || !offset.checked_add(field_size).is_some_and(|end| end <= root_size)
        {
            return reject(self, "Borrow(temporary field is outside or misaligned in its home)");
        }
        // Preserve the root's Scope wrappers so their normal drop hooks run.
        let Some(value) = self.lower_expr(root_expression) else {
            if !self.sealed && self.unsupported.len() == mark {
                return reject(self, "Borrow(temporary field value is unavailable)");
            }
            return Some(None);
        };
        if self.unsupported.len() != mark || self.sealed {
            return Some(None);
        }
        if self.is_borrow_ptr(value) || self.carrier_spelling(value).is_some() {
            return reject(self, "Borrow(temporary field root is not an owned value)");
        }
        let slot = self.fresh();
        self.push_node(
            InstrNode::new(Inst::Alloca { ty: root_ty.clone(), count: None, align: None })
                .with_result(slot),
        );
        self.push_node(InstrNode::new(Inst::Store {
            ty: root_ty.clone(),
            ptr: slot,
            value,
            volatile: false,
            align: None,
        }));
        self.drops.partial_homes.insert(root_index, (value, slot, root_ty.clone()));
        self.record_owned_shared_temporary(value, slot, root_ty);
        let off = self.fresh();
        self.push_node(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(i128::from(offset)) })
                .with_result(off),
        );
        let pointer = self.fresh();
        self.push_node(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I8,
                base: slot,
                indices: vec![off],
                inbounds: true,
            })
            .with_result(pointer),
        );
        self.borrow_ptrs.push(pointer);
        self.frame_interior_ptrs.push(pointer);
        Some(Some(pointer))
    }
}
