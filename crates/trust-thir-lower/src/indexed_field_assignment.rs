//! Scalar field writes to an element of an unborrowed local array.
//!
//! Compose the existing array and struct value operations, without manufacturing
//! an address or widening any borrowed/promoted storage lane. Planning is read
//! only; after it succeeds, this lane owns both operands and never falls back.

use rustc_middle::thir::{ExprId, ExprKind, LocalVarId};
use rustc_middle::ty::{self, Ty as RustcTy, TypeVisitableExt as _};
use trust_ir::proof::ProofAnnotation;
use trust_ir::{AssertKind, Constant, ICmpOp, Inst, InstrNode, Ty, ValueId};

use crate::{LowerCx, MirAssignOp, MirBinOp, is_scalar_ty, scalar_ret_ty};

struct Plan {
    local: LocalVarId,
    index: ExprId,
    array_ty: Ty,
    element_ty: Ty,
    field: u32,
    field_ty: Ty,
    len: u64,
}

impl<'a, 'tcx> LowerCx<'a, 'tcx> {
    /// A pure, narrow admission: Field(Index(Scope* VarRef)), with a real
    /// first-class array of a registered plain-data struct. ValueExpr is not
    /// transparent here: it creates a temporary, not the local's writable place.
    fn indexed_local_field_plan(&self, lhs: ExprId) -> Option<Plan> {
        let peel = |mut id: ExprId| {
            while let ExprKind::Scope { value, .. } = self.thir.exprs[id].kind {
                id = value;
            }
            id
        };
        let field_expr = peel(lhs);
        let ExprKind::Field { lhs: indexed, variant_index, name } =
            self.thir.exprs[field_expr].kind
        else {
            return None;
        };
        if variant_index.as_u32() != 0 {
            return None;
        }
        let indexed = peel(indexed);
        let ExprKind::Index { lhs: base, index } = self.thir.exprs[indexed].kind else {
            return None;
        };
        let local = self.index_place_local(base)?;
        if !self.indexed_field_local_is_ssa(local) {
            return None;
        }
        let array_rty = self.thir.exprs[base].ty;
        let ty::Array(element_rty, len) = array_rty.kind() else { return None };
        // No normalization or mapping probes: the source and registered image
        // must already agree before either operand is evaluated.
        if element_rty.has_param()
            || element_rty.has_infer()
            || element_rty.has_escaping_bound_vars()
        {
            return None;
        }
        let ty::Adt(adt, _) = element_rty.kind() else { return None };
        if !adt.is_struct() {
            return None;
        }
        let len = len.try_to_target_usize(self.tcx)?;
        let array_ty = self.local_ty(local)?;
        let Ty::Array(element_id, mapped_len) = &array_ty else { return None };
        if *mapped_len != len || len == 0 {
            return None;
        }
        let element_ty = self.pending_tys.get(element_id.as_usize())?.clone();
        let Ty::Struct(sid) = &element_ty else { return None };
        if self.registered_struct_id(*element_rty) != Some(*sid)
            || self.thir.exprs[indexed].ty != *element_rty
            || !matches!(self.thir.exprs[index].ty.kind(), ty::Uint(ty::UintTy::Usize))
        {
            return None;
        }
        let fields = self.registered_struct_field_tys(*sid)?;
        let source_fields = &adt.non_enum_variant().fields;
        if fields.len() != source_fields.len()
            || !self.registered_plain_value_matches(*element_rty, &element_ty)
        {
            return None;
        }
        let field = name.as_u32();
        let mapped_field = fields.get(field as usize)?;
        let source_field = scalar_ret_ty(self.thir.exprs[field_expr].ty)?;
        if !(is_scalar_ty(&source_field) || matches!(source_field, Ty::F32 | Ty::F64))
            || mapped_field != &source_field
        {
            return None;
        }
        Some(Plan { local, index, array_ty, element_ty, field, field_ty: source_field, len })
    }

    /// Check the complete value carried through Extract/InsertElement and
    /// InsertField, including siblings the write never selects. A scalar-only
    /// screen needlessly rejects faithful nested aggregates; plain_data_rty
    /// alone also accepts enums whose emitted image may have collapsed.
    ///
    /// This is a read-only comparison with the already registered image. It
    /// cannot normalize, register a type, create an opaque value, or add a
    /// lowering refusal while deciding whether this place lane owns the write.
    /// Exact pairs are visited once, without recursively expanding type DAGs or
    /// imposing a nesting limit. Pointer, enum and Drop-bearing leaves refuse.
    pub(super) fn registered_plain_value_matches(&self, source: RustcTy<'tcx>, mapped: &Ty) -> bool {
        let mut pending = vec![(source, mapped.clone())];
        let mut checked = std::collections::HashSet::new();
        while let Some((source, mapped)) = pending.pop() {
            if !checked.insert((source, mapped.clone())) {
                continue;
            }
            // The signature helper also maps tuples and thin pointers. Only
            // primitive source kinds belong to the scalar leaf decision; a
            // tuple must reach the structural worklist arm below.
            if matches!(source.kind(), ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_)) {
                let Some(scalar) = scalar_ret_ty(source) else { return false };
                if (is_scalar_ty(&scalar) || matches!(scalar, Ty::F32 | Ty::F64))
                    && scalar == mapped
                {
                    continue;
                }
                return false;
            }
            match (source.kind(), &mapped) {
                (ty::Tuple(source), Ty::Unit) if source.is_empty() => {}
                (ty::Tuple(source), Ty::Tuple(mapped)) if source.len() == mapped.len() => {
                    pending.extend(source.iter().zip(mapped).map(|(s, m)| (s, m.clone())));
                }
                (ty::Array(source, len), Ty::Array(element, mapped_len))
                    if len.try_to_target_usize(self.tcx) == Some(*mapped_len) =>
                {
                    let Some(mapped) = self.pending_tys.get(element.as_usize()) else {
                        return false;
                    };
                    pending.push((*source, mapped.clone()));
                }
                (ty::Adt(adt, args), Ty::Struct(sid))
                    if adt.is_struct()
                        && adt.destructor(self.tcx).is_none()
                        && self.registered_struct_id(source) == Some(*sid) =>
                {
                    let Some(mapped) = self.registered_struct_field_tys(*sid) else {
                        return false;
                    };
                    let fields = &adt.non_enum_variant().fields;
                    if fields.len() != mapped.len() {
                        return false;
                    }
                    pending.extend(fields.iter().zip(mapped).map(|(field, mapped)| {
                        (field.ty(self.tcx, *args).skip_normalization(), mapped)
                    }));
                }
                _ => return false,
            }
        }
        true
    }

    fn indexed_field_local_is_ssa(&self, local: LocalVarId) -> bool {
        !self.is_promoted(local)
            && self.promoted_slot(local).is_none()
            && !self.shared_value_slots.iter().any(|(var, _)| *var == local)
            && self.local_value(local).is_some_and(|value| !self.is_borrow_ptr(value))
    }

    /// `false` means a pure miss. `true` includes successful writes, divergence,
    /// and a refused operand: none may retry another lane or replay an effect.
    pub(crate) fn lower_indexed_local_field_assign(
        &mut self,
        span: rustc_span::Span,
        lhs: ExprId,
        rhs: ExprId,
    ) -> bool {
        self.lower_indexed_local_field_update(span, lhs, rhs, None)
    }

    pub(crate) fn lower_indexed_local_field_assign_op(
        &mut self,
        span: rustc_span::Span,
        op: MirAssignOp,
        lhs: ExprId,
        rhs: ExprId,
    ) -> bool {
        self.lower_indexed_local_field_update(span, lhs, rhs, Some(op))
    }

    /// Primitive compound assignment has the same RHS-first place evaluation
    /// as assignment. Read the selected field only after both operands, then
    /// use the common checked arithmetic emitter before updating that exact
    /// element. The unborrowed local, registered layout and sibling-type
    /// requirements are identical for both operations.
    fn lower_indexed_local_field_update(
        &mut self,
        span: rustc_span::Span,
        lhs: ExprId,
        rhs: ExprId,
        operation: Option<MirAssignOp>,
    ) -> bool {
        let Some(plan) = self.indexed_local_field_plan(lhs) else { return false };
        let rhs_no_value = if operation.is_some() {
            "AssignOp(indexed field rhs no value)"
        } else {
            "Assign(indexed field rhs no value)"
        };
        let index_no_value = if operation.is_some() {
            "AssignOp(indexed field index no value)"
        } else {
            "Assign(indexed field index no value)"
        };
        let storage_changed = if operation.is_some() {
            "AssignOp(indexed field storage changed)"
        } else {
            "Assign(indexed field storage changed)"
        };
        let mark = self.unsupported.len();
        let rhs_ty = self.thir.exprs[rhs].ty;
        let lowered_rhs = self.lower_expr(rhs);
        if self.sealed || self.unsupported.len() != mark {
            return true;
        }
        let Some(value) = lowered_rhs.filter(|value| !self.is_borrow_ptr(*value)) else {
            self.unsupported.push((format!("{span:?}"), rhs_no_value));
            return true;
        };
        let index = self.lower_expr(plan.index);
        if self.sealed || self.unsupported.len() != mark {
            return true;
        }
        let Some(index) = index.filter(|value| !self.is_borrow_ptr(*value)) else {
            self.unsupported.push((format!("{span:?}"), index_no_value));
            return true;
        };
        // RHS/index may replace the array, or even materialize address storage.
        // Re-read its current SSA value only after both effects and fail closed
        // if it acquired storage; never overwrite a stale pre-operand snapshot.
        if !self.indexed_field_local_is_ssa(plan.local)
            || self.local_ty(plan.local).as_ref() != Some(&plan.array_ty)
        {
            self.unsupported.push((format!("{span:?}"), storage_changed));
            return true;
        }
        let Some(current) = self.local_value(plan.local) else {
            self.unsupported.push((format!("{span:?}"), storage_changed));
            return true;
        };
        let len = self.fresh();
        self.push_node(
            InstrNode::new(Inst::Const {
                ty: Ty::Usize,
                value: Constant::Int(i128::from(plan.len)),
            })
            .with_result(len),
        );
        let in_bounds = self.fresh();
        self.push_node(
            InstrNode::new(Inst::ICmp { op: ICmpOp::Ult, ty: Ty::Usize, lhs: index, rhs: len })
                .with_result(in_bounds),
        );
        self.push_node(
            InstrNode::new(Inst::Assert {
                cond: in_bounds,
                kind: AssertKind::BoundsCheck { index, len },
                site: None,
            })
            .with_proof(ProofAnnotation::InBounds),
        );
        self.record_direct_assert_typed(
            crate::direct_obligations::SLUG_BOUNDS_CHECK,
            ProofAnnotation::InBounds,
            span,
            &crate::direct_formula_capture::DirectAssertShape::Bounds { index, len: plan.len },
        );
        // A literal out-of-range SSA index makes the assertion above panic.
        // Do not emit statically invalid element operations after that check:
        // the validator checks their indices even in unreachable code. Read
        // the emitted value, including predecessor blocks, rather than probing
        // or re-evaluating the original (possibly effectful) index expression.
        if self.indexed_field_constant_out_of_bounds(index, plan.len) {
            // SEAL(divergence): the preceding bounds assertion always panics for this literal index.
            self.seal_with(Inst::Unreachable);
            return true;
        }
        let element = self.fresh();
        self.push_node(
            InstrNode::new(Inst::ExtractElement {
                ty: plan.element_ty.clone(),
                array: current,
                index,
            })
            .with_result(element),
        );
        let value = if let Some(op) = operation {
            let current_field = self.fresh();
            self.push_node(
                InstrNode::new(Inst::ExtractField {
                    ty: plan.field_ty.clone(),
                    aggregate: element,
                    field: plan.field,
                })
                .with_result(current_field),
            );
            let signed = matches!(self.thir.exprs[lhs].ty.kind(), ty::Int(_));
            let Some(updated) = self.emit_arith_binop(
                span, MirBinOp::from(op), plan.field_ty, signed, rhs_ty, current_field, value,
            ) else {
                // A refused operation or checked divergence owns this route;
                // neither may retry the operands through another place lane.
                return true;
            };
            updated
        } else {
            value
        };
        let updated_element = self.fresh();
        self.push_node(
            InstrNode::new(Inst::InsertField {
                ty: plan.element_ty,
                aggregate: element,
                field: plan.field,
                value,
            })
            .with_result(updated_element),
        );
        let updated_array = self.fresh();
        self.push_node(
            InstrNode::new(Inst::InsertElement {
                ty: plan.array_ty.clone(),
                array: current,
                index,
                value: updated_element,
            })
            .with_result(updated_array),
        );
        self.set_local(plan.local, updated_array, plan.array_ty);
        true
    }

    fn indexed_field_constant_out_of_bounds(&self, index: ValueId, len: u64) -> bool {
        self.cur.iter().chain(self.blocks.iter().flat_map(|block| &block.body)).any(|node| {
            node.results.len() == 1
                && node.results.first() == Some(&index)
                && matches!(
                    &node.inst,
                    Inst::Const { ty: Ty::Usize, value: Constant::Int(value) }
                        if *value < 0 || *value >= i128::from(len)
                )
        })
    }
}
