//! Source-ordered shared-slice destructuring, with real payload addresses.
//!
//! A length test dominates every element address and subslice construction.
//! This is structural lowering, without a proof or body-admission upgrade.

use super::*;

struct SliceArm {
    prefix: Vec<Option<LocalVarId>>,
    suffix: Vec<Option<LocalVarId>>,
    // Outer Some means a rest exists; inner Some means it is bound.
    rest: Option<Option<LocalVarId>>,
    body: ExprId,
}

/// The match's place may be `s` or the unsized place `*s`. Recover only the
/// exact shared-slice pointer; do not erase a deref/call for an unrelated type.
fn shared_slice<'tcx>(thir: &Thir<'tcx>, mut expr: ExprId) -> Option<(ExprId, RustcTy<'tcx>)> {
    loop {
        match thir.exprs[expr].kind {
            ExprKind::Scope { value, .. } => expr = value,
            ExprKind::ValueExpr { source } => expr = source,
            _ => break,
        }
    }
    if let ExprKind::Deref { arg } = thir.exprs[expr].kind {
        if matches!(thir.exprs[expr].ty.kind(), ty::Slice(_)) {
            if !matches!(thir.exprs[arg].ty.kind(),
                ty::Ref(_, pointee, rustc_hir::Mutability::Not) if *pointee == thir.exprs[expr].ty)
            {
                return None;
            }
            expr = arg;
        }
    }
    let ty::Ref(_, pointee, rustc_hir::Mutability::Not) = thir.exprs[expr].ty.kind() else {
        return None;
    };
    let ty::Slice(element) = pointee.kind() else { return None };
    Some((expr, *element))
}

fn element_binding<'tcx>(pat: &Pat<'tcx>, element: RustcTy<'tcx>) -> Option<Option<LocalVarId>> {
    if pat.ty != element {
        return None;
    }
    match &pat.kind {
        PatKind::Wild => Some(None),
        PatKind::Binding {
            var,
            mode: rustc_hir::BindingMode(rustc_hir::ByRef::Yes(_, rustc_hir::Mutability::Not), _),
            ty: binding_ty,
            subpattern: None,
            ..
        } if matches!(binding_ty.kind(),
            ty::Ref(_, pointee, rustc_hir::Mutability::Not) if *pointee == element) =>
        {
            Some(Some(*var))
        }
        _ => None,
    }
}

impl<'a, 'tcx> LowerCx<'a, 'tcx> {
    /// None is a preflight decline with no IR emitted; Some owns the match,
    /// including failures in its scrutinee/body. Never retry a failed lowering.
    pub(super) fn try_lower_ordered_slice_match(
        &mut self,
        result_rty: RustcTy<'tcx>,
        span: rustc_span::Span,
        scrutinee: ExprId,
        arms: &[ArmId],
    ) -> Option<Option<ValueId>> {
        if self.tcx.data_layout.pointer_size().bits() != 64 {
            return None;
        }
        let (pointer_expr, element) = shared_slice(self.thir, scrutinee)?;
        let pointer_rty = self.thir.exprs[pointer_expr].ty;
        let mut cases = Vec::new();
        let mut default = None;
        for arm_id in arms {
            let arm = &self.thir.arms[*arm_id];
            if arm.guard.is_some() || default.is_some() {
                return None;
            }
            let mut pattern = &*arm.pattern;
            if matches!(pattern.kind, PatKind::Wild) {
                default = Some(arm.body);
                continue;
            }
            if let PatKind::Deref { pin: rustc_hir::Pinnedness::Not, subpattern } = &pattern.kind {
                // Exactly the one reference to the slice, not `&&[T]` or
                // a deref pattern that invokes user code.
                if pattern.ty != pointer_rty {
                    return None;
                }
                pattern = subpattern;
            }
            let PatKind::Slice { prefix, slice, suffix } = &pattern.kind else {
                return None;
            };
            if !matches!(pattern.ty.kind(), ty::Slice(t) if *t == element) {
                return None;
            }
            let prefix =
                prefix.iter().map(|p| element_binding(p, element)).collect::<Option<Vec<_>>>()?;
            let suffix =
                suffix.iter().map(|p| element_binding(p, element)).collect::<Option<Vec<_>>>()?;
            let rest = match slice {
                None => None,
                Some(rest) if rest.ty == pattern.ty => Some(match &rest.kind {
                    PatKind::Wild => None,
                    PatKind::Binding {
                        var,
                        mode:
                            rustc_hir::BindingMode(
                                rustc_hir::ByRef::Yes(_, rustc_hir::Mutability::Not),
                                _,
                            ),
                        ty: binding_ty,
                        subpattern,
                        ..
                    } if *binding_ty == pointer_rty
                        && subpattern.as_ref().is_none_or(|p| matches!(p.kind, PatKind::Wild)) =>
                    {
                        Some(*var)
                    }
                    _ => return None,
                }),
                Some(_) => return None,
            };
            let mut seen = std::collections::HashSet::new();
            for var in prefix.iter().chain(&suffix).flatten().copied().chain(rest.flatten()) {
                if self.is_promoted(var) || !seen.insert(var) {
                    return None;
                }
            }
            prefix.len().checked_add(suffix.len()).and_then(|n| u64::try_from(n).ok())?;
            cases.push(SliceArm { prefix, suffix, rest, body: arm.body });
        }
        if cases.is_empty() {
            return None;
        }
        // Actual Rust element layout, including ZSTs. A missing/unknown layout
        // refuses; no opaque element or guessed aggregate stride is used.
        let size =
            self.cycle_safe_layout_of(ty::TypingEnv::fully_monomorphized(), element)?.size.bytes();
        for case in &cases {
            u64::try_from(case.prefix.len()).ok()?.checked_mul(size)?;
        }
        let fat_ty = self.map_ty(pointer_rty);
        if !matches!(fat_ty, Ty::FatPtr(trust_ir::FatPtrKind::Slice(_))) {
            return None;
        }
        let result_ty = self.map_ty(result_rty);
        // The shared provenance transfer currently covers only thin pointers.
        // Do not erase a rest-slice borrow at a fresh fat-pointer result join.
        if matches!(&result_ty, Ty::FatPtr(_)) {
            return None;
        }
        let value_producing = !matches!(result_ty, Ty::Unit);
        // Block IDs, not vector positions: emission can seal an already-open
        // caller block whose parameters predate this claimed match.
        let first_new_block = self.next_block as usize;
        let value = self.emit_ordered_slice_match(
            span,
            pointer_expr,
            fat_ty,
            result_rty,
            result_ty,
            value_producing,
            size,
            cases,
            default,
        );
        // Inspect after emission returns, including its all-arms-diverge path.
        // Nested fat results can erase taint before returning directly from an
        // arm. No new fat join earns read/escape permissions in this matcher.
        let owned_blocks = first_new_block..self.next_block as usize;
        let mut fat_joins: Vec<_> = self.blocks.iter()
            .filter(|block| owned_blocks.contains(&block.id.as_usize()))
            .flat_map(|block| block.params.iter())
            .filter_map(|(value, ty)| matches!(ty, Ty::FatPtr(_)).then_some(*value))
            .collect();
        if owned_blocks.contains(&self.cur_id.as_usize()) {
            fat_joins.extend(self.cur_params.iter()
                .filter_map(|(value, ty)| matches!(ty, Ty::FatPtr(_)).then_some(*value)));
        }
        for joined in fat_joins {
            if !self.deferred_join_refusals.iter().any(|(value, _, _)| *value == joined) {
                self.deferred_join_refusals.push((
                    joined, span, "SliceMatch(fat pointer control-flow join)",
                ));
            }
        }
        Some(value)
    }

    fn emit_ordered_slice_match(
        &mut self,
        span: rustc_span::Span,
        pointer_expr: ExprId,
        fat_ty: Ty,
        result_rty: RustcTy<'tcx>,
        result_ty: Ty,
        value_producing: bool,
        size: u64,
        cases: Vec<SliceArm>,
        default: Option<ExprId>,
    ) -> Option<ValueId> {
        // Evaluate the original place expression exactly once, including calls.
        let pointer = match self.lower_expr(pointer_expr) {
            Some(pointer) => pointer,
            None => {
                self.unsupported.push((format!("{span:?}"), "SliceMatch(scrutinee unsupported)"));
                return None;
            }
        };
        let len = self.fresh();
        self.push_node(
            InstrNode::new(Inst::PtrMetadata {
                ptr_ty: fat_ty.clone(),
                metadata_ty: Ty::U64,
                ptr: pointer,
            })
            .with_result(len),
        );
        let data = self.fresh();
        self.push_node(
            InstrNode::new(Inst::PtrData { ptr_ty: fat_ty.clone(), ptr: pointer })
                .with_result(data),
        );
        let stride = self.slice_pattern_constant(size);
        let miss = self.fresh_block_id();
        let join = self.fresh_block_id();
        let blocks: Vec<_> =
            cases.iter().map(|_| (self.fresh_block_id(), self.fresh_block_id())).collect();
        self.seal_with(Inst::Br { target: blocks[0].0, args: vec![] });
        let before = self.locals.clone();
        let mut captured = Vec::new();
        for (i, case) in cases.into_iter().enumerate() {
            self.locals = before.clone();
            self.start_block(blocks[i].0, vec![]);
            let prefix = case.prefix.len() as u64;
            let suffix = case.suffix.len() as u64;
            let needed = self.slice_pattern_constant(prefix + suffix);
            let fits = self.fresh();
            self.push_node(
                InstrNode::new(Inst::ICmp {
                    op: if case.rest.is_some() { ICmpOp::Uge } else { ICmpOp::Eq },
                    ty: Ty::U64,
                    lhs: len,
                    rhs: needed,
                })
                .with_result(fits),
            );
            self.seal_with(Inst::CondBr {
                cond: fits,
                then_target: blocks[i].1,
                then_args: vec![],
                else_target: blocks.get(i + 1).map_or(miss, |b| b.0),
                else_args: vec![],
            });
            self.start_block(blocks[i].1, vec![]);
            for (position, binding) in case.prefix.iter().enumerate() {
                if let Some(var) = binding {
                    let index = self.slice_pattern_constant(position as u64);
                    let ptr = self.slice_pattern_address(data, index, stride);
                    self.set_local(*var, ptr, Ty::Ptr);
                }
            }
            for (position, binding) in case.suffix.iter().enumerate() {
                if let Some(var) = binding {
                    let distance = self.slice_pattern_constant(suffix - position as u64);
                    let index = self.fresh();
                    self.push_node(
                        InstrNode::new(Inst::BinOp {
                            op: BinOp::Sub,
                            ty: Ty::U64,
                            lhs: len,
                            rhs: distance,
                        })
                        .with_result(index),
                    );
                    let ptr = self.slice_pattern_address(data, index, stride);
                    self.set_local(*var, ptr, Ty::Ptr);
                }
            }
            if let Some(Some(var)) = case.rest {
                let first = self.slice_pattern_constant(prefix);
                let rest_data = self.slice_pattern_address(data, first, stride);
                let rest_len = self.fresh();
                self.push_node(
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Sub,
                        ty: Ty::U64,
                        lhs: len,
                        rhs: needed,
                    })
                    .with_result(rest_len),
                );
                let rest = self.fresh();
                self.push_node(
                    InstrNode::new(Inst::PtrFromParts {
                        ptr_ty: fat_ty.clone(),
                        metadata_ty: Ty::U64,
                        data: rest_data,
                        metadata: rest_len,
                    })
                    .with_result(rest),
                );
                // Keep the existing conservative borrow/escape boundary.
                self.borrow_ptrs.push(rest);
                self.set_local(var, rest, fat_ty.clone());
            }
            let value = self.lower_expr(case.body);
            captured.push(self.capture_arm(
                span,
                value_producing,
                value,
                "SliceMatch(case arm no value)",
                Some(&result_ty),
            ));
        }
        self.locals = before.clone();
        if let Some(body) = default {
            captured.push(self.lower_match_arm(
                span,
                value_producing,
                miss,
                body,
                "SliceMatch(default arm no value)",
                Some(&result_ty),
            ));
        } else {
            self.start_block(miss, vec![]);
            // SEAL(divergence): Rust's exhaustiveness check established the final miss is dead.
            self.seal_with(Inst::Unreachable);
        }
        if !captured.iter().any(CapturedArm::is_reaching) {
            self.locals = before;
            return None;
        }
        let refs: Vec<_> = captured.iter().collect();
        let merged = self.merged_locals(&before, &refs);
        let result = value_producing.then(|| self.fresh());
        if let Some(result) = result {
            if matches!(&result_ty, Ty::Ptr) {
                let incoming: Vec<_> = refs
                    .iter()
                    .filter_map(|arm| match arm {
                        CapturedArm::Reaching { result, .. } => *result,
                        CapturedArm::Diverged => None,
                    })
                    .collect();
                if let Err(reason) =
                    self.record_join_borrow_provenance(result, result_rty, &result_ty, &incoming)
                {
                    self.unsupported.push((format!("{span:?}"), reason));
                }
            }
        }
        let local_params = self.merged_local_params(span, &before, &merged, &refs);
        // Fat local joins have no provenance transfer yet. Reject their uses
        // even if an inner expression already erased its incoming borrow taint.
        // The existing deferred-use walk follows branch transport and permits
        // an overwritten/dead joined value without inventing read/escape facts.
        for ((_, ty), (joined, _)) in merged.iter().zip(&local_params) {
            if matches!(ty, Ty::FatPtr(_)) {
                self.deferred_join_refusals.push((
                    *joined,
                    span,
                    "SliceMatch(fat pointer local join)",
                ));
            }
        }
        for arm in captured {
            self.seal_arm_into_join(arm, join, result.is_some(), &before, &merged);
        }
        let mut params = Vec::new();
        if let Some(value) = result {
            params.push((value, result_ty));
        }
        params.extend(local_params.iter().cloned());
        self.locals = before;
        self.start_block(join, params);
        for ((var, ty), (value, _)) in merged.iter().zip(&local_params) {
            self.set_local(*var, *value, ty.clone());
        }
        result
    }

    fn slice_pattern_constant(&mut self, value: u64) -> ValueId {
        let id = self.fresh();
        self.push_node(
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(i128::from(value)) })
                .with_result(id),
        );
        id
    }

    fn slice_pattern_address(&mut self, data: ValueId, index: ValueId, stride: ValueId) -> ValueId {
        let offset = self.fresh();
        self.push_node(
            InstrNode::new(Inst::BinOp { op: BinOp::Mul, ty: Ty::U64, lhs: index, rhs: stride })
                .with_result(offset),
        );
        let ptr = self.fresh();
        self.push_node(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I8,
                base: data,
                indices: vec![offset],
                inbounds: true,
            })
            .with_result(ptr),
        );
        self.borrow_ptrs.push(ptr);
        ptr
    }
}
