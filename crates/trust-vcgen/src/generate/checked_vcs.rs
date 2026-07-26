// The remaining L0 obligation constructors: assert negation, bounds checks,
// signed division overflow, shift amounts, casts and negation.

use super::*;

pub(crate) fn v2_build_assert_overflow_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    target: BlockId,
    op: BinOp,
    cond: &Operand,
    expected: bool,
    span: &SourceSpan,
) -> Option<VerificationCondition> {
    if matches!(op, BinOp::Shl | BinOp::Shr) {
        let (lhs, rhs) = v2_find_block_binary_operands(block, op)
            .or_else(|| v2_find_target_binary_operands(func, target, op))?;
        return v2_build_shift_overflow_vc(func, block, op, lhs, rhs, span, None);
    }

    if matches!(op, BinOp::Div | BinOp::Rem) {
        let (lhs, rhs) = v2_find_block_binary_operands(block, op)
            .or_else(|| v2_find_target_binary_operands(func, target, op))?;
        return v2_build_signed_div_overflow_vc(func, block, op, lhs, rhs, span, None);
    }

    if let Some(vc) = v2_build_overflow_vc(func, block, op, span) {
        return Some(vc);
    }

    let (lhs, rhs) = v2_find_target_binary_operands(func, target, op)?;
    match op {
        BinOp::Shl | BinOp::Shr => {
            v2_build_shift_overflow_vc(func, block, op, lhs, rhs, span, None)
        }
        BinOp::Div | BinOp::Rem => {
            v2_build_signed_div_overflow_vc(func, block, op, lhs, rhs, span, None)
        }
        _ => {
            let lhs_ty = crate::operand_ty(func, lhs)?;
            let rhs_ty = crate::operand_ty(func, rhs)?;
            Some(VerificationCondition {
                kind: VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) },
                function: func.name.clone().into(),
                location: span.clone(),
                formula: v2_formula_with_block_defs(
                    func,
                    block,
                    v2_assert_failure_formula(func, cond, expected),
                ),
                contract_metadata: None,
            })
        }
    }
}

pub(super) fn v2_build_assert_negation_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    target: BlockId,
    cond: &Operand,
    expected: bool,
    span: &SourceSpan,
) -> Option<VerificationCondition> {
    let operand = v2_find_target_neg_operand(func, target)?;
    // NB: owned — `ty` is moved into `VcKind::NegationOverflow { ty }` below (a stored
    // obligation type), so the borrowed walk does not apply here. The negated operand is
    // a scalar int, never the fat recursive ADT, so no clone is saved anyway.
    let ty = crate::operand_ty(func, operand)?;
    if !ty.is_signed() {
        return None;
    }
    let width = ty.int_width()?;

    // signed-128 neg → BV: the canonical assert shape `_c = (x == INT_MIN); Assert
    // { OverflowNeg } on _c` (expected false) would carry the `INT_MIN = -2^127`
    // literal in the cond's block-def, which the native typed-CHC lane rejects on
    // the Int path (`parse_i64`). Emit the BV neg-overflow failure (`x == INT_MIN`)
    // directly on the negated operand, conjoining the BV-rendered block-defs of its
    // defining shift (so signed_min's `-(1i128 << (width-1))` proves). SOUND: an
    // unconstrained operand has no block-def → the failure stays SAT (refutable).
    if width >= 128 {
        if let Some(bv_formula) = v2_signed_bv_neg_overflow_formula(func, operand, width) {
            let mut terms = Vec::new();
            if let Operand::Copy(p) | Operand::Move(p) = operand
                && p.projections.is_empty()
            {
                let base = crate::place_to_var_name(func, p);
                let bv_name = format!("__trust_ovf_bv_neg_{base}");
                // The negate runs in the TARGET block; its operand's defining shift
                // is in this (source) block. Render over the whole source block.
                v2_collect_bv_shl_blockdef(
                    func,
                    block,
                    block.stmts.len(),
                    p.local,
                    &bv_name,
                    width,
                    &mut terms,
                );
            }
            let formula = if terms.is_empty() {
                bv_formula
            } else {
                terms.push(bv_formula);
                Formula::And(terms)
            };
            return Some(VerificationCondition {
                kind: VcKind::NegationOverflow { ty },
                function: func.name.clone().into(),
                location: span.clone(),
                formula,
                contract_metadata: None,
            });
        }
        // Symbolic operand: fall through to the Int cond path (sound; UNKNOWN on
        // the native lane, as before).
    }

    Some(VerificationCondition {
        kind: VcKind::NegationOverflow { ty },
        function: func.name.clone().into(),
        location: span.clone(),
        formula: v2_formula_with_block_defs(
            func,
            block,
            v2_assert_failure_formula(func, cond, expected),
        ),
        contract_metadata: None,
    })
}

/// Whether this block's `BoundsCheck` assert provably CANNOT fire: the assert
/// expects its condition TRUE, the condition is `Lt(index, len)`, and BOTH
/// operands resolve to compile-time constants with `index < len` (a literal
/// element access like `cols[0]` on `[Vec4; 4]`).
///
/// WHY suppress instead of emitting: the violation formula for two constants
/// is the constant-false `Ge(k, L)`. The native lane happily proves it UNSAT —
/// and then `trust_router::constant_folder::apply_vacuity_gate` strips the
/// proof's authority, because a constant-false violation skeleton is
/// indistinguishable from the legacy vacuous placeholder it exists to reject
/// (observed: every literal-index bounds obligation of a matrix crate proved
/// by PDR, then downgraded to "Proved without exact kernel/native proof
/// authority"). An obligation that provably cannot fire is not minted — the
/// same principle as `v2_build_float_overflow_vc` returning `None` and the
/// Div/Rem nonzero-constant skip.
///
/// SOUNDNESS of the constant resolution: each side must be an operand-level
/// integer constant, or a bare local EVERY def of which (Assign stmts AND call
/// destinations — a call-written local fails, unlike `index_local_const`'s
/// stmt-only scan) is the SAME non-negative constant or a `Len` of a place
/// whose type is a fixed-length array (the length is a type-level constant).
/// Differing defs, symbolic values, projections, or `expected == false` all
/// return false — the obligation is kept (fail-closed). A genuinely
/// out-of-range constant access (`k >= L`) is NOT suppressed: its violation is
/// constant-TRUE and must surface as the refutation it is.
pub(crate) fn v2_bounds_assert_const_index_in_range(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    cond: &Operand,
    expected: bool,
) -> bool {
    if !expected {
        return false;
    }
    let Some((BinOp::Lt, lhs, rhs)) = v2_find_condition_binary_operands(block, cond) else {
        return false;
    };
    match (v2_const_unsigned_operand_value(func, lhs), v2_const_unsigned_operand_value(func, rhs)) {
        (Some(index), Some(len)) => index < len,
        _ => false,
    }
}

/// Resolve an operand to a single compile-time non-negative integer value:
/// a constant operand, or a bare local whose EVERY def (Assign rvalues and
/// call destinations) yields the same value — a `Use` of an integer constant,
/// or a `Len` of a fixed-length-array place (its length is the type-level
/// constant). Any other def shape, a projected read, or disagreeing defs
/// return `None`.
pub(super) fn v2_const_unsigned_operand_value(func: &VerifiableFunction, op: &Operand) -> Option<u128> {
    if let Some(v) = operand_const_int(op) {
        return u128::try_from(v).ok();
    }
    let place = match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p,
        _ => return None,
    };
    let mut found: Option<u128> = None;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place: dest, rvalue, .. } => {
                    // A `&mut`/`&raw mut` borrow of the local opens a write
                    // channel the def scan cannot see (`*r = 9;` assigns
                    // through `r`, not this local) — poison, mirroring
                    // `float_whole_local_defs` (round-13).
                    if let Rvalue::Ref { mutable: true, place: borrowed }
                    | Rvalue::AddressOf(true, borrowed) = rvalue
                        && borrowed.local == place.local
                    {
                        return None;
                    }
                    if dest.local != place.local {
                        continue;
                    }
                    if !dest.projections.is_empty() {
                        return None;
                    }
                    let v = match rvalue {
                        Rvalue::Use(inner) => u128::try_from(operand_const_int(inner)?).ok()?,
                        Rvalue::Len(measured) => {
                            match crate::place_ty_cow(func, measured)?.as_ref() {
                                Ty::Array { len, .. } => u128::from(*len),
                                _ => return None,
                            }
                        }
                        _ => return None,
                    };
                    match found {
                        Some(prev) if prev != v => return None,
                        _ => found = Some(v),
                    }
                }
                Statement::SetDiscriminant { place: dest, .. }
                | Statement::Deinit { place: dest } => {
                    if dest.local == place.local {
                        return None;
                    }
                }
                _ => {}
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.local == place.local
        {
            return None;
        }
    }
    found
}

pub(super) fn v2_build_bounds_assert_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    target: BlockId,
    cond: &Operand,
    expected: bool,
    span: &SourceSpan,
) -> Option<VerificationCondition> {
    let kind = v2_infer_bounds_kind(func, target)?;
    let direct_formula = if let Some((BinOp::Lt, lhs, rhs)) =
        v2_find_condition_binary_operands(block, cond)
    {
        let lhs_f = operand_to_formula(func, lhs);
        let rhs_f = operand_to_formula(func, rhs);
        let violation = if crate::operand_ty_cow(func, lhs).as_deref().is_some_and(Ty::is_signed) {
            Formula::Or(vec![
                Formula::Lt(Box::new(lhs_f.clone()), Box::new(Formula::Int(0))),
                Formula::Ge(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
            ])
        } else {
            Formula::Ge(Box::new(lhs_f.clone()), Box::new(rhs_f.clone()))
        };
        v2_formula_with_block_defs(func, block, violation)
    } else {
        v2_formula_with_block_defs(func, block, v2_assert_failure_formula(func, cond, expected))
    };
    Some(VerificationCondition {
        kind,
        function: func.name.clone().into(),
        location: span.clone(),
        formula: direct_formula,
        contract_metadata: None,
    })
}

pub(super) fn v2_infer_bounds_kind(func: &VerifiableFunction, target: BlockId) -> Option<VcKind> {
    let block = func.body.blocks.get(target.0)?;
    for stmt in &block.stmts {
        let Statement::Assign { rvalue, .. } = stmt else {
            continue;
        };
        let indexed = match rvalue {
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                if v2_place_has_index(place) =>
            {
                place
            }
            _ => continue,
        };
        return Some(if v2_place_uses_slice(func, indexed) {
            VcKind::SliceBoundsCheck
        } else {
            VcKind::IndexOutOfBounds
        });
    }

    Some(VcKind::IndexOutOfBounds)
}

pub(super) fn v2_place_has_index(place: &trust_types::Place) -> bool {
    place.projections.iter().any(|proj| {
        matches!(
            proj,
            trust_types::Projection::Index(_)
                | trust_types::Projection::ConstantIndex { .. }
                | trust_types::Projection::Subslice { .. }
        )
    })
}

pub(super) fn v2_place_uses_slice(func: &VerifiableFunction, place: &trust_types::Place) -> bool {
    let Some(mut ty) = func.body.locals.get(place.local).map(|decl| decl.ty.clone()) else {
        return false;
    };

    for proj in &place.projections {
        match (proj, &ty) {
            (trust_types::Projection::Deref, Ty::Ref { inner, .. }) => ty = *inner.clone(),
            (trust_types::Projection::Deref, Ty::RawPtr { pointee, .. }) => ty = *pointee.clone(),
            (trust_types::Projection::Subslice { .. }, _) => return true,
            (
                trust_types::Projection::Index(_) | trust_types::Projection::ConstantIndex { .. },
                Ty::Slice { .. },
            ) => return true,
            (
                trust_types::Projection::Index(_) | trust_types::Projection::ConstantIndex { .. },
                Ty::Array { .. },
            ) => return false,
            (trust_types::Projection::Field(index), Ty::Tuple(fields)) => {
                ty = fields.get(*index).cloned().unwrap_or(Ty::Unit)
            }
            (trust_types::Projection::Field(index), Ty::Adt { fields, .. }) => {
                ty = fields.get(*index).map(|(_, field_ty)| field_ty.clone()).unwrap_or(Ty::Unit)
            }
            _ => {}
        }
    }

    false
}

pub(super) fn v2_build_signed_div_overflow_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    span: &SourceSpan,
    stmt_index: Option<usize>,
) -> Option<VerificationCondition> {
    let lhs_ty = crate::operand_ty(func, lhs)?;
    let rhs_ty = crate::operand_ty(func, rhs)?;
    if !lhs_ty.is_signed() || !rhs_ty.is_signed() {
        return None;
    }

    // Recover the true width from a non-constant operand — a signed constant
    // lhs (`(-128i8) / y`) loses its width, so deriving INT_MIN from it would
    // use i64::MIN and miss the i8 INT_MIN / -1 overflow (round-19).
    let (width, _) = int_op_type(func, lhs, rhs)?;
    let lhs_f = operand_to_formula(func, lhs);
    let rhs_f = operand_to_formula(func, rhs);
    let lhs_range = crate::range::input_range_constraint(&lhs_f, width, true);
    let rhs_range = crate::range::input_range_constraint(&rhs_f, rhs_ty.int_width()?, true);
    let int_min = crate::range::type_min_formula(width, true);
    let formula = v2_formula_with_block_defs_at(
        func,
        block,
        stmt_index,
        Formula::And(vec![
            lhs_range,
            rhs_range,
            Formula::Eq(Box::new(lhs_f), Box::new(int_min)),
            Formula::Eq(Box::new(rhs_f), Box::new(Formula::Int(-1))),
        ]),
    );

    Some(VerificationCondition {
        kind: VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) },
        function: func.name.clone().into(),
        location: span.clone(),
        formula,
        contract_metadata: None,
    })
}

/// Width of a shift's RESULT type, read from the assignment DESTINATION at
/// `stmt_index`. Recovers the shifted-value width when the shifted value is a
/// width-less signed constant (`1i32 << n`); returns None when the statement is
/// not a whole-local integer assignment. Trust #soundness (round-19).
pub(super) fn v2_shift_dest_width(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    stmt_index: Option<usize>,
) -> Option<u32> {
    let stmt = block.stmts.get(stmt_index?)?;
    let Statement::Assign { place, .. } = stmt else { return None };
    if !place.projections.is_empty() {
        return None;
    }
    func.body.locals.get(place.local)?.ty.int_width()
}

/// Structural equality on two operands, enough to recognize the SAME shift
/// statement by its operands. `trust_types::Operand` derives no `PartialEq` (it
/// carries a `Formula` lifting variant), so this compares the variants that a
/// shift's operands take: a plain/projected local (`Place: Eq`) or an integer
/// constant. Constants compare by their carried value+width; other constant
/// kinds (and the lifted-`Formula` operand) conservatively return `false`, which
/// only widens the by-operands width search to the type fallback — never a false
/// match onto an unrelated shift.
pub(super) fn v2_operands_structurally_equal(a: &Operand, b: &Operand) -> bool {
    match (a, b) {
        (Operand::Copy(pa), Operand::Copy(pb)) | (Operand::Move(pa), Operand::Move(pb)) => pa == pb,
        (Operand::Constant(ca), Operand::Constant(cb)) => match (ca, cb) {
            (ConstValue::Int(x), ConstValue::Int(y)) => x == y,
            (ConstValue::Uint(x, wx), ConstValue::Uint(y, wy)) => x == y && wx == wy,
            (ConstValue::Bool(x), ConstValue::Bool(y)) => x == y,
            _ => false,
        },
        _ => false,
    }
}

/// Width of the SHIFT-RESULT type, recovered from the destination of the
/// `op` (`Shl`/`Shr`) statement whose operands are exactly `(lhs, rhs)`, scanning
/// the whole function. This recovers the shifted-value width when the shifted
/// value is a width-less constant (`1i128 << k`, where `operand_ty` fabricates an
/// `i64`) AND the VC is built from the ASSERT terminator — in which case the
/// caller passes the assert block (not the shift block) and `stmt_index = None`,
/// so [`v2_shift_dest_width`] cannot read the dest. Without this, `1i128 << k` is
/// checked against width 64 instead of 128, false-FAILing a provably-safe shift
/// (e.g. `signed_max`'s `width <= 127`-guarded `1i128 << (width-1)`).
///
/// SOUNDNESS: the destination of `dst = Shl(lhs, rhs)` has exactly the shift's
/// result type, so its width is the EXACT bit width the `amount >= width` UB
/// check must use — not an over-estimate (which could hide a real
/// `64 <= n < 128` UB shift) nor an under-estimate (a false-FAIL). The match is
/// keyed on operand equality and the `Shl`/`Shr` opcode, so it locates this
/// shift's own destination; a function with multiple distinct shifts resolves
/// each by its own operands.
pub(super) fn v2_shift_result_width_by_operands(
    func: &VerifiableFunction,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
) -> Option<u32> {
    // Soundness: take the MINIMUM result width across all operand-matching shifts,
    // not the first. A width-less constant shifted value (`ConstValue::Int(1)`,
    // which `v2_operands_structurally_equal` treats as equal for any signedness/
    // width) means `1i64 << k` and `1i128 << k` with the same `k` match each other;
    // returning the first could hand back the LARGER width (128) for the smaller
    // (i64) shift — an OVER-estimate that would loosen the `amount >= width` UB
    // bound and could hide a real `64 <= n < 128` UB shift (a false-PROVE). The
    // minimum is a safe under-estimate (tighter bound → false-FAIL at worst, never
    // false-PROVE); for the common single-match case it IS the exact result width.
    let mut min_width: Option<u32> = None;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place, rvalue, .. } = stmt else {
                continue;
            };
            if !place.projections.is_empty() {
                continue;
            }
            let (stmt_op, stmt_lhs, stmt_rhs) = match rvalue {
                Rvalue::BinaryOp(stmt_op, l, r) | Rvalue::CheckedBinaryOp(stmt_op, l, r) => {
                    (*stmt_op, l, r)
                }
                _ => continue,
            };
            if stmt_op == op
                && v2_operands_structurally_equal(stmt_lhs, lhs)
                && v2_operands_structurally_equal(stmt_rhs, rhs)
                && let Some(width) =
                    func.body.locals.get(place.local).and_then(|d| d.ty.int_width())
            {
                min_width = Some(min_width.map_or(width, |m| m.min(width)));
            }
        }
    }
    min_width
}

/// The shift no-overflow VIOLATION formula — `shift_range AND invalid_shift`
/// (i.e. the amount is within its own type range yet `amount >= width`, the actual
/// shift UB) — UNWRAPPED (no block-defs). Both the per-statement shift VC and the
/// hardened MIR-assert shift twin build from this so the two lanes carry an
/// IDENTICAL, lowerable shift condition. Returns the violation plus the recovered
/// (operand_ty, shift_ty) for the VC kind.
pub(super) fn v2_shift_violation_formula(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    stmt_index: Option<usize>,
) -> Option<(Formula, Ty, Ty)> {
    let operand_ty = crate::operand_ty(func, lhs)?;
    let shift_ty = crate::operand_ty(func, rhs)?;
    // Trust #soundness (round-19): the shifted-value width drives the
    // `amount >= width` UB check. A SIGNED constant shifted value (`1i32 << n`)
    // loses its width at extraction (operand_ty fabricates i64), so the check
    // would become `n >= 64` and miss a real `32 <= n < 64` UB shift. Unlike
    // arithmetic, the shift operands have DIFFERENT types (value vs amount), so
    // recover the value width from the assignment DESTINATION's type (the shift
    // result type) when the shifted value is a constant.
    //
    // The per-statement path supplies (block, stmt_index) of the shift itself, so
    // `v2_shift_dest_width` reads the dest directly. The ASSERT-driven path
    // (`v2_build_assert_overflow_vc` / `v2_assert_shift_violation_formula`) instead
    // passes the ASSERT block and `stmt_index = None` (the shift lives in the
    // assert's TARGET block), so the direct read fails and we fall back to locating
    // the shift's destination by its operands across the function — recovering the
    // true 128-bit width of `1i128 << k` instead of the fabricated i64 width that
    // false-FAILed a provably-safe `width <= 127`-guarded shift
    // (`signed_max`/`signed_min`).
    let shifted_width = if matches!(lhs, Operand::Constant(_)) {
        v2_shift_dest_width(func, block, stmt_index)
            .or_else(|| v2_shift_result_width_by_operands(func, op, lhs, rhs))
            .or_else(|| operand_ty.int_width())
    } else {
        operand_ty.int_width()
    }?;
    let bit_width = i128::from(shifted_width);
    let shift_f = operand_to_formula(func, rhs);
    let shift_range = if let Some(width) = shift_ty.int_width() {
        crate::range::input_range_constraint(&shift_f, width, shift_ty.is_signed())
    } else {
        Formula::Bool(true)
    };

    let invalid_shift = if shift_ty.is_signed() {
        Formula::Or(vec![
            Formula::Lt(Box::new(shift_f.clone()), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(shift_f), Box::new(Formula::Int(bit_width))),
        ])
    } else {
        Formula::Ge(Box::new(shift_f), Box::new(Formula::Int(bit_width)))
    };

    Some((Formula::And(vec![shift_range, invalid_shift]), operand_ty, shift_ty))
}

/// Assert-driven UNWRAPPED shift-overflow violation, for the hardened MIR-assert
/// boundary lane. Recovers the shift operands from the `Overflow(Shl|Shr)` assert
/// (the shift lives in this block or the assert's target block) and returns the
/// SAME `shift_range AND invalid_shift` violation the per-statement VC proves —
/// but unwrapped, so the hardened lane can conjoin its OWN block-defs / dominating
/// guards / preconditions with consistent versioning. This replaces the generic
/// `extract_assert_passed_semantics` operand-range encoding for shifts, which the
/// native typed-CHC lane cannot lower (it left `octree_node_count`'s `1u64 << exp`
/// hardened twin without publishable proof evidence — the 84/85 miss). Returns
/// `None` for non-shift ops or when the operands can't be recovered.
pub(crate) fn v2_assert_shift_violation_formula(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    target: BlockId,
    op: BinOp,
) -> Option<Formula> {
    // Scope: ONLY a left shift by a NON-CONSTANT amount needs this. That is the
    // single case the generic `extract_assert_passed_semantics` encoding cannot
    // lower — the result of `value << amount` is `value * 2^amount`, NON-LINEAR in
    // a variable `amount`, so the native typed-CHC lane reports it UNSUPPORTED (the
    // a3d-kernel `octree_node_count` `1u64 << exp` miss). Every other shift the
    // generic path already proves with publishable native evidence and MUST be left
    // alone: a right shift `value >> amount` is `value / 2^amount` (its overflow
    // assert constrains only the amount), and a CONSTANT-amount shift has a linear,
    // lowerable result. Over-applying the violation to those regressed them to
    // UNSUPPORTED. The shifted VALUE may be constant or variable — only the AMOUNT
    // being non-constant matters.
    if op != BinOp::Shl {
        return None;
    }
    let (lhs, rhs) = v2_find_block_binary_operands(block, op)
        .or_else(|| v2_find_target_binary_operands(func, target, op))?;
    if matches!(rhs, Operand::Constant(_)) {
        return None;
    }
    let (violation, _operand_ty, _shift_ty) =
        v2_shift_violation_formula(func, block, op, lhs, rhs, None)?;
    Some(violation)
}

pub(super) fn v2_build_shift_overflow_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    span: &SourceSpan,
    stmt_index: Option<usize>,
) -> Option<VerificationCondition> {
    let (violation, operand_ty, shift_ty) =
        v2_shift_violation_formula(func, block, op, lhs, rhs, stmt_index)?;
    Some(VerificationCondition {
        kind: VcKind::ShiftOverflow { op, operand_ty, shift_ty },
        function: func.name.clone().into(),
        location: span.clone(),
        formula: v2_formula_with_block_defs_at(func, block, stmt_index, violation),
        contract_metadata: None,
    })
}

pub(super) fn v2_build_cast_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    operand: &Operand,
    to_ty: &Ty,
    span: &SourceSpan,
    stmt_index: usize,
) -> Option<VerificationCondition> {
    let from_ty = match crate::operand_ty(func, operand) {
        Some(ty) => ty,
        None => {
            return Some(v2_unsupported_cast_vc(
                func,
                block,
                None,
                to_ty,
                span,
                stmt_index,
                "source operand type is unavailable",
            ));
        }
    };

    if matches!(&from_ty, Ty::Bool) && to_ty.is_integer() {
        return None;
    }

    if crate::is_thin_pointer_identity_cast(&from_ty, to_ty)
        || crate::is_fn_pointer_identity_cast(&from_ty, to_ty)
        || crate::is_callable_reification_cast(&from_ty, to_ty)
        // `&[T; N] -> &[T]` unsize is a metadata-only coercion (slice len is the
        // array's static N); it carries no arithmetic/bounds obligation, so it is
        // modeled with no VC, mirroring the primary cast-relation gate.
        || crate::is_array_to_slice_ref_cast(&from_ty, to_ty)
    {
        return None;
    }

    // float `as` casts are infallible (no overflow/panic obligation); the value
    // is modeled as unconstrained elsewhere, so emit no cast-range VC here.
    if crate::is_float_numeric_cast(&from_ty, to_ty) {
        return None;
    }

    // A pointer→integer cast (the `*const _ -> usize` address-exposure leg of the
    // `vec!`/box-machinery alignment & null checks) is INFALLIBLE: exposing a
    // pointer's address yields a defined integer (`usize` is pointer-width — no
    // truncation panic, and pointer-to-smaller-int truncation is itself defined, not
    // UB), so it carries NO `CastOverflow`/safety obligation. The dest is left
    // UNCONSTRAINED (no value-fact), so any derived null/alignment assert stays
    // soundly caught and nothing is falsely proved. Mirrors the primary cast-relation
    // gate (`collect_cast_relation_unsupported`); without it this one cast poisoned
    // the whole function's obligations (its address-exposure stayed UnsupportedMir).
    if from_ty.is_pointer_like() && to_ty.is_integer() {
        return None;
    }

    if !from_ty.is_integer() || !to_ty.is_integer() {
        return Some(v2_unsupported_cast_vc(
            func,
            block,
            Some(&from_ty),
            to_ty,
            span,
            stmt_index,
            &crate::unsupported_cast_reason(&from_ty, to_ty),
        ));
    }

    // A value-preserving WIDENING cast can never overflow its target, so it
    // needs no CastOverflow obligation. Check this BEFORE demanding an
    // target-range representation: a 128-bit *unsigned* target (`u128`) has a
    // maximum (`u128::MAX`) that does not fit an `i128`, yet a widening such as
    // `u32 as u128` is exactly representable and provably non-overflowing. The
    // `dest == source` value fact and the source-width range bound for the
    // casted local are already emitted by `guards::cast_definition_formula` /
    // `guards::widening_cast_result_range` (both handle 128-bit widths), so the
    // widened value stays constrained for downstream arithmetic.
    //
    // Soundness: returns `None` (drops the obligation) ONLY for a
    // value-preserving widening — the result unconditionally lies inside the
    // target range, so the CastOverflow VC would be vacuously safe. Narrowing,
    // same-width signedness reinterpret, and signed->unsigned casts are NOT
    // value-preserving and fall through to the modeled / fail-closed paths
    // below (still UNKNOWN for an unrepresentable 128-bit target).
    if v2_is_value_preserving_widening(&from_ty, to_ty) {
        return None;
    }

    // A FLOAT→INT `as` cast is SATURATING (Rust 1.45+): an out-of-range magnitude
    // clamps to the target's MIN/MAX and NaN maps to 0 — it NEVER traps. So it
    // carries no CastOverflow safety obligation. (The numerical result may be
    // imprecise / saturated, but that is not a memory-safety concern; a downstream
    // out-of-bounds index built from the result is caught by its OWN bounds
    // obligation.) Without this, a float source falls through to the `int_width()`
    // failure below and emits a fail-closed `[cast] UNKNOWN` that no backend can
    // decide — leaving e.g. `arr[((a + b) as usize) & 3]` not fully proved.
    if matches!(from_ty, Ty::Float { .. }) && matches!(to_ty, Ty::Int { .. }) {
        return None;
    }

    // Trust (drop-in, owner decision 2026-07-06): a plain integer→integer `as`
    // cast is DEFINED behavior in Rust — it truncates / sign-extends / reinterprets
    // the bit pattern and NEVER traps or is UB (unlike arithmetic overflow). It is
    // therefore NOT "unsafe behavior" within pillar 1's scope (overflow, bounds,
    // panics, UB, ownership), so Trust does NOT restrict the programmer by rejecting
    // it. We do the work on our side instead: the cast RESULT is TYPE-TRACKED as a
    // value of its NEW type (`guards::narrowing_cast_result_range` emits the
    // target-type range `type_min(to_ty) <= dest <= type_max(to_ty)`), so downstream
    // bounds / overflow obligations reason about the wrapped value soundly — a
    // genuinely out-of-range index built FROM a cast result is still CAUGHT by its
    // own bounds VC, and `(x as u8) as u32 + 1` proves (result <= 255).
    //
    // Previously this emitted a `CastOverflow` obligation asserting the source value
    // FIT the target — a LOSSLESSNESS property Rust does not require — which
    // false-refuted every truncating / signedness-reinterpreting cast (`x as u8`,
    // `i32 as u32`) and broke drop-in. Both `from_ty` and `to_ty` are integers here
    // (non-integer casts returned above), so no obligation is warranted.
    let _ = (operand, block, stmt_index);
    None
}

pub(super) fn v2_unsupported_cast_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    from_ty: Option<&Ty>,
    to_ty: &Ty,
    span: &SourceSpan,
    stmt_index: usize,
    reason: &str,
) -> VerificationCondition {
    let from_ty = from_ty.map_or_else(|| "<unknown>".to_string(), |ty| format!("{ty:?}"));
    unsupported_mir_vc(
        func,
        "Rvalue::Cast".to_string(),
        format!(
            "bb{} stmt {stmt_index}: unsupported cast {from_ty} -> {to_ty:?}: {reason}",
            block.id.0
        ),
        span.clone(),
    )
}

/// Whether `from_ty as to_ty` is a value-preserving WIDENING integer cast — one
/// that cannot change the mathematical value for ANY input, so its result is
/// unconditionally contained in the target's range and needs no CastOverflow
/// obligation. This mirrors [`crate::is_modeled_identity_cast`]'s widening rule
/// but excludes the same-width no-op (that is value-preserving but not a
/// *widening*, and a same-width cast already has representable bounds, so it
/// flows through the normal containment check at no precision loss).
///
/// A widening (`tw > fw`) preserves the value iff it is not signed->unsigned:
///   * unsigned source, any wider target: `0..=2^fw-1` ⊆ target (zero-extend);
///   * signed source, wider *signed* target: `-2^(fw-1)..=2^(fw-1)-1` ⊆ target;
///   * signed source -> unsigned target: a negative source wraps to a huge
///     unsigned value (value-CHANGING), so it is NOT value-preserving — excluded.
///
/// Crucially this is decided purely from widths/signedness, so it is correct
/// even when the target is 128-bit and its bound is not `i128`-representable.
pub(super) fn v2_is_value_preserving_widening(from_ty: &Ty, to_ty: &Ty) -> bool {
    let (Ty::Int { width: fw, signed: fs }, Ty::Int { width: tw, signed: ts }) = (from_ty, to_ty)
    else {
        return false;
    };
    *tw > *fw && !(*fs && !*ts)
}

pub(super) fn v2_build_negation_raw_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    operand: &Operand,
    span: &SourceSpan,
    stmt_index: usize,
) -> Option<VerificationCondition> {
    // NB: owned — `ty` is moved into `VcKind::NegationOverflow { ty }` below (a stored
    // obligation type). The negated operand is a scalar int, never the fat recursive ADT.
    let ty = crate::operand_ty(func, operand)?;
    if !ty.is_signed() {
        return None;
    }
    let width = ty.int_width()?;

    // signed-128 neg → BV: the native typed-CHC lane cannot represent the `INT_MIN
    // = -2^127` literal on the Int path (`parse_i64` rejects it). Emit the BV
    // neg-overflow failure (`x == INT_MIN`) and conjoin the BV-rendered block-defs
    // on the operand local (so signed_min's `-(1i128 << (width-1))` proves: the
    // defining shift makes `_5` a power of two in `[1, 2^(width-1)]`, never INT_MIN).
    // SOUND: an unconstrained operand carries no block-def, so `x == INT_MIN` stays
    // SAT (refutable). See the add/sub routing note.
    if width >= 128 {
        if let Some(bv_formula) = v2_signed_bv_neg_overflow_formula(func, operand, width) {
            // The neg operand uses BV var role "neg"; render its defining shift.
            let mut terms = Vec::new();
            if let Operand::Copy(p) | Operand::Move(p) = operand
                && p.projections.is_empty()
            {
                let base = crate::place_to_var_name(func, p);
                let bv_name = format!("__trust_ovf_bv_neg_{base}");
                v2_collect_bv_shl_blockdef(
                    func, block, stmt_index, p.local, &bv_name, width, &mut terms,
                );
            }
            let formula = if terms.is_empty() {
                bv_formula
            } else {
                terms.push(bv_formula);
                Formula::And(terms)
            };
            return Some(VerificationCondition {
                kind: VcKind::NegationOverflow { ty },
                function: func.name.clone().into(),
                location: span.clone(),
                formula,
                contract_metadata: None,
            });
        }
        // Symbolic operand: fall through to the Int path (sound; stays UNKNOWN on
        // the native lane, exactly as before).
    }

    let value = operand_to_formula(func, operand);
    let int_min = crate::range::type_min_formula(width, true);
    let formula = Formula::And(vec![
        crate::range::input_range_constraint(&value, width, true),
        Formula::Eq(Box::new(value), Box::new(int_min)),
    ]);

    Some(VerificationCondition {
        kind: VcKind::NegationOverflow { ty },
        function: func.name.clone().into(),
        location: span.clone(),
        formula: v2_formula_with_block_defs_before_stmt(func, block, stmt_index, formula),
        contract_metadata: None,
    })
}
