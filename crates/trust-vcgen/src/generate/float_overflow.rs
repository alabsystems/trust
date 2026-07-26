// Float overflow obligations: whether a binary operation's result can leave
// the finite range, given the magnitude hypotheses in scope.

use super::*;

/// Test-facing compat shim for [`v2_float_binop_cannot_overflow_at`]: no
/// reading-block guard context, no summaries.
#[cfg(test)]
pub(super) fn v2_float_binop_cannot_overflow(
    func: &VerifiableFunction,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
) -> bool {
    v2_float_binop_cannot_overflow_at(func, None, None, op, lhs, rhs)
}

/// True when `a op b` (f64) provably CANNOT overflow to infinity, so its
/// `FloatOverflowToInfinity` VC is discharged. SOUND: gated entirely on the
/// conservative, fail-closed [`float_range`] interval tracer (NaN-tolerant
/// mode) — the RESULT interval of the op must sit inside
/// `±FLOAT_OVERFLOW_DISCHARGE_MARGIN`.
///
/// NaN case analysis (`FloatNanMode::NanOrBounded`: a clamp of a NaN self
/// passes NaN through, sin/cos of ±inf is NaN): a `Some` operand interval
/// admits NaN but never a FRESH ±inf. If ANY operand is NaN the IEEE result of
/// Mul/Add/Sub/Div is NaN — not an overflow TO INFINITY, so discharging stays
/// truthful (and matches the minted witness, which a NaN operand can never
/// satisfy). If no operand is NaN, the interval arithmetic bounds the result
/// below the margin.
///
/// Div: the result magnitude is bounded by `max(|numerator|) / m` where `m` is
/// a STRICTLY positive divisor magnitude floor (sign-definite interval, or a
/// one-sided dominating guard like `len > 1e-20` — see
/// `float_divisor_magnitude_floor`); fl-monotonicity makes the computed
/// quotient bound an upper bound on every IEEE quotient of in-range operands.
pub(super) fn v2_float_binop_cannot_overflow_at(
    func: &VerifiableFunction,
    block_id: Option<BlockId>,
    summaries: Option<&crate::modular::SummaryDatabase>,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
) -> bool {
    let ctx = FloatRangeCtx::new(func, summaries);
    let mode = FloatNanMode::NanOrBounded;
    let range = |operand: &Operand| {
        float_range(&ctx, mode, block_id, operand, &mut Vec::new(), FLOAT_EXP_BOUND_FUEL)
    };
    let within_margin = |(lo, hi): (f64, f64)| {
        lo.abs() <= FLOAT_OVERFLOW_DISCHARGE_MARGIN && hi.abs() <= FLOAT_OVERFLOW_DISCHARGE_MARGIN
    };
    match op {
        BinOp::Add | BinOp::Sub => {
            let (ra, rb) = (range(lhs), range(rhs));
            // One TINY operand alone suffices — see FLOAT_ADD_TINY_OPERAND_BOUND.
            let tiny = |r: &Option<(f64, f64)>| matches!(r, Some((lo, hi)) if lo.abs().max(hi.abs()) < FLOAT_ADD_TINY_OPERAND_BOUND);
            if tiny(&ra) || tiny(&rb) {
                return true;
            }
            match (ra, rb) {
                (Some(a), Some(b)) => float_interval_binop(op, a, b).is_some_and(within_margin),
                _ => false,
            }
        }
        BinOp::Mul => match (range(lhs), range(rhs)) {
            (Some(a), Some(b)) => float_interval_binop(op, a, b).is_some_and(within_margin),
            _ => false,
        },
        BinOp::Div => {
            let Some((lo, hi)) = range(lhs) else { return false };
            let magnitude = lo.abs().max(hi.abs());
            let Some(floor) = float_divisor_magnitude_floor(
                &ctx,
                mode,
                block_id,
                rhs,
                &mut Vec::new(),
                FLOAT_EXP_BOUND_FUEL,
            ) else {
                return false;
            };
            // `floor > 0` by the helper's contract; fl-monotone: every IEEE
            // quotient of in-range operands is `<= fl(magnitude / floor)`.
            let bound = magnitude / floor;
            bound.is_finite() && bound <= FLOAT_OVERFLOW_DISCHARGE_MARGIN
        }
        _ => false,
    }
}

pub(super) fn v2_build_float_overflow_vc(
    context: V2FloatOverflowContext<'_>,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
) -> Option<VerificationCondition> {
    // NB: owned — `operand_ty` is moved into `VcKind::FloatOverflowToInfinity { operand_ty }`
    // below (a stored obligation type). The operand is a float scalar, never the fat ADT.
    let operand_ty = crate::operand_ty(context.func, lhs)?;
    if !matches!(operand_ty, Ty::Float { .. }) {
        return None;
    }

    // COMPLETENESS (fuzzer-revealed, `fp_masked_index_safe`): float overflow to
    // infinity is NON-TRAPPING (IEEE-754: the result is `±inf`, a defined value),
    // and a float→int `as` cast is SATURATING (`inf as usize == usize::MAX`, no
    // panic). So when this float op's result is consumed ONLY by a float→int cast
    // (`(a + b) as usize`), the overflow is BENIGN for safety — it can never reach a
    // trap; the saturated integer is then bounds-checked by its own obligation
    // (e.g. the masked index `& 3`). Suppress the overflow obligation in exactly
    // that case so the safe `arr[((a+b) as usize) & 3]` proves. This does NOT regress
    // the round-9 numerical verification below: a float result used AS A FLOAT (any
    // use other than the single int cast) still emits the witness obligation.
    if let trust_types::Statement::Assign { place: dest, .. } =
        &context.block.stmts[context.stmt_index]
        && dest.projections.is_empty()
        && v2_float_result_only_feeds_int_cast(context.func, dest.local)
    {
        return None;
    }

    // soundness (round-9): do NOT model the violation as the program's own
    // range-check booleans. The former `v2_float_bound_guard_formula` preference
    // returned `Or([a_too_large, b_too_large])` — the SAME discriminants the
    // safe-path guard negates — so the VC was the tautology `(¬p ∧ ¬q) ∧ (p ∨ q)`,
    // UNSAT for every input, reporting the FloatOverflowToInfinity obligation
    // Proved regardless of whether the program's range check was correct (a
    // self-referential false-PROVE: a wrong/vacuous guard like `abs(a) > -1.0` was
    // still "proved" overflow-free). Always use the real semantic witness instead.
    // On a safe path whose float-ordering guards are unmodeled (round-8), the
    // operands are unconstrained, so the witness is satisfiable and the obligation
    // is reported Failed/Unknown — fail-closed, never falsely Proved.
    //
    // DISCHARGE: when the operands' values are PROVABLY bounded (a u64-ranged int->f64
    // cast, a `Duration::as_secs_f64`, a contract magnitude bound, a dominating float
    // guard, or interval compositions thereof) far enough below `f64::MAX` that
    // overflow is impossible, the witness is UNSAT by construction — emit no obligation.
    // Gated on the conservative, fail-closed `float_range` interval tracer, so an
    // unconstrained operand keeps its obligation (the round-8 fail-closed behaviour
    // above is preserved for everything else).
    if v2_float_binop_cannot_overflow_at(
        context.func,
        Some(context.block.id),
        context.summaries,
        op,
        lhs,
        rhs,
    ) {
        return None;
    }
    let formula = v2_float_overflow_witness_formula(context.func, op, lhs, rhs)?;
    // F7: conjoin the ENTRY-STABLE contract magnitude bounds on the operands
    // as pure-BV hypotheses, so the typed-CHC/PDR solver lane can discharge
    // the witness from a `#[requires]` bound (previously the witness carried
    // no contract content at all and could never be proved UNSAT by a
    // solver). Conjoining only ever shrinks the violation set by states the
    // gated contract already excludes — see
    // `v2_float_contract_magnitude_hypotheses` for the bit-level argument.
    let mut hypotheses = v2_float_contract_magnitude_hypotheses(context.func, lhs, rhs);
    let formula = if hypotheses.is_empty() {
        formula
    } else {
        hypotheses.push(formula);
        Formula::And(hypotheses)
    };

    Some(VerificationCondition {
        kind: VcKind::FloatOverflowToInfinity { op, operand_ty },
        function: context.func.name.clone().into(),
        location: context.span.clone(),
        formula: v2_formula_with_block_defs_before_stmt(
            context.func,
            context.block,
            context.stmt_index,
            formula,
        ),
        contract_metadata: None,
    })
}

/// F7 — pure-BV contract hypotheses for a float overflow witness: for each
/// f64 OPERAND place carrying an entry-stable, gated two-sided contract bound
/// (`contract_range`'s own discipline, reused verbatim — formal-parameter
/// base, `param_place_is_entry_stable`, both sides present in the gated
/// precondition set), emit
///
///   `BvULe( magnitude_bits(x), bits(C) )`   with `C = max(|l|, |u|)`
///
/// over the SAME bit-vector encoding the witness itself uses
/// (`v2_float_magnitude_bits` — the low `width-1` bits, sign stripped).
///
/// FAITHFULNESS (why the BV comparison is exactly the contract's semantic
/// content at bit level):
///   * For FINITE doubles, sign-stripped bit-pattern order IS numeric
///     magnitude order — the IEEE-754 encoding is exponent-then-mantissa
///     lexicographic, monotone in |x|. The witness machinery already relies on
///     this (its `MAX/2` / `sqrt(MAX)` / `1.0` thresholds are `to_bits()`
///     values compared with `BvULt` on the magnitude extract; see the witness
///     shape comments in `v2_float_overflow_witness_formula`).
///   * NaN: a TRUE contract comparison `l <= x && x <= u` implies `x` is
///     ORDERED (an IEEE comparison involving NaN is false — the same license
///     `contract_range` documents). And every NaN bit pattern has magnitude
///     bits (exponent all-ones, fraction nonzero) strictly ABOVE every finite
///     value's — in particular above `bits(C)` for finite `C` — as does ±inf
///     (exponent all-ones, fraction zero). So `BvULe(mag(x), bits(C))` holds
///     for exactly the values with `|x| <= C` finite, EXCLUDING every NaN and
///     infinity pattern: precisely what the true contract bound guarantees
///     (`|x| <= C`, ordered, finite), no more and no less.
///
/// SOUNDNESS of conjoining: the bound is read from the extraction-GATED
/// precondition set, so every caller carries the matching `Precondition`
/// PROVE obligation — on every execution reaching this op the hypothesis is
/// TRUE (entry-stability pins the operand to its entry value). Conjoining a
/// program-true fact onto the SAT-iff-violation witness removes only
/// non-program states: it can turn Unknown into Proved, never the reverse.
/// `C = max(|l|, |u|)` WEAKENS an asymmetric contract interval to a symmetric
/// magnitude bound — a weaker hypothesis is still implied by the contract,
/// so it stays sound (it merely proves less). Both endpoints are finite by
/// `contract_range`'s validation, hence so is `C`. Non-f64 widths are skipped
/// (the witness only mints 64-bit shapes today); a repeated operand place is
/// emitted once.
pub(super) fn v2_float_contract_magnitude_hypotheses(
    func: &VerifiableFunction,
    lhs: &Operand,
    rhs: &Operand,
) -> Vec<Formula> {
    let mut hypotheses = Vec::new();
    let mut seen: Vec<&Place> = Vec::new();
    for operand in [lhs, rhs] {
        let (Operand::Copy(place) | Operand::Move(place)) = operand else { continue };
        if seen.contains(&place) {
            continue;
        }
        seen.push(place);
        if !matches!(crate::operand_ty_cow(func, operand).as_deref(), Some(Ty::Float { width: 64 }))
        {
            continue;
        }
        // Direct param-rooted read (`self.0 * k` with `self` entry-stable), or —
        // the dominant real-MIR shape — a compiler TEMP holding a single stable
        // copy of one (`_3 = ((*_1).0); _5 = Mul(_3, _4)`): resolve the temp
        // through its stable unique def chain back to the underlying
        // parameter-rooted place and read the contract bound off THAT.
        // SOUNDNESS: `stable_unique_def_through_copies` demands every hop and
        // the terminus be single-def and never mutably borrowed, so the temp
        // provably HOLDS the value of the resolved place at its def; and
        // `contract_range` (unchanged) demands the resolved base be an
        // ENTRY-STABLE formal parameter, so that value is the entry value the
        // contract bounds. The hypothesis is still minted over the OPERAND's
        // own term (`operand_to_formula(func, operand)` below) — exactly the
        // term the witness formula uses — so no name substitution occurs.
        let range = contract_range(func, place).or_else(|| {
            if !place.projections.is_empty() {
                return None;
            }
            // Hop through single-def whole-local copies until the copied-FROM
            // place is parameter-rooted (`_3 = ((*_1).0)` or `_4 = _3`), then
            // read the contract off THAT place — `contract_range` re-checks
            // the param's entry stability and the raw-ptr aliasing rules.
            // (`stable_unique_def_through_copies` doesn't fit here: a formal
            // parameter has no defining rvalue, so its terminus never
            // surfaces the param place itself.)
            let mut cur = place.local;
            for _ in 0..8 {
                if !crate::place_source_is_stable(func, cur) {
                    return None;
                }
                match crate::unique_whole_local_def(func, cur)? {
                    Rvalue::Use(Operand::Copy(q) | Operand::Move(q)) => {
                        if (1..=func.body.arg_count).contains(&q.local) {
                            return contract_range(func, q);
                        }
                        if q.projections.is_empty() && q.local != cur {
                            cur = q.local;
                            continue;
                        }
                        return None;
                    }
                    _ => return None,
                }
            }
            None
        });
        let Some((l, u)) = range else { continue };
        let c = l.abs().max(u.abs());
        let width = 64u32;
        let mag_width = width - 1;
        let c_bits = (c.to_bits() & ((1u64 << mag_width) - 1)) as i128;
        hypotheses.push(Formula::BvULe(
            Box::new(v2_float_magnitude_bits(operand_to_formula(func, operand), width)),
            Box::new(Formula::BitVec { value: c_bits, width: mag_width }),
            mag_width,
        ));
    }
    hypotheses
}

pub(super) fn v2_float_overflow_witness_formula(
    func: &VerifiableFunction,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
) -> Option<Formula> {
    let width = match crate::operand_ty_cow(func, lhs)?.as_ref() {
        Ty::Float { width } => *width,
        _ => return None,
    };

    // Trust #soundness (witness direction): this formula is the VIOLATION shape
    // the solver tries to SATISFY — proving it UNSAT discharges the obligation.
    // It must therefore OVER-approximate the real violation set: every operand
    // pair whose op truly rounds to ±inf must satisfy the witness. An UNDER-
    // approximating witness is a false-proof channel — a hypothesis that merely
    // excludes the witness (e.g. a contract `|a| <= MAX/4` against a both-
    // operands-above-MAX/2 shape) proves UNSAT while `MAX/4 + MAX` still
    // overflows (round-11 audit; the previous shapes required BOTH operands
    // above the threshold, which real overflows do not). The sound direction
    // costs solver-lane completeness only: extra SAT states leave the
    // obligation unknown, and the interval tracer (`v2_float_binop_cannot_
    // overflow_at`) is the intended discharge lane.
    match (op, width) {
        // Add: overflow requires SAME-sign finite operands (opposite signs give
        // `|a + b| <= max(|a|, |b|) <= MAX`), and `|a + b| <= |a| + |b| <=
        // 2·max(|a|, |b|)`, so `|a + b| > MAX` forces `max(|a|, |b|) > MAX/2` —
        // AT LEAST ONE operand above MAX/2 (not both: `MAX/4 + MAX` overflows
        // with one small operand). Sub mirrors with OPPOSITE signs
        // (`a − b = a + (−b)`).
        (BinOp::Add | BinOp::Sub, 64) => {
            let lhs_value = operand_to_formula(func, lhs);
            let rhs_value = operand_to_formula(func, rhs);
            let sign_width = 1;
            let mag_width = width - sign_width;
            let exp_width = 11;
            let frac_width = 52;
            let threshold = Formula::BitVec {
                value: ((f64::MAX / 2.0).to_bits() & ((1u64 << 63) - 1)) as i128,
                width: mag_width,
            };
            let finite_exponent = Formula::BitVec { value: 0x7ff, width: exp_width };

            let sign_eq = Formula::Eq(
                Box::new(Formula::BvExtract {
                    inner: Box::new(lhs_value.clone()),
                    high: width - 1,
                    low: width - 1,
                }),
                Box::new(Formula::BvExtract {
                    inner: Box::new(rhs_value.clone()),
                    high: width - 1,
                    low: width - 1,
                }),
            );
            let sign_shape =
                if op == BinOp::Add { sign_eq } else { Formula::Not(Box::new(sign_eq)) };
            Some(Formula::And(vec![
                sign_shape,
                Formula::Or(vec![
                    Formula::BvULt(
                        Box::new(threshold.clone()),
                        Box::new(v2_float_magnitude_bits(lhs_value.clone(), width)),
                        mag_width,
                    ),
                    Formula::BvULt(
                        Box::new(threshold),
                        Box::new(v2_float_magnitude_bits(rhs_value.clone(), width)),
                        mag_width,
                    ),
                ]),
                Formula::BvULt(
                    Box::new(Formula::BvExtract {
                        inner: Box::new(lhs_value),
                        high: width - 2,
                        low: frac_width,
                    }),
                    Box::new(finite_exponent.clone()),
                    exp_width,
                ),
                Formula::BvULt(
                    Box::new(Formula::BvExtract {
                        inner: Box::new(rhs_value),
                        high: width - 2,
                        low: frac_width,
                    }),
                    Box::new(finite_exponent),
                    exp_width,
                ),
            ]))
        }
        // Mul: `|a · b| > MAX` forces `max(|a|, |b|) > sqrt(MAX)` — AT LEAST
        // ONE operand above sqrt(MAX) (not both: `2 · MAX` overflows with one
        // small operand).
        (BinOp::Mul, 64) => {
            let mag_width = width - 1;
            let threshold = Formula::BitVec {
                value: ((f64::MAX.sqrt()).to_bits() & ((1u64 << 63) - 1)) as i128,
                width: mag_width,
            };

            Some(Formula::Or(vec![
                Formula::BvULt(
                    Box::new(threshold.clone()),
                    Box::new(v2_float_magnitude_bits(operand_to_formula(func, lhs), width)),
                    mag_width,
                ),
                Formula::BvULt(
                    Box::new(threshold),
                    Box::new(v2_float_magnitude_bits(operand_to_formula(func, rhs), width)),
                    mag_width,
                ),
            ]))
        }
        // Div (honest L1 widening, float-residuals round): with a FINITE
        // numerator, `|a / b| > MAX` forces `|b| < |a| / MAX <= 1` — the
        // divisor magnitude below 1.0 is the one condition every real Div
        // overflow satisfies (a zero or subnormal divisor is inside the shape;
        // `2 / 5e-324 = inf` has a numerator far below any sqrt(MAX)-style
        // threshold, which is why no numerator-magnitude conjunct may appear).
        // `|b| >= 1` with finite `a` bounds the quotient by `|a| <= MAX` —
        // never an overflow — so the shape over-approximates exactly.
        (BinOp::Div, 64) => {
            let mag_width = width - 1;
            let exp_width = 11;
            let frac_width = 52;
            let mag_mask = (1u64 << 63) - 1;
            let divisor_threshold = Formula::BitVec {
                value: ((1.0f64).to_bits() & mag_mask) as i128,
                width: mag_width,
            };
            let finite_exponent = Formula::BitVec { value: 0x7ff, width: exp_width };
            let lhs_value = operand_to_formula(func, lhs);
            Some(Formula::And(vec![
                Formula::BvULt(
                    Box::new(v2_float_magnitude_bits(operand_to_formula(func, rhs), width)),
                    Box::new(divisor_threshold),
                    mag_width,
                ),
                Formula::BvULt(
                    Box::new(Formula::BvExtract {
                        inner: Box::new(lhs_value),
                        high: width - 2,
                        low: frac_width,
                    }),
                    Box::new(finite_exponent),
                    exp_width,
                ),
            ]))
        }
        _ => None,
    }
}
