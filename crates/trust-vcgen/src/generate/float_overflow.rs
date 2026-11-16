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

/// True when `a op b` provably CANNOT overflow to infinity, so its
/// `FloatOverflowToInfinity` VC is discharged. SOUND: gated entirely on the
/// conservative, fail-closed [`float_range`] interval tracer (NaN-tolerant
/// mode) — the RESULT interval of the op must sit inside the discharge margin
/// FOR THIS OPERATION'S IEEE WIDTH.
///
/// WIDTH (Trust 2026-09-17): the thresholds are `MAX`-relative, so they are
/// read from [`float_overflow_discharge_margin`] and
/// [`float_add_tiny_operand_bound`] per width, never as f64 constants. Using
/// the f64 figures for a binary32 op is a FALSE PROOF — `2^1020` is
/// astronomically above `f32::MAX ~ 2^128`, so two f32 operands near `3e38`
/// read as "tiny" and their sum is infinity. An unmodelled width discharges
/// NOTHING.
///
/// The tracer stores intervals in `f64`, but each intermediate arithmetic
/// result is enclosed at its own IEEE width before that interval is propagated.
/// Widening an f32 value is exact; evaluating its arithmetic at f64 precision
/// alone does not enclose the rounded f32 result.
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
    // Both operands must describe the same supported IEEE operation.
    let Some(width) = v2_float_binop_width(func, lhs, rhs) else { return false };
    let (Some(margin), Some(tiny_bound)) =
        (float_overflow_discharge_margin(width), float_add_tiny_operand_bound(width))
    else {
        return false;
    };

    let ctx = FloatRangeCtx::new(func, summaries);
    let mode = FloatNanMode::NanOrBounded;
    let range = |operand: &Operand| {
        float_range(&ctx, mode, block_id, operand, &mut Vec::new(), FLOAT_EXP_BOUND_FUEL)
    };
    let within_margin = |(lo, hi): (f64, f64)| lo.abs() <= margin && hi.abs() <= margin;
    match op {
        BinOp::Add | BinOp::Sub => {
            // One TINY operand alone suffices — see `float_add_tiny_operand_bound`.
            // The `<` is STRICT and load-bearing: the bound is exactly
            // `ulp(MAX) / 2`, the round-to-infinity boundary, so an operand AT
            // the bound added to `MAX` ties and rounds AWAY to infinity.
            let tiny = |r: &Option<(f64, f64)>| matches!(r, Some((lo, hi)) if lo.abs().max(hi.abs()) < tiny_bound);
            if matches!(rhs, Operand::Constant(_)) && !matches!(lhs, Operand::Constant(_)) {
                let rb = range(rhs);
                if tiny(&rb) {
                    return true;
                }
                let ra = range(lhs);
                if tiny(&ra) {
                    return true;
                }
                match (ra, rb) {
                    (Some(a), Some(b)) => float_interval_binop(op, a, b).is_some_and(within_margin),
                    _ => false,
                }
            } else {
                let ra = range(lhs);
                if tiny(&ra) {
                    return true;
                }
                let rb = range(rhs);
                if tiny(&rb) {
                    return true;
                }
                match (ra, rb) {
                    (Some(a), Some(b)) => float_interval_binop(op, a, b).is_some_and(within_margin),
                    _ => false,
                }
            }
        }
        BinOp::Mul => {
            let Some(a) = range(lhs) else { return false };
            let Some(b) = range(rhs) else { return false };
            float_interval_binop(op, a, b).is_some_and(within_margin)
        }
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
            bound.is_finite() && bound <= margin
        }
        _ => false,
    }
}

/// The IEEE bit pattern of the width's tiny-addend bound (`float_add_tiny_operand_bound`),
/// encoded AT that width: `None` for an unmodelled width or a bound that does not narrow
/// exactly (both bounds are powers of two, so they do).
fn float_tiny_operand_bound_bits(width: u32) -> Option<u128> {
    let bound = float_add_tiny_operand_bound(width)?;
    match width {
        64 => Some(u128::from(bound.to_bits())),
        32 => {
            let narrow = bound as f32;
            (f64::from(narrow) == bound).then(|| u128::from(narrow.to_bits()))
        }
        _ => None,
    }
}

/// Trust (2026-10-17, gate RCA precision T7): `a op b` is an `Add`/`Sub` one of whose
/// operands is a float CONSTANT strictly below the width's tiny-addend bound `T` — the
/// case where the interval discharge's tiny-operand rule holds on a ground operand, so
/// [`float_add_tiny_operand_conjuncts`] carry a conjunct that is false on a ground term.
///
/// [`v2_build_float_overflow_vc`] keeps such a row (witness and those conjuncts) even when
/// the interval discharge holds. Since f559970230 (2026-09-17) the tracer reads binary32
/// literals, so `self.quiet + 4.0` (f32) is discharged, and a discharge emits NO
/// obligation: the two `float_overflow_to_infinity` rows of aterm-effects
/// `kitty_pet.rs:7601/7609`, which the seal (321aaeda75) published PROVED
/// (kernel-certified), vanished from the report (MISSING on the candidate gate of
/// 2026-10-16). A discharge whose argument the row can state itself is a proof, so the
/// row is reported, and proves.
///
/// BINARY32 ONLY (2026-10-18, revised from "every width"). The row is kept exactly where
/// the published seal kept it: before f559970230 the tracer read no binary32 literal, so
/// the seal emitted (and proved) the binary32 row, while its binary64 discharge already
/// dropped `x + 0.05` (aterm-types `lighter + 0.05`). Emitting the binary64 row too
/// changed the row inventory of bodies the seal reported, and a body whose only
/// obligation was such an add lost the seal's `no_obligations` row (an identity the next
/// gate, against the same seal, would read MISSING). Either answer is sound: the row
/// proves, and the discharge it replaces is the same argument.
fn float_add_witness_refutes_by_constant(
    func: &VerifiableFunction,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
) -> bool {
    if !matches!(op, BinOp::Add | BinOp::Sub) {
        return false;
    }
    let Some(width) = v2_float_binop_width(func, lhs, rhs) else { return false };
    if width != 32 {
        return false;
    }
    let Some(tiny) = float_add_tiny_operand_bound(width) else { return false };
    [lhs, rhs].into_iter().any(|operand| match operand {
        Operand::Constant(c) => {
            super::float_range::f64_const_value(c).is_some_and(|v| v.is_finite() && v.abs() < tiny)
        }
        _ => false,
    })
}

/// Trust (2026-10-17, gate RCA precision T7): `T <= |a|` and `T <= |b|` for an `Add`/`Sub`
/// at a modelled width, `T = ulp(MAX) / 2` the width's tiny-addend bound
/// (`float_add_tiny_operand_bound`: 2^103 binary32, 2^970 binary64), compared as IEEE
/// magnitude bits at the operation's width, the encoding the witness itself uses
/// (`v2_float_magnitude_bits`; sign-stripped bit order is magnitude order).
///
/// SOUNDNESS: every real overflow satisfies both. With `|b| < T` and `a` finite, the
/// exact sum (difference, for opposite signs) has magnitude `<= |a| + |b| < MAX +
/// ulp(MAX) / 2`, strictly below the round-to-nearest-even boundary to infinity, so it
/// rounds to at most `MAX`: no overflow; symmetrically for `|a| < T`. Conjoined onto the
/// witness they therefore keep it an over-approximation of the violation set. This is
/// the argument the interval discharge's tiny-operand rule already makes
/// (`v2_float_binop_cannot_overflow_at`), stated in the obligation. They are conjoined
/// ONLY onto the row [`float_add_witness_refutes_by_constant`] keeps; every other float
/// row's formula is unchanged.
fn float_add_tiny_operand_conjuncts(
    func: &VerifiableFunction,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
) -> Option<Vec<Formula>> {
    if !matches!(op, BinOp::Add | BinOp::Sub) {
        return None;
    }
    let width = match crate::operand_ty_cow(func, lhs)?.as_ref() {
        Ty::Float { width: width @ (32 | 64) } => *width,
        _ => return None,
    };
    let mag_width = trust_floatbits::magnitude_field_width(width);
    let magnitude_mask = u128::from(trust_floatbits::magnitude_mask(width));
    let tiny_bits = float_tiny_operand_bound_bits(width)?;
    let tiny = Formula::BitVec { value: (tiny_bits & magnitude_mask) as i128, width: mag_width };
    Some(
        [lhs, rhs]
            .into_iter()
            .map(|operand| {
                Formula::BvULe(
                    Box::new(tiny.clone()),
                    Box::new(v2_float_magnitude_bits(operand_to_formula(func, operand), width)),
                    mag_width,
                )
            })
            .collect(),
    )
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
    //
    // Trust (2026-10-17, gate RCA precision T7): EXCEPT a discharge earned by a tiny
    // CONSTANT operand (`float_add_witness_refutes_by_constant`): that row is emitted
    // with the tiny-operand conjuncts (`float_add_tiny_operand_conjuncts`), one of which
    // is false on a ground term, so it proves, as the seal reported it.
    let discharged = v2_float_binop_cannot_overflow_at(
        context.func,
        Some(context.block.id),
        context.summaries,
        op,
        lhs,
        rhs,
    );
    let tiny_constant_row =
        discharged && float_add_witness_refutes_by_constant(context.func, op, lhs, rhs);
    if discharged && !tiny_constant_row {
        return None;
    }
    // Trust 2026-08-03 — do NOT let "no witness shape" masquerade as
    // "discharged". A `None` here is indistinguishable from the discharge
    // `return None` ten lines above, and that conflation is what made every f32
    // op emit NO obligation at all before the width arms were generalised: the
    // row came back `no_obligations` / `proved` having checked nothing.
    //
    // The width arms now cover binary32/binary64, but the CONFLATION is the
    // durable defect — it silently swallows any width the arms do not cover, and
    // f16/f128 are exactly that today. For an unmodellable width, emit the
    // obligation carrying the MAXIMAL over-approximation of the violation set
    // (`true`). That is the sound direction by this module's own criterion — the
    // witness must over-approximate, and `true` contains every real overflow —
    // so it can never be proved UNSAT and can never falsely discharge. The row
    // stays visible and unproved instead of vanishing into a `proved`.
    let formula = match v2_float_overflow_witness_formula(context.func, op, lhs, rhs) {
        Some(formula) => formula,
        None if !float_witness_width_is_supported(v2_float_operand_width(context.func, lhs)?) => {
            Formula::Bool(true)
        }
        // A SUPPORTED width that still yielded no witness means there is
        // genuinely nothing to model (e.g. a non-float operand slipped through);
        // keep the historical behaviour.
        None => return None,
    };
    let formula = if tiny_constant_row {
        let Some(mut conjuncts) = float_add_tiny_operand_conjuncts(context.func, op, lhs, rhs)
        else {
            // No conjuncts at this width: the discharge stands, as before.
            return None;
        };
        conjuncts.insert(0, formula);
        Formula::And(conjuncts)
    } else {
        formula
    };
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
        function: context.func.name.as_str().into(),
        location: context.span.clone(),
        formula: v2_formula_with_block_defs_before_stmt(
            context.func,
            context.block,
            context.stmt_index,
            formula,
        ),
        contract_metadata: None,
        obligation: None,
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
    if func.preconditions.is_empty() {
        return Vec::new();
    }
    let mut hypotheses = Vec::new();
    let mut seen: Vec<&Place> = Vec::new();
    for operand in [lhs, rhs] {
        let (Operand::Copy(place) | Operand::Move(place)) = operand else { continue };
        if seen.contains(&place) {
            continue;
        }
        seen.push(place);
        let Some(width) = v2_float_operand_width(func, operand).filter(|w| matches!(w, 32 | 64))
        else {
            continue;
        };
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
                if (1..=func.body.arg_count).contains(&cur) {
                    return None;
                }
                match crate::local_defs::unique_value_def(func, cur)? {
                    Rvalue::Use(Operand::Copy(q) | Operand::Move(q)) => {
                        if (1..=func.body.arg_count).contains(&q.local) {
                            if !crate::place_source_is_stable(func, cur) {
                                return None;
                            }
                            return contract_range(func, q);
                        }
                        if q.projections.is_empty()
                            && q.local != cur
                            && crate::place_source_is_stable(func, cur)
                        {
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
        // The hypothesis is `magnitude_bits(operand) <= C`, and it must be
        // WEAKER than the contract, never stronger: every value the contract
        // admits has to satisfy it, or the solver is assuming more than the
        // user wrote. Magnitude bit patterns are monotone in magnitude, so `C`
        // must be the pattern of a value at this width that is `>= c`.
        //
        // `c` is tracked as f64. At binary32 `c as f32` rounds to NEAREST and
        // can land BELOW `c`, which would exclude values the contract admits —
        // the unsound direction. So mint the hypothesis only when the
        // narrowing is EXACT. That is the real shape anyway: for an f32
        // operand, `contract_range` derived `c` from f32 literals that widened
        // to f64 exactly.
        let c_bits_raw = match width {
            64 => c.to_bits(),
            32 => {
                let narrow = c as f32;
                if f64::from(narrow) != c {
                    continue;
                }
                u64::from(narrow.to_bits())
            }
            _ => continue,
        };
        // Trust: the magnitude field width and its mask are the VERIFIED
        // `trust-floatbits` table, not a fourth open-coded `(1 << (w-1)) - 1`.
        // `magnitude_mask(64)` is exactly what `binary64_magnitude_bits` applied,
        // so the f64 lane is bit-identical to before.
        let mag_width = trust_floatbits::magnitude_field_width(width);
        let c_bits = i128::from(c_bits_raw & trust_floatbits::magnitude_mask(width));
        hypotheses.push(Formula::BvULe(
            Box::new(v2_float_magnitude_bits(operand_to_formula(func, operand), width)),
            Box::new(Formula::BitVec { value: c_bits, width: mag_width }),
            mag_width,
        ));
    }
    hypotheses
}

/// Whether this module can build a SOUND overflow witness for `width`.
///
/// The witness arms cover binary32 and binary64. `f16`/`f128` are deliberately
/// absent: fabricating their constants would risk an UNDER-approximating
/// witness, which is the one direction that is a false-proof channel (see the
/// soundness note on [`v2_float_overflow_witness_formula`]). Refusing them is
/// correct — refusing them SILENTLY is not, which is what
/// [`v2_build_float_overflow_vc`] now prevents.
#[must_use]
pub(super) fn float_witness_width_is_supported(width: u32) -> bool {
    // Trust: the SAME predicate the field accessors saturate on, so a width this
    // returns `true` for is exactly a width `trust-floatbits` has a table row
    // for. Spelled separately (`matches!(width, 32 | 64)`) they could drift, and
    // the drift direction that matters is a `true` here for a width whose field
    // accessors all return `0`.
    trust_floatbits::format_supported(width) == 1
}

/// The common supported IEEE width of a binary operation. A missing, mixed or
/// unsupported operand width cannot authorize a numerical range or discharge.
pub(super) fn v2_float_binop_width(
    func: &VerifiableFunction,
    lhs: &Operand,
    rhs: &Operand,
) -> Option<u32> {
    match (v2_float_operand_width(func, lhs), v2_float_operand_width(func, rhs)) {
        (Some(width @ (32 | 64)), Some(other)) if width == other => Some(width),
        _ => None,
    }
}

/// The float width of `operand`, or `None` if it is not a float.
pub(super) fn v2_float_operand_width(func: &VerifiableFunction, operand: &Operand) -> Option<u32> {
    match crate::operand_ty_cow(func, operand).as_deref() {
        Some(Ty::Float { width }) => Some(*width),
        _ => None,
    }
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
        (BinOp::Add | BinOp::Sub, width @ (32 | 64)) => {
            let lhs_value = operand_to_formula(func, lhs);
            let rhs_value = operand_to_formula(func, rhs);
            // Trust: the IEEE-754 field table is the VERIFIED `trust-floatbits`
            // one. It used to be an ad-hoc tuple literal here, a second one in
            // the Div arm and a third open-coded mask in the Mul arm; a mask
            // that keeps the SIGN bit makes every negative operand compare as
            // enormous and silently stops the overflow witness from firing,
            // which is the under-approximating direction this whole module's
            // soundness note forbids.
            let mag_width = trust_floatbits::magnitude_field_width(width);
            let exp_width = trust_floatbits::exponent_field_width(width);
            let frac_width = trust_floatbits::fraction_field_width(width);
            let finite_exponent_value = i128::from(trust_floatbits::nonfinite_exponent(width));
            let threshold_bits = if width == 32 {
                (f32::MAX / 2.0).to_bits() as u128
            } else {
                (f64::MAX / 2.0).to_bits() as u128
            };
            let magnitude_mask = u128::from(trust_floatbits::magnitude_mask(width));
            let threshold = Formula::BitVec {
                value: (threshold_bits & magnitude_mask) as i128,
                width: mag_width,
            };
            let finite_exponent =
                Formula::BitVec { value: finite_exponent_value, width: exp_width };

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
        (BinOp::Mul, width @ (32 | 64)) => {
            // Trust: verified field table — see the Add/Sub arm.
            let mag_width = trust_floatbits::magnitude_field_width(width);
            let threshold_bits = if width == 32 {
                f32::MAX.sqrt().to_bits() as u128
            } else {
                f64::MAX.sqrt().to_bits() as u128
            };
            let magnitude_mask = u128::from(trust_floatbits::magnitude_mask(width));
            let threshold = Formula::BitVec {
                value: (threshold_bits & magnitude_mask) as i128,
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
        (BinOp::Div, width @ (32 | 64)) => {
            // Trust: verified field table — see the Add/Sub arm.
            let mag_width = trust_floatbits::magnitude_field_width(width);
            let exp_width = trust_floatbits::exponent_field_width(width);
            let frac_width = trust_floatbits::fraction_field_width(width);
            let finite_exponent_value = i128::from(trust_floatbits::nonfinite_exponent(width));
            let one_bits =
                if width == 32 { 1.0f32.to_bits() as u128 } else { 1.0f64.to_bits() as u128 };
            let magnitude_mask = u128::from(trust_floatbits::magnitude_mask(width));
            let divisor_threshold =
                Formula::BitVec { value: (one_bits & magnitude_mask) as i128, width: mag_width };
            let finite_exponent =
                Formula::BitVec { value: finite_exponent_value, width: exp_width };
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
