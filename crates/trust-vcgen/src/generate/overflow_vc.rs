// Arithmetic overflow obligations and their bit-vector encodings, including
// the dominating guard constraints that tighten operand ranges before the
// overflow question is asked. Signed multiplication is handled corner-by-corner
// because interval reasoning alone is too weak for it.

use super::*;

/// Dominating `<var> CMP <const>` facts that hold whenever the multiply at
/// `(block, use_stmt_index)` reads each of `operands`, as owned `(name, cmp,
/// constant)` triples — exactly what the bounded-corner overflow check needs to
/// compute the box the product ranges over.
///
/// Trust (2026-10-01): answered by the per-function [`dominating_facts`] index —
/// edge dominance and SSA value identity — instead of a per-row walk over the
/// enumerated paths (cubic, capped at `MAX_PATHS_PER_BLOCK`, and unsound across a
/// loop: see that module). EXACT-NAME lane deliberately: `operands` are the
/// multiply's own RAW operand locals, never copy-resolved bases, so a guard
/// contributes only when it names the operand itself. See
/// [`dominating_facts::GuardSubject`].
pub(super) fn v2_signed_mul_dominating_facts<'a>(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    use_stmt_index: usize,
    operands: &'a [(usize, String)],
) -> Vec<(&'a str, BvGuardCmp, i128)> {
    let index = super::dominating_facts_for(func);
    let mut facts = Vec::new();
    for (local, name) in operands {
        for &(cmp, constant) in index.facts(
            func,
            *local,
            block.id,
            use_stmt_index,
            dominating_facts::GuardSubject::ExactName,
        ) {
            facts.push((name.as_str(), cmp, constant));
        }
    }
    facts
}

/// Tighten `[lo, hi]` with one `<var> CMP c` fact. `Lt`/`Gt` shift the bound by
/// one toward the interior (`a < c` ⇒ `a <= c-1`); if that shift would over/under-
/// flow i128 the fact is dropped (a bound at the type extreme is not a real
/// tightening). All updates are monotone (a bound can only shrink the box), so a
/// fact can never enlarge the interval — soundness is preserved.
pub(super) fn v2_tighten_bound(
    cmp: BvGuardCmp,
    c: i128,
    lo: &mut Option<i128>,
    hi: &mut Option<i128>,
) {
    match cmp {
        BvGuardCmp::Le => *hi = Some(hi.map_or(c, |h| h.min(c))),
        BvGuardCmp::Lt => {
            if let Some(c1) = c.checked_sub(1) {
                *hi = Some(hi.map_or(c1, |h| h.min(c1)));
            }
        }
        BvGuardCmp::Ge => *lo = Some(lo.map_or(c, |l| l.max(c))),
        BvGuardCmp::Gt => {
            if let Some(c1) = c.checked_add(1) {
                *lo = Some(lo.map_or(c1, |l| l.max(c1)));
            }
        }
        BvGuardCmp::Eq => {
            *lo = Some(lo.map_or(c, |l| l.max(c)));
            *hi = Some(hi.map_or(c, |h| h.min(c)));
        }
    }
}

/// Concrete constant bounds `[lo, hi]` (both i128) that PROVABLY hold for `op` on
/// every reaching path into the multiply, or `None` if no such bounded box is
/// established. Sources (identical to the ones the add/sub arm's bound-gathering
/// consumes): a literal constant operand; a block-def pinning the operand's local
/// to a constant; dominating range guards; and gated contract preconditions.
///
/// SOUNDNESS: only facts true on EVERY reaching path are used, and each source is
/// staleness-guarded exactly as the add/sub arm is:
///   * a block-def constant pin is honored only when the local is single-def and
///     cannot be alias-mutated (`index_local_stable`), so the pinned constant IS
///     its live value at the multiply;
///   * a NON-constant in-block (re)assignment makes any block-entry guard stale,
///     so the operand yields no bound (fail closed);
///   * a contract precondition is used only while the operand still has its
///     function-entry version at the multiply.
///
/// A missing side (only a lower OR only an upper bound established) yields `None`:
/// the corner check needs a genuinely finite box on BOTH axes, so a symbolic /
/// one-sided-bounded operand fails closed — never proved.
fn v2_signed_mul_in_block_operand_bounds(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    local: usize,
    end: usize,
) -> Option<Option<(i128, i128)>> {
    // BLOCK-DEF CONSTANT PIN: the operand's LAST projection-free definition
    // strictly before the multiply is `local = <const>`.
    let mut const_pin: Option<i128> = None;
    let mut cast_box: Option<(i128, i128)> = None;
    let mut assigned_in_block = false;
    for stmt in block.stmts.iter().take(end) {
        let Statement::Assign { place: p, rvalue, .. } = stmt else {
            continue;
        };
        if p.local != local || !p.projections.is_empty() {
            continue;
        }
        assigned_in_block = true;
        cast_box = None;
        const_pin = match rvalue {
            Rvalue::Use(inner) => operand_const_int(inner),
            // Trust (2026-09-30): `x as i128` from a NARROWER integer keeps the
            // value, so the operand lies in the source type's range (sweep `m20`:
            // `(a as i128) * (b as i128)` over two i64 parameters, which cannot
            // overflow i128, was refused for want of any box).
            Rvalue::Cast(src, _) => {
                cast_box = match crate::operand_ty_cow(func, src).as_deref() {
                    Some(Ty::Int { width, signed: true }) if (1..128).contains(width) => {
                        let half = 1i128 << (width - 1);
                        Some((-half, half - 1))
                    }
                    Some(Ty::Int { width, signed: false }) if (1..127).contains(width) => {
                        Some((0, (1i128 << width) - 1))
                    }
                    _ => None,
                };
                None
            }
            _ => None,
        };
    }
    if let Some(bx) = cast_box {
        // Same stability gate as the constant pin: single-def, never alias-mutated.
        return Some(crate::index_local_stable(func, local).then_some(bx));
    }
    if let Some(c) = const_pin {
        // Honor the pin only if the local is single-def and cannot be alias-
        // mutated between the def and the multiply (`&mut`/opaque-move escape).
        return Some(crate::index_local_stable(func, local).then_some((c, c)));
    }
    // A non-constant in-block (re)assignment makes any block-ENTRY guard stale.
    if assigned_in_block {
        return Some(None);
    }
    None
}

fn v2_signed_mul_guard_and_precondition_bounds(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    base: &str,
    end: usize,
    guard_facts: &[(&str, BvGuardCmp, i128)],
    sv: &mut Option<std::rc::Rc<StmtVersionCtx>>,
) -> Option<(i128, i128)> {
    // DOMINATING GUARDS + gated contract preconditions: tighten [lo, hi].
    let mut lo: Option<i128> = None;
    let mut hi: Option<i128> = None;
    for (name, cmp, c) in guard_facts {
        if *name == base {
            v2_tighten_bound(*cmp, *c, &mut lo, &mut hi);
        }
    }
    if !func.preconditions.is_empty() {
        for fact in &func.preconditions {
            let Some((name, cmp, c)) = v2_linear_var_const_fact(fact) else {
                continue;
            };
            if name != base {
                continue;
            }
            let sv = sv.get_or_insert_with(|| super::stmt_versions_for(func));
            if sv.version_token_at(func, block.id, end, name).is_some() {
                continue;
            }
            v2_tighten_bound(cmp, c, &mut lo, &mut hi);
        }
    }
    match (lo, hi) {
        (Some(l), Some(h)) if l <= h => Some((l, h)),
        _ => None,
    }
}

pub(super) fn v2_signed_mul_operand_bounds(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: &Operand,
    end: usize,
    guard_facts: &[(&str, BvGuardCmp, i128)],
    sv: &mut Option<std::rc::Rc<StmtVersionCtx>>,
) -> Option<(i128, i128)> {
    // Literal constant operand: an exact single-point box.
    if let Some(c) = operand_const_int(op) {
        return Some((c, c));
    }
    let (Operand::Copy(place) | Operand::Move(place)) = op else {
        return None;
    };
    if !place.projections.is_empty() {
        return None;
    }
    let local = place.local;
    if guards::value_local_is_unstable(func, local) {
        return None;
    }
    if let Some(in_block) = v2_signed_mul_in_block_operand_bounds(func, block, local, end) {
        return in_block;
    }
    if guard_facts.is_empty() && func.preconditions.is_empty() {
        return None;
    }
    let base = crate::place_to_var_name(func, place);
    v2_signed_mul_guard_and_precondition_bounds(func, block, &base, end, guard_facts, sv)
}

/// Constant bounded boxes `([la,ha], [lb,hb])` for the signed-128 multiply's
/// operands, or `None` when EITHER operand lacks a finite constant box (⇒ the
/// caller keeps the fail-closed runtime-check). `end` bounds the block-def scan
/// to statements before the operation, mirroring `v2_signed_bv_blockdef_constraints`.
pub(super) fn v2_signed_mul_corner_bounds(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    lhs: &Operand,
    rhs: &Operand,
    stmt_index: Option<usize>,
) -> Option<((i128, i128), (i128, i128))> {
    let end = stmt_index.unwrap_or(block.stmts.len());
    let mut resolved: [Option<(i128, i128)>; 2] = [None, None];
    let mut operands: Vec<(usize, String)> = Vec::with_capacity(2);
    let mut operand_names: [Option<usize>; 2] = [None, None];
    for (idx, operand) in [lhs, rhs].into_iter().enumerate() {
        if let Some(c) = operand_const_int(operand) {
            resolved[idx] = Some((c, c));
            continue;
        }
        let (Operand::Copy(place) | Operand::Move(place)) = operand else {
            return None;
        };
        if !place.projections.is_empty() || guards::value_local_is_unstable(func, place.local) {
            return None;
        }
        if let Some(in_block) = v2_signed_mul_in_block_operand_bounds(func, block, place.local, end)
        {
            resolved[idx] = Some(in_block?);
            continue;
        }
        let pos = operands.len();
        operands.push((place.local, crate::place_to_var_name(func, place)));
        operand_names[idx] = Some(pos);
    }
    if operands.is_empty() {
        return Some((resolved[0]?, resolved[1]?));
    }
    let guard_facts = v2_signed_mul_dominating_facts(func, block, end, &operands);
    if guard_facts.is_empty() && func.preconditions.is_empty() {
        return None;
    }
    let mut sv = None;
    let a = match resolved[0] {
        Some(bx) => bx,
        None => {
            let base = &operands[operand_names[0]?].1;
            v2_signed_mul_guard_and_precondition_bounds(func, block, base, end, &guard_facts, &mut sv)?
        }
    };
    let b = match resolved[1] {
        Some(bx) => bx,
        None => {
            let base = &operands[operand_names[1]?].1;
            v2_signed_mul_guard_and_precondition_bounds(func, block, base, end, &guard_facts, &mut sv)?
        }
    };
    Some((a, b))
}

/// Does `[la,ha] * [lb,hb]` provably stay within `[i128::MIN, i128::MAX]`?
///
/// For EXACT integer multiplication the extremes of the product over a box are
/// attained at the four CORNERS `la*lb, la*hb, ha*lb, ha*hb` (standard interval
/// arithmetic), so the whole product range fits i128 IFF every corner fits.
/// `i128::checked_mul` returns `None` EXACTLY when the mathematical product falls
/// outside `[i128::MIN, i128::MAX]`, so "all four corners `Some`" is a sound,
/// exact "cannot overflow" test — no wider integer type is needed. A `None` on
/// ANY corner ⇒ that corner overflows ⇒ overflow is possible ⇒ NOT provable.
/// An inconsistent (empty) box is treated as not-provable (conservative).
pub(super) fn v2_signed_mul_corners_fit(a: (i128, i128), b: (i128, i128)) -> bool {
    let ((la, ha), (lb, hb)) = (a, b);
    if la > ha || lb > hb {
        return false;
    }
    [(la, lb), (la, hb), (ha, lb), (ha, hb)].into_iter().all(|(x, y)| x.checked_mul(y).is_some())
}

/// Whether `lhs * rhs` at signed 128-bit provably CANNOT overflow, by the
/// bounded-corner argument.
///
/// THE SINGLE SOURCE OF TRUTH for that question, deliberately. Two callers must
/// agree on it exactly, and they answer for opposite reasons:
///
///  * `v2_build_overflow_vc_for_operands` uses it to mint NO obligation.
///  * `v2_overflow_assert_provably_cannot_fire` uses it to suppress the assert
///    BEFORE the builder runs — necessary because in the assert lane a builder
///    returning `None` means "could not analyse" and raises
///    `RecognizedSafetyAssertProofGap`, not "provably safe".
///
/// Were these two to drift apart, the assert lane would call the builder, get
/// `None`, and emit a proof gap — i.e. a runtime check. That is the fail-closed
/// direction, so a divergence costs precision, never soundness. Sharing this
/// function removes the possibility either way.
///
/// Answers `false` for every shape that is not the signed-128 Mul case, so it is
/// safe to call unconditionally.
pub(super) fn v2_signed_mul_provably_cannot_overflow(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    stmt_index: Option<usize>,
) -> bool {
    if !matches!(op, BinOp::Mul) {
        return false;
    }
    let Some((width, signed)) = int_op_type(func, lhs, rhs) else {
        return false;
    };
    if !signed || width < 128 {
        return false;
    }
    v2_signed_mul_corner_bounds(func, block, lhs, rhs, stmt_index)
        .is_some_and(|(a_box, b_box)| v2_signed_mul_corners_fit(a_box, b_box))
}

/// Trust (arith ARM, 2026-07-31): split a block-def-versioned arithmetic-overflow
/// violation body `And([lhs_range, rhs_range, out_of_range])` into the authenticated
/// obligation. `rec_body` is the version-renamed body as it appears INSIDE the emitted
/// formula (from `v2_formula_with_block_defs_at_point_recorded`), `kept` the block-defs
/// conjoined around it.
///
/// The RECORDED `body` is the ATOMIC out-of-range core the consumer's `is_core` accepts —
/// `Or([Lt(a∘b, MIN), Gt(a∘b, MAX)])` for uadd / signed add,sub,mul / umul, or the bare
/// `Lt(a-b, 0)` unsigned-sub underflow — and the two operand ranges are DEMOTED to a
/// `ConjoinFactsLast` wrapper (they are premises, not the violation). A second
/// `ConjoinFactsLast` carries the kept block-defs. Ordered innermost-first so
/// `reconstruct(body, wrappers)` reproduces the emitted formula BIT-FOR-BIT:
/// the range wrapper rebuilds `And([r0, r1, core]) == rec_body`, then the block-def
/// wrapper rebuilds `And([kept.., rec_body])`.
///
/// `subject = None` (arithmetic overflow is payload-free); `width` is the REAL operand
/// width from `int_op_type` (the non-constant operand's type, NOT `min(wa, wb)`), the
/// [10]-class width authority. FAILS CLOSED (`None`) when `rec_body` is not the canonical
/// 3-conjunct `And` — which excludes the Pow bodies (`Bool(true)`, or a 2-conjunct
/// `And([base_range, out_of_range])`), leaving those genuinely-unmodeled shapes to peel.
pub(super) fn v2_arith_overflow_seed_record(
    rec_body: Formula,
    kept: Vec<Formula>,
    width: u32,
) -> Option<ObligationRecord> {
    let Formula::And(mut conjuncts) = rec_body else {
        return None;
    };
    let Some(atomic_core) = (conjuncts.len() == 3).then(|| conjuncts.pop()).flatten() else {
        return None;
    };
    let mut wrappers = vec![ObligationWrapper::ConjoinFactsLast { facts: conjuncts }];
    if !kept.is_empty() {
        wrappers.push(ObligationWrapper::ConjoinFactsLast { facts: kept });
    }
    Some(ObligationRecord { body: atomic_core, wrappers, subject: None, width: Some(width) })
}

// Production callers all thread the audited destination type through the
// `_typed` entry below; only the operand-inference test suites still exercise
// this untyped entry directly.
#[cfg(test)]
pub(super) fn v2_build_overflow_vc_for_operands(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    span: &SourceSpan,
    stmt_index: Option<usize>,
) -> Option<VerificationCondition> {
    v2_build_overflow_vc_for_operands_impl(
        func,
        block,
        op,
        lhs,
        rhs,
        span,
        stmt_index,
        None,
        "IntegerMulOverflow",
    )
}

/// Trust (width-soundness): the plain/checked overflow row built at the
/// assignment DESTINATION's VALIDATED integer type, mirroring what the
/// `UncheckedBinaryOp` arm already does. Signed constants carry no width in
/// TrustIR, so when BOTH operands are widthless constants `int_op_type`
/// fabricates i64 and a forged-but-admitted `_1: i8 = Add(100, 100)` (each
/// literal fits i8, so `validate_binary_assignment_types` admits it) would be
/// checked against the i64 bound — `200 outside i64` is UNSAT and the runtime
/// i8 overflow is falsely PROVED away. The destination type is the audited
/// operation type (admission pins every operand to it), so threading it can
/// only replace a fabricated width with the true one. `operation_ty: None`
/// preserves the untyped operand-inference behavior byte-for-byte for callers
/// with no destination authority.
pub(super) fn v2_build_overflow_vc_for_operands_typed(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    span: &SourceSpan,
    stmt_index: Option<usize>,
    operation_ty: Option<Ty>,
) -> Option<VerificationCondition> {
    v2_build_overflow_vc_for_operands_impl(
        func,
        block,
        op,
        lhs,
        rhs,
        span,
        stmt_index,
        operation_ty,
        "IntegerMulOverflow",
    )
}

/// Build the mandatory overflow row for a validated UB-bearing unchecked
/// assignment. Unlike ordinary binary arithmetic, the operation's type comes
/// from the assignment destination: signed constants do not retain a width in
/// TrustIR, so inferring from two constants could silently check i64 bounds for
/// an i8 operation.
pub(super) fn v2_build_unchecked_overflow_vc_for_operands(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    span: &SourceSpan,
    stmt_index: Option<usize>,
    operation_ty: Ty,
) -> Option<VerificationCondition> {
    v2_build_overflow_vc_for_operands_impl(
        func,
        block,
        op,
        lhs,
        rhs,
        span,
        stmt_index,
        Some(operation_ty),
        "Rvalue::UncheckedBinaryOp",
    )
}

fn v2_build_overflow_vc_for_operands_impl(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    span: &SourceSpan,
    stmt_index: Option<usize>,
    operation_ty: Option<Ty>,
    unsupported_carrier_kind: &'static str,
) -> Option<VerificationCondition> {
    if [lhs, rhs]
        .iter()
        .any(|operand| matches!(operand, Operand::Constant(value) if value.contains_memory_image()))
    {
        return Some(unsupported_mir_vc(
            func,
            crate::MEMORY_IMAGE_KIND.into(),
            crate::MEMORY_IMAGE_DETAIL.into(),
            span.clone(),
        ));
    }
    // `OpaqueScalar` is a value this builder does not model (an unevaluated
    // constant, or a runtime value such as an exposed address) and its symbol
    // carries no range bound, so an overflow row over it would be decided by an
    // unconstrained Int. Refuse before formula construction for every arithmetic
    // carrier that shares this builder. (Before OPAQUE-SCALAR-ID-1 two
    // same-typed occurrences also rendered to ONE symbol, so `a - b` became the
    // false proof `x - x`; that is closed at the renderer, and this refusal stays
    // as the precision boundary.) Const parameters keep their stable name.
    if matches!(lhs, Operand::Constant(ConstValue::OpaqueScalar { .. }))
        || matches!(rhs, Operand::Constant(ConstValue::OpaqueScalar { .. }))
    {
        return Some(unsupported_mir_vc(
            func,
            "IntegerArithmeticOpaqueScalar".to_string(),
            format!("bb{}: overflow checking does not model OpaqueScalar operands", block.id.0),
            span.clone(),
        ));
    }

    let inferred_lhs_ty = crate::operand_ty_cow(func, lhs)?;
    let inferred_rhs_ty = crate::operand_ty_cow(func, rhs)?;
    // Recover the true (width, signed) from a non-constant operand — a signed
    // constant lhs (e.g. `100i8 + x`) loses its width and would otherwise make
    // this check the overflow bound at i64 instead of the real type (round-19).
    let (width, signed) = if let Some(ref operation_ty) = operation_ty {
        crate::fixed_width_integer_descriptor(operation_ty)?
    } else {
        let op_ty = if !matches!(lhs, Operand::Constant(_)) {
            inferred_lhs_ty.as_ref()
        } else if !matches!(rhs, Operand::Constant(_)) {
            inferred_rhs_ty.as_ref()
        } else {
            let wa = inferred_lhs_ty.int_width().unwrap_or(u32::MAX);
            let wb = inferred_rhs_ty.int_width().unwrap_or(u32::MAX);
            if wa <= wb { inferred_lhs_ty.as_ref() } else { inferred_rhs_ty.as_ref() }
        };
        (op_ty.int_width()?, op_ty.is_signed())
    };

    // Trust #soundness (i128): in the ABSTRACT, the Int/LIA path is sound for signed
    // 128-bit ADD/SUB — `Sort::Int` is unbounded arbitrary-precision (ay lowers every
    // `Formula::Int` via `Expr::int_const(impl Into<BigInt>)`), so a `result < i128::MIN
    // ∨ result > i128::MAX` query is SAT exactly when a real i128 add/sub overflows. BUT
    // the NATIVE typed-CHC lane that actually solves these obligations
    // (`trust-mc/.../native/typed_chc_ay.rs`) lowers every `Formula::Int(c)` constant
    // through `parse_i64`, which REJECTS the ±2^127 range bounds an i128 VC carries
    // (`type_min_formula`/`type_max_formula` = `i128::MIN`/`i128::MAX`) → "does not fit
    // native ay-chc i64" → the obligation is UNSUPPORTED → UNKNOWN. That is precisely why
    // `trust-semantics::signed_max`/`signed_min`'s trailing `_5 - 1` / `-_5` were UNKNOWN.
    //
    // The same native lane's BITVECTOR theory handles the FULL 128-bit width: it lowers
    // `BitVecConst` via `parse_u128` and ships sound add/sub/neg overflow expansions
    // (`require_bv_width` allows <=128). So for signed >=128-bit add/sub/neg we EMIT THE
    // VC IN BV (not Int), via the cheap `w+1`-bit sign-extension check
    // (`v2_signed_bv_addsub_overflow_formula`), conjoining BV-rendered block-defs / guard
    // bounds on the operands so a value safe ONLY because of a defining shift (signed_max's
    // `_5 = 1i128 << (width-1)`) still PROVES. Widths <=64 stay on the Int path (the native
    // i64-LIA handles them losslessly and the Int path preserves the conjoined
    // guards/block-defs there, which the self-contained fresh-BV-operand encoding drops).
    //
    // MUL is the sole exception: signed MUL is nonlinear, the signed BV mul check needs a
    // `2w` = 256-bit multiplier (declined > 64), and the Int-path fallback is NIA
    // (undecidable / hangs). So signed 128-bit MUL stays fail-closed → runtime-check
    // (UNKNOWN, sound) — UNLESS both operands have KNOWN CONSTANT bounds, in which case a
    // BOUNDED-CORNER check decides overflow with pure i128 arithmetic (no nonlinear product,
    // no 256-bit multiplier). When `a ∈ [la,ha]` and `b ∈ [lb,hb]` are established on every
    // reaching path (block-def const pins, dominating range guards, or gated preconditions —
    // the SAME facts the add/sub arm gathers), the exact integer product `a*b` overflows i128
    // IFF at least one of the four CORNER products falls outside `[i128::MIN, i128::MAX]`
    // (interval-arithmetic: the extremes of a product over a box are at its corners). If ALL
    // four corners fit i128 the multiply provably cannot overflow → emit a Bool(false)
    // violation formula (trivially UNSAT ⇒ certifies). SOUNDNESS: proving requires a genuinely
    // finite box on BOTH operands from every-path facts (a symbolic / one-sided-bounded /
    // reassigned-stale operand yields no box ⇒ no proof), and a `checked_mul` overflow on ANY
    // corner keeps the fail-closed runtime-check. Never a false PROVE.
    if signed && width >= 128 && matches!(op, BinOp::Mul) {
        if v2_signed_mul_provably_cannot_overflow(func, block, op, lhs, rhs, stmt_index) {
            // SUPPRESS — mint nothing. This used to emit
            // `formula: Formula::Bool(false), obligation: None` on the theory
            // that "trivially UNSAT ⇒ certifies". It never certified, for two
            // independent reasons, either of which is fatal:
            //
            //  1. `trust_router::constant_folder::apply_vacuity_gate` cannot
            //     distinguish a constant-false violation from the legacy vacuous
            //     placeholder it exists to reject, so it rewrote the row to
            //     `Unknown { reason: "vacuous proof rejected …" }`. That gate runs
            //     on EVERY row in `build_proof_results`.
            //  2. Even exempted from the gate, `convert_result` demotes any Proved
            //     row carrying no row-bound `ResultProofAuthority`, and a bare
            //     `Bool(false)` with `obligation: None` can acquire none:
            //     `certify_vc` has no family for it, both production safety
            //     certifiers require an authenticated `ObligationRecord`, and the
            //     one vacuity-exempt native authority is the CHC/PDR lane — which
            //     is exactly the lane that declines signed 128-bit Mul, the reason
            //     this arm exists at all.
            //
            // So the capability read as a proof at this seam and was graded
            // Unknown/runtime-checked one layer down, with a diagnostic that
            // actively misdescribed it.
            //
            // Suppression is this module tree's convention for a "provably
            // cannot fire" case whose obligation could carry NO authority even
            // if minted — see `v2_build_float_overflow_vc` returning `None` and
            // the Div/Rem nonzero-constant skip, both of which would emit a bare
            // `Bool(false)` with `obligation: None`. It is NOT the convention
            // for every provably-safe case: the literal in-range BoundsCheck
            // (`arr[0]` on `[i64; 3]`) IS minted, because its violation is an
            // arithmetic core carrying a real `ObligationRecord` — reason 1
            // does not fire on it and reason 2 does not apply. See the
            // `AssertMessage::BoundsCheck` arm in `safety.rs`.
            //
            // The ASSERT lane must not see this `None`. There, a builder returning
            // `None` means "could not analyse" and raises
            // `RecognizedSafetyAssertProofGap`, so the suppression is decided
            // BEFORE the builder by `v2_overflow_assert_provably_cannot_fire`,
            // which shares `v2_signed_mul_provably_cannot_overflow` with this arm
            // so the two can never disagree. If they ever did, this `None` would
            // become a proof gap — the fail-closed direction.
            //
            // SOUNDNESS unchanged: reaching here needs a genuinely finite box on
            // BOTH operands from every-path facts and all four corner products
            // fitting i128 (interval arithmetic puts the extremes of a product
            // over a box at its corners). A symbolic, one-sided-bounded or
            // reassigned-stale operand yields no box, and a `checked_mul`
            // overflow on ANY corner falls through to the fail-closed runtime
            // check below. Never a false PROVE.
            return None;
        }
        return Some(unsupported_mir_vc(
            func,
            unsupported_carrier_kind.to_string(),
            format!(
                "bb{}: signed {width}-bit Mul overflow is nonlinear (NIA) and not decidable \
                 on the Int path; the BV path declines width > 64 → fail-closed to runtime-check",
                block.id.0
            ),
            span.clone(),
        ));
    }

    let (lhs_ty, rhs_ty) = match operation_ty {
        Some(operation_ty) => (operation_ty.clone(), operation_ty),
        None => (inferred_lhs_ty.into_owned(), inferred_rhs_ty.into_owned()),
    };

    // signed-128 add/sub → BV (the native LIA lane cannot represent ±2^127; see the
    // soundness note above). Build the self-contained `w+1`-bit sign-extension overflow
    // check and conjoin the BV-rendered block-defs / dominating guard bounds on the
    // operands. SOUNDNESS: the violation formula is `block_defs ∧ guards ∧ overflow`, SAT
    // iff a feasible input overflows; an unconstrained operand (free `x`) carries NO
    // block-def, so a real overflow stays refutable (the adversarial guardrail). Only
    // facts TRUE on every reaching path are conjoined, so a flip Failed -> Proved happens
    // only when no feasible overflow exists — never a false PROVE.
    if signed && width >= 128 && matches!(op, BinOp::Add | BinOp::Sub) {
        let bv0 = v2_signed_bv_addsub_overflow_formula(func, lhs, rhs, op, width);
        if let Some(bv_formula) = bv0 {
            let mut terms =
                v2_signed_bv_blockdef_constraints(func, block, lhs, rhs, stmt_index, width);
            // Trust (completeness, task #77): also thread the DOMINATING RANGE GUARDS on
            // the operands (`if a < 100 { a + 1 }`) onto the fresh BV operand vars — the
            // same staleness-aware mechanism the unsigned/≤64-bit signed BV mul path uses
            // (`v2_bv_mul_dominating_guard_constraints` → `dominating_facts`). The
            // signed-128 add/sub formula's operands are the SAME `__trust_ovf_bv_{role}_{base}`
            // fresh vars, so the constraints bind. SOUNDNESS: only facts of a DOMINATING
            // guarded edge about the very SSA value the operation reads are conjoined, and an
            // operand that can be written through an alias takes none (verified: the unsigned
            // `&mut`-stale mul stays Failed) — so a stale `a < 10` over a `*p = b` reassignment
            // does NOT thread, and the unguarded `a + b` (no dominating fact) stays refutable.
            terms.extend(v2_bv_mul_dominating_guard_constraints(
                func, block, lhs, rhs, stmt_index, width, true,
            ));
            // Also render a SIGNED-accumulator reduction bound (`acc ∈ [init, init+K·per_max]`,
            // `addend ∈ [0, per_max]`) onto the fresh BV operands, so an i128 shift/widening
            // reduction whose sum provably fits PROVES (the global Int accumulator facts don't
            // bind to the disjoint BV vars). See `v2_signed_bv_accumulator_constraints`.
            terms.extend(v2_signed_bv_accumulator_constraints(func, block, lhs, rhs, width));
            let formula = if terms.is_empty() {
                bv_formula
            } else {
                terms.push(bv_formula);
                Formula::And(terms)
            };
            return Some(VerificationCondition {
                kind: VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) },
                function: func.name.as_str().into(),
                location: span.clone(),
                formula,
                contract_metadata: None,
                obligation: None,
            });
        }
        // Operands not BV-encodable (symbolic): fall through to the Int path (sound;
        // stays UNKNOWN on the native lane, exactly as before this change).
    }

    // bitvec-overflow: only UNSIGNED MULTIPLY needs the bitvector
    // encoding. Unsigned add/sub overflow is LINEAR over mathematical integers,
    // so the Int path below decides it *completely* — its conjoined range +
    // guard + block-def constraints (`input_range_constraint`,
    // `v2_formula_with_block_defs`) let a precondition-bounded add/sub PROVE.
    // Routing add/sub through the self-contained BV failure condition would drop
    // those guards (the BV operands are fresh, see
    // `v2_unsigned_bv_overflow_formula`) and false-Fail provably-safe code, so
    // we deliberately do NOT do that.
    //
    // MUL on the Int path is nonlinear (NIA) and undecidable (hangs / Unknown),
    // which is exactly what the bitvector encoding fixes: bvmul/bvudiv (unsigned)
    // and the sign-extended width-doubling product check (signed) are decidable.
    // SOUNDNESS vs COMPLETENESS of the BV mul path — the BV operands are
    // fresh/unconstrained UNLESS one is recognized as a value-preserving widening
    // cast, in which case `v2_bv_operand_term` encodes it STRUCTURALLY as a
    // zero/sign-extension of a fresh source-width var (capturing its true range
    // in pure QF_BV). So:
    //   * an unguarded mul that can overflow is correctly REFUTED with a
    //     verified counterexample (the new capability; previously NIA-Unknown);
    //   * a safe WIDENING mul like `(x as u64) * (y as u64)` (x,y: u32) now
    //     PROVES, because each operand is < 2^32 by construction;
    //   * a mul that is safe ONLY because of a non-cast precondition may still
    //     report Failed (conservative false-Failed) — never a false "Proved".
    //
    // Both add/sub stay on the Int/LIA path: they are linear and the Int path
    // keeps the conjoined preconditions/guards/block-defs (the fresh-BV-operand
    // encoding would drop them), so a precondition-bounded add/sub PROVES there.
    // Only MUL is routed to BV.
    //
    // `int_width()` already resolves `usize` to the target pointer width at
    // MIR-extraction time, so `width` is the true machine width here.
    // A CONSTANT-multiplier mul with no widening-cast operand (`x * 4`) is LINEAR,
    // so the Int/LIA path below decides it exactly AND retains the conjoined
    // block-defs + slice-length / arg-type bounds that the fresh-BV-operand encoding
    // DROPS. Routing it here proves precondition-bounded products such as the base64
    // `(full_chunks + 1) * 4` (full_chunks = len / 3, len <= isize::MAX), which the
    // BV path false-Fails on an unconstrained fresh operand. A var*var mul (genuinely
    // NIA) or a widening-cast mul stays on the BV path, where BV is the stronger /
    // required procedure and the fresh-operand precondition drop is acceptable.
    // This also routes the loop-var-bounded `y * W` flattened-2D-index stride
    // (`g[y*W+x]`) to Int, where the yield-bound `y < H` proves it (the BV
    // `bvudiv(bvmul,..)` overflow check returns Unknown on it).
    // Trust (Program 3, authority gap): a widening-cast operand is ALSO linear when
    // the other operand is a constant, so it belongs on the Int/LIA path too.
    //
    // `v2_widening_bv_source` returns `Some` only for a STRICT, value-preserving
    // widening (`dw > sw`, never signed->unsigned) whose local is
    // `index_local_stable` — a unique reaching whole-local def with no alias
    // mutation. Under exactly those conditions the operand's Int value EQUALS its
    // source value, so Int and BV agree on it and LIA decides `widened * k`
    // exactly, using the source-width bound (`0 <= _2 <= 255`) that block-defs
    // already conjoin alongside the target-width one.
    //
    // Why it matters beyond precision: the BV encoding of a mul is not reachable by
    // `certify_vc`'s reconstruction families — they cover signed BV add/sub and the
    // unsigned div-sum, not BV mul — so `(v as u16) * 2` was solver-`Proved` and
    // then downgraded to `runtime-checked` for want of exact kernel authority, which
    // cannot license an erasure and fails a strict build. On the Int path the same
    // obligation lands in the linear fragment the kernel CAN reconstruct, exactly as
    // `v as u16 + 1` already does.
    //
    // A var*var mul (genuinely NIA) still takes the BV path: this relaxes only the
    // CONSTANT-multiplier case, where linearity is structural.
    let linear_const_mul = matches!(op, BinOp::Mul)
        && (matches!(lhs, Operand::Constant(_)) || matches!(rhs, Operand::Constant(_)));
    if matches!(op, BinOp::Mul) && !linear_const_mul {
        let bv_formula = if signed {
            v2_signed_bv_overflow_formula(func, lhs, rhs, width)
        } else {
            v2_unsigned_bv_overflow_formula(func, lhs, rhs, op, width)
        };
        if let Some(bv_formula) = bv_formula {
            // Conjoin BV-encoded dominating guard bounds on the operands so a
            // guard-bounded mul (`if cols <= 4096 { cols * 64 }`) PROVES
            // instead of false-Failing on the fresh, unconstrained BV vars.
            // Both the signed arm (line ~748) and the unsigned arm (line ~859)
            // also render the Int twin of these exact facts, so mine once.
            let mul_dom_facts =
                v2_mul_dominating_operand_facts(func, block, lhs, rhs, stmt_index, width);
            let mut terms = v2_bv_guard_constraints_from_facts(&mul_dom_facts, width, signed);
            // Also render a LOOP-VAR yield bound (`y < W` for `for y in 0..W`) onto the operands so
            // a flattened-2D-index `y*W` mul-overflow PROVES. See `v2_bv_yield_constraints`.
            terms.extend(v2_bv_yield_constraints(func, block, lhs, rhs, width, signed));
            // And render a REMAINDER bound (`r < C` for `r = x % C`) so the range-clamping
            // idiom `(a % 100) * (b % 50)` PROVES. See `v2_bv_rem_constraints`.
            terms.extend(v2_bv_rem_constraints(func, lhs, rhs, width, signed));
            // Trust: 2026-09-18 (the SIGNED g7 twin) — the SIGNED row needs the same
            // INT rendering of the dominating facts that the unsigned row below
            // already gets, and for the same measured reason: the deployed interval
            // backend's `prove_bv_smul_no_overflow` is the lane that decides a
            // guard-bounded signed multiply, and it decides it by INTERVAL
            // ARITHMETIC — `env.eval(lhs).mul(env.eval(rhs))` over the four corners
            // of the two operand boxes, checked against `[i64::MIN, i64::MAX]`. That
            // is exactly the two-sided reasoning a signed multiply needs: a bound on
            // one side alone leaves the other's box infinite, the product interval
            // is unbounded, and the backend declines — so the ONE-SIDED twin
            // (`if a < 1000 && b < 1000 { b = a * b; }` over i64, where both operands
            // may be hugely negative) is not proved by accident.
            //
            // `env.eval` reads a fresh `__trust_ovf_bv_{role}_{base}` var by looking
            // the NUMERIC bounds of `{base}` up in its INT environment; it never
            // reads a `BvSlt`/`BvSgt` atom as a bound. So the BV rendering above,
            // alone, gives the backend nothing to compute a box from, and the signed
            // row sat at `Unknown` (measured: ay computed UNSAT on the pure-BV query
            // in 30 s and strict certification then rejected the proof —
            // "step t1 uses unsupported theory lemma kind Generic in strict mode" —
            // so the row fell to a runtime check even when it was not refuted).
            //
            // NOT an Int CORE for the signed row. The unsigned arm below also makes
            // the Int out-of-range reading the obligation BODY; that is sound there
            // because the unsigned BV overflow predicate and the Int reading are the
            // same machine predicate, and it is USEFUL there because the kernel's
            // product lift can ground it. For SIGNED operands the kernel's lift
            // (`product_upper_lift` / `product_nonneg_lift` in trust-certify) is
            // NON-NEGATIVE-ONLY — it declines on a negative bound outright — so an
            // Int core would buy no kernel authority, while making the row a mixed
            // QF_BV + NIA query of exactly the kind the umul record comment records
            // as having cost a `Failed`-with-witness once already. Facts only.
            if signed {
                terms.extend(v2_int_guard_constraints_from_facts(&mul_dom_facts));
            }
            // Trust: UMUL RECORD, RE-LANDED (2026-08-20) — the UNSIGNED var*var
            // mul VC carries an AUTHENTICATED obligation again: the Int-reading
            // out-of-range core `Or([Lt(a*b,0), Gt(a*b,MAX)])` becomes the record
            // BODY and the formula's final conjunct, with the BV rendering and
            // the guard bounds demoted to a `ConjoinFactsLast` wrapper — so
            // `reconstruct(record) == formula` bit-for-bit (the authentication
            // invariant) and the trust-ir/mirsem umul arms can ground the core.
            //
            // THIS WAS RETRACTED ONCE, on 2026-08-20, and the reason it is safe
            // NOW is a change in a different crate. The Int core makes the query
            // a mixed QF_BV + NIA problem that ay has no combined decision
            // procedure for: it answers `incomplete`, phase
            // `theory-combination`, with its executor refusal ("unsupported
            // logic: QF_AUFBVNIA (no combined decision procedure …)") as the
            // detail (`internal-error` before ay's AD1 fix, f0bb8f9368),
            // so an unguarded overflowing `a*b` degraded from `Failed` WITH A
            // VERIFIED COUNTEREXAMPLE to `Unknown` — under the prime directive,
            // from a build error to a runtime check. `trust-router`'s
            // DISJOINT-COMPONENT REFUTATION lane now refutes such a query
            // component-wise (the BV predicate and the Int core are over disjoint
            // variable sets), so that verdict is `Failed` with a composed witness
            // again — MEASURED both ways before re-landing. Do not re-land this
            // conjunct into a build where that lane is absent or narrowed: the
            // pins `trust_router::in_process_ay_backend::tests::
            // umul_bare_bv_unguarded_refutes_with_counterexample` and
            // `disjoint_split_refutes_the_mixed_bv_nia_mul_query` are what hold
            // the pair together.
            //
            // SOUNDNESS of the conjoin itself (unchanged from the first landing):
            // for unsigned width-w operands the BV overflow predicate and the Int
            // out-of-range reading are the SAME machine predicate in two
            // renderings. PROVE direction — conjoining can only SHRINK the
            // violation's SAT set, so every previously-proved row stays proved.
            // REFUTE direction — the only conjuncts over the core's REAL operand
            // vars are drop-only facts true on every reaching execution, so a
            // genuinely overflowing execution models the whole conjunction; the
            // core goes UNSAT only when those facts bound `a*b` into range, i.e.
            // exactly when no real overflow exists. The SIGNED var*var path is
            // UNCHANGED (its Int reading needs the two-sided signed core and its
            // own spec treatment).
            if !signed {
                let lhs_f = operand_to_formula(func, lhs);
                let rhs_f = operand_to_formula(func, rhs);
                let result = Formula::Mul(Box::new(lhs_f), Box::new(rhs_f));
                let out_of_range = Formula::Or(vec![
                    Formula::Lt(
                        Box::new(result.clone()),
                        Box::new(crate::range::type_min_formula(width, false)),
                    ),
                    Formula::Gt(
                        Box::new(result),
                        Box::new(crate::range::type_max_formula(width, false)),
                    ),
                ]);
                // Trust: SAME-BLOCK COPY TIES (2026-09-18) — the g7 false
                // refutation. The Int core reads the operands AT THE MULTIPLY'S
                // OWN USE POINT, and this was the only Int-reading overflow arm
                // that conjoined nothing the multiply's own block establishes
                // before that point; only CROSS-block path defs reached the row,
                // later, in the safety loop. So an operand that is a same-block
                // COPY of a guarded value had no tie to it. Debug rustc keeps
                // exactly that copy for a reassigned parameter under a
                // short-circuit guard —
                // `pub fn g7(a: u64, mut b: u64) -> u64 { if a < 1000 && b < 1000 { b = a * b; } b }`:
                //
                //   bb1: _5 = copy _2; _4 = Lt(move _5, 1000); switch _4 ..
                //   bb2: _6 = copy _2; _7 = CheckedMul(copy _1, copy _6); assert(!_7.1) ..
                //
                // `_5 == b` and `_5 < 1000` arrive as path facts, `_6 == b` never
                // did, so the core read `a * _6` with `_6` FREE and the row was
                // refuted at `_6 = 2^63` — valid Rust, rejected. The `-O` MIR
                // multiplies `_2` directly, which is why the same function
                // compiled in release and not in debug.
                //
                // COPY TIES ONLY, not the full block-defs the Int path below
                // conjoins: this row is a MIXED BV + Int query, and dragging the
                // block's other computations into the Int core takes it out of
                // the fragment `trust-router`'s disjoint-component lane refutes
                // in. Measured: the unrestricted conjoin turns the genuine
                // `(x ^ y | 7) * x` overflow of
                // `path_guard_collapse_cost_real_mir` from `Failed`-with-witness
                // into `Unknown`, and moves that file's size pin off 77. A copy
                // tie is one `Eq` between two reads; it renames, it never
                // computes, and a block that computes its operands rather than
                // copying them gets nothing. See
                // `block_defs::v2_formula_with_copy_ties_at_point_recorded` for
                // the soundness argument and the establish-point versioning that
                // keeps a tie whose source is overwritten before the multiply
                // (`b = c; t = copy b; a * t`) name-disjoint and therefore
                // pruned.
                //
                // The ties join the row's EXISTING flat conjunct list rather than
                // wrapping the core in an `And` of their own: the interval backend
                // reads this row as a list of facts plus one goal atom, and an extra
                // level of nesting around the goal hides it (measured — the wrapped
                // form left `g7` at `Unknown` with the ties present and unusable).
                // One `ConjoinFactsLast` wrapper over `ties ++ terms` still
                // reconstructs the formula bit-for-bit, which is the authentication
                // invariant.
                //
                // The ties alone do NOT finish the job, and the other half is the
                // SAME lost tie in the other rendering: the dominating `< 1000` is
                // keyed on the guard's own copy `_5`, so nothing bounds the operand
                // under ITS name. `v2_int_mul_dominating_guard_constraints` renders
                // the operand-resolved facts in Int beside the BV terms above —
                // that is the spelling the deployed interval backend reads a bound
                // out of, and the Int core reads the operand directly.
                terms.extend(v2_int_guard_constraints_from_facts(&mul_dom_facts));
                let end = stmt_index.unwrap_or(block.stmts.len());
                let (_, rec_body, ties) =
                    v2_formula_with_copy_ties_at_point_recorded(func, block, end, out_of_range);
                terms.push(bv_formula);
                let mut facts = ties;
                facts.extend(terms);
                let mut conjuncts = Vec::with_capacity(facts.len() + 1);
                conjuncts.extend_from_slice(&facts);
                conjuncts.push(rec_body.clone());
                return Some(VerificationCondition {
                    kind: VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) },
                    function: func.name.as_str().into(),
                    location: span.clone(),
                    formula: Formula::And(conjuncts),
                    contract_metadata: None,
                    obligation: Some(ObligationRecord {
                        body: rec_body,
                        wrappers: vec![ObligationWrapper::ConjoinFactsLast { facts }],
                        subject: None,
                        width: Some(width),
                    }),
                });
            }
            let formula = if terms.is_empty() {
                bv_formula
            } else {
                terms.push(bv_formula);
                Formula::And(terms)
            };
            return Some(VerificationCondition {
                kind: VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) },
                function: func.name.as_str().into(),
                location: span.clone(),
                formula,
                contract_metadata: None,
                obligation: None,
            });
        }
        // Operands could not be encoded as BV terms (e.g. symbolic), or the
        // signed width is capped (i128); fall through to the Int path. Sound,
        // but mul there is NIA / likely Unknown.
    }

    let lhs_f = operand_to_formula(func, lhs);
    let rhs_f = operand_to_formula(func, rhs);
    let lhs_range = crate::range::input_range_constraint(&lhs_f, width, signed);
    let rhs_range = crate::range::input_range_constraint(&rhs_f, width, signed);

    let result = match op {
        BinOp::Add => Formula::Add(Box::new(lhs_f), Box::new(rhs_f)),
        BinOp::Sub => Formula::Sub(Box::new(lhs_f), Box::new(rhs_f)),
        BinOp::Mul => Formula::Mul(Box::new(lhs_f), Box::new(rhs_f)),
        _ => {
            return Some(unsupported_mir_vc(
                func,
                "Rvalue::CheckedBinaryOp".to_string(),
                format!("bb{}: checked {op:?} overflow semantics are not modeled", block.id.0),
                span.clone(),
            ));
        }
    };

    let min_f = crate::range::type_min_formula(width, signed);
    let max_f = crate::range::type_max_formula(width, signed);
    let out_of_range = if !signed && matches!(op, BinOp::Sub) {
        // UNSIGNED subtraction overflows ONLY by underflow (`result < 0`): the
        // mathematical result `lhs - rhs <= lhs <= max`, so the `result > max`
        // disjunct is tautologically false here. Dropping it is sound (removes an
        // unsatisfiable case) AND removes the `u64::MAX`/`usize::MAX` literal,
        // which ay's i64 integer domain cannot represent — its presence makes ay
        // return Unknown even on guarded, provably-safe code (e.g. the early-
        // return-guarded `haystack.len() - needle.len()`). The retained `< 0`
        // underflow check carries no oversize literal, so a captured guard
        // `needle.len() <= haystack.len()` discharges it.
        Formula::Lt(Box::new(result), Box::new(min_f))
    } else {
        Formula::Or(vec![
            Formula::Lt(Box::new(result.clone()), Box::new(min_f)),
            Formula::Gt(Box::new(result), Box::new(max_f)),
        ])
    };

    let body = Formula::And(vec![lhs_range, rhs_range, out_of_range]);
    // Direct and checked-BinaryOp callers pass the statement index so defs are
    // taken BEFORE the operation (not the whole block, which would include the
    // op's own result definition or later operand reassignments).
    //
    // Trust (arith ARM, 2026-07-31): use the RECORDED block-defs helper — its `.0` is
    // byte-identical to the previous `v2_formula_with_block_defs{_before_stmt}` (both are
    // `v2_formula_with_block_defs_at_point(..end..)`, `end = stmt_index.unwrap_or(len)`),
    // so `formula` is UNCHANGED, and its `rec_body`/`kept` seed the authenticated
    // obligation (atomic out-of-range core, operand ranges + block-defs demoted to
    // ConjoinFactsLast wrappers). `width` from `int_op_type` (real operand width).
    let end = stmt_index.unwrap_or(block.stmts.len());
    let (formula, rec_body, kept) =
        v2_formula_with_block_defs_at_point_recorded(func, block, end, body);
    let mut vc = VerificationCondition {
        kind: VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) },
        function: func.name.as_str().into(),
        location: span.clone(),
        formula,
        contract_metadata: None,
        obligation: v2_arith_overflow_seed_record(rec_body, kept, width),
    };
    // The four construction-time conjoins the direct/checked BinaryOp Int path applies.
    // Each is a pure `And([facts.., formula])` push (facts LAST) or identity, so mirror
    // each onto the recorded obligation as a `ConjoinFactsLast` via `ob_record_conjoin_wrap`
    // — the SAME mechanism the shared safety loop uses for bounds VCs — keeping
    // `reconstruct(record)` byte-identical to `formula`. The shared loop later applies +
    // mirrors its OWN copy of the same four onto the returned VC (the pre-existing double
    // application; the emitted formula is UNCHANGED here). No-op when the seed is `None`.
    //
    // Bound any parameter that entered the VC only via a conjoined block definition,
    // non-parameter integer locals/temps (excluding the checked op's own result copy
    // closure — see `checked_arith_result_value_vars`), fixed-width-integer datatype
    // fields, and slice/array length terms in a single fused pass (`RangeBatteryClass::Arithmetic`).
    {
        let formula = std::mem::replace(&mut vc.formula, Formula::Bool(true));
        let mut ob = vc.obligation.as_mut();
        vc.formula = conjoin_type_range_battery(
            func,
            formula,
            RangeBatteryClass::Arithmetic,
            &mut |before, after| {
                if let Some(ob) = ob.as_deref_mut()
                    && let Some(facts) = extract_conjoined_facts(before, after)
                    && !facts.is_empty()
                {
                    ob.wrappers
                        .push(ObligationWrapper::ConjoinFactsLast { facts: facts.to_vec() });
                }
            },
        );
    }
    Some(vc)
}

/// Build the fixed-width bitvector OVERFLOW (failure) condition for an
/// UNSIGNED `lhs OP rhs` of width `width` bits.
///
/// The returned formula is the failure condition the VC asserts: the solver
/// proving it UNSAT = "no overflow proved"; a SAT model = a verified
/// overflow counterexample. All terms are the SAME `width`-bit BV sort, so the
/// whole formula lives in a single BV theory — no Int subterms, no
/// zero-extend/extract (TrustSpec lacks those and the same-width idioms below
/// don't need them).
///
/// Soundness of each idiom (let `w = width`, values in `[0, 2^w)`):
///   * add: `a + b` overflows ⟺ `bvult(bvadd(a,b), a)`.
///       bvadd is mod-2^w. If no overflow, `a + b < 2^w` so `bvadd(a,b) = a+b ≥ a`.
///       If overflow, `bvadd(a,b) = a+b-2^w`; since `b < 2^w`, `a+b-2^w < a`. Iff.
///   * sub: `a - b` underflows ⟺ `bvult(a, b)`. Exact by definition of unsigned sub.
///   * mul: `a * b` overflows ⟺ `a ≠ 0 ∧ bvudiv(bvmul(a,b), a) ≠ b`.
///       If `a = 0` the true product is 0 — never overflows — hence the guard.
///       For `a ≠ 0`: if no overflow, `bvmul(a,b) = a*b` exactly so
///       `bvudiv(a*b, a) = b`. If overflow, the truncated product divided by `a`
///       cannot recover `b`. Standard hardware mul-overflow check.
///
/// Variable naming: the BV operand terms use FRESH names distinct from the
/// Int-sorted names the rest of the VC pipeline uses (`__trust_ovf_bv_*`).
/// This is REQUIRED for soundness: the caller later conjoins Int-sorted
/// preconditions/guards/block-defs (built via `operand_to_formula`, which
/// emits `Sort::Int` vars) onto this formula. Reusing the operands' real names
/// would put the same symbol at two sorts (Int and BitVec) in one formula,
/// which `ay_bridge::formula_to_expr` would declare twice with conflicting
/// sorts. Using fresh names keeps the BV sub-formula self-contained.
///
/// Trade-off (documented for the main session): because the BV operands are
/// fresh/unconstrained, precondition- or guard-implied bounds on the real
/// operands do NOT restrict them here. So a case that cannot overflow only
/// because of a precondition may report Failed (overflow possible) instead of
/// Proved. This is a COMPLETENESS loss (conservative false-Failed), never a
/// SOUNDNESS loss — we never mark a real overflow "Proved".
pub(super) fn v2_unsigned_bv_overflow_formula(
    func: &VerifiableFunction,
    lhs: &Operand,
    rhs: &Operand,
    op: BinOp,
    width: u32,
) -> Option<Formula> {
    if width == 0 {
        return None;
    }
    let a = v2_bv_operand_term(func, lhs, width, "lhs")?;
    let b = v2_bv_operand_term(func, rhs, width, "rhs")?;

    let formula = match op {
        // bvult(bvadd(a, b), a)
        BinOp::Add => Formula::BvULt(
            Box::new(Formula::BvAdd(Box::new(a.clone()), Box::new(b), width)),
            Box::new(a),
            width,
        ),
        // bvult(a, b)
        BinOp::Sub => Formula::BvULt(Box::new(a), Box::new(b), width),
        // a != 0  AND  bvudiv(bvmul(a, b), a) != b
        BinOp::Mul => {
            let zero = Formula::BitVec { value: 0, width };
            let a_ne_zero =
                Formula::Not(Box::new(Formula::Eq(Box::new(a.clone()), Box::new(zero))));
            let prod = Formula::BvMul(Box::new(a.clone()), Box::new(b.clone()), width);
            let recovered = Formula::BvUDiv(Box::new(prod), Box::new(a), width);
            let mismatch = Formula::Not(Box::new(Formula::Eq(Box::new(recovered), Box::new(b))));
            Formula::And(vec![a_ne_zero, mismatch])
        }
        _ => return None,
    };
    Some(formula)
}

/// Build the fixed-width bitvector OVERFLOW (failure) condition for a SIGNED
/// `lhs * rhs` of `width` bits, via the exact two's-complement width-doubling
/// check.
///
/// Soundness (let `w = width`): sign-extend both operands to `2w` bits and form
/// the exact `2w`-bit product `p` (a `2w`-bit product of `w`-bit signed values
/// never truncates, so `p` is the true mathematical product). `p` is
/// representable in `w` signed bits IFF its top `w+1` bits all equal the result
/// sign bit — i.e. the slice `p[2w-1 : w-1]` (which is `w+1` bits wide) is
/// all-zeros (nonnegative, fits) or all-ones (negative, fits). The VC asserts
/// the NEGATION (overflow): the solver proving it UNSAT = "no signed overflow
/// proved"; a SAT model = a verified `w`-bit signed-overflow counterexample.
/// This is the standard `bvsmulo` expansion; ay's SMT-LIB text frontend does not
/// parse `bvsmulo`, so we emit the plain QF_BV expansion (sign_extend / bvmul /
/// extract / =), all of which print via smtlib.rs and decide via ay's complete
/// BV bit-blaster. EXACT — it can never report Proved for a real overflow.
///
/// Operand encoding and the fresh-name / widening trade-off are shared with the
/// unsigned path (see `v2_unsigned_bv_overflow_formula` and `v2_bv_operand_term`).
pub(super) fn v2_signed_bv_overflow_formula(
    func: &VerifiableFunction,
    lhs: &Operand,
    rhs: &Operand,
    width: u32,
) -> Option<Formula> {
    if width == 0 {
        return None;
    }
    // The width-doubling product is a `2*width`-bit bvmul. For i128 that is a
    // 256-bit bit-blasted multiplier whose query may not close within the budget.
    // Decline width > 64 and fall back to the Int path (sound: runtime_checked,
    // never false-Proved). i8/i16/i32/i64 (2w = 16/32/64/128) are well within
    // what the unsigned path already solves.
    if width > 64 {
        return None;
    }
    let dw = width.checked_mul(2)?;
    let a = v2_bv_operand_term(func, lhs, width, "lhs")?;
    let b = v2_bv_operand_term(func, rhs, width, "rhs")?;
    // Sign-extend each `width`-bit operand by `width` bits -> `2*width`-bit term.
    let sa = Formula::BvSignExt(Box::new(a), width);
    let sb = Formula::BvSignExt(Box::new(b), width);
    let prod = Formula::BvMul(Box::new(sa), Box::new(sb), dw);
    let high = dw - 1;
    let low = width - 1;
    let slice_w = high - low + 1; // == width + 1
    let slice = Formula::BvExtract { inner: Box::new(prod), high, low };
    let zeros = Formula::BitVec { value: 0, width: slice_w };
    // slice_w == width + 1 <= 65 here (width <= 64), so 2^slice_w - 1 is a
    // positive i128; the SMT layer masks it to the `slice_w`-bit all-ones value.
    let all_ones = Formula::BitVec { value: (1i128 << slice_w) - 1, width: slice_w };
    let fits = Formula::Or(vec![
        Formula::Eq(Box::new(slice.clone()), Box::new(zeros)),
        Formula::Eq(Box::new(slice), Box::new(all_ones)),
    ]);
    Some(Formula::Not(Box::new(fits)))
}

/// Build the fixed-width bitvector OVERFLOW (failure) condition for a SIGNED
/// `lhs OP rhs` (`OP` in Add/Sub) of `width` bits: the sign-bit test
/// `trust_types::signed_bv_addsub_overflow_sign_test` (the negation of
/// `BvAdd/BvSubNoOverflowSigned`), over the encoded operands.
///
/// The predicate uses ONLY `BvULt` + `BvAdd`/`BvSub` at the operand width +
/// `And`/`Or`/`Not` + `BitVec` — the SAME op family the native typed-CHC lane proves
/// for the neg/shift checks (`v2_signed_bv_neg_overflow_formula`, the `BvShl`
/// block-defs). It REPLACED the `w+1`-bit sign-extension / bit-extraction form,
/// which that lane returns `Unsupported` for — exactly why `signed_max`'s trailing
/// `_5 - 1` (`Overflow(Sub)`) stayed UNKNOWN while `signed_min`'s `-_5` proved. Both
/// forms are the EXACT two's-complement overflow predicate (see the exhaustive
/// `w=8` cross-check in `signed_128_overflow_tests.rs`). The VC asserts the
/// overflow: the solver proving it UNSAT = "no signed overflow proved"; a SAT model
/// = a verified `w`-bit signed add/sub-overflow counterexample. It can never report
/// Proved for a real overflow.
///
/// The predicate is single-sourced in trust-types because its consumers match it:
/// trust-certify's signed-BV lane and trust-router's structural twin discharge a
/// row by the operands' bounds only when the row asserts exactly this predicate as
/// top-level conjuncts (`trust_types::asserted_signed_bv_addsub_overflows`).
///
/// Unlike the signed MUL check (which needs a `2w`-bit multiplier and so declines
/// `w > 64`), this needs no wider bits, so it is cheap and is the ROUTE for
/// signed 128-bit add/sub (which the native LIA path cannot represent — its i64
/// constant lane rejects the ±2^127 range bounds).
///
/// Operand encoding and the fresh-name / widening trade-off are shared with the
/// mul path (see `v2_signed_bv_overflow_formula` and `v2_bv_operand_term`).
pub(crate) fn v2_signed_bv_addsub_overflow_formula(
    func: &VerifiableFunction,
    lhs: &Operand,
    rhs: &Operand,
    op: BinOp,
    width: u32,
) -> Option<Formula> {
    if width == 0 || width > 128 || !matches!(op, BinOp::Add | BinOp::Sub) {
        return None;
    }
    let a = v2_bv_operand_term(func, lhs, width, "lhs")?;
    let b = v2_bv_operand_term(func, rhs, width, "rhs")?;
    trust_types::signed_bv_addsub_overflow_sign_test(a, b, matches!(op, BinOp::Add), width)
}

/// Build the fixed-width bitvector NEGATION-OVERFLOW (failure) condition for a
/// SIGNED `-x` of `width` bits: `-x` overflows IFF `x == INT_MIN` (the single
/// `w`-bit signed value whose negation `2^(w-1)` is unrepresentable).
///
/// The VC asserts the failure (`x == bv_signed_min`): the solver proving it UNSAT
/// = "no negation overflow proved"; a SAT model = the verified `x = INT_MIN`
/// counterexample. EXACT — this is byte-for-byte the negation of the native
/// `BvNegNoOverflow` predicate (`a != INT_MIN`). Routes signed 128-bit neg, which
/// the native LIA path cannot represent (the `INT_MIN = -2^127` literal does not
/// fit i64).
pub(crate) fn v2_signed_bv_neg_overflow_formula(
    func: &VerifiableFunction,
    operand: &Operand,
    width: u32,
) -> Option<Formula> {
    if width == 0 || width > 128 {
        return None;
    }
    let x = v2_bv_operand_term(func, operand, width, "neg")?;
    // INT_MIN for a `width`-bit signed BV is the sign bit set: `1 << (width-1)`.
    // For width == 128 this is 2^127, which does NOT fit `i128`; the `BitVec`
    // value field is `i128`, so build it as the two's-complement bit pattern via
    // the masking the SMT layer applies: `i128::MIN` has exactly the top bit set
    // in a 128-bit field. For width < 128, `1i128 << (width-1)` fits.
    let int_min = if width == 128 {
        Formula::BitVec { value: i128::MIN, width }
    } else {
        Formula::BitVec { value: 1i128 << (width - 1), width }
    };
    Some(Formula::Eq(Box::new(x), Box::new(int_min)))
}

/// Translate the BLOCK-DEFINITIONS and dominating path-bounds that constrain a
/// signed-BV overflow VC's plain-local operands into BV facts, so a value that is
/// safe ONLY because of a defining shift/cast (`signed_max`'s `_5 = 1i128 <<
/// (width-1)`, then `_5 - 1`) PROVES instead of false-FAILing on the fresh,
/// unconstrained BV operand var.
///
/// The returned facts are conjoined onto the self-contained BV violation formula.
/// SOUNDNESS: every emitted fact is TRUE on every reaching execution (it mirrors a
/// real block-def equality or a dominating guard bound), so conjoining can only
/// remove INFEASIBLE counterexamples — it can flip Failed -> Proved when no real
/// overflow exists, NEVER mask a real one. Any shape we cannot render EXACTLY in
/// BV is OMITTED (sound: at worst the prove fails / stays Failed).
///
/// Covered, exactly:
///   * a bare-local operand whose UNIQUE in-block defining statement is
///     `dest = Shl(const_base, amount_local)` over an integer type: emit
///     `bv_operand == bvshl(BitVec(base), zext(amount_bv))` plus the dominating
///     bound on `amount` (`amount < width`) when present, AND `amount`'s own
///     defining `Sub`/`Add`/`Cast`/copy (so `_6 = width - 1` threads through).
/// Everything else is omitted.
/// BV-render the SIGNED-accumulator bound onto the fresh `__trust_ovf_bv_*` operand vars of a
/// signed-128 reduction add `acc = acc + addend`, so the i128 add-overflow check discharges.
///
/// The global `build_accumulator_bound_facts` emits `acc ∈ [init, init+K·per_max]` and
/// `addend ∈ [0, per_max]` as INT-sorted facts — but the BV overflow core deliberately uses fresh
/// BV operand vars disjoint from the Int vars (see `v2_bv_operand_term`), so those Int facts never
/// bind. This renders the SAME true bounds in signed BV via the already-sound `v2_bv_guard_constraint`
/// (the channel the guard/precondition lanes use), conjoined onto `__trust_ovf_bv_lhs_{acc}` /
/// `__trust_ovf_bv_rhs_{addend}`. With `acc ≤ bound` and `addend ≤ per_max`, `acc+addend ≤
/// bound+per_max`; for a reduction that provably can't overflow (`bound ≪ i128::MAX`) the BV
/// overflow formula is UNSAT → PROVED.
///
/// SOUNDNESS: the conjoined bounds are TRUE on every reaching path (the same facts the Int lane
/// emits, gated by the same `block_execution_bound`/`addend_per_iteration_bound`/
/// `accumulator_bound_init_const` recognition that excludes call-clobbered / mutably-aliased /
/// parameter-entry-valued / unbounded
/// reductions), rendered via the validated signed-BV helper. SELF-LIMITING: a genuinely-overflowing
/// reduction has `bound > i128::MAX`, so the `acc ≤ bound` constraint does NOT remove the overflow
/// model and it stays refutable.
pub(super) fn v2_signed_bv_accumulator_constraints(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    lhs: &Operand,
    rhs: &Operand,
    width: u32,
) -> Vec<Formula> {
    let (Operand::Copy(acc_p) | Operand::Move(acc_p)) = lhs else { return Vec::new() };
    let (Operand::Copy(rhs_p) | Operand::Move(rhs_p)) = rhs else { return Vec::new() };
    if !acc_p.projections.is_empty() || !rhs_p.projections.is_empty() {
        return Vec::new();
    }
    // Locate the CheckedAdd `ck_dest = CheckedAdd(acc, addend)` (matched by operand locals, since
    // `Operand` is not `PartialEq`) to recover `ck_dest` for the accumulator-init check.
    let op_local = |op: &Operand| match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
        _ => None,
    };
    let Some(ck_dest_local) = block.stmts.iter().find_map(|stmt| match stmt {
        Statement::Assign { place, rvalue: Rvalue::CheckedBinaryOp(BinOp::Add, l, r), .. }
            if op_local(l) == Some(acc_p.local)
                && op_local(r) == Some(rhs_p.local)
                && place.projections.is_empty() =>
        {
            Some(place.local)
        }
        _ => None,
    }) else {
        return Vec::new();
    };
    let Some(k) = block_execution_bound(func, block.id.0) else { return Vec::new() };
    let Some(per_max) = addend_per_iteration_bound(func, rhs_p.local) else {
        return Vec::new();
    };
    let Some(init_c) = accumulator_bound_init_const(func, acc_p.local, ck_dest_local) else {
        return Vec::new();
    };
    let Some(bound) = k.checked_mul(per_max).and_then(|nm| init_c.checked_add(nm)) else {
        return Vec::new();
    };
    let acc_bv = format!("__trust_ovf_bv_lhs_{}", crate::place_to_var_name(func, acc_p));
    let rhs_bv = format!("__trust_ovf_bv_rhs_{}", crate::place_to_var_name(func, rhs_p));
    let mut out = Vec::new();
    for (bv, lo, hi) in [(&acc_bv, init_c, bound), (&rhs_bv, 0i128, per_max)] {
        if let Some(f) = v2_bv_guard_constraint(bv, BvGuardCmp::Ge, lo, width, true) {
            out.push(f);
        }
        if let Some(f) = v2_bv_guard_constraint(bv, BvGuardCmp::Le, hi, width, true) {
            out.push(f);
        }
    }
    out
}

/// BV-render the LOOP-VAR YIELD bound for `for y in start..end` onto the fresh
/// `__trust_ovf_bv_*` operand vars of an overflow check — so a flattened 2D index's `y*W`
/// [overflow:mul] (BV-encoded, usize) discharges. Mirrors `v2_bv_mul_dominating_guard_constraints`
/// but the bound source is the exclusive-range yield invariant, not a dominating guard.
///
/// WHAT IS ACTUALLY EMITTED is a SUBSET of `start <= y < end`, not the pair:
///
///  * `y < end` — always (`loop_var_const_range` declines outright unless `end` is a constant
///    operand, so reaching this point means `end` is known);
///  * `start <= y` — ONLY when `start` is a CONSTANT operand too. `loop_var_const_range` returns
///    `start` as an `Option<i128>`: a non-const lower bound (`for y in k..end`) is `None` and no
///    lower bound is rendered at all. That `None` is the tracer's "no const start recovered"
///    signal, not a withheld fact — see the note on the `Ge` arm below and `RangeOrigin`.
///
/// Either constraint is additionally dropped when `v2_bv_guard_constraint` declines the constant
/// for this width (width 0 / > 128, or a constant outside the type range).
///
/// SOUNDNESS: `y` is the Some-payload of `Range::next`, single-assigned (`loop_var_const_range` uses
/// `unique_value_def`), so `start <= y < end` holds at every read — each half rendered, when it is
/// rendered, via the validated `v2_bv_guard_constraint`. Emitting only a subset is the monotone
/// direction: fewer hypotheses can turn a PROVE into a FAIL, never the reverse. SELF-LIMITING: a mul
/// that can still overflow given `y < end` (huge end) is not prevented; a reassigned operand
/// (assigned in this block) is skipped.
pub(super) fn v2_bv_yield_constraints(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    lhs: &Operand,
    rhs: &Operand,
    width: u32,
    signed: bool,
) -> Vec<Formula> {
    if !body_has_iterator_next(func) {
        return Vec::new();
    }
    let mut out = Vec::new();
    for (op, role) in [(lhs, "lhs"), (rhs, "rhs")] {
        let (Operand::Copy(p) | Operand::Move(p)) = op else { continue };
        if !p.projections.is_empty()
            || crate::local_defs::is_parameter(func, p.local)
            || block
                .stmts
                .iter()
                .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == p.local))
        {
            continue;
        }
        let Some((start, end)) = loop_var_const_range(func, p.local) else { continue };
        if guards::value_local_is_unstable(func, p.local) {
            continue;
        }
        if v2_widening_bv_source(func, op, width).is_some() {
            continue;
        }
        let base = crate::place_to_var_name(func, p);
        let bv = format!("__trust_ovf_bv_{role}_{base}");
        // Trust (2026-09-16): `start` is ADMITTED across the iterator origin hop — under
        // `iter_mut_borrows_only_feed_next` the local's only mutation is std
        // `Iterator::next` on itself, which consumes from the constructor's yield set
        // (`start <= v < end`) and never adds to it, so `Ge start` is a yield-set fact
        // with the same force as `Lt end` (argument on `iterator_yield::RangeOrigin`).
        // The `Option` here is the tracer's own "no range aggregate found" signal, not
        // a withheld bound.
        if let Some(start) = start
            && let Some(f) = v2_bv_guard_constraint(&bv, BvGuardCmp::Ge, start, width, signed)
        {
            out.push(f);
        }
        if let Some(f) = v2_bv_guard_constraint(&bv, BvGuardCmp::Lt, end, width, signed) {
            out.push(f);
        }
    }
    out
}

/// BV-render the REMAINDER bound of a mul operand uniquely defined as
/// `x % C` (constant `C > 0`) onto its fresh `__trust_ovf_bv_*` var — so the
/// ubiquitous range-clamping idiom `(a % 100) * (b % 50)` PROVES instead of
/// false-Failing on unconstrained fresh BV operands (whose counterexample was
/// visibly inconsistent: `a = 0, b = 0` next to `bv_lhs = u32::MAX`). The Int
/// side already carries the mod bound (`build_global_invariant_facts`), but
/// those Int-sorted facts share no variable with the BV core and CANNOT cross
/// the sort boundary — this is the BV channel, exactly parallel to the
/// dominating-guard and loop-yield channels above.
///
/// SOUNDNESS: for unsigned `r = x % C` (C > 0), `r < C` holds for every defined
/// result. For signed, Rust's `%` truncates toward zero with the DIVIDEND's
/// sign, so `-(C-1) <= r <= C-1`. Both are unconditional facts of the defining
/// statement; constraining a fresh var with a true fact only removes infeasible
/// counterexamples (monotone — can flip false-Fail to Prove, never mint a false
/// Prove). Gated on `unique_value_def` (a reassigned local has no single
/// defining rem) and on the operand NOT being a widening-cast source (those are
/// structurally encoded already, and the fresh-var name would not match).
pub(super) fn v2_bv_rem_constraints(
    func: &VerifiableFunction,
    lhs: &Operand,
    rhs: &Operand,
    width: u32,
    signed: bool,
) -> Vec<Formula> {
    let mut out = Vec::new();
    for (op, role) in [(lhs, "lhs"), (rhs, "rhs")] {
        let (Operand::Copy(p) | Operand::Move(p)) = op else { continue };
        if !p.projections.is_empty() || crate::local_defs::is_parameter(func, p.local) {
            continue;
        }
        let Some(Rvalue::BinaryOp(BinOp::Rem, _, divisor)) =
            crate::local_defs::unique_value_def(func, p.local)
        else {
            continue;
        };
        let Some(c) = const_int_value(divisor) else { continue };
        if c <= 0 || guards::value_local_is_unstable(func, p.local) {
            continue;
        }
        let base = crate::place_to_var_name(func, p);
        let bv = format!("__trust_ovf_bv_{role}_{base}");
        if let Some(f) = v2_bv_guard_constraint(&bv, BvGuardCmp::Lt, c, width, signed) {
            out.push(f);
        }
        if signed && let Some(f) = v2_bv_guard_constraint(&bv, BvGuardCmp::Gt, -c, width, true) {
            out.push(f);
        }
    }
    out
}

pub(crate) fn v2_signed_bv_blockdef_constraints(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    lhs: &Operand,
    rhs: &Operand,
    stmt_index: Option<usize>,
    width: u32,
) -> Vec<Formula> {
    let end = stmt_index.unwrap_or(block.stmts.len());
    let mut out = Vec::new();
    for (op, role) in [(lhs, "lhs"), (rhs, "rhs")] {
        let (Operand::Copy(place) | Operand::Move(place)) = op else {
            continue;
        };
        if !place.projections.is_empty()
            || crate::local_defs::is_parameter(func, place.local)
            || guards::value_local_is_unstable(func, place.local)
        {
            continue;
        }
        // The fresh BV var the violation formula uses for this operand.
        let base = crate::place_to_var_name(func, place);
        let bv_name = format!("__trust_ovf_bv_{role}_{base}");
        v2_collect_bv_shl_blockdef(func, block, end, place.local, &bv_name, width, &mut out);
    }
    out
}

/// The operands of the `CheckedBinaryOp(op, lhs, rhs)` that DEFINES the tuple
/// local the assert's cond reads as its `.1` overflow flag. The hardened assert
/// cond is `Move/Copy(_N.1)`; this returns the operands of the matching
/// `_N = CheckedBinaryOp(op, ..)`, so a block carrying multiple same-`op`
/// statements (a u32 amount sub AND the i128 result sub) selects the ASSERTED one.
/// `None` if the cond is not a `.1` flag, or the live definition is not the
/// matching CheckedBinaryOp. Callers may then use only an independently unique
/// target-block candidate; no path selects the first same-op statement. The
/// returned statement index is part of the authority: formulas and block
/// definitions must be versioned at the operation, not at the terminator after
/// later writes may have changed either operand local.
pub(super) fn v2_find_checked_binop_for_assert_cond<'a>(
    func: &VerifiableFunction,
    block: &'a trust_types::BasicBlock,
    cond: &Operand,
    op: BinOp,
) -> Option<(usize, &'a Operand, &'a Operand)> {
    let cond_place = match cond {
        Operand::Copy(p) | Operand::Move(p) => p,
        _ => return None,
    };
    // Must be the `.1` overflow-flag field of a tuple local.
    if cond_place.projections.len() != 1 {
        return None;
    }
    let trust_types::Projection::Field(1) = &cond_place.projections[0] else {
        return None;
    };
    let tuple_local = cond_place.local;
    if !block.stmts.iter().any(|stmt| {
        matches!(
            stmt,
            Statement::Assign {
                place,
                rvalue: Rvalue::CheckedBinaryOp(stmt_op, ..),
                ..
            } if place.local == tuple_local && place.projections.is_empty() && *stmt_op == op
        )
    }) {
        return None;
    }
    // Trust (m3 `Branching` false refutation): refuse only an address-taken
    // carrier. A mutable borrow / raw address of the tuple (materialized or
    // passed to a call) can write the flag through a pointer the backward walk
    // below does not name, so the checked operation cannot be the proven
    // definition (`checked_overflow_flag_alias_write_cannot_reuse_the_old_safe_operation`).
    // A plain REASSIGNMENT is not a reason to refuse, and the former whole-function
    // store count (`value_local_is_unstable`) left a tuple reused across branches
    // with a free flag. Every direct write that can run between this block's
    // statements and its own terminator is an in-block `Assign` / `SetDiscriminant`
    // / `Deinit` (projected or whole, plus opaque-deref havoc), which
    // `stmt_writes_name` sees in the backward walk. Stores in other blocks and call
    // destinations cannot run between the operation and this terminator, and the
    // returned statement index versions the operands at the operation itself.
    if guards::value_local_is_mut_borrowed(func, tuple_local) {
        return None;
    }
    // Canonical rustc layout: the matching `CheckedBinaryOp` is the final
    // statement before the assert terminator, so no later in-block statement
    // exists and the whole-local tuple assignment always rebinds `_tuple.1`.
    if let Some((
        stmt_index,
        Statement::Assign {
            place,
            rvalue: Rvalue::CheckedBinaryOp(stmt_op, lhs, rhs),
            ..
        },
    )) = block.stmts.iter().enumerate().next_back()
        && place.local == tuple_local
        && place.projections.is_empty()
        && *stmt_op == op
    {
        return Some((stmt_index, lhs, rhs));
    }
    let cond_name = crate::place_to_var_name(func, cond_place);
    // MIR in the public schema is not required to be SSA. The assert observes
    // the last write to `_tuple.1` before the terminator, never the first
    // same-op assignment in the block. Walk backwards and stop at the live
    // whole-local definition or at a direct mutation of the flag field.
    for (stmt_index, stmt) in block.stmts.iter().enumerate().rev() {
        if !stmt_writes_name(func, block, stmt_index, &cond_name) {
            continue;
        }
        let Statement::Assign { place, rvalue, .. } = stmt else {
            return None;
        };
        if place.local == tuple_local && place.projections.is_empty() {
            return match rvalue {
                Rvalue::CheckedBinaryOp(stmt_op, lhs, rhs) if *stmt_op == op => {
                    Some((stmt_index, lhs, rhs))
                }
                _ => None,
            };
        }
        // Any other canonical write overlapping the observed `.1` flag—direct,
        // projected, or through a mutable alias—replaces the checked result.
        return None;
    }
    None
}

/// Build the standalone BV overflow-violation formula for a signed >= 128-bit
/// arithmetic-overflow ASSERT (`Overflow(Add|Sub)` or `OverflowNeg`), for the
/// HARDENED panic_boundary lane. Returns `None` when the assert is NOT a signed
/// >= 128-bit add/sub/neg (so the caller keeps the Int-path
/// `extract_assert_passed_semantics` encoding, which the native i64-LIA lane
/// decides losslessly for widths <= 64).
///
/// WHY this exists (and is the SAME fix as the v2 per-statement path): the Int
/// path's no-overflow predicate carries the type's `±2^127` range bounds
/// (`type_min/max_formula`), which the native typed-CHC lane lowers via
/// `parse_i64` and REJECTS → the obligation is UNSUPPORTED → UNKNOWN. That is
/// exactly why `signed_max`'s trailing `_5 - 1` (`Overflow(Sub)`) and
/// `signed_min`'s `-_5` (`OverflowNeg`) stayed UNKNOWN on the hardened lane. The
/// native BV theory handles the full 128-bit width, so we emit the violation in
/// pure QF_BV (the cheap `w+1`-bit sign-extension add/sub check, or the
/// `x == INT_MIN` neg check), conjoining the BV-rendered block-defs / dominating
/// guard bounds on the operands so a value safe ONLY because of a defining shift
/// (`signed_max`'s `_5 = 1i128 << (width-1)`, then `_5 - 1`) PROVES.
///
/// SOUNDNESS: the returned formula is `block_defs ∧ overflow`, SAT iff a feasible
/// input overflows. Every conjoined block-def fact is TRUE on every reaching path
/// (a real block-def equality or a dominating guard bound, rendered exactly in
/// BV), so conjoining can only remove INFEASIBLE counterexamples — flipping
/// Failed → Proved when no real overflow exists, NEVER masking a real one. An
/// UNGUARDED operand (a free i128 param, no constraining block-def) carries no
/// fact, so a real `i128::MAX - (-1)` / `-(i128::MIN)` / `1<<127 then -1` stays
/// SAT/refutable (the adversarial guardrail). The BV formula uses FRESH
/// `__trust_ovf_bv_*` names disjoint from the Int-sorted vars the rest of the
/// hardened pipeline (preconditions / guards / arg-ranges) emits — so the caller
/// must NOT thread those Int-sorted facts onto this BV core (they share no
/// variable and would only double-declare a symbol at two sorts); the BV
/// block-defs are the sole, sound channel for the constraining facts.
pub(crate) fn v2_hardened_signed_bv_overflow_formula(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    msg: &AssertMessage,
    cond: &Operand,
    expected: bool,
    target: BlockId,
) -> Option<Formula> {
    if expected {
        return None;
    }
    match msg {
        // `Overflow(Add|Sub)`: the assert block IS the CheckedBinaryOp block; the
        // cond is the overflow flag `_N.1`. Recover the operands from the
        // CheckedBinaryOp that defines `_N` — keyed on the assert cond's tuple local,
        // NOT the first matching binop in the block. (A block like signed_max's bb1
        // holds `_6 = width - 1` AND `_9 = CheckedSub(_5, 1)`; keying on `_9` is what
        // selects the i128 sub, not the u32 amount sub.)
        AssertMessage::Overflow(op @ (BinOp::Add | BinOp::Sub)) => {
            let (stmt_index, lhs, rhs) =
                v2_find_checked_binop_for_assert_cond(func, block, cond, *op)?;
            let (width, signed) = int_op_type(func, lhs, rhs)?;
            if !signed || width < 128 {
                return None;
            }
            let bv_formula = v2_signed_bv_addsub_overflow_formula(func, lhs, rhs, *op, width)?;
            let mut terms =
                v2_signed_bv_blockdef_constraints(func, block, lhs, rhs, Some(stmt_index), width);
            if terms.is_empty() {
                Some(bv_formula)
            } else {
                terms.push(bv_formula);
                Some(Formula::And(terms))
            }
        }
        // `OverflowNeg`: require the exact source comparison against the signed
        // minimum and the unique, non-reassigned target Neg operand. A message
        // and target operation alone are not proof authority.
        AssertMessage::OverflowNeg => {
            let operand = v2_find_target_neg_operand(func, target)?;
            let ty = crate::operand_ty_cow(func, operand)?;
            if !ty.is_signed() {
                return None;
            }
            let width = ty.int_width()?;
            if width < 128 {
                return None;
            }
            let (_, BinOp::Eq, lhs, rhs) = v2_find_condition_binary_operands(func, block, cond)?
            else {
                return None;
            };
            let same_runtime_operand = |candidate: &Operand| match (candidate, operand) {
                (Operand::Copy(a) | Operand::Move(a), Operand::Copy(b) | Operand::Move(b)) => {
                    a == b
                }
                _ => false,
            };
            let min = crate::range::signed_min(width);
            if !((same_runtime_operand(lhs) && const_int_value(rhs) == Some(min))
                || (same_runtime_operand(rhs) && const_int_value(lhs) == Some(min)))
            {
                return None;
            }
            let bv_formula = v2_signed_bv_neg_overflow_formula(func, operand, width)?;
            let mut terms = Vec::new();
            if let Operand::Copy(p) | Operand::Move(p) = operand
                && p.projections.is_empty()
                && !crate::local_defs::is_parameter(func, p.local)
                && !guards::value_local_is_unstable(func, p.local)
            {
                let base = crate::place_to_var_name(func, p);
                let bv_name = format!("__trust_ovf_bv_neg_{base}");
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
            // Trust: 2026-09-21 (the 128-bit NEGATION lane) — the hardened twin of
            // the per-statement fix: the DOMINATING GUARD on the negated operand,
            // rendered onto the neg core's own fresh BV var. The block-def walk
            // above speaks only about a local DEFINED IN THIS BLOCK, so a guarded
            // PARAMETER mined nothing and the row refuted at `2^127` on valid Rust.
            terms.extend(v2_bv_neg_dominating_guard_constraints(
                func,
                block,
                operand,
                Some(block.stmts.len()),
                width,
            ));
            if terms.is_empty() {
                Some(bv_formula)
            } else {
                terms.push(bv_formula);
                Some(Formula::And(terms))
            }
        }
        _ => None,
    }
}

/// Emit BV facts for a bare-local operand `target_local` whose defining statement
/// (the LAST assignment to it strictly before `end`, in this block) is a
/// `Shl(const_base, amount)`. The operand's fresh BV var is `bv_name`. Pushes
/// `bv_name == bvshl(BitVec(base), zext(amount_bv))` and the dominating bound on
/// the shift amount. OMITS everything not in the exact shape (sound).
pub(crate) fn v2_collect_bv_shl_blockdef(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    end: usize,
    target_local: usize,
    bv_name: &str,
    width: u32,
    out: &mut Vec<Formula>,
) {
    if crate::local_defs::is_parameter(func, target_local)
        || guards::value_local_is_unstable(func, target_local)
    {
        return;
    }
    // Trust (2026-09-29): a WIDENING-SOURCE operand is excluded, as the yield, rem
    // and dominating-guard channels already exclude it: `v2_bv_operand_term` encodes
    // it as an extension of a fresh var at the NARROWER source width under this very
    // name, so a `width`-bit fact about `bv_name` would declare it at a second sort.
    // MEASURED once `i128::from(x)` became a widening source: `let wide =
    // i128::from(u64::MAX) + 1` declined with "free variable
    // `__trust_ovf_bv_lhs__2` has conflicting sorts BitVec(64) and BitVec(128)". Its
    // range is already in the structure, which is all the add/sub/neg cores need.
    if v2_widening_bv_source(func, &Operand::Copy(Place::local(target_local)), width).is_some() {
        return;
    }
    // Trust: 2026-09-19 (the NEGATION lane's spelling dependence) — the CLOSED
    // CONSTANT EXPRESSION case first, because the `Shl` walk below cannot see it.
    //
    // `if a > -(1i128 << 62) && …` lowers (un-optimized) to `_5 = Shl(const 1i128,
    // const 62i32)` — a shift by a CONSTANT amount. The walk below requires the
    // amount to be a bare LOCAL (it renders `bvshl(base, amt_bv)` and needs a BV var
    // to name), so it declined, `__trust_ovf_bv_neg__5` stayed completely free, and
    // the `OverflowNeg` rows were refuted at `__trust_ovf_bv_neg__5 = 2^127`, i.e.
    // `i128::MIN` — four failed `[negation]` rows on a function that cannot negate
    // `i128::MIN`, because `1i128 << 62` is `2^62`. Resolving the operand as the
    // exact constant it is states the same fact the `Shl` rendering exists to state,
    // in one equality and with no free shift-amount var at all.
    //
    // WHY IT IS SOUND. `v2_const_expr_operand_int` is exact-or-nothing (every step
    // range-checked against its own destination type, no variable anywhere inside,
    // `local_defs::unique_value_def` for the walk, so an aliased, re-assigned or
    // parameter local resolves to NOTHING), and the emitted equality pins the fresh
    // BV var to the literal bit pattern of that value at this width — checked to fit
    // the local's own integer type, whose width must BE `width`, so no truncation or
    // re-signing happens in the rendering. An unresolvable operand pushes nothing and
    // stays refutable, exactly as before: a missing hypothesis can only under-prove.
    if let Some(ty) = crate::local_ty_ref(func, target_local)
        && let Ty::Int { width: local_width, .. } = ty
        && *local_width == width
        && let Some(value) = crate::const_expr::v2_const_expr_operand_int(
            func,
            &Operand::Copy(Place::local(target_local)),
            crate::const_expr::V2_CONST_EXPR_FUEL,
        )
        && crate::const_expr::v2_const_expr_int_fits(ty, value).is_some()
    {
        out.push(Formula::Eq(
            Box::new(Formula::var_owned(bv_name.to_string(), Sort::BitVec(width))),
            Box::new(Formula::BitVec { value, width }),
        ));
        return;
    }
    // Find the LAST canonical write of `target_local` strictly before `end`.
    // A dereference through a separately named `&mut` can write the same local,
    // so local-id comparisons are not an authority boundary here: use exactly
    // the overlap-aware write relation that drives statement versioning.
    // First locate the last direct whole-local assignment to `target_local` in
    // `0..prefix_end` and require it to be `BinaryOp(Shl, const_base, amount)`:
    // any later direct whole-local assignment to `target_local` always writes
    // `target_name`, so a non-`Shl` last direct assignment can never survive.
    let prefix_end = end.min(block.stmts.len());
    let Some((shl_stmt_index, base, amount)) = (0..prefix_end)
        .rev()
        .find_map(|stmt_index| match &block.stmts[stmt_index] {
            Statement::Assign { place, rvalue, .. }
                if place.local == target_local && place.projections.is_empty() =>
            {
                match rvalue {
                    Rvalue::BinaryOp(BinOp::Shl, base, amount) => {
                        Some(Some((stmt_index, base, amount)))
                    }
                    _ => Some(None),
                }
            }
            _ => None,
        })
        .flatten()
    else {
        return;
    };
    // The shifted base must be an integer constant (e.g. `1i128`); a symbolic base
    // is not rendered (sound omission).
    let base_val: i128 = match base {
        Operand::Constant(ConstValue::Int(n)) => *n,
        Operand::Constant(ConstValue::Uint(n, _)) => *n as i128,
        _ => return,
    };
    // The shift amount must be a bare integer local whose BV var we can name. We
    // model it at the SHIFT-RESULT width (`width`) so `bvshl` is well-typed; the
    // amount's true (narrower) type bound is enforced via the dominating
    // `amount < width` guard, so widening it here loses no soundness.
    let (Operand::Copy(amt_place) | Operand::Move(amt_place)) = amount else {
        return;
    };
    if !amt_place.projections.is_empty() {
        return;
    }
    if guards::value_local_is_unstable(func, amt_place.local) {
        return;
    }
    let amt_base = crate::place_to_var_name(func, amt_place);
    // Reject if any statement in `shl_stmt_index + 1..prefix_end` writes an
    // overlapping projection or alias of `target_local` or `amt_place`.
    if shl_stmt_index + 1 < prefix_end {
        let target_name = crate::place_to_var_name(func, &Place::local(target_local));
        if (shl_stmt_index + 1..prefix_end).any(|stmt_index| {
            stmt_writes_name(func, block, stmt_index, &target_name)
                || stmt_writes_name(func, block, stmt_index, &amt_base)
        }) {
            return;
        }
    }
    // The shift-amount BV var, at the shift-result width.
    let amt_bv = Formula::var_owned(format!("__trust_ovf_bv_amt_{amt_base}"), Sort::BitVec(width));
    // `bv_name == bvshl(BitVec(base), amt_bv)`.
    let shifted = Formula::BvShl(
        Box::new(Formula::BitVec { value: base_val, width }),
        Box::new(amt_bv.clone()),
        width,
    );
    out.push(Formula::Eq(
        Box::new(Formula::var_owned(bv_name.to_string(), Sort::BitVec(width))),
        Box::new(shifted),
    ));
    // Dominating bound on the shift amount: the rustc `Shl` ASSERT guards
    // `amount < bits` (here `_6 < 128`), so on EVERY reaching path the amount is
    // `< width`. That bound (rendered `bvult(amt_bv, BitVec(width))`) is what makes
    // `base << amount` a power of two in `[1, 2^(width-1)]` (for base = 1), so
    // `_5 - 1` cannot underflow. Conjoin it as a TRUE dominating fact.
    let amt_bound =
        v2_dominating_shift_amount_bound(func, block, shl_stmt_index, amt_place.local, width);
    if let Some(bound) = amt_bound {
        out.push(bound);
    }
}

/// A guard fact together with the statement of its SOURCE block (the block whose
/// terminator branches on it — the caller's argument) whose value it describes.
///
/// The source point is proof authority.  A syntactically identical `_n < 127`
/// elsewhere in the function (including an unreachable block) says nothing
/// about the value used by the guarded shift.
pub(super) struct V2SourcedGuardFact {
    pub(super) stmt_index: usize,
    pub(super) formula: Formula,
    /// The projection-free place operands the comparison reads, as locals — the only
    /// locals a leaf of `formula` can name. (Trust 2026-10-01: lets the dominating-fact
    /// index map a leaf back to its local without a name search over every local.)
    pub(super) subjects: Vec<usize>,
}

/// The projection-free place operands among `operands`, as locals.
fn v2_place_operand_locals<'a>(operands: impl IntoIterator<Item = &'a Operand>) -> Vec<usize> {
    let mut locals = Vec::new();
    for operand in operands {
        if let Operand::Copy(place) | Operand::Move(place) = operand
            && place.projections.is_empty()
            && !locals.contains(&place.local)
        {
            locals.push(place.local);
        }
    }
    locals
}

// Trust: 2026-09-19 (the NEGATION lane's spelling dependence) — the
// closed-constant-expression resolver that landed here on 2026-09-18 now lives in
// `crate::const_expr`, because `crate::guards` needs it too and is not a child of
// `generate`. Re-exported under its original names so every call site and the
// unit pins in `const_expr_bound_tests` read unchanged. See that module for the
// exactness contract: the value the machine computes, or nothing.
pub(super) use crate::const_expr::{V2_CONST_EXPR_FUEL, v2_const_expr_operand_int};

/// Trust: 2026-09-18 — each side is rendered as its CONSTANT VALUE when it is a
/// closed constant expression rustc left unfolded (`-(1i64 << 31)`), and as its
/// variable otherwise. See [`v2_const_expr_operand_int`] for why a guard whose
/// bound is spelled as an expression must mine the same fact a literal does.
fn v2_comparison_formula(
    func: &VerifiableFunction,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
) -> Option<Formula> {
    let side =
        |operand: &Operand| match v2_const_expr_operand_int(func, operand, V2_CONST_EXPR_FUEL) {
            Some(value) => Box::new(Formula::Int(value)),
            None => Box::new(operand_to_formula(func, operand)),
        };
    let lhs = side(lhs);
    let rhs = side(rhs);
    Some(match op {
        BinOp::Lt => Formula::Lt(lhs, rhs),
        BinOp::Le => Formula::Le(lhs, rhs),
        BinOp::Gt => Formula::Gt(lhs, rhs),
        BinOp::Ge => Formula::Ge(lhs, rhs),
        BinOp::Eq => Formula::Eq(lhs, rhs),
        BinOp::Ne => Formula::Not(Box::new(Formula::Eq(lhs, rhs))),
        _ => return None,
    })
}

/// Resolve a control-flow guard at the block that actually produced it.
///
/// Boolean temporaries are inlined only through the live comparison definition
/// in that source block.  `v2_find_condition_binary_operands` rejects a later
/// direct or aliasing rewrite, so the returned statement point denotes the value
/// observed by the terminator.  We deliberately do not search the whole function
/// by local name: doing so let a dead block manufacture a bound for a live shift.
pub(super) fn v2_sourced_guard_fact(
    func: &VerifiableFunction,
    source: BlockId,
    guard: &trust_types::GuardCondition,
) -> Option<V2SourcedGuardFact> {
    use trust_types::GuardCondition;

    let block = func.body.blocks.get(source.0).filter(|block| block.id == source)?;
    let comparison = |cond: &Operand, truth: bool| -> Option<V2SourcedGuardFact> {
        let (stmt_index, op, lhs, rhs) = v2_find_condition_binary_operands(func, block, cond)?;
        let formula = v2_comparison_formula(func, op, lhs, rhs)?;
        Some(V2SourcedGuardFact {
            stmt_index,
            formula: if truth { formula } else { Formula::Not(Box::new(formula)) },
            subjects: v2_place_operand_locals([lhs, rhs]),
        })
    };

    match guard {
        GuardCondition::AssertHolds { cond, expected } => comparison(cond, *expected),
        GuardCondition::AssertFails { cond, expected, .. } => comparison(cond, !*expected),
        GuardCondition::SwitchIntMatch { discr, value }
            if matches!(
                crate::operand_ty_cow(func, discr).as_deref(),
                Some(trust_types::Ty::Bool)
            ) =>
        {
            comparison(discr, *value != 0)
        }
        GuardCondition::SwitchIntOtherwise { discr, excluded_values }
            if matches!(
                crate::operand_ty_cow(func, discr).as_deref(),
                Some(trust_types::Ty::Bool)
            ) =>
        {
            let excludes_false = excluded_values.contains(&0);
            let excludes_true = excluded_values.iter().any(|value| *value != 0);
            let truth = match (excludes_false, excludes_true) {
                (true, false) => true,
                (false, true) => false,
                _ => return None,
            };
            comparison(discr, truth)
        }
        // A non-boolean SwitchInt guard reads its discriminant at the source
        // terminator.  Its direct formula is safe once the variable's reaching
        // version is checked against the use point below.
        GuardCondition::SwitchIntMatch { discr, .. }
        | GuardCondition::SwitchIntOtherwise { discr, .. } => Some(V2SourcedGuardFact {
            stmt_index: block.stmts.len(),
            formula: guards::guard_to_formula(func, guard),
            subjects: v2_place_operand_locals([discr]),
        }),
        _ => None,
    }
}

/// Tightest strict upper bound on `local` that holds whenever it is read at
/// `(use_block, use_stmt_index)` (see [`dominating_facts`]).
fn v2_dominating_strict_upper_bound(
    func: &VerifiableFunction,
    local: usize,
    use_block: BlockId,
    use_stmt_index: usize,
) -> Option<i128> {
    let mut bound = None;
    // EXACT-NAME lane deliberately: `local` here is a RAW MIR local (the shift
    // amount, or the `amount = source - c` source), never a copy-resolved base.
    // See `dominating_facts::GuardSubject`.
    for &(cmp, constant) in super::dominating_facts_for(func).facts(
        func,
        local,
        use_block,
        use_stmt_index,
        dominating_facts::GuardSubject::ExactName,
    ) {
        let upper = match cmp {
            BvGuardCmp::Lt => Some(constant),
            BvGuardCmp::Le => constant.checked_add(1),
            _ => None,
        };
        if let Some(upper) = upper {
            bound = Some(bound.map_or(upper, |current: i128| current.min(upper)));
        }
    }
    bound
}

/// The dominating upper bound `amount < width` on a shift amount local, rendered
/// in BV (`bvult(amt_bv, BitVec(width))`), IF such a guard dominates this block.
/// trust-vcgen guarantees a `Shl` is reachable only past its `amount < bits`
/// overflow assert; we confirm the bound is present on EVERY recorded path into
/// this block (so it is a TRUE dominating fact, never a fabricated one). Returns
/// `None` (omit, sound) when no dominating `amount < K` (K <= width) guard exists.
pub(super) fn v2_dominating_shift_amount_bound(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    shl_stmt_index: usize,
    amt_local: usize,
    width: u32,
) -> Option<Formula> {
    if !super::dominating_facts_for(func).reachable(block.id) {
        return None;
    }
    let sv = super::stmt_versions_for(func);

    // (1) A direct dominating bound on the shift amount (`_6 < 128` from the SHL
    //     assert), and
    // (2) the SEMANTIC bound threaded through the amount's `_6 = src - c` definition:
    //     if `src` is dominated by `src <= W` then `_6 <= W - c`, i.e. `_6 < W - c +
    //     1`. This is what derives `_6 <= 126` from `width <= 127` (`signed_max`/
    //     `signed_min`'s `_6 = width - 1`), the bound that makes `_5` a power of two in
    //     `[1, 2^126]` so `_5 - 1` / `-_5` provably cannot overflow.
    let mut best = v2_dominating_strict_upper_bound(func, amt_local, block.id, shl_stmt_index);
    if let Some((src_local, sub_const, source_block, source_stmt_index)) =
        v2_amount_sub_source_at_use(func, &sv, block.id, shl_stmt_index, amt_local)
        && let Some(src_ub_excl) =
            v2_dominating_strict_upper_bound(func, src_local, source_block, source_stmt_index)
    {
        // src < src_ub_excl  ⇒  src <= src_ub_excl - 1  ⇒  amt = src - c <= src_ub_excl
        // - 1 - c  ⇒  amt < src_ub_excl - c.
        if let Some(derived) = src_ub_excl.checked_sub(sub_const) {
            best = Some(best.map_or(derived, |b: i128| b.min(derived)));
        }
    }

    // The bound is only USEFUL (and well-typed) when `1 <= ub <= width`.
    let ub = best.filter(|&u| u >= 1 && u <= i128::from(width))?;
    let amt_base = crate::place_to_var_name(func, &Place::local(amt_local));
    let amt_bv = Formula::var_owned(format!("__trust_ovf_bv_amt_{amt_base}"), Sort::BitVec(width));
    // `amount < ub`.
    Some(Formula::BvULt(Box::new(amt_bv), Box::new(Formula::BitVec { value: ub, width }), width))
}

/// Recover the exact reaching `amount = source - constant` definition at a Shl
/// use point.  The returned source program point is where `source` was read.
/// Joined, ambiguous, unreachable, or overwritten definitions decline.
fn v2_amount_sub_source_at_use(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    use_block: BlockId,
    use_stmt_index: usize,
    amt_local: usize,
) -> Option<(usize, i128, BlockId, usize)> {
    // Trust: 2026-11-09 (VCGEN-SEAM-PERF-REDS-1) — the amount's ONE value is asked of
    // the seam. `local_defs::unique_value_def` sees every write channel (a `Call`
    // destination beside the `Assign`, a partial or unlocatable write, a mutable alias)
    // and a parameter's ENTRY definition, and answers only when `amt_local` holds
    // exactly one value, written by one whole-local `Assign`; `unique_defining_block`
    // locates it, and the defining statement is the one whose rvalue IS the resolved
    // one. (This was a hand `Assign`-only scan behind `value_local_is_unstable`, whose
    // `Call`-destination count is what kept it sound.)
    let rvalue = crate::local_defs::unique_value_def(func, amt_local)?;
    match rvalue {
        Rvalue::BinaryOp(BinOp::Sub, src, constant) => {
            let (src_local, _) = v2_plain_sub_source(src, constant)?;
            if guards::value_local_is_unstable(func, src_local) {
                return None;
            }
        }
        Rvalue::Use(Operand::Copy(tuple_result) | Operand::Move(tuple_result))
            if tuple_result.projections.len() == 1
                && matches!(tuple_result.projections[0], trust_types::Projection::Field(0)) =>
        {
            if guards::value_local_is_unstable(func, tuple_result.local) {
                return None;
            }
        }
        _ => return None,
    }
    let block = func.body.blocks.get(crate::local_defs::unique_defining_block(func, amt_local)?)?;
    let stmt_index = block.stmts.iter().position(|stmt| {
        matches!(stmt, Statement::Assign { rvalue: defined, .. } if std::ptr::eq(defined, rvalue))
    })?;
    // The definition must be the one the Shl reads.
    let amt_name = crate::place_to_var_name(func, &Place::local(amt_local));
    let use_token = sv.version_token_at(func, use_block, use_stmt_index, &amt_name)?;
    if sv.version_token_at(func, block.id, stmt_index + 1, &amt_name)? != use_token {
        return None;
    }
    let candidate = match rvalue {
        // Trust: 2026-11-09 (WRAPPING-SUB-AND-INTERVAL-NEG-1) — a bare `BinaryOp(Sub)`
        // WRAPS mod 2^w (the checked form is `CheckedBinaryOp` + its assert; see
        // `guards::extract_block_definitions_range_impl` and
        // `assert_refutation::wrapping_binop_modular_ite`). Reading it as mathematical
        // subtraction needs the same cannot-wrap proof the checked arm gets from its
        // assert's success edge, here a dominating lower bound on the source. Without
        // it `if src < 4294967210 { amt = src.wrapping_sub(4294967200); .. }` derived
        // `amt < 10` though `src = 31` gives `amt = 127`, and the 128-bit negation of
        // `1i128 << amt` became UNSAT for every amount.
        Rvalue::BinaryOp(BinOp::Sub, src, constant) => v2_plain_sub_source(src, constant)
            .filter(|&(local, value)| {
                guards::bare_binop_machine_shape(func, &Place::local(amt_local), src, constant)
                    .is_some_and(|(width, signed)| {
                        v2_plain_sub_cannot_wrap(
                            func, local, value, width, signed, block.id, stmt_index,
                        )
                    })
            })
            .map(|(local, value)| (local, value, block.id, stmt_index)),
        Rvalue::Use(Operand::Copy(tuple_result) | Operand::Move(tuple_result))
            if tuple_result.projections.len() == 1
                && matches!(tuple_result.projections[0], trust_types::Projection::Field(0)) =>
        {
            v2_checked_sub_source_at_use(func, block.id, stmt_index, tuple_result)
        }
        _ => None,
    }?;
    (!guards::value_local_is_unstable(func, candidate.0)).then_some(candidate)
}

fn v2_plain_sub_source(src: &Operand, constant: &Operand) -> Option<(usize, i128)> {
    let (Operand::Copy(place) | Operand::Move(place)) = src else {
        return None;
    };
    if !place.projections.is_empty() {
        return None;
    }
    let value = match constant {
        Operand::Constant(ConstValue::Int(value)) => *value,
        Operand::Constant(ConstValue::Uint(value, _)) => i128::try_from(*value).ok()?,
        _ => return None,
    };
    Some((place.local, value))
}

/// Does the WRAPPING `source - constant` read at `(block, stmt_index)` equal the
/// mathematical difference on every execution reaching that read?
///
/// A bare `BinaryOp(Sub)` of a `w`-bit integer computes `(source - constant) mod 2^w`
/// in the type's range. With `constant >= 0` it can only wrap DOWNWARD, and it does
/// so exactly when `source < type_min + constant` (unsigned: `source < constant`;
/// signed: below `MIN + constant`). So it equals the mathematical difference exactly
/// when `source >= type_min + constant`, which must hold on every execution reaching
/// the read: a dominating `source >= L` / `source > L` / `source == L` fact (the same
/// value-identity index the upper bound is read from), or the type's own minimum.
/// `(width, signed)` is the subtraction's machine shape
/// (`guards::bare_binop_machine_shape`: the destination's, which both operands must
/// share). A negative constant (an upward wrap), an unknown shape, or no such bound
/// declines, and the caller then derives nothing from this definition (fail-closed).
fn v2_plain_sub_cannot_wrap(
    func: &VerifiableFunction,
    source: usize,
    constant: i128,
    width: u32,
    signed: bool,
    block: BlockId,
    stmt_index: usize,
) -> bool {
    if constant < 0 {
        return false;
    }
    let type_min = match (signed, width) {
        (false, 1..=128) => 0i128,
        (true, 1..=127) => -(1i128 << (width - 1)),
        (true, 128) => i128::MIN,
        _ => return false,
    };
    let Some(no_wrap_floor) = type_min.checked_add(constant) else {
        return false;
    };
    let guard_floor = v2_dominating_inclusive_lower_bound(func, source, block, stmt_index);
    let floor = guard_floor.map_or(type_min, |lb| lb.max(type_min));
    floor >= no_wrap_floor
}

/// Tightest inclusive lower bound on `local` that holds whenever it is read at
/// `(use_block, use_stmt_index)` (the lower-bound twin of
/// [`v2_dominating_strict_upper_bound`], over the same dominating facts).
fn v2_dominating_inclusive_lower_bound(
    func: &VerifiableFunction,
    local: usize,
    use_block: BlockId,
    use_stmt_index: usize,
) -> Option<i128> {
    let mut bound = None;
    for &(cmp, constant) in super::dominating_facts_for(func).facts(
        func,
        local,
        use_block,
        use_stmt_index,
        dominating_facts::GuardSubject::ExactName,
    ) {
        let lower = match cmp {
            BvGuardCmp::Ge | BvGuardCmp::Eq => Some(constant),
            BvGuardCmp::Gt => constant.checked_add(1),
            _ => None,
        };
        if let Some(lower) = lower {
            bound = Some(bound.map_or(lower, |current: i128| current.max(lower)));
        }
    }
    bound
}

/// Recover the `source - constant` behind a `tuple.0` read of a `CheckedBinaryOp
/// (Sub)` result, authenticated as MATHEMATICAL subtraction at the use point.
///
/// Reaching identity is deliberately NOT established with `version_token_at`: the
/// statement-version oracle derives written names from the block-def extraction,
/// which SKIPS `CheckedBinaryOp` (its `.0` value is only meaningful on the assert
/// success edge), so the oracle is blind to the tuple's own write and reports the
/// entry value on BOTH sides of exactly the canonical `_7 = SubWithOverflow(w, 1);
/// assert(!_7.1); _6 = _7.0` shape — a token pin here can never authenticate the
/// def it exists for. The replacement is structural and at least as strong:
///   * `v2_checked_sub_success_edge_dominates_use` requires the defining block's
///     own `Overflow(Sub)` assert on THIS tuple's live `.1` flag to target
///     `use_block` DIRECTLY and to be an edge every execution reaching it traverses
///     (edge dominance; 2026-10-01 — it was "every recorded path"), so the
///     definition is the immediate predecessor of the use on every path (no
///     intermediate block exists in which the value could be rewritten);
///   * the two `stmt_writes_name` scans below refuse any interposed write that
///     overlaps the `.0` value — after the checked sub in the defining block and
///     before the read in the use block. `stmt_writes_name` sees every `Assign`
///     dest (including the `CheckedBinaryOp` writes the token oracle cannot), and
///     the assert authenticates only the `.1` flag, so a sibling `.0` store
///     between the two points would change the value while keeping the flag
///     authentic — exactly what these scans decline (fail-closed).
fn v2_checked_sub_source_at_use(
    func: &VerifiableFunction,
    use_block: BlockId,
    use_stmt_index: usize,
    tuple_result: &Place,
) -> Option<(usize, i128, BlockId, usize)> {
    if guards::value_local_is_unstable(func, tuple_result.local) {
        return None;
    }
    let use_bb = func.body.blocks.get(use_block.0).filter(|b| b.id == use_block)?;
    let use_prefix_end = use_stmt_index.min(use_bb.stmts.len());
    let mut tuple_name: Option<String> = None;
    let mut found = None;
    let mut invalid = false;
    crate::visit_local_write_indexed_stmts(
        func,
        &func.body.blocks,
        tuple_result.local,
        |block, stmt_index, stmt| {
            if invalid {
                return;
            }
            if !matches!(
                &block.terminator,
                Terminator::Assert {
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Sub),
                    target,
                    ..
                } if *target == use_block
            ) {
                return;
            }
            let Statement::Assign {
                place,
                rvalue: Rvalue::CheckedBinaryOp(BinOp::Sub, src, constant),
                ..
            } = stmt
            else {
                return;
            };
            if place.local != tuple_result.local || !place.projections.is_empty() {
                return;
            }
            if !v2_checked_sub_success_edge_dominates_use(
                func,
                block,
                stmt_index,
                tuple_result.local,
                use_block,
            ) {
                return;
            }
            // No later write in the DEFINING block may overlap the read `.0`
            // value (the assert's reverse scan pins only `.1`-overlapping writes),
            // nor may any write in the USE block before the read point.
            if stmt_index + 1 < block.stmts.len() || use_prefix_end > 0 {
                let tuple_name =
                    tuple_name.get_or_insert_with(|| crate::place_to_var_name(func, tuple_result));
                if (stmt_index + 1..block.stmts.len())
                    .any(|later| stmt_writes_name(func, block, later, tuple_name))
                    || (0..use_prefix_end)
                        .any(|earlier| stmt_writes_name(func, use_bb, earlier, tuple_name))
                {
                    return;
                }
            }
            let Some((source, value)) = v2_plain_sub_source(src, constant) else {
                invalid = true;
                return;
            };
            let candidate = (source, value, block.id, stmt_index);
            if found.replace(candidate).is_some() {
                invalid = true;
            }
        },
    );
    if invalid {
        return None;
    }
    found
}

/// Authenticate a checked subtraction's `.0` value as MATHEMATICAL subtraction.
///
/// `CheckedBinaryOp(Sub)` always computes a wrapping tuple value; `.0 == lhs -
/// rhs` over mathematical integers is valid only on the NORMAL edge of the exact
/// `Assert(tuple.1, expected = false, Overflow(Sub))` that checks its `.1` flag.
/// A caller-built TrustIR body may otherwise ignore the flag and feed the wrapped
/// value to a later shift.  Treating that value as mathematical subtraction can
/// manufacture a false dominating shift bound and make a real i128 overflow
/// UNSAT.  We therefore require both occurrence identity (the assert observes
/// this exact live tuple definition) and every-path dominance of its success edge.
fn v2_checked_sub_success_edge_dominates_use(
    func: &VerifiableFunction,
    defining_block: &trust_types::BasicBlock,
    defining_stmt_index: usize,
    tuple_local: usize,
    use_block: BlockId,
) -> bool {
    let Terminator::Assert {
        cond,
        expected: false,
        msg: AssertMessage::Overflow(BinOp::Sub),
        target,
        ..
    } = &defining_block.terminator
    else {
        return false;
    };
    if *target != use_block {
        return false;
    }
    let (Operand::Copy(flag_place) | Operand::Move(flag_place)) = cond else {
        return false;
    };
    if flag_place.local != tuple_local
        || !matches!(flag_place.projections.as_slice(), [trust_types::Projection::Field(1)])
    {
        return false;
    }
    let Some((authenticated_stmt_index, _, _)) =
        v2_find_checked_binop_for_assert_cond(func, defining_block, cond, BinOp::Sub)
    else {
        return false;
    };
    if authenticated_stmt_index != defining_stmt_index {
        return false;
    }

    // Every execution reaching `use_block` must have taken THIS assert's success edge
    // (`target == use_block`, checked above, so the edge's guard is the
    // `AssertHolds { cond: flag, expected: false }` the tuple's `.1` was tested by).
    // Trust (2026-10-01): decided by EDGE DOMINANCE rather than by scanning every
    // enumerated path into `use_block` — the same question, without the per-row
    // path walk and without the `MAX_PATHS_PER_BLOCK` collapse that answered "no".
    super::dominating_facts_for(func).guarded_edge_dominates(defining_block, use_block)
}

/// Try to read a path fact as `<var> CMP <integer constant>` (either argument
/// order; one level of `Not(...)` normalized by comparison inversion).
/// Flatten a dominating-guard fact into its leaf comparison facts, recursing
/// through `And`. A `(L..=U).contains(&x)` validation guard resolves to a single
/// `And(Ge, Le)`; without flattening, `v2_linear_var_const_fact` drops it (no
/// `And` arm) and both bounds are lost. Non-conjunctive facts pass through.
pub(super) fn v2_flatten_guard_conjuncts(fact: &Formula) -> Vec<&Formula> {
    fn push_flat<'a>(fact: &'a Formula, out: &mut Vec<&'a Formula>) {
        match fact {
            Formula::And(conjuncts) => {
                for c in conjuncts {
                    push_flat(c, out);
                }
            }
            other => out.push(other),
        }
    }
    let mut out = Vec::new();
    push_flat(fact, &mut out);
    out
}

pub(super) fn v2_linear_var_const_fact(fact: &Formula) -> Option<(&str, BvGuardCmp, i128)> {
    use BvGuardCmp::{Eq, Ge, Gt, Le, Lt};
    let invert = |cmp: BvGuardCmp| match cmp {
        Le => Some(Gt),
        Lt => Some(Ge),
        Ge => Some(Lt),
        Gt => Some(Le),
        Eq => None, // `!=` gives no usable bound for the BV translation
    };
    // Integer literal, including the `Neg(Int(c))` wrapper shape contract
    // preconditions carry for negative bounds (`x >= -1000`).
    fn int_const(f: &Formula) -> Option<i128> {
        match f {
            Formula::Int(c) => Some(*c),
            Formula::Neg(inner) => match inner.as_ref() {
                Formula::Int(c) => c.checked_neg(),
                _ => None,
            },
            _ => None,
        }
    }
    fn extract<'f>(
        a: &'f Formula,
        b: &'f Formula,
        cmp: BvGuardCmp,
        mirrored: BvGuardCmp,
    ) -> Option<(&'f str, BvGuardCmp, i128)> {
        match (a, b) {
            (Formula::Var(name, Sort::Int), other) => {
                int_const(other).map(|c| (name.as_str(), cmp, c))
            }
            (other, Formula::Var(name, Sort::Int)) => {
                int_const(other).map(|c| (name.as_str(), mirrored, c))
            }
            _ => None,
        }
    }
    match fact {
        Formula::Le(a, b) => extract(a, b, Le, Ge),
        Formula::Lt(a, b) => extract(a, b, Lt, Gt),
        Formula::Ge(a, b) => extract(a, b, Ge, Le),
        Formula::Gt(a, b) => extract(a, b, Gt, Lt),
        Formula::Eq(a, b) => extract(a, b, Eq, Eq),
        Formula::Not(inner) => {
            let (name, cmp, c) = v2_linear_var_const_fact(inner)?;
            Some((name, invert(cmp)?, c))
        }
        _ => None,
    }
}

/// BV-encode one `<var> CMP <constant>` fact over the fresh BV operand var.
///
/// Exact-fit only: the encoding is used only for constants inside the operand
/// type's value range, where the w-bit BV comparison agrees with the Int
/// comparison for every value the operand can hold. Negative signed constants
/// are emitted as plain `BitVec { value: c, .. }` — both downstream constant
/// paths mask to exact two's complement (the SMT printer masks via
/// `(value as u128) & ((1 << w) - 1)` in trust-types formula/smtlib.rs, and
/// the typed-CHC native lane lands in `ay_bindings::normalize_bitvec_value`,
/// a mod-2^w BigInt normalization), so `bvsle/bvslt` read back exactly `c`.
/// Out-of-range constants are declined — declining is always sound: a weaker
/// violation formula can only under-prove, never mask a real overflow.
pub(super) fn v2_bv_guard_constraint(
    bv_name: &str,
    cmp: BvGuardCmp,
    c: i128,
    width: u32,
    signed: bool,
) -> Option<Formula> {
    // Trust (completeness, signed-128 dominating-guard threading, task #77): handle
    // widths up to 128. The bounds are computed with the overflow-SAFE
    // `range::signed_min/max` (which return i128::MIN/MAX at 128 rather than
    // panicking on `1i128 << 127`); for unsigned width >= 64 the type max exceeds
    // i128 but a guard constant `c` is an i128, so it can never exceed i128::MAX —
    // that is the representable upper bound here. The 129-bit signed add/sub overflow
    // formula already exercises ay's 128-bit BV theory, so a 128-bit BvSLt/BvULt
    // bound is well-formed. SOUND: a guard constraint only REMOVES infeasible
    // counterexamples (monotone); a constant out of the type range is rejected.
    if width == 0 || width > 128 {
        return None;
    }
    let (min, max) = if signed {
        (crate::range::signed_min(width), crate::range::signed_max(width))
    } else if width >= 64 {
        (0, i128::MAX)
    } else {
        (0, (1i128 << width) - 1)
    };
    if c < min || c > max {
        return None;
    }
    let var = Box::new(Formula::var_owned(bv_name.to_string(), Sort::BitVec(width)));
    let bvc = Box::new(Formula::BitVec { value: c, width });
    Some(match (cmp, signed) {
        (BvGuardCmp::Le, false) => Formula::BvULe(var, bvc, width),
        (BvGuardCmp::Lt, false) => Formula::BvULt(var, bvc, width),
        (BvGuardCmp::Ge, false) => Formula::BvULe(bvc, var, width),
        (BvGuardCmp::Gt, false) => Formula::BvULt(bvc, var, width),
        (BvGuardCmp::Le, true) => Formula::BvSLe(var, bvc, width),
        (BvGuardCmp::Lt, true) => Formula::BvSLt(var, bvc, width),
        (BvGuardCmp::Ge, true) => Formula::BvSLe(bvc, var, width),
        (BvGuardCmp::Gt, true) => Formula::BvSLt(bvc, var, width),
        (BvGuardCmp::Eq, _) => Formula::Eq(var, bvc),
    })
}

/// Conjoin BV-encoded DOMINATING path facts about a multiply's plain-local
/// operands into the self-contained BV overflow formula.
///
/// The BV mul violation formula uses FRESH operand vars
/// (`__trust_ovf_bv_{role}_{base}`, see `v2_bv_operand_term`), so the Int-lane
/// path guards wrapped around the VC later never constrain them — the
/// documented conservative false-Failed for a mul that is safe only because of
/// a guard (`if cols <= 4096 { cols * 64 }`). This closes that gap for the
/// common linear case: a `operand CMP integer-constant` fact that holds on
/// EVERY execution reaching the mul is translated into the equivalent BV
/// comparison over the fresh operand var.
///
/// Soundness (Trust 2026-10-01: the facts come from [`dominating_facts`]):
///  * Dominance: a fact comes from a guarded edge that every execution reaching
///    the mul traverses (edge dominance, no path enumeration and so no path cap).
///    A real overflow's witness state therefore satisfies every conjoined fact,
///    so conjoining removes only INFEASIBLE counterexamples — it can flip
///    Failed -> Proved only when no feasible violation exists, never hide one.
///  * Same value: the fact is keyed on the SSA VALUE its subject held at the
///    guard (`version_ssa::ValueId`), and the mul's operand must read that very
///    value — a write between the guard and the mul, on any path, including one
///    around a loop, gives the operand a different value and the fact is not
///    offered.
///  * Exact fit: constants outside the operand type's value range are skipped
///    (see `v2_bv_guard_constraint`); skipping is always sound.
pub(super) fn v2_bv_mul_dominating_guard_constraints(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    lhs: &Operand,
    rhs: &Operand,
    stmt_index: Option<usize>,
    width: u32,
    signed: bool,
) -> Vec<Formula> {
    let facts = v2_mul_dominating_operand_facts(func, block, lhs, rhs, stmt_index, width);
    v2_bv_guard_constraints_from_facts(&facts, width, signed)
}

fn v2_bv_guard_constraints_from_facts(
    facts: &DominatingOperandFacts,
    width: u32,
    signed: bool,
) -> Vec<Formula> {
    let mut constraints = Vec::new();
    for &(target_idx, cmp, constant) in &facts.facts {
        let Some((_, bv_name)) = facts.targets.get(target_idx) else {
            continue;
        };
        if let Some(constraint) = v2_bv_guard_constraint(bv_name, cmp, constant, width, signed)
            && !constraints.contains(&constraint)
        {
            constraints.push(constraint);
        }
    }
    constraints
}

/// Trust: 2026-09-18 (g7 false refutation) — the INT rendering of exactly the
/// facts [`v2_bv_mul_dominating_guard_constraints`] renders in BV, keyed on the
/// operand's OWN Int variable rather than on the fresh BV var.
///
/// The BV constraint alone does not reach the deployed prover for this class.
/// `trust-router`'s interval backend bounds a fresh `__trust_ovf_bv_{role}_{base}`
/// var by looking the recorded NUMERIC bounds of `{base}` up in its Int
/// environment (`IntervalEnv::bound_of`'s prefix fallback); it never reads a
/// `BvULt` atom as a bound. So a guard whose subject is a per-guard COPY of the
/// operand's value left the operand's own name carrying nothing but its type
/// range, and `g7` stayed unproved even with the BV bound present and the Int
/// core's copy tie conjoined — measured, `interval_claims=false` at 113 formula
/// nodes. Rendering the same fact in Int gives `bound_of` something to find, and
/// gives the Int core the bound directly.
///
/// SOUNDNESS is the BV renderer's, unchanged: these are DOMINATING facts (from a
/// guarded edge every execution reaching the multiply traverses), keyed on the SSA
/// value the multiply actually reads, so conjoining them removes only INFEASIBLE
/// counterexamples. A genuinely overflowing execution satisfies every one of them
/// and is still refuted.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn v2_int_mul_dominating_guard_constraints(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    lhs: &Operand,
    rhs: &Operand,
    stmt_index: Option<usize>,
    width: u32,
) -> Vec<Formula> {
    let facts = v2_mul_dominating_operand_facts(func, block, lhs, rhs, stmt_index, width);
    v2_int_guard_constraints_from_facts(&facts)
}

fn v2_int_guard_constraints_from_facts(facts: &DominatingOperandFacts) -> Vec<Formula> {
    let mut constraints = Vec::new();
    for &(target_idx, cmp, constant) in &facts.facts {
        let Some((base, _)) = facts.targets.get(target_idx) else {
            continue;
        };
        let var = Box::new(Formula::var_owned(base.clone(), Sort::Int));
        let c = Box::new(Formula::Int(constant));
        let constraint = match cmp {
            BvGuardCmp::Le => Formula::Le(var, c),
            BvGuardCmp::Lt => Formula::Lt(var, c),
            BvGuardCmp::Ge => Formula::Ge(var, c),
            BvGuardCmp::Gt => Formula::Gt(var, c),
            BvGuardCmp::Eq => Formula::Eq(var, c),
        };
        if !constraints.contains(&constraint) {
            constraints.push(constraint);
        }
    }
    constraints
}

/// Trust: 2026-09-21 (the 128-bit NEGATION lane) — conjoin BV-encoded DOMINATING
/// path facts about the NEGATED operand onto the self-contained signed-BV
/// negation-overflow formula.
///
/// THE DEFECT THIS CLOSES. For a signed width >= 128 the negation obligation is
/// emitted in pure QF_BV (`v2_signed_bv_neg_overflow_formula`), because the Int
/// lane's `INT_MIN = -2^127` literal does not survive the native `parse_i64`
/// lowering. That core names the operand with a FRESH var,
/// `__trust_ovf_bv_neg_{base}`, deliberately disjoint from the Int-sorted `{base}`
/// the guard/precondition lanes emit — so the dominating guard conjoined AROUND
/// the VC could never bind it. The only facts the neg core carried were
/// `v2_collect_bv_shl_blockdef`'s, which speak about a local DEFINED IN THE BLOCK
/// (a defining `Shl`, or a closed constant expression). A PARAMETER has no such
/// definition, so on
///
/// ```ignore (illustrative)
/// pub fn f(a: i128) -> i128 {
///     if a >= -170141183460469231731687303715884105727i128 { -a } else { 0 }
/// }
/// ```
///
/// the fresh var stayed completely FREE and `= 2^127` was always a model:
/// `[negation] FAILED (ay-in-process); counterexample: __trust_ovf_bv_neg_a =
/// 2^127, a = 0` — a strict build error on valid Rust whose bound is a plain
/// literal that excludes `i128::MIN`. The same shape at `i64` reports
/// `1 proved, 0 failed`, so the gap is 128-BIT-ONLY, and every bound spelling
/// failed identically, so it is also SPELLING-INDEPENDENT — a different defect
/// from the unfolded-constant one 5d400f920cf fixed, and named in that commit's
/// own `NOT CLAIMED` section.
///
/// The facts come from [`v2_dominating_operand_facts`] — the SAME miner the
/// multiply lane uses, with the operand list as a parameter — so the two lanes
/// can never drift about which facts hold.
///
/// SOUNDNESS is the multiply renderer's, unchanged:
///  * Dominance: a fact comes from a guarded edge every execution reaching the
///    negation traverses ([`dominating_facts`]; no path is enumerated, so no
///    `MAX_PATHS_PER_BLOCK` collapse can drop it).
///  * Same value: the fact is keyed on the SSA value its subject held at the guard,
///    and the negation must read that very value (`version_ssa::ValueId`). The
///    2026-09-21 cut compared reaching-def SETS instead, and a loop made those equal
///    across a write (`neg128_dominating_guard_realmir`'s `loop_kill`).
///  * Exact fit: a constant outside the operand type's value range is skipped by
///    `v2_bv_guard_constraint` (skipping is always sound).
///
/// So a genuinely overflowing execution satisfies every conjoined fact and stays
/// refuted: an UNGUARDED `-a` mines nothing and keeps its `a = i128::MIN` witness,
/// and a guard that really ADMITS `i128::MIN` (`a >= i128::MIN`) renders to
/// `bvsle(INT_MIN, a)`, which excludes nothing. Both are pinned in
/// `tests/neg128_dominating_guard_realmir.rs`.
///
/// NOT rendered in Int as well (the multiply lane's `v2_int_mul_dominating_guard_
/// constraints` twin): the negation VC's formula IS the BV core, and the Int-sorted
/// `{base}` already carries the guard through the ordinary path-guard conjunction
/// the <= 64-bit lane proves on. Adding a second spelling here would double-declare
/// the operand's own name at two sorts inside one formula.
pub(super) fn v2_bv_neg_dominating_guard_constraints(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    operand: &Operand,
    stmt_index: Option<usize>,
    width: u32,
) -> Vec<Formula> {
    // The negation lane only ever reaches here for a SIGNED operand (both
    // emitters check `ty.is_signed()` before building the BV core), so the
    // bound is rendered with the signed comparisons — the same order relation
    // the `x == INT_MIN` goal is stated in.
    let facts = v2_dominating_operand_facts(func, block, &[(operand, "neg")], stmt_index, width);
    v2_bv_guard_constraints_from_facts(&facts, width, true)
}

#[derive(Default)]
struct DominatingOperandFacts {
    /// `(operand_var_name, fresh_bv_var_name)` allocated at most once per operand.
    targets: Vec<(String, String)>,
    /// `(target_idx, cmp, constant)` referencing `targets[target_idx]`.
    facts: Vec<(usize, BvGuardCmp, i128)>,
}

/// The dominating `operand CMP constant` facts for a multiply's plain-local
/// operands. Shared by the BV and Int renderers above so the two can never drift
/// apart about WHICH facts hold — only about how they are spelled.
fn v2_mul_dominating_operand_facts(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    lhs: &Operand,
    rhs: &Operand,
    stmt_index: Option<usize>,
    width: u32,
) -> DominatingOperandFacts {
    v2_dominating_operand_facts(func, block, &[(lhs, "lhs"), (rhs, "rhs")], stmt_index, width)
}

/// The dominating `operand CMP constant` facts for a set of an operation's
/// plain-local operands, keyed by the BV ROLE each operand carries in its violation
/// formula (`"lhs"`/`"rhs"` for a multiply, `"neg"` for a negation) so the emitted
/// name is byte-identical to the one [`v2_bv_operand_term`] mints for that operand.
///
/// Trust: 2026-09-21 (the 128-bit NEGATION lane) — this body was
/// `v2_mul_dominating_operand_facts` verbatim; only the operand list became a
/// parameter. The negation lane needs EXACTLY these facts, mined EXACTLY this
/// way, and a second implementation would be a second place for the dominance,
/// version and fit checks to drift.
fn v2_dominating_operand_facts(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    operands: &[(&Operand, &str)],
    stmt_index: Option<usize>,
    width: u32,
) -> DominatingOperandFacts {
    // (local, local name, fresh BV var name) for each plain-local operand. Constants
    // need no bound; widening-cast operands already encode their true range
    // structurally (and their fresh var lives at the narrower source width).
    let use_stmt_index = stmt_index.unwrap_or(block.stmts.len());
    let index = super::dominating_facts_for(func);
    if !index.reachable(block.id) {
        return DominatingOperandFacts::default();
    }
    let mut candidates: Vec<(&Place, &str)> = Vec::with_capacity(operands.len());
    for (op, role) in operands.iter().copied() {
        let (Operand::Copy(place) | Operand::Move(place)) = op else {
            continue;
        };
        // A widening-cast operand is EXCLUDED, unchanged: it encodes its true range
        // structurally and its fresh BV var lives at the NARROWER source width, so a
        // `width`-wide guard constraint would not even be well-typed on it.
        //
        // Trust: 2026-09-18 (SIGNED g7 twin) — the staleness gate is
        // `value_local_is_unstable` MINUS the reassignment-only case, because the
        // `-O` lowering of `pub fn sgn_mut(a: i64, mut b: i64)` multiplies the
        // REASSIGNED PARAMETER ITSELF (`_9 = CheckedMul(copy _1, copy _2)`), and a
        // reassigned parameter is `unstable` by that predicate's definition. So the
        // operand was never even a TARGET: it got no bound of any kind, the fresh BV
        // var stayed free, and valid Rust was refuted at `b = 2^63`. The gate is
        // `DominatingFacts::admits` (stable, or written only by whole-local `Assign`s
        // the version oracle stamps): every fact the index offers is keyed on the SSA
        // VALUE the multiply reads, and that identity is exact precisely for the
        // writes the oracle stamps.
        if !place.projections.is_empty()
            || !index.admits(func, place.local)
            || v2_widening_bv_source(func, op, width).is_some()
        {
            continue;
        }
        candidates.push((place, role));
    }
    if candidates.is_empty() {
        return DominatingOperandFacts::default();
    }

    let mut facts: Vec<(usize, BvGuardCmp, i128)> = Vec::new();
    for (target_idx, &(place, _)) in candidates.iter().enumerate() {
        let local = place.local;
        // Trust: 2026-09-18 (g7) — mine the facts under the operand's own local AND
        // under the whole local it is a live pure copy of where the operation reads
        // it. The fact is always attributed to the OPERAND (its fresh BV var and its
        // own Int name); only the local it is looked up under changes, and
        // `DominatingFacts::copy_source_at` admits the hop only while the operand
        // really holds that local's value here (same SSA value at the copy and at
        // the use, the copy dominating the use).
        let copy_src = index.copy_source_at(func, local, block.id, use_stmt_index);
        for asked in [Some(local), copy_src].into_iter().flatten() {
            for &(cmp, constant) in index.facts(
                func,
                asked,
                block.id,
                use_stmt_index,
                dominating_facts::GuardSubject::LiveCopyOfBase,
            ) {
                facts.push((target_idx, cmp, constant));
            }
        }
    }

    // Contract preconditions: `func.preconditions` holds only GATED body
    // assumptions (contract_assumption_gate: params-only variables, raw
    // shadow/alias rejection, ground-witness vacuity check), the same facts
    // the Int lane conjoins via conjoin_live_preconditions. Translate the
    // var-vs-const comparisons among them onto the fresh BV operand vars so a
    // contract-bounded multiply (`#[trust::requires(x <= 1000)] ... x * 4`)
    // proves instead of false-Failing. Staleness is STATEMENT-GRANULAR via the
    // version-token oracle: a fact is skipped iff `version_token_at` reports the
    // parameter no longer holds its ENTRY value at the multiply's own use point
    // `(block, use_stmt_index)` — an overlap-aware earlier same-block write, or a
    // non-entry reaching-def version at block entry (preconditions speak about
    // entry values). A write that happens only LATER in the block, or on a path
    // that does not reach this use point, does NOT kill the fact.
    // NOTE: a `#[requires(a && b)]` parses to ONE `And` precondition, so a
    // conjunctive bound currently does NOT reach the BV mul operand here (only
    // flat, single-comparison preconditions do). Flattening the `And` (so both
    // bounds bind) was tried and REVERTED: it makes the bounded multi-128-bit-BV
    // mul formula of a mul/div-heavy function (days_from_civil) provable in
    // principle but the native solver has no effective deadline on this path and
    // SPINS indefinitely (a fast-Fail became a 23h hang). Re-enable the flatten
    // ONLY together with a native per-obligation solve timeout / size budget so a
    // hard formula reports Unknown instead of hanging.
    let mut base_names: Option<Vec<String>> = None;
    if !func.preconditions.is_empty() {
        let mut sv = None;
        for fact in &func.preconditions {
            let Some((name, cmp, c)) = v2_linear_var_const_fact(fact) else {
                continue;
            };
            let bases = base_names.get_or_insert_with(|| {
                candidates
                    .iter()
                    .map(|&(place, _)| crate::place_to_var_name(func, place))
                    .collect()
            });
            if !bases.iter().any(|base| base == name) {
                continue;
            };
            let sv = sv.get_or_insert_with(|| super::stmt_versions_for(func));
            if sv.version_token_at(func, block.id, use_stmt_index, name).is_some() {
                continue;
            };
            for (target_idx, base) in bases.iter().enumerate() {
                if base == name {
                    facts.push((target_idx, cmp, c));
                }
            }
        }
    }
    if facts.is_empty() {
        return DominatingOperandFacts::default();
    }
    let targets: Vec<(String, String)> = match base_names {
        Some(bases) => bases
            .into_iter()
            .zip(candidates.iter())
            .map(|(base, &(_, role))| {
                let bv_name = format!("__trust_ovf_bv_{role}_{base}");
                (base, bv_name)
            })
            .collect(),
        None => candidates
            .into_iter()
            .map(|(place, role)| {
                let base = crate::place_to_var_name(func, place);
                let bv_name = format!("__trust_ovf_bv_{role}_{base}");
                (base, bv_name)
            })
            .collect(),
    };
    DominatingOperandFacts { targets, facts }
}

/// widening-mul: if `op` is a bare local defined (uniquely) by a
/// value-preserving widening integer cast into `width` bits, return the
/// `(source_width, source_signed)` of the pre-cast value. Mirrors the #52
/// `widening_cast_result_range` gating exactly: strictly wider, and never
/// signed->unsigned (a negative source wraps to a huge unsigned value, so the
/// source-width range would be false). The caller encodes the operand as a
/// zero/sign-extension of a fresh source-width BV var, so a safe widening
/// multiply like `(x as u64) * (y as u64)` (x,y: u32) PROVES (each operand is
/// `< 2^sw` by construction) while a same-width or widened-times-unbounded
/// multiply still correctly FAILS.
pub(crate) fn v2_widening_bv_source(
    func: &VerifiableFunction,
    op: &Operand,
    width: u32,
) -> Option<(u32, bool)> {
    let (Operand::Copy(place) | Operand::Move(place)) = op else {
        return None;
    };
    if !place.projections.is_empty() {
        return None;
    }
    let local = place.local;
    if crate::local_defs::is_parameter(func, local) {
        return None;
    }
    // Trust (2026-09-29): the SAME widening spelled as the std conversion call
    // `<i128 as From<u64>>::from(x)` / `<u64 as Into<i128>>::into(x)`, whose result is
    // `x`'s value (`lossless_int_conversion_arg`). Without this arm the fresh
    // `width`-bit operand var was free and `i128::from(x) + 1` / `-i128::from(x)`
    // were refuted at `i128::MAX` / `i128::MIN`, values no `u64` widens to
    // (trust-ir-conformance `generate.rs:468/477`, measured 2026-09-29).
    //
    // It is checked BEFORE the cast arm's `index_local_stable` gate on purpose: that
    // gate counts EVERY call destination as a reseat (`array_local_escapes`), so a
    // call-defined local can never pass it. The call arm's stability is
    // `local_defs::unique_value_call` instead, which is the stronger statement —
    // the local's ONE value is this call's result: no second call destination, no
    // whole or partial store, no escaping `&mut`, not a parameter. The type gates are
    // the cast arm's, verbatim: the destination is exactly `width` bits and the step
    // is a STRICT, value-preserving widening (never same-width, never
    // signed-to-unsigned) — which every std integer `From`/`Into` impl is, and which
    // a non-std callee cannot claim, the callee being the authenticated
    // `core`/`std` `convert` spelling.
    if let Some(Ty::Int { width: dw, signed: ds }) = crate::local_ty_ref(func, local)
        && *dw == width
        && super::terminator_presence_for(func).has_bare_dest_call
        && let Some(arg) = crate::generate::lossless_int_conversion_arg(func, local)
    {
        let Some(&Ty::Int { width: sw, signed: ss }) = crate::operand_ty_cow(func, arg).as_deref()
        else {
            return None;
        };
        if *dw <= sw || (ss && !*ds) {
            return None;
        }
        return Some((sw, ss));
    }
    // Trust (widening-operand staleness): only narrow the operand to its cast
    // SOURCE width when the cast is the operand's UNIQUE reaching whole-local
    // definition and the local cannot be mutated through an alias. Otherwise a
    // reassignment after the cast (`let w = x as i64; w = big; w*w`, or
    // `w = f()`, or `&mut w` to a callee) would leave the operand structurally
    // pinned to the narrow source range while its real value is the reassigned
    // full-width one -- a false-PROVE (the product `big*big` reads as bounded and
    // the overflow is vacuously discharged; confirmed by the cross-feature audit).
    // When not stable, bail so `v2_bv_operand_term` falls back to a full-`width`
    // fresh BV var (sound: the product can overflow -> Failed, never false-Proved).
    if !crate::index_local_stable(func, local) {
        return None;
    }
    let mut found: Option<(u32, bool)> = None;
    let mut invalid = false;
    crate::visit_local_write_stmts(func, &func.body.blocks, local, |_block, stmt| {
        if invalid {
            return;
        }
        let Statement::Assign { place: dest, rvalue, .. } = stmt else {
            return;
        };
        if dest.local != local || !dest.projections.is_empty() {
            return;
        }
        let Rvalue::Cast(inner, to_ty) = rvalue else {
            invalid = true;
            return;
        };
        if found.is_some() {
            invalid = true;
            return;
        }
        let Ty::Int { width: dw, signed: ds } = to_ty else {
            invalid = true;
            return;
        };
        if *dw != width {
            invalid = true;
            return;
        }
        let inner_ty = crate::operand_ty_cow(func, inner);
        let Some(Ty::Int { width: sw, signed: ss }) = inner_ty.as_deref() else {
            invalid = true;
            return;
        };
        // Strict, value-preserving widening only (mirror #52).
        if *dw <= *sw || (*ss && !*ds) {
            invalid = true;
            return;
        }
        found = Some((*sw, *ss));
    });
    if invalid {
        return None;
    }
    found
}

/// Encode an unsigned operand as a `width`-bit BV term.
///
/// Integer constants become `Formula::BitVec`. Other operands (variables,
/// places, symbolic, etc.) become a FRESH `width`-bit BV variable whose name is
/// derived from the operand's pretty name but namespaced (`__trust_ovf_bv_*`)
/// so it can never collide with the Int-sorted variable of the same source
/// local elsewhere in the VC. See the soundness note on
/// `v2_unsigned_bv_overflow_formula`.
pub(super) fn v2_bv_operand_term(
    func: &VerifiableFunction,
    op: &Operand,
    width: u32,
    role: &str,
) -> Option<Formula> {
    match op {
        Operand::Constant(ConstValue::Int(n)) => Some(Formula::BitVec { value: *n, width }),
        Operand::Constant(ConstValue::Uint(n, _)) => {
            // BitVec stores the bit pattern as i128; reinterpret the unsigned
            // value's low `width` bits. For width <= 127 this is exact for any
            // representable constant; the SMT layer masks to `width` bits.
            let value = *n as i128;
            Some(Formula::BitVec { value, width })
        }
        Operand::Copy(place) | Operand::Move(place) => {
            let base = crate::place_to_var_name(func, place);
            // widening-mul: if this operand is a value-preserving widening
            // cast from a narrower width `sw`, model it STRUCTURALLY as an
            // extension of a fresh source-width var — zext for an unsigned source
            // (value in [0, 2^sw)), sext for a signed source (value in
            // [-2^(sw-1), 2^(sw-1))). This captures the operand's TRUE range in
            // pure QF_BV, so a safe widening multiply proves; a same-width or
            // widened-times-unbounded multiply still (correctly) fails.
            if let Some((sw, src_signed)) = v2_widening_bv_source(func, op, width) {
                let narrow =
                    Formula::var_owned(format!("__trust_ovf_bv_{role}_{base}"), Sort::BitVec(sw));
                let added = width - sw;
                return Some(if src_signed {
                    Formula::BvSignExt(Box::new(narrow), added)
                } else {
                    Formula::BvZeroExt(Box::new(narrow), added)
                });
            }
            Some(Formula::var_owned(format!("__trust_ovf_bv_{role}_{base}"), Sort::BitVec(width)))
        }
        // Symbolic / unsupported / unknown operands cannot be soundly pinned to
        // a fresh BV var without losing their meaning; bail so the caller can
        // fall back to the Int path (or unsupported) rather than guess.
        _ => None,
    }
}

pub(super) fn v2_assert_failure_formula(
    func: &VerifiableFunction,
    cond: &Operand,
    expected: bool,
) -> Formula {
    let cond_f = operand_to_formula(func, cond);
    if expected { Formula::Not(Box::new(cond_f)) } else { cond_f }
}

// Trust (#57, 2026-08-17) — these five now DELEGATE to `trust_types::static_truth`.
// The bodies moved there verbatim so the trust-ir spine can apply the SAME fold:
// the spine used to emit a divisor obligation for `n % 2` that trust-vcgen folded
// away, which was the entire surviving population of the missing-obligation alarm.
// Reimplementing the fold on the spine side would have made any drift between the
// two copies surface as a phantom disagreement — an alarm about the checkers
// disagreeing rather than about a hole in the checking. One definition, two callers.

pub(super) fn v2_assert_failure_is_known_false(
    block: &trust_types::BasicBlock,
    cond: &Operand,
    expected: bool,
) -> bool {
    trust_types::static_truth::assert_failure_is_known_false(block, cond, expected)
}

#[cfg(test)]
pub(super) fn v2_const_eq_truth(lhs: &ConstValue, rhs: &ConstValue) -> Option<bool> {
    trust_types::static_truth::const_eq_truth(lhs, rhs)
}

pub(super) fn v2_build_terminator_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<VerificationCondition> {
    // Trust (W4/spine-derives-unreachable): the Unreachable-classified arms are
    // decided by the SHARED classifier — the same definition the trust-ir spine
    // consumes (`trust_types::terminator_obligations`, one definition, two
    // callers). Arm order and outcomes are the verbatim move of the match this
    // replaces:
    //  * `SwitchInt::exhaustive_enum_unreachable` is serialized public input,
    //    not proof authority — the bare-`Unreachable` row is ALWAYS kept, never
    //    erased by an unauthenticated hint;
    //  * `unreachable!()` lowers to the BARE panic intrinsic with the sentinel
    //    message, and only an unreachable-chain classification turns a
    //    panic-call row from `Assertion` into `Unreachable`.
    use trust_types::terminator_obligations::{
        TerminatorObligationShape, classify_terminator_obligation,
    };

    let (kind, span) = match classify_terminator_obligation(func, block)? {
        TerminatorObligationShape::Unreachable(span) => (VcKind::Unreachable, span),
        // The `Assertion`-classified panic-call outcomes (NOT on an unreachable
        // chain). Scoped to the sentinel/assertion and outlined-default recognizers
        // so panic sites — which already have an obligation — do NOT get a second,
        // dataflow-starved VC that false-FAILs them; the message rendering is
        // vcgen-local obligation prose, not comparison identity.
        TerminatorObligationShape::AssertionPanicCall(span) => {
            let Terminator::Call { func: callee, args, .. } = &block.terminator else {
                return None;
            };
            (
                VcKind::Assertion { message: v2_panic_call_vc_message(func, callee, args) },
                span,
            )
        }
    };

    Some(VerificationCondition {
        kind,
        function: func.name.as_str().into(),
        location: span,
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    })
}
