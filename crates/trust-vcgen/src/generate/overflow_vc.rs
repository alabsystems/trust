// Arithmetic overflow obligations and their bit-vector encodings, including
// the dominating guard constraints that tighten operand ranges before the
// overflow question is asked. Signed multiplication is handled corner-by-corner
// because interval reasoning alone is too weak for it.

use super::*;

/// Dominating `<var> CMP <const>` facts that hold on EVERY recorded path into
/// `block`, as owned tuples. This is the SAME intersection machinery the
/// signed-128 add/sub arm threads through `v2_bv_mul_dominating_guard_constraints`
/// (build the path-guard map, resolve each path's guards to formulas, keep only
/// facts present on every path, flatten `And` range-validation guards), but it
/// returns the CONCRETE `(name, cmp, constant)` triples instead of BV formulas —
/// exactly what the bounded-corner overflow check needs to compute the box the
/// product ranges over. Dominance (every-path intersection) is what makes a fact
/// TRUE on every reaching path; a saturated block records an unguarded path,
/// which empties the intersection (no facts) — sound.
pub(super) fn v2_signed_mul_dominating_facts(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Vec<(String, BvGuardCmp, i128)> {
    let mut facts = Vec::new();
    let path_map = v2_build_path_guard_map(func);
    let Some(paths) = path_map.get(&block.id) else {
        return facts;
    };
    let resolved: Vec<Vec<Formula>> = paths
        .iter()
        .map(|gs| gs.iter().map(|(_, g)| guards::guard_to_formula(func, g)).collect())
        .collect();
    let Some((first, rest)) = resolved.split_first() else {
        return facts;
    };
    for fact in first {
        if !rest.iter().all(|path| path.contains(fact)) {
            continue;
        }
        for leaf in v2_flatten_guard_conjuncts(fact) {
            if let Some((name, cmp, c)) = v2_linear_var_const_fact(leaf) {
                facts.push((name.to_string(), cmp, c));
            }
        }
    }
    facts
}

/// Tighten `[lo, hi]` with one `<var> CMP c` fact. `Lt`/`Gt` shift the bound by
/// one toward the interior (`a < c` ⇒ `a <= c-1`); if that shift would over/under-
/// flow i128 the fact is dropped (a bound at the type extreme is not a real
/// tightening). All updates are monotone (a bound can only shrink the box), so a
/// fact can never enlarge the interval — soundness is preserved.
pub(super) fn v2_tighten_bound(cmp: BvGuardCmp, c: i128, lo: &mut Option<i128>, hi: &mut Option<i128>) {
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
///   * a contract precondition is used only if its parameter is never reassigned
///     anywhere (`v2_local_assigned_anywhere`), matching the BV guard arm.
///
/// A missing side (only a lower OR only an upper bound established) yields `None`:
/// the corner check needs a genuinely finite box on BOTH axes, so a symbolic /
/// one-sided-bounded operand fails closed — never proved.
pub(super) fn v2_signed_mul_operand_bounds(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: &Operand,
    end: usize,
    guard_facts: &[(String, BvGuardCmp, i128)],
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
    let base = crate::place_to_var_name(func, place);

    // BLOCK-DEF CONSTANT PIN: the operand's LAST projection-free definition
    // strictly before the multiply is `local = <const>`.
    let mut const_pin: Option<i128> = None;
    let mut assigned_in_block = false;
    for stmt in block.stmts.iter().take(end) {
        let Statement::Assign { place: p, rvalue, .. } = stmt else {
            continue;
        };
        if p.local != local || !p.projections.is_empty() {
            continue;
        }
        assigned_in_block = true;
        const_pin = match rvalue {
            Rvalue::Use(inner) => operand_const_int(inner),
            _ => None,
        };
    }
    if let Some(c) = const_pin {
        // Honor the pin only if the local is single-def and cannot be alias-
        // mutated between the def and the multiply (`&mut`/opaque-move escape).
        return crate::index_local_stable(func, local).then_some((c, c));
    }
    // A non-constant in-block (re)assignment makes any block-ENTRY guard stale.
    if assigned_in_block {
        return None;
    }

    // DOMINATING GUARDS + gated contract preconditions: tighten [lo, hi].
    let mut lo: Option<i128> = None;
    let mut hi: Option<i128> = None;
    for (name, cmp, c) in guard_facts {
        if name == &base {
            v2_tighten_bound(*cmp, *c, &mut lo, &mut hi);
        }
    }
    for fact in &func.preconditions {
        let Some((name, cmp, c)) = v2_linear_var_const_fact(fact) else {
            continue;
        };
        if name != base || v2_local_assigned_anywhere(func, name) {
            continue;
        }
        v2_tighten_bound(cmp, c, &mut lo, &mut hi);
    }
    match (lo, hi) {
        (Some(l), Some(h)) if l <= h => Some((l, h)),
        _ => None,
    }
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
    let guard_facts = v2_signed_mul_dominating_facts(func, block);
    let a = v2_signed_mul_operand_bounds(func, block, lhs, end, &guard_facts)?;
    let b = v2_signed_mul_operand_bounds(func, block, rhs, end, &guard_facts)?;
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

pub(super) fn v2_build_overflow_vc_for_operands(
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
    // Recover the true (width, signed) from a non-constant operand — a signed
    // constant lhs (e.g. `100i8 + x`) loses its width and would otherwise make
    // this check the overflow bound at i64 instead of the real type (round-19).
    let (width, signed) = int_op_type(func, lhs, rhs)?;

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
        if let Some((a_box, b_box)) = v2_signed_mul_corner_bounds(func, block, lhs, rhs, stmt_index)
            && v2_signed_mul_corners_fit(a_box, b_box)
        {
            return Some(VerificationCondition {
                kind: VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) },
                function: func.name.clone().into(),
                location: span.clone(),
                // Violation formula is trivially UNSAT ⇒ "no overflow" is PROVED (the
                // codebase's no-overflow proof shape; the dual of the Bool(true) fail-closed
                // obligation the provably-overflowing const-pow path emits).
                formula: Formula::Bool(false),
                contract_metadata: None,
            });
        }
        return Some(unsupported_mir_vc(
            func,
            "Rvalue::CheckedBinaryOp".to_string(),
            format!(
                "bb{}: signed {width}-bit Mul overflow is nonlinear (NIA) and not decidable \
                 on the Int path; the BV path declines width > 64 → fail-closed to runtime-check",
                block.id.0
            ),
            span.clone(),
        ));
    }

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
            // (`v2_bv_mul_dominating_guard_constraints` → `v2_build_path_guard_map`). The
            // signed-128 add/sub formula's operands are the SAME `__trust_ovf_bv_{role}_{base}`
            // fresh vars, so the constraints bind. SOUNDNESS: only facts true on EVERY
            // dominating path are conjoined, and the guard map EXCLUDES a guard whose value
            // was reassigned / `&mut`-borrowed after it (verified: the unsigned `&mut`-stale
            // mul stays Failed) — so a stale `a < 10` over a `*p = b` reassignment does NOT
            // thread, and the unguarded `a + b` (no dominating fact) stays refutable.
            terms
                .extend(v2_bv_mul_dominating_guard_constraints(func, block, lhs, rhs, width, true));
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
                function: func.name.clone().into(),
                location: span.clone(),
                formula,
                contract_metadata: None,
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
            let mut terms =
                v2_bv_mul_dominating_guard_constraints(func, block, lhs, rhs, width, signed);
            // Also render a LOOP-VAR yield bound (`y < W` for `for y in 0..W`) onto the operands so
            // a flattened-2D-index `y*W` mul-overflow PROVES. See `v2_bv_yield_constraints`.
            terms.extend(v2_bv_yield_constraints(func, block, lhs, rhs, width, signed));
            // And render a REMAINDER bound (`r < C` for `r = x % C`) so the range-clamping
            // idiom `(a % 100) * (b % 50)` PROVES. See `v2_bv_rem_constraints`.
            terms.extend(v2_bv_rem_constraints(func, lhs, rhs, width, signed));
            let formula = if terms.is_empty() {
                bv_formula
            } else {
                terms.push(bv_formula);
                Formula::And(terms)
            };
            return Some(VerificationCondition {
                kind: VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) },
                function: func.name.clone().into(),
                location: span.clone(),
                formula,
                contract_metadata: None,
            });
        }
        // Operands could not be encoded as BV terms (e.g. symbolic), or the
        // signed width is capped (i128); fall through to the Int path. Sound,
        // but mul there is NIA / likely Unknown.
    }

    let lhs_f = operand_to_formula(func, lhs);
    let rhs_f = operand_to_formula(func, rhs);

    let result = match op {
        BinOp::Add => Formula::Add(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        BinOp::Sub => Formula::Sub(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        BinOp::Mul => Formula::Mul(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
        _ => {
            return Some(unsupported_mir_vc(
                func,
                "Rvalue::CheckedBinaryOp".to_string(),
                format!("bb{}: checked {op:?} overflow semantics are not modeled", block.id.0),
                span.clone(),
            ));
        }
    };

    let lhs_range = crate::range::input_range_constraint(&lhs_f, width, signed);
    let rhs_range = crate::range::input_range_constraint(&rhs_f, width, signed);
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
        Formula::Lt(Box::new(result.clone()), Box::new(min_f))
    } else {
        Formula::Or(vec![
            Formula::Lt(Box::new(result.clone()), Box::new(min_f)),
            Formula::Gt(Box::new(result), Box::new(max_f)),
        ])
    };

    let body = Formula::And(vec![lhs_range, rhs_range, out_of_range]);
    // Direct-BinaryOp callers pass the statement index so defs are taken BEFORE
    // the operation (not the whole block, which would include the op's own
    // result definition); the checked path conjoins whole-block defs.
    let formula = match stmt_index {
        Some(idx) => v2_formula_with_block_defs_before_stmt(func, block, idx, body),
        None => v2_formula_with_block_defs(func, block, body),
    };
    // Bound any parameter that entered the VC only via a conjoined block
    // definition (sound — parameters are always within their type range; see
    // `conjoin_arg_type_ranges`). Closes spurious-overflow false-FAILs such as
    // `safe_midpoint`'s `lo + (hi - lo) / 2` without ever masking a real one.
    let formula = conjoin_arg_type_ranges(func, formula);
    // Trust (unsigned-sub vacuous-UNSAT false-accept fix): this builder's VC IS
    // the checked op's own overflow/underflow check, so the result copy closure's
    // type-ranges are circular premises here — exclude them (see
    // `checked_arith_result_value_vars`).
    let excl = checked_arith_result_value_vars(func);
    // verifier-precision: bound NON-parameter integer locals/temps too (the sibling
    // of arg ranges) — closes spurious-overflow false-FAILs over an unbounded-Int
    // temp. SOUNDNESS: DROP-ONLY (a true in-type-range fact).
    let formula = conjoin_local_type_ranges_excluding(func, formula, &excl);
    // Lever A: bound fixed-width-integer datatype FIELDS too (same sound bound) so the
    // direct overflow-VC callers (incl. the CheckedBinaryOp `Assert{Overflow}` path)
    // carry the field bound, not only the funnel passes. SOUNDNESS: DROP-ONLY.
    let formula = conjoin_datatype_field_ranges_excluding(func, formula, &excl);
    // Bound any slice/array length term by `isize::MAX` so a `i < s.len()`-guarded
    // increment cannot false-fail with an impossible `s.len() = 2^64` cex.
    let formula = conjoin_slice_len_bounds(func, formula);

    Some(VerificationCondition {
        kind: VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) },
        function: func.name.clone().into(),
        location: span.clone(),
        formula,
        contract_metadata: None,
    })
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
/// `lhs OP rhs` (`OP` in Add/Sub) of `width` bits, via the exact one-bit
/// sign-extension check (the negation of `BvAdd/BvSubNoOverflowSigned`).
///
/// Soundness (let `w = width`): sign-extend both operands by ONE bit to `w+1`
/// bits, perform the add/sub in `w+1` bits (which can NEVER itself overflow, so
/// the `w+1`-bit result is the EXACT mathematical sum/difference), and ask
/// whether that result is representable in `w` signed bits — i.e. whether its
/// top two bits (`[w]` and `[w-1]`) are EQUAL (the sign and the would-be sign
/// agree). The VC asserts the NEGATION (overflow): the solver proving it UNSAT =
/// "no signed overflow proved"; a SAT model = a verified `w`-bit signed
/// add/sub-overflow counterexample. This is byte-for-byte the same encoding the
/// native typed-CHC `lower_no_overflow_addsub_signed` uses, negated. EXACT — it
/// can never report Proved for a real overflow.
///
/// Unlike the signed MUL check (which needs a `2w`-bit multiplier and so declines
/// `w > 64`), this needs only `w+1` bits, so it is cheap and is the ROUTE for
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
    Some(signed_bv_addsub_overflow_sign_test(a, b, op, width))
}

/// The SIGNED add/sub overflow (failure) condition via the SIGN-BIT test, in pure
/// QF_BV using ONLY `BvULt` + `BvAdd`/`BvSub` at the operand width + `And`/`Or`/`Not`
/// + `BitVec`. This is the SAME op family the native typed-CHC lane proves for the
/// neg/shift checks (`v2_signed_bv_neg_overflow_formula`, the `BvShl` block-defs),
/// and it deliberately AVOIDS the `w+1`-bit sign-extension / bit-extraction encoding
/// that lane returns `Unsupported` for — which is exactly why `signed_max`'s trailing
/// `_5 - 1` (`Overflow(Sub)`) stayed UNKNOWN while `signed_min`'s `-_5` proved.
///
/// A `width`-bit value `v` is SIGNED-NEGATIVE iff its UNSIGNED value has the sign bit
/// set, i.e. `NOT (v <u 2^(width-1))`. With `r = a OP b` taken at width `width`
/// (two's-complement wraparound), signed overflow is the classic sign-relation test:
///   * `a + b` overflows iff `a`,`b` have the SAME sign and `r`'s sign differs from `a`'s;
///   * `a - b` overflows iff `a`,`b` have DIFFERENT signs and `r`'s sign differs from `a`'s.
///
/// SOUNDNESS: this is the EXACT two's-complement overflow predicate (it agrees with the
/// `w+1`-bit sign-extension form on every input — see the exhaustive `w=8` cross-check
/// test). An unconstrained operand keeps it satisfiable, so a real `i128::MAX - (-1)` /
/// `1<<127` overflow stays SAT/refutable; a defining shift + dominating bound (conjoined
/// by the caller) removes the infeasible witnesses so the guarded case PROVES.
pub(super) fn signed_bv_addsub_overflow_sign_test(a: Formula, b: Formula, op: BinOp, width: u32) -> Formula {
    // The sign-bit mask `2^(width-1)`. For `width == 128` this is `i128::MIN`'s bit
    // pattern (the `BitVec` value field is two's-complement; the SMT layer masks to
    // `width`) — the SAME representation the neg `INT_MIN` check uses.
    let msb = Formula::BitVec {
        value: if width == 128 { i128::MIN } else { 1i128 << (width - 1) },
        width,
    };
    let nonneg = |v: &Formula| Formula::BvULt(Box::new(v.clone()), Box::new(msb.clone()), width);
    let result = match op {
        BinOp::Add => Formula::BvAdd(Box::new(a.clone()), Box::new(b.clone()), width),
        BinOp::Sub => Formula::BvSub(Box::new(a.clone()), Box::new(b.clone()), width),
        _ => unreachable!("guarded by the caller to Add/Sub"),
    };
    let nn_a = nonneg(&a);
    let nn_b = nonneg(&b);
    let nn_r = nonneg(&result);
    // Boolean `x != y`, expanded to `And`/`Or`/`Not` so no Bool-sorted `Eq` is emitted.
    let differ = |x: &Formula, y: &Formula| {
        Formula::Or(vec![
            Formula::And(vec![x.clone(), Formula::Not(Box::new(y.clone()))]),
            Formula::And(vec![Formula::Not(Box::new(x.clone())), y.clone()]),
        ])
    };
    let result_sign_flips = differ(&nn_r, &nn_a);
    let sign_relation = match op {
        // SAME sign = NOT (signs differ).
        BinOp::Add => Formula::Not(Box::new(differ(&nn_a, &nn_b))),
        BinOp::Sub => differ(&nn_a, &nn_b),
        _ => unreachable!("guarded by the caller to Add/Sub"),
    };
    Formula::And(vec![sign_relation, result_sign_flips])
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
/// emits, gated by the same `total_loop_iterations`/`addend_per_iteration_bound`/
/// `accumulator_init_const` recognition that excludes call-clobbered / mutably-aliased / unbounded
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
    let Some(k) = total_loop_iterations(func) else { return Vec::new() };
    let Some((_, per_max)) = addend_per_iteration_bound(func, rhs_p.local) else {
        return Vec::new();
    };
    let Some(init_c) = accumulator_init_const(func, acc_p.local, ck_dest_local) else {
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

/// BV-render the LOOP-VAR YIELD bound (`start <= y < end` for `for y in start..end`) onto the fresh
/// `__trust_ovf_bv_*` operand vars of an overflow check — so a flattened 2D index's `y*W`
/// [overflow:mul] (BV-encoded, usize) discharges. Mirrors `v2_bv_mul_dominating_guard_constraints`
/// but the bound source is the exclusive-range yield invariant, not a dominating guard.
///
/// SOUNDNESS: `y` is the Some-payload of `Range::next`, single-assigned (`loop_var_const_range` uses
/// `unique_whole_local_def`), so `start <= y < end` holds at every read — rendered via the validated
/// `v2_bv_guard_constraint`. SELF-LIMITING: a mul that can still overflow given `y < end` (huge end)
/// is not prevented; a reassigned operand (assigned in this block) is skipped.
pub(super) fn v2_bv_yield_constraints(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    lhs: &Operand,
    rhs: &Operand,
    width: u32,
    signed: bool,
) -> Vec<Formula> {
    let mut out = Vec::new();
    for (op, role) in [(lhs, "lhs"), (rhs, "rhs")] {
        let (Operand::Copy(p) | Operand::Move(p)) = op else { continue };
        if !p.projections.is_empty() || v2_widening_bv_source(func, op, width).is_some() {
            continue;
        }
        if block
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == p.local))
        {
            continue;
        }
        let Some((start, end)) = loop_var_const_range(func, p.local) else { continue };
        let base = crate::place_to_var_name(func, p);
        let bv = format!("__trust_ovf_bv_{role}_{base}");
        if let Some(f) = v2_bv_guard_constraint(&bv, BvGuardCmp::Ge, start, width, signed) {
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
/// Prove). Gated on `unique_whole_local_def` (a reassigned local has no single
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
        if !p.projections.is_empty() || v2_widening_bv_source(func, op, width).is_some() {
            continue;
        }
        let Some(Rvalue::BinaryOp(BinOp::Rem, _, divisor)) =
            crate::unique_whole_local_def(func, p.local)
        else {
            continue;
        };
        let Some(c) = const_int_value(divisor) else { continue };
        if c <= 0 {
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
        if !place.projections.is_empty() {
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
/// `None` if the cond is not a `.1` flag, or no matching CheckedBinaryOp defines
/// it (the caller then falls back to the first block binop).
pub(super) fn v2_find_checked_binop_for_assert_cond<'a>(
    block: &'a trust_types::BasicBlock,
    cond: &Operand,
    op: BinOp,
) -> Option<(&'a Operand, &'a Operand)> {
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
    block.stmts.iter().find_map(|stmt| {
        let Statement::Assign { place, rvalue: Rvalue::CheckedBinaryOp(stmt_op, lhs, rhs), .. } =
            stmt
        else {
            return None;
        };
        if place.local == tuple_local && place.projections.is_empty() && *stmt_op == op {
            Some((lhs, rhs))
        } else {
            None
        }
    })
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
    target: BlockId,
) -> Option<Formula> {
    match msg {
        // `Overflow(Add|Sub)`: the assert block IS the CheckedBinaryOp block; the
        // cond is the overflow flag `_N.1`. Recover the operands from the
        // CheckedBinaryOp that defines `_N` — keyed on the assert cond's tuple local,
        // NOT the first matching binop in the block. (A block like signed_max's bb1
        // holds `_6 = width - 1` AND `_9 = CheckedSub(_5, 1)`; keying on `_9` is what
        // selects the i128 sub, not the u32 amount sub.)
        AssertMessage::Overflow(op @ (BinOp::Add | BinOp::Sub)) => {
            let Terminator::Assert { cond, .. } = &block.terminator else {
                return None;
            };
            let (lhs, rhs) = v2_find_checked_binop_for_assert_cond(block, cond, *op)
                // Fall back to the first matching binop (e.g. a direct
                // `_N = CheckedBinaryOp(...)` whose flag the assert reads, with no
                // confounding same-op statement). Sound: if both shapes resolve to
                // different operands, the cond-keyed one is the asserted op.
                .or_else(|| v2_find_block_binary_operands(block, *op))?;
            let (width, signed) = int_op_type(func, lhs, rhs)?;
            if !signed || width < 128 {
                return None;
            }
            let bv_formula = v2_signed_bv_addsub_overflow_formula(func, lhs, rhs, *op, width)?;
            // The CheckedBinaryOp's overflow is asserted at the block terminator,
            // so the operands' defining shifts are whole-block defs (`None`).
            let mut terms = v2_signed_bv_blockdef_constraints(func, block, lhs, rhs, None, width);
            if terms.is_empty() {
                Some(bv_formula)
            } else {
                terms.push(bv_formula);
                Some(Formula::And(terms))
            }
        }
        // `OverflowNeg`: the `Neg(x)` runs in the TARGET block (the assert cond is
        // `_c = (x == INT_MIN)`); recover `x` from there. The operand's defining
        // shift (signed_min's `-(1i128 << (width-1))`) lives in THIS source block.
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
            let bv_formula = v2_signed_bv_neg_overflow_formula(func, operand, width)?;
            let mut terms = Vec::new();
            if let Operand::Copy(p) | Operand::Move(p) = operand
                && p.projections.is_empty()
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
    // Find the LAST defining `Shl` of `target_local` strictly before `end`.
    let mut found: Option<(&Operand, &Operand)> = None;
    for stmt in block.stmts.iter().take(end) {
        let Statement::Assign { place, rvalue, .. } = stmt else {
            continue;
        };
        if place.local != target_local || !place.projections.is_empty() {
            continue;
        }
        match rvalue {
            Rvalue::BinaryOp(BinOp::Shl, base, amount) => found = Some((base, amount)),
            // Any OTHER (re)definition of this local before `end` means the value
            // is not the clean single-Shl shape — decline (omit, sound).
            _ => found = None,
        }
    }
    let Some((base, amount)) = found else {
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
    let amt_base = crate::place_to_var_name(func, amt_place);
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
    let amt_bound = v2_dominating_shift_amount_bound(func, block, amt_place.local, width);
    if let Some(bound) = amt_bound {
        out.push(bound);
    }
}

/// Inline a bare boolean-temp guard fact (`Var(_c, Bool)`) to its defining
/// comparison (`_c = (n < K)`), so an assert-sourced shift guard exposes the
/// linear bound on the shift amount. Leaves any other fact unchanged. A `Not(_c)`
/// wrapper is preserved around the inlined comparison (the linear-fact reader then
/// inverts it). Only single-comparison bool defs are inlined; anything else (a
/// logical `&&`/`||`, a non-comparison) passes through unchanged (sound: a fact we
/// can't inline simply yields no bound).
pub(super) fn v2_inline_bool_guard_fact(func: &VerifiableFunction, fact: Formula) -> Formula {
    // Resolve a bool local name to its UNIQUE defining comparison formula.
    let define = |name: &str| -> Option<Formula> {
        let mut found: Option<Formula> = None;
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                let Statement::Assign { place, rvalue, .. } = stmt else {
                    continue;
                };
                if !place.projections.is_empty() || crate::place_to_var_name(func, place) != name {
                    continue;
                }
                let Rvalue::BinaryOp(op, lhs, rhs) = rvalue else {
                    return None;
                };
                // Only simple integer comparisons are useful here.
                if !matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq) {
                    return None;
                }
                let l = operand_to_formula(func, lhs);
                let r = operand_to_formula(func, rhs);
                let f = match op {
                    BinOp::Lt => Formula::Lt(Box::new(l), Box::new(r)),
                    BinOp::Le => Formula::Le(Box::new(l), Box::new(r)),
                    BinOp::Gt => Formula::Gt(Box::new(l), Box::new(r)),
                    BinOp::Ge => Formula::Ge(Box::new(l), Box::new(r)),
                    BinOp::Eq => Formula::Eq(Box::new(l), Box::new(r)),
                    _ => return None,
                };
                match &found {
                    Some(prev) if prev != &f => return None, // ambiguous: decline
                    _ => found = Some(f),
                }
            }
        }
        found
    };
    match &fact {
        Formula::Var(name, Sort::Bool) => define(name.as_str()).unwrap_or(fact),
        Formula::Not(inner) => {
            if let Formula::Var(name, Sort::Bool) = inner.as_ref() {
                match define(name.as_str()) {
                    Some(f) => Formula::Not(Box::new(f)),
                    None => fact,
                }
            } else {
                fact
            }
        }
        _ => fact,
    }
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
    amt_local: usize,
    width: u32,
) -> Option<Formula> {
    let amt_base = crate::place_to_var_name(func, &Place::local(amt_local));
    let amt_bv = Formula::var_owned(format!("__trust_ovf_bv_amt_{amt_base}"), Sort::BitVec(width));
    let path_map = v2_build_path_guard_map(func);
    let paths = path_map.get(&block.id)?;
    // Resolve each path's guards to semantic facts; keep facts on EVERY path.
    // A shift's `amount < bits` guard reaches the block as an `AssertHolds { _c }`
    // whose cond `_c` is a bare bool temp (`guard_to_formula` does NOT inline an
    // assert cond's defining comparison, unlike a SwitchInt discriminant). So we
    // additionally INLINE a bare `Var(_c, Bool)` fact to its defining `_c = (n < K)`
    // comparison, then look for the linear bound on the shift amount.
    let resolved: Vec<Vec<Formula>> = paths
        .iter()
        .map(|gs| {
            gs.iter()
                .map(|(_, g)| v2_inline_bool_guard_fact(func, guards::guard_to_formula(func, g)))
                .collect()
        })
        .collect();
    let (first, rest) = resolved.split_first()?;
    // Collect the DOMINATING facts (present on every path).
    let dominating: Vec<&Formula> = first
        .iter()
        .filter(|fact| rest.iter().all(|path| path.contains(*fact)))
        .flat_map(v2_flatten_guard_conjuncts)
        .collect();

    // The tightest STRICT upper bound `var < ub` derivable from the dominating facts.
    let strict_ub = |var: &str| -> Option<i128> {
        let mut best: Option<i128> = None;
        for leaf in &dominating {
            if let Some((name, cmp, c)) = v2_linear_var_const_fact(leaf)
                && name == var
            {
                let ub = match cmp {
                    BvGuardCmp::Lt => Some(c),
                    BvGuardCmp::Le => c.checked_add(1),
                    _ => None,
                };
                if let Some(ub) = ub {
                    best = Some(best.map_or(ub, |b: i128| b.min(ub)));
                }
            }
        }
        best
    };

    // (1) A direct dominating bound on the shift amount (`_6 < 128` from the SHL
    //     assert), and
    // (2) the SEMANTIC bound threaded through the amount's `_6 = src - c` definition:
    //     if `src` is dominated by `src <= W` then `_6 <= W - c`, i.e. `_6 < W - c +
    //     1`. This is what derives `_6 <= 126` from `width <= 127` (`signed_max`/
    //     `signed_min`'s `_6 = width - 1`), the bound that makes `_5` a power of two in
    //     `[1, 2^126]` so `_5 - 1` / `-_5` provably cannot overflow.
    let mut best: Option<i128> = strict_ub(&amt_base);
    if let Some((src_local, sub_const)) = v2_amount_sub_source(func, amt_local)
        && let Some(src_ub_excl) =
            strict_ub(&crate::place_to_var_name(func, &Place::local(src_local)))
    {
        // src < src_ub_excl  ⇒  src <= src_ub_excl - 1  ⇒  amt = src - c <= src_ub_excl
        // - 1 - c  ⇒  amt < src_ub_excl - c.
        if let Some(derived) = src_ub_excl.checked_sub(sub_const) {
            best = Some(best.map_or(derived, |b: i128| b.min(derived)));
        }
    }

    // The bound is only USEFUL (and well-typed) when `1 <= ub <= width`.
    let ub = best.filter(|&u| u >= 1 && u <= i128::from(width))?;
    // `amount < ub`.
    Some(Formula::BvULt(Box::new(amt_bv), Box::new(Formula::BitVec { value: ub, width }), width))
}

/// If the shift-amount local is uniquely defined by `amt = src - c` (a `Sub` of a
/// plain local minus an integer constant), return `(src_local, c)`. Used to thread
/// a dominating bound on `src` (`width <= 127`) through to the amount (`_6 = width
/// - 1 <= 126`). Returns `None` for any other defining shape (sound: no derived
/// bound, the prove may simply fail).
pub(super) fn v2_amount_sub_source(func: &VerifiableFunction, amt_local: usize) -> Option<(usize, i128)> {
    let mut found: Option<(usize, i128)> = None;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place, rvalue, .. } = stmt else {
                continue;
            };
            if place.local != amt_local || !place.projections.is_empty() {
                continue;
            }
            // Only a clean `src - const` defines a usable derived bound.
            let cand = match rvalue {
                Rvalue::BinaryOp(BinOp::Sub, src, c)
                | Rvalue::CheckedBinaryOp(BinOp::Sub, src, c) => {
                    let (Operand::Copy(sp) | Operand::Move(sp)) = src else {
                        return None;
                    };
                    if !sp.projections.is_empty() {
                        return None;
                    }
                    let cv = match c {
                        Operand::Constant(ConstValue::Int(n)) => *n,
                        Operand::Constant(ConstValue::Uint(n, _)) => *n as i128,
                        _ => return None,
                    };
                    Some((sp.local, cv))
                }
                // `_6 = move (_N.0)`: rustc lowers a checked `width - 1` as
                // `_N = SubWithOverflow(width, 1); assert(!_N.1); _6 = _N.0`, so the
                // amount is the RESULT FIELD of a CheckedBinaryOp Sub, reached via a
                // `.0` projection — not a direct `Sub` defining `_6`. Follow the
                // projection to that Sub's operands so the dominating bound on `width`
                // (`width <= 127`) still threads to `_6 <= 126`. Without this, the
                // derived bound is lost and a guarded `1i128 << (width-1)` shift
                // false-FAILs (only the weak `_6 < 128` survives, admitting
                // `_6 = 127 ⇒ _5 = i128::MIN`).
                Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                    if p.projections.len() == 1
                        && matches!(p.projections[0], trust_types::Projection::Field(0)) =>
                {
                    match v2_checked_sub_operands_for_tuple(func, p.local) {
                        Some(pair) => Some(pair),
                        None => return None,
                    }
                }
                // Any other (re)definition of the amount means it is not the clean
                // single-Sub shape — decline.
                _ => return None,
            };
            match (found, cand) {
                (Some(prev), Some(cand)) if prev != cand => return None,
                (_, Some(cand)) => found = Some(cand),
                (_, None) => {}
            }
        }
    }
    found
}

/// Operands `(src_local, c)` of the unique `_N = CheckedBinaryOp(Sub, src, c)`
/// (`SubWithOverflow`) that defines tuple local `_N`, where `src` is a bare local
/// and `c` an integer constant. Used by [`v2_amount_sub_source`] to thread a
/// dominating bound on `src` through a checked `width - 1` whose result is read as
/// `_N.0`. `None` for any other shape (sound: no derived bound).
pub(super) fn v2_checked_sub_operands_for_tuple(
    func: &VerifiableFunction,
    tuple_local: usize,
) -> Option<(usize, i128)> {
    let mut found: Option<(usize, i128)> = None;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign {
                place,
                rvalue:
                    Rvalue::CheckedBinaryOp(BinOp::Sub, src, c) | Rvalue::BinaryOp(BinOp::Sub, src, c),
                ..
            } = stmt
            else {
                continue;
            };
            if place.local != tuple_local || !place.projections.is_empty() {
                continue;
            }
            let (Operand::Copy(sp) | Operand::Move(sp)) = src else {
                return None;
            };
            if !sp.projections.is_empty() {
                return None;
            }
            let cv = match c {
                Operand::Constant(ConstValue::Int(n)) => *n,
                Operand::Constant(ConstValue::Uint(n, _)) => *n as i128,
                _ => return None,
            };
            let cand = (sp.local, cv);
            match found {
                Some(prev) if prev != cand => return None,
                _ => found = Some(cand),
            }
        }
    }
    found
}

/// Try to read a path fact as `<var> CMP <integer constant>` (either argument
/// order; one level of `Not(...)` normalized by comparison inversion).
/// Flatten a dominating-guard fact into its leaf comparison facts, recursing
/// through `And`. A `(L..=U).contains(&x)` validation guard resolves to a single
/// `And(Ge, Le)`; without flattening, `v2_linear_var_const_fact` drops it (no
/// `And` arm) and both bounds are lost. Non-conjunctive facts pass through.
pub(super) fn v2_flatten_guard_conjuncts(fact: &Formula) -> Vec<&Formula> {
    match fact {
        Formula::And(conjuncts) => conjuncts.iter().flat_map(v2_flatten_guard_conjuncts).collect(),
        other => vec![other],
    }
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
    let var = || Box::new(Formula::var_owned(bv_name.to_string(), Sort::BitVec(width)));
    let bvc = || Box::new(Formula::BitVec { value: c, width });
    Some(match (cmp, signed) {
        (BvGuardCmp::Le, false) => Formula::BvULe(var(), bvc(), width),
        (BvGuardCmp::Lt, false) => Formula::BvULt(var(), bvc(), width),
        (BvGuardCmp::Ge, false) => Formula::BvULe(bvc(), var(), width),
        (BvGuardCmp::Gt, false) => Formula::BvULt(bvc(), var(), width),
        (BvGuardCmp::Le, true) => Formula::BvSLe(var(), bvc(), width),
        (BvGuardCmp::Lt, true) => Formula::BvSLt(var(), bvc(), width),
        (BvGuardCmp::Ge, true) => Formula::BvSLe(bvc(), var(), width),
        (BvGuardCmp::Gt, true) => Formula::BvSLt(bvc(), var(), width),
        (BvGuardCmp::Eq, _) => Formula::Eq(var(), bvc()),
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
/// EVERY recorded path into the mul's block is translated into the equivalent
/// BV comparison over the fresh operand var.
///
/// Soundness:
///  * Dominance: a fact is used only if it appears on every path
///    `v2_build_path_guard_map` records for this block; a saturated block
///    records an unguarded path, which empties the intersection. A real
///    overflow's witness state therefore satisfies every conjoined fact, so
///    conjoining removes only INFEASIBLE counterexamples — it can flip
///    Failed -> Proved only when no feasible violation exists, never hide one.
///  * Same value: the fact and the fresh BV var denote the same local's value;
///    facts about a local this block itself assigns are skipped (the
///    block-entry fact may be stale by the time the mul executes).
///  * Exact fit: constants outside the operand type's value range are skipped
///    (see `v2_bv_guard_constraint`); skipping is always sound.
pub(super) fn v2_bv_mul_dominating_guard_constraints(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    lhs: &Operand,
    rhs: &Operand,
    width: u32,
    signed: bool,
) -> Vec<Formula> {
    // (local name, fresh BV var name) for each plain-local operand. Constants
    // need no bound; widening-cast operands already encode their true range
    // structurally (and their fresh var lives at the narrower source width).
    let mut targets: Vec<(String, String)> = Vec::new();
    for (op, role) in [(lhs, "lhs"), (rhs, "rhs")] {
        let (Operand::Copy(place) | Operand::Move(place)) = op else {
            continue;
        };
        if !place.projections.is_empty() || v2_widening_bv_source(func, op, width).is_some() {
            continue;
        }
        let assigned_in_block = block.stmts.iter().any(|stmt| {
            matches!(stmt, trust_types::Statement::Assign { place: p, .. } if p.local == place.local)
        });
        if assigned_in_block {
            continue;
        }
        let base = crate::place_to_var_name(func, place);
        targets.push((base.clone(), format!("__trust_ovf_bv_{role}_{base}")));
    }
    if targets.is_empty() {
        return Vec::new();
    }

    let path_map = v2_build_path_guard_map(func);
    let Some(paths) = path_map.get(&block.id) else {
        return Vec::new();
    };
    // Resolve each path's guard conditions to semantic formulas, then keep
    // only facts present on EVERY path (set intersection by formula equality).
    let resolved: Vec<Vec<Formula>> = paths
        .iter()
        .map(|gs| gs.iter().map(|(_, g)| guards::guard_to_formula(func, g)).collect())
        .collect();
    let Some((first, rest)) = resolved.split_first() else {
        return Vec::new();
    };
    let mut constraints = Vec::new();
    for fact in first {
        if !rest.iter().all(|path| path.contains(fact)) {
            continue;
        }
        // A range-validation guard `(L..=U).contains(&x)` resolves to a single
        // `And(Ge(x,L), Le(x,U))` (the rewrite's `BitAnd`), unlike a hand-written
        // `&&` guard which splits into two single-fact switches. Flatten conjuncts
        // so BOTH bounds bind to the BV operand; otherwise a range-validated
        // `x * <const>` false-FAILs. Post-intersection, so only facts true on EVERY
        // dominating path are flattened (sound). GUARD lane only — distinct from the
        // precondition `And`-flatten reverted above for the days_from_civil spin.
        for leaf in v2_flatten_guard_conjuncts(fact) {
            let Some((name, cmp, c)) = v2_linear_var_const_fact(leaf) else {
                continue;
            };
            for (base, bv_name) in &targets {
                if base == name
                    && let Some(constraint) = v2_bv_guard_constraint(bv_name, cmp, c, width, signed)
                {
                    constraints.push(constraint);
                }
            }
        }
    }

    // Contract preconditions: `func.preconditions` holds only GATED body
    // assumptions (contract_assumption_gate: params-only variables, raw
    // shadow/alias rejection, ground-witness vacuity check), the same facts
    // the Int lane conjoins via conjoin_live_preconditions. Translate the
    // var-vs-const comparisons among them onto the fresh BV operand vars so a
    // contract-bounded multiply (`#[trust::requires(x <= 1000)] ... x * 4`)
    // proves instead of false-Failing. Staleness is handled strictly more
    // conservatively than the Int lane's killed-set discipline: a fact is
    // skipped if its parameter is assigned ANYWHERE in the function
    // (preconditions speak about entry values).
    // NOTE: a `#[requires(a && b)]` parses to ONE `And` precondition, so a
    // conjunctive bound currently does NOT reach the BV mul operand here (only
    // flat, single-comparison preconditions do). Flattening the `And` (so both
    // bounds bind) was tried and REVERTED: it makes the bounded multi-128-bit-BV
    // mul formula of a mul/div-heavy function (days_from_civil) provable in
    // principle but the native solver has no effective deadline on this path and
    // SPINS indefinitely (a fast-Fail became a 23h hang). Re-enable the flatten
    // ONLY together with a native per-obligation solve timeout / size budget so a
    // hard formula reports Unknown instead of hanging.
    for fact in &func.preconditions {
        let Some((name, cmp, c)) = v2_linear_var_const_fact(fact) else {
            continue;
        };
        if v2_local_assigned_anywhere(func, name) {
            continue;
        }
        for (base, bv_name) in &targets {
            if base == name
                && let Some(constraint) = v2_bv_guard_constraint(bv_name, cmp, c, width, signed)
            {
                constraints.push(constraint);
            }
        }
    }
    constraints
}

/// Whether any statement in the function assigns the plain local named
/// `name` (projection-free writes; conservative for the precondition
/// staleness check above).
pub(super) fn v2_local_assigned_anywhere(func: &VerifiableFunction, name: &str) -> bool {
    func.body.blocks.iter().any(|block| {
        block.stmts.iter().any(|stmt| {
            matches!(
                stmt,
                Statement::Assign { place, .. }
                    if place.projections.is_empty()
                        && crate::place_to_var_name(func, place) == name
            )
        })
    })
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
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: dest, rvalue: Rvalue::Cast(inner, to_ty), .. } = stmt
            else {
                continue;
            };
            if dest.local != local || !dest.projections.is_empty() {
                continue;
            }
            let Ty::Int { width: dw, signed: ds } = to_ty else {
                return None;
            };
            if *dw != width {
                return None;
            }
            let inner_ty = crate::operand_ty_cow(func, inner);
            let Some(Ty::Int { width: sw, signed: ss }) = inner_ty.as_deref() else {
                return None;
            };
            // Strict, value-preserving widening only (mirror #52).
            if *dw <= *sw || (*ss && !*ds) {
                return None;
            }
            let cand = (*sw, *ss);
            match found {
                Some(prev) if prev != cand => return None,
                _ => found = Some(cand),
            }
        }
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

pub(super) fn v2_assert_failure_formula(func: &VerifiableFunction, cond: &Operand, expected: bool) -> Formula {
    let cond_f = operand_to_formula(func, cond);
    if expected { Formula::Not(Box::new(cond_f)) } else { cond_f }
}

pub(super) fn v2_assert_failure_is_known_false(
    block: &trust_types::BasicBlock,
    cond: &Operand,
    expected: bool,
) -> bool {
    v2_condition_truth_until(block, cond, block.stmts.len()).is_some_and(|truth| truth == expected)
}

pub(super) fn v2_condition_truth_until(
    block: &trust_types::BasicBlock,
    cond: &Operand,
    end_stmt_exclusive: usize,
) -> Option<bool> {
    match cond {
        Operand::Constant(ConstValue::Bool(value)) => Some(*value),
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => {
            v2_local_condition_truth_until(block, place.local, end_stmt_exclusive)
        }
        _ => None,
    }
}

pub(super) fn v2_local_condition_truth_until(
    block: &trust_types::BasicBlock,
    local: usize,
    end_stmt_exclusive: usize,
) -> Option<bool> {
    for (idx, stmt) in block.stmts.iter().take(end_stmt_exclusive).enumerate().rev() {
        let Statement::Assign { place, rvalue, .. } = stmt else {
            continue;
        };
        if place.local != local || !place.projections.is_empty() {
            continue;
        }
        return match rvalue {
            Rvalue::Use(operand) => v2_condition_truth_until(block, operand, idx),
            Rvalue::BinaryOp(BinOp::Eq, lhs, rhs) => v2_constant_eq_truth(lhs, rhs),
            Rvalue::BinaryOp(BinOp::Ne, lhs, rhs) => {
                v2_constant_eq_truth(lhs, rhs).map(|truth| !truth)
            }
            _ => None,
        };
    }

    None
}

pub(super) fn v2_constant_eq_truth(lhs: &Operand, rhs: &Operand) -> Option<bool> {
    match (lhs, rhs) {
        (Operand::Constant(lhs), Operand::Constant(rhs)) => v2_const_eq_truth(lhs, rhs),
        _ => None,
    }
}

pub(super) fn v2_const_eq_truth(lhs: &ConstValue, rhs: &ConstValue) -> Option<bool> {
    match (lhs, rhs) {
        (ConstValue::Bool(lhs), ConstValue::Bool(rhs)) => Some(lhs == rhs),
        (ConstValue::Int(lhs), ConstValue::Int(rhs)) => Some(lhs == rhs),
        (ConstValue::Uint(lhs, _), ConstValue::Uint(rhs, _)) => Some(lhs == rhs),
        (ConstValue::Int(lhs), ConstValue::Uint(rhs, _)) => {
            (*lhs >= 0).then_some(*lhs as u128 == *rhs)
        }
        (ConstValue::Uint(lhs, _), ConstValue::Int(rhs)) => {
            (*rhs >= 0).then_some(*lhs == *rhs as u128)
        }
        (ConstValue::Float(lhs), ConstValue::Float(rhs)) => Some(lhs == rhs),
        (ConstValue::Unit, ConstValue::Unit) => Some(true),
        // Callable identity is extraction evidence for syntactic recognizers,
        // never a solver-level equality fact. Historical dumps encoded these
        // values as Unit; returning unknown is strictly more conservative.
        (ConstValue::CallableItem { .. }, _) | (_, ConstValue::CallableItem { .. }) => None,
        // two `&str` literals are equal iff their bytes match. This is
        // exact (the bytes come straight from the literal's allocation), so it is
        // sound to let it decide a constant branch. Without this arm the catch-all
        // would answer `Some(false)` for *equal* strings and could prune the
        // genuinely-taken branch, dropping its safety obligations.
        (ConstValue::Str { bytes: lhs }, ConstValue::Str { bytes: rhs }) => Some(lhs == rhs),
        // An `OpaqueConst` (fresh-symbolic aggregate/opaque constant — empty
        // collections, `Cell`, alloc handles, `&[&str]` tables) or an
        // `OpaqueScalar` (a const-generic / associated / `size_of` integer with no
        // evaluated value) carries no decidable value, so its equality is UNKNOWN.
        // Return `None` so the caller verifies BOTH branches rather than pruning
        // one. This MUST precede the `_ => Some(false)` catch-all: answering
        // "definitely unequal" for two opaque consts that are in fact equal would
        // prune the genuinely-taken branch and silently drop its safety obligations
        // — a false PROVE. (Same hazard the `Str` arm above guards against for equal
        // string literals.)
        (ConstValue::OpaqueConst, _) | (_, ConstValue::OpaqueConst) => None,
        // A `UnitVariantRef` (promoted `&Option<T>::None`-style reference constant)
        // value-lowers exactly like `OpaqueConst` — a fresh symbolic ref with no
        // decidable value — so its equality is UNKNOWN. Return `None` (verify BOTH
        // branches), never `Some(false)`, for the same false-PROVE hazard as above.
        (ConstValue::UnitVariantRef { .. }, _) | (_, ConstValue::UnitVariantRef { .. }) => None,
        (ConstValue::OpaqueScalar { .. }, _) | (_, ConstValue::OpaqueScalar { .. }) => None,
        // Trust: piece #7a — a const-generic PARAM value carries no decidable
        // value, so its equality is UNKNOWN. Return `None` (verify BOTH branches),
        // NEVER `Some(false)` — answering "definitely unequal" for a const-param
        // that is in fact equal (`N == N`) would prune the taken branch and drop
        // its safety obligations (a false PROVE). This MUST precede the
        // `_ => Some(false)` catch-all, exactly like the `OpaqueScalar` arm. It is
        // sound EVEN for two SYNTACTICALLY-distinct params `M`, `N`: `None`
        // over-approximates (checks both sides), never merges them.
        (ConstValue::ConstParam { .. }, _) | (_, ConstValue::ConstParam { .. }) => None,
        _ => Some(false),
    }
}

/// True iff `target` is the `otherwise` arm of some `SwitchInt` whose
/// `exhaustive_enum_unreachable` flag is set — i.e. a TyCtxt-certified-exhaustive
/// enum-discriminant switch whose default is provably infeasible. Used to suppress
/// the redundant per-VC `Unreachable` obligation that the native CHC structural
/// proof already discharges (the flag is set only under the strict soundness gate
/// in `trust-mir-extract::mark_exhaustive_enum_unreachable_switches`).
pub(super) fn v2_is_exhaustive_enum_unreachable_target(func: &VerifiableFunction, target: BlockId) -> bool {
    func.body.blocks.iter().any(|b| {
        matches!(
            &b.terminator,
            Terminator::SwitchInt { otherwise, exhaustive_enum_unreachable: true, .. }
                if *otherwise == target
        )
    })
}

pub(super) fn v2_build_terminator_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<VerificationCondition> {
    let (kind, span) = match &block.terminator {
        // A bare `Unreachable` reached ONLY as the `otherwise` arm of an
        // exhaustive enum-discriminant `SwitchInt` (flag `exhaustive_enum_unreachable`,
        // set ONLY by trust-mir-extract's TyCtxt-vetted gate: single-assignment
        // `Discriminant(enum)` selector whose explicit cases equal the enum's FULL
        // tag set) is GENUINELY infeasible — `disc ∈ {cases}` is a type invariant.
        // The native CHC structural proof discharges it soundly (trust-ir-bridge
        // conjoins `disc ∈ {case tags}` on that edge, `assume_discriminant_in_cases`),
        // but the per-VC obligation's `Bool(true)` goal carries the un-lowerable
        // `Discriminant` def in its path facts and reports UNKNOWN. Suppress that
        // redundant per-VC obligation here. Soundness: a partial match / genuine
        // `unreachable_unchecked` keeps the flag FALSE, so its obligation is still
        // emitted and still refutes — only TyCtxt-certified-exhaustive arms are
        // suppressed. (The `?`/`Try`→`ControlFlow` desugar is one such arm.)
        Terminator::Unreachable if v2_is_exhaustive_enum_unreachable_target(func, block.id) => {
            return None;
        }
        Terminator::Unreachable => (VcKind::Unreachable, v2_block_span(func, block)),
        Terminator::Call { func: callee, span, .. } if v2_is_unreachable_panic_call(callee) => {
            (VcKind::Unreachable, span.clone())
        }
        // Trust: `unreachable!()` lowers to the BARE panic intrinsic
        // `core::panicking::panic("...entered unreachable code")`, which neither
        // recognizer above matched — so a dead `unreachable!()` branch got NO VC and
        // its modulo/path-guard facts had no goal to discharge. Emit an Assertion VC
        // (fail-closed `Bool(true)` goal that the path guard must refute). Scoped to
        // the unreachable SENTINEL message so `assert!`/`panic!` panic sites — which
        // share the `core::panicking::panic` callee but already have an obligation —
        // do NOT get a second, dataflow-starved VC that false-FAILs them.
        Terminator::Call { func: callee, args, span, .. }
            if v2_is_unreachable_sentinel_panic(callee, args) =>
        {
            let kind = if v2_is_unreachable_panic_chain(func, block.id) {
                VcKind::Unreachable
            } else {
                VcKind::Assertion { message: v2_panic_call_vc_message(func, callee, args) }
            };
            (kind, span.clone())
        }
        Terminator::Call { func: callee, args, span, .. } if v2_is_assertion_panic_call(callee) => {
            let kind = if v2_is_unreachable_panic_chain(func, block.id) {
                VcKind::Unreachable
            } else {
                VcKind::Assertion { message: v2_panic_call_vc_message(func, callee, args) }
            };
            (kind, span.clone())
        }
        _ => return None,
    };

    Some(VerificationCondition {
        kind,
        function: func.name.clone().into(),
        location: span,
        formula: Formula::Bool(true),
        contract_metadata: None,
    })
}
