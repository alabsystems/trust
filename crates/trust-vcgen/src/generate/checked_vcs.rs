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
    // The canonical assert polarity is PER-OP. rustc's flag-based arithmetic
    // asserts (the Add/Sub/Mul `.1` overflow flags and the computed Div/Rem
    // overflow/zero conditions) panic when the condition is TRUE, so their
    // normal edge is `expected == false`; a caller-constructed inverse assert
    // of that family has different semantics and must surface as a proof gap
    // rather than borrowing the overflow proposition. rustc's SHIFT asserts
    // have the OPPOSITE canonical polarity: the condition is the guard itself
    // (`cond = Lt(amount, BITS)`) and the normal edge requires it to HOLD
    // (`expected == true`). An exactly-bound canonical shift assert lowers to
    // the REAL shift-overflow obligation; any other shift shape (either
    // polarity) keeps the generic fall-through below, which proves EXACTLY the
    // runtime failure condition the terminator reads — never the target
    // operation's proposition (see
    // `target_operation_never_substitutes_for_a_caller_controlled_assert_condition`).
    if matches!(op, BinOp::Shl | BinOp::Shr) {
        if expected
            && let Some(vc) = v2_build_assert_shift_overflow_vc(func, block, target, op, cond, span)
        {
            return Some(vc);
        }
    } else if expected {
        return None;
    }

    if matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul)
        && let Some((stmt_index, lhs, rhs)) =
            v2_find_checked_binop_for_assert_cond(func, block, cond, op)
    {
        // Trust (width-soundness): the checked op's VALIDATED destination
        // payload type — field 0 of the `(int, bool)` tuple, pinned by
        // `validate_checked_assignment_types` — is the operation-width
        // authority. Without it, two widthless signed constants
        // (`CheckedAdd(100, 100)` into an `(i8, bool)` carrier) let
        // `int_op_type` fabricate i64 and the VC checks `200 outside i64`
        // (UNSAT → false PROVE) while the i8 operation overflows at runtime.
        let operation_ty = v2_checked_binop_payload_ty(func, block, stmt_index);
        return v2_build_overflow_vc_for_operands_typed(
            func,
            block,
            op,
            lhs,
            rhs,
            span,
            Some(stmt_index),
            operation_ty,
        );
    }

    // A message plus a unique same-op statement in the normal target is not a
    // binding between the public Assert condition and that operation. Preserve
    // the detailed kind/type diagnostic when a unique target exists, but prove
    // exactly the runtime failure condition read by the terminator. The target
    // operation receives its own per-statement safety VC independently.
    //
    // Trust (checked-flag alias clobber, fail-closed): when the exact-binding
    // matcher above refused because a LATER write — direct, projected, or
    // through a mutable alias — overlaps the observed `.1` overflow flag, the
    // old operand-based no-overflow proof is exactly what must NOT be reused.
    // But the assert is still a real arithmetic-overflow obligation over the
    // value the terminator actually reads, so recover the clobbered
    // CheckedBinaryOp purely for the kind's operand-type diagnostic and emit
    // the SAME terminator-condition formula as the target-block fall-through:
    // `block_defs AND assert-failure-condition`. The versioned block-defs pin
    // the flag to the clobbering write's value (or leave it unconstrained when
    // the write is opaque), so a forged failure value REFUTES (SAT -> Failed)
    // instead of falling to an UnsupportedMir proof gap no solver may decide.
    // A genuinely unfireable assert stays provable (UNSAT) on the same read.
    let (lhs, rhs) = v2_find_target_binary_operands(func, target, op)
        .map(|(_, _, lhs, rhs)| (lhs, rhs))
        .or_else(|| v2_find_clobbered_checked_binop_for_assert_cond(func, block, cond, op))?;
    let lhs_ty = crate::operand_ty(func, lhs)?;
    let rhs_ty = crate::operand_ty(func, rhs)?;
    Some(VerificationCondition {
        kind: VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) },
        function: func.name.as_str().into(),
        location: span.clone(),
        formula: v2_formula_with_block_defs(
            func,
            block,
            v2_assert_failure_formula(func, cond, expected),
        ),
        contract_metadata: None,
        obligation: None,
    })
}

/// Recover the CheckedBinaryOp whose overflow flag a `.1`-field assert condition
/// nominally observes, AFTER `v2_find_checked_binop_for_assert_cond` refused the
/// exact binding (a later overlapping write, or an unstable tuple local). Used
/// only for the `VcKind::ArithmeticOverflow` operand-type diagnostic — never as
/// a binding that would let the checked operation's own safety proof stand in
/// for the (possibly clobbered) flag value the terminator reads. The latest
/// whole-local same-op definition is taken; `None` when the condition is not a
/// tuple-local `.1` read or no such definition exists (the caller then keeps
/// the explicit `RecognizedSafetyAssertProofGap` row).
fn v2_find_clobbered_checked_binop_for_assert_cond<'a>(
    _func: &VerifiableFunction,
    block: &'a trust_types::BasicBlock,
    cond: &Operand,
    op: BinOp,
) -> Option<(&'a Operand, &'a Operand)> {
    if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
        return None;
    }
    let cond_place = match cond {
        Operand::Copy(p) | Operand::Move(p) => p,
        _ => return None,
    };
    if cond_place.projections.len() != 1 {
        return None;
    }
    let trust_types::Projection::Field(1) = &cond_place.projections[0] else {
        return None;
    };
    let tuple_local = cond_place.local;
    block.stmts.iter().rev().find_map(|stmt| match stmt {
        Statement::Assign { place, rvalue: Rvalue::CheckedBinaryOp(stmt_op, lhs, rhs), .. }
            if place.local == tuple_local && place.projections.is_empty() && *stmt_op == op =>
        {
            Some((lhs, rhs))
        }
        _ => None,
    })
}

/// The VALIDATED payload type of the `CheckedBinaryOp` at `stmt_index` — field 0
/// of its whole-tuple-local `(int, bool)` destination. This is the [10]-class
/// operation-width authority for the checked-assert overflow lane
/// (`validate_checked_assignment_types` pins the destination to exactly
/// `(supported fixed-width integer, bool)` and both operands to that payload
/// type). Returns `None` for any other shape, in which case the caller falls
/// back to operand-type inference (today's behavior — sound for any operand
/// that carries a real width, fabrication-prone only for the two-widthless-
/// constants shape that admission ties to a typed destination).
fn v2_checked_binop_payload_ty(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    stmt_index: usize,
) -> Option<Ty> {
    let Statement::Assign { place, .. } = block.stmts.get(stmt_index)? else {
        return None;
    };
    if !place.projections.is_empty() {
        return None;
    }
    let Ty::Tuple(fields) = crate::local_ty_ref(func, place.local)? else {
        return None;
    };
    if fields.len() != 2 || fields[1] != Ty::Bool {
        return None;
    }
    let payload = &fields[0];
    crate::fixed_width_integer_descriptor(payload).is_some().then(|| payload.clone())
}

/// The canonical rustc SHIFT assert — `cond = Lt(amount, BITS);
/// Assert(cond, expected: true, Overflow(Shl|Shr))` with the shift itself in the
/// assert's TARGET block — lowered to the REAL shift-overflow obligation.
/// (`CheckedBinaryOp(Shl|Shr)` does not exist: admission outlaws it — only
/// Add/Sub/Mul produce the audited `(value, bool)` carrier — and the extractor
/// never emits it, so the flag-based recovery path can never apply to shifts.)
///
/// FAIL-CLOSED BINDING, in the operand/cond-identity discipline (never bare
/// target identity):
///  * the assert cond's live definition must be exactly `Lt(amount, const BITS)`
///    with the comparison inputs stable through the terminator
///    (`v2_find_condition_binary_operands`);
///  * the target block must hold a UNIQUE same-op shift whose amount operand is
///    STRUCTURALLY the cond's `amount`, and no statement before the shift may
///    rewrite the amount (else the assert guards a different value than the
///    shift reads);
///  * `BITS` must equal the shift-RESULT width recovered from MIR
///    (`v2_shift_violation_formula`'s destination-type authority), so the assert
///    is the exact `amount < width` UB guard, not a lookalike.
/// Any mismatch returns `None` and the caller keeps the explicit
/// `RecognizedSafetyAssertProofGap` row.
///
/// The emitted VC is built over the ASSERT block (`stmt_index = None`), exactly
/// like the historical assert-driven shift path: the violation reads the amount
/// at the assert point (verified identical to the shift's read by the
/// no-rewrite checks above), and the by-operands width recovery inside
/// `v2_shift_violation_formula` supplies the true shifted width even for a
/// widthless-constant shifted value (`1i128 << k`).
fn v2_build_assert_shift_overflow_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    target: BlockId,
    op: BinOp,
    cond: &Operand,
    span: &SourceSpan,
) -> Option<VerificationCondition> {
    let (_, lhs, rhs, shifted_width) =
        v2_shift_assert_binds_statement(func, block, target, op, cond)?;
    // Trust (SHIFT-BINDER-RESIDUE-1, 2026-10-11): built at the width the binder
    // resolved for THE BOUND STATEMENT, the width the statement-lane row it
    // suppresses is built at. Recovering it here instead (`stmt_index = None`
    // falls to the by-operands MINIMUM over every matching shift) put a different
    // width on the surviving row than on the suppressed one.
    v2_build_shift_overflow_vc(func, block, op, lhs, rhs, span, V2ShiftSite::Bound(shifted_width))
}

/// THE shift assert/statement binding, factored out of
/// [`v2_build_assert_shift_overflow_vc`] so the assert lane that EMITS the row
/// and the statement lane that SUPPRESSES its vacuous duplicate
/// ([`v2_shift_assert_exactly_bound`]) decide identity with one predicate rather
/// than two that can drift apart. Returns the bound `(stmt_index, lhs, rhs)` of
/// the shift in `target`, or `None` for any non-canonical shape.
///
/// The three fail-closed criteria are exactly the ones documented on
/// [`v2_build_assert_shift_overflow_vc`]: the cond's live definition is
/// `Lt(amount, const BITS)` with stable inputs, `target` holds a UNIQUE same-op
/// plain-`BinaryOp` shift whose amount is STRUCTURALLY the cond's `amount` (or,
/// for a SIGNED amount, the source of rustc's same-width `as uW` cast that
/// `amount` is: [`v2_shift_amount_cast_source`]) and is not rewritten before the
/// shift reads it, and `BITS` equals the true shift-RESULT width OF THAT
/// STATEMENT. The returned `u32` is that width, so the assert lane builds its row
/// at exactly the width the statement lane builds the row it suppresses.
///
/// Trust (SHIFT-BINDER-RESIDUE-1, 2026-10-11): the two refusals this closes, each
/// measured to leave a vacuous `shift:*` row `proved` (one kernel-certified) at the
/// span of a shift that panics, beside the assert lane's generic `overflow` row:
///  * THE WIDTH. `(1i64 << n, 1i8 << n)` shifts the same widthless `Int(1)` by the
///    same amount twice, so the by-operands recovery (which takes the MINIMUM over
///    every operand-matching shift) answered 8 for BOTH asserts, and the first
///    (`Lt(n, 64)`) never bound. The width now comes from the bound statement's own
///    destination, through the statement lane's own recovery.
///  * THE SIGNED AMOUNT. `x << s` with `s: i32` lowers its check through a cast
///    temporary (`_t = s as u32; Lt(move _t, 32)`), so `amount` is `_t`, never the
///    shift's `s`.
fn v2_shift_assert_binds_statement<'a>(
    func: &'a VerifiableFunction,
    block: &trust_types::BasicBlock,
    target: BlockId,
    op: BinOp,
    cond: &Operand,
) -> Option<(usize, &'a Operand, &'a Operand, u32)> {
    // PROJECTED comparison inputs are the REAL rustc lowering here, not a
    // hypothetical: `1u32 << t` with `let t = (x | 64) + 1` extracts as
    // `_4 = Lt(Copy _3.0, const 32u32); assert(_4, Overflow(Shl))`, whose input
    // is `_3.0` — the value field of the CheckedAdd tuple. The projection-free
    // finder refuses that, and because c67021cd0d made THIS predicate serve both
    // shift lanes so they cannot drift apart, its `None` moved both at once: the
    // assert lane fell through to a generic `ArithmeticOverflow` row while the
    // per-statement `ShiftOverflow` row — the VACUOUS one, under the assert's own
    // `AssertHolds` guard, whose violation is `_4 AND NOT _4` — survived as the
    // ONLY `shift:left` row at the span and read `proved` on a genuinely-UB
    // shift. Selecting the projection-aware SIBLING here is the opt-in its own
    // doc names ("Until that call site selects this rule the projected shape
    // stays broken"); the projection-free rule stays in force for the bounds,
    // div/rem and arithmetic lanes that share it.
    let (cmp_index, BinOp::Lt, amount, bits) =
        v2_find_projected_condition_binary_operands(func, block, cond)?
    else {
        return None;
    };
    let bits_value = const_int_value(bits)?;
    let shift_block = func.body.blocks.get(target.0)?;
    let (stmt_index, lhs, rhs) = v2_find_block_binary_operands(shift_block, op)?;
    // The bound statement must be the plain `BinaryOp` spelling (the finder also
    // matches the checked carrier, which admission rejects for shifts anyway).
    let Some(Statement::Assign { rvalue: Rvalue::BinaryOp(..), .. }) =
        shift_block.stmts.get(stmt_index)
    else {
        return None;
    };
    // The amount the assert compared is the shift's own `rhs`: directly (an
    // unsigned amount), or as the source of rustc's same-width `as uW` cast (a
    // signed one — see `v2_shift_amount_cast_source` for why `src as uW < BITS`
    // is exactly the signed shift's `0 <= src < BITS`).
    let same_amount_and_rhs = v2_operands_structurally_equal(rhs, amount);
    let amount_is_rhs = same_amount_and_rhs
        || v2_shift_amount_cast_source(func, block, cmp_index, amount, bits_value)
            .is_some_and(|src| v2_operands_structurally_equal(rhs, src));
    if !amount_is_rhs {
        return None;
    }
    // BITS must be exactly the true shifted width OF THE BOUND STATEMENT; a
    // lookalike guard against a different constant is not this shift's UB check.
    // Resolved exactly as the statement lane resolves it for its own row (the
    // shift's block and statement index: the destination's width first), never
    // from the assert block, where only the by-operands MINIMUM over every
    // matching shift is available (SHIFT-BINDER-RESIDUE-1, above).
    let shifted_width = v2_shift_resolved_width(
        func,
        shift_block,
        op,
        lhs,
        rhs,
        V2ShiftSite::Statement(stmt_index),
    )?;
    if i128::from(shifted_width) != bits_value {
        return None;
    }
    // The amount the assert guarded must be the amount the shift reads: refuse
    // if any target-block statement before the shift rewrites it. In the cast
    // case the shift reads `rhs` (the cast's source), so that is checked too.
    if stmt_index > 0 {
        for (idx, read) in [amount, rhs].into_iter().enumerate() {
            if idx == 1 && same_amount_and_rhs {
                break;
            }
            if let Operand::Copy(p) | Operand::Move(p) = read {
                let name = crate::place_to_var_name(func, p);
                if (0..stmt_index).any(|k| stmt_writes_name(func, shift_block, k, &name)) {
                    return None;
                }
            }
        }
    }
    Some((stmt_index, lhs, rhs, shifted_width))
}

/// rustc's lowering of a SIGNED shift amount: the overflow check compares a
/// same-width UNSIGNED cast temporary, not the amount itself
/// (`rustc_mir_build`'s `build_binary_op`), e.g. for `x << s`, `s: i32`:
///
/// ```text
/// bb0: _3 = Cast(Copy _2, u32); _4 = Lt(Move _3, const 32_u32);
///      assert(Move _4, Overflow(Shl)) -> bb1
/// bb1: _0 = Shl(Copy _1, Copy _2)
/// ```
///
/// (and `_2 = Cast(const N, u32)` for `x << N`, `N: i32`). Returns the cast's
/// SOURCE when `amount` (the `Lt`'s left input at `cmp_index` in the assert
/// `block`) is exactly such a temporary, so the binder can compare it with the
/// shift's `rhs`; `None` for every other shape.
///
/// WHY THE BINDING IS EXACT. For `src: iW`, `src as uW` is `src` when `src >= 0`
/// and `src + 2^W >= 2^(W-1)` when `src < 0`. So while `BITS <= 2^(W-1)`, the
/// assert's `(src as uW) < BITS` holds exactly when `0 <= src < BITS`, which is
/// the signed shift's own no-UB condition (`v2_shift_violation_formula` refutes
/// `src < 0 || src >= BITS`). `BITS` is at most 128 and `W` at least 8, so the
/// bound always holds for a real shift; it is checked anyway.
///
/// FAIL-CLOSED. The extracted `Rvalue::Cast` carries no `CastKind`, so the kind
/// is pinned by TYPES, as `trust_types::admissible_body` pins it: the source is a
/// SIGNED integer of width `W` and the target (the cast type AND the temporary's
/// declared type) the UNSIGNED integer of the SAME width. An integer-to-integer
/// cast is the only kind with that signature. Refused: a truncating or widening
/// cast, an unsigned source, a temporary that is a parameter or the return place,
/// a temporary whose last write before the comparison is not this cast, a
/// projected or unstable source place, a source place rewritten after the cast
/// in this block, and every non-literal constant source without a value identity.
/// The comparison's own finder already refused a temporary rewritten after the
/// comparison.
///
/// A width-less signed LITERAL source (`x << 40`: `_t = Cast(const 40, u32)`) has no
/// type to pin (`operand_ty` fabricates i64 for it), so it is admitted by VALUE
/// instead: the literal must lie in `iW`. Since `L as uW` is `L mod 2^W` whatever the
/// literal's own integer type, the exactness argument above holds unchanged, and a
/// literal has no rewrite window to scan. A literal outside `iW` is refused
/// (SELF-GUARDED-LITERAL-OPERAND-2; before it, every literal kept the refusal).
fn v2_shift_amount_cast_source<'b>(
    func: &VerifiableFunction,
    block: &'b trust_types::BasicBlock,
    cmp_index: usize,
    amount: &Operand,
    bits_value: i128,
) -> Option<&'b Operand> {
    let (Operand::Copy(temp) | Operand::Move(temp)) = amount else {
        return None;
    };
    if cmp_index == 0
        || !temp.projections.is_empty()
        || temp.local == 0
        || temp.local <= func.body.arg_count
    {
        return None;
    }
    let Some(&Ty::Int { width, signed: false }) = crate::local_ty_ref(func, temp.local) else {
        return None;
    };
    // `2^(W-1)` as a `u128`: at `W = 128` it does not fit an `i128`.
    if !(8..=128).contains(&width)
        || bits_value <= 0
        || bits_value.unsigned_abs() > 1u128 << (width - 1)
    {
        return None;
    }
    // The cast must be the temporary's LIVE definition at the comparison.
    // Because `temp` is projection-free, any direct `Assign` to `temp` writes
    // `temp_name`; find the last direct assignment first, validate its `Cast`
    // shape, and only scan `(cast_index + 1..prefix_end)` for an intervening
    // alias/deref write when statements exist between the cast and the comparison.
    let prefix_end = cmp_index.min(block.stmts.len());
    let cast_index = (0..prefix_end).rev().find(|&k| {
        matches!(&block.stmts[k], Statement::Assign { place, .. } if place == temp)
    })?;
    let Statement::Assign { rvalue: Rvalue::Cast(src, cast_ty), .. } =
        &block.stmts[cast_index]
    else {
        return None;
    };
    if *cast_ty != (Ty::Int { width, signed: false }) {
        return None;
    }
    if cast_index + 1 < prefix_end {
        let temp_name = crate::place_to_var_name(func, temp);
        if (cast_index + 1..prefix_end).any(|k| stmt_writes_name(func, block, k, &temp_name)) {
            return None;
        }
    }
    // Trust (SELF-GUARDED-LITERAL-OPERAND-2, 2026-10-13): a width-less signed LITERAL
    // source (`x << 40`, whose amount defaults to `i32`: `_t = Cast(const 40, u32)`).
    // `operand_ty` FABRICATES i64 for it, so the type pin below can never hold at
    // `W = 32` and the literal kept the refusal it had: the statement-lane `shift:*`
    // row, under the assert's own `AssertHolds` guard (`40 < 32` is false, so UNSAT
    // by construction), shipped kernel-certified at the span of a shift that panics on
    // every call, beside the assert lane's FAILED generic `overflow` row.
    //
    // The pin is replaced by a VALUE check: `L` lies in `iW`'s two's-complement range.
    // For ANY integer source, `L as uW` is `L mod 2^W`, so for `L` in `iW` it is `L`
    // when `L >= 0` and `L + 2^W >= 2^(W-1) >= BITS` when `L < 0`: the assert's
    // `(L as uW) < BITS` holds exactly when `0 <= L < BITS`, the signed shift's own
    // no-UB condition, as for a place source (the argument above). A literal has no
    // rewrite window, so the place arm's stability scans have nothing to scan, and the
    // caller's `v2_operands_structurally_equal(rhs, src)` pins VALUE identity with
    // the shift's own literal amount. A literal outside `iW` is refused, which keeps
    // both rows.
    if let Operand::Constant(ConstValue::Int(value)) = src {
        // `W = 128` admits every `i128`; below it, `-2^(W-1) <= L < 2^(W-1)`.
        let fits = width == 128 || {
            let half = 1i128 << (width - 1);
            (-half..half).contains(value)
        };
        return fits.then_some(src);
    }
    if crate::operand_ty_cow(func, src).as_deref() != Some(&Ty::Int { width, signed: true }) {
        return None;
    }
    match src {
        Operand::Copy(p) | Operand::Move(p) => {
            if !p.projections.is_empty() || crate::guards::value_local_is_unstable(func, p.local) {
                return None;
            }
            if cast_index + 1 < block.stmts.len() {
                let name = crate::place_to_var_name(func, p);
                if (cast_index + 1..block.stmts.len())
                    .any(|k| stmt_writes_name(func, block, k, &name))
                {
                    return None;
                }
            }
        }
        Operand::Constant(value) if v2_const_has_symbolic_identity(value) => {}
        _ => return None,
    }
    Some(src)
}

/// Whether an `Assert { Overflow(Shl | Shr), expected: true }` somewhere in the
/// function is EXACTLY BOUND to the `op` statement at `(shift_block,
/// stmt_index)` over operands `(lhs, rhs)` — the canonical rustc chain
///
/// ```text
/// _c = Lt(amount, const BITS); assert(move _c, Overflow(op)) -> shift_block;
/// shift_block: ... = BinaryOp(op, lhs, amount)
/// ```
///
/// THE SHIFT MEMBER OF THE SAME FAMILY AS
/// [`v2_divrem_overflow_assert_exactly_bound`] and
/// [`v2_divzero_assert_exactly_bound`], and for the same reason. Under this
/// binding the assert-lane row states EXACTLY the same proposition as the
/// per-statement `VcKind::ShiftOverflow` row — literally so: both are built by
/// [`v2_build_shift_overflow_vc`] from the same `(op, lhs, rhs)`. The
/// per-statement row sits in the assert's TARGET block, where the threaded
/// `AssertHolds` path guard discharges it VACUOUSLY: on the real canary MIR its
/// formula is
///
/// ```text
/// (and (= _2 (bv2nat (bvor x 64))) (= _3 (< _2 32))
///      (and _3 ... (>= _2 32)))
/// ```
///
/// — it binds `_3 = (_2 < 32)`, then asserts `_3` AND `_2 >= 32`, i.e. `_3 AND
/// NOT _3`, UNSAT by construction for every program. It can never fail and
/// discharges nothing, but it shipped in the structured transport as a `proved`
/// `shift:left` row at the exact span of a genuinely-false shift overflow, which
/// is how `clean/tests/trust_verify/vacuity_sentinel.rs`'s
/// `sentinel_shift_overflow_must_not_prove` came to be reported CERTIFIED.
///
/// WHY THIS IS NOT A NEW POLARITY ARM ON THE DIV/REM RULES. `Overflow(Shl|Shr)`'s
/// canonical MIR assert expects `true` (the cond IS the guard); `Overflow(Div|Rem)`
/// and `DivisionByZero` expect `false` (the cond is the failure condition). The
/// cond shapes differ too — one `Lt(amount, BITS)` against the shift-RESULT width
/// versus `BitAnd(Eq(rhs, -1), Eq(lhs, INT_MIN))` at the operation width, or
/// `Eq(divisor, 0)` — and the div/rem overflow rule is signed-only while the shift
/// obligation exists at both signednesses. Parameterizing one rule over all of
/// that would put the div/rem suppressions and this one on a single code path
/// where a slip loosens three rules at once.
///
/// Same fail-closed discipline as both twins, and it is load-bearing: bare target
/// identity is NEVER suppression authority, the compared values must be
/// rewrite-stable between the comparison and the read, and the shift's block must
/// have the bound assert's success edge as its SOLE entry, so a forged body cannot
/// launder the obligation through an assert its executions can bypass. Any
/// non-canonical shape returns `false`, keeping both rows — duplicates
/// over-report, never under-report.
pub(super) fn v2_shift_assert_exactly_bound(
    func: &VerifiableFunction,
    op: BinOp,
    shift_block_id: BlockId,
    stmt_index: usize,
    lhs: &Operand,
    rhs: &Operand,
) -> bool {
    if !matches!(op, BinOp::Shl | BinOp::Shr)
        || shift_block_id.0 == 0
        || !super::terminator_presence_for(func).has_overflow_assert
    {
        return false;
    }
    let Some(op_block) = func.body.blocks.get(shift_block_id.0) else {
        return false;
    };
    let Some((found_index, found_lhs, found_rhs)) = v2_find_block_binary_operands(op_block, op)
    else {
        return false;
    };
    if found_index != stmt_index
        || !v2_operands_structurally_equal(found_lhs, lhs)
        || !v2_operands_structurally_equal(found_rhs, rhs)
    {
        return false;
    }
    // The compared values must not be rewritten before the shift reads them.
    // (The binder already enforces this for the amount; the shifted value is
    // added here for the same reason, so the suppressed row's operands are the
    // ones the surviving row was bound over.)
    //
    // PERF-COMPILER-VCGEN-799: evaluated lazily, only once a candidate assert has
    // passed its cheap structural checks (terminator shape, op, target, unwind),
    // so a shift with no bound assert never allocates operand names or scans the
    // prefix. The answer is identical: a `false` here still refuses every candidate.
    let operands_stable: std::cell::OnceCell<bool> = std::cell::OnceCell::new();
    let operands_stable_now = || {
        *operands_stable.get_or_init(|| {
            if stmt_index == 0 {
                return true;
            }
            let same_operands = v2_operands_structurally_equal(lhs, rhs);
            for (idx, operand) in [lhs, rhs].into_iter().enumerate() {
                if idx == 1 && same_operands {
                    break;
                }
                if let Operand::Copy(p) | Operand::Move(p) = operand {
                    let name = crate::place_to_var_name(func, p);
                    if (0..stmt_index).any(|k| stmt_writes_name(func, op_block, k, &name)) {
                        return false;
                    }
                }
            }
            true
        })
    };

    let check_candidate =
        |assert_block: &trust_types::BasicBlock, sole_entry_verified: bool| -> bool {
            let Terminator::Assert {
                cond,
                expected: true,
                msg: AssertMessage::Overflow(assert_op),
                target,
                ..
            } = &assert_block.terminator
            else {
                return false;
            };
            if *assert_op != op || *target != shift_block_id {
                return false;
            }
            // PARITY with the bounds member (block_defs.rs): the assert's FAILURE /
            // cleanup edge runs exactly when the checked condition is violated, so
            // it must not re-enter the block whose rows this would suppress.
            // Excluding only `assert_block.id` from the scan below leaves that edge
            // invisible, and a row reachable through it is REFUTABLE, not vacuous.
            if assert_block.terminator.unwind_cleanup_target() == Some(shift_block_id) {
                return false;
            }
            if !operands_stable_now() {
                return false;
            }
            // The assert lane's OWN binder decides identity, so the suppression can
            // only fire where that lane really emits the equivalent row.
            // PERF-COMPILER-VCGEN-806: asked before the O(blocks) sole-entry scan
            // below; both are pure conjuncts of the same answer.
            let Some((found_index, found_lhs, found_rhs, _)) =
                v2_shift_assert_binds_statement(func, assert_block, *target, op, cond)
            else {
                return false;
            };
            if found_index != stmt_index
                || !v2_operands_structurally_equal(found_lhs, lhs)
                || !v2_operands_structurally_equal(found_rhs, rhs)
            {
                return false;
            }
            // Sole-entry check: no OTHER block's terminator may reach the shift's
            // block, so the surviving assert row covers every execution of the
            // shift.
            sole_entry_verified
                || !func.body.blocks.iter().any(|b| {
                    b.id != assert_block.id && b.terminator.has_exit_block_target(shift_block_id)
                })
        };

    if let Some(unique_pred) = crate::fn_memo::sole_predecessors(func)
        .and_then(|sp| sp.unique_exit_predecessor(shift_block_id))
    {
        return unique_pred
            .and_then(|pred_id| func.body.blocks.get(pred_id.0))
            .is_some_and(|assert_block| check_candidate(assert_block, true));
    }

    func.body.blocks.iter().any(|assert_block| check_candidate(assert_block, false))
}

/// Whether neither `lhs` nor `rhs` (each a place, or skipped when a constant) is
/// written by any of `op_block.stmts[..stmt_index]`, i.e. the values an assert
/// compared are the values the operation at `stmt_index` reads.
///
/// BUDGET POLL, per STATEMENT probe. Written as a loop rather than
/// `(0..stmt_index).any(..)` because a poll outside it could not interrupt ONE
/// scan: `stmt_writes_name` rebuilds the block's `deref_store_havoc_names` set at
/// every opaque deref-store, so this rewrite-stability scan is
/// O(stmt_index x block) by itself. An exhausted budget answers `false` — the SAME
/// value a genuinely rewritten operand returns — which declines every suppression
/// that asks (fail-closed: both rows are emitted, PROVE-to-FAIL only).
///
/// PERF-COMPILER-VCGEN-800: factored out of the div/rem binders so they can ask it
/// LAZILY, after a candidate assert has passed its cheap structural checks.
fn v2_binop_operands_unwritten_before(
    func: &VerifiableFunction,
    op_block: &trust_types::BasicBlock,
    stmt_index: usize,
    lhs: &Operand,
    rhs: &Operand,
) -> bool {
    if stmt_index == 0 {
        return true;
    }
    let same_operands = v2_operands_structurally_equal(lhs, rhs);
    for (idx, operand) in [lhs, rhs].into_iter().enumerate() {
        if idx == 1 && same_operands {
            break;
        }
        if let Operand::Copy(p) | Operand::Move(p) = operand {
            let name = crate::place_to_var_name(func, p);
            for k in 0..stmt_index {
                if trust_types::verify_budget::budget_exhausted()
                    || stmt_writes_name(func, op_block, k, &name)
                {
                    return false;
                }
            }
        }
    }
    true
}

/// Whether an `Assert { Overflow(Div|Rem), expected: false }` somewhere in the
/// function is EXACTLY BOUND to the `op` statement at `(div_block, stmt_index)`
/// over operands `(lhs, rhs)` — the canonical rustc chain
///
/// ```text
/// _a = Eq(rhs, const -1); _b = Eq(lhs, const INT_MIN);
/// _c = BitAnd(_a, _b);    assert(!move _c, Overflow(op)) -> div_block;
/// div_block: ... = BinaryOp(op, lhs, rhs)
/// ```
///
/// with every read stable (no rewrite of the compared values between their
/// comparison and either read point) and `INT_MIN` at the operation's true
/// width. Under this binding the assert-lane row
/// (`v2_build_assert_overflow_vc`'s target fall-through) states EXACTLY the
/// same proposition as the per-statement `v2_build_signed_div_overflow_vc` row,
/// so the caller may suppress the per-statement duplicate: the surviving
/// assert-lane row is the refutable one (the statement row sits in the assert's
/// TARGET block, where the threaded `AssertHolds` path guard discharges it
/// vacuously), so exactly one live obligation remains.
///
/// THE SURVIVOR EXISTS STRUCTURALLY, not incidentally — a suppression that fires
/// where the assert lane emits nothing would DELETE the obligation, not
/// deduplicate it. Under this binding it cannot:
/// `v2_overflow_assert_provably_cannot_fire` recovers operands only from a
/// `.1`-FIELD cond, while `v2_find_condition_binary_operands` here demands a
/// projection-free one, so it can never suppress the assert row; `Div`/`Rem` skip
/// `v2_build_assert_overflow_vc`'s checked-flag branch and land on its target
/// fall-through, whose `v2_find_target_binary_operands` is the same unique-statement
/// rule this binder re-checks; its two `operand_ty` reads are exactly the two
/// `v2_build_signed_div_overflow_vc` performs first, so the suppressed row could not
/// exist where the surviving one does not; and this binder takes its width from
/// [`literal_pair_int_type`], the one the builder takes, so it never decides about a
/// row built at a different width (and where that width is unresolvable it keeps
/// both rows). This is an exact
/// operand/cond-identity suppression — a bare "an assert targets this block" is
/// NEVER authority (see the plain-arm comment in `safety.rs`), and any
/// non-canonical shape returns `false`, keeping both rows (fail-closed:
/// duplicates over-report, never under-report).
pub(super) fn v2_divrem_overflow_assert_exactly_bound(
    func: &VerifiableFunction,
    op: BinOp,
    div_block: BlockId,
    stmt_index: usize,
    lhs: &Operand,
    rhs: &Operand,
) -> bool {
    // The suppression is sound only when the SURVIVING assert row covers every
    // execution of the operation. The assert row proves the cond read at ITS
    // terminator, so an operation block with any other way in (a second
    // predecessor edge, or being the entry block) keeps its own row — a forged
    // body must not launder the obligation through an assert its executions can
    // bypass.
    if !matches!(op, BinOp::Div | BinOp::Rem)
        || div_block.0 == 0
        || !super::terminator_presence_for(func).has_overflow_assert
    {
        return false;
    }
    let Some(op_block) = func.body.blocks.get(div_block.0) else {
        return false;
    };
    // The width whose INT_MIN the per-statement row proves about — the same
    // recovery `v2_build_signed_div_overflow_vc` uses. A non-signed operation
    // has no overflow row to deduplicate.
    //
    // Trust (LITERAL-PAIR-WIDTH-1, SELF-GUARDED-LITERAL-OPERAND-2, 2026-10-13):
    // `literal_pair_int_type`, not `int_op_type`, IN LOCKSTEP with the row builder:
    // for two width-less literals (`i32::MIN / -1`) `int_op_type` answers i64, the
    // canonical cond's `Eq(const -2147483648, const -2147483648)` never matched
    // `i64::MIN`, and the statement-lane row — built at the same i64, `lhs ==
    // i64::MIN` UNSAT — shipped kernel-certified beside the FAILED assert row. At the
    // destination width the cond binds by `v2_eq_def_binds_divrem_overflow_operand`'s
    // constant arm, exactly as `i64::MIN / -1` always did. `None` (an unresolvable
    // destination) keeps both rows, and the builder then emits its unknown row.
    let Some((width, signed)) = literal_pair_int_type(func, op_block, stmt_index, lhs, rhs) else {
        return false;
    };
    if !signed {
        return false;
    }
    let int_min = crate::range::signed_min(width);

    // The assert lane binds its fall-through row through
    // `v2_find_target_binary_operands`, which demands a UNIQUE same-op
    // statement; check uniqueness once upfront before scanning statements,
    // predecessors, or candidate assert blocks.
    let Some((found_index, found_lhs, found_rhs)) = v2_find_block_binary_operands(op_block, op)
    else {
        return false;
    };
    if found_index != stmt_index
        || !v2_operands_structurally_equal(found_lhs, lhs)
        || !v2_operands_structurally_equal(found_rhs, rhs)
    {
        return false;
    }

    // The compared values must not be rewritten before the division reads them.
    // PERF-COMPILER-VCGEN-800: asked lazily (once), only after a candidate assert
    // passes its cheap terminator checks; see `v2_binop_operands_unwritten_before`
    // for the budget discipline, which is unchanged (`false` declines).
    let operands_stable: std::cell::OnceCell<bool> = std::cell::OnceCell::new();
    let operands_stable_now = || {
        *operands_stable
            .get_or_init(|| v2_binop_operands_unwritten_before(func, op_block, stmt_index, lhs, rhs))
    };

    if let Some(unique_pred) =
        crate::fn_memo::sole_predecessors(func).and_then(|sp| sp.unique_exit_predecessor(div_block))
    {
        if trust_types::verify_budget::budget_exhausted() {
            return false;
        }
        let Some(assert_block) = unique_pred.and_then(|pred_id| func.body.blocks.get(pred_id.0))
        else {
            return false;
        };
        if !matches!(&assert_block.terminator, Terminator::Assert { target, .. } if *target == div_block)
            || assert_block.terminator.unwind_cleanup_target() == Some(div_block)
            || !operands_stable_now()
        {
            return false;
        }
        return v2_divrem_overflow_assert_binds_statement(
            func,
            op,
            assert_block,
            div_block,
            op_block,
            stmt_index,
            lhs,
            rhs,
            int_min,
            v2_eq_def_binds_divrem_overflow_operand,
            v2_eq_def_binds_divrem_overflow_operand,
        );
    }

    // Written as an explicit loop rather than `blocks.iter().any(..)` so an
    // exhausted budget can leave the FUNCTION: a `return false` inside an `.any`
    // closure only rejects the current candidate and the scan keeps running.
    // Every closure-level `return false` below is a `continue` here and the
    // match arm is a `return true`, so the non-exhausted path is unchanged.
    for assert_block in func.body.blocks.iter() {
        // BUDGET POLL, per candidate assert block: this scan is O(blocks), and
        // each candidate that survives the two cheap terminator tests costs a
        // second O(blocks) sole-entry scan plus a full cond/operand binder walk,
        // so the pair is quadratic in the block count and had no poll at all.
        // Exhaustion returns `false` — the value every non-canonical shape
        // already returns — so no suppression fires and the assert-lane row and
        // the per-statement row are BOTH emitted. Extra rows over-report
        // (PROVE-to-FAIL); only a `true` here could delete an obligation, and
        // exhaustion never produces one.
        if trust_types::verify_budget::budget_exhausted() {
            return false;
        }
        if !matches!(&assert_block.terminator, Terminator::Assert { target, .. } if *target == div_block)
        {
            continue;
        }
        // PARITY with the bounds member (block_defs.rs): the assert's FAILURE /
        // cleanup edge runs exactly when the checked condition is violated, so
        // it must not re-enter the block whose rows this would suppress. The
        // scan below excludes `assert_block.id`, which leaves that edge
        // invisible; a row reachable through it is REFUTABLE, not vacuous.
        if assert_block.terminator.unwind_cleanup_target() == Some(div_block) {
            continue;
        }
        if !operands_stable_now() {
            return false;
        }
        // PERF-COMPILER-VCGEN-806: the binder (scans of this block and the op
        // block) before the O(blocks) sole-entry scan; both are pure conjuncts.
        if !v2_divrem_overflow_assert_binds_statement(
            func,
            op,
            assert_block,
            div_block,
            op_block,
            stmt_index,
            lhs,
            rhs,
            int_min,
            v2_eq_def_binds_divrem_overflow_operand,
            v2_eq_def_binds_divrem_overflow_operand,
        ) {
            continue;
        }
        // Sole-entry check: no OTHER block's terminator may reach the
        // operation's block (the bound assert's own success edge is the one
        // permitted way in; the assert terminator has no second normal edge to
        // the same block, and a cleanup edge into it from anywhere else counts
        // as a bypass).
        //
        // BUDGET POLL, per SCANNED block: the per-candidate poll above cannot
        // interrupt ONE sole-entry scan, which walks every block and allocates a
        // fresh `exit_targets` Vec for each. The two outcomes are deliberately
        // distinct — a bypass rejects this candidate and moves to the next, an
        // exhausted budget stops deciding altogether — and both are fail-closed,
        // since the function-level `false` keeps both rows.
        let mut bypassed = false;
        for b in func.body.blocks.iter() {
            if trust_types::verify_budget::budget_exhausted() {
                return false;
            }
            if b.id != assert_block.id && b.terminator.has_exit_block_target(div_block) {
                bypassed = true;
                break;
            }
        }
        if bypassed {
            continue;
        }
        return true;
    }
    false
}

/// A `flag = Eq(value, const)` binder: `(func, block, before, flag,
/// expected_operand, const_value) -> bool`. The three implementations differ in
/// EXACTLY ONE dimension — which COMPARED VALUES they admit ([`V2ComparedValue`])
/// — and are otherwise one rule, shared verbatim by
/// [`v2_eq_def_binds_compared_value`]: live-def reverse scan, const identity,
/// structural operand equality, stability of the compared value through the
/// terminator read. Passing the rule explicitly at each call site is how that
/// dimension stays visible instead of being smuggled in by a default. Two more,
/// [`v2_eq_def_binds_chain_dividend`] (the chain's dividend conjunct) and
/// [`v2_eq_def_binds_divisor`] (the zero assert's own cond and the chain's divisor
/// conjunct), are the projected rule OR an exact literal-value identity, for the
/// zero-divisor binding only (SELF-GUARDED-LITERAL-OPERAND-1).
type V2EqConstBinder =
    fn(&VerifiableFunction, &trust_types::BasicBlock, usize, &Operand, &Operand, i128) -> bool;

/// Whether `assert_block`'s OWN `Assert { Overflow(op), expected: false } ->
/// div_block` terminator is EXACTLY BOUND, by cond and operand identity, to the
/// unique `op` statement at `(op_block, stmt_index)` over `(lhs, rhs)`.
///
/// The IDENTITY half of [`v2_divrem_overflow_assert_exactly_bound`], factored out
/// so the SIGNED zero-divisor chain (see
/// [`v2_divzero_signed_chain_binds_operation`]) decides "is this block the
/// canonical intervening overflow assert for this very operation?" with the
/// overflow lane's own rule instead of a second transcription of it that could
/// drift. The CFG-SHAPE half stays with each caller on purpose: the direct caller
/// has one edge to pin, the chain caller has two, and a shared "good enough" edge
/// rule would be the weaker of them.
///
/// The two binders exist because the two callers meet this cond at different
/// operand shapes, MEASURED not assumed. Both need PROJECTION tolerance — on the
/// real extraction the value compared here is `_3.0`, the value field of a
/// `CheckedAdd`/`CheckedSub` tuple — and they differ on CONSTANTS.
/// `v2_divrem_overflow_assert_exactly_bound` passes
/// [`v2_eq_def_binds_divrem_overflow_operand`] for BOTH conjuncts, which admits
/// one, because `i32::MIN / y` lowers to `Eq(const INT_MIN, const INT_MIN)` and
/// refusing it resurrects a vacuous row. The zero-divisor chain passes
/// [`v2_eq_def_binds_divisor`] for the DIVISOR conjunct (`divisor_binds`), which
/// refuses a literal compared against a PLACE divisor, because a const-false
/// `assert(2 == 0)` must not take a real divisor's obligation, and admits only the
/// exact literal identity of a literal divisor; and [`v2_eq_def_binds_chain_dividend`]
/// for the DIVIDEND conjunct (`min_binds`), which also admits the exact literal
/// identity of a literal dividend (SELF-GUARDED-LITERAL-OPERAND-1). Nothing else
/// about the rule moves.
#[allow(clippy::too_many_arguments)]
fn v2_divrem_overflow_assert_binds_statement(
    func: &VerifiableFunction,
    op: BinOp,
    assert_block: &trust_types::BasicBlock,
    div_block: BlockId,
    op_block: &trust_types::BasicBlock,
    stmt_index: usize,
    lhs: &Operand,
    rhs: &Operand,
    int_min: i128,
    divisor_binds: V2EqConstBinder,
    min_binds: V2EqConstBinder,
) -> bool {
    let Terminator::Assert {
        cond,
        expected: false,
        msg: AssertMessage::Overflow(assert_op),
        target,
        ..
    } = &assert_block.terminator
    else {
        return false;
    };
    if *assert_op != op || *target != div_block {
        return false;
    }
    // The assert lane binds its fall-through row through
    // `v2_find_target_binary_operands`, which demands a UNIQUE same-op
    // statement; require the same statement here so the suppressed row and
    // the surviving row are about one operation.
    let Some((found_index, found_lhs, found_rhs)) = v2_find_block_binary_operands(op_block, op)
    else {
        return false;
    };
    if found_index != stmt_index
        || !v2_operands_structurally_equal(found_lhs, lhs)
        || !v2_operands_structurally_equal(found_rhs, rhs)
    {
        return false;
    }
    // cond's live def must be `BitAnd(a, b)` with stable inputs.
    let Some((and_index, BinOp::BitAnd, a, b)) =
        v2_find_condition_binary_operands(func, assert_block, cond)
    else {
        return false;
    };
    // The two conjuncts must be the exact `rhs == -1` and `lhs == INT_MIN`
    // comparisons, in either order.
    let binds = |divisor_flag: &Operand, min_flag: &Operand| {
        divisor_binds(func, assert_block, and_index, divisor_flag, rhs, -1)
            && min_binds(func, assert_block, and_index, min_flag, lhs, int_min)
    };
    binds(a, b) || binds(b, a)
}

/// Whether an `Assert { DivisionByZero | RemainderByZero, expected: false }`
/// somewhere in the function is EXACTLY BOUND to the `op` statement at
/// `(div_block, stmt_index)` over operands `(lhs, divisor)` — the canonical
/// rustc chain
///
/// ```text
/// _c = Eq(divisor, const 0); assert(!move _c, DivisionByZero) -> div_block;
/// div_block: ... = BinaryOp(op, lhs, divisor)
/// ```
///
/// — or its SIGNED form, where rustc inserts one intervening overflow assert
/// between the zero check and the operation (see
/// [`v2_divzero_signed_chain_binds_operation`]).
///
/// THE ZERO-DIVISOR MEMBER OF THE SAME FAMILY AS
/// [`v2_divrem_overflow_assert_exactly_bound`], and for the same reason. Under
/// this binding the assert-lane row states EXACTLY the same proposition as the
/// per-statement `VcKind::DivisionByZero`/`RemainderByZero` row, and the
/// per-statement row sits in the assert's TARGET block, where the threaded
/// `AssertHolds` path guard discharges it VACUOUSLY: its violation formula
/// reduces to `divisor != 0 && divisor == 0`, UNSAT by construction for every
/// program. It can never fail and discharges nothing — but it was published in
/// the structured transport as a `proved` `divzero`/`remzero` row at the exact
/// span of a genuinely-false division by zero, which is how
/// `clean/tests/trust_verify/vacuity_sentinel.rs`'s
/// `sentinel_div_by_zero_must_not_prove` came to be reported CERTIFIED.
///
/// Same fail-closed discipline as the overflow twin, and it is load-bearing:
/// bare target identity is NEVER suppression authority (a const-false
/// `assert(2 == 0)` targeting a block that also divides by a variable `y` must
/// not take `x / y`'s obligation), the compared value must be rewrite-stable
/// between the comparison and the read, and the operation's block must have the
/// bound assert's success edge as its SOLE entry, so a forged body cannot
/// launder the obligation through an assert its executions can bypass. Any
/// non-canonical shape returns `false`, keeping both rows — duplicates
/// over-report, never under-report. On the signed chain every one of those rules
/// is re-checked AT EACH HOP.
pub(super) fn v2_divzero_assert_exactly_bound(
    func: &VerifiableFunction,
    op: BinOp,
    div_block: BlockId,
    stmt_index: usize,
    lhs: &Operand,
    divisor: &Operand,
) -> bool {
    // `AssertMessage` has no `PartialEq`; match the wanted variant structurally.
    let msg_matches_op = |msg: &AssertMessage| match op {
        BinOp::Div => matches!(msg, AssertMessage::DivisionByZero),
        BinOp::Rem => matches!(msg, AssertMessage::RemainderByZero),
        _ => false,
    };
    // The entry block has no guarding predecessor to inherit an assert from.
    if !matches!(op, BinOp::Div | BinOp::Rem)
        || div_block.0 == 0
        || !super::terminator_presence_for(func).has_divrem_zero_assert
    {
        return false;
    }
    let Some(op_block) = func.body.blocks.get(div_block.0) else {
        return false;
    };
    // One operation: the suppressed row and the surviving row must be about
    // the same unique same-op statement over structurally identical operands.
    // Checked once upfront before any statement, predecessor, or candidate-block scan.
    let Some((found_index, found_lhs, found_rhs)) = v2_find_block_binary_operands(op_block, op)
    else {
        return false;
    };
    if found_index != stmt_index
        || !v2_operands_structurally_equal(found_lhs, lhs)
        || !v2_operands_structurally_equal(found_rhs, divisor)
    {
        return false;
    }

    // The compared values must not be rewritten before the operation reads them.
    // PERF-COMPILER-VCGEN-801: asked lazily (once), only after a candidate zero
    // assert passes its cheap terminator checks; the answer and its budget
    // discipline are `v2_binop_operands_unwritten_before`'s (`false` declines).
    let operands_stable: std::cell::OnceCell<bool> = std::cell::OnceCell::new();
    let operands_stable_now = || {
        *operands_stable.get_or_init(|| {
            v2_binop_operands_unwritten_before(func, op_block, stmt_index, lhs, divisor)
        })
    };

    if let Some(sp) = crate::fn_memo::sole_predecessors(func)
        && let Some(opt_pred1) = sp.unique_exit_predecessor(div_block)
    {
        if trust_types::verify_budget::budget_exhausted() {
            return false;
        }
        // Any candidate that binds must reach `div_block` either directly as its sole
        // exit predecessor (`pred1`, unsigned 1-hop) or as the sole exit predecessor
        // `pred0` of `pred1` (signed 2-hop through the intervening overflow assert).
        let Some(pred1) = opt_pred1 else {
            return false;
        };
        let mut candidates = [Some(pred1), None];
        if let Some(Some(pred0)) = sp.unique_exit_predecessor(pred1)
            && pred0 != pred1
        {
            if pred0.0 < pred1.0 {
                candidates = [Some(pred0), Some(pred1)];
            } else {
                candidates[1] = Some(pred0);
            }
        }
        for pred_id in candidates.into_iter().flatten() {
            if trust_types::verify_budget::budget_exhausted() {
                return false;
            }
            let Some(assert_block) = func.body.blocks.get(pred_id.0) else {
                continue;
            };
            let Terminator::Assert { cond, expected: false, msg, target, .. } =
                &assert_block.terminator
            else {
                continue;
            };
            if !msg_matches_op(msg) {
                continue;
            }
            if !operands_stable_now() {
                return false;
            }
            // PERF-COMPILER-VCGEN-805: the cond binding is one reverse scan of this
            // block; every CFG check below is a conjunct of the same pure answer, so
            // asking it first only skips the chain walk for a non-binding cond.
            if !v2_divzero_cond_binds_divisor(func, assert_block, cond, divisor) {
                continue;
            }
            if *target == div_block {
                if assert_block.id != pred1
                    || assert_block.terminator.unwind_cleanup_target() == Some(div_block)
                {
                    continue;
                }
            } else if !v2_divzero_signed_chain_binds_operation(
                func,
                op,
                assert_block,
                *target,
                div_block,
                op_block,
                stmt_index,
                lhs,
                divisor,
            ) {
                continue;
            }
            return true;
        }
        return false;
    }

    // An explicit loop, not `blocks.iter().any(..)`, so an exhausted budget can
    // leave the FUNCTION: a `return false` inside an `.any` closure only rejects
    // the current candidate and the scan keeps running. Every closure-level
    // `return false` below became a `continue` and the match arm a `return
    // true`, so the non-exhausted path is unchanged.
    for assert_block in func.body.blocks.iter() {
        // BUDGET POLL, per candidate assert block: this scan is O(blocks) and a
        // surviving candidate costs either another O(blocks) sole-entry scan or
        // the whole two-hop `v2_divzero_signed_chain_binds_operation` walk (two
        // more block scans plus the overflow lane's binder), so the nest is
        // quadratic in the block count and polled nothing. Exhaustion returns
        // `false` — "not exactly bound", the value every non-canonical shape
        // already returns — so the per-statement duplicate row is NOT
        // suppressed. Keeping a row over-reports (PROVE-to-FAIL); only a `true`
        // could delete an obligation, and exhaustion never produces one.
        if trust_types::verify_budget::budget_exhausted() {
            return false;
        }
        let Terminator::Assert { cond, expected: false, msg, target, .. } =
            &assert_block.terminator
        else {
            continue;
        };
        if !msg_matches_op(msg) {
            continue;
        }
        if !operands_stable_now() {
            return false;
        }
        // PERF-COMPILER-VCGEN-805: the cheap cond binding before the O(blocks)
        // sole-entry scan and the two-hop chain walk (pure conjuncts, same answer).
        if !v2_divzero_cond_binds_divisor(func, assert_block, cond, divisor) {
            continue;
        }
        if *target == div_block {
            // UNSIGNED shape: the zero assert's success edge lands directly on
            // the operation. Sole-entry check: no OTHER block's terminator may
            // reach the operation's block, so the surviving assert row covers
            // every execution of the operation. PARITY with the bounds member:
            // the assert's FAILURE / cleanup edge runs exactly when the checked
            // condition is violated, and the scan below excludes
            // `assert_block.id`, so that edge must be refused explicitly — a row
            // reachable through it is REFUTABLE, not vacuous.
            if assert_block.terminator.unwind_cleanup_target() == Some(div_block) {
                continue;
            }
            // BUDGET POLL, per SCANNED block: the per-candidate poll above
            // cannot interrupt ONE sole-entry scan, which walks every block and
            // allocates a fresh `exit_targets` Vec for each. The two outcomes
            // stay distinct — a bypass rejects this candidate and the search
            // continues, an exhausted budget stops deciding altogether — and
            // both are fail-closed, since the function-level `false` keeps the
            // per-statement row.
            let mut bypassed = false;
            for b in func.body.blocks.iter() {
                if trust_types::verify_budget::budget_exhausted() {
                    return false;
                }
                if b.id != assert_block.id && b.terminator.has_exit_block_target(div_block) {
                    bypassed = true;
                    break;
                }
            }
            if bypassed {
                continue;
            }
        } else if !v2_divzero_signed_chain_binds_operation(
            func,
            op,
            assert_block,
            *target,
            div_block,
            op_block,
            stmt_index,
            lhs,
            divisor,
        ) {
            continue;
        }
        return true;
    }
    false
}

/// Whether `to` is entered ONLY by `from`'s NORMAL success edge — `to` is not the
/// entry block (function entry would reach it without executing `from` at all),
/// `from`'s own unwind/cleanup edge does not re-enter it (that edge is the
/// assert's FAILURE path, so control arriving there has NOT passed the assert),
/// and no other block's terminator lists `to` as an exit.
///
/// Deliberately STRICTER than the single-hop sole-entry test the direct div/rem
/// rules inline, which excludes the bound assert's whole block — including its
/// cleanup edge. A two-hop chain has an extra block to launder an obligation
/// through, so the chain pins the panic edge explicitly at both hops rather than
/// inheriting a rule written for one.
fn v2_block_entered_only_from(
    func: &VerifiableFunction,
    from: &trust_types::BasicBlock,
    to: BlockId,
) -> bool {
    if to.0 == 0 || from.terminator.unwind_cleanup_target() == Some(to) {
        return false;
    }
    if let Some(no_other) = crate::fn_memo::sole_predecessors(func)
        .and_then(|sp| sp.no_other_exit_predecessor(to, from.id))
    {
        if trust_types::verify_budget::budget_exhausted() {
            return false;
        }
        return no_other;
    }
    // BUDGET POLL, per SCANNED block, in an explicit loop rather than
    // `!blocks.iter().any(..)` because a closure cannot return from this
    // function: the scan walks every block and allocates a fresh `exit_targets`
    // Vec for each, and it runs at BOTH hops of the signed chain for every
    // candidate assert block `v2_divzero_assert_exactly_bound` considers, so it
    // is the innermost tier of that quadratic nest. Exhaustion returns `false`,
    // the same value a second entry edge returns: the block is treated as NOT
    // solely entered from `from`, which REFUSES the chain binding. Refusing
    // keeps the per-statement duplicate row, so a dropped decision can only add
    // an obligation (PROVE-to-FAIL), never launder one away.
    for b in func.body.blocks.iter() {
        if trust_types::verify_budget::budget_exhausted() {
            return false;
        }
        if b.id != from.id && b.terminator.has_exit_block_target(to) {
            return false;
        }
    }
    true
}

/// Whether the canonical SIGNED chain really connects `zero_block`'s zero-divisor
/// assert to the `op` statement at `(div_block, stmt_index)` over `(lhs,
/// divisor)`, through the intervening overflow assert at `ovf_id`:
///
/// ```text
/// zero_block: _z = Eq(divisor, const 0);  assert(!_z, DivisionByZero) -> ovf;
/// ovf:        _a = Eq(divisor, const -1); _b = Eq(lhs, const INT_MIN);
///             _c = BitAnd(_a, _b);        assert(!_c, Overflow(op))    -> div_block;
/// div_block:  ... = BinaryOp(op, lhs, divisor)
/// ```
///
/// WHY THIS HOP HAS TO EXIST. For SIGNED division rustc emits that overflow
/// assert BETWEEN the zero check and the operation, so the zero assert's `target`
/// is the overflow block and never the operation block.
/// [`v2_divzero_assert_exactly_bound`]'s one-hop `*target == div_block` test can
/// therefore never fire on signed code, and the vacuous
/// `divisor != 0 && divisor == 0` duplicate that 18a0083876 removed for `u64`
/// went on shipping as a `proved` `divzero` row for `i64`/`i32`. MEASURED on one
/// compile of the same source: `u64 x / (n - n)` emits ONE row, `i64 x / (n - n)`
/// emits `divzero failed` PLUS `divzero proved` — and the proved one's formula is
/// character for character the `(= _4 (= _3.0 0)) ... (not _4) ... (= _3.0 0)`
/// shape 18a0083876 names. Unsigned division has no intervening assert, which is
/// exactly why the original fix worked there and only there.
///
/// NOT "any reachable block". Every fail-closed rule of the one-hop rule is
/// re-checked AT EACH HOP, plus the one the one-hop rule never needed:
///
/// 1. SIGNEDNESS. The intervening overflow assert exists only for signed `Div`/
///    `Rem`; an unsigned operation reached through an extra block is not this
///    shape and keeps both rows. (The same `int_op_type` recovery fixes the width
///    step 3's `INT_MIN` is taken at, so a width-less literal dividend is compared
///    at the divisor's declared width; when BOTH operands are width-less literals,
///    at the operation's destination width — [`literal_pair_int_type`].)
/// 2. SOLE ENTRY, TWICE. `zero_block -> ovf` and `ovf -> div_block` must each be
///    the only way into their successor ([`v2_block_entered_only_from`]). If
///    EITHER hop could be bypassed the surviving assert row would not cover every
///    execution of the operation, which is the whole soundness claim.
/// 3. THE INTERVENING BLOCK IS THAT OPERATION'S OWN OVERFLOW ASSERT, decided by
///    the overflow lane's own binder
///    ([`v2_divrem_overflow_assert_binds_statement`]) — same opcode, same unique
///    statement, same operands, canonical `BitAnd(Eq(divisor, -1), Eq(lhs,
///    INT_MIN))` cond at the operation's true width. Block adjacency is not
///    authority any more than bare target identity is. A LITERAL dividend has no
///    place to bind, so its `INT_MIN` conjunct is bound by exact VALUE identity
///    instead ([`v2_eq_def_binds_chain_dividend`]): `Eq(const L, const INT_MIN)`,
///    in either orientation, where `L` is the operation's own literal dividend.
///    A LITERAL divisor's `rhs == -1` conjunct likewise binds only as `Eq(const D,
///    const -1)` with `D` the operation's own literal divisor
///    ([`v2_eq_def_binds_divisor`]); a place divisor binds exactly as before.
/// 4. NO REWRITE IN THE NEW WINDOW. The intervening block is a rewrite window the
///    single-hop rule never had: a store to the divisor there would decouple the
///    zero assert from the value the operation actually divides by, and the
///    surviving row would then prove a property of a stale value. No statement in
///    `ovf` may write either compared value.
///
/// Anything else returns `false` and keeps both rows — duplicates over-report,
/// never under-report.
#[allow(clippy::too_many_arguments)]
fn v2_divzero_signed_chain_binds_operation(
    func: &VerifiableFunction,
    op: BinOp,
    zero_block: &trust_types::BasicBlock,
    ovf_id: BlockId,
    div_block: BlockId,
    op_block: &trust_types::BasicBlock,
    stmt_index: usize,
    lhs: &Operand,
    divisor: &Operand,
) -> bool {
    // (1) The intervening assert is a SIGNED-only lowering.
    let Some((width, signed)) = literal_pair_int_type(func, op_block, stmt_index, lhs, divisor)
    else {
        return false;
    };
    if !signed {
        return false;
    }
    // (2a) Hop one: the zero assert's success edge is the only way into `ovf`.
    if !v2_block_entered_only_from(func, zero_block, ovf_id) {
        return false;
    }
    let Some(ovf_block) = func.body.blocks.get(ovf_id.0) else {
        return false;
    };
    // (2b) Hop two: the overflow assert's success edge is the only way into the
    // operation's block. (`v2_divzero_assert_exactly_bound` has already refused
    // `div_block.0 == 0`; this re-refuses it for the second hop in its own right.)
    if !v2_block_entered_only_from(func, ovf_block, div_block) {
        return false;
    }
    // (3) …and the intervening block is THIS operation's overflow assert, on the
    // overflow lane's own terms. The projection-tolerant compared-value binder is
    // required here and only here: on the real `i64 x / (n - n)` extraction the
    // divisor this cond compares is `_3.0`, the value field of the `CheckedSub`
    // tuple. (`--emit=mir` pretty-prints that as a plain local and hides it; the
    // extracted verification input does not.)
    //
    // Trust (SELF-GUARDED-LITERAL-OPERAND-1, 2026-10-12): the DIVIDEND conjunct
    // takes `v2_eq_def_binds_chain_dividend`, which also admits a LITERAL dividend
    // by exact value identity. `100 / x` lowers its conjunct as `Eq(const 100, const
    // i32::MIN)`, a literal on BOTH sides, and the literal-refusing binder never
    // bound it, so this step failed for every signed division with a literal
    // dividend and the statement-lane `divzero`/`remzero` row — under the zero
    // assert's own `AssertHolds` guard, UNSAT by construction — shipped
    // kernel-certified at the span of a division that panics at `x == 0`.
    //
    // Trust (SELF-GUARDED-LITERAL-OPERAND-1, literal-divisor follow-up, 2026-10-13):
    // the DIVISOR conjunct takes `v2_eq_def_binds_divisor`, the same place-or-literal
    // rule the zero assert's own binding now uses. `x / 0` lowers it as `Eq(const 0,
    // const -1)`, a literal on both sides, which the literal-refusing binder never
    // bound. A PLACE divisor binds exactly as before.
    if !v2_divrem_overflow_assert_binds_statement(
        func,
        op,
        ovf_block,
        div_block,
        op_block,
        stmt_index,
        lhs,
        divisor,
        crate::range::signed_min(width),
        v2_eq_def_binds_divisor,
        v2_eq_def_binds_chain_dividend,
    ) {
        return false;
    }
    // (4) The new rewrite window: nothing in the intervening block may redefine
    // the value the zero assert compared or the value the operation divides.
    if !ovf_block.stmts.is_empty() {
        let same_operands = v2_operands_structurally_equal(lhs, divisor);
        for (idx, operand) in [lhs, divisor].into_iter().enumerate() {
            if idx == 1 && same_operands {
                break;
            }
            if let Operand::Copy(p) | Operand::Move(p) = operand {
                let name = crate::place_to_var_name(func, p);
                if (0..ovf_block.stmts.len()).any(|k| stmt_writes_name(func, ovf_block, k, &name)) {
                    return false;
                }
            }
        }
    }
    true
}

/// Whether BOTH operands are width-less signed literals (`ConstValue::Int`): the one
/// operand pair for which [`int_op_type`] has no typed operand to read. It then takes
/// the narrower of two `operand_ty` results, and `operand_ty` FABRICATES i64 for a bare
/// literal (i128 when the value does not fit i64), so the "operation width" it returns
/// is a guess, not a type. Every builder that reads a width for such a pair reads it
/// from the operation's DESTINATION instead ([`literal_pair_int_type`],
/// `v2_overflow_call_body`'s `Unchecked` arm).
pub(super) fn v2_operands_are_literal_pair(lhs: &Operand, rhs: &Operand) -> bool {
    let bare_literal = |operand: &Operand| matches!(operand, Operand::Constant(ConstValue::Int(_)));
    bare_literal(lhs) && bare_literal(rhs)
}

/// The declared type of the WHOLE-LOCAL destination of the `Assign` at `stmt_index` in
/// `op_block`, when it is a fixed-width integer (`Ty::Int`, or `Ty::PtrSizedInt` at the
/// pinned 64-bit width — [`crate::fixed_width_integer_descriptor`]). `None` for a
/// projected destination, a non-integer one, or an index that is not an `Assign`.
fn v2_literal_pair_destination_ty(
    func: &VerifiableFunction,
    op_block: &trust_types::BasicBlock,
    stmt_index: usize,
) -> Option<Ty> {
    let Statement::Assign { place, .. } = op_block.stmts.get(stmt_index)? else {
        return None;
    };
    if !place.projections.is_empty() {
        return None;
    }
    let ty = crate::local_ty_ref(func, place.local)?;
    crate::fixed_width_integer_descriptor(ty).is_some().then(|| ty.clone())
}

/// The `(width, signed)` of the integer `Div`/`Rem` at `(op_block, stmt_index)` over
/// `(lhs, rhs)`: [`int_op_type`], except when BOTH operands are width-less signed
/// literals ([`v2_operands_are_literal_pair`]), where `int_op_type` falls back to the
/// i64 `operand_ty` fabricates for a bare literal. There the statement's own
/// DESTINATION is read instead: an integer `Div`/`Rem` has one type for both operands
/// and its result, so the destination's declared integer type is the operation's
/// width exactly (the same destination authority `v2_shift_dest_width` and
/// `v2_negation_row_shape` use for a width-less literal). A destination that is not a
/// whole-local fixed-width integer returns `None`.
///
/// THE ONE WIDTH of every signed `Div`/`Rem` overflow decision, so that none of them can
/// drift from another:
///  * step 1 of the signed zero-divisor chain
///    ([`v2_divzero_signed_chain_binds_operation`]): `None` refuses the chain and keeps
///    both rows;
///  * the direct `Overflow(Div|Rem)` suppression
///    ([`v2_divrem_overflow_assert_exactly_bound`]): `None` keeps both rows;
///  * the statement-lane row itself ([`v2_build_signed_div_overflow_vc`]): for a
///    literal pair, `None` is the `LiteralPairWidthUnresolved` unknown row, never a
///    dropped obligation.
///
/// Trust (SELF-GUARDED-LITERAL-OPERAND-1, literal-divisor follow-up, 2026-10-13):
/// `100 / 0` (`i32`) lowers its dividend conjunct as `Eq(const 100, const
/// i32::MIN)`, which the literal identity compares against `INT_MIN` at this width;
/// read at i64 it never bound, and the vacuous zero-divisor row stayed.
///
/// Trust (LITERAL-PAIR-WIDTH-1, SELF-GUARDED-LITERAL-OPERAND-2, 2026-10-13): that fix
/// reached the chain only, and the overflow row and its suppression kept
/// `int_op_type`. `core::intrinsics::unchecked_div(i8::MIN, -1)` lowers to a bare
/// `_0 = Div(const -128, const -1)` into `_0: i8`, with no assert, so the statement
/// row is the function's ONLY obligation. Built at i64 it read `-128 == i64::MIN`
/// (UNSAT), and the function was VERIFIED, its row clean-kernel `Certified` under the
/// one closed false hypothesis `h_0 : -128 = -9223372036854775808`, while every call
/// executes UB. The checked `i32::MIN / -1` kept a FAILED assert row beside the same
/// certified false one. Renamed from `v2_divrem_chain_int_type` when it became the
/// shared authority; the chain's answer is unchanged on the verifier lane (which
/// spells `isize` as `Ty::Int { width: 64 }`). `Ty::PtrSizedInt`, the faithful
/// lane's spelling, now resolves at 64 instead of refusing.
pub(super) fn literal_pair_int_type(
    func: &VerifiableFunction,
    op_block: &trust_types::BasicBlock,
    stmt_index: usize,
    lhs: &Operand,
    rhs: &Operand,
) -> Option<(u32, bool)> {
    if !v2_operands_are_literal_pair(lhs, rhs) {
        return int_op_type(func, lhs, rhs);
    }
    crate::fixed_width_integer_descriptor(&v2_literal_pair_destination_ty(
        func, op_block, stmt_index,
    )?)
}

/// Whether `cond`'s live definition in `block` is exactly `cond = Eq(divisor, 0)`
/// (const on either side) over a value STRUCTURALLY equal to `divisor` and stable
/// through the assert's terminator read.
///
/// A dedicated check rather than [`v2_eq_def_binds_operand_to_const`]: that helper
/// refuses a PROJECTED compared value, and the zero-divisor shape needs one — for
/// `x / (n - n)` under overflow checks the divisor rustc compares and then divides
/// by is `_3.0`, the value field of the `CheckedSub` tuple. Stability is enforced
/// the way [`guards::value_local_is_unstable`]'s own contract prescribes for a
/// projected value: on the BASE local, which counts field stores and so covers the
/// aggregate as a whole (a single-assigned base is stable function-wide, strictly
/// stronger than a same-block scan). A LITERAL divisor binds only by exact value
/// identity ([`v2_eq_def_binds_divisor`]). Fail-closed on every other shape.
fn v2_divzero_cond_binds_divisor(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    cond: &Operand,
    divisor: &Operand,
) -> bool {
    // Trust (SELF-GUARDED-LITERAL-OPERAND-1, literal-divisor follow-up, 2026-10-13):
    // `v2_eq_def_binds_divisor`, not the literal-refusing projected rule alone, so a
    // literal zero divisor's `Eq(const 0, const 0)` binds (see that binder).
    v2_eq_def_binds_divisor(func, block, block.stmts.len(), cond, divisor, 0)
}

/// Whether `flag`'s live definition before `before` in `block` is exactly
/// `flag = Eq(value, const value)` (const on either side) over a value
/// STRUCTURALLY equal to `expected` and stable through the assert's terminator
/// read — the PROJECTION-TOLERANT sibling of
/// [`v2_eq_def_binds_operand_to_const`], and the body
/// [`v2_divzero_cond_binds_divisor`] has always had.
///
/// The projection tolerance is required by the real lowering rather than chosen:
/// for `x / (n - n)` under overflow checks the divisor rustc compares,
/// overflow-checks and then divides by is `_3.0`, the value field of the
/// `CheckedSub` tuple, and the projection-free helper refuses it. Stability is
/// enforced the way [`guards::value_local_is_unstable`]'s own contract prescribes
/// for a projected value: on the BASE local, which counts field stores and so
/// covers the aggregate as a whole (a single-assigned base is stable
/// function-wide, strictly stronger than a same-block scan). A LITERAL constant
/// compared value is refused outright — the zero-divisor callers handle nonzero
/// constants earlier via `v2_divisor_is_nonzero_constant`, and admitting one here is
/// how a const-false `assert(2 == 0)` would take a real divisor's obligation (a
/// LITERAL divisor's own check binds by exact value identity instead, in
/// [`v2_eq_def_binds_divisor`], never here). A
/// SYMBOLIC constant with a value identity (a const-generic `N`, a keyed `T::U`) is
/// admitted: `assert(N == 0)` is that divisor's own refutable check, not a
/// const-false lookalike (SELF-GUARDED-CONST-OPERAND-1).
/// Fail-closed on every other shape.
fn v2_eq_def_binds_projected_operand(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    before: usize,
    flag: &Operand,
    expected: &Operand,
    value: i128,
) -> bool {
    v2_eq_def_binds_compared_value(
        func,
        block,
        before,
        flag,
        expected,
        value,
        V2ComparedValue::StaticPlace,
    )
}

/// Whether `flag`'s live definition before `before` in `block` is exactly
/// `flag = Eq(operand, const value)` (const on either side), with `operand`
/// STRUCTURALLY equal to `expected_operand` and its value stable from the
/// comparison through the end of the block (the assert reads the flag at the
/// terminator, so a later rewrite of the compared value would decouple the
/// assert from the operation it nominally guards). Admits a CONSTANT or a
/// PROJECTION-FREE place — the shipped rule. Fail-closed on every other shape.
// MERGE NOTE (integrate-e6-perfield-20260831): orphaned when the merge took
// the other line's caller; kept for the lane that owns it. `expect` is
// self-expiring — this warns the moment a caller lands.
#[expect(dead_code, reason = "merge-orphaned; see MERGE NOTE above the item")]
fn v2_eq_def_binds_operand_to_const(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    before: usize,
    flag: &Operand,
    expected_operand: &Operand,
    value: i128,
) -> bool {
    v2_eq_def_binds_compared_value(
        func,
        block,
        before,
        flag,
        expected_operand,
        value,
        V2ComparedValue::ConstOrBarePlace,
    )
}

/// The compared-value rule the DIRECT `Overflow(Div|Rem)` caller
/// ([`v2_divrem_overflow_assert_exactly_bound`]) needs: the UNION of what the two
/// binders above admit. The union is forced by measurement on EXTRACTED MIR
/// (`-Ztrust-dump=mir`, stage2 @ 17abbefc3), not chosen — neither half may be
/// dropped:
///
///  * PROJECTED compared values are ADMITTED, which
///    [`v2_eq_def_binds_operand_to_const`] refuses. Under overflow checks the
///    value rustc compares against `INT_MIN`/`-1` and then divides is `_3.0`, the
///    value field of a `CheckedAdd`/`CheckedSub` tuple, so the canonical
///    `let a = x + 1; a / b` kept BOTH rows and the statement-lane one was
///
///    ```text
///    (eq _6 (eq _3.0 -2147483648)) (eq _7 (and _5 _6)) (not _7)
///        ... (eq _3.0 -2147483648) (eq b -1)
///    ```
///
///    — `NOT _7 AND _7`, UNSAT by construction, a `proved` row at the span of a
///    genuinely-false division. (`--emit=mir` pretty-prints an intervening copy
///    and hides this; the extracted verification input does not.) 18a0083876's own
///    message named this refusal while fixing only the zero-divisor row three
///    lines below.
///  * …but only STATICALLY ADDRESSED projections, which
///    [`v2_eq_def_binds_projected_operand`] did not restrict. See
///    [`v2_place_is_statically_addressed`].
///  * CONSTANT compared values stay ADMITTED, which
///    [`v2_eq_def_binds_projected_operand`] refuses. That refusal is right for the
///    zero-divisor caller and wrong here: `i32::MIN / y` lowers to
///    `_4 = Eq(const INT_MIN, const INT_MIN)` and is suppressed TODAY (measured:
///    one `arithmetic overflow (Div)` row, and one `Overflow(Rem)` row for the
///    twin). Refusing it would resurrect the vacuous row this family exists to
///    remove. Identity is still pinned by `v2_operands_structurally_equal`, and a
///    constant cannot be rewritten, so there is nothing to keep stable.
///
/// Fail-closed on every other shape: anything non-canonical keeps both rows.
fn v2_eq_def_binds_divrem_overflow_operand(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    before: usize,
    flag: &Operand,
    expected_operand: &Operand,
    value: i128,
) -> bool {
    v2_eq_def_binds_compared_value(
        func,
        block,
        before,
        flag,
        expected_operand,
        value,
        V2ComparedValue::ConstOrStaticPlace,
    )
}

/// The DIVIDEND-conjunct rule of the SIGNED zero-divisor chain
/// ([`v2_divzero_signed_chain_binds_operation`], step 3) — and of nothing else:
/// [`v2_eq_def_binds_projected_operand`], OR the exact LITERAL identity of
/// [`v2_eq_def_binds_literal_identity`].
///
/// Trust (SELF-GUARDED-LITERAL-OPERAND-1, 2026-10-12). The chain used to bind this
/// conjunct with [`v2_eq_def_binds_projected_operand`], which refuses a literal
/// compared value outright, so for a LITERAL dividend — `100 / x`, `i32::MIN / x`,
/// `(-15i16) / z`, which rustc lowers with the conjunct `Eq(const 100, const
/// i32::MIN)` (a literal on BOTH sides) — step 3 never bound, the statement-lane
/// zero-divisor row was not suppressed, and it shipped under the zero assert's own
/// `AssertHolds` guard: `x != 0 && x == 0`, UNSAT by construction, a `proved`,
/// clean-kernel `Certified` `divzero`/`remzero` row at the span of a division that
/// panics at `x == 0`, beside the assert lane's FAILED twin.
///
/// The SAME "union of admissions" argument the direct overflow caller's binder
/// ([`v2_eq_def_binds_divrem_overflow_operand`]) states, applied to the one
/// conjunct it concerns:
///
///  * a PLACE dividend binds exactly as before (the projected binder's whole rule);
///  * a LITERAL dividend binds only by VALUE IDENTITY with the operation's own
///    literal dividend, and only against `INT_MIN` at the operation's width. A
///    literal is one value wherever it occurs and has no rewrite window, so
///    value equality IS the occurrence identity the place rule approximates with
///    rewrite-stability scans.
///
/// What it does NOT reach, on purpose: the DIVISOR side. As first landed the
/// divisor conjunct (`rhs == -1`) and the zero assert's own binding
/// ([`v2_divzero_cond_binds_divisor`]) kept the literal-refusing binder; the
/// literal-DIVISOR follow-up (2026-10-13) gives both [`v2_eq_def_binds_divisor`],
/// which admits a literal only against the operation's own LITERAL divisor, so a
/// const-false `assert(2 == 0)` still cannot take a PLACE divisor's obligation. And
/// this decides only WHICH block is the operation's own overflow assert; the
/// surviving zero-divisor row is still the zero assert's, built over the divisor it
/// compares. Steps 2a/2b and 4 of the chain are unchanged (step 1 only reads a
/// both-literal operation's width at its destination), and step 4 has nothing to
/// scan for a literal.
///
/// The DIRECT overflow suppression does not use this rule. For `7 / y` its
/// statement-lane `Overflow(Div)` row is TRUE (`7 != INT_MIN`), not a lie, and
/// `a_mismatched_comparison_constant_keeps_both_rows` pins that it stays.
fn v2_eq_def_binds_chain_dividend(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    before: usize,
    flag: &Operand,
    expected: &Operand,
    value: i128,
) -> bool {
    v2_eq_def_binds_projected_operand(func, block, before, flag, expected, value)
        || v2_eq_def_binds_literal_identity(func, block, before, flag, expected, value)
}

/// The DIVISOR rule of the zero-divisor binding, at both places it compares the
/// divisor: the zero assert's own `Eq(divisor, 0)` ([`v2_divzero_cond_binds_divisor`],
/// one-hop and chain alike) and the signed chain's `rhs == -1` conjunct
/// ([`v2_divzero_signed_chain_binds_operation`], step 3).
/// [`v2_eq_def_binds_projected_operand`], OR the exact LITERAL identity of
/// [`v2_eq_def_binds_literal_identity`].
///
/// Trust (SELF-GUARDED-LITERAL-OPERAND-1, literal-divisor follow-up, 2026-10-13). Both
/// places used [`v2_eq_def_binds_projected_operand`] alone, which refuses a literal
/// compared value outright. A LITERAL zero divisor under `#![allow(unconditional_panic)]`
/// — `x / 0`, `a % 0u8`, `100 / 0` — lowers its zero check as `Eq(const 0, const 0)`,
/// a literal on BOTH sides, so the binding never fired, and the statement-lane
/// `divzero`/`remzero` row, under the zero assert's own `AssertHolds` guard (`!(0 == 0)
/// && 0 == 0`, UNSAT by construction), shipped `proved`, clean-kernel `Certified`, at
/// the span of a division that panics on every call, beside the assert lane's FAILED
/// twin. The dividend-side fix ([`v2_eq_def_binds_chain_dividend`]) did not reach it.
///
/// The SAME "union of admissions" argument, on the divisor:
///
///  * a PLACE divisor binds exactly as before (the projected binder's whole rule), so
///    a const-false `assert(2 == 0)` — or `assert(0 == 0)` — still cannot take a PLACE
///    divisor's obligation: [`v2_eq_def_binds_literal_identity`] requires `expected`,
///    the operation's own divisor, to be a literal;
///  * a LITERAL divisor binds only by VALUE IDENTITY: the comparison is `Eq(c1, c2)`
///    over two integer literals, one value-equal to the operation's own literal divisor
///    and the other `value` (`0` for the zero check, `-1` for the conjunct), in either
///    orientation. A literal is one value wherever it occurs and has no rewrite window,
///    so `Eq(L, 0)` with `L` the divisor's own value IS the proposition the
///    statement-lane row states (`L != 0` read negated), and the surviving assert-lane
///    row is built over that same comparison. `Eq(const 2, const 0)` beside `x / 0`
///    names a different value and is refused, keeping both rows.
///
/// A nonzero literal divisor never reaches this rule (`v2_divisor_is_nonzero_constant`
/// emits no statement-lane row for it), so in practice the literal arm decides only a
/// literal ZERO divisor, the shape that panics on every call.
fn v2_eq_def_binds_divisor(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    before: usize,
    flag: &Operand,
    expected: &Operand,
    value: i128,
) -> bool {
    v2_eq_def_binds_projected_operand(func, block, before, flag, expected, value)
        || v2_eq_def_binds_literal_identity(func, block, before, flag, expected, value)
}

/// Whether `flag`'s live definition before `before` in `block` is exactly
/// `flag = Eq(c1, c2)` over two integer LITERALS, one of which is value-equal
/// ([`v2_operands_structurally_equal`]) to `expected` — itself required to be an
/// integer literal — and the other of which is the literal `value`, in either
/// orientation.
///
/// The flag clauses are the shared rule's ([`v2_eq_def_binds_compared_value`]):
/// a projection-free, function-stable flag local whose LAST write before `before`
/// is that very assignment. There is no compared-value stability clause because a
/// literal cannot be rewritten. Fail-closed on every other shape: a place or a
/// symbolic constant on either side, a literal that differs from `expected` by
/// value (`Eq(const 99, const MIN)` for `100 / x`), a second literal that is not
/// `value`, or a flag whose live write is anything else.
fn v2_eq_def_binds_literal_identity(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    before: usize,
    flag: &Operand,
    expected: &Operand,
    value: i128,
) -> bool {
    if const_int_value(expected).is_none() {
        return false;
    }
    let (Operand::Copy(flag_place) | Operand::Move(flag_place)) = flag else {
        return false;
    };
    let end = before.min(block.stmts.len());
    if !flag_place.projections.is_empty() || end == 0 {
        return false;
    }
    // PERF-COMPILER-VCGEN-731: locate the last `flag_place = BinaryOp(Eq, l, r)` in
    // `block.stmts[..end]` and check its literal operands before consulting
    // `value_local_is_unstable`, `place_to_var_name`, or `stmt_writes_name` (which only
    // needs to scan `(k + 1..end)` rather than `(0..end)`).
    let Some((k, l, r)) = (0..end).rev().find_map(|k| match &block.stmts[k] {
        Statement::Assign { place, rvalue: Rvalue::BinaryOp(BinOp::Eq, l, r), .. }
            if place == flag_place =>
        {
            Some((k, l, r))
        }
        _ => None,
    }) else {
        return false;
    };
    let (Some(l_value), Some(r_value)) = (const_int_value(l), const_int_value(r)) else {
        return false;
    };
    if !((v2_operands_structurally_equal(l, expected) && r_value == value)
        || (v2_operands_structurally_equal(r, expected) && l_value == value))
        || guards::value_local_is_unstable(func, flag_place.local)
    {
        return false;
    }
    if k + 1 < end {
        let flag_name = crate::place_to_var_name(func, flag_place);
        if (k + 1..end).any(|j| stmt_writes_name(func, block, j, &flag_name)) {
            return false;
        }
    }
    true
}

/// Which COMPARED VALUES a [`V2EqConstBinder`] admits — the one dimension in which
/// this family's three call sites genuinely differ. Every other clause of the rule
/// is shared by [`v2_eq_def_binds_compared_value`] and so cannot drift between
/// them.
///
/// Orthogonal to all three: a SYMBOLIC constant with a value identity (a
/// const-generic parameter or a keyed opaque scalar) is admitted by every rule
/// ([`V2ComparedValue::admits_symbolic_constant`]); "constant" below means a
/// LITERAL.
#[derive(Clone, Copy)]
enum V2ComparedValue {
    /// A literal CONSTANT, or a PROJECTION-FREE place. The rule 18a0083876 shipped.
    ConstOrBarePlace,
    /// A STATICALLY ADDRESSED place, projected or not — never a literal constant.
    StaticPlace,
    /// A STATICALLY ADDRESSED place, or a literal CONSTANT.
    ConstOrStaticPlace,
}

impl V2ComparedValue {
    /// Whether a LITERAL constant may stand in for the compared value.
    fn admits_constant(self) -> bool {
        matches!(self, Self::ConstOrBarePlace | Self::ConstOrStaticPlace)
    }

    /// Whether a SYMBOLIC constant with a value identity
    /// ([`v2_const_has_symbolic_identity`]: a const-generic parameter or a keyed
    /// opaque scalar) may stand in for the compared value. Every rule admits one
    /// (SELF-GUARDED-CONST-OPERAND-1): it is a single value throughout the body
    /// with a single solver symbol, so it is at least as good an identity as the
    /// rewrite-stable place every rule already admits, and it has no rewrite
    /// window at all. The literal refusal of [`Self::StaticPlace`] does not carry
    /// over: that refusal stops a const-FALSE `assert(2 == 0)` from taking a real
    /// divisor's obligation, and a symbolic `assert(N == 0)` is not const-false —
    /// it is the divisor's own refutable check. Written as an exhaustive match so a
    /// new rule has to decide.
    fn admits_symbolic_constant(self) -> bool {
        match self {
            Self::ConstOrBarePlace | Self::StaticPlace | Self::ConstOrStaticPlace => true,
        }
    }

    fn admits_place(self, place: &trust_types::Place) -> bool {
        match self {
            Self::ConstOrBarePlace => place.projections.is_empty(),
            Self::StaticPlace | Self::ConstOrStaticPlace => v2_place_is_statically_addressed(place),
        }
    }
}

/// The single `flag = Eq(compared value, const)` binding rule this family shares;
/// `rule` is its only degree of freedom. Whether `flag`'s live definition before
/// `before` in `block` is exactly that comparison, over a value STRUCTURALLY equal
/// to `expected` and stable from the comparison through the assert's own read at
/// the terminator (a later rewrite of the compared value would decouple the assert
/// from the operation it nominally guards). Fail-closed on every other shape.
fn v2_eq_def_binds_compared_value(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    before: usize,
    flag: &Operand,
    expected: &Operand,
    value: i128,
    rule: V2ComparedValue,
) -> bool {
    let expected_admitted = match expected {
        Operand::Copy(p) | Operand::Move(p) => rule.admits_place(p),
        Operand::Constant(c) => {
            if v2_const_has_symbolic_identity(c) {
                rule.admits_symbolic_constant()
            } else {
                rule.admits_constant()
            }
        }
        _ => false,
    };
    if !expected_admitted {
        return false;
    }
    let (Operand::Copy(flag_place) | Operand::Move(flag_place)) = flag else {
        return false;
    };
    let end = before.min(block.stmts.len());
    if !flag_place.projections.is_empty() || end == 0 {
        return false;
    }
    // PERF-COMPILER-VCGEN-731: locate the last `flag_place = BinaryOp(Eq, l, r)` in
    // `block.stmts[..end]` and check its operands before consulting
    // `value_local_is_unstable`, `place_to_var_name`, or `stmt_writes_name` (which only
    // needs to scan `(k + 1..end)` for `flag_name`).
    let Some((k, l, r)) = (0..end).rev().find_map(|k| match &block.stmts[k] {
        Statement::Assign { place, rvalue: Rvalue::BinaryOp(BinOp::Eq, l, r), .. }
            if place == flag_place =>
        {
            Some((k, l, r))
        }
        _ => None,
    }) else {
        return false;
    };
    // Trust (SELF-GUARDED-CONST-OPERAND-1, 2026-10-11): the LITERAL side is the
    // one with a known integer value, not "whichever side is a constant". rustc
    // spells the check over a const generic as `Eq(const N, const 0)` — a
    // constant on BOTH sides, the symbolic one on the LEFT — and the old
    // `matches!(l, Operand::Constant(_))` took `N` for the literal, read no
    // value from it, and refused every such binding. When `l` is a literal this
    // is exactly the old choice (including literal-vs-literal); it differs only
    // where `l` is a non-literal constant, which used to refuse unconditionally.
    let (var_side, const_side) = if const_int_value(l).is_some() { (r, l) } else { (l, r) };
    if const_int_value(const_side) != Some(value)
        || !v2_operands_structurally_equal(var_side, expected)
        || guards::value_local_is_unstable(func, flag_place.local)
    {
        return false;
    }
    if k + 1 < end {
        let flag_name = crate::place_to_var_name(func, flag_place);
        if (k + 1..end).any(|j| stmt_writes_name(func, block, j, &flag_name)) {
            return false;
        }
    }
    match var_side {
        Operand::Copy(p) | Operand::Move(p) => {
            if !rule.admits_place(p) || guards::value_local_is_unstable(func, p.local) {
                return false;
            }
            if k + 1 < block.stmts.len() {
                let name = crate::place_to_var_name(func, p);
                if (k + 1..block.stmts.len()).any(|j| stmt_writes_name(func, block, j, &name)) {
                    return false;
                }
            }
        }
        // A constant cannot be rewritten, so there is nothing to keep stable;
        // whether one may stand in for the operand at all is `rule`'s call —
        // separately for a symbolic constant with a value identity and for a
        // literal (see `V2ComparedValue::admits_symbolic_constant`).
        Operand::Constant(c) => {
            let admitted = if v2_const_has_symbolic_identity(c) {
                rule.admits_symbolic_constant()
            } else {
                rule.admits_constant()
            };
            if !admitted {
                return false;
            }
        }
        // Every other spelling lacks the occurrence identity this binding
        // needs; `v2_operands_structurally_equal` has already refused them,
        // and `Operand` is `#[non_exhaustive]`, so refuse explicitly.
        _ => return false,
    }
    true
}

/// Whether every component of `place`'s projection path denotes a STATICALLY fixed
/// sub-location of its base local. For such a place — and only such a place — a
/// [`guards::value_local_is_unstable`] check on the BASE really does decide whether
/// the place can be rewritten anywhere in the function, because the base local is
/// the only runtime input to the address.
///
/// `Index(local)` and `Deref` are REFUSED. `Index` reads a SEPARATE index local
/// that no check in this family covers: `_a[_i]` compared against `INT_MIN`, `_i`
/// rewritten, then `_a[_i]` divided, is two different values under one place
/// spelling — `value_local_is_unstable` is asked about `_a`, and the name-keyed
/// rewrite scans look for writes to `_a[_i]`, so a write to `_i` is invisible to
/// both (`place_names_overlap("i", "a[_i]")` is false: no shared prefix boundary).
/// `Deref` reaches through a pointer whose pointee no direct-def scan tracks.
/// Either would let a forged body launder the obligation onto a value the assert
/// never compared. rustc emits neither here — measured, it copies a deref/element
/// read into a projection-free temporary before comparing it — so this costs no
/// real coverage, and the family's own rule is that a FORGED body must not be able
/// to launder an obligation.
///
/// A POSITIVE allowlist on purpose: `Projection` is `#[non_exhaustive]`, so a
/// future variant lands on `false` and keeps both rows. A projection-free place is
/// trivially statically addressed, so every previously-admitted shape is unchanged.
fn v2_place_is_statically_addressed(place: &trust_types::Place) -> bool {
    use trust_types::Projection;
    place.projections.iter().all(|p| {
        matches!(
            p,
            Projection::Field(_)
                | Projection::Downcast(_)
                | Projection::ConstantIndex { .. }
                | Projection::Subslice { .. }
                | Projection::OpaqueCast(_)
                | Projection::UnwrapUnsafeBinder(_)
        )
    })
}

/// The `(type, width)` at which EVERY negation lane builds — or looks for — the
/// `NegationOverflow` row of `dest = Neg(operand)`: the assert lane
/// ([`v2_build_assert_negation_vc`]), the statement lane
/// ([`v2_build_negation_raw_vc`]) and the suppression between them
/// (`safety::v2_negation_assert_exactly_bound`). One function, so the three cannot
/// disagree about which width a row is at.
///
/// Trust (SELF-GUARDED-LITERAL-OPERAND-1, 2026-10-12): a WIDTH-LESS integer literal
/// (`ConstValue::Int`) takes its machine shape from the DESTINATION, through
/// [`guards::bare_neg_machine_shape`] — a MIR `Neg`'s result type IS its operand
/// type, while `crate::operand_ty` of a `ConstValue::Int` is derived from the
/// constant's VALUE (`i64` for `i32::MIN`, `i64` for `i8::MIN`). Read that way,
/// `-i32::MIN` was checked against `i64::MIN`, which it is not, and its row could
/// only prove. The same literal-width hazard ABS-LIT-WIDTH-1 fixed for `abs`'s row
/// and NEG-WRAP-OFF-1 avoided for the bare-`Neg` value definition (which reads this
/// same destination shape). A destination whose shape is not a machine integer of
/// `1..=128` bits
/// refuses (`None`): the assert lane then reports its proof gap and the statement
/// lane emits no row it cannot place, rather than either guessing a width.
///
/// Every other operand (a place, a symbolic constant, an unsigned literal that
/// carries its own width) keeps `operand_ty`, exactly as before.
pub(super) fn v2_negation_row_shape(
    func: &VerifiableFunction,
    dest: &trust_types::Place,
    operand: &Operand,
) -> Option<(Ty, u32)> {
    if matches!(operand, Operand::Constant(ConstValue::Int(_))) {
        let (width, _) = guards::bare_neg_machine_shape(func, dest, operand)?;
        let ty = crate::place_ty(func, dest)?;
        return Some((ty, width));
    }
    let ty = crate::operand_ty(func, operand)?;
    let width = ty.int_width()?;
    Some((ty, width))
}

pub(super) fn v2_build_assert_negation_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    target: BlockId,
    cond: &Operand,
    expected: bool,
    span: &SourceSpan,
) -> Option<VerificationCondition> {
    if expected {
        return None;
    }
    let (dest, operand) = v2_find_target_neg_statement(func, target)?;
    // NB: owned — `ty` is moved into `VcKind::NegationOverflow { ty }` below (a stored
    // obligation type), so the borrowed walk does not apply here. The negated operand is
    // a scalar int, never the fat recursive ADT, so no clone is saved anyway.
    // Trust (SELF-GUARDED-LITERAL-OPERAND-1): a width-less literal operand takes its
    // type and width from the Neg's DESTINATION (`v2_negation_row_shape`).
    let (ty, width) = v2_negation_row_shape(func, dest, operand)?;
    if !ty.is_signed() {
        return None;
    }
    let (_, BinOp::Eq, lhs, rhs) = v2_find_condition_binary_operands(func, block, cond)? else {
        return None;
    };
    let same_runtime_operand = |candidate: &Operand| match (candidate, operand) {
        (Operand::Copy(a) | Operand::Move(a), Operand::Copy(b) | Operand::Move(b)) => a == b,
        // Trust (SELF-GUARDED-CONST-OPERAND-1, 2026-10-11): a SYMBOLIC constant
        // with a value identity — a const-generic `N`, a keyed `T::K` — is the
        // same value wherever it occurs, and rustc does NOT fold its negation:
        // `fn neg_c<const N: i32>() -> i32 { -N }` extracts as
        //     bb0: _1 = Eq(const N, const i32::MIN); assert(!_1, OverflowNeg) -> bb1
        //     bb1: _0 = Neg(const N)
        // The old comment here ("constant negations are folded before this MIR
        // shape") was false for const generics, and refusing them left this lane
        // with a `RecognizedSafetyAssertProofGap` while the statement lane's
        // self-guarded row — `NOT _1` beside `_1`'s own definition, UNSAT by
        // construction — shipped as the function's only `negation` row,
        // kernel-certified at the span of a negation that overflows at
        // `N == i32::MIN`. Identity is the whole `v2_operands_structurally_equal`
        // key, so `-M` guarded by `N == MIN` still declines.
        (Operand::Constant(c), Operand::Constant(_)) if v2_const_has_symbolic_identity(c) => {
            v2_operands_structurally_equal(candidate, operand)
        }
        // Trust (SELF-GUARDED-LITERAL-OPERAND-1, 2026-10-12): two integer LITERALS of
        // the same value are the same runtime operand — a literal is its value, with
        // no occurrence to tell apart and no rewrite window. The old comment here
        // ("literal negations are folded (or rejected as a const-eval error) before
        // this MIR shape") is false under `#![allow(arithmetic_overflow)]`:
        // `-i32::MIN` extracts as
        //     bb0: _1 = Eq(const i32::MIN, const i32::MIN); assert(!_1, OverflowNeg) -> bb1
        //     bb1: _0 = Neg(const i32::MIN)
        // and refusing it left this lane with a `RecognizedSafetyAssertProofGap`
        // while the statement lane's self-guarded row (`NOT _1` beside `_1`'s own
        // definition, built at i64 because `operand_ty` types the literal by its
        // value) shipped kernel-certified at the span of a negation that panics on
        // every run. Value identity only: `-5` guarded by `Eq(const 6, const MIN)`
        // still declines, and so does any place or symbolic constant against a
        // literal.
        (Operand::Constant(_), Operand::Constant(_))
            if const_int_value(candidate).is_some() && const_int_value(operand).is_some() =>
        {
            v2_operands_structurally_equal(candidate, operand)
        }
        // Every other public spelling lacks stable occurrence identity here and
        // declines.
        _ => false,
    };
    let min = crate::range::signed_min(width);
    let cond_binds_operand = (same_runtime_operand(lhs) && const_int_value(rhs) == Some(min))
        || (same_runtime_operand(rhs) && const_int_value(lhs) == Some(min));
    if !cond_binds_operand {
        // A unique Neg in the target is still insufficient identity: a forged
        // or stale assert can compare one value with MIN and then negate a
        // different value. Refuse rather than mint a proof for the wrong op.
        return None;
    }

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
                && !crate::local_defs::is_parameter(func, p.local)
                && !guards::value_local_is_unstable(func, p.local)
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
            // Trust: 2026-09-21 (the 128-bit NEGATION lane) — and the DOMINATING
            // GUARD on the operand, rendered onto that same fresh BV var. The
            // block-def walk above only ever speaks about a local DEFINED IN THIS
            // BLOCK, so a guarded PARAMETER (`if a >= i128::MIN + 1 { -a }`) mined
            // nothing at all and the fresh var stayed free — `= 2^127` was always a
            // model and valid Rust was refuted, whatever the bound was spelled as.
            // See `v2_bv_neg_dominating_guard_constraints` for the soundness
            // argument; in one line, these are facts true on every path into this
            // block, version-checked against the value the negation reads, so a real
            // overflow's witness satisfies them and is still refuted.
            terms.extend(v2_bv_neg_dominating_guard_constraints(
                func,
                block,
                operand,
                Some(block.stmts.len()),
                width,
            ));
            // Trust (slice ARM 2, BV-128 path): the body IS the raw BV neg-overflow
            // violation (`operand == INT_MIN`); any collected shift block-defs are a
            // ConjoinFactsLast wrapper (the body is pushed LAST, so
            // `And([defs.., body])` reconstructs the formula). No construction-time
            // version rename here — the formula is built directly — so body and
            // subject stay bare; the shared loop's rename/normalize mirrors apply.
            let obligation_body = bv_formula.clone();
            let (formula, ob_wrappers) = if terms.is_empty() {
                (bv_formula, Vec::new())
            } else {
                let wrappers = vec![ObligationWrapper::ConjoinFactsLast { facts: terms.clone() }];
                terms.push(bv_formula);
                (Formula::And(terms), wrappers)
            };
            return Some(VerificationCondition {
                kind: VcKind::NegationOverflow { ty },
                function: func.name.as_str().into(),
                location: span.clone(),
                formula,
                contract_metadata: None,
                obligation: Some(ObligationRecord {
                    body: obligation_body,
                    wrappers: ob_wrappers,
                    subject: Some(operand_to_formula(func, operand)),
                    width: Some(width),
                }),
            });
        }
        // Symbolic operand: fall through to the Int cond path (sound; UNKNOWN on
        // the native lane, as before).
    }

    // Trust (slice ARM 2, Int assert path): seed the obligation from what the
    // emitter builds — the raw assert-failure violation, the kept block-defs (as a
    // ConjoinFactsLast wrapper), the negated operand as SUBJECT and `ty.int_width()`
    // as WIDTH (the [10]-class authority, cross-checked against MIR at consumption).
    // The subject is renamed with the SAME construction-point rename the body gets,
    // so it stays byte-identical to the operand's occurrence inside the formula.
    let raw = v2_assert_failure_formula(func, cond, expected);
    let (formula, body, kept) =
        v2_formula_with_block_defs_at_point_recorded(func, block, block.stmts.len(), raw);
    let sv = super::stmt_versions_for(func);
    let subject = version_rename_owned_at(
        operand_to_formula(func, operand),
        &sv,
        func,
        block.id,
        block.stmts.len(),
    );
    let mut wrappers = Vec::new();
    if !kept.is_empty() {
        wrappers.push(ObligationWrapper::ConjoinFactsLast { facts: kept });
    }
    Some(VerificationCondition {
        kind: VcKind::NegationOverflow { ty },
        function: func.name.as_str().into(),
        location: span.clone(),
        formula,
        contract_metadata: None,
        obligation: Some(ObligationRecord {
            body,
            wrappers,
            subject: Some(subject),
            width: Some(width),
        }),
    })
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
    // Trust (bounds ARM): the RAW violation the emitter is already building — the atomic
    // bounds core (`Ge(i, len)` unsigned, or `Or([Lt(i,0), Ge(i,len)])` signed) from the
    // `i < len` assert condition, or the bare assert-failure condition otherwise.
    let raw = if expected
        && let Some((_, BinOp::Lt, lhs, rhs)) = v2_find_condition_binary_operands(func, block, cond)
    {
        let lhs_f = operand_to_formula(func, lhs);
        let rhs_f = operand_to_formula(func, rhs);
        if crate::operand_ty_cow(func, lhs).as_deref().is_some_and(Ty::is_signed) {
            Formula::Or(vec![
                Formula::Lt(Box::new(lhs_f.clone()), Box::new(Formula::Int(0))),
                Formula::Ge(Box::new(lhs_f), Box::new(rhs_f)),
            ])
        } else {
            Formula::Ge(Box::new(lhs_f), Box::new(rhs_f))
        }
    } else {
        v2_assert_failure_formula(func, cond, expected)
    };
    // Trust (bounds ARM): seed the authenticated-obligation record from the raw violation
    // and the block-defs it conjoins — EXACTLY as `v2_build_divrem_vc_raw` does for the
    // div/rem twin (this VC rides the SAME shared wrapping loop in `generate_v2_safety_vcs`,
    // which appends every later wrapper — path-defs, yield facts, preconditions, path
    // guards, semantic guards — and the final token-collapse). `end = block.stmts.len()`
    // makes `v2_formula_with_block_defs_at_point_recorded(..).0` byte-identical to the
    // previous `v2_formula_with_block_defs`, so `formula` is unchanged. Payload-free:
    // subject/width are `None` (the consumer reads index+len structurally from the body).
    let (formula, body, kept) =
        v2_formula_with_block_defs_at_point_recorded(func, block, block.stmts.len(), raw);
    let mut wrappers = Vec::new();
    if !kept.is_empty() {
        wrappers.push(ObligationWrapper::ConjoinFactsLast { facts: kept });
    }
    Some(VerificationCondition {
        kind,
        function: func.name.as_str().into(),
        location: span.clone(),
        formula,
        contract_metadata: None,
        obligation: Some(ObligationRecord { body, wrappers, subject: None, width: None }),
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
    const UNIT_TY: Ty = Ty::Unit;
    let Some(mut ty) = crate::local_ty_ref(func, place.local) else {
        return false;
    };

    for proj in &place.projections {
        match (proj, ty) {
            (trust_types::Projection::Deref, Ty::Ref { inner, .. }) => ty = inner.as_ref(),
            (trust_types::Projection::Deref, Ty::RawPtr { pointee, .. }) => ty = pointee.as_ref(),
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
                ty = fields.get(*index).unwrap_or(&UNIT_TY)
            }
            (trust_types::Projection::Field(index), Ty::Adt { fields, .. }) => {
                ty = fields.get(*index).map_or(&UNIT_TY, |(_, field_ty)| field_ty)
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
    let lhs_ty = crate::operand_ty_cow(func, lhs)?;
    let rhs_ty = crate::operand_ty_cow(func, rhs)?;
    if !lhs_ty.is_signed() || !rhs_ty.is_signed() {
        return None;
    }

    // Trust (LITERAL-PAIR-WIDTH-1, SELF-GUARDED-LITERAL-OPERAND-2, 2026-10-13): TWO
    // width-less literals carry no width at all, and `int_op_type` answers the i64
    // `operand_ty` fabricates. `core::intrinsics::unchecked_div(i8::MIN, -1)` lowers
    // to a bare `_0 = Div(const -128, const -1)` into `_0: i8` with NO assert, so
    // this row is the function's only obligation; at i64 it read `-128 == i64::MIN`
    // (UNSAT) and the function was verified, kernel-certified, while every call is
    // UB. Such a pair takes the statement's DESTINATION width (the one
    // `literal_pair_int_type` gives `v2_divrem_overflow_assert_exactly_bound`, the
    // suppression that may delete this row), both range facts at that width, and the
    // destination type as both recorded operand types, so `typed_kind` and the
    // trust-clean adequacy check see the real `i8`.
    // A destination that cannot be read (no statement index, a projected or
    // non-integer place) is an UNKNOWN row, never `None`: for the intrinsic, `None`
    // would delete the only obligation. Every other operand pair is unchanged.
    if v2_operands_are_literal_pair(lhs, rhs) {
        let resolved = stmt_index.and_then(|index| {
            let ty = v2_literal_pair_destination_ty(func, block, index)?;
            let (width, signed) = crate::fixed_width_integer_descriptor(&ty)?;
            signed.then_some((ty, width))
        });
        let Some((dest_ty, width)) = resolved else {
            return Some(unsupported_mir_vc(
                func,
                "LiteralPairWidthUnresolved".into(),
                format!(
                    "bb{}: {op:?} of two width-less signed literals whose destination is \
                     not a whole-local signed fixed-width integer (statement {stmt_index:?}): \
                     the operation width is unknown, so its `MIN / -1` overflow is not \
                     modeled",
                    block.id.0
                ),
                span.clone(),
            ));
        };
        return Some(v2_signed_div_overflow_vc_at(
            func,
            block,
            op,
            lhs,
            rhs,
            span,
            stmt_index,
            width,
            width,
            (dest_ty.clone(), dest_ty),
        ));
    }

    // Recover the true width from a non-constant operand — a signed constant
    // lhs (`(-128i8) / y`) loses its width, so deriving INT_MIN from it would
    // use i64::MIN and miss the i8 INT_MIN / -1 overflow (round-19).
    let (width, _) = int_op_type(func, lhs, rhs)?;
    let rhs_width = rhs_ty.int_width()?;
    Some(v2_signed_div_overflow_vc_at(
        func,
        block,
        op,
        lhs,
        rhs,
        span,
        stmt_index,
        width,
        rhs_width,
        (lhs_ty.into_owned(), rhs_ty.into_owned()),
    ))
}

/// The signed `MIN / -1` overflow row of [`v2_build_signed_div_overflow_vc`], at the
/// resolved widths: `lhs` in range at `width`, `rhs` in range at `rhs_width`, `lhs ==
/// MIN(width)`, `rhs == -1`, conjoined with the block defs before `stmt_index`.
#[allow(clippy::too_many_arguments)]
fn v2_signed_div_overflow_vc_at(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    span: &SourceSpan,
    stmt_index: Option<usize>,
    width: u32,
    rhs_width: u32,
    operand_tys: (Ty, Ty),
) -> VerificationCondition {
    let lhs_f = operand_to_formula(func, lhs);
    let rhs_f = operand_to_formula(func, rhs);
    let lhs_range = crate::range::input_range_constraint(&lhs_f, width, true);
    let rhs_range = crate::range::input_range_constraint(&rhs_f, rhs_width, true);
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

    VerificationCondition {
        kind: VcKind::ArithmeticOverflow { op, operand_tys },
        function: func.name.as_str().into(),
        location: span.clone(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
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
    crate::local_ty_ref(func, place.local)?.int_width()
}

/// Structural equality on two operands, enough to recognize the SAME shift
/// statement by its operands. `trust_types::Operand` derives no `PartialEq` (it
/// carries a `Formula` lifting variant), so this compares the variants that a
/// shift's operands take: a plain/projected local (`Place: Eq`), an integer
/// constant, or a SYMBOLIC constant that carries a value identity (see
/// [`v2_const_has_symbolic_identity`]). Literal constants compare by their carried
/// value+width; a const-generic parameter by its whole `(index, name, width,
/// signed)`; a keyed opaque scalar by its whole `(key, width, signed)`. Every
/// other constant kind (a site-placed or unplaced opaque scalar, the opaque
/// reference carriers, …) and the lifted-`Formula` operand conservatively return
/// `false`, which only widens the by-operands width search to the type fallback
/// and keeps both rows of every exact-binding suppression — never a false match
/// onto an unrelated operation.
pub(super) fn v2_operands_structurally_equal(a: &Operand, b: &Operand) -> bool {
    match (a, b) {
        // Trust #soundness (2026-08-25): COPY AND MOVE OF THE SAME PLACE ARE THE SAME
        // VALUE. `Move` is a `Copy` that additionally invalidates the source, so for
        // the question these callers ask — "is the value the assert compared the value
        // the operation then uses?" — the spelling is irrelevant. Refusing the cross
        // pairing rejected on a MIR spelling artifact, not a semantic difference.
        //
        // MEASURED, the shape that exposed it: `struct S { d: u32 }; let s = S { d: 0 };
        // x / s.d` lowers to
        //     bb0: _3 = Use(Copy(_2.0)); _4 = Eq(Copy(_3), 0); assert(!_4) -> bb1
        //     bb1: _0 = Div(Copy(_1), Move(_3))
        // The assert compares `Copy(_3)` and the division uses `Move(_3)` — the SAME
        // local. `(Copy, Move)` fell to the `_ => false` arm below, so
        // `v2_divzero_assert_exactly_bound` concluded the assert was not bound to the
        // divisor, declined to suppress, and the statement-lane row shipped as a
        // vacuous `proved` divzero at the span of a genuinely-false division by zero
        // (`arithmetic_safety:0 failed` beside `arithmetic_safety:1 proved`).
        //
        // `crates/trust-vcgen/tests/projected_shift_canary_real_mir.rs` already NAMED
        // this refusal ("the fixture as shipped reads `Copy _2` in the cond and
        // `Move _2` in the shift, and `v2_operands_structurally_equal` refuses that
        // spelling") and worked around it by matching the spellings, rather than
        // fixing it here.
        //
        // WHAT IS DELIBERATELY NOT WEAKENED: the comparison stays on the WHOLE
        // `Place` (`pa == pb`), so `p.0` and `p.1` remain distinct. That same test
        // pins the difference — weakening to `pa.local == pb.local` is MEASURED to let
        // a `p.1` guard suppress the obligation about `p.0`. Value stability across
        // the gap is enforced separately by the callers' own write scans, so admitting
        // the cross pairing does not bypass it.
        (Operand::Copy(pa) | Operand::Move(pa), Operand::Copy(pb) | Operand::Move(pb)) => pa == pb,
        (Operand::Constant(ca), Operand::Constant(cb)) => match (ca, cb) {
            (ConstValue::Int(x), ConstValue::Int(y)) => x == y,
            (ConstValue::Uint(x, wx), ConstValue::Uint(y, wy)) => x == y && wx == wy,
            (ConstValue::Bool(x), ConstValue::Bool(y)) => x == y,
            // Trust (SELF-GUARDED-CONST-OPERAND-1, 2026-10-11): THE SYMBOLIC
            // CONSTANTS THAT HAVE A VALUE IDENTITY. Before these two arms every
            // non-literal constant fell to `_ => false`, so the canonical rustc
            // chain over a const-generic operand —
            //     bb0: _2 = Eq(const N, const 0); assert(!_2, DivisionByZero) -> bb1
            //     bb1: _0 = Div(x, const N)
            // — (and its `Lt(const N, BITS)` / `Eq(const N, INT_MIN)` /
            // `Eq(const T::U, 0)` siblings) never bound, and the statement-lane row
            // sitting under the assert's own `AssertHolds` guard shipped as a
            // kernel-certified `proved` at the span of a genuinely-false check.
            //
            // A const-generic PARAMETER is one value throughout the body: every
            // occurrence lowers to the one symbol
            // `__trust_constparam_{index}_{name}`. The WHOLE identity is compared
            // — `(index, name)` is what keeps `M` and `N` apart (the "M==N
            // collision" the variant exists to prevent), and width/signedness
            // must agree too, so a mismatched spelling never binds.
            (
                ConstValue::ConstParam { index: ia, name: na, width: wa, signed: sa },
                ConstValue::ConstParam { index: ib, name: nb, width: wb, signed: sb },
            ) => ia == ib && na == nb && wa == wb && sa == sb,
            // A KEYED opaque scalar (`OpaqueOrigin::Const`, an unevaluated constant
            // such as `T::U` keyed by item + normalized generic arguments) is one
            // value per key: OPAQUE-SCALAR-ID-1 renders equal keys to one symbol and
            // different keys to different symbols, and this arm compares exactly
            // what that symbol is spelled from. A SITE-placed (`OpaqueOrigin::Site`,
            // a runtime value such as `ptr as usize`) or UNPLACED one never matches,
            // not even itself: two sites may hold two different values, and that is
            // the occurrence identity OPAQUE-SCALAR-ID-1 exists to keep apart.
            (
                ConstValue::OpaqueScalar {
                    width: wa,
                    signed: sa,
                    origin: trust_types::OpaqueOrigin::Const { key: ka },
                },
                ConstValue::OpaqueScalar {
                    width: wb,
                    signed: sb,
                    origin: trust_types::OpaqueOrigin::Const { key: kb },
                },
            ) => ka == kb && wa == wb && sa == sb,
            _ => false,
        },
        _ => false,
    }
}

/// Whether `value` is a SYMBOLIC constant with a VALUE IDENTITY: a const-generic
/// parameter ([`ConstValue::ConstParam`]) or a KEYED opaque scalar
/// ([`ConstValue::OpaqueScalar`] with [`trust_types::OpaqueOrigin::Const`]).
///
/// Such a constant has no known value, but every occurrence of it in one body
/// denotes the SAME value and is rendered to the SAME solver symbol, so — exactly
/// like a rewrite-stable place — "the value the assert compared" and "the value
/// the operation reads" can be decided by [`v2_operands_structurally_equal`]. It
/// can never be rewritten, so there is no stability window to check.
///
/// This is IDENTITY, never a truth fold: `trust_types::static_truth::const_eq_truth`
/// still answers `None` for `N == N` (`const_param_fold_tests`), and nothing here
/// lets a branch be pruned. It is consulted only by the exact-binding suppressors
/// and the assert-lane negation builder, where the surviving row is built over the
/// very symbol the suppressed row reads.
///
/// Fail-closed by construction: a positive allowlist. A site-placed or unplaced
/// opaque scalar, the opaque reference carriers, and every literal answer `false`
/// (literals keep their own, separate admission rule).
pub(super) fn v2_const_has_symbolic_identity(value: &ConstValue) -> bool {
    matches!(
        value,
        ConstValue::ConstParam { .. }
            | ConstValue::OpaqueScalar { origin: trust_types::OpaqueOrigin::Const { .. }, .. }
    )
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
///
/// Trust (SHIFT-BINDER-RESIDUE-1, 2026-10-11): "each by its own operands" fails
/// when two shifts of DIFFERENT widths share both operands (`(1i64 << n, 1i8 <<
/// n)`): both match, and the minimum (8) is not the first shift's width. That
/// sent the assert binder a width its `Lt(n, 64)` could never equal, so the first
/// assert never bound and its shift's vacuous statement row shipped `proved`. The
/// assert lane now resolves the width at the bound statement itself
/// (`v2_shift_assert_binds_statement`) and passes it as `V2ShiftSite::Bound`; this scan
/// is left to a statement-lane row whose destination is projected.
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
            let Statement::Assign {
                place,
                rvalue:
                    Rvalue::BinaryOp(stmt_op, stmt_lhs, stmt_rhs)
                    | Rvalue::CheckedBinaryOp(stmt_op, stmt_lhs, stmt_rhs),
                ..
            } = stmt
            else {
                continue;
            };
            if *stmt_op == op
                && place.projections.is_empty()
                && v2_operands_structurally_equal(stmt_lhs, lhs)
                && v2_operands_structurally_equal(stmt_rhs, rhs)
                && let Some(width) =
                    crate::local_ty_ref(func, place.local).and_then(Ty::int_width)
            {
                min_width = Some(min_width.map_or(width, |m| m.min(width)));
            }
        }
    }
    min_width
}

/// Where a shift row is built, and so where its shifted width comes from.
///
/// Trust (SHIFT-BINDER-RESIDUE-1, 2026-10-11): before this, the pair was
/// `stmt_index: Option<usize>`, and the assert lane passed `None`, which recovered
/// the width from the ASSERT block through the by-operands MINIMUM over every
/// matching shift (`v2_shift_result_width_by_operands`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum V2ShiftSite {
    /// The statement lane: the shift is `block.stmts[index]` itself, and its
    /// width is read off that statement's destination first.
    Statement(usize),
    /// The assert lane: the VC is built over the ASSERT block (to its end), at
    /// the width `v2_shift_assert_binds_statement` resolved at the BOUND
    /// statement, which is the width of the statement row it suppresses.
    Bound(u32),
}

impl V2ShiftSite {
    fn stmt_index(self) -> Option<usize> {
        match self {
            V2ShiftSite::Statement(index) => Some(index),
            V2ShiftSite::Bound(_) => None,
        }
    }
}

pub(super) fn v2_shift_resolved_width(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    site: V2ShiftSite,
) -> Option<u32> {
    let operand_ty = crate::operand_ty_cow(func, lhs)?;
    let _shift_ty = crate::operand_ty_cow(func, rhs)?;
    if let V2ShiftSite::Bound(width) = site {
        Some(width)
    } else if matches!(lhs, Operand::Constant(_)) {
        v2_shift_dest_width(func, block, site.stmt_index())
            .or_else(|| v2_shift_result_width_by_operands(func, op, lhs, rhs))
            .or_else(|| operand_ty.int_width())
    } else {
        operand_ty.int_width()
    }
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
    site: V2ShiftSite,
) -> Option<(Formula, Ty, Ty, u32)> {
    let operand_ty = crate::operand_ty_cow(func, lhs)?;
    let shift_ty = crate::operand_ty_cow(func, rhs)?;
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
    //
    // Trust (SHIFT-BINDER-RESIDUE-1, 2026-10-11): that by-operands fallback takes
    // the MINIMUM over every matching shift, which is not THIS shift's width when
    // two shifts of different widths share a widthless constant and an amount
    // (`(1i64 << n, 1i8 << n)`). The assert lane therefore no longer reaches it:
    // its binder resolves the width at the bound statement itself and hands it
    // over as `V2ShiftSite::Bound`. The fallback is left only to a statement-lane
    // call whose destination is projected.
    let shifted_width = if let V2ShiftSite::Bound(width) = site {
        Some(width)
    } else if matches!(lhs, Operand::Constant(_)) {
        v2_shift_dest_width(func, block, site.stmt_index())
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

    // `shifted_width` is the TRUE shifted-operand width from MIR (the shift-RESULT
    // type), NOT the `Formula::Int(bit_width)` threshold inside `invalid_shift` — the
    // [10]-class width authority the shift obligation records.
    Some((
        Formula::And(vec![shift_range, invalid_shift]),
        operand_ty.into_owned(),
        shift_ty.into_owned(),
        shifted_width,
    ))
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
pub(super) fn v2_build_shift_overflow_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    span: &SourceSpan,
    site: V2ShiftSite,
) -> Option<VerificationCondition> {
    let (violation, operand_ty, shift_ty, shifted_width) =
        v2_shift_violation_formula(func, block, op, lhs, rhs, site)?;
    // Trust (shift ARM, 2026-07-31): seed the authenticated-obligation record from what
    // the emitter is ALREADY building. `violation = And([shift_range, invalid_shift])`;
    // record the ATOMIC `invalid_shift` core the consumer's `is_core` accepts (unsigned
    // `Ge(n, W)`; signed `Or([Lt(n, 0), Ge(n, W)])`) and DEMOTE `shift_range` (the
    // `And([Le, Le])` amount-type bound) to a `ConjoinFactsLast` fact. subject = the shift
    // amount `n` (renamed at the same use-point the body is); width = the TRUE shifted-
    // operand width from MIR (`shifted_width`, NOT the formula threshold — the [10] fix).
    // `.0` of the recorded block-defs helper is byte-identical to the previous
    // `v2_formula_with_block_defs_at`, so `formula` is UNCHANGED. The shared safety loop
    // appends every later wrapper (path-defs / yield / semantic guards / path guards /
    // token-collapse); shift is not `ArithmeticOverflow`/bounds, so the four range
    // conjoins do NOT apply to it.
    let end = site.stmt_index().unwrap_or(block.stmts.len());
    let (formula, rec_body, kept) =
        v2_formula_with_block_defs_at_point_recorded(func, block, end, violation);
    let obligation =
        v2_shift_overflow_seed_record(func, block, rhs, rec_body, kept, end, shifted_width);
    Some(VerificationCondition {
        kind: VcKind::ShiftOverflow { op, operand_ty, shift_ty },
        function: func.name.as_str().into(),
        location: span.clone(),
        formula,
        contract_metadata: None,
        obligation,
    })
}

/// Trust (shift ARM, 2026-07-31): split a block-def-versioned shift-overflow violation
/// body `And([shift_range, invalid_shift])` into the authenticated obligation. `rec_body`
/// is the version-renamed body inside the emitted formula; `kept` the block-defs conjoined
/// around it; `end` the use-point the body was renamed at (so the subject renames to match
/// its occurrence inside the body); `shifted_width` the TRUE MIR shifted-operand width.
///
/// The RECORDED `body` is the ATOMIC `invalid_shift` core (`Ge(n, W)` unsigned, or
/// `Or([Lt(n, 0), Ge(n, W)])` signed); `shift_range` is DEMOTED to a `ConjoinFactsLast`
/// wrapper and the block-defs to a second, ordered innermost-first so
/// `reconstruct(body, wrappers)` reproduces `formula` BIT-FOR-BIT. `subject` is the shift
/// amount `n`; `width` the shifted-operand width. FAILS CLOSED (`None`) if `rec_body` is
/// not the canonical 2-conjunct `And`.
fn v2_shift_overflow_seed_record(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    rhs: &Operand,
    rec_body: Formula,
    kept: Vec<Formula>,
    end: usize,
    shifted_width: u32,
) -> Option<ObligationRecord> {
    let Formula::And(mut conjuncts) = rec_body else {
        return None;
    };
    let Some(atomic_core) = (conjuncts.len() == 2).then(|| conjuncts.pop()).flatten() else {
        return None;
    };
    let sv = super::stmt_versions_for(func);
    let subject = version_rename_owned_at(operand_to_formula(func, rhs), &sv, func, block.id, end);
    let mut wrappers = vec![ObligationWrapper::ConjoinFactsLast { facts: conjuncts }];
    if !kept.is_empty() {
        wrappers.push(ObligationWrapper::ConjoinFactsLast { facts: kept });
    }
    Some(ObligationRecord {
        body: atomic_core,
        wrappers,
        subject: Some(subject),
        width: Some(shifted_width),
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
    let from_ty = match crate::operand_ty_cow(func, operand) {
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
    let from_ty = from_ty.as_ref();

    // Fast path: integer-to-integer, bool-to-integer, and float-to-integer `as`
    // casts are defined behavior in Rust (widening, wrapping/truncating, or
    // saturating) and never carry a CastOverflow safety obligation (see the
    // detailed drop-in soundness comments below). Short-circuiting here avoids
    // evaluating the 15 pointer/ZST/trait-object/newtype type-shape predicates
    // on the most common `Rvalue::Cast` operations.
    if (from_ty.is_integer() || matches!(from_ty, Ty::Bool | Ty::Float { .. }))
        && to_ty.is_integer()
    {
        return None;
    }

    // A cast between two inhabited zero-sized types (a ZST transmute the
    // extractor admits) moves the unique inhabitant; it cannot overflow
    // or trap and carries no arithmetic obligation.
    if crate::is_zst_to_zst_cast(from_ty, to_ty) {
        return None;
    }

    // Rust permits exactly one integer-to-char `as` cast: `u8 as char`.
    // Every u8 value is a Unicode scalar (the surrogate interval starts at
    // 0xD800), so this conversion cannot trap, overflow, or create an invalid
    // char. Wider integer-to-char casts are rejected by rustc and every other
    // non-integer destination still reaches the fail-closed arm below.
    if matches!(from_ty, Ty::Int { width: 8, signed: false }) && matches!(to_ty, Ty::Char) {
        return None;
    }

    if crate::is_thin_pointer_identity_cast(from_ty, to_ty)
        || crate::is_fn_pointer_identity_cast(from_ty, to_ty)
        || crate::is_callable_reification_cast(from_ty, to_ty)
        // Trust (G1): `fn as *const ()` — infallible; the value is a fresh opaque code
        // address in the CHC lane and has no block definition (`guards`).
        || crate::is_fn_pointer_to_code_address_cast(from_ty, to_ty)
        // `&[T; N] -> &[T]` unsize is a metadata-only coercion (slice len is the
        // array's static N); it carries no arithmetic/bounds obligation, so it is
        // modeled with no VC, mirroring the primary cast-relation gate.
        || crate::is_array_to_slice_ref_cast(from_ty, to_ty)
        // `&T -> &dyn Trait` (trait-object pointer unsize) is likewise a
        // metadata-only coercion — an infallible vtable attach with no
        // arithmetic/range obligation. `convert.rs` began spelling it
        // `Rvalue::Cast` in d806992cd4 (it was `Use(OpaqueConst)` before); without
        // this arm the coercion mints a spurious `unsupported cast` here.
        || crate::cast_target_is_trait_object_pointer(to_ty)
        // Trust (2026-09-12, -O print machinery): the three DEFINED casts std's
        // `format_args!` emits when inlined at -Copt-level>=2 — a syntactic
        // identity / the `&str -> &[u8]` byte view [B], a fat->thin raw-pointer
        // metadata drop [A], and the `usize -> NonNull<T>` fmt-packing transmute
        // the extractor admits [C]. All infallible (no overflow, no panic), so no
        // cast VC; the CHC lowering models each (identity / fresh value). The
        // refused twins (thin->fat fabrication, `&[u8] -> &str` UTF-8 assertion,
        // `usize -> *const T` provenance recover) still reach the fail-closed arm
        // below — each pinned by a negative test in `tests.rs`.
        || crate::is_syntactic_identity_cast(from_ty, to_ty)
        || crate::is_str_ref_to_byte_slice_ref_cast(from_ty, to_ty)
        || crate::is_fat_to_thin_raw_ptr_cast(from_ty, to_ty)
        || crate::is_ptr_width_int_to_pointer_newtype_transmute(from_ty, to_ty)
        || crate::is_pointer_wrapper_to_raw_fat_ptr_cast(from_ty, to_ty)
    {
        return None;
    }

    // float `as` casts are infallible (no overflow/panic obligation); the value
    // is modeled as unconstrained elsewhere, so emit no cast-range VC here.
    if crate::is_float_numeric_cast(from_ty, to_ty) {
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

    // Trust (verified-sysroot §5 step 3, slice 1): the same address-exposure,
    // spelled through a thin single-pointer NEWTYPE source (`NonNull<T> ->
    // usize`, the extractor's `nonnull_to_usize` transmute leg), which
    // `is_pointer_like` (Ref/RawPtr only) does not cover. Equally infallible —
    // no overflow/panic obligation — and the value lane is handled by
    // `is_modeled_identity_cast` (identity over the collapsed allocation
    // model's address value). Guards inside the predicate keep fat/narrowing/
    // signed/recover shapes on the fail-closed path below.
    if crate::is_thin_pointer_address_expose_cast(from_ty, to_ty) {
        return None;
    }

    if !from_ty.is_integer() || !to_ty.is_integer() {
        return Some(v2_unsupported_cast_vc(
            func,
            block,
            Some(from_ty),
            to_ty,
            span,
            stmt_index,
            &crate::unsupported_cast_reason(from_ty, to_ty),
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
    if v2_is_value_preserving_widening(from_ty, to_ty) {
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

    // Trust (drop-in, decision 2026-07-06): a plain integer→integer `as`
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
    //
    // Trust (SELF-GUARDED-LITERAL-OPERAND-1, 2026-10-12): the shape every negation
    // lane shares (`v2_negation_row_shape`), read off THIS statement's destination,
    // so a width-less literal is checked at its declared width (`-i32::MIN` at 32,
    // not at the i64 `operand_ty` derives from its value). A statement at
    // `stmt_index` that is not `_ = Neg(operand)` has no destination to read: a
    // literal operand then refuses (no row at a guessed width) and every other
    // operand keeps its own type, as before.
    let ty_and_width = match block.stmts.get(stmt_index) {
        Some(Statement::Assign {
            place: dest,
            rvalue: Rvalue::UnaryOp(trust_types::UnOp::Neg, negated),
            ..
        }) if v2_operands_structurally_equal(negated, operand) => {
            v2_negation_row_shape(func, dest, operand)
        }
        _ if matches!(operand, Operand::Constant(ConstValue::Int(_))) => None,
        _ => crate::operand_ty(func, operand).and_then(|ty| {
            let width = ty.int_width()?;
            Some((ty, width))
        }),
    };
    let (ty, width) = ty_and_width?;
    if !ty.is_signed() {
        return None;
    }

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
                && !crate::local_defs::is_parameter(func, p.local)
                && !guards::value_local_is_unstable(func, p.local)
            {
                let base = crate::place_to_var_name(func, p);
                let bv_name = format!("__trust_ovf_bv_neg_{base}");
                v2_collect_bv_shl_blockdef(
                    func, block, stmt_index, p.local, &bv_name, width, &mut terms,
                );
            }
            // Trust: 2026-09-21 (the 128-bit NEGATION lane) — plus the DOMINATING
            // GUARD on the operand, on the same fresh BV var and versioned at the
            // `Neg` statement itself. A guarded PARAMETER has no block definition to
            // walk, so without this the var is free and the row refutes at `2^127`.
            terms.extend(v2_bv_neg_dominating_guard_constraints(
                func,
                block,
                operand,
                Some(stmt_index),
                width,
            ));
            // Trust (slice ARM 2, BV-128 path): the body IS the raw BV neg-overflow
            // violation (`operand == INT_MIN`); any collected shift block-defs are a
            // ConjoinFactsLast wrapper (the body is pushed LAST, so
            // `And([defs.., body])` reconstructs the formula). No construction-time
            // version rename here — the formula is built directly — so body and
            // subject stay bare; the shared loop's rename/normalize mirrors apply.
            let obligation_body = bv_formula.clone();
            let (formula, ob_wrappers) = if terms.is_empty() {
                (bv_formula, Vec::new())
            } else {
                let wrappers = vec![ObligationWrapper::ConjoinFactsLast { facts: terms.clone() }];
                terms.push(bv_formula);
                (Formula::And(terms), wrappers)
            };
            return Some(VerificationCondition {
                kind: VcKind::NegationOverflow { ty },
                function: func.name.as_str().into(),
                location: span.clone(),
                formula,
                contract_metadata: None,
                obligation: Some(ObligationRecord {
                    body: obligation_body,
                    wrappers: ob_wrappers,
                    subject: Some(operand_to_formula(func, operand)),
                    width: Some(width),
                }),
            });
        }
        // Symbolic operand: fall through to the Int path (sound; stays UNKNOWN on
        // the native lane, exactly as before).
    }

    let value = operand_to_formula(func, operand);
    let int_min = crate::range::type_min_formula(width, true);
    let raw = Formula::And(vec![
        crate::range::input_range_constraint(&value, width, true),
        Formula::Eq(Box::new(value.clone()), Box::new(int_min)),
    ]);

    // Trust (slice ARM 2, Int raw-Neg path): the body `And([range, value == INT_MIN])`
    // directly carries the negated operand, so SUBJECT is that operand and WIDTH is
    // `ty.int_width()`. Body/subject are renamed with the SAME mid-block use-point
    // (`stmt_index`) `v2_formula_with_block_defs_before_stmt` uses, keeping them
    // byte-identical to the formula. Kept block-defs form a ConjoinFactsLast wrapper.
    let (formula, body, kept) =
        v2_formula_with_block_defs_at_point_recorded(func, block, stmt_index, raw);
    let sv = super::stmt_versions_for(func);
    let subject = version_rename_owned_at(value, &sv, func, block.id, stmt_index);

    // Trust (slice ARM 2, Int raw-Neg path — ATOMIC-CORE recording, 2026-07-31).
    // `v2_formula_with_block_defs_at_point_recorded` renames the raw `And([range,
    // Eq])` STRUCTURALLY (`version_rename_at` maps node-by-node, no flatten and no
    // single-conjunct collapse), so `body` is exactly `And([range_r, Eq_r])` — the
    // renamed input-range constraint first, the renamed atomic overflow core
    // `Eq(value, INT_MIN)` second. The consumer's negation `is_core` accepts ONLY
    // the ATOMIC `Eq(var, INT_MIN)` (mirsem/vc_faithful.rs, `K::NegationOverflow`),
    // NOT the composite And. So RECORD the atom as `body` and demote the renamed
    // range constraint to a `ConjoinFactsLast` FACT.
    //
    // The `formula` the lane VERIFIES is UNCHANGED — only what is RECORDED changes —
    // so the wrappers must reconstruct it BIT-FOR-BIT (`#token` stamps included):
    //   * `kept` empty   ⇒ `formula` = And([range_r, Eq_r])
    //   * `kept` present ⇒ `formula` = And([kept.., And([range_r, Eq_r])])
    //     (`combine_relevant_block_defs_recorded` pushes the whole `body` And as ONE
    //     conjunct — it does NOT flatten it — so the range/Eq pair stays nested one
    //     level in).
    // `reconstruct_obligation` replays each `ConjoinFactsLast` as `And([facts.., cur])`,
    // so the two nesting levels are replayed by two wrappers IN ORDER: the INNER
    // conjoins the range onto the atom (→ `And([range_r, Eq_r])`), and the OUTER
    // conjoins the kept block-defs around that (→ `And([kept.., And([range_r, Eq_r])])`).
    // For empty `kept` only the inner wrapper is recorded, giving `And([range_r, Eq_r])`.
    // Either way `reconstruct_obligation(rec) == formula` exactly.
    let Formula::And(mut body_conjuncts) = body else {
        // Unreachable — `raw` is literally a 2-conjunct `And` and the rename is
        // structural. Fail closed if that ever changes: emit the VC with NO
        // recorded obligation so the consumer takes the legacy peel route rather
        // than authenticating an unfaithful record.
        return Some(VerificationCondition {
            kind: VcKind::NegationOverflow { ty },
            function: func.name.as_str().into(),
            location: span.clone(),
            formula,
            contract_metadata: None,
            obligation: None,
        });
    };
    let Some(atomic_core) = (body_conjuncts.len() == 2).then(|| body_conjuncts.pop()).flatten()
    else {
        return Some(VerificationCondition {
            kind: VcKind::NegationOverflow { ty },
            function: func.name.as_str().into(),
            location: span.clone(),
            formula,
            contract_metadata: None,
            obligation: None,
        });
    };
    let mut wrappers = vec![ObligationWrapper::ConjoinFactsLast { facts: body_conjuncts }];
    if !kept.is_empty() {
        wrappers.push(ObligationWrapper::ConjoinFactsLast { facts: kept });
    }
    Some(VerificationCondition {
        kind: VcKind::NegationOverflow { ty },
        function: func.name.as_str().into(),
        location: span.clone(),
        formula,
        contract_metadata: None,
        obligation: Some(ObligationRecord {
            body: atomic_core,
            wrappers,
            subject: Some(subject),
            width: Some(width),
        }),
    })
}

/// REAL-ARTIFACT guards for the SIGNED zero-divisor chain.
///
/// The shipped `18a0083876` fix covered UNSIGNED division only, and nobody
/// noticed because `clean/tests/trust_verify/vacuity_sentinel.rs`'s canaries are
/// `u64`. For SIGNED division rustc inserts an intervening `Overflow(Div|Rem)`
/// assert between the zero check and the operation, so the zero assert's `target`
/// is the overflow block and the one-hop `*target == div_block` test could never
/// fire. MEASURED on one compile of `tests/data/signed_div_arms.rs`: `u64
/// x / (n - n)` emits ONE `divzero` row; `i64 x / (n - n)` emits `divzero failed`
/// PLUS `divzero proved`, and the proved one is the `divisor != 0 && divisor == 0`
/// vacuity the earlier fix removed for unsigned.
///
/// Every fixture these tests load is the compiler's OWN extracted verification
/// input (`-Ztrust-dump=mir`), not a hand-built approximation, and the forged
/// arms MUTATE that real input one field at a time so each guard has a planted
/// violation whose provenance is the real lowering.
#[cfg(test)]
mod signed_divzero_chain_tests {
    use trust_types::{AssertMessage, BasicBlock, UnwindEdge, VcKind};

    use super::*;

    fn load(name: &str) -> VerifiableFunction {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");
        let text = std::fs::read_to_string(format!("{path}{name}.json"))
            .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must be readable: {e}"));
        serde_json::from_str(&text)
            .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must deserialize: {e}"))
    }

    /// The production predicate's verdict for every `Div`/`Rem` statement in the
    /// body, in body order, decided over the production operands.
    fn suppressed(func: &VerifiableFunction) -> Vec<bool> {
        let mut out = Vec::new();
        for block in &func.body.blocks {
            for (stmt_index, stmt) in block.stmts.iter().enumerate() {
                let Statement::Assign { rvalue: Rvalue::BinaryOp(op, lhs, rhs), .. } = stmt else {
                    continue;
                };
                if !matches!(op, BinOp::Div | BinOp::Rem) {
                    continue;
                }
                out.push(v2_divzero_assert_exactly_bound(
                    func, *op, block.id, stmt_index, lhs, rhs,
                ));
            }
        }
        assert!(!out.is_empty(), "fixture must contain a Div/Rem statement");
        out
    }

    fn zero_divisor_rows(func: &VerifiableFunction) -> usize {
        crate::generate_vcs(func)
            .into_iter()
            .filter(|vc| matches!(vc.kind, VcKind::DivisionByZero | VcKind::RemainderByZero))
            .count()
    }

    /// The `Assert` terminator of `bb<index>`, with a fixture-drift message if the
    /// dump ever stops having that shape there.
    fn assert_terminator(func: &mut VerifiableFunction, index: usize) -> &mut Terminator {
        let block = &mut func.body.blocks[index];
        assert_eq!(block.id.0, index, "fixture drift: blocks are no longer in id order");
        assert!(
            matches!(block.terminator, Terminator::Assert { .. }),
            "fixture drift: expected an Assert terminator on bb{index}"
        );
        &mut block.terminator
    }

    /// Appends `bbN: goto -> target`, giving `target` a second predecessor.
    fn add_goto_predecessor(func: &mut VerifiableFunction, target: usize) {
        let id = BlockId(func.body.blocks.len());
        func.body.blocks.push(BasicBlock {
            id,
            stmts: Vec::new(),
            terminator: Terminator::Goto(BlockId(target)),
        });
    }

    // -----------------------------------------------------------------------
    // The canaries that were being certified at the signed width.
    // -----------------------------------------------------------------------

    #[test]
    fn signed_div_canary_keeps_exactly_one_zero_divisor_row() {
        let func = load("sentinel_signed_div_by_zero_must_not_prove");
        assert_eq!(
            suppressed(&func),
            vec![true],
            "the signed canary's per-statement `divzero` row sits under the chain's \
             passed-assert guard — `_3.0 != 0 && _3.0 == 0`, UNSAT by construction — \
             so it must be suppressed, not shipped as a `proved` row at the span of a \
             genuinely-false division by zero"
        );
        assert_eq!(zero_divisor_rows(&func), 1, "exactly one live obligation must remain");
    }

    #[test]
    fn signed_rem_canary_keeps_exactly_one_zero_divisor_row() {
        let func = load("sentinel_signed_rem_by_zero_must_not_prove");
        assert_eq!(suppressed(&func), vec![true], "the `Rem` member of the same family");
        assert_eq!(zero_divisor_rows(&func), 1);
    }

    #[test]
    fn narrower_signed_width_binds_its_own_int_min() {
        // `i32 a / b`: the chain recovers INT_MIN at the operation's true width,
        // so a rule that hard-coded i64's INT_MIN would leave this one duplicated.
        let func = load("unguarded_signed_division");
        assert_eq!(suppressed(&func), vec![true]);
        assert_eq!(zero_divisor_rows(&func), 1);
    }

    // -----------------------------------------------------------------------
    // THE SURFACE MUST NOT SHRINK. A suppression that deletes an honest row is
    // a lost recovery, not a fix.
    // -----------------------------------------------------------------------

    #[test]
    fn provably_safe_signed_division_keeps_a_dischargeable_obligation() {
        // `x / (n | 1)` is genuinely safe. Exactly one REAL obligation must remain
        // for the discharge lanes to prove — the vacuous twin is what goes away.
        let func = load("provably_safe_signed_division");
        assert_eq!(suppressed(&func), vec![true]);
        assert_eq!(
            zero_divisor_rows(&func),
            1,
            "the safe case keeps one real obligation to discharge; deleting it would \
             be a lost recovery, not a fix"
        );
    }

    #[test]
    fn a_user_guarded_division_keeps_its_honest_row() {
        // `if d != 0 { x / d }` is the proved+proved shape where ONE ROW IS
        // HONEST. rustc cannot discharge `d != 0` at MIR-build time, so it emits
        // the full chain anyway — through NON-CONTIGUOUS blocks (bb1 -> bb4 ->
        // bb5), which is why the hops are followed by target rather than by
        // adjacency. The row that survives is the assert-lane one at bb1, which
        // sits under the `SwitchInt` guard and IS dischargeable; the vacuous twin
        // in bb5 is what goes. Deleting the honest one would be a lost recovery.
        let func = load("guarded_signed_division");
        assert_eq!(suppressed(&func), vec![true]);
        assert_eq!(
            zero_divisor_rows(&func),
            1,
            "the guarded case keeps exactly its one honest, dischargeable row"
        );
    }

    #[test]
    fn two_distinct_signed_divisors_each_keep_their_own_obligation() {
        // Two divisors, two chains. A skip keyed on the BLOCK rather than on the
        // DIVISOR drops one of two real obligations; pre-fix this emitted FOUR
        // rows, two honest and two vacuous.
        let func = load("two_distinct_signed_divisors");
        assert_eq!(suppressed(&func), vec![true, true]);
        assert_eq!(zero_divisor_rows(&func), 2, "each distinct divisor keeps one row");
    }

    #[test]
    fn the_unsigned_surface_is_untouched() {
        // The one-hop rule 18a0083876 shipped still decides unsigned code, and the
        // chain must not have moved it in either direction.
        for name in ["unsigned_control", "unguarded_unsigned_division"] {
            let func = load(name);
            assert_eq!(suppressed(&func), vec![true], "{name}");
            assert_eq!(zero_divisor_rows(&func), 1, "{name}");
        }
    }

    // -----------------------------------------------------------------------
    // FORGED ARMS. Each mutates the REAL canary in one place and must restore
    // BOTH rows: over-reporting is the safe direction. The comment on each names
    // the loosening that turns it red, and only that loosening does.
    // -----------------------------------------------------------------------

    #[test]
    fn a_second_entry_into_the_overflow_block_keeps_both_rows() {
        // Hop ONE is bypassable: control can reach the overflow block, and thus
        // the division, without ever executing the zero assert. RED under: making
        // `v2_block_entered_only_from` accept any non-entry block. (The hop-two
        // check does not catch it — the second predecessor is on the FIRST edge.)
        let mut func = load("sentinel_signed_div_by_zero_must_not_prove");
        add_goto_predecessor(&mut func, 2);
        assert_eq!(suppressed(&func), vec![false]);
    }

    #[test]
    fn a_second_entry_into_the_operation_block_keeps_both_rows() {
        // Hop TWO is bypassable. RED under the same loosening; kept as its own arm
        // because the two hops are separate calls and a fix could pin one only.
        let mut func = load("sentinel_signed_div_by_zero_must_not_prove");
        add_goto_predecessor(&mut func, 3);
        assert_eq!(suppressed(&func), vec![false]);
    }

    #[test]
    fn a_panic_edge_back_into_the_chain_keeps_both_rows() {
        // The zero assert's own UNWIND edge re-enters the overflow block: control
        // reaches the division on the path where the assert FAILED. RED under:
        // dropping the `unwind_cleanup_target() == Some(to)` clause. The
        // other-predecessor scan alone does NOT catch this, because it excludes
        // the bound assert's whole block — which is exactly why the chain uses a
        // stricter entry rule than the one-hop twins inline.
        let mut func = load("sentinel_signed_div_by_zero_must_not_prove");
        let Terminator::Assert { unwind, .. } = assert_terminator(&mut func, 1) else {
            unreachable!()
        };
        *unwind = UnwindEdge::Cleanup(BlockId(2));
        assert_eq!(suppressed(&func), vec![false]);
    }

    #[test]
    fn a_divisor_defined_inside_the_intervening_block_keeps_both_rows() {
        // Moving the `CheckedSub` that defines `_3` out of bb0 and INTO the
        // overflow block leaves `_3` with exactly ONE definition function-wide, so
        // `guards::value_local_is_unstable` still calls it stable — yet the zero
        // assert now compares a value the intervening block redefines before the
        // division reads it. RED under: deleting the intervening-block rewrite
        // scan. This is the rewrite window the single-hop rule never had, and it
        // is the one guard the function-wide stability check cannot stand in for.
        let mut func = load("sentinel_signed_div_by_zero_must_not_prove");
        let stmt = func.body.blocks[0].stmts.remove(0);
        func.body.blocks[2].stmts.insert(0, stmt);
        assert_eq!(suppressed(&func), vec![false]);
    }

    #[test]
    fn a_mismatched_intervening_opcode_keeps_both_rows() {
        // `Overflow(Rem)` sitting between a zero check and a `Div`. RED under:
        // accepting the intervening block on adjacency instead of running the
        // overflow lane's own binder over it.
        let mut func = load("sentinel_signed_div_by_zero_must_not_prove");
        let Terminator::Assert { msg, .. } = assert_terminator(&mut func, 2) else {
            unreachable!()
        };
        *msg = AssertMessage::Overflow(BinOp::Rem);
        assert_eq!(suppressed(&func), vec![false]);
    }

    #[test]
    fn an_intervening_guard_over_a_different_value_keeps_both_rows() {
        // The `== -1` conjunct is retargeted from the divisor `_3.0` to the
        // dividend `_1`, so the block is assert-shaped but is not THIS operation's
        // overflow guard. RED under the same adjacency loosening — this is the
        // operand-exactness half of it.
        let mut func = load("sentinel_signed_div_by_zero_must_not_prove");
        let Statement::Assign { rvalue: Rvalue::BinaryOp(_, lhs, _), .. } =
            &mut func.body.blocks[2].stmts[0]
        else {
            unreachable!("fixture drift: bb2[0] is the `Eq(divisor, -1)` conjunct")
        };
        *lhs = Operand::Copy(trust_types::Place::local(1));
        assert_eq!(suppressed(&func), vec![false]);
    }

    #[test]
    fn an_inverted_intervening_polarity_keeps_both_rows() {
        // rustc's `Overflow(Div|Rem)` assert panics when the condition is TRUE, so
        // its normal edge is `expected: false`; an inverted one has different
        // semantics and cannot stand in. RED under: dropping `expected: false`
        // from the binder's terminator pattern.
        let mut func = load("sentinel_signed_div_by_zero_must_not_prove");
        let Terminator::Assert { expected, .. } = assert_terminator(&mut func, 2) else {
            unreachable!()
        };
        *expected = true;
        assert_eq!(suppressed(&func), vec![false]);
    }

    #[test]
    fn an_intervening_assert_that_targets_elsewhere_keeps_both_rows() {
        // The chain must actually END at the operation. RED under: dropping the
        // binder's `*target != div_block` test.
        let mut func = load("sentinel_signed_div_by_zero_must_not_prove");
        let Terminator::Assert { target, .. } = assert_terminator(&mut func, 2) else {
            unreachable!()
        };
        *target = BlockId(0);
        assert_eq!(suppressed(&func), vec![false]);
    }

    #[test]
    fn an_unsigned_operation_behind_the_same_chain_keeps_both_rows() {
        // Every integer local of the canary is relabelled UNSIGNED, leaving the
        // whole canonical cond chain in place. rustc emits no intervening overflow
        // assert for unsigned division, so this shape is forged by construction.
        // RED under: dropping the signedness gate. Nothing else refuses it — the
        // conjunct constants still match literally.
        let mut func = load("sentinel_signed_div_by_zero_must_not_prove");
        for decl in &mut func.body.locals {
            match &mut decl.ty {
                Ty::Int { signed, .. } => *signed = false,
                Ty::Tuple(fields) => {
                    for field in fields {
                        if let Ty::Int { signed, .. } = field {
                            *signed = false;
                        }
                    }
                }
                _ => {}
            }
        }
        assert_eq!(suppressed(&func), vec![false]);
    }

    #[test]
    fn a_zero_check_over_a_different_divisor_keeps_both_rows() {
        // Bare target identity is NEVER suppression authority: the zero assert is
        // retargeted to compare the dividend, so it does not guard this division's
        // divisor at all. RED under: keying the suppression on the block rather
        // than on `v2_divzero_cond_binds_divisor`'s operand identity.
        let mut func = load("sentinel_signed_div_by_zero_must_not_prove");
        let Statement::Assign { rvalue: Rvalue::BinaryOp(_, lhs, _), .. } =
            &mut func.body.blocks[1].stmts[0]
        else {
            unreachable!("fixture drift: bb1[0] is the `Eq(divisor, 0)` comparison")
        };
        *lhs = Operand::Copy(trust_types::Place::local(1));
        assert_eq!(suppressed(&func), vec![false]);
    }

    // -----------------------------------------------------------------------
    // SELF-GUARDED-LITERAL-OPERAND-1: a LITERAL dividend. rustc spells the
    // intervening conjunct `Eq(const L, const INT_MIN)` — a literal on BOTH sides
    // — and the literal-refusing binder never bound it, so step 3 failed for every
    // signed division with a literal dividend and the statement-lane row, under the
    // zero assert's own `AssertHolds` guard, shipped kernel-certified beside the
    // assert lane's FAILED twin. Every fixture below read TWO zero-divisor rows
    // before the fix.
    // -----------------------------------------------------------------------

    /// `7 / y`, `i32::MIN / y`, `i32::MIN % y` (`divrem_projected_arms.rs`) and
    /// `7i16 / (b as i16)` (`literal_operand_arms.rs`).
    const LITERAL_DIVIDEND: [&str; 4] = [
        "nonmin_const_dividend_div",
        "const_min_dividend_div",
        "const_min_dividend_rem",
        "literal_div_cast_divisor",
    ];

    fn zero_divisor_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
        crate::generate_vcs(func)
            .into_iter()
            .filter(|vc| matches!(vc.kind, VcKind::DivisionByZero | VcKind::RemainderByZero))
            .collect()
    }

    /// No surviving zero-divisor row may assert its flag FALSE beside the flag's own
    /// defining comparison TRUE — `divisor != 0 && divisor == 0`, UNSAT for every
    /// program. The detector is the overflow module's; a zero-divisor cond is its
    /// single-comparison case, and `the_zero_divisor_vacuity_detector_can_fail`
    /// shows it firing on exactly that row.
    fn assert_no_vacuous_zero_divisor_row(name: &str, func: &VerifiableFunction) {
        for vc in zero_divisor_vcs(func) {
            let bad = super::projected_divrem_overflow_tests::vacuous_flags(&vc);
            assert!(
                bad.is_empty(),
                "{name}: a surviving zero-divisor row asserts {bad:?} false while \
                 asserting its defining comparison true — UNSAT by construction, so it \
                 can only ever be `proved`: {}",
                vc.formula.to_smtlib()
            );
        }
    }

    /// `bb<block>.stmts[stmt]`'s `Eq` operands, with a fixture-drift message.
    fn eq_operands(
        func: &mut VerifiableFunction,
        block: usize,
        stmt: usize,
    ) -> (&mut Operand, &mut Operand) {
        let Statement::Assign { rvalue: Rvalue::BinaryOp(BinOp::Eq, l, r), .. } =
            &mut func.body.blocks[block].stmts[stmt]
        else {
            unreachable!("fixture drift: bb{block}[{stmt}] is an `Eq` comparison")
        };
        (l, r)
    }

    fn lit(value: i128) -> Operand {
        Operand::Constant(ConstValue::Int(value))
    }

    #[test]
    fn a_literal_dividend_keeps_exactly_one_zero_divisor_row() {
        for name in LITERAL_DIVIDEND {
            let func = load(name);
            assert_eq!(
                suppressed(&func),
                vec![true],
                "{name}: the chain must bind through the literal dividend's own \
                 `Eq(const L, const INT_MIN)` conjunct"
            );
            assert_eq!(zero_divisor_rows(&func), 1, "{name}: exactly one live obligation");
            assert_no_vacuous_zero_divisor_row(name, &func);
        }
    }

    #[test]
    fn the_zero_divisor_vacuity_detector_can_fail() {
        // A detector nobody has watched fire proves nothing. With the conjunct's
        // literal changed (`Eq(const 6, const MIN)` beside `Div(const 7, y)`) the
        // chain refuses and both rows ship: exactly the statement-lane one must be
        // flagged. If this reports zero, every `assert_no_vacuous_zero_divisor_row`
        // above passes for free.
        let mut func = load("nonmin_const_dividend_div");
        *eq_operands(&mut func, 1, 1).0 = lit(6);
        let rows = zero_divisor_vcs(&func);
        assert_eq!(rows.len(), 2);
        let flagged = rows
            .iter()
            .filter(|vc| !super::projected_divrem_overflow_tests::vacuous_flags(vc).is_empty())
            .count();
        assert_eq!(flagged, 1, "exactly the self-guarded duplicate must be flagged");
    }

    #[test]
    fn either_orientation_of_the_literal_conjunct_binds() {
        // `Eq(const INT_MIN, const 7)`: the same comparison, operands swapped.
        let mut func = load("nonmin_const_dividend_div");
        let (l, r) = eq_operands(&mut func, 1, 1);
        std::mem::swap(l, r);
        assert_eq!(suppressed(&func), vec![true]);
        assert_eq!(zero_divisor_rows(&func), 1);
    }

    #[test]
    fn the_literal_identity_binder_admits_exactly_the_operations_own_literal() {
        // The binder itself, on `7 / y`'s real `bb1` (`_4` defined at index 1, the
        // `BitAnd` at index 2), with `INT_MIN` at the operation's i32 width. The
        // conjunct is rewritten to each case and asked about a `100 / x`-shaped
        // dividend.
        let min = crate::range::signed_min(32);
        let flag = Operand::Move(trust_types::Place::local(4));
        let binds = |left: i128, right: i128, dividend: &Operand| {
            let mut func = load("nonmin_const_dividend_div");
            let (l, r) = eq_operands(&mut func, 1, 1);
            *l = lit(left);
            *r = lit(right);
            v2_eq_def_binds_chain_dividend(&func, &func.body.blocks[1], 2, &flag, dividend, min)
        };
        assert!(binds(100, min, &lit(100)), "`Eq(const 100, const MIN)` binds `100 / x`");
        assert!(binds(min, 100, &lit(100)), "…in either orientation");
        assert!(binds(min, min, &lit(min)), "`Eq(const MIN, const MIN)` binds `MIN / x`");
        assert!(!binds(99, min, &lit(100)), "`Eq(const 99, const MIN)` is not `100 / x`'s");
        assert!(!binds(100, min + 1, &lit(100)), "the other literal must be INT_MIN");
        assert!(!binds(100, 100, &lit(100)), "`Eq(const 100, const 100)` checks nothing");
        // A PLACE dividend never binds by a literal: the projected rule decides it,
        // and `Eq(const 100, const MIN)` names no place.
        let place = Operand::Copy(trust_types::Place::local(1));
        assert!(!binds(100, min, &place));
        // …and the projected rule's own refusal of a literal is unchanged: the
        // literal identity is this binder's, not the shared rule's.
        let mut func = load("nonmin_const_dividend_div");
        *eq_operands(&mut func, 1, 1).0 = lit(100);
        assert!(!v2_eq_def_binds_projected_operand(
            &func,
            &func.body.blocks[1],
            2,
            &flag,
            &lit(100),
            min
        ));
    }

    // FORGED ARMS for the literal dividend. Each mutates real extracted MIR in one
    // place and must keep BOTH rows.

    #[test]
    fn a_different_literal_in_the_min_conjunct_keeps_both_rows() {
        // The conjunct compares a literal that is NOT the operation's dividend, so
        // the block is assert-shaped but is not this division's overflow check.
        // RED under: dropping the `v2_operands_structurally_equal(_, expected)` value
        // identity from `v2_eq_def_binds_literal_identity`.
        for (name, forged) in [
            ("nonmin_const_dividend_div", lit(6)),
            ("const_min_dividend_div", lit(crate::range::signed_min(32) + 1)),
        ] {
            let mut func = load(name);
            *eq_operands(&mut func, 1, 1).0 = forged;
            assert_eq!(suppressed(&func), vec![false], "{name}");
            assert_eq!(zero_divisor_rows(&func), 2, "{name}");
        }
    }

    #[test]
    fn a_literal_compared_with_something_other_than_int_min_keeps_both_rows() {
        // `Eq(const 7, const MIN + 1)`: the dividend is named, but not against
        // INT_MIN at the operation's width. RED under: dropping the `== value`
        // half of the literal identity.
        let mut func = load("nonmin_const_dividend_div");
        *eq_operands(&mut func, 1, 1).1 = lit(crate::range::signed_min(32) + 1);
        assert_eq!(suppressed(&func), vec![false]);
        assert_eq!(zero_divisor_rows(&func), 2);
    }

    #[test]
    fn a_second_entry_into_the_literal_chain_keeps_both_rows() {
        // Hop one (into the overflow block) and hop two (into the division's
        // block), each made bypassable. RED under: making
        // `v2_block_entered_only_from` accept any non-entry block — the literal
        // admission must not have opened a way around the sole-entry rule.
        for target in [1, 2] {
            let mut func = load("nonmin_const_dividend_div");
            add_goto_predecessor(&mut func, target);
            assert_eq!(suppressed(&func), vec![false], "second entry into bb{target}");
            assert_eq!(zero_divisor_rows(&func), 2, "second entry into bb{target}");
        }
    }

    #[test]
    fn a_divisor_rewritten_inside_the_overflow_block_keeps_both_rows() {
        // `7i16 / (b as i16)`: the divisor `_2` has ONE definition (`_2 = _1 as
        // i16`, bb0[0]), so moving it INTO the overflow block keeps
        // `guards::value_local_is_unstable` quiet — yet the zero assert now compares
        // a value the intervening block redefines before the division reads it.
        // RED under: deleting step 4's intervening-block rewrite scan. A literal
        // dividend has no rewrite window of its own; the divisor's is unchanged.
        let mut func = load("literal_div_cast_divisor");
        let unmutated = func.clone();
        assert_eq!(suppressed(&unmutated), vec![true], "the unmutated fixture binds");
        let stmt = func.body.blocks[0].stmts.remove(0);
        func.body.blocks[1].stmts.insert(0, stmt);
        assert_eq!(suppressed(&func), vec![false]);
        assert_eq!(zero_divisor_rows(&func), 2);
    }

    #[test]
    fn the_direct_overflow_suppression_is_unchanged_for_a_literal_dividend() {
        // The literal identity serves the CHAIN only. The direct `Overflow(Div)`
        // suppression still refuses `7 / y` (its statement-lane overflow row is
        // TRUE, `7 != INT_MIN`, so it is not a lie) and still binds `i32::MIN / y`.
        // `projected_divrem_overflow_tests` pins the row counts.
        let decide = |name: &str| {
            let func = load(name);
            let block = &func.body.blocks[2];
            let Statement::Assign { rvalue: Rvalue::BinaryOp(op, lhs, rhs), .. } = &block.stmts[0]
            else {
                unreachable!("fixture drift: bb2[0] is the division")
            };
            v2_divrem_overflow_assert_exactly_bound(&func, *op, block.id, 0, lhs, rhs)
        };
        assert!(!decide("nonmin_const_dividend_div"));
        assert!(decide("const_min_dividend_div"));
        assert!(decide("const_min_dividend_rem"));
    }

    // -----------------------------------------------------------------------
    // SELF-GUARDED-LITERAL-OPERAND-1, literal-DIVISOR follow-up (2026-10-13). A
    // LITERAL zero divisor under `#![allow(unconditional_panic)]` spells its zero
    // check `Eq(const 0, const 0)` and, signed, its intervening conjunct `Eq(const 0,
    // const -1)`, a literal on both sides each time. The zero assert's binding and the
    // chain's divisor conjunct both refused a literal, so the statement-lane row,
    // under the zero assert's own guard, shipped kernel-certified beside the FAILED
    // twin at the span of a division that panics on every call. Every fixture below
    // read TWO zero-divisor rows before the fix.
    // -----------------------------------------------------------------------

    /// `literal_divisor_arms.rs`: `x / 0`, `x % 0` (`i32`, the chain), `a % 0u8`,
    /// `a / 0u32`, `(false as u8) % 0u8` (one hop) and `100 / 0` (`i32`, the chain over
    /// two width-less literals).
    const LITERAL_DIVISOR: [&str; 6] = [
        "literal_divisor_div_x0",
        "literal_divisor_rem_x0",
        "literal_divisor_rem_u8_0",
        "literal_divisor_div_u32_0",
        "literal_divisor_rem_cast_0",
        "literal_divisor_div_lit_lit0",
    ];

    #[test]
    fn a_literal_zero_divisor_keeps_exactly_one_zero_divisor_row() {
        for name in LITERAL_DIVISOR {
            let func = load(name);
            assert_eq!(
                suppressed(&func),
                vec![true],
                "{name}: the zero check `Eq(const 0, const 0)` names the operation's own \
                 literal divisor and must bind"
            );
            assert_eq!(zero_divisor_rows(&func), 1, "{name}: exactly one live obligation");
            assert_no_vacuous_zero_divisor_row(name, &func);
        }
    }

    #[test]
    fn a_nonzero_literal_divisor_has_no_zero_divisor_row() {
        // `x / 5`, the control: `v2_divisor_is_nonzero_constant` skips the
        // statement-lane row before any binding is asked, and the assert lane emits
        // none for `Eq(const 5, const 0)`, whose failure is known false
        // (`v2_assert_failure_is_known_false`). The literal identity moves nothing here.
        let func = load("literal_divisor_div_x5");
        assert_eq!(zero_divisor_rows(&func), 0);
    }

    #[test]
    fn the_divisor_binder_admits_exactly_the_operations_own_literal() {
        // The binder itself, on `x / 0`'s real zero check (`bb0[0]`, `_2`), asked about
        // the zero check (`value` 0) of a literal or a place divisor.
        let flag = Operand::Move(trust_types::Place::local(2));
        let binds = |left: i128, right: i128, divisor: &Operand| {
            let mut func = load("literal_divisor_div_x0");
            let (l, r) = eq_operands(&mut func, 0, 0);
            *l = lit(left);
            *r = lit(right);
            v2_eq_def_binds_divisor(&func, &func.body.blocks[0], 1, &flag, divisor, 0)
        };
        assert!(binds(0, 0, &lit(0)), "`Eq(const 0, const 0)` binds `x / 0`");
        assert!(!binds(2, 0, &lit(0)), "`Eq(const 2, const 0)` is not `x / 0`'s check");
        assert!(!binds(0, 2, &lit(0)), "…in either orientation");
        assert!(!binds(1, 1, &lit(1)), "the other literal must be the compared 0");
        // A PLACE divisor never binds by a literal: `assert(2 == 0)` and `assert(0 ==
        // 0)` are not `y`'s check.
        let place = Operand::Copy(trust_types::Place::local(1));
        assert!(!binds(2, 0, &place));
        assert!(!binds(0, 0, &place));
    }

    // FORGED ARMS for the literal divisor. Each mutates real extracted MIR in one
    // place and must keep BOTH rows.

    #[test]
    fn a_zero_check_over_a_different_literal_keeps_the_statement_row() {
        // `Eq(const 2, const 0)` beside a division by literal 0: const-FALSE, so the
        // assert passes on every run, and the assert lane emits NO row for it (its
        // failure is known false, `v2_assert_failure_is_known_false`). The
        // statement-lane row — `0 == 0` under a guard that holds — is then the ONLY,
        // and a refutable, obligation; suppressing it would report a division that
        // panics on every call as having nothing to prove. RED under: dropping the
        // value identity from `v2_eq_def_binds_literal_identity`. One hop and chain
        // alike. (`tests/self_guarded_literal_operand_real_mir.rs` shows the
        // surviving row REFUTED.)
        for (name, forged) in [
            ("literal_divisor_div_x0", lit(2)),
            ("literal_divisor_rem_u8_0", Operand::Constant(ConstValue::Uint(2, 8))),
        ] {
            let mut func = load(name);
            *eq_operands(&mut func, 0, 0).0 = forged;
            assert_eq!(suppressed(&func), vec![false], "{name}");
            assert_eq!(zero_divisor_rows(&func), 1, "{name}: the statement-lane row stays");
            assert_no_vacuous_zero_divisor_row(name, &func);
        }
    }

    #[test]
    fn a_const_false_zero_check_still_cannot_take_a_place_divisors_obligation() {
        // The original refusal, re-pinned after the literal admission: a literal
        // `assert(2 == 0)` (and `assert(0 == 0)`) targeting a block that divides by a
        // PLACE must not bind. The literal identity requires the operation's own
        // divisor to be a literal. The const-false `Eq(2, 0)` assert emits no row of
        // its own (its failure is known false), so the statement-lane row is the one
        // that must stay; `Eq(0, 0)` keeps both.
        for (name, index) in
            [("unsigned_control", 1), ("sentinel_signed_div_by_zero_must_not_prove", 1)]
        {
            for (left, right, rows) in [(2, 0, 1), (0, 0, 2)] {
                let mut func = load(name);
                let (l, r) = eq_operands(&mut func, index, 0);
                let width = match r {
                    Operand::Constant(ConstValue::Uint(_, w)) => Some(*w),
                    _ => None,
                };
                let spell = |v: i128| match width {
                    Some(w) => Operand::Constant(ConstValue::Uint(u128::try_from(v).unwrap(), w)),
                    None => lit(v),
                };
                *l = spell(left);
                *r = spell(right);
                assert_eq!(suppressed(&func), vec![false], "{name}: Eq({left}, {right})");
                assert_eq!(zero_divisor_rows(&func), rows, "{name}: Eq({left}, {right})");
            }
        }
    }

    #[test]
    fn a_different_literal_in_the_divisor_conjunct_keeps_both_rows() {
        // `x / 0` with its intervening conjunct rewritten to `Eq(const 1, const -1)`
        // (a literal that is not the divisor) or `Eq(const 0, const -2)` (not against
        // -1): the block is assert-shaped but is not this division's overflow check.
        // RED under: dropping either half of the literal identity for the divisor
        // conjunct.
        for (left, right) in [(1, -1), (0, -2)] {
            let mut func = load("literal_divisor_div_x0");
            let (l, r) = eq_operands(&mut func, 1, 0);
            *l = lit(left);
            *r = lit(right);
            assert_eq!(suppressed(&func), vec![false], "Eq({left}, {right})");
            assert_eq!(zero_divisor_rows(&func), 2, "Eq({left}, {right})");
        }
    }

    #[test]
    fn a_second_entry_into_a_literal_divisor_chain_keeps_both_rows() {
        // Chain hop one and hop two (`x / 0`), and the one hop (`a % 0u8`), each made
        // bypassable. RED under: making the sole-entry rules accept any non-entry
        // block — the literal admission must not open a way around them.
        for (name, target) in [
            ("literal_divisor_div_x0", 1),
            ("literal_divisor_div_x0", 2),
            ("literal_divisor_rem_u8_0", 1),
        ] {
            let mut func = load(name);
            add_goto_predecessor(&mut func, target);
            assert_eq!(suppressed(&func), vec![false], "{name}: second entry into bb{target}");
            assert_eq!(zero_divisor_rows(&func), 2, "{name}: second entry into bb{target}");
        }
    }

    #[test]
    fn a_two_literal_division_reads_int_min_at_its_destination_width() {
        // `100 / 0` (`i32`): both operands are width-less literals, so `int_op_type`
        // falls back to the i64 `operand_ty` gives a bare literal, and the conjunct
        // `Eq(const 100, const i32::MIN)` (`bb1[1]`) never bound at that width. The
        // chain reads the destination `_0: i32` instead. Both directions pinned: the
        // real conjunct binds, and one rewritten to `i64::MIN` — the conjunct an i64
        // reading would have bound — does not. RED under: reading the width anywhere
        // but the destination.
        let unmutated = load("literal_divisor_div_lit_lit0");
        assert_eq!(suppressed(&unmutated), vec![true], "the real i32 conjunct binds");
        let mut func = unmutated.clone();
        *eq_operands(&mut func, 1, 1).1 = lit(crate::range::signed_min(64));
        assert_eq!(suppressed(&func), vec![false]);
        assert_eq!(zero_divisor_rows(&func), 2);
    }
}

// REAL-ARTIFACT guards for the PROJECTED-OPERAND `Overflow(Div|Rem)` row.
#[cfg(test)]
mod projected_divrem_overflow_tests;

/// SELF-GUARDED-CONST-OPERAND-1: the IDENTITY rule for symbolic constants, pinned
/// at the predicate, at the shared `Eq` binder, and at the assert-lane negation
/// builder. The real-MIR arms (every operator, and the forged cond mutations) live
/// in `tests/self_guarded_const_operand_real_mir.rs`; these pin the fail-closed
/// edges of the rule itself, where a loosening would let a guard over one value
/// suppress the obligation about another.
#[cfg(test)]
mod symbolic_constant_identity_tests {
    use trust_types::{OpaqueOrigin, Place};

    use super::*;

    fn param(index: u32, name: &str, width: u32, signed: bool) -> Operand {
        Operand::Constant(ConstValue::ConstParam { index, name: name.to_string(), width, signed })
    }

    fn opaque(width: u32, signed: bool, origin: OpaqueOrigin) -> Operand {
        Operand::Constant(ConstValue::OpaqueScalar { width, signed, origin })
    }

    fn keyed(key: &str) -> OpaqueOrigin {
        OpaqueOrigin::Const { key: key.to_string() }
    }

    fn load(name: &str) -> VerifiableFunction {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");
        let text = std::fs::read_to_string(format!("{path}{name}.json"))
            .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must be readable: {e}"));
        serde_json::from_str(&text)
            .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must deserialize: {e}"))
    }

    const RULES: [V2ComparedValue; 3] = [
        V2ComparedValue::ConstOrBarePlace,
        V2ComparedValue::StaticPlace,
        V2ComparedValue::ConstOrStaticPlace,
    ];

    // -----------------------------------------------------------------------
    // The predicate.
    // -----------------------------------------------------------------------

    #[test]
    fn a_const_param_is_identical_only_under_its_whole_key() {
        let n = param(0, "N", 32, true);
        assert!(v2_operands_structurally_equal(&n, &param(0, "N", 32, true)));
        // A different param is a different value: the "M==N collision".
        assert!(!v2_operands_structurally_equal(&n, &param(1, "N", 32, true)), "index");
        assert!(!v2_operands_structurally_equal(&n, &param(0, "M", 32, true)), "name");
        assert!(!v2_operands_structurally_equal(&n, &param(1, "M", 32, true)), "index+name");
        assert!(!v2_operands_structurally_equal(&n, &param(0, "N", 64, true)), "width");
        assert!(!v2_operands_structurally_equal(&n, &param(0, "N", 32, false)), "signedness");
    }

    #[test]
    fn a_keyed_opaque_scalar_is_identical_only_under_its_whole_key() {
        let k = opaque(32, false, keyed("crate::Tr::U@1"));
        assert!(v2_operands_structurally_equal(&k, &opaque(32, false, keyed("crate::Tr::U@1"))));
        // A different key is a different constant, never conflated.
        assert!(!v2_operands_structurally_equal(&k, &opaque(32, false, keyed("crate::Tr::U@2"))));
        assert!(!v2_operands_structurally_equal(&k, &opaque(32, false, keyed("crate::Tr::V@1"))));
        assert!(!v2_operands_structurally_equal(&k, &opaque(64, false, keyed("crate::Tr::U@1"))));
        assert!(!v2_operands_structurally_equal(&k, &opaque(32, true, keyed("crate::Tr::U@1"))));
    }

    #[test]
    fn a_positional_opaque_scalar_is_never_identical_not_even_to_itself() {
        // A SITE-placed opaque scalar is a runtime value (`ptr as usize`, a
        // transmute): two sites may hold two values, and the same spelling at the
        // same site is still not an identity this rule may lean on. Unplaced
        // carriers alias every other unplaced one, so they are refused too.
        let site = OpaqueOrigin::Site { block: 0, stmt: 0, slot: 1 };
        let s = opaque(32, false, site.clone());
        assert!(!v2_operands_structurally_equal(&s, &opaque(32, false, site)));
        let u = opaque(32, false, OpaqueOrigin::Unplaced);
        assert!(!v2_operands_structurally_equal(&u, &opaque(32, false, OpaqueOrigin::Unplaced)));
        assert!(!v2_operands_structurally_equal(&s, &opaque(32, false, keyed("k"))));
        assert!(!v2_operands_structurally_equal(&opaque(32, false, keyed("k")), &s));
    }

    #[test]
    fn different_constant_kinds_are_never_identical() {
        let n = param(0, "N", 32, false);
        let k = opaque(32, false, keyed("N"));
        assert!(!v2_operands_structurally_equal(&n, &k));
        assert!(!v2_operands_structurally_equal(&k, &n));
        assert!(!v2_operands_structurally_equal(&n, &Operand::Constant(ConstValue::Uint(0, 32))));
        assert!(!v2_operands_structurally_equal(&Operand::Constant(ConstValue::Int(0)), &k));
        assert!(!v2_operands_structurally_equal(&n, &Operand::Copy(Place::local(1))));
    }

    #[test]
    fn symbolic_identity_is_a_positive_allowlist() {
        let has = |op: Operand| match op {
            Operand::Constant(c) => v2_const_has_symbolic_identity(&c),
            _ => unreachable!(),
        };
        assert!(has(param(0, "N", 32, true)));
        assert!(has(opaque(32, false, keyed("k"))));
        assert!(!has(opaque(32, false, OpaqueOrigin::Site { block: 0, stmt: 0, slot: 0 })));
        assert!(!has(opaque(32, false, OpaqueOrigin::Unplaced)));
        assert!(!has(Operand::Constant(ConstValue::Int(0))));
        assert!(!has(Operand::Constant(ConstValue::Uint(0, 32))));
        assert!(!has(Operand::Constant(ConstValue::Bool(false))));
        assert!(!has(Operand::Constant(ConstValue::opaque_const())));
    }

    // -----------------------------------------------------------------------
    // The shared `Eq` binder, on real extracted input
    // (`x / N`: `bb0: _2 = Eq(const N, const 0u32); assert(!_2) -> bb1`).
    // -----------------------------------------------------------------------

    /// `bb0`'s `Eq` operands, for mutation.
    fn eq_sides(func: &mut VerifiableFunction) -> (&mut Operand, &mut Operand) {
        let Statement::Assign { rvalue: Rvalue::BinaryOp(BinOp::Eq, l, r), .. } =
            &mut func.body.blocks[0].stmts[0]
        else {
            unreachable!("fixture drift: bb0[0] is the `Eq(N, 0)` zero check")
        };
        (l, r)
    }

    fn binds(func: &VerifiableFunction, expected: &Operand, rule: V2ComparedValue) -> bool {
        let block = &func.body.blocks[0];
        let Terminator::Assert { cond, .. } = &block.terminator else {
            unreachable!("fixture drift: bb0 ends in the zero-divisor assert")
        };
        v2_eq_def_binds_compared_value(func, block, block.stmts.len(), cond, expected, 0, rule)
    }

    #[test]
    fn a_const_param_compared_on_the_left_binds_under_every_rule() {
        // THE DEFECT at the binder: `Eq(const N, const 0)` — constants on BOTH
        // sides, the symbolic one LEFT — took `N` for the literal and refused.
        let func = load("const_operand_div_c");
        let n = param(0, "N", 32, false);
        for rule in RULES {
            assert!(binds(&func, &n, rule), "`N == 0` must bind `N` under every rule");
            // …and only `N`.
            assert!(!binds(&func, &param(1, "M", 32, false), rule), "`N == 0` must not bind `M`");
        }
    }

    #[test]
    fn the_symbolic_side_may_be_on_either_side() {
        let mut func = load("const_operand_div_c");
        let (l, r) = eq_sides(&mut func);
        std::mem::swap(l, r);
        for rule in RULES {
            assert!(binds(&func, &param(0, "N", 32, false), rule), "`0 == N` must bind `N`");
        }
    }

    #[test]
    fn a_comparison_with_no_literal_side_never_binds() {
        // `Eq(const N, const N)` has no value to compare against `0`.
        let mut func = load("const_operand_div_c");
        let (l, r) = eq_sides(&mut func);
        *r = l.clone();
        for rule in RULES {
            assert!(!binds(&func, &param(0, "N", 32, false), rule));
        }
    }

    #[test]
    fn the_literal_admission_rule_is_unchanged() {
        // A LITERAL compared value still answers to `rule.admits_constant()`:
        // `Eq(0u32, 0u32)` binds the literal `0u32` only under the rules that
        // admit constants. The symbolic admission must not have widened this.
        let mut func = load("const_operand_div_c");
        let zero = Operand::Constant(ConstValue::Uint(0, 32));
        *eq_sides(&mut func).0 = zero.clone();
        assert!(binds(&func, &zero, V2ComparedValue::ConstOrBarePlace));
        assert!(binds(&func, &zero, V2ComparedValue::ConstOrStaticPlace));
        assert!(!binds(&func, &zero, V2ComparedValue::StaticPlace));
    }

    #[test]
    fn a_site_placed_opaque_divisor_never_binds() {
        let mut func = load("const_operand_div_c");
        let site = opaque(32, false, OpaqueOrigin::Site { block: 0, stmt: 0, slot: 1 });
        *eq_sides(&mut func).0 = site.clone();
        for rule in RULES {
            assert!(!binds(&func, &site, rule));
        }
    }

    // -----------------------------------------------------------------------
    // The assert-lane negation builder's operand identity.
    // -----------------------------------------------------------------------

    fn assert_lane_negation(func: &VerifiableFunction) -> Option<VerificationCondition> {
        let block = &func.body.blocks[0];
        let Terminator::Assert { cond, expected, target, span, .. } = &block.terminator else {
            unreachable!("fixture drift: bb0 ends in the OverflowNeg assert")
        };
        v2_build_assert_negation_vc(func, block, *target, cond, *expected, span)
    }

    #[test]
    fn the_negation_builder_binds_a_const_param_operand() {
        // `-N`: before, `same_runtime_operand` refused every constant and this lane
        // emitted a `RecognizedSafetyAssertProofGap` instead of the real row.
        let func = load("const_operand_neg_c");
        let vc = assert_lane_negation(&func).expect("the assert lane must build the `-N` row");
        assert!(matches!(vc.kind, VcKind::NegationOverflow { .. }));
    }

    #[test]
    fn the_negation_builder_refuses_a_guard_over_a_different_const_param() {
        let mut func = load("const_operand_neg_c");
        *eq_sides(&mut func).0 = param(1, "M", 32, true);
        assert!(
            assert_lane_negation(&func).is_none(),
            "`M == MIN` is not the overflow check of `-N`"
        );
    }
}

/// SELF-GUARDED-LITERAL-OPERAND-1: the LITERAL member of the negation family, on
/// real extracted input (`tests/data/literal_<fn>.json`, source
/// `literal_operand_arms.rs`). Under `#![allow(arithmetic_overflow)]` rustc keeps
/// the checked `Neg` of a literal:
///
/// ```text
/// bb0: _1 = Eq(const i32::MIN, const i32::MIN); assert(!_1, OverflowNeg) -> bb1
/// bb1: _0 = Neg(const i32::MIN)
/// ```
///
/// Before: the assert-lane builder refused a literal (`RecognizedSafetyAssertProofGap`),
/// so the statement-lane row was the function's only `negation` row — built at
/// the i64 `operand_ty` derives from the literal's value, under the assert's own
/// `AssertHolds` guard, and kernel-certified at the span of a negation that panics
/// on every run. These pin the identity, the width, the suppression and the
/// refusals.
#[cfg(test)]
mod literal_negation_tests {
    use trust_types::{BasicBlock, UnOp, VcKind};

    use super::*;

    fn load(name: &str) -> VerifiableFunction {
        // STRAIGHT FROM TEXT: `literal_neg_min128` carries `Int: i128::MIN`, which a
        // `serde_json::Value` round-trip would widen to `f64`.
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");
        let text = std::fs::read_to_string(format!("{path}{name}.json"))
            .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must be readable: {e}"));
        serde_json::from_str(&text)
            .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must deserialize: {e}"))
    }

    /// `(fixture, the Neg destination's declared width)`.
    const LITERAL_NEGATIONS: [(&str, u32); 4] = [
        ("literal_neg_min", 32),
        ("literal_neg_min8", 8),
        ("literal_neg_max", 32),
        ("literal_neg_min128", 128),
    ];

    fn assert_lane_negation(func: &VerifiableFunction) -> Option<VerificationCondition> {
        let block = &func.body.blocks[0];
        let Terminator::Assert { cond, expected, target, span, .. } = &block.terminator else {
            unreachable!("fixture drift: bb0 ends in the OverflowNeg assert")
        };
        v2_build_assert_negation_vc(func, block, *target, cond, *expected, span)
    }

    /// The `Neg` operand of `bb1[0]`.
    fn neg_operand(func: &VerifiableFunction) -> &Operand {
        let Statement::Assign { rvalue: Rvalue::UnaryOp(UnOp::Neg, operand), .. } =
            &func.body.blocks[1].stmts[0]
        else {
            unreachable!("fixture drift: bb1[0] is the Neg")
        };
        operand
    }

    fn negation_rows(func: &VerifiableFunction) -> Vec<VerificationCondition> {
        crate::generate_vcs(func)
            .into_iter()
            .filter(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. }))
            .collect()
    }

    fn proof_gaps(func: &VerifiableFunction) -> usize {
        crate::generate_vcs(func)
            .into_iter()
            .filter(|vc| match &vc.kind {
                VcKind::UnsupportedMir { kind, detail } => {
                    kind.contains("RecognizedSafetyAssertProofGap")
                        || detail.contains("RecognizedSafetyAssertProofGap")
                }
                _ => false,
            })
            .count()
    }

    fn row_width(vc: &VerificationCondition) -> (Ty, Option<u32>) {
        let VcKind::NegationOverflow { ty } = &vc.kind else {
            panic!("not a negation row: {:?}", vc.kind)
        };
        (ty.clone(), vc.obligation.as_ref().and_then(|o| o.width))
    }

    #[test]
    fn the_negation_builder_binds_a_literal_at_its_declared_width() {
        // THE DEFECT at the builder: it refused every literal, and `operand_ty`
        // typed one by its VALUE (`i64` for `i32::MIN` and for `i8::MIN`).
        for (name, width) in LITERAL_NEGATIONS {
            let func = load(name);
            let vc = assert_lane_negation(&func)
                .unwrap_or_else(|| panic!("{name}: the assert lane must build the literal's row"));
            assert_eq!(
                row_width(&vc),
                (Ty::Int { width, signed: true }, Some(width)),
                "{name}: the row is at the Neg destination's width"
            );
        }
    }

    #[test]
    fn the_statement_row_is_built_at_the_destination_width_too() {
        // `v2_build_negation_raw_vc` reads the same shape off its own statement, so
        // where it still emits (the forged arms below) it agrees with the builder.
        for (name, width) in LITERAL_NEGATIONS {
            let func = load(name);
            let block = &func.body.blocks[1];
            let vc = v2_build_negation_raw_vc(&func, block, neg_operand(&func), &func.span, 0)
                .unwrap_or_else(|| panic!("{name}: the statement lane builds its row"));
            assert_eq!(row_width(&vc), (Ty::Int { width, signed: true }, Some(width)), "{name}");
        }
    }

    #[test]
    fn a_literal_statement_row_without_its_neg_refuses_rather_than_guessing() {
        // No `_ = Neg(operand)` at `stmt_index` means no destination to read a
        // literal's width from: no row, never one at the value-derived i64.
        let func = load("literal_neg_min");
        let block = &func.body.blocks[1];
        assert!(
            v2_build_negation_raw_vc(&func, block, neg_operand(&func), &func.span, 7).is_none()
        );
    }

    #[test]
    fn each_literal_negation_keeps_exactly_one_row_and_no_gap() {
        // Before: a `RecognizedSafetyAssertProofGap` plus the vacuous statement row
        // (measured: `neg_min`, `neg_min8`, `neg_max` at `Int { width: 64 }`,
        // `neg_min128` at 128, every one `proved` and kernel-certified).
        for (name, width) in LITERAL_NEGATIONS {
            let func = load(name);
            let neg_block = &func.body.blocks[1];
            assert!(
                safety::v2_negation_assert_exactly_bound(&func, neg_block, neg_operand(&func)),
                "{name}: the statement row is exactly bound to the assert's"
            );
            let rows = negation_rows(&func);
            assert_eq!(rows.len(), 1, "{name}: one negation row, the assert lane's");
            assert_eq!(row_width(&rows[0]).1, Some(width), "{name}");
            assert_eq!(proof_gaps(&func), 0, "{name}: the assert lane builds the row");
        }
    }

    // FORGED ARMS: one field of real input changed each; the builder must refuse
    // and BOTH rows (the proof gap and the statement row) must stand.

    fn assert_cond_operands(func: &mut VerifiableFunction) -> (&mut Operand, &mut Operand) {
        let Statement::Assign { rvalue: Rvalue::BinaryOp(BinOp::Eq, l, r), .. } =
            &mut func.body.blocks[0].stmts[0]
        else {
            unreachable!("fixture drift: bb0[0] is the `Eq(operand, MIN)` check")
        };
        (l, r)
    }

    fn assert_refused(name: &str, func: &VerifiableFunction) {
        assert!(assert_lane_negation(func).is_none(), "{name}: the builder must refuse");
        assert!(!safety::v2_negation_assert_exactly_bound(
            func,
            &func.body.blocks[1],
            neg_operand(func)
        ));
        assert_eq!(negation_rows(func).len(), 1, "{name}: the statement row stands");
        assert_eq!(proof_gaps(func), 1, "{name}: beside the assert lane's gap");
    }

    #[test]
    fn a_guard_over_a_different_literal_does_not_bind() {
        // `Eq(const MIN + 1, const MIN)` guarding `Neg(const MIN)`: the literal the
        // assert compares is not the one negated. RED under: admitting any two
        // literals rather than two EQUAL ones.
        let mut func = load("literal_neg_min");
        *assert_cond_operands(&mut func).0 =
            Operand::Constant(ConstValue::Int(crate::range::signed_min(32) + 1));
        assert_refused("different literal", &func);
    }

    #[test]
    fn a_guard_against_a_value_other_than_int_min_does_not_bind() {
        // `Eq(const MAX, const MAX)` guarding `Neg(const MAX)`: the right literal,
        // but not compared with i32::MIN. RED under: dropping the `== Some(min)`
        // half of `cond_binds_operand`.
        let mut func = load("literal_neg_max");
        let (l, r) = assert_cond_operands(&mut func);
        *r = l.clone();
        assert_refused("not INT_MIN", &func);
    }

    #[test]
    fn a_guard_at_the_value_derived_width_does_not_bind() {
        // `Eq(const i8::MIN, const i64::MIN)` guarding the i8 `Neg(const -128)`: a
        // MIN at the width `operand_ty` derives (64) is not the destination's.
        // RED under: reading the literal's width from `operand_ty` again.
        let mut func = load("literal_neg_min8");
        *assert_cond_operands(&mut func).1 =
            Operand::Constant(ConstValue::Int(crate::range::signed_min(64)));
        assert_refused("i64 MIN for an i8 Neg", &func);
    }

    #[test]
    fn a_place_guard_does_not_bind_a_literal() {
        // `Eq(_0, const MIN)`: a place is not the literal it may happen to hold.
        let mut func = load("literal_neg_min");
        *assert_cond_operands(&mut func).0 = Operand::Copy(trust_types::Place::local(0));
        assert_refused("place guard", &func);
    }

    #[test]
    fn a_second_entry_into_the_negation_block_keeps_both_rows() {
        // The builder still binds, but the Neg can be reached without passing the
        // assert, so the statement row is not self-guarded and must stay. RED under:
        // dropping the sole-entry scan of `v2_negation_assert_exactly_bound`.
        let mut func = load("literal_neg_min");
        let id = BlockId(func.body.blocks.len());
        func.body.blocks.push(BasicBlock {
            id,
            stmts: Vec::new(),
            terminator: Terminator::Goto(BlockId(1)),
        });
        assert!(assert_lane_negation(&func).is_some());
        assert!(!safety::v2_negation_assert_exactly_bound(
            &func,
            &func.body.blocks[1],
            neg_operand(&func)
        ));
        assert_eq!(negation_rows(&func).len(), 2);
    }
}

/// LITERAL-PAIR-WIDTH-1 and SELF-GUARDED-LITERAL-OPERAND-2 (2026-10-13): the width of an
/// operation over TWO width-less signed literals, and a literal shift-amount cast source.
/// Real artifacts from `tests/data/literal_pair_width_arms.rs`; the whole-pipeline
/// verdicts are pinned by `tests/literal_pair_width_real_mir.rs`, and these pin the
/// helpers that decide them: the destination width, the unknown row that replaces a
/// dropped one, the binder/builder lockstep and the literal cast-source value check.
#[cfg(test)]
mod literal_pair_width_tests {
    use trust_types::{Place, VcKind};

    use super::*;

    fn load(name: &str) -> VerifiableFunction {
        // STRAIGHT FROM TEXT: `literal_pair_ud128` carries `Int: i128::MIN`.
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");
        let text = std::fs::read_to_string(format!("{path}literal_pair_{name}.json"))
            .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must be readable: {e}"));
        serde_json::from_str(&text)
            .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must deserialize: {e}"))
    }

    /// `(block, stmt_index, op, lhs, rhs)` of the one `Div`/`Rem` statement.
    fn divrem(func: &VerifiableFunction) -> (BlockId, usize, BinOp, Operand, Operand) {
        for block in &func.body.blocks {
            for (index, stmt) in block.stmts.iter().enumerate() {
                if let Statement::Assign { rvalue: Rvalue::BinaryOp(op, lhs, rhs), .. } = stmt
                    && matches!(op, BinOp::Div | BinOp::Rem)
                {
                    return (block.id, index, *op, lhs.clone(), rhs.clone());
                }
            }
        }
        unreachable!("fixture drift: no Div/Rem statement")
    }

    fn statement_row(
        func: &VerifiableFunction,
        stmt_index: Option<usize>,
    ) -> VerificationCondition {
        let (block, _, op, lhs, rhs) = divrem(func);
        v2_build_signed_div_overflow_vc(
            func,
            &func.body.blocks[block.0],
            op,
            &lhs,
            &rhs,
            &SourceSpan::default(),
            stmt_index,
        )
        .expect("a signed Div/Rem over two literals always gets a row")
    }

    #[test]
    fn a_literal_pair_reads_the_destination_width() {
        // RED under: `literal_pair_int_type` falling back to `int_op_type`, which
        // answers 64 for every one of these (and 64 for `i128::MIN / -1` too: the
        // narrower of 128 and -1's 64).
        for (name, width) in
            [("ud8", 8), ("ud16", 16), ("ud32", 32), ("ud128", 128), ("ur8", 8), ("cd8", 8)]
        {
            let func = load(name);
            let (block, index, _, lhs, rhs) = divrem(&func);
            assert_eq!(
                literal_pair_int_type(&func, &func.body.blocks[block.0], index, &lhs, &rhs),
                Some((width, true)),
                "{name}"
            );
            assert_eq!(int_op_type(&func, &lhs, &rhs), Some((64, true)), "{name}: the old answer");
        }
    }

    #[test]
    fn every_other_pair_keeps_int_op_type() {
        // A place on either side: the helper is `int_op_type`, byte for byte.
        for name in ["ctl_ud_px", "ctl_ud_py"] {
            let func = load(name);
            let (block, index, _, lhs, rhs) = divrem(&func);
            assert_eq!(
                literal_pair_int_type(&func, &func.body.blocks[block.0], index, &lhs, &rhs),
                int_op_type(&func, &lhs, &rhs),
                "{name}"
            );
        }
    }

    #[test]
    fn the_statement_row_is_built_at_the_destination_width() {
        // `ud8`: the row is `-128 in i8 && -1 in i8 && -128 == -128 && -1 == -1`, and
        // records the operation's `i8`, not the fabricated `i64`.
        let func = load("ud8");
        let row = statement_row(&func, Some(0));
        let i8_ty = Ty::Int { width: 8, signed: true };
        assert!(
            matches!(&row.kind, VcKind::ArithmeticOverflow { op: BinOp::Div, operand_tys }
                if *operand_tys == (i8_ty.clone(), i8_ty.clone())),
            "{:?}",
            row.kind
        );
        let smt = row.formula.to_smtlib();
        assert!(!smt.contains("9223372036854775808"), "no i64 bound survives: {smt}");
        assert!(smt.contains("(- 128)") || smt.contains("-128"), "INT_MIN at i8: {smt}");
    }

    #[test]
    fn an_unresolvable_width_is_an_unknown_row_never_none() {
        // No statement index (no destination to read), and a projected destination:
        // the builder must still return a row, the fail-closed unknown one.
        let func = load("ud8");
        let unknown = |vc: &VerificationCondition| match &vc.kind {
            VcKind::UnsupportedMir { kind, .. } => kind == "LiteralPairWidthUnresolved",
            _ => false,
        };
        assert!(unknown(&statement_row(&func, None)), "no statement index");

        let mut projected = load("ud8");
        projected.body.locals[0].ty =
            Ty::Tuple(vec![Ty::Int { width: 8, signed: true }, Ty::Int { width: 8, signed: true }]);
        let Statement::Assign { place, .. } = &mut projected.body.blocks[0].stmts[0] else {
            unreachable!()
        };
        place.projections.push(trust_types::Projection::Field(0));
        assert!(unknown(&statement_row(&projected, Some(0))), "projected destination");
        assert_eq!(
            literal_pair_int_type(
                &projected,
                &projected.body.blocks[0],
                0,
                &Operand::Constant(ConstValue::Int(-128)),
                &Operand::Constant(ConstValue::Int(-1)),
            ),
            None,
            "the binder refuses (keeps both rows) where the builder emits the unknown row"
        );

        let mut unsigned = load("ud8");
        unsigned.body.locals[0].ty = Ty::Int { width: 8, signed: false };
        assert!(
            unknown(&statement_row(&unsigned, Some(0))),
            "a signed pair into an unsigned place"
        );
    }

    #[test]
    fn a_pointer_sized_destination_reads_64() {
        // The faithful lane's `isize` spelling resolves at the pinned 64-bit width.
        let mut func = load("ctl_ud64");
        func.body.locals[0].ty = Ty::PtrSizedInt { signed: true };
        let (block, index, _, lhs, rhs) = divrem(&func);
        assert_eq!(
            literal_pair_int_type(&func, &func.body.blocks[block.0], index, &lhs, &rhs),
            Some((64, true))
        );
    }

    #[test]
    fn the_checked_chain_suppression_binds_at_the_destination_width() {
        // The direct `Overflow(Div|Rem)` suppression, in lockstep with the builder.
        // RED under: reverting its width to `int_op_type` (the cond's `Eq(const MIN,
        // const MIN)` is then compared against `i64::MIN` and never binds).
        for name in ["cd8", "cd32", "cr16", "cd128", "ctl_cd64", "ctl_cdsize"] {
            let func = load(name);
            let (block, index, op, lhs, rhs) = divrem(&func);
            assert!(
                v2_divrem_overflow_assert_exactly_bound(&func, op, block, index, &lhs, &rhs),
                "{name}: the canonical chain binds"
            );
        }
        // `100 / 7`: `Eq(const 7, const -1)` compares two DIFFERENT literals, and the
        // binder takes the left one as the constant side, so it still refuses; the
        // statement row it keeps is TRUE (`100 != i32::MIN`).
        let func = load("ok_cd32");
        let (block, index, op, lhs, rhs) = divrem(&func);
        assert!(!v2_divrem_overflow_assert_exactly_bound(&func, op, block, index, &lhs, &rhs));
    }

    /// `shl_lit`'s amount comparison: `_2 = Cast(const 40, u32); _3 = Lt(move _2,
    /// const 32_u32)` in bb0.
    fn cast_source(func: &VerifiableFunction) -> Option<Operand> {
        let block = &func.body.blocks[0];
        let Statement::Assign { rvalue: Rvalue::BinaryOp(BinOp::Lt, amount, bits), .. } =
            &block.stmts[1]
        else {
            unreachable!("fixture drift: bb0[1] is the amount comparison")
        };
        let bits = const_int_value(bits).expect("BITS is a constant");
        v2_shift_amount_cast_source(func, block, 1, amount, bits).cloned()
    }

    fn with_cast_source(value: i128) -> VerifiableFunction {
        let mut func = load("shl_lit");
        let Statement::Assign { rvalue: Rvalue::Cast(src, _), .. } =
            &mut func.body.blocks[0].stmts[0]
        else {
            unreachable!("fixture drift: bb0[0] is the amount cast")
        };
        *src = Operand::Constant(ConstValue::Int(value));
        func
    }

    #[test]
    fn a_literal_cast_source_is_admitted_by_value() {
        // RED under: the literal arm reverted to `_ => return None`.
        let func = load("shl_lit");
        assert!(matches!(cast_source(&func), Some(Operand::Constant(ConstValue::Int(40)))));
        for value in [i128::from(i32::MIN), -1, 0, 31, 32, i128::from(i32::MAX)] {
            let admitted = match cast_source(&with_cast_source(value)) {
                Some(Operand::Constant(ConstValue::Int(v))) => v == value,
                _ => false,
            };
            assert!(admitted, "{value} lies in i32");
        }
    }

    #[test]
    fn a_literal_outside_the_signed_amount_type_is_refused() {
        for value in [i128::from(i32::MIN) - 1, i128::from(i32::MAX) + 1, 5_000_000_000] {
            assert!(cast_source(&with_cast_source(value)).is_none(), "{value} is no i32");
        }
    }

    #[test]
    fn a_literal_cast_into_a_parameter_or_a_mistyped_temporary_is_refused() {
        // The place checks still apply to the TEMPORARY of a literal cast.
        let mut retyped = load("shl_lit");
        retyped.body.locals[2].ty = Ty::Int { width: 64, signed: false };
        assert!(cast_source(&retyped).is_none(), "temporary declared u64, cast u32");

        let mut param = load("shl_lit");
        let Statement::Assign { place, .. } = &mut param.body.blocks[0].stmts[0] else {
            unreachable!()
        };
        *place = Place::local(1);
        let Statement::Assign { rvalue: Rvalue::BinaryOp(BinOp::Lt, amount, _), .. } =
            &mut param.body.blocks[0].stmts[1]
        else {
            unreachable!()
        };
        *amount = Operand::Move(Place::local(1));
        assert!(cast_source(&param).is_none(), "a parameter is never the cast temporary");
    }
}
