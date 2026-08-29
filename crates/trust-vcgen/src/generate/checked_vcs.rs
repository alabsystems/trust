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
        function: func.name.clone().into(),
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
    let Ty::Tuple(fields) = crate::place_ty(func, place)? else {
        return None;
    };
    if fields.len() != 2 || fields[1] != Ty::Bool {
        return None;
    }
    let payload = fields.into_iter().next()?;
    crate::fixed_width_integer_descriptor(&payload).is_some().then_some(payload)
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
    let (_, lhs, rhs) = v2_shift_assert_binds_statement(func, block, target, op, cond)?;
    v2_build_shift_overflow_vc(func, block, op, lhs, rhs, span, None)
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
/// plain-`BinaryOp` shift whose amount is STRUCTURALLY the cond's `amount` and
/// is not rewritten before the shift reads it, and `BITS` equals the true
/// shift-RESULT width.
fn v2_shift_assert_binds_statement<'a>(
    func: &'a VerifiableFunction,
    block: &trust_types::BasicBlock,
    target: BlockId,
    op: BinOp,
    cond: &Operand,
) -> Option<(usize, &'a Operand, &'a Operand)> {
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
    let (_, BinOp::Lt, amount, bits) =
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
    if !v2_operands_structurally_equal(rhs, amount) {
        return None;
    }
    // The amount the assert guarded must be the amount the shift reads: refuse
    // if any target-block statement before the shift rewrites it.
    if let Operand::Copy(p) | Operand::Move(p) = amount {
        let name = crate::place_to_var_name(func, p);
        if (0..stmt_index).any(|k| stmt_writes_name(func, shift_block, k, &name)) {
            return None;
        }
    }
    // BITS must be exactly the true shifted width; a lookalike guard against a
    // different constant is not this shift's UB check.
    let (_, _, _, shifted_width) = v2_shift_violation_formula(func, block, op, lhs, rhs, None)?;
    if i128::from(shifted_width) != bits_value {
        return None;
    }
    Some((stmt_index, lhs, rhs))
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
    if !matches!(op, BinOp::Shl | BinOp::Shr) {
        return false;
    }
    let Some(op_block) = func.body.blocks.get(shift_block_id.0) else {
        return false;
    };
    // The compared values must not be rewritten before the shift reads them.
    // (The binder already enforces this for the amount; the shifted value is
    // added here for the same reason, so the suppressed row's operands are the
    // ones the surviving row was bound over.)
    for operand in [lhs, rhs] {
        if let Operand::Copy(p) | Operand::Move(p) = operand {
            let name = crate::place_to_var_name(func, p);
            if (0..stmt_index).any(|k| stmt_writes_name(func, op_block, k, &name)) {
                return false;
            }
        }
    }
    // The entry block has no guarding predecessor to inherit an assert from.
    if shift_block_id.0 == 0 {
        return false;
    }

    func.body.blocks.iter().any(|assert_block| {
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
        // Sole-entry check: no OTHER block's terminator may reach the shift's
        // block, so the surviving assert row covers every execution of the
        // shift.
        let bypassed = func.body.blocks.iter().any(|b| {
            b.id != assert_block.id
                && b.terminator.exit_targets().iter().any(
                    |t| matches!(t, trust_types::ClauseTarget::Block(succ) if *succ == shift_block_id),
                )
        });
        if bypassed {
            return false;
        }
        // The assert lane's OWN binder decides identity, so the suppression can
        // only fire where that lane really emits the equivalent row.
        let Some((found_index, found_lhs, found_rhs)) =
            v2_shift_assert_binds_statement(func, assert_block, *target, op, cond)
        else {
            return false;
        };
        found_index == stmt_index
            && v2_operands_structurally_equal(found_lhs, lhs)
            && v2_operands_structurally_equal(found_rhs, rhs)
    })
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
/// rule this binder re-checks; and its two `operand_ty` reads are exactly the two
/// `v2_build_signed_div_overflow_vc` performs, so the suppressed row could not
/// exist where the surviving one does not. This is an exact
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
    if !matches!(op, BinOp::Div | BinOp::Rem) {
        return false;
    }
    // The width whose INT_MIN the per-statement row proves about — the same
    // recovery `v2_build_signed_div_overflow_vc` uses. A non-signed operation
    // has no overflow row to deduplicate.
    let Some((width, signed)) = int_op_type(func, lhs, rhs) else {
        return false;
    };
    if !signed {
        return false;
    }
    let int_min = crate::range::signed_min(width);

    // The compared values must not be rewritten before the division reads them.
    let Some(op_block) = func.body.blocks.get(div_block.0) else {
        return false;
    };
    for operand in [lhs, rhs] {
        if let Operand::Copy(p) | Operand::Move(p) = operand {
            let name = crate::place_to_var_name(func, p);
            if (0..stmt_index).any(|k| stmt_writes_name(func, op_block, k, &name)) {
                return false;
            }
        }
    }

    // The suppression is sound only when the SURVIVING assert row covers every
    // execution of the operation. The assert row proves the cond read at ITS
    // terminator, so an operation block with any other way in (a second
    // predecessor edge, or being the entry block) keeps its own row — a forged
    // body must not launder the obligation through an assert its executions can
    // bypass.
    if div_block.0 == 0 {
        return false;
    }

    func.body.blocks.iter().any(|assert_block| {
        if !matches!(&assert_block.terminator, Terminator::Assert { target, .. } if *target == div_block)
        {
            return false;
        }
        // PARITY with the bounds member (block_defs.rs): the assert's FAILURE /
        // cleanup edge runs exactly when the checked condition is violated, so
        // it must not re-enter the block whose rows this would suppress. The
        // scan below excludes `assert_block.id`, which leaves that edge
        // invisible; a row reachable through it is REFUTABLE, not vacuous.
        if assert_block.terminator.unwind_cleanup_target() == Some(div_block) {
            return false;
        }
        // Sole-entry check: no OTHER block's terminator may reach the
        // operation's block (the bound assert's own success edge is the one
        // permitted way in; the assert terminator has no second normal edge to
        // the same block, and a cleanup edge into it from anywhere else counts
        // as a bypass).
        let bypassed = func.body.blocks.iter().any(|b| {
            b.id != assert_block.id
                && b.terminator.exit_targets().iter().any(
                    |t| matches!(t, trust_types::ClauseTarget::Block(succ) if *succ == div_block),
                )
        });
        if bypassed {
            return false;
        }
        v2_divrem_overflow_assert_binds_statement(
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
        )
    })
}

/// A `flag = Eq(value, const)` binder: `(func, block, before, flag,
/// expected_operand, const_value) -> bool`. The three implementations differ in
/// EXACTLY ONE dimension — which COMPARED VALUES they admit ([`V2ComparedValue`])
/// — and are otherwise one rule, shared verbatim by
/// [`v2_eq_def_binds_compared_value`]: live-def reverse scan, const identity,
/// structural operand equality, stability of the compared value through the
/// terminator read. Passing the rule explicitly at each call site is how that
/// dimension stays visible instead of being smuggled in by a default.
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
/// `eq_binds` exists because the two callers meet this cond at different operand
/// shapes, MEASURED not assumed. Both need PROJECTION tolerance — on the real
/// extraction the value compared here is `_3.0`, the value field of a
/// `CheckedAdd`/`CheckedSub` tuple — and they differ on CONSTANTS.
/// `v2_divrem_overflow_assert_exactly_bound` passes
/// [`v2_eq_def_binds_divrem_overflow_operand`], which admits one, because
/// `i32::MIN / y` lowers to `Eq(const INT_MIN, const INT_MIN)` and refusing it
/// resurrects a vacuous row. The zero-divisor chain passes
/// [`v2_eq_def_binds_projected_operand`], which refuses one, because a const-false
/// `assert(2 == 0)` must not take a real divisor's obligation. Nothing else about
/// the rule moves.
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
    eq_binds: V2EqConstBinder,
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
        eq_binds(func, assert_block, and_index, divisor_flag, rhs, -1)
            && eq_binds(func, assert_block, and_index, min_flag, lhs, int_min)
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
    if !matches!(op, BinOp::Div | BinOp::Rem) {
        return false;
    }
    let Some(op_block) = func.body.blocks.get(div_block.0) else {
        return false;
    };
    // The compared values must not be rewritten before the operation reads them.
    for operand in [lhs, divisor] {
        if let Operand::Copy(p) | Operand::Move(p) = operand {
            let name = crate::place_to_var_name(func, p);
            if (0..stmt_index).any(|k| stmt_writes_name(func, op_block, k, &name)) {
                return false;
            }
        }
    }
    // The entry block has no guarding predecessor to inherit an assert from.
    if div_block.0 == 0 {
        return false;
    }

    func.body.blocks.iter().any(|assert_block| {
        let Terminator::Assert { cond, expected: false, msg, target, .. } =
            &assert_block.terminator
        else {
            return false;
        };
        if !msg_matches_op(msg) {
            return false;
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
                return false;
            }
            let bypassed = func.body.blocks.iter().any(|b| {
                b.id != assert_block.id
                    && b.terminator.exit_targets().iter().any(
                        |t| matches!(t, trust_types::ClauseTarget::Block(succ) if *succ == div_block),
                    )
            });
            if bypassed {
                return false;
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
            return false;
        }
        // One operation: the suppressed row and the surviving row must be about
        // the same unique same-op statement over structurally identical operands.
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
        v2_divzero_cond_binds_divisor(func, assert_block, cond, divisor)
    })
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
    !func.body.blocks.iter().any(|b| {
        b.id != from.id
            && b.terminator
                .exit_targets()
                .iter()
                .any(|t| matches!(t, trust_types::ClauseTarget::Block(succ) if *succ == to))
    })
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
///    shape and keeps both rows.
/// 2. SOLE ENTRY, TWICE. `zero_block -> ovf` and `ovf -> div_block` must each be
///    the only way into their successor ([`v2_block_entered_only_from`]). If
///    EITHER hop could be bypassed the surviving assert row would not cover every
///    execution of the operation, which is the whole soundness claim.
/// 3. THE INTERVENING BLOCK IS THAT OPERATION'S OWN OVERFLOW ASSERT, decided by
///    the overflow lane's own binder
///    ([`v2_divrem_overflow_assert_binds_statement`]) — same opcode, same unique
///    statement, same operands, canonical `BitAnd(Eq(divisor, -1), Eq(lhs,
///    INT_MIN))` cond at the operation's true width. Block adjacency is not
///    authority any more than bare target identity is.
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
    let Some((width, signed)) = int_op_type(func, lhs, divisor) else {
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
    // (4) The new rewrite window: nothing in the intervening block may redefine
    // the value the zero assert compared or the value the operation divides.
    for operand in [lhs, divisor] {
        if let Operand::Copy(p) | Operand::Move(p) = operand {
            let name = crate::place_to_var_name(func, p);
            if (0..ovf_block.stmts.len()).any(|k| stmt_writes_name(func, ovf_block, k, &name)) {
                return false;
            }
        }
    }
    // (3) …and the intervening block is THIS operation's overflow assert, on the
    // overflow lane's own terms. The projection-tolerant compared-value binder is
    // required here and only here: on the real `i64 x / (n - n)` extraction the
    // divisor this cond compares is `_3.0`, the value field of the `CheckedSub`
    // tuple. (`--emit=mir` pretty-prints that as a plain local and hides it; the
    // extracted verification input does not.)
    v2_divrem_overflow_assert_binds_statement(
        func,
        op,
        ovf_block,
        div_block,
        op_block,
        stmt_index,
        lhs,
        divisor,
        crate::range::signed_min(width),
        v2_eq_def_binds_projected_operand,
    )
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
/// stronger than a same-block scan). Fail-closed on every other shape.
fn v2_divzero_cond_binds_divisor(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    cond: &Operand,
    divisor: &Operand,
) -> bool {
    v2_eq_def_binds_projected_operand(func, block, block.stmts.len(), cond, divisor, 0)
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
/// function-wide, strictly stronger than a same-block scan). A CONSTANT compared
/// value is refused outright — the zero-divisor callers handle nonzero constants
/// earlier via `v2_divisor_is_nonzero_constant`, and admitting one here is how a
/// const-false `assert(2 == 0)` would take a real divisor's obligation.
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

/// Which COMPARED VALUES a [`V2EqConstBinder`] admits — the one dimension in which
/// this family's three call sites genuinely differ. Every other clause of the rule
/// is shared by [`v2_eq_def_binds_compared_value`] and so cannot drift between
/// them.
#[derive(Clone, Copy)]
enum V2ComparedValue {
    /// A CONSTANT, or a PROJECTION-FREE place. The rule 18a0083876 shipped.
    ConstOrBarePlace,
    /// A STATICALLY ADDRESSED place, projected or not — never a constant.
    StaticPlace,
    /// A STATICALLY ADDRESSED place, or a CONSTANT.
    ConstOrStaticPlace,
}

impl V2ComparedValue {
    fn admits_constant(self) -> bool {
        matches!(self, Self::ConstOrBarePlace | Self::ConstOrStaticPlace)
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
    let (Operand::Copy(flag_place) | Operand::Move(flag_place)) = flag else {
        return false;
    };
    if !flag_place.projections.is_empty() || guards::value_local_is_unstable(func, flag_place.local)
    {
        return false;
    }
    let flag_name = crate::place_to_var_name(func, flag_place);
    for k in (0..before.min(block.stmts.len())).rev() {
        if !stmt_writes_name(func, block, k, &flag_name) {
            continue;
        }
        let Statement::Assign { place, rvalue, .. } = &block.stmts[k] else {
            return false;
        };
        if place != flag_place {
            return false;
        }
        let Rvalue::BinaryOp(BinOp::Eq, l, r) = rvalue else {
            return false;
        };
        let (var_side, const_side) =
            if matches!(l, Operand::Constant(_)) { (r, l) } else { (l, r) };
        if const_int_value(const_side) != Some(value)
            || !v2_operands_structurally_equal(var_side, expected)
        {
            return false;
        }
        match var_side {
            Operand::Copy(p) | Operand::Move(p) => {
                if !rule.admits_place(p) || guards::value_local_is_unstable(func, p.local) {
                    return false;
                }
                let name = crate::place_to_var_name(func, p);
                if (k + 1..block.stmts.len()).any(|j| stmt_writes_name(func, block, j, &name)) {
                    return false;
                }
            }
            // A constant cannot be rewritten, so there is nothing to keep stable;
            // whether one may stand in for the operand at all is `rule`'s call.
            Operand::Constant(_) => {
                if !rule.admits_constant() {
                    return false;
                }
            }
            // Every other spelling lacks the occurrence identity this binding
            // needs; `v2_operands_structurally_equal` has already refused them,
            // and `Operand` is `#[non_exhaustive]`, so refuse explicitly.
            _ => return false,
        }
        return true;
    }
    false
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
    let operand = v2_find_target_neg_operand(func, target)?;
    // NB: owned — `ty` is moved into `VcKind::NegationOverflow { ty }` below (a stored
    // obligation type), so the borrowed walk does not apply here. The negated operand is
    // a scalar int, never the fat recursive ADT, so no clone is saved anyway.
    let ty = crate::operand_ty(func, operand)?;
    if !ty.is_signed() {
        return None;
    }
    let width = ty.int_width()?;
    let (_, BinOp::Eq, lhs, rhs) = v2_find_condition_binary_operands(func, block, cond)? else {
        return None;
    };
    let same_runtime_operand = |candidate: &Operand| match (candidate, operand) {
        (Operand::Copy(a) | Operand::Move(a), Operand::Copy(b) | Operand::Move(b)) => a == b,
        // Constant negations are folded before this MIR shape; every other
        // public spelling lacks stable occurrence identity here and declines.
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
                function: func.name.clone().into(),
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
    let sv = StmtVersionCtx::build(func);
    let subject = version_rename_at(
        &operand_to_formula(func, operand),
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
        function: func.name.clone().into(),
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
                Formula::Ge(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
            ])
        } else {
            Formula::Ge(Box::new(lhs_f.clone()), Box::new(rhs_f.clone()))
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
        function: func.name.clone().into(),
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
        obligation: None,
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
        (
            Operand::Copy(pa) | Operand::Move(pa),
            Operand::Copy(pb) | Operand::Move(pb),
        ) => pa == pb,
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
) -> Option<(Formula, Ty, Ty, u32)> {
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

    // `shifted_width` is the TRUE shifted-operand width from MIR (the shift-RESULT
    // type), NOT the `Formula::Int(bit_width)` threshold inside `invalid_shift` — the
    // [10]-class width authority the shift obligation records.
    Some((Formula::And(vec![shift_range, invalid_shift]), operand_ty, shift_ty, shifted_width))
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
    stmt_index: Option<usize>,
) -> Option<VerificationCondition> {
    let (violation, operand_ty, shift_ty, shifted_width) =
        v2_shift_violation_formula(func, block, op, lhs, rhs, stmt_index)?;
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
    let end = stmt_index.unwrap_or(block.stmts.len());
    let (formula, rec_body, kept) =
        v2_formula_with_block_defs_at_point_recorded(func, block, end, violation);
    let obligation =
        v2_shift_overflow_seed_record(func, block, rhs, &rec_body, kept, end, shifted_width);
    Some(VerificationCondition {
        kind: VcKind::ShiftOverflow { op, operand_ty, shift_ty },
        function: func.name.clone().into(),
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
    rec_body: &Formula,
    kept: Vec<Formula>,
    end: usize,
    shifted_width: u32,
) -> Option<ObligationRecord> {
    let Formula::And(conjuncts) = rec_body else {
        return None;
    };
    if conjuncts.len() != 2 {
        return None;
    }
    let shift_range = conjuncts[0].clone();
    let atomic_core = conjuncts[1].clone();
    let sv = StmtVersionCtx::build(func);
    let subject = version_rename_at(&operand_to_formula(func, rhs), &sv, func, block.id, end);
    let mut wrappers = vec![ObligationWrapper::ConjoinFactsLast { facts: vec![shift_range] }];
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

    // Rust permits exactly one integer-to-char `as` cast: `u8 as char`.
    // Every u8 value is a Unicode scalar (the surrogate interval starts at
    // 0xD800), so this conversion cannot trap, overflow, or create an invalid
    // char. Wider integer-to-char casts are rejected by rustc and every other
    // non-integer destination still reaches the fail-closed arm below.
    if matches!(&from_ty, Ty::Int { width: 8, signed: false }) && matches!(to_ty, Ty::Char) {
        return None;
    }

    if crate::is_thin_pointer_identity_cast(&from_ty, to_ty)
        || crate::is_fn_pointer_identity_cast(&from_ty, to_ty)
        || crate::is_callable_reification_cast(&from_ty, to_ty)
        // `&[T; N] -> &[T]` unsize is a metadata-only coercion (slice len is the
        // array's static N); it carries no arithmetic/bounds obligation, so it is
        // modeled with no VC, mirroring the primary cast-relation gate.
        || crate::is_array_to_slice_ref_cast(&from_ty, to_ty)
        // `&T -> &dyn Trait` (trait-object pointer unsize) is likewise a
        // metadata-only coercion — an infallible vtable attach with no
        // arithmetic/range obligation. `convert.rs` began spelling it
        // `Rvalue::Cast` in d806992cd4 (it was `Use(OpaqueConst)` before); without
        // this arm the coercion mints a spurious `unsupported cast` here.
        || crate::cast_target_is_trait_object_pointer(to_ty)
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
                function: func.name.clone().into(),
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
    let sv = StmtVersionCtx::build(func);
    let subject = version_rename_at(&value, &sv, func, block.id, stmt_index);

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
    let Formula::And(body_conjuncts) = &body else {
        // Unreachable — `raw` is literally a 2-conjunct `And` and the rename is
        // structural. Fail closed if that ever changes: emit the VC with NO
        // recorded obligation so the consumer takes the legacy peel route rather
        // than authenticating an unfaithful record.
        return Some(VerificationCondition {
            kind: VcKind::NegationOverflow { ty },
            function: func.name.clone().into(),
            location: span.clone(),
            formula,
            contract_metadata: None,
            obligation: None,
        });
    };
    if body_conjuncts.len() != 2 {
        return Some(VerificationCondition {
            kind: VcKind::NegationOverflow { ty },
            function: func.name.clone().into(),
            location: span.clone(),
            formula,
            contract_metadata: None,
            obligation: None,
        });
    }
    let range_fact = body_conjuncts[0].clone();
    let atomic_core = body_conjuncts[1].clone();
    let mut wrappers = vec![ObligationWrapper::ConjoinFactsLast { facts: vec![range_fact] }];
    if !kept.is_empty() {
        wrappers.push(ObligationWrapper::ConjoinFactsLast { facts: kept });
    }
    Some(VerificationCondition {
        kind: VcKind::NegationOverflow { ty },
        function: func.name.clone().into(),
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
}

/// REAL-ARTIFACT guards for the PROJECTED-OPERAND `Overflow(Div|Rem)` row.
///
/// `18a0083876` wrote that `v2_eq_def_binds_operand_to_const` "refuses a PROJECTED
/// compared value, and this shape needs one" — and then applied the reasoning to
/// the zero-divisor row while leaving the overflow row three lines above bound to
/// the refusing helper. So under overflow checks, where the value rustc compares
/// against `INT_MIN` and then divides is `_3.0` (the value field of a
/// `CheckedAdd`/`CheckedSub` tuple), the canonical `let a = x + 1; a / b` kept BOTH
/// `arithmetic overflow (Div)` rows and the statement-lane one was `NOT _7 AND _7`
/// — UNSAT by construction, a `proved` row at the span of a genuinely-false
/// division. MEASURED on the extracted bundle, not on pretty-printed `--emit=mir`,
/// which folds the projection into a plain local and hides the whole family.
///
/// Every fixture loaded here is the compiler's OWN extracted verification input
/// (`-Ztrust-dump=mir`, stage2 @ 17abbefc3) and its source is committed beside them
/// as `tests/data/divrem_projected_arms.rs`, so every row re-derives. The forged
/// arms MUTATE that real input one field at a time, so each guard has a planted
/// violation whose provenance is the real lowering.
#[cfg(test)]
mod projected_divrem_overflow_tests {
    use std::collections::HashMap;

    use trust_types::{AssertMessage, BasicBlock, Place, Projection, VcKind};

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
                out.push(v2_divrem_overflow_assert_exactly_bound(
                    func, *op, block.id, stmt_index, lhs, rhs,
                ));
            }
        }
        assert!(!out.is_empty(), "fixture must contain a Div/Rem statement");
        out
    }

    /// The shipped `arithmetic overflow (Div|Rem)` rows — both lanes emit this same
    /// `VcKind`, at the same span, so the transport cannot tell them apart and the
    /// count is the whole observable.
    fn overflow_rows(func: &VerifiableFunction) -> Vec<VerificationCondition> {
        crate::generate_vcs(func)
            .into_iter()
            .filter(|vc| {
                matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Div | BinOp::Rem, .. })
            })
            .collect()
    }

    /// Walk the VC's top-level conjunction, recording
    ///   * `defs` — flag definitions `flag = <condition>` (the MIR bool temps);
    ///   * `neg`  — flags asserted NEGATIVELY (`(not flag)`, i.e. a passed assert);
    ///   * `pos`  — everything asserted POSITIVELY, rendered.
    fn collect(
        f: &Formula,
        defs: &mut HashMap<String, Formula>,
        neg: &mut Vec<String>,
        pos: &mut Vec<String>,
    ) {
        match f {
            Formula::And(parts) => {
                for p in parts {
                    collect(p, defs, neg, pos);
                }
            }
            Formula::Not(inner) => {
                if let Formula::Var(name, _) = inner.as_ref() {
                    neg.push(name.clone());
                }
            }
            Formula::Var(name, _) => pos.push(format!("VAR:{name}")),
            Formula::Eq(a, b) => {
                // `flag = <condition>` is a DEFINITION, not an assertion of `flag`.
                if let Formula::Var(name, _) = a.as_ref() {
                    defs.insert(name.clone(), b.as_ref().clone());
                } else if let Formula::Var(name, _) = b.as_ref() {
                    defs.insert(name.clone(), a.as_ref().clone());
                }
                pos.push(f.to_smtlib());
            }
            other => pos.push(other.to_smtlib()),
        }
    }

    /// The flags this VC asserts to be FALSE while also asserting every conjunct of
    /// their defining condition TRUE — `flag != 0` and `flag == 0` at once. Such a
    /// VC is UNSAT by construction: it can only ever come back `proved`, and it
    /// proves nothing. That is precisely the shape shipping as a `proved`
    /// `arithmetic overflow (Div)` row at the span of a genuinely-false division.
    ///
    /// Resolution goes one level THROUGH the `BitAnd` carrier on purpose. This
    /// family's cond is `_7 = _5 AND _6` with `_5 = (rhs == -1)` and
    /// `_6 = (lhs == INT_MIN)`, and the statement-lane row asserts the two
    /// COMPARISONS separately rather than the conjunction — so the zero-divisor
    /// canary's rule (compare `defs[flag]` against the positive terms verbatim,
    /// correct where the cond IS a single comparison) sees nothing here.
    fn vacuous_flags(vc: &VerificationCondition) -> Vec<String> {
        let mut defs = HashMap::new();
        let (mut neg, mut pos) = (Vec::new(), Vec::new());
        collect(&vc.formula, &mut defs, &mut neg, &mut pos);
        let conjuncts = |def: &Formula| -> Vec<Formula> {
            match def {
                Formula::And(parts) if !parts.is_empty() => parts
                    .iter()
                    .map(|part| match part {
                        Formula::Var(n, _) => defs.get(n).cloned().unwrap_or_else(|| part.clone()),
                        other => other.clone(),
                    })
                    .collect(),
                other => vec![other.clone()],
            }
        };
        let mut bad: Vec<String> = neg
            .iter()
            .filter(|flag| {
                defs.get(*flag)
                    .is_some_and(|def| conjuncts(def).iter().all(|c| pos.contains(&c.to_smtlib())))
            })
            .cloned()
            .collect();
        bad.sort();
        bad.dedup();
        bad
    }

    fn assert_no_vacuous_row(name: &str, func: &VerifiableFunction) {
        for vc in overflow_rows(func) {
            let bad = vacuous_flags(&vc);
            assert!(
                bad.is_empty(),
                "{name}: a surviving `Overflow(Div|Rem)` row asserts {bad:?} false while \
                 asserting every conjunct of its defining condition true — UNSAT by \
                 construction, so it can only ever be `proved`: {}",
                vc.formula.to_smtlib()
            );
        }
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

    /// Moves `bb<from>`'s statement 0 to position `at` in `bb<to>`, leaving the
    /// number of definitions of the value it writes UNCHANGED at one — so
    /// `guards::value_local_is_unstable` still calls it stable and the arm isolates
    /// a positional rewrite scan instead of the function-wide stability check.
    fn relocate_first_stmt(func: &mut VerifiableFunction, from: usize, to: usize, at: usize) {
        let stmt = func.body.blocks[from].stmts.remove(0);
        func.body.blocks[to].stmts.insert(at, stmt);
    }

    // -----------------------------------------------------------------------
    // THE DEFECT. A projected compared value is the canonical rustc lowering
    // under overflow checks, and it kept the vacuous duplicate.
    // -----------------------------------------------------------------------

    #[test]
    fn a_projected_dividend_keeps_exactly_one_overflow_row() {
        // `let a = x + 1; a / b`. Two `arithmetic overflow (Div)` rows before this
        // fix; the statement-lane one binds `_7 = (b == -1) & (_3.0 == INT_MIN)`,
        // asserts `(not _7)` as a path guard, and then asserts both conjuncts.
        let func = load("projected_dividend_div");
        assert_eq!(suppressed(&func), vec![true]);
        assert_eq!(overflow_rows(&func).len(), 1, "exactly one live obligation must remain");
        assert_no_vacuous_row("projected_dividend_div", &func);
    }

    #[test]
    fn a_projected_divisor_keeps_exactly_one_overflow_row() {
        // The other side of the same cond: `Eq(_3.0, -1)` compares the projection.
        let func = load("projected_divisor_div");
        assert_eq!(suppressed(&func), vec![true]);
        assert_eq!(overflow_rows(&func).len(), 1);
        assert_no_vacuous_row("projected_divisor_div", &func);
    }

    #[test]
    fn both_operands_projected_keeps_exactly_one_overflow_row() {
        for name in ["projected_both_div", "projected_both_rem"] {
            let func = load(name);
            assert_eq!(suppressed(&func), vec![true], "{name}");
            assert_eq!(overflow_rows(&func).len(), 1, "{name}");
            assert_no_vacuous_row(name, &func);
        }
    }

    // -----------------------------------------------------------------------
    // THE SURFACE MUST NOT SHRINK. A suppression that deletes an honest row is a
    // lost recovery, not a fix.
    // -----------------------------------------------------------------------

    #[test]
    fn a_provably_safe_projected_division_keeps_a_dischargeable_obligation() {
        // `let a = (x & 1) + 1; a / b` provably cannot overflow — `a` is 1 or 2.
        // Exactly one REAL, refutable obligation must remain for the discharge
        // lanes to prove; deleting it would be a lost recovery, not a fix.
        let func = load("provably_safe_projected_dividend_div");
        assert_eq!(suppressed(&func), vec![true]);
        assert_eq!(overflow_rows(&func).len(), 1);
        assert_no_vacuous_row("provably_safe_projected_dividend_div", &func);
    }

    #[test]
    fn two_distinct_projected_divisors_each_keep_their_own_obligation() {
        // Two divisions, two chains, one shared dividend `_4.0`. A skip keyed on
        // the BLOCK rather than on the OPERANDS collapses these into one. Pre-fix
        // this emitted FOUR rows, two honest and two vacuous.
        let func = load("two_distinct_projected_divisors");
        assert_eq!(suppressed(&func), vec![true, true]);
        assert_eq!(overflow_rows(&func).len(), 2, "each division keeps one row");
        assert_no_vacuous_row("two_distinct_projected_divisors", &func);
    }

    #[test]
    fn the_unprojected_surface_is_untouched() {
        // The rule 18a0083876 shipped still decides plain-local code, and admitting
        // projections must not have moved it in either direction.
        //  * `plain_dividend_deep_div` is the CONTROL: identical block depth,
        //    identical assert-chain length, identical sole-entry topology, `Div` in
        //    the same block position — the ONE difference is that its dividend is a
        //    plain local. One row before this fix and one after.
        //  * `deref_operand_div` is `*p / *q`, which rustc lowers through
        //    projection-free temporaries, so it too is the plain shape.
        for name in ["plain_dividend_deep_div", "deref_operand_div"] {
            let func = load(name);
            assert_eq!(suppressed(&func), vec![true], "{name}");
            assert_eq!(overflow_rows(&func).len(), 1, "{name}");
            assert_no_vacuous_row(name, &func);
        }
    }

    #[test]
    fn a_constant_compared_value_stays_suppressed() {
        // `i32::MIN / y` lowers to `_4 = Eq(const INT_MIN, const INT_MIN)` and is
        // suppressed TODAY. RED under: swapping the direct caller onto
        // `v2_eq_def_binds_projected_operand`, whose `let Copy | Move = var_side
        // else { return false }` refuses a constant outright — which would take
        // these back to two rows and RESURRECT the vacuous row at the span of a
        // genuinely-false division. The union of the two admissions is forced.
        for name in ["const_min_dividend_div", "const_min_dividend_rem"] {
            let func = load(name);
            assert_eq!(suppressed(&func), vec![true], "{name}");
            assert_eq!(overflow_rows(&func).len(), 1, "{name}");
            assert_no_vacuous_row(name, &func);
        }
    }

    #[test]
    fn an_unsigned_projected_division_has_no_overflow_row_to_move() {
        // No signed `Overflow(Div)` obligation exists, and rustc emits no such
        // assert. Untouched in both directions.
        let func = load("projected_unsigned_div");
        assert_eq!(suppressed(&func), vec![false]);
        assert_eq!(overflow_rows(&func).len(), 0);
    }

    #[test]
    fn an_unguarded_library_call_division_keeps_its_surface() {
        // `a.div_euclid(b)` lowers to a Call with NO MIR overflow assert. There is
        // nothing to bind to, so nothing here can reach it.
        let func = load("unguarded_call_projected_div");
        assert_eq!(overflow_rows(&func).len(), 0);
    }

    // -----------------------------------------------------------------------
    // MEASURED NON-SUPPRESSIONS. These keep BOTH rows, one of which is vacuous —
    // over-reporting, which is the safe direction, and the reason each refuses is
    // a rule that must stay.
    // -----------------------------------------------------------------------

    #[test]
    fn a_mismatched_comparison_constant_keeps_both_rows() {
        // `7 / y` lowers to `_4 = Eq(const 7, const INT_MIN)`. The constant does
        // not match the operation's INT_MIN, so no binding exists. RED under:
        // dropping the `const_int_value(const_side) != Some(value)` identity check.
        let func = load("nonmin_const_dividend_div");
        assert_eq!(suppressed(&func), vec![false]);
        assert_eq!(overflow_rows(&func).len(), 2);
    }

    #[test]
    fn a_constant_divisor_keeps_both_rows() {
        // `a / 3` compares two constants on BOTH sides of the `== -1` conjunct, so
        // no place identity exists to bind. Two rows before this fix and two after.
        let func = load("provably_safe_projected_div");
        assert_eq!(suppressed(&func), vec![false]);
        assert_eq!(overflow_rows(&func).len(), 2);
    }

    #[test]
    fn the_vacuity_detector_can_fail() {
        // A guard nobody has watched fail proves nothing. `7 / y`'s statement-lane
        // row IS the vacuous shape — it asserts `(not _5)` where
        // `_5 = (y == -1) & (7 == INT_MIN)`, then asserts both conjuncts — and it
        // is deliberately NOT suppressed (no constant identity to bind). So exactly
        // one of its two rows must be flagged. If this arm ever reports zero, the
        // detector has stopped detecting and every `assert_no_vacuous_row` above is
        // passing for free; check first that the block-def rendering of a comparison
        // still matches `v2_build_signed_div_overflow_vc`'s violation rendering
        // character for character.
        let func = load("nonmin_const_dividend_div");
        let rows = overflow_rows(&func);
        assert_eq!(rows.len(), 2);
        let flagged = rows.iter().filter(|vc| !vacuous_flags(vc).is_empty()).count();
        assert_eq!(flagged, 1, "exactly the self-guarded duplicate must be flagged");
    }

    // -----------------------------------------------------------------------
    // FORGED ARMS. Each mutates REAL extracted MIR in one place and must restore
    // BOTH rows: over-reporting is the safe direction. The comment on each names
    // the loosening that turns it red, and only that loosening does.
    // -----------------------------------------------------------------------

    #[test]
    fn an_index_projected_compared_value_keeps_both_rows() {
        // `_a[_i]` compared against INT_MIN, `_i` rewritten, then `_a[_i]` divided,
        // is two different values under one place spelling: the base-stability check
        // is asked about `_a`, and the name-keyed rewrite scans look for writes to
        // `a[_i]`, so a write to `_i` is invisible to BOTH. RED under: deleting
        // `v2_place_is_statically_addressed`, which is the only thing that refuses
        // this — `_1` is a never-assigned parameter, so the base is "stable".
        //
        // rustc copies an element read into a projection-free temporary before
        // comparing it, so the comparison and the division are retargeted onto the
        // element place itself. `_1` really is `[i32; 4]`, so `_1[_2]` types as
        // `i32` and every other clause of the binding still holds. The Move -> Copy
        // normalisation of the divisor is required only because
        // `v2_operands_structurally_equal` distinguishes the two spellings; without
        // it the arm would refuse for an unrelated reason and could never go red.
        let mut func = load("index_operand_div");
        let element = Operand::Copy(Place { local: 1, projections: vec![Projection::Index(2)] });
        let Statement::Assign { rvalue: Rvalue::BinaryOp(_, eq_lhs, _), .. } =
            &mut func.body.blocks[3].stmts[1]
        else {
            unreachable!("fixture drift: bb3[1] is the `Eq(dividend, INT_MIN)` conjunct")
        };
        *eq_lhs = element.clone();
        let Statement::Assign { rvalue: Rvalue::BinaryOp(_, div_lhs, div_rhs), .. } =
            &mut func.body.blocks[4].stmts[0]
        else {
            unreachable!("fixture drift: bb4[0] is the division")
        };
        *div_lhs = element;
        *div_rhs = Operand::Copy(Place::local(6));
        assert_eq!(suppressed(&func), vec![false]);
    }

    #[test]
    fn a_deref_projected_compared_value_keeps_both_rows() {
        // `(*_p)` reaches through a pointer whose pointee no direct-def scan tracks,
        // so a store through an alias between the comparison and the division is
        // invisible to this binding. RED under the same loosening as the `Index`
        // arm; kept separate because a partial allowlist could admit one and not the
        // other. The unmutated fixture BINDS (it is the plain-local shape), so this
        // arm changes exactly one thing: which place the comparison and the division
        // name.
        let mut func = load("deref_operand_div");
        let pointee = Operand::Copy(Place { local: 1, projections: vec![Projection::Deref] });
        let Statement::Assign { rvalue: Rvalue::BinaryOp(_, eq_lhs, _), .. } =
            &mut func.body.blocks[1].stmts[1]
        else {
            unreachable!("fixture drift: bb1[1] is the `Eq(dividend, INT_MIN)` conjunct")
        };
        *eq_lhs = pointee.clone();
        let Statement::Assign { rvalue: Rvalue::BinaryOp(_, div_lhs, _), .. } =
            &mut func.body.blocks[2].stmts[0]
        else {
            unreachable!("fixture drift: bb2[0] is the division")
        };
        *div_lhs = pointee;
        assert_eq!(suppressed(&func), vec![false]);
    }

    #[test]
    fn a_second_definition_of_the_base_in_a_third_block_keeps_both_rows() {
        // The plant has to sit in a THIRD block for this guard to be the one that
        // catches it: the same store inside the assert block, or in the division's
        // block before the division, is already caught by the two name-keyed scans
        // (`place_names_overlap("_3", "_3.0")` is true). Nowhere else in the
        // function is covered by anything but `guards::value_local_is_unstable` on
        // the BASE local, which counts field stores. RED under: dropping that check
        // from the compared-value stability clause.
        let mut func = load("projected_dividend_div");
        let redefinition = func.body.blocks[0].stmts[0].clone();
        let id = BlockId(func.body.blocks.len());
        func.body.blocks.push(BasicBlock {
            id,
            stmts: vec![redefinition],
            terminator: Terminator::Return,
        });
        assert_eq!(suppressed(&func), vec![false]);
    }

    #[test]
    fn a_rewrite_after_the_comparison_keeps_both_rows() {
        // The `CheckedAdd` that defines `_3` is moved out of bb0 and INTO the
        // overflow-assert block AFTER the `Eq(_3.0, INT_MIN)` conjunct, so `_3`
        // still has exactly ONE definition function-wide and the base-stability
        // check still calls it stable — yet the assert now compares a value that is
        // redefined before its own terminator reads the flag. RED under: deleting
        // the `(k + 1..)` post-comparison rewrite scan.
        let mut func = load("projected_dividend_div");
        relocate_first_stmt(&mut func, 0, 2, 2);
        assert_eq!(suppressed(&func), vec![false]);
    }

    #[test]
    fn a_rewrite_before_the_division_keeps_both_rows() {
        // Same relocation, into the DIVISION's block ahead of the division: the
        // assert compared one value and the division reads another. RED under:
        // deleting the caller's own pre-operation rewrite scan over `(0..stmt_index)`.
        let mut func = load("projected_dividend_div");
        relocate_first_stmt(&mut func, 0, 3, 0);
        assert_eq!(suppressed(&func), vec![false]);
    }

    #[test]
    fn a_second_entry_into_the_division_block_keeps_both_rows() {
        // Control can reach the division without executing the overflow assert, so
        // the surviving assert row does not cover every execution of the operation.
        // RED under: dropping the sole-entry scan.
        let mut func = load("projected_dividend_div");
        add_goto_predecessor(&mut func, 3);
        assert_eq!(suppressed(&func), vec![false]);
    }

    #[test]
    fn a_mismatched_opcode_keeps_both_rows() {
        // `Overflow(Rem)` guarding a `Div`. RED under: dropping the binder's
        // `*assert_op != op` test.
        let mut func = load("projected_dividend_div");
        let Terminator::Assert { msg, .. } = assert_terminator(&mut func, 2) else {
            unreachable!()
        };
        *msg = AssertMessage::Overflow(BinOp::Rem);
        assert_eq!(suppressed(&func), vec![false]);
    }

    #[test]
    fn an_inverted_assert_polarity_keeps_both_rows() {
        // rustc's `Overflow(Div|Rem)` assert panics when the condition is TRUE, so
        // its normal edge is `expected: false`; an inverted one has different
        // semantics and cannot stand in. RED under: dropping `expected: false` from
        // the binder's terminator pattern.
        let mut func = load("projected_dividend_div");
        let Terminator::Assert { expected, .. } = assert_terminator(&mut func, 2) else {
            unreachable!()
        };
        *expected = true;
        assert_eq!(suppressed(&func), vec![false]);
    }

    #[test]
    fn a_guard_over_a_different_value_keeps_both_rows() {
        // Bare target identity is NEVER suppression authority: the `== INT_MIN`
        // conjunct is retargeted from the projected dividend `_3.0` to the divisor
        // `_2`, so the assert is assert-shaped but does not guard this division's
        // dividend at all — and the duplicate it would suppress is genuinely
        // REFUTABLE (`b == -1` is consistent with `not((b == -1) & (b == INT_MIN))`).
        // RED under: keying the suppression on the block or the target instead of on
        // `v2_operands_structurally_equal`.
        let mut func = load("projected_dividend_div");
        let Statement::Assign { rvalue: Rvalue::BinaryOp(_, lhs, _), .. } =
            &mut func.body.blocks[2].stmts[1]
        else {
            unreachable!("fixture drift: bb2[1] is the `Eq(dividend, INT_MIN)` conjunct")
        };
        *lhs = Operand::Copy(Place::local(2));
        assert_eq!(suppressed(&func), vec![false]);
        assert_eq!(overflow_rows(&func).len(), 2);
    }
}
