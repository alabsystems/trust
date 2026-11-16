// The L0 safety pass: one VC per potentially-trapping operation in the body,
// each carried under the path guard of the block it occurs in.

use super::*;

// ---------------------------------------------------------------------------
// Authenticated-obligation recording (vertical slice: div/rem, negation)
// ---------------------------------------------------------------------------
// These helpers ONLY mutate `vc.obligation`; they never touch `vc.formula`, so the
// emitted formula is byte-identical whether or not an obligation is recorded. A VC
// with `obligation == None` (every non-slice kind, and every legacy dump) is left
// untouched. The record is a CLAIM the consumer authenticates by reconstruct-and-
// equate against `formula`; any incompleteness here costs certificates, never
// soundness (the consumer DECLINES on any mismatch). Every wrapping site in the
// shared loop below feeds one of these so the stored `{body, wrappers}` replays to
// exactly `formula`.

/// Record a `ConjoinFactsLast { facts }` wrapper — the shape every
/// `vc.formula = And([facts.., vc.formula])` conjoin site produces. No-op when the
/// VC carries no obligation or `facts` is empty (an empty conjoin is identity, and
/// the conjoin sites themselves skip empty fact lists).
pub(super) fn ob_record_conjoin(vc: &mut VerificationCondition, facts: &[Formula]) {
    if facts.is_empty() {
        return;
    }
    if let Some(ob) = vc.obligation.as_mut() {
        ob.wrappers.push(ObligationWrapper::ConjoinFactsLast { facts: facts.to_vec() });
    }
}

pub(super) fn ob_record_conjoin_owned(vc: &mut VerificationCondition, facts: Vec<Formula>) {
    if facts.is_empty() {
        return;
    }
    if let Some(ob) = vc.obligation.as_mut() {
        ob.wrappers.push(ObligationWrapper::ConjoinFactsLast { facts });
    }
}

/// Apply `f` to every `Formula` stored in a wrapper (conjoin facts, or a guarded
/// path term's guards). `Raw` terms carry no formula.
pub(super) fn ob_map_wrapper_formulas(
    w: &mut ObligationWrapper,
    f: &mut impl FnMut(Formula) -> Formula,
) {
    match w {
        ObligationWrapper::ConjoinFactsLast { facts } => {
            for fact in facts.iter_mut() {
                let owned = std::mem::replace(fact, Formula::Bool(true));
                *fact = f(owned);
            }
        }
        ObligationWrapper::PathGuardOr { paths } => {
            for p in paths.iter_mut() {
                if let PathGuardTerm::Guarded { guards } = p {
                    for g in guards.iter_mut() {
                        let owned = std::mem::replace(g, Formula::Bool(true));
                        *g = f(owned);
                    }
                }
            }
        }
    }
}

/// Mirror a whole-formula `version_rename_at` onto every recorded Formula — body,
/// subject, and every wrapper fact accumulated SO FAR — so each stays byte-identical
/// to its copy inside `formula`. `version_rename_at` is a per-variable deterministic
/// map that distributes over `And`/`Or`, so applying it piecewise equals applying it
/// to the whole tree. Called at the precondition step (the sole whole-formula rename
/// in the shared loop) BEFORE the precondition facts are recorded (they are conjoined
/// bare, after the rename).
pub(super) fn ob_record_rename_at(
    vc: &mut VerificationCondition,
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: BlockId,
    stmt_idx: usize,
) {
    let Some(ob) = vc.obligation.as_mut() else {
        return;
    };
    let body = std::mem::replace(&mut ob.body, Formula::Bool(true));
    ob.body = version_rename_owned_at(body, sv, func, block, stmt_idx);
    if let Some(s) = ob.subject.as_mut() {
        let subj = std::mem::replace(s, Formula::Bool(true));
        *s = version_rename_owned_at(subj, sv, func, block, stmt_idx);
    }
    for w in &mut ob.wrappers {
        ob_map_wrapper_formulas(w, &mut |x| version_rename_owned_at(x, sv, func, block, stmt_idx));
    }
}

/// Record a pure `inner ↦ And([facts.., inner])` conjoin by reading the facts back
/// from a before/after pair, for conjoin sites that compute their facts internally
/// (the type-range conjoins) and do not expose them. This records the WRAPPER the
/// step applied — the body was seeded earlier and is unchanged — so it is not a
/// guess about which sub-formula is the obligation. `after == before` is identity
/// (no wrapper). Any shape other than `And([.., before])` records nothing, so
/// reconstruction diverges and the consumer DECLINES (fail-closed).
pub(super) fn extract_conjoined_facts<'a>(
    before: &Formula,
    after: &'a Formula,
) -> Option<&'a [Formula]> {
    if std::ptr::eq(before, after) {
        return None;
    }
    if let Formula::And(children) = after
        && children.len() >= 2
        && children.last().is_some_and(|last| std::ptr::eq(last, before) || last == before)
    {
        Some(&children[..children.len() - 1])
    } else {
        None
    }
}

#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn ob_record_conjoin_step(
    vc: &mut VerificationCondition,
    f: impl FnOnce(Formula) -> (Formula, bool),
) {
    let formula = std::mem::replace(&mut vc.formula, Formula::Bool(true));
    let (after, wrapped) = f(formula);
    if vc.obligation.is_some()
        && wrapped
        && let Formula::And(children) = &after
        && children.len() >= 2
    {
        let facts = children[..children.len() - 1].to_vec();
        if let Some(ob) = vc.obligation.as_mut()
            && !facts.is_empty()
        {
            ob.wrappers.push(ObligationWrapper::ConjoinFactsLast { facts });
        }
    }
    vc.formula = after;
}

pub(super) fn ob_record_conjoin_wrap(
    vc: &mut VerificationCondition,
    before: &Formula,
    after: &Formula,
) {
    if vc.obligation.is_none() {
        return;
    }
    if let Some(facts) = extract_conjoined_facts(before, after) {
        ob_record_conjoin(vc, facts);
    }
    // Otherwise: identity (`after == before`) or unexpected shape — record nothing;
    // on an unexpected shape reconstruction will mismatch and the consumer DECLINES
    // (fail-closed).
}

pub(super) fn ob_record_conjoin_wrap_in_place(vc: &mut VerificationCondition, before: &Formula) {
    if vc.obligation.is_none() {
        return;
    }
    if let Some(facts) = extract_conjoined_facts(before, &vc.formula).map(<[Formula]>::to_vec) {
        if let Some(ob) = vc.obligation.as_mut()
            && !facts.is_empty()
        {
            ob.wrappers.push(ObligationWrapper::ConjoinFactsLast { facts });
        }
    }
}

/// Mirror the final `normalize_ssa_version_tokens` collapse onto every recorded
/// Formula. Same distributivity argument: the collapse decision is per-local
/// deterministic (a function of `func` + local, not of formula content), so
/// per-piece normalization equals whole-formula normalization restricted to that
/// piece. Called last, mirroring the shared loop's final normalize pass.
pub(super) fn ob_record_normalize(vc: &mut VerificationCondition, func: &VerifiableFunction) {
    let Some(ob) = vc.obligation.as_mut() else {
        return;
    };
    let body = std::mem::replace(&mut ob.body, Formula::Bool(true));
    ob.body = normalize_ssa_version_tokens_owned(func, body);
    if let Some(s) = ob.subject.as_mut() {
        let subj = std::mem::replace(s, Formula::Bool(true));
        *s = normalize_ssa_version_tokens_owned(func, subj);
    }
    for w in &mut ob.wrappers {
        ob_map_wrapper_formulas(w, &mut |x| normalize_ssa_version_tokens_owned(func, x));
    }
}

/// Trust (GAP 2): mirror the outermost `eliminate_term_ites` formula rewrite onto every
/// recorded Formula — body, subject, and every wrapper fact/guard — at the SAME place
/// (`generate_vcs`, entry.rs) it runs on `vc.formula`. The record is built PRE-elimination
/// (each producer/wrapper site conjoins the raw, possibly `Ite`-carrying facts), so
/// without this the record replays to the PRE-elimination formula and reconstruction
/// diverges from the rewritten `formula`. `eliminate_term_ites` is a pure `Formula ->
/// Formula` map that distributes over `And`/`Or`/`Not`/`Implies` exactly as
/// `reconstruct_obligation` composes the wrappers, so applying it piecewise here keeps
/// `reconstruct(record)` byte-identical to the eliminated `formula` (reuse the map — do
/// not re-derive it). No-op when the VC carries no obligation.
pub(super) fn ob_record_eliminate_ites(vc: &mut VerificationCondition, cap: usize) {
    let Some(ob) = vc.obligation.as_mut() else {
        return;
    };
    ob.body =
        eliminate_term_ites_owned(std::mem::replace(&mut ob.body, Formula::Bool(false)), cap);
    if let Some(s) = ob.subject.as_mut() {
        *s = eliminate_term_ites_owned(std::mem::replace(s, Formula::Bool(false)), cap);
    }
    for w in &mut ob.wrappers {
        ob_map_wrapper_formulas(w, &mut |x| eliminate_term_ites_owned(x, cap));
    }
}

/// Trust (slice ARM 1): build a div/rem-by-zero VC whose obligation is seeded from
/// what the emitter is ALREADY building — the raw assert-failure violation and the
/// block-defs it conjoins — NOT re-parsed from the finished formula. `subject` and
/// `width` are `None` (div/rem is payload-free). The shared wrapping loop below then
/// appends any further wrappers it applies.
fn v2_build_divrem_vc(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    cond: &Operand,
    expected: bool,
    span: &SourceSpan,
    kind: VcKind,
) -> VerificationCondition {
    v2_build_divrem_vc_raw(
        func,
        block,
        v2_assert_failure_formula(func, cond, expected),
        block.stmts.len(),
        span,
        kind,
    )
}

/// Trust (slice ARM 1): build a div/rem-by-zero VC from a raw violation the emitter
/// already built (`v2_assert_failure_formula` for the assert-terminator path, or
/// `v2_divisor_is_zero_formula` for the statement-`BinaryOp` and library-call
/// paths). `end` is the use-point the block-defs are versioned at (the block
/// terminal for the assert/call paths, the statement index for the mid-block
/// statement path). Payload-free: `subject`/`width` are `None`. The VC is pushed
/// into `block_vcs`, so the shared wrapping loop appends every later wrapper.
fn v2_build_divrem_vc_raw(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    raw: Formula,
    end: usize,
    span: &SourceSpan,
    kind: VcKind,
) -> VerificationCondition {
    let (formula, body, kept) = v2_formula_with_block_defs_at_point_recorded(func, block, end, raw);
    let mut wrappers = Vec::new();
    if !kept.is_empty() {
        wrappers.push(ObligationWrapper::ConjoinFactsLast { facts: kept });
    }
    VerificationCondition {
        kind,
        function: func.name.as_str().into(),
        location: span.clone(),
        formula,
        contract_metadata: None,
        obligation: Some(ObligationRecord { body, wrappers, subject: None, width: None }),
    }
}

// ---------------------------------------------------------------------------
// Pipeline v2 VC generator
// ---------------------------------------------------------------------------
/// Generate safety VCs (overflow, divzero, remainder-by-zero) with real SMT
/// formulas for the canonical VC pipeline.
///
/// When v2 was introduced, `generate_vcs` was reduced to a stub that
/// returned an empty Vec. Downstream integration tests (`real_ay_verification`,
/// `m5_e2e_loop`) call this function directly and expect formulas a solver
/// can reason about — not an empty Vec or `Formula::Bool(false)` placeholders.
///
/// This generator walks each block and emits:
///
/// - **Overflow VCs** for `Assert { msg: Overflow(op), .. }` paired with a
///   `CheckedBinaryOp(op, lhs, rhs)` in the same block. The emitted formula
///   is `input_ranges(lhs,rhs) AND NOT in_range_of_result_type(lhs op rhs)` —
///   satisfiable iff the operation can overflow given the input types.
/// - **Division/remainder-by-zero VCs** for `BinaryOp(Div|Rem, _, divisor)`
///   statements. The emitted formula is `divisor == 0` when `divisor` is a
///   variable. Literal nonzero divisors are skipped before VC construction.
///
/// Semantic guards from `build_semantic_guard_map` are conjoined to each VC
/// so successor blocks inherit the assert-passed dataflow (e.g., after a
/// passing `CheckedSub`, downstream overflow checks see `hi >= lo`).
#[cfg(test)]
pub(super) fn generate_v2_safety_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    generate_v2_safety_vcs_impl(func, None)
}

/// Whether an `Assert { OverflowNeg, expected: false }` somewhere in the function
/// is EXACTLY BOUND to `neg_block`'s `Neg` over `operand` — the canonical rustc
/// chain
///
/// ```text
/// _c = Eq(operand, const INT_MIN); assert(!move _c, OverflowNeg) -> neg_block;
/// neg_block: ... = UnaryOp(Neg, operand)
/// ```
///
/// THE NEGATION MEMBER OF THE FAMILY whose zero-divisor
/// ([`v2_divzero_assert_exactly_bound`]), `Overflow(Div|Rem)`
/// ([`v2_divrem_overflow_assert_exactly_bound`]) and shift
/// ([`v2_shift_assert_exactly_bound`]) members are already suppressed, and for
/// the same reason. `OverflowNeg` has the div/rem POLARITY — the cond is the
/// FAILURE condition and the assert expects `false` — not the shift's.
///
/// Under this binding the assert-lane row states EXACTLY the same proposition as
/// the per-statement `VcKind::NegationOverflow` row: the binding forces `cond`'s
/// live definition to be `operand == INT_MIN` over the very place the Neg
/// negates, and `INT_MIN` to be `signed_min` of that operand's own width, so the
/// assert lane's violation `cond` and the statement lane's violation
/// `operand == INT_MIN` are the same predicate. The per-statement row sits in the
/// assert's TARGET block, where the threaded `AssertHolds` path guard discharges
/// it VACUOUSLY. Measured on the real canary
/// (`let m = (x & 0) | i32::MIN; -m`, false for EVERY input) its formula is
///
/// ```text
/// (and (= _3 …) (= m …) (= _4 (= m (- 2147483648)))
///      (and (not _4) … (= _4 (= m (- 2147483648))) … (= m (- 2147483648))))
/// ```
///
/// — it binds `_4 = (m == INT_MIN)`, then asserts `NOT _4` AND `m == INT_MIN`,
/// i.e. `_4 AND NOT _4`, UNSAT by construction for every program. It can never
/// fail and discharges nothing, but it shipped in the structured transport as the
/// canary's ONLY positive claim: `summary: 0 trusted, 1 certified, 0 failed,
/// 0 unknown, 1 runtime-checked out of 2`, the `certified` row being this one.
///
/// IDENTITY, NOT REPLICATION. The last criterion asks the ASSERT LANE'S OWN
/// BUILDER whether it really emits the equivalent row for this assert, so the
/// suppressing lane cannot drift away from the emitting one: if
/// [`v2_build_assert_negation_vc`] declines for any reason (unsigned operand, no
/// integer width, a non-unique or rewritten target Neg, a cond that compares a
/// DIFFERENT value or a value other than `INT_MIN`, an `expected: true`
/// lookalike) there is no surviving twin and the per-statement row is kept. The
/// cheap structural filters run first, so at most one assert per Neg reaches the
/// builder.
///
/// i128 IS EXCLUDED, AND THAT IS MEASURED. At width 128 the two lanes take
/// DIFFERENT constructors — `v2_signed_bv_neg_overflow_formula` conjoined with
/// the SOURCE block's BV defs in the assert lane, with the TARGET block's in the
/// statement lane — so "the same proposition" would be an argument rather than an
/// identity. And there is nothing to fix: `-x` on `i128` reports BOTH rows
/// `failed`, so it over-reports and never false-proves; suppressing there could
/// only lose a refutable row. The exclusion is keyed on that BV constructor, not
/// on the width (SELF-GUARDED-CONST-OPERAND-1): a SYMBOLIC constant operand
/// (`const N: i128`) has no BV rendering, so at width 128 both lanes take the Int
/// constructors this rule was written for, and its statement row is the same
/// self-guarded vacuity as below 128.
///
/// SYMBOLIC CONSTANT OPERANDS (SELF-GUARDED-CONST-OPERAND-1). The negated value
/// may be a const-generic parameter or a keyed opaque scalar rather than a place
/// (`-N` extracts as `Eq(const N, const MIN)` / `Neg(const N)`); the assert lane's
/// builder binds it by value identity (`v2_operands_structurally_equal`), and a
/// constant has no rewrite window to check. This function needs no constant arm of
/// its own for that: it defers to the builder, which used to refuse every constant
/// and so left the vacuous statement row as the only `negation` row.
///
/// LITERAL OPERANDS (SELF-GUARDED-LITERAL-OPERAND-1). Under
/// `#![allow(arithmetic_overflow)]` `-i32::MIN` extracts as `Eq(const MIN, const
/// MIN)` / `Neg(const MIN)`. The builder now binds two equal literals by value, and
/// takes a width-less literal's width from the Neg's DESTINATION; this function
/// reads its width the same way (`checked_vcs::v2_negation_row_shape`), so the
/// constructor test asks about the row the builder really builds. Before, the
/// builder refused, the assert lane left a proof gap, and the statement row — built
/// at the i64 `operand_ty` gives the literal, and self-guarded besides — was the
/// function's only `negation` row, kernel-certified. A literal is NOT covered by the
/// i128 exclusion above: at width 128 neither lane conjoins anything to its BV
/// core, so the two rows are one formula (see the note at the exclusion).
///
/// Same fail-closed discipline as all three twins, and it is load-bearing: bare
/// target identity is NEVER suppression authority, the compared value must be
/// rewrite-stable between the comparison and the negation (enforced inside both
/// [`v2_find_target_neg_operand`] and [`v2_find_condition_binary_operands`]), and
/// the Neg's block must have the bound assert's success edge as its SOLE entry,
/// so a forged body cannot launder the obligation through an assert its
/// executions can bypass. Any non-canonical shape returns `false`, keeping both
/// rows — duplicates over-report, never under-report.
///
/// `neg_block` is the block being generated for, passed by reference rather than
/// by `BlockId`: [`v2_find_target_neg_operand`] and the `exit_targets`
/// reachability scan both address blocks by id-as-INDEX, so a body whose ids
/// disagree with their positions (or repeats one) could otherwise bind an assert
/// to a DIFFERENT block than the one holding the statement. The identity check
/// below refuses that outright.
pub(super) fn v2_negation_assert_exactly_bound(
    func: &VerifiableFunction,
    neg_block: &trust_types::BasicBlock,
    operand: &Operand,
) -> bool {
    // The entry block has no guarding predecessor to inherit an assert from.
    if neg_block.id.0 == 0 || !super::terminator_presence_for(func).has_overflow_neg_assert {
        return false;
    }
    // Id-as-index identity: `blocks[neg_block.id.0]` must be THIS block.
    if func.body.blocks.get(neg_block.id.0).is_none_or(|b| !std::ptr::eq(b, neg_block)) {
        return false;
    }
    // Trust (SELF-GUARDED-LITERAL-OPERAND-1, 2026-10-12): the WIDTH is the one the
    // assert lane's builder uses (`checked_vcs::v2_negation_row_shape`), so the
    // constructor test below asks about the row the builder really builds. For a
    // width-less literal that is the Neg's DESTINATION width, read off this block's
    // unique Neg (the same statement `v2_find_target_neg_operand` names below); a
    // literal whose statement cannot be found keeps both rows. Every other operand
    // keeps `operand_ty`, exactly as before.
    let (signed, width, mut target_has_unique_neg) =
        if matches!(operand, Operand::Constant(ConstValue::Int(_))) {
            let Some((ty, width)) = v2_find_target_neg_statement(func, neg_block.id)
                .filter(|(_, found)| v2_operands_structurally_equal(found, operand))
                .and_then(|(dest, found)| v2_negation_row_shape(func, dest, found))
            else {
                return false;
            };
            (ty.is_signed(), width, Some(true))
        } else {
            let Some(ty) = crate::operand_ty_cow(func, operand) else {
                return false;
            };
            let Some(width) = ty.int_width() else {
                return false;
            };
            (ty.is_signed(), width, None)
        };
    if !signed {
        return false;
    }
    // Trust (SELF-GUARDED-CONST-OPERAND-1, 2026-10-11): the measured i128
    // exclusion is keyed on the CONSTRUCTOR, not on the width. Both lanes ask the
    // same `v2_signed_bv_neg_overflow_formula(func, operand, width)` over this one
    // operand, so they take the BV constructors together or not at all. A place
    // or literal operand at width 128 does (the two lanes then conjoin different
    // BV block-def sets — the measured reason this member stays out). A symbolic
    // constant (`const N: i128`) has no BV rendering, so BOTH lanes fall back to
    // the same Int constructors used below width 128, and its statement row is the
    // same self-guarded vacuity: measured before the fix, `neg_c128` read `1
    // proved … of which 1 kernel-certified` beside `1 unknown`. A width above 128
    // (no Rust integer has one) stays out of scope outright, as before.
    //
    // Trust (SELF-GUARDED-LITERAL-OPERAND-1, 2026-10-12): …and an integer LITERAL
    // operand at width 128 takes the BV constructors in BOTH lanes but conjoins
    // NOTHING to them in either: `v2_collect_bv_shl_blockdef` reads only a place,
    // and `v2_dominating_operand_facts` skips every constant. So both rows are the
    // bare `Eq(BitVec(c, 128), BitVec(i128::MIN, 128))` — the identity this rule
    // needs, not an argument — and the measured reason for the exclusion (two
    // DIFFERENT block-def sets) does not exist for a literal. MEASURED before this
    // fix on the stage 1 of `46e9afaf95`: `-i128::MIN` under
    // `#![allow(arithmetic_overflow)]` read one `negation` row, PROVED and
    // kernel-certified (the statement row, behind the assert it duplicates), beside
    // the assert lane's proof gap; the builder now builds the BV row, and this lets
    // it be the only one.
    let literal = const_int_value(operand).is_some();
    if width > 128 {
        return false;
    }
    // PERF-COMPILER-VCGEN-804: the width-128 BV-constructor probe builds a whole
    // formula just to ask `is_some`; it is a function-level exclusion, so ask it
    // once, lazily, only after a candidate assert has passed its structural checks.
    // The answer is identical: an excluded operand still refuses every candidate.
    let bv_excluded: std::cell::OnceCell<bool> = std::cell::OnceCell::new();
    let bv_excluded_now = || {
        *bv_excluded.get_or_init(|| {
            width == 128
                && !literal
                && v2_signed_bv_neg_overflow_formula(func, operand, width).is_some()
        })
    };

    let mut check_candidate =
        |assert_block: &trust_types::BasicBlock, sole_entry_verified: bool| -> bool {
            let Terminator::Assert {
                cond,
                expected: false,
                msg: AssertMessage::OverflowNeg,
                target,
                span,
                ..
            } = &assert_block.terminator
            else {
                return false;
            };
            if *target != neg_block.id {
                return false;
            }
            // PARITY with the bounds member (block_defs.rs): the assert's FAILURE /
            // cleanup edge runs exactly when the checked condition is violated, so
            // it must not re-enter the block whose rows this would suppress.
            // Excluding only `assert_block.id` from the scan below leaves that edge
            // invisible, and a row reachable through it is REFUTABLE, not vacuous.
            if assert_block.terminator.unwind_cleanup_target() == Some(neg_block.id) {
                return false;
            }
            if bv_excluded_now() {
                return false;
            }
            // ONE negation, and therefore THIS one. `v2_find_target_neg_operand`
            // yields `Some` only when `target` holds exactly one `Neg` statement, and
            // `target` is this very block, so the assert the builder binds below is
            // bound to the statement now being generated for — not merely to its
            // block. A second `Neg` here makes the binder ambiguous and both rows stay.
            if !*target_has_unique_neg
                .get_or_insert_with(|| v2_find_target_neg_operand(func, *target).is_some())
            {
                return false;
            }
            // Sole-entry check: no OTHER block's terminator may reach the negation's
            // block, so the surviving assert row covers every execution of the Neg.
            if !sole_entry_verified
                && func.body.blocks.iter().any(|b| {
                    b.id != assert_block.id && b.terminator.has_exit_block_target(neg_block.id)
                })
            {
                return false;
            }
            // IDENTITY, NOT REPLICATION: the assert lane's OWN builder decides whether
            // the equivalent row really exists, so this lane cannot drift away from it.
            v2_build_assert_negation_vc(func, assert_block, *target, cond, false, span)
                .is_some_and(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. }))
        };

    if let Some(unique_pred) =
        crate::fn_memo::sole_predecessors(func).and_then(|sp| sp.unique_exit_predecessor(neg_block.id))
    {
        return unique_pred
            .and_then(|pred_id| func.body.blocks.get(pred_id.0))
            .is_some_and(|assert_block| check_candidate(assert_block, true));
    }

    func.body.blocks.iter().any(|assert_block| check_candidate(assert_block, false))
}

/// Summary-aware safety generation: the per-block semantic guard map also carries
/// each proved callee's rebound postcondition, so body safety VCs may soundly
/// assume them (separate-compilation boundary). The `None` path is the canonical
/// non-summary generator. Test-only since T3 C05: the production generation reads the
/// walk with its origins ([`generate_v2_safety_vcs_impl_with_origins_checked`]).
#[cfg(test)]
pub(super) fn generate_v2_safety_vcs_impl(
    func: &VerifiableFunction,
    summaries: Option<&crate::modular::SummaryDatabase>,
) -> Vec<VerificationCondition> {
    generate_v2_safety_vcs_impl_with_origins_checked(func, summaries)
        .rows
        .into_iter()
        .map(|(_, vc)| vc)
        .collect()
}

/// What the safety walk returns.
pub(super) struct SafetyWalk {
    /// Each row, paired with its originating `BlockId` (== `mir::BasicBlock` index, see
    /// `trust-mir-extract/src/convert.rs`).
    pub(super) rows: Vec<(BlockId, VerificationCondition)>,
    /// The indices into `rows`, ascending, of the rows an `Assert(Overflow(_))`
    /// terminator minted (T3 C05). Only such a row's block holds the overflow check the
    /// elision seam may remove: an arithmetic STATEMENT in the same block (a plain
    /// `BinaryOp`, e.g. inlined from a crate built without overflow checks) mints a row
    /// of the same kind and op that guards no `Assert` at all.
    pub(super) overflow_assert_rows: Vec<usize>,
    /// Whether the ambient verify budget or the row cap cut the walk short.
    pub(super) truncated: bool,
    /// Whether the row cap ([`MAX_VC_ROWS_PER_FUNCTION`]) cut it short. Unlike a budget
    /// trip, which latches the ambient budget and so reaches the compiler's checkpoint,
    /// the cap latches nothing: the caller must refuse the rows itself.
    pub(super) row_capped: bool,
}

/// Trust (2026-10-16, S1): the ordinary splice's path terms with every `Raw`
/// term marked [`PathGuardTerm::Collapsed`] when the block's guards were LOST —
/// a `degraded` block, except a content-free row whose reachability summary is
/// `Unconditional`. There the empty path is the in-edge disjunction itself
/// (`true`): positive information that the block is reachable, which keeps a
/// reachable `unreachable!()` a refutation; marking it would hold that genuine
/// refutation. `Collapsed` renders exactly as `Raw`, so no formula changes.
pub(super) fn v2_mark_lost_guards(
    path_terms: Vec<PathGuardTerm>,
    degraded: bool,
    is_content_free: bool,
    reachability: Option<&ReachSummary>,
) -> Vec<PathGuardTerm> {
    let guards_lost =
        degraded && !(is_content_free && matches!(reachability, Some(ReachSummary::Unconditional)));
    if !guards_lost {
        return path_terms;
    }
    path_terms
        .into_iter()
        .map(|term| match term {
            PathGuardTerm::Raw => PathGuardTerm::Collapsed,
            other => other,
        })
        .collect()
}

/// The safety walk ([`SafetyWalk`]).
///
/// The rows are the same rows whether or not the walk was cut short; what the
/// `truncated` flag adds is the ability to tell a COMPLETE enumeration from a prefix of
/// one. The proven-overflow-check elision seam
/// needs both halves: it joins a KernelCertified overflow row to its MIR block by the
/// origin, and there "no row for this key" and "the row that would have made this key
/// AMBIGUOUS was never generated" are the same observation, and only the second is a
/// licence to delete a live overflow check. The production generation keeps both
/// (T3 C05, `super::overflow_origins`).
pub(super) fn generate_v2_safety_vcs_impl_with_origins_checked(
    func: &VerifiableFunction,
    summaries: Option<&crate::modular::SummaryDatabase>,
) -> SafetyWalk {
    // Set at every point the ambient budget cuts the generation walk short. The returned
    // rows are then a PREFIX of the true set, not the set. A trip in the later
    // fact-decoration passes leaves the row LIST complete but some of its rows
    // UNDECORATED — still not the true set, and still refused by every consumer that
    // requires a complete one.
    let mut truncated = false;
    let mut row_capped = false;
    let path_guards = super::path_guard_analysis_for(func);
    let guard_paths_map = &*path_guards.paths;
    // Trust (lane-A CSE, deferred): build `StmtVersionCtx`, `path_definition_map`, and
    // `semantic_guards` lazily only when a generated row actually needs them (matching
    // `alloc_vcs.rs`), and query `tinv_rows::active_request` once per function rather
    // than per block and per statement.
    let sv_lazy: std::cell::OnceCell<std::rc::Rc<StmtVersionCtx>> = std::cell::OnceCell::new();
    let active_tinv_req = super::tinv_rows::active_request(func);

    // Track the originating block id alongside each VC so we can apply the
    // correct semantic guards. Matching by span is unreliable when multiple
    // blocks share `SourceSpan::default()` (as in many synthetic test MIRs).
    let mut block_vcs: Vec<(BlockId, VerificationCondition)> = Vec::new();
    // T3 C05: which rows an overflow `Assert` terminator minted (`SafetyWalk`). Nothing
    // below reorders or removes `block_vcs`, so an index stays the row's index.
    let mut overflow_assert_rows: Vec<usize> = Vec::new();
    // The USE POINT of each row, parallel to `block_vcs`: the statement index a
    // per-statement row reads its operands at, or the block terminal for every
    // other row. Filled by `pad_row_points`, so a row nobody labelled gets the
    // terminal — the pre-existing, whole-block kill.
    //
    // TWO passes consume it, and they must agree on the point FOR EACH ROW:
    //   1. the path-definition conjoin (`v2_live_path_defs_at_point`), which must
    //      not kill an entry fact on account of a write that happens AFTER the
    //      row's own read; and
    //   2. the whole-row version rename
    //      (`conjoin_preconditions_versioned_at_point_recorded`), which must not
    //      move that same read to its POST-write token.
    // Give one row two different points and the fact and the body it is about stop
    // naming the same value: the kept entry fact is then either name-disjoint from
    // the read it was kept for (a false REFUTATION) or, in the other direction,
    // re-unified with a post-write read. Both passes `zip` this vector against
    // `block_vcs` under their own length asserts; nothing between them pushes to,
    // removes from or reorders either side.
    let mut row_points: Vec<usize> = Vec::new();
    fn pad_row_points(row_points: &mut Vec<usize>, rows: usize, point: usize) {
        if row_points.len() < rows {
            row_points.resize(rows, point);
        }
    }

    // Trust (G1, 2026-10-27): the documented-return-contract facts of the body's
    // pointer-returning libc calls, computed at most once (only a body with a rustc
    // Null/Misaligned pointer assert asks).
    let ffi_pointer_facts: std::cell::OnceCell<Option<crate::ffi_pointer_contract::PointerFacts>> =
        std::cell::OnceCell::new();
    let fn_sym: trust_types::Symbol = func.name.as_str().into();
    for block in &func.body.blocks {
        pad_row_points(&mut row_points, block_vcs.len(), usize::MAX);
        // Trust (L0 termination guarantee — VC GENERATION): poll the ambient
        // per-function budget once per block.
        //
        // `trust_types::verify_budget` names "the VC-generation walks" as a
        // choke point, but this walk had NO poll at all, so
        // `-Ztrust-verify-function-budget-ms` could not bound VC generation:
        // a function whose generation spun never reached the post-generation
        // `preprocessing_budget_exceeded` checkpoint, and the budget that
        // exists to prevent exactly that never fired. Measured on `nn-core`,
        // `ny-core` and `clean-kernel`, all three spun here with no diagnostic.
        //
        // Breaking out is the ONLY sound degradation available. A gen-set
        // oracle may not return a truncated answer on overrun — an
        // under-approximated kill set lets a stale fact survive and vacuously
        // discharge a real obligation (a false PROVE) — so the values stay
        // exact and generation simply stops producing more rows. The caller in
        // `rustc_mir_transform::trust_verify` then observes the spent budget at
        // its existing checkpoint and applies the discipline `d9d9d675e3`
        // already landed: advisory warns and substitutes one counted `Unknown`
        // with the partial VCs DISCARDED, strict/certify/memory-safe keep the
        // located hard error. This adds a poll to an existing mechanism; it
        // does not introduce a second one.
        if trust_types::verify_budget::budget_exhausted()
            || block_vcs.len() >= max_vc_rows_per_function()
        {
            // The ROW COUNT is the second half of that bound, and it is the half
            // that defends MEMORY rather than time. Nothing capped how many rows
            // one function may generate, and each row's formula is rewritten up
            // to five times by the decoration phase below (path defs,
            // preconditions, path guards, the type-range battery, version
            // normalization), every rewrite allocating a fresh tree. MEASURED
            // 2026-09-10 on tla-cli: `heap -s` counted 86 MILLION live malloc
            // nodes at a 140.6 GB peak, and the body in the log was
            // `<ty::cli_schema::Cli as clap_builder::derive::FromArgMatches>
            // ::from_arg_matches_mut` — what `#[derive(Parser)]` emits for a CLI
            // with ty's number of subcommands, whose CFG no hand-written body
            // approaches. A step budget cannot see that: the rows are cheap to
            // produce and expensive to KEEP.
            //
            // The walk stops the same way for both. `truncated` tells the
            // overflow-check origin inventory (T3 C05, `super::overflow_origins`)
            // that its enumeration is not complete, so it gives no table. What
            // happens to the ROWS differs. A budget trip latches the ambient budget,
            // and the compiler's post-generation checkpoint discards the partial
            // set (advisory substitutes one counted `Unknown`, strict keeps the
            // located hard error). The cap latches nothing, so no checkpoint sees
            // it: `row_capped` tells `generate_vcs_impl_with_origins` to replace
            // the prefix with one fail-closed `Unknown` row (2026-10-11; until then
            // a capped function shipped a prefix of its rows as its obligation set,
            // which could report it proved by omission). No row is silently dropped
            // from a set anyone reads as complete.
            row_capped = block_vcs.len() >= max_vc_rows_per_function();
            truncated = true;
            break;
        }
        // 1. VCs from rustc Assert terminators that guard safety checks.
        // `unwind: _`: this loop emits the assert's OWN safety VC; the cleanup
        // successor is an unguarded CFG edge handled by the path/CHC machinery.
        if let Terminator::Assert { cond, expected, msg, span, target, unwind: _ } =
            &block.terminator
        {
            let vc = match msg {
                AssertMessage::DivisionByZero => {
                    (!v2_assert_failure_is_known_false(block, cond, *expected)).then(|| {
                        v2_build_divrem_vc(
                            func,
                            block,
                            cond,
                            *expected,
                            span,
                            VcKind::DivisionByZero,
                        )
                    })
                }
                AssertMessage::RemainderByZero => {
                    (!v2_assert_failure_is_known_false(block, cond, *expected)).then(|| {
                        v2_build_divrem_vc(
                            func,
                            block,
                            cond,
                            *expected,
                            span,
                            VcKind::RemainderByZero,
                        )
                    })
                }
                AssertMessage::Overflow(op) => {
                    // A signed 128-bit multiply whose operands both carry finite
                    // constant boxes on every reaching path provably cannot
                    // overflow (all four corner products fit i128) — emit
                    // nothing, exactly as the BoundsCheck arm below does for a
                    // literal in-range index.
                    //
                    // This gate is what makes suppression EXPRESSIBLE here. The
                    // builder's `None` means "could not analyse" and falls to
                    // `RecognizedSafetyAssertProofGap`, so without a pre-check
                    // the provably-safe case had no way to say so and was
                    // encoded as a constant-false violation formula instead —
                    // which `apply_vacuity_gate` then rejected as vacuous, and
                    // which could carry no proof authority in any case.
                    if v2_overflow_assert_provably_cannot_fire(
                        func, block, *target, *op, cond, *expected,
                    ) {
                        None
                    } else {
                        Some(
                            v2_build_assert_overflow_vc(
                                func, block, *target, *op, cond, *expected, span,
                            )
                            .unwrap_or_else(|| {
                                v2_recognized_assert_proof_gap_vc(
                                    func,
                                    block,
                                    *target,
                                    format!("Overflow({op:?})"),
                                    cond,
                                    *expected,
                                    span,
                                )
                            }),
                        )
                    }
                }
                AssertMessage::OverflowNeg => Some(
                    v2_build_assert_negation_vc(func, block, *target, cond, *expected, span)
                        .unwrap_or_else(|| {
                            v2_recognized_assert_proof_gap_vc(
                                func,
                                block,
                                *target,
                                "OverflowNeg".to_string(),
                                cond,
                                *expected,
                                span,
                            )
                        }),
                ),
                // EVERY `BoundsCheck` assert mints an obligation — including the
                // literal in-range element access (`arr[0]` on `[i64; 3]`,
                // `cols[0]` on `[Vec4; 4]`).
                //
                // Trust (#57 follow-up): this arm USED TO suppress that case
                // (`v2_bounds_assert_const_index_in_range`, now deleted) on the
                // theory that a provably-safe access needs no obligation. It is
                // provably safe — and that is exactly why the obligation must be
                // EMITTED. An obligation that is never emitted is SILENT, and
                // silence is indistinguishable from success at every layer below,
                // including the Clean kernel, which can only re-check propositions
                // it is handed. The trust-ir spine derives the obligation from the
                // same assert, so suppressing it here also manufactured a
                // producer disagreement (`ObligationSetDiff::native_only`) — the
                // fail-closed alarm 92b7a1fc52 added. On a3d's dependency-free
                // verified kernel that alarm fired 190 times, all of it this shape.
                //
                // The old suppression's stated cost does not apply to this arm and
                // was measured not to: the violation it builds is an ARITHMETIC
                // core (`Ge(_i, LEN)` conjoined with the index def `_i = k`), not
                // a `Bool` literal, so `apply_vacuity_gate` — which folds only the
                // BOOLEAN-literal skeleton — leaves it alone; and it carries a real
                // `ObligationRecord`, so `trust_certify::certify_vc` mints a
                // CleanCic interval-refutation certificate for it (`Int.lt_irrefl`)
                // and it acquires row-bound proof authority. That is the same lane
                // the constant SHIFT-amount check (`Or([1 < 0, 1 >= 8])`) already
                // proves through. Measured: all 95 of a3d's literal-index bounds
                // obligations PROVE and CERTIFY; `tests/trust-falsification/proved/
                // const_array_index.rs` — a fixture whose entire subject is this
                // obligation — goes from red back to proved.
                //
                // The genuinely-safe-but-unemittable shapes stay suppressed at
                // their own arms (Div/Rem's constant divisor via the shared
                // `static_truth` fold, signed-128 Mul via
                // `v2_overflow_assert_provably_cannot_fire`); those emit a bare
                // `Bool(false)` with `obligation: None`, which can acquire no
                // authority at all. This one is not that.
                AssertMessage::BoundsCheck => Some(
                    v2_build_bounds_assert_vc(func, block, *target, cond, *expected, span)
                        .unwrap_or_else(|| {
                            v2_recognized_assert_proof_gap_vc(
                                func,
                                block,
                                *target,
                                "BoundsCheck".to_string(),
                                cond,
                                *expected,
                                span,
                            )
                        }),
                ),
                AssertMessage::Custom(message) => Some(VerificationCondition {
                    kind: VcKind::Assertion { message: message.clone() },
                    function: fn_sym,
                    location: span.clone(),
                    formula: v2_formula_with_block_defs(
                        func,
                        block,
                        v2_assert_failure_formula(func, cond, *expected),
                    ),
                    contract_metadata: None,
                    obligation: None,
                }),
                // These spellings are protocol sentinels only in an authenticated
                // compiler lowering. Public TrustIR carries no such authority,
                // so preserve their exact runtime assertion instead of silently
                // treating the message as an Assume.
                AssertMessage::ResumedAfterReturn
                | AssertMessage::ResumedAfterPanic
                | AssertMessage::ResumedAfterDrop => Some(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!("public coroutine protocol assert: {msg:?}"),
                    },
                    function: fn_sym,
                    location: span.clone(),
                    formula: v2_formula_with_block_defs(
                        func,
                        block,
                        v2_assert_failure_formula(func, cond, *expected),
                    ),
                    contract_metadata: None,
                    obligation: None,
                }),
                // Trust (FIX A — trusted-std pointer-deref assert suppression):
                // a rustc-inserted Null/Misaligned pointer-dereference UB assert
                // whose OWN source span resolves under a CANONICAL sysroot std root
                // (`library/{core,alloc,std}/src/…` or the remapped
                // `/rustc/<hash>/library/…` form — the non-forgeable
                // `sep_engine::is_trusted_std_span` gate, which fails closed on
                // empty / `binary:` / user-crate spans) is STD-INTERNAL TCB: it is
                // the `vec!` macro's inlined `Box::new_uninit` allocation pointer
                // (non-null via `handle_alloc_error`, aligned to `Layout::align()`),
                // NOT a user `&T`/`*raw` deref. Discharging it rests on
                // allocation-provenance + trusted-std inlining (already trusted
                // campaign-wide via F5), NOT the `&T` reference invariant. SKIP the
                // VC at generation (mint nothing) so no un-modeled pointer formula
                // is ever handed to a spec-predicate lane — dissolving the
                // downstream `trust-types.Formula@1` schema-tag mismatch as a side
                // effect. FAIL CLOSED: the SAME assert with an empty / `binary:` /
                // synthetic / USER-CRATE span does NOT match this guard and falls
                // through to the fail-closed `other` catch-all below, so a genuine
                // `unsafe { *raw_ptr }` in user code keeps its refutable obligation.
                AssertMessage::NullPointerDereference
                | AssertMessage::MisalignedPointerDereference
                    if crate::sep_engine::is_trusted_std_span(span) =>
                {
                    None
                }
                // Trust (G1, 2026-10-27): a rustc Null/Misaligned pointer assert on a
                // CONTRACT-ROOTED local — the single, never-borrowed result of a libc
                // call with a documented pointer return contract (`__error`,
                // `__errno_location`, `getpwuid`) — that the contract and the
                // dominating checks make unable to fail: non-null by the contract or a
                // dominating `is_null`-false edge / passed null assert; aligned to the
                // assert's `K` by the contract's alignment or a dominating passed
                // alignment assert. Mint nothing, as the std-span arm above and the
                // extractor's `discharge_provably_safe_pointer_asserts` do for their
                // provably-safe asserts. Every other pointer assert (an unrooted local,
                // a nullable result with no dominating check, a larger `K`) falls
                // through to the fail-closed arm below. The hardened twin asks the same
                // question (`hardened::append_assert_panic_vcs`).
                AssertMessage::NullPointerDereference
                | AssertMessage::MisalignedPointerDereference
                    if ffi_pointer_facts
                        .get_or_init(|| {
                            crate::ffi_pointer_contract::PointerFacts::for_function(func)
                        })
                        .as_ref()
                        .is_some_and(|facts| facts.discharges_assert(func, block)) =>
                {
                    None
                }
                // Any safety assert that vcgen does not model above
                // (NullPointerDereference, MisalignedPointerDereference,
                // InvalidEnumConstruction, and any future AssertMessage) must
                // FAIL CLOSED, never silently drop.
                // rustc inserts these as real runtime UB checks; dropping the
                // obligation leaves nothing for the solver to refute, so the
                // function is reported vacuously "proved" while the check would
                // still fire at runtime -- a false-PROVE (e.g. an unchecked
                // `*ptr` where `ptr` is null). Emit an UnsupportedMir obligation
                // instead (formula `true`, i.e. unprovable); the compiler
                // preclassifies it to Unknown and it is never counted as proved.
                other => Some(unsupported_mir_vc(
                    func,
                    format!("UnmodeledSafetyAssert({other:?})"),
                    format!("{:?}: safety assert not modeled by vcgen: {other:?}", block.id),
                    span.clone(),
                )),
            };
            if let Some(vc) = vc {
                if matches!(msg, AssertMessage::Overflow(_)) {
                    overflow_assert_rows.push(block_vcs.len());
                }
                block_vcs.push((block.id, vc));
            }
        }

        // 1b. Panic-style assertion/unreachable terminators from native MIR.
        // Skip blocks that the path walk proves unreachable from the entry — generating
        // an Unreachable VC for dead code would falsely refute programs whose dead
        // blocks the compiler intentionally left as Unreachable scaffolding.
        if matches!(&block.terminator, Terminator::Unreachable | Terminator::Call { .. })
            && guard_paths_map.contains_key(&block.id)
            && let Some(vc) = v2_build_terminator_vc(func, block)
        {
            block_vcs.push((block.id, vc));
        }

        // 1c. Overflow obligations for arithmetic hidden INSIDE a library/intrinsic
        // Call that produces no caller-visible BinaryOp/Assert: `i32::pow` and the
        // `unchecked_{add,sub,mul}` UB-on-overflow intrinsics. Without this the op
        // is reported vacuously safe (no VC). Pushed keyed by `block.id` so it
        // inherits the SAME block-defs / path-guard / semantic-guard / precondition
        // / arg-type-range discharge machinery as the BinaryOp overflow VCs below —
        // a dominating `#[requires(n < K)]` (or small-const base) PROVES it, an
        // unguarded op FAILS. Native overflow asserts are not a suppression
        // authority: the old target-block-only set lost operation and operand
        // identity, so an unrelated predecessor could erase this obligation.
        if let Terminator::Call { func: callee, args, dest, span, callee_key, .. } =
            &block.terminator
        {
            let call_tail = method_tail(callee);
            if matches!(call_tail, "pow" | "unchecked_add" | "unchecked_sub" | "unchecked_mul")
                && let Some(kind) = overflow_arith_call(callee)
                && let Some((body, op, lhs_ty, rhs_ty, width)) =
                    v2_overflow_call_body(func, kind, args, dest)
            {
                // Trust (arith ARM, 2026-07-31): seed the authenticated obligation from the
                // block-def-versioned body EXACTLY as the direct/checked BinaryOp Int path
                // does — `v2_arith_overflow_seed_record` records the atomic out-of-range core
                // and demotes the operand ranges + block-defs to ConjoinFactsLast wrappers.
                // `.0` is byte-identical to the previous `v2_formula_with_block_defs`, so the
                // emitted formula is UNCHANGED. Fail-closed to `None` for the Pow bodies
                // (`Bool(true)` / 2-conjunct `And`), which are the genuinely-unmodeled shapes.
                // The four arg/local/field/slice conjoins + every later wrapper are applied and
                // mirrored by the shared loop below (this VC's kind is `ArithmeticOverflow`).
                let (formula, rec_body, kept) = v2_formula_with_block_defs_at_point_recorded(
                    func,
                    block,
                    block.stmts.len(),
                    body,
                );
                // SPLIT AT THE KIND LEVEL — `Unchecked` and `Pow` share this mint
                // site and the identical out-of-range obligation, but they do NOT
                // share a runtime guard, and `VcKind::has_runtime_fallback` can only
                // tell them apart if the kind does.
                //
                // `pow` is an ordinary checked library op: it panics on overflow when
                // `-C overflow-checks` is on, so `ArithmeticOverflow`'s
                // `overflow_checks` answer is TRUE for it, exactly as for the direct
                // `BinaryOp` path. `unchecked_{add,sub,mul}` lower to LLVM
                // `add nsw`/`nuw` (rustc_codegen_ssa/src/mir/rvalue.rs) — no Assert,
                // no branch, nothing gated on `overflow_checks` at ANY value.
                // MEASURED (stage2, `--emit=llvm-ir`): with
                // `-Coverflow-checks=off -Cdebug-assertions=off`, `u32::unchecked_add`
                // is a lone `add nuw` while `a + b` keeps `panic_const_add_overflow`
                // under `-Coverflow-checks=on`; and with
                // `-Coverflow-checks=off -Zub-checks=yes` the unchecked call gains a
                // `precondition_check` that `a + b` does not. The knobs are
                // independent, so sharing the kind minted the wrong claim from the
                // wrong knob.
                //
                // Only the KIND is split. The formula, the recorded obligation seed,
                // and every downstream conjoin below are byte-identical, so nothing
                // that was dischargeable stops being dischargeable here.
                let vc_kind = match kind {
                    OverflowCall::Unchecked(_) => {
                        VcKind::UncheckedArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) }
                    }
                    OverflowCall::Pow => {
                        VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) }
                    }
                };
                block_vcs.push((
                    block.id,
                    VerificationCondition {
                        kind: vc_kind,
                        function: fn_sym,
                        location: span.clone(),
                        formula,
                        contract_metadata: None,
                        obligation: v2_arith_overflow_seed_record(rec_body, kept, width),
                    },
                ));
            }

            // 1c-fold. Iterator::sum / Iterator::product over an INTEGER accumulator:
            // the fold arithmetic lives inside the library impl (no caller-visible
            // BinaryOp), and it can overflow-panic (`(1..=n).product::<i32>()` for
            // n >= 13). `overflow_arith_call` deliberately skips it (a REFUTABLE VC
            // would false-FAIL an ordinary bounded `vec.sum()`), which left it a SILENT
            // false-accept — 0 obligations, vacuously "safe". Surface it as an
            // UnsupportedMir obligation instead (→ Unknown → runtime-checked in the
            // default lane, exactly like the `m[&k]` map-index backstop): HONESTLY
            // accounted and delegated to the runtime overflow check, never silently
            // verified and never false-FAILED. Gated to an INTEGER result type — a
            // float sum/product does not overflow-panic (it saturates to ±inf), so it
            // is left untouched.
            //
            // Trust (2026-09-25, F4): the recognizer never matched rustc's qualified
            // spelling, so NO integer sum/product was ever charged (see
            // `iterator_integer_fold_call`). It now fires, and the row is a CALLER-
            // VALUE overflow — the same property `a + b` owes — with two shapes:
            //
            //  * the source's item COUNT is bounded (`fold_source_bound`: a range,
            //    `take(n)`, `repeat_n`, through count-preserving/-reducing adaptors)
            //    AND its items lie in a modelled range: an `ArithmeticOverflow` row
            //    whose failure condition is
            //    `count >= 1 && (count * hi > MAX || count * lo < MIN)` for `sum`
            //    (every partial sum lies in `[min(0, count*lo), max(0, count*hi)]`),
            //    and `count >= 2 && (hi >= 2 || lo <= -2)` for `product` (a product
            //    of items in `[-1, 1]` stays there; anything wider is not modeled).
            //    A dominating guard or a `min` bound on the count therefore PROVES
            //    it, and an unguarded one is REFUTED — exactly like `a + b`;
            //  * the count is bounded but the items are NOT MODELLED (a `map`,
            //    `filter_map`, `map_while` or `scan` result; a repeated non-integer):
            //    the row is kept only for a CLOSED count of at most one, which no
            //    item can overflow. Otherwise it is the `iterator-fold-overflow`
            //    Unknown below. Trust (CL-FOLD-MAP-FORCED-1, 2026-10-11): the items
            //    used to default to the accumulator's full range in an ordinary
            //    refutable row, and with a constant count of 4 `4 * MAX > MAX` folds
            //    to true. `(0..4usize).map(|_| 1u32).sum::<u32>()` (it returns 4) was
            //    then REFUTED, its "counterexample" holding only the range's fields,
            //    and escalated to a "guaranteed Level 0 safety violation". An
            //    unmodelled value is "I do not know": Unknown, never a counterexample
            //    (the `UnmodeledCalleeReturn` rule, `havoc_decline.rs`). COST, recorded
            //    in DECISION_QUEUE: a SYMBOLIC count that a guard bounds at one
            //    (`if n <= 1 { (0..n).map(f).sum() }`) proved and is now Unknown;
            //  * the count is NOT established (a slice or any other collection, a
            //    user iterator): the `iterator-fold-overflow` UnsupportedMir row,
            //    which carries no runtime fallback, so the default lane refuses it.
            //    An existing collection bounds the count only by memory, and `n`
            //    items of `u32::MAX` overflow a `u32` from `n = 2`.
            //
            // The accumulator is the destination's integer type, or the payload of
            // an `Option`/`Result` destination (`Sum<Option<U>> for Option<T>` runs
            // `T`'s own fold inside `try_process`).
            if matches!(call_tail, "sum" | "product")
                && let Some(fold) = iterator_integer_fold_call(callee)
                && let Some(acc_ty) =
                    crate::place_ty_cow(func, dest).as_deref().and_then(fold_accumulator_int_ty)
            {
                let mut bound =
                    args.first().map(|it| fold_source_bound(func, it, 0)).unwrap_or_default();
                // Trust (2026-10-01): a source whose count `fold_source_bound` does not
                // establish may still have the loop lane's yield bound: an array's length
                // through `a.iter()` (and its length-non-increasing adapters), or
                // `isize::MAX` for a slice of a non-zero-sized element. Both bound how many
                // items ONE instance yields, and the fold consumes that instance (sweep A10).
                // Only with a known item range: with the items defaulted to the
                // accumulator's whole range a count this loose refutes correct programs,
                // where the `iterator-fold-overflow` row below reports them unsupported.
                // A `map` summary that bounds NEITHER side is no item model at all, so it
                // stays `items: None` and takes the CL-FOLD-MAP-FORCED-1 arm below.
                //
                // Trust (merge 2026-10-14): "bounds" means TIGHTER than the accumulator's
                // own range, and on every side the row reads: `hi` always, and `lo` too for
                // a signed accumulator (`count * lo < MIN`, `lo <= -2`). A side that is
                // open, or no tighter than the accumulator's own extreme, is the
                // defaulted item CL-FOLD-MAP-FORCED-1 refuses to refute on. Measured:
                // `(0..4u32).map(u32::from).sum::<u32>()` (it returns 6) reached this arm
                // with core's identity `From<u32> for u32` giving `[0, u32::MAX]` on both
                // sides (`lossless_from_mapper_items`), and the row was REFUTED with
                // `count = 2`. Such a fold is now the `iterator-fold-overflow` Unknown,
                // and a source-type range that is tighter (`map(u32::from)` over `u8`,
                // `|&x| x as u64` over `u32`) keeps its row exactly as before.
                //
                // The PRODUCT row models only items in `[-1, 1]` and charges anything
                // wider as an overflow, so a mapped item outside it would again be
                // refuted on an item the row does not model:
                // `(0..4usize).map(|_i| 2u32).product::<u32>()` (it returns 16) with the
                // closure's `[2, 2]` summary. A mapped product keeps its row only when
                // the summary puts every item in `[-1, 1]`.
                if bound.items.is_none()
                    && let Some((lo, hi)) = bound.partial_items
                {
                    let width = acc_ty.int_width().unwrap_or(64);
                    let signed = acc_ty.is_signed();
                    let min_f = crate::range::type_min_formula(width, signed);
                    let max_f = crate::range::type_max_formula(width, signed);
                    // `closed_formula_int_value` is `None` only for `u128::MAX`, which no
                    // `i128` side reaches, so every side is tighter there.
                    let hi = hi.filter(|&h| closed_formula_int_value(&max_f).is_none_or(|m| h < m));
                    let lo = lo.filter(|&l| closed_formula_int_value(&min_f).is_none_or(|m| l > m));
                    let modelled = match fold {
                        IteratorFold::Sum => hi.is_some() && (!signed || lo.is_some()),
                        IteratorFold::Product => {
                            hi.is_some_and(|h| h <= 1) && (!signed || lo.is_some_and(|l| l >= -1))
                        }
                    };
                    if modelled {
                        bound.items =
                            Some((lo.map_or(min_f, Formula::Int), hi.map_or(max_f, Formula::Int)));
                    }
                }
                if bound.count.is_none() && bound.items.is_some() {
                    bound.count = args
                        .first()
                        .and_then(|it| super::loop_bounds::iterated_source_yield_bound(func, it, 16))
                        .map(Formula::Int);
                }
                let unmodelled = |detail: &str| {
                    (
                        block.id,
                        VerificationCondition {
                            kind: VcKind::UnsupportedMir {
                                kind: "iterator-fold-overflow".into(),
                                detail: detail.into(),
                            },
                            function: fn_sym,
                            location: span.clone(),
                            formula: Formula::Bool(true),
                            contract_metadata: None,
                            obligation: None,
                        },
                    )
                };
                match bound.count {
                    None => block_vcs.push(unmodelled(
                        "Iterator::sum/product accumulates inside the library impl and can \
                         overflow-panic, and the number of items its source yields is not \
                         bounded (a collection bounds it only by memory; two items of the \
                         type's maximum already overflow) — refused unless the source is a \
                         range, `take(n)` or `repeat_n` whose count a guard bounds",
                    )),
                    // CL-FOLD-MAP-FORCED-1: a bounded count over UNMODELLED items. Only a
                    // closed count of at most one keeps the row (one item cannot overflow
                    // a sum, and a product of one item is that item); anything else is
                    // Unknown, never a refutation on a defaulted item.
                    Some(count)
                        if bound.items.is_none()
                            && !closed_formula_int_value(&count).is_some_and(|c| c <= 1) =>
                    {
                        block_vcs.push(unmodelled(
                            "Iterator::sum/product accumulates inside the library impl and can \
                             overflow-panic; its source yields a bounded number of items, but \
                             their values are not modelled (a `map`, `filter_map`, `map_while` \
                             or `scan` result, or a repeated non-integer), so whether they \
                             overflow is unknown — refused, never refuted on an assumed \
                             maximal item",
                        ));
                    }
                    Some(count) => {
                        let width = acc_ty.int_width().unwrap_or(64);
                        let signed = acc_ty.is_signed();
                        let max_f = crate::range::type_max_formula(width, signed);
                        let min_f = crate::range::type_min_formula(width, signed);
                        // Reached with `items: None` only for a closed count of at most
                        // one (the arm above), where the item range cannot matter.
                        let (lo, hi) =
                            bound.items.unwrap_or_else(|| (min_f.clone(), max_f.clone()));
                        let at_least = |f: Formula, k: i128| {
                            Formula::Ge(Box::new(f), Box::new(Formula::Int(k)))
                        };
                        // Trust (2026-09-30): `count` is an UPPER bound in general
                        // (`take(1000)` yields at most 1000) and the item range may be the
                        // type's whole range by default, so a ground `count`/`hi` pair
                        // folded to a forced-true formula and the row was escalated as a
                        // "guaranteed" violation of a correct program
                        // (`v.iter().take(1000).map(|&b| b as u64).sum()`, sweep `r33`),
                        // with an empty counterexample. Range over every count up to the
                        // bound instead: the overflow condition is monotone in the count,
                        // so satisfiability is unchanged, and the formula no longer folds.
                        let bound_count = count;
                        let count =
                            Formula::Var(format!("__trust_fold_count_{}", block.id.0), Sort::Int);
                        let within_bound =
                            Formula::Le(Box::new(count.clone()), Box::new(bound_count));
                        // LINEAR on purpose: `count * hi` with both symbolic is a
                        // nonlinear product the in-process solver answers `Unknown`,
                        // and an `Unknown` overflow row is reported runtime-checked —
                        // measured, `(a..b).sum::<u64>()` built exit 0 that way. See
                        // `fold_product_may_leave_range`.
                        let mut exceeds =
                            vec![fold_product_may_leave_range(&count, &hi, width, signed, true)];
                        if signed {
                            exceeds.push(fold_product_may_leave_range(
                                &count, &lo, width, signed, false,
                            ));
                        }
                        let (op, body) = match fold {
                            IteratorFold::Sum => (
                                BinOp::Add,
                                Formula::And(vec![
                                    within_bound,
                                    at_least(count.clone(), 1),
                                    Formula::Or(exceeds),
                                ]),
                            ),
                            IteratorFold::Product => (
                                BinOp::Mul,
                                Formula::And(vec![
                                    within_bound,
                                    at_least(count, 2),
                                    Formula::Or(vec![
                                        at_least(hi, 2),
                                        Formula::Le(Box::new(lo), Box::new(Formula::Int(-2))),
                                    ]),
                                ]),
                            ),
                        };
                        let formula = v2_formula_with_block_defs_at_point(
                            func,
                            block,
                            block.stmts.len(),
                            body,
                        );
                        block_vcs.push((
                            block.id,
                            VerificationCondition {
                                kind: VcKind::ArithmeticOverflow {
                                    op,
                                    operand_tys: (acc_ty.clone(), acc_ty),
                                },
                                function: fn_sym,
                                location: span.clone(),
                                formula,
                                contract_metadata: None,
                                obligation: None,
                            },
                        ));
                    }
                }
            }

            // 1c-repeat. `str::repeat(n)` — sibling of the sum/product fold: the result
            // capacity `s.len() * n` is computed INSIDE the library impl and
            // overflow-panics ("capacity overflow") for large `n`, with no
            // caller-visible BinaryOp, so it was SILENTLY accepted (0 obligations).
            // Surface the same UnsupportedMir obligation (→ Unknown → runtime-checked)
            // as the iterator fold, per the default lane's disclosed runtime-checked demotion.
            // Gated to the `str` inherent impl (`<impl str>::repeat`) so `slice`/`Vec::
            // repeat` — which already mint a runtime-checked obligation via the
            // bulk-alloc capacity path — are NOT double-counted or regressed.
            if call_tail == "repeat" && str_repeat_capacity_overflow_call(callee) {
                block_vcs.push((
                    block.id,
                    VerificationCondition {
                        kind: VcKind::UnsupportedMir {
                            kind: "str-repeat-capacity-overflow".into(),
                            detail: "str::repeat computes its result capacity (len * n) \
                                     inside the library impl and can overflow-panic \
                                     (\"capacity overflow\"); not statically modeled — \
                                     reported Unknown (runtime-checked), never silently \
                                     verified"
                                .into(),
                        },
                        function: fn_sym,
                        location: span.clone(),
                        formula: Formula::Bool(true),
                        contract_metadata: None,
                        obligation: None,
                    },
                ));
            }

            // 1d. Division/remainder-by-zero for a dynamic divisor hidden INSIDE a
            // library Call that produces no caller-visible `BinaryOp(Div|Rem)`:
            // `a.checked_div(b)` / `checked_rem` / `div_euclid` / `rem_euclid` (panic
            // / UB / `None` on a zero divisor) and `Iterator::step_by(n)` (panics when
            // `n == 0`). Without this the divisor obligation is never emitted and the
            // op is reported vacuously safe — a false PROVE for `a.div_euclid(b)` with
            // a runtime-zero `b`. Reuses the exact `v2_divisor_is_zero_formula` body +
            // const-nonzero skip the BinaryOp arms use, pushed keyed by `block.id` so
            // it inherits the SAME block-defs / path-guard / semantic-guard /
            // precondition machinery — a dominating `if b != 0 { … }` guard or
            // `#[requires(b != 0)]` PROVES it, an unguarded one FAILS. Float divisors
            // are skipped: integer division panics on zero while `f64::div_euclid(0.0)`
            // does not, so flagging a float here would false-FAIL ordinary code.
            if matches!(
                call_tail,
                "div_euclid"
                    | "div_ceil"
                    | "rem_euclid"
                    | "step_by"
                    | "wrapping_div"
                    | "overflowing_div"
                    | "saturating_div"
                    | "wrapping_div_euclid"
                    | "overflowing_div_euclid"
                    | "wrapping_rem"
                    | "overflowing_rem"
                    | "wrapping_rem_euclid"
                    | "overflowing_rem_euclid"
            ) && let Some((divisor_idx, kind)) = divzero_call(callee)
                && let Some(divisor) = args.get(divisor_idx)
                && !v2_is_float_operand(func, divisor)
                && !v2_divisor_is_nonzero_constant(divisor)
            {
                // Args are evaluated BEFORE the terminator, so there are no in-block
                // statement defs to take "before the statement" — use the same
                // whole-block-defs builder the 1c overflow-call recognizer uses.
                block_vcs.push((
                    block.id,
                    v2_build_divrem_vc_raw(
                        func,
                        block,
                        v2_divisor_is_zero_formula(func, divisor),
                        block.stmts.len(),
                        span,
                        kind,
                    ),
                ));
            }

            // 1d'. The signed `MIN / -1` overflow of a std `div_euclid`/`rem_euclid`
            // call (Trust, 2026-09-30): its other panic, which 1d's zero-divisor row does
            // not state. Same builder and guard machinery as 1d, so `if n > 0` proves it
            // and `if n != 0` alone refutes it at `(MIN, -1)`.
            if matches!(call_tail, "div_euclid" | "rem_euclid")
                && let Some((violation, kind)) = signed_euclid_overflow_call(func, callee, args)
            {
                block_vcs.push((
                    block.id,
                    v2_build_divrem_vc_raw(func, block, violation, block.stmts.len(), span, kind),
                ));
            }

            // 1e. Slice-method panics whose out-of-bounds / zero-size argument lowers
            // to a `Terminator::Call` carrying NO caller-visible `Projection::Index`,
            // so the rvalue-safety bounds path never sees them and the op is reported
            // vacuously safe — a false PROVE for `s.split_at(mid)` with `mid > len`,
            // `s.chunks(0)`, or `s.swap(i, j)` with an out-of-range index. The body is
            // the unguarded failure (`mid > len` / `n == 0` / `i >= len || j >= len`),
            // pushed keyed by `block.id` so it inherits the SAME block-defs / path-guard
            // / semantic-guard / precondition machinery — a dominating `if mid <= s.len()`
            // / `if n != 0` PROVES it, an unguarded one FAILS. Unrecognized slice methods
            // return `None` from the recognizer: NO fail-close, to keep drop-in Rust.
            if let Some(panic) = SliceMethodPanic::classify_with_tail(callee, call_tail)
                // Trust (str char-boundary soundness): the `::<__trust_str_index>` marker
                // `func_operand_name` appends to a `str` range-index callee — the Self
                // identity that survives `str`→`[u8]` erasure. The RangeIndex body uses it
                // to mint the UTF-8 char-boundary obligation for str receivers only.
                // W4 round 3 (2026-09-29): the SplitAt body needs the same identity for
                // `str::split_at`/`split_at_mut`, which carry no marker — see
                // `callee_is_str_split_at`.
                && let Some((violation, kind)) = (match panic {
                    // Trust (VEC-INSERT, 2026-09-25): a `Vec` index mutator reached inside
                    // its base's pre-mutation region gets the REAL index precondition over
                    // the region length (`vec_region`); anywhere else the fail-honest
                    // `UnsupportedMir` row below stands.
                    SliceMethodPanic::VecPanicMethod { .. } => {
                        vec_mutator_index_violation(func, block)
                            .map(|violation| (violation, VcKind::SliceBoundsCheck))
                    }
                    _ => None,
                })
                .or_else(|| {
                    slice_method_panic_body(
                        func,
                        &panic,
                        callee,
                        args,
                        callee.contains("__trust_str_index")
                            || callee_is_str_split_at(callee, callee_key.as_ref()),
                        block,
                    )
                })
            {
                // Args are evaluated BEFORE the terminator, so there are no in-block
                // statement defs to take "before the statement" — use the same
                // whole-block-defs builder the 1c/1d call recognizers use. Conjoin the
                // `0 <= len` lower bound for the `__slice_len` term the `split_at`/`swap`
                // bodies reference (a no-op for the `chunks(n)` zero-size form, which
                // carries no length term); the bound is unconditionally true and sound.
                //
                // `RangeIndex` is the exception: its bounds are ALREADY resolved to the
                // underlying param symbols by `resolve_range_bound_formula`, so it needs
                // NO block-defs — and `v2_formula_with_block_defs` would otherwise conjoin
                // the `Range { .. }` aggregate's field equalities (`_t.0 == b`, the `@0.0`
                // aggregate-construction twin), noise that makes the default-mode solver
                // return Unknown on an otherwise-trivial `guard ∧ b > len` contradiction.
                // Skipping them is sound (dropping true equalities only weakens the
                // discharge, never the violation). NOTE: the exclusive-range violation
                // stays a single `Or[start>end, end>len]` VC — splitting it into two
                // single-`Gt` VCs (which the default-mode solver discharges better) is
                // UNSOUND here because both carry the SAME (span, kind, location) and the
                // result accounting then SHARES one verdict across them (the provable
                // ordering VC masks an undischarged end-bound VC). So a correctly-guarded
                // exclusive `&s[a..b]` currently fails closed (sound, incomplete); the
                // single-`Gt` `RangeTo`/`RangeFrom` discharge precisely. Completeness for
                // the exclusive `Or` is a follow-up (needs distinct per-disjunct VC ids).
                // Trust (versioned-def tie for the #7c scalar `v[i]`): the skip above is
                // scoped to TRUE range indexing only — discriminated by the presence of a
                // panicking-range arg, the SAME `range_operand` test the RangeIndex arm
                // itself keys on. The owned-Vec SCALAR index rides the RangeIndex arm too
                // (no range arg) but builds its index with a bare `operand_to_formula`, so
                // it NEEDS the block-defs: the index operand is a copy local (`_9 = copy i`)
                // whose def `_9 == i#<version>` is the ONLY tie to the versioned loop var
                // the `i < v.len()` guard constrains. Without it, `_9` is a free var and
                // `while i < v.len() { v[i] }` on `&Vec` FALSE-REFUTES with `_9 = len`
                // (observed: `_9 = 1, i#s0_0_s5_0 = 0, v = 1`) while the slice twin —
                // whose Assert-path VC builder conjoins block-defs — proves. Conjoining
                // defs is DROP-ONLY-in-reverse (true path equalities, monotone): it can
                // discharge a spurious refutation but never hide a real OOB, whose
                // counterexample satisfies the defs too (gate: `while i <= v.len()` still
                // refutes).
                // Trust: 2026-09-16 (round A8) — the range-index arm now takes the
                // same-block LENGTH TIES and nothing else (`v2_formula_with_slice_len_ties`):
                // the obligation's length is the argument temp's own `__slice_len` name
                // whenever the root is not licensed for the canonical one, and the tie is
                // its only connection to the length a guard or a `min` fact bounds.
                // Trust: 2026-09-21 — this arm now RECORDS its obligation.
                //
                // It pushed `obligation: None`, and that row is the one a whole
                // investigation converged on: a bounds row with no `{body,
                // wrappers}` is outside the authenticated-obligation invariant
                // entirely, and it is what decides the verdict on the
                // `closure-slice-facts` false refutations while the recorded row
                // beside it PROVES.
                //
                // It could not record before, and correctly did not try. Both
                // builders below VERSION-RENAME the body, so a record seeded with
                // the original `violation` cannot reconstruct `formula`, and
                // `ob_record_conjoin_wrap` is fail-closed against that shape — an
                // unreplayable record is worse than an absent one. The `_recorded`
                // twins return `(formula, renamed_body, kept)` precisely so the
                // record can be seeded at the SAME point the formula was renamed
                // at, which is the versioning reconciliation this lane needed.
                // Trust (CONST-RANGE-INDEX-1, 2026-10-06): "is a range index" is the
                // arm's own answer (`range_index_range_operand`), so a constant range the
                // callee names takes the same builder as a typed one.
                let (base, body, kept) = if matches!(panic, SliceMethodPanic::RangeIndex)
                    && range_index_range_operand(func, callee, args).is_some()
                {
                    v2_formula_with_slice_len_ties_recorded(func, block, violation)
                } else {
                    v2_formula_with_block_defs_recorded(func, block, violation)
                };
                let (formula, wrapped) = conjoin_slice_len_bounds_step(func, base);
                let mut wrappers = Vec::new();
                if !kept.is_empty() {
                    wrappers.push(trust_types::ObligationWrapper::ConjoinFactsLast { facts: kept });
                }
                // The one conjoin applied AFTER the recorded pair, recorded the same
                // way every other post-hoc conjoin in this file is.
                if wrapped
                    && let Formula::And(children) = &formula
                    && children.len() >= 2
                {
                    let facts = children[..children.len() - 1].to_vec();
                    if !facts.is_empty() {
                        wrappers.push(trust_types::ObligationWrapper::ConjoinFactsLast { facts });
                    }
                }
                let vc = VerificationCondition {
                    kind,
                    function: fn_sym,
                    location: span.clone(),
                    formula,
                    contract_metadata: None,
                    obligation: Some(trust_types::ObligationRecord {
                        body,
                        wrappers,
                        subject: None,
                        width: None,
                    }),
                };
                block_vcs.push((block.id, vc));
            }

            // 1f. Trust (2026-09-25, std-numeric-family): std numeric methods that
            // panic on a caller-supplied argument VALUE inside the library —
            // `Ord::clamp`/`f64::clamp` bounds, `ilog*`/`isqrt` domains, a radix
            // outside `[2, 36]`, `next_power_of_two`/`next_multiple_of` overflow, the
            // signed `div_euclid`/`rem_euclid` `MIN / -1`, `Duration`/`Instant`
            // arithmetic. The caller's MIR has no `Assert` for any of them, and the
            // bundled member's internal check is reported, not failed, so the
            // argument was never charged (see `numeric_panic`). A precise row is
            // pushed keyed by `block.id` exactly like the 1d divisor row, so a
            // dominating guard PROVES it and an unguarded call is REFUTED; a
            // fail-closed `UnsupportedMir` row is pushed bare, like the 1c-fold row.
            // The same-type `strict_add/sub/mul` and by-value `Add::add`-style calls
            // ARE the `a op b` overflow, so they get the row the `BinaryOp` statement
            // arm builds for `a op b` — the same builder, at the call's destination
            // type (its bit-vector route is what refutes a product of two variables;
            // an LIA `Assertion` over `a * b` is answered `Unknown` and reported
            // runtime-checked, which let `i32::strict_mul` build rc=0).
            let numeric_callee =
                super::numeric_panic::NumericCallee::for_minting(callee, call_tail);
            if let Some(overflow) = numeric_callee.overflow_call(func, args) {
                match overflow {
                    super::numeric_panic::NumericOverflow::BinOp(op) => {
                        let operation_ty = crate::place_ty_cow(func, dest)
                            .filter(|ty| crate::fixed_width_integer_descriptor(ty).is_some())
                            .map(std::borrow::Cow::into_owned);
                        if let (Some(lhs), Some(rhs)) = (args.first(), args.get(1))
                            && let Some(vc) = v2_build_overflow_vc_for_operands_typed(
                                func,
                                block,
                                op,
                                lhs,
                                rhs,
                                span,
                                None,
                                operation_ty,
                            )
                        {
                            block_vcs.push((block.id, vc));
                        }
                    }
                    // `<iN as AddAssign>::add_assign(p, b)` (and Sub/Mul): the row the
                    // `BinaryOp` arm builds for `*p + b` — the operand the operator
                    // spelling `*p += b` reads — typed at `*p`'s own integer type (the
                    // call's destination is `()`). With both operands typed the builder
                    // answers `None` only through its signed-128 `Mul` suppression (a
                    // finite corner box that provably cannot overflow), which mints
                    // nothing exactly as for `a * b`; an operand it cannot type is
                    // refused here rather than silently accepted.
                    super::numeric_panic::NumericOverflow::AssignBinOp { op, lhs } => {
                        let operation_ty = crate::operand_ty_cow(func, &lhs)
                            .filter(|ty| crate::fixed_width_integer_descriptor(ty).is_some())
                            .map(std::borrow::Cow::into_owned);
                        let rhs =
                            args.get(1).filter(|rhs| crate::operand_ty_cow(func, rhs).is_some());
                        let typed = operation_ty.is_some() && rhs.is_some();
                        let vc = match rhs {
                            Some(rhs) if typed => v2_build_overflow_vc_for_operands_typed(
                                func,
                                block,
                                op,
                                &lhs,
                                rhs,
                                span,
                                None,
                                operation_ty,
                            ),
                            _ => None,
                        };
                        match vc {
                            Some(vc) => block_vcs.push((block.id, vc)),
                            None if typed => {}
                            None => block_vcs.push((
                                block.id,
                                unsupported_mir_vc(
                                    func,
                                    "int-assign-op-overflow-unmodeled".to_string(),
                                    format!(
                                        "bb{}: `{callee}`'s receiver or right operand is not a \
                                         typed integer place, so its overflow obligation cannot be \
                                         built — refused, never silently verified",
                                        block.id.0
                                    ),
                                    span.clone(),
                                ),
                            )),
                        }
                    }
                    // `strict_pow`: the 1c `pow` row, byte-for-byte.
                    super::numeric_panic::NumericOverflow::Pow => {
                        if let Some((body, op, lhs_ty, rhs_ty, width)) =
                            v2_overflow_call_body(func, OverflowCall::Pow, args, dest)
                        {
                            let (formula, rec_body, kept) =
                                v2_formula_with_block_defs_at_point_recorded(
                                    func,
                                    block,
                                    block.stmts.len(),
                                    body,
                                );
                            block_vcs.push((
                                block.id,
                                VerificationCondition {
                                    kind: VcKind::ArithmeticOverflow {
                                        op,
                                        operand_tys: (lhs_ty, rhs_ty),
                                    },
                                    function: fn_sym,
                                    location: span.clone(),
                                    formula,
                                    contract_metadata: None,
                                    obligation: v2_arith_overflow_seed_record(
                                        rec_body, kept, width,
                                    ),
                                },
                            ));
                        }
                    }
                }
            } else if let Some((violation, kind)) =
                numeric_callee.value_panic_row(func, args, dest)
            {
                if matches!(kind, VcKind::UnsupportedMir { .. }) {
                    block_vcs.push((
                        block.id,
                        VerificationCondition {
                            kind,
                            function: fn_sym,
                            location: span.clone(),
                            formula: violation,
                            contract_metadata: None,
                            obligation: None,
                        },
                    ));
                } else {
                    block_vcs.push((
                        block.id,
                        v2_build_divrem_vc_raw(
                            func,
                            block,
                            violation,
                            block.stmts.len(),
                            span,
                            kind,
                        ),
                    ));
                }
            }
        }

        // TINV step 7.5: the requested type-invariant rows of this terminator. A no-op
        // unless a `tinv_rows` request for THIS body is installed, so ordinary
        // generation is byte-identical.
        super::tinv_rows::push_tinv_terminator_rows(
            func,
            active_tinv_req.as_deref(),
            || &**sv_lazy.get_or_init(|| super::stmt_versions_for(func)),
            block,
            &mut block_vcs,
        );
        // Every row pushed so far for this block is a terminator/call row.
        pad_row_points(&mut row_points, block_vcs.len(), usize::MAX);
        let mut stmt_point = usize::MAX;
        for (stmt_index, stmt) in block.stmts.iter().enumerate() {
            // Every row the PREVIOUS iteration pushed reads at that iteration's
            // statement. Labelled on entry to the next iteration (and once after
            // the loop), so no `continue` / `break` in the arms below can leave a
            // row unlabelled.
            pad_row_points(&mut row_points, block_vcs.len(), stmt_point);
            stmt_point = stmt_index;
            // TINV step 7.5: the requested E/M rows at this statement (no-op without a
            // request), labelled with this statement's use point on the next pad.
            super::tinv_rows::push_tinv_statement_rows(
                func,
                active_tinv_req.as_deref(),
                || &**sv_lazy.get_or_init(|| super::stmt_versions_for(func)),
                block,
                stmt_index,
                &mut block_vcs,
            );
            // Per-STATEMENT poll (see the per-block poll above). A block-level
            // bound alone is too coarse: the pathological bodies are a single
            // enormous block, so an overrun inside one block's statement walk
            // would still spin unboundedly.
            if trust_types::verify_budget::budget_exhausted() {
                truncated = true;
                break;
            }
            let Statement::Assign { place, rvalue, span } = stmt else {
                continue;
            };
            match rvalue {
                Rvalue::BinaryOp(BinOp::Div, lhs, divisor) => {
                    let is_float =
                        v2_is_float_operand(func, lhs) || v2_is_float_operand(func, divisor);

                    // Trust (DESIGN_PHILOSOPHY §9 — defined behavior is not unsafe):
                    // IEEE-754 float division is TOTAL. `a / 0.0` is DEFINED —
                    // it yields ±inf (or NaN for `0.0 / 0.0`), never traps, never
                    // panics, never invokes UB (unlike integer `/ 0`, which
                    // aborts). inf/NaN are ordinary `f64` values. So there is no
                    // safety property to prove and no obligation to emit — exactly
                    // as an int→int `as` cast emits nothing (the canonical §9 case).
                    // Emitting a `FloatDivisionByZero` L0 refutation here rejected
                    // ubiquitous valid Rust (`fn mean(s: f64, n: f64) { s / n }`).
                    // Only INTEGER division (which genuinely traps on a zero
                    // divisor) keeps its obligation. Kept in sync with the
                    // cross-check reference generator (`reference_vcgen.rs`).
                    //
                    // Trust (exact-identity dedup, zero-divisor member): the same
                    // discipline the `Overflow(Div)` row below already applies. When
                    // the `DivisionByZero` assert is EXACTLY BOUND to this statement's
                    // divisor, the assert lane's row states the same proposition and
                    // remains the refutable one, while THIS row sits under the assert's
                    // `AssertHolds` path guard — its violation reduces to
                    // `divisor != 0 && divisor == 0`, UNSAT by construction, so it can
                    // only ever be `proved`. That vacuous row shipped in the transport
                    // as a `proved` `divzero` at the exact span of a genuinely-false
                    // division by zero. Suppress it; anything short of the exact cond
                    // binding keeps both rows (bare target identity is never
                    // suppression authority).
                    if !is_float
                        && !v2_divisor_is_nonzero_constant(divisor)
                        && !v2_divzero_assert_exactly_bound(
                            func,
                            BinOp::Div,
                            block.id,
                            stmt_index,
                            lhs,
                            divisor,
                        )
                    {
                        block_vcs.push((
                            block.id,
                            v2_build_divrem_vc_raw(
                                func,
                                block,
                                v2_divisor_is_zero_formula(func, divisor),
                                stmt_index,
                                span,
                                VcKind::DivisionByZero,
                            ),
                        ));
                    }

                    // Trust (exact-identity dedup): when an `Overflow(Div)` assert
                    // is EXACTLY BOUND to this statement's operands (the canonical
                    // `(rhs == -1) & (lhs == INT_MIN)` cond chain over structurally
                    // identical, rewrite-stable operands at this operation's true
                    // width), the assert lane's own row states the same proposition
                    // and remains the refutable one — this row would sit under the
                    // assert's `AssertHolds` path guard and discharge vacuously.
                    // Suppress the vacuous duplicate; anything short of the exact
                    // cond binding keeps both rows (bare target identity is never
                    // suppression authority).
                    if !is_float
                        && !v2_divrem_overflow_assert_exactly_bound(
                            func,
                            BinOp::Div,
                            block.id,
                            stmt_index,
                            lhs,
                            divisor,
                        )
                        && let Some(vc) = v2_build_signed_div_overflow_vc(
                            func,
                            block,
                            BinOp::Div,
                            lhs,
                            divisor,
                            span,
                            Some(stmt_index),
                        )
                    {
                        block_vcs.push((block.id, vc));
                    }

                    // Trust (float-residuals F1): float division is TOTAL (§9
                    // above — no DivisionByZero obligation), but it CAN create
                    // ±inf from FINITE operands (`1.0 / 1e-320`, `x / 0.0`) —
                    // the same numeric-overflow class as Add/Sub/Mul. Emit the
                    // FloatOverflowToInfinity witness obligation; the interval
                    // lane discharges it when the numerator is bounded and the
                    // divisor has a proven magnitude floor (a sign-definite
                    // contract interval, or a dominating `d > 1e-20`-style
                    // guard). Rem stays obligation-free: fmod of finite
                    // operands cannot produce ±inf (a NaN from `x % 0.0` is
                    // not an infinity).
                    if is_float {
                        let context =
                            V2FloatOverflowContext { func, block, span, stmt_index, summaries };
                        if let Some(vc) =
                            v2_build_float_overflow_vc(context, BinOp::Div, lhs, divisor)
                        {
                            block_vcs.push((block.id, vc));
                        }
                    }
                }
                Rvalue::BinaryOp(BinOp::Rem, lhs, divisor)
                    if !v2_is_float_operand(func, lhs) && !v2_is_float_operand(func, divisor) =>
                {
                    // Trust (exact-identity dedup, zero-divisor member): same
                    // discipline as the Div arm above — suppressed only under the
                    // exact `RemainderByZero` assert cond binding, never bare target
                    // identity. See `v2_divzero_assert_exactly_bound`.
                    if !v2_divisor_is_nonzero_constant(divisor)
                        && !v2_divzero_assert_exactly_bound(
                            func,
                            BinOp::Rem,
                            block.id,
                            stmt_index,
                            lhs,
                            divisor,
                        )
                    {
                        block_vcs.push((
                            block.id,
                            v2_build_divrem_vc_raw(
                                func,
                                block,
                                v2_divisor_is_zero_formula(func, divisor),
                                stmt_index,
                                span,
                                VcKind::RemainderByZero,
                            ),
                        ));
                    }

                    // Trust (exact-identity dedup): same discipline as the Div arm
                    // above — suppressed only under the exact `Overflow(Rem)` assert
                    // cond binding, never bare target identity.
                    if !v2_divrem_overflow_assert_exactly_bound(
                        func,
                        BinOp::Rem,
                        block.id,
                        stmt_index,
                        lhs,
                        divisor,
                    ) && let Some(vc) = v2_build_signed_div_overflow_vc(
                        func,
                        block,
                        BinOp::Rem,
                        lhs,
                        divisor,
                        span,
                        Some(stmt_index),
                    ) {
                        block_vcs.push((block.id, vc));
                    }
                }
                Rvalue::BinaryOp(op @ (BinOp::Shl | BinOp::Shr), lhs, rhs) => {
                    // Trust (exact-identity dedup, SHIFT member): the same
                    // discipline the `DivisionByZero` and `Overflow(Div|Rem)` rows
                    // above already apply, at the shift assert's own polarity
                    // (`expected: true`). When the `Overflow(Shl|Shr)` assert is
                    // EXACTLY BOUND to this statement, the assert lane's row is
                    // built by THIS SAME constructor from THIS SAME `(op, lhs,
                    // rhs)` — it states the identical proposition and remains the
                    // refutable one, while THIS row sits under the assert's
                    // `AssertHolds` path guard: its violation reduces to
                    // `amount < BITS && amount >= BITS`, UNSAT by construction, so
                    // it can only ever be `proved`. That vacuous row shipped in the
                    // transport as a `proved` `shift:left` at the exact span of a
                    // genuinely-false shift overflow. Suppress it; anything short of
                    // the exact cond binding keeps both rows (bare target identity
                    // is never suppression authority).
                    if !v2_shift_assert_exactly_bound(func, *op, block.id, stmt_index, lhs, rhs)
                        && let Some(vc) = v2_build_shift_overflow_vc(
                            func,
                            block,
                            *op,
                            lhs,
                            rhs,
                            span,
                            V2ShiftSite::Statement(stmt_index),
                        )
                    {
                        block_vcs.push((block.id, vc));
                    }
                }
                // Float or direct integer Add | Sub | Mul: evaluate the float-operand
                // check once so integer arithmetic statements do not re-query operand_ty_cow.
                Rvalue::BinaryOp(op @ (BinOp::Add | BinOp::Sub | BinOp::Mul), lhs, rhs) => {
                    if v2_is_float_operand(func, lhs) || v2_is_float_operand(func, rhs) {
                        let context =
                            V2FloatOverflowContext { func, block, span, stmt_index, summaries };
                        if let Some(vc) = v2_build_float_overflow_vc(context, *op, lhs, rhs) {
                            block_vcs.push((block.id, vc));
                        }
                    } else if !crate::is_certified_modular_arith(&func.def_path, span, *op) {
                        // Trust (width-soundness): the assignment DESTINATION's
                        // validated integer type is the operation-width authority,
                        // exactly as in the UncheckedBinaryOp arm below
                        // (`validate_binary_assignment_types` pins both operands to
                        // it). Without it, a public body whose operands are BOTH
                        // widthless signed constants (`_1: i8 = Add(100, 100)` —
                        // admitted, each literal fits i8) lets `int_op_type`
                        // fabricate i64 and the VC proves `200 fits i64` while the
                        // i8 operation overflows at runtime — a false PROVE. A
                        // destination without a fixed-width descriptor falls back
                        // to operand inference (today's behavior; unreachable on
                        // the validated path).
                        let operation_ty = crate::place_ty_cow(func, place)
                            .filter(|ty| crate::fixed_width_integer_descriptor(ty).is_some())
                            .map(std::borrow::Cow::into_owned);
                        if let Some(vc) = v2_build_overflow_vc_for_operands_typed(
                            func,
                            block,
                            *op,
                            lhs,
                            rhs,
                            span,
                            Some(stmt_index),
                            operation_ty,
                        ) {
                            block_vcs.push((block.id, vc));
                        }
                    }
                }
                // A modular-arithmetic certificate is authority only for the
                // plain `BinaryOp` spelling produced by lowered `wrapping_*`.
                // It must never silence an `*Unchecked` operation: overflow of
                // this preserved MIR spelling is UB, even at the same span and
                // with the same operator as a certified wrapping statement.
                Rvalue::UncheckedBinaryOp(
                    op @ (BinOp::Add | BinOp::Sub | BinOp::Mul),
                    lhs,
                    rhs,
                ) if !v2_is_float_operand(func, lhs) && !v2_is_float_operand(func, rhs) => {
                    if let Some(operation_ty) = crate::place_ty_cow(func, place)
                        && let Some(mut vc) = v2_build_unchecked_overflow_vc_for_operands(
                            func,
                            block,
                            *op,
                            lhs,
                            rhs,
                            span,
                            Some(stmt_index),
                            operation_ty.into_owned(),
                        )
                    {
                        // The SECOND route to `unchecked_{add,sub,mul}` — and the
                        // one an optimized build actually takes. `LowerIntrinsics`
                        // rewrites the intrinsic CALL into this preserved MIR
                        // spelling (see `Rvalue::UncheckedBinaryOp` in
                        // trust-types/model.rs), so the `Terminator::Call` split
                        // above covers only the pre-`-O` shape. Both routes must
                        // answer the same, or `-O` re-opens the hole the other
                        // closed.
                        //
                        // The builder is shared with the PLAIN `Rvalue::BinaryOp`
                        // path (`v2_build_overflow_vc_for_operands_impl`, in
                        // overflow_vc.rs) and correctly mints `ArithmeticOverflow`
                        // for it, so the kind is corrected HERE — at the only
                        // call site that knows the operand carrier was the
                        // UB-on-overflow one. Retag only that exact kind: the
                        // builder also returns `UnsupportedMir` rows (the
                        // OpaqueScalar refusal), which must pass through
                        // untouched. Formula, location, and the authenticated
                        // obligation seed are preserved byte-for-byte, so this
                        // costs no dischargeability.
                        if let VcKind::ArithmeticOverflow { op, operand_tys } = vc.kind {
                            vc.kind = VcKind::UncheckedArithmeticOverflow { op, operand_tys };
                        }
                        block_vcs.push((block.id, vc));
                    }
                }
                Rvalue::Cast(operand, to_ty) => {
                    if let Some(vc) =
                        v2_build_cast_vc(func, block, operand, to_ty, span, stmt_index)
                    {
                        block_vcs.push((block.id, vc));
                    }
                }
                Rvalue::UnaryOp(trust_types::UnOp::Neg, operand) => {
                    // Trust (exact-identity dedup, NEGATION member): the same
                    // discipline the `DivisionByZero`, `Overflow(Div|Rem)` and
                    // `Overflow(Shl|Shr)` rows already apply, at the div/rem
                    // polarity (`expected: false`). When the `OverflowNeg` assert
                    // is EXACTLY BOUND to this statement, the assert lane's row
                    // states the identical proposition (its cond IS
                    // `operand == INT_MIN`) and remains the refutable one, while
                    // THIS row sits under the assert's `AssertHolds` path guard:
                    // its violation reduces to
                    // `operand != INT_MIN && operand == INT_MIN`, UNSAT by
                    // construction, so it can only ever be `proved`. That vacuous
                    // row shipped in the transport as a `certified` `negation` at
                    // the exact span of a genuinely-false negation overflow — the
                    // sole positive claim in the canary's census. Suppress it;
                    // anything short of the exact cond binding keeps both rows
                    // (bare target identity is never suppression authority).
                    if !v2_negation_assert_exactly_bound(func, block, operand)
                        && let Some(vc) =
                            v2_build_negation_raw_vc(func, block, operand, span, stmt_index)
                    {
                        block_vcs.push((block.id, vc));
                    }
                }
                _ => {}
            }
        }
        pad_row_points(&mut row_points, block_vcs.len(), stmt_point);
    }
    pad_row_points(&mut row_points, block_vcs.len(), usize::MAX);
    assert_eq!(
        row_points.len(),
        block_vcs.len(),
        "every generated row must carry its use point before decoration"
    );

    // THE COLLAPSE INVARIANT, capture step. Classify every row NOW, while
    // `vc.formula` is still the row's OWN violation condition: from the next
    // statement on it accumulates value facts, length-guard facts, global
    // invariants and preconditions, all of them satisfiable FACTS rather than
    // content, and any of them would mask "this row says nothing on its own".
    // The classification is POSITIONAL: nothing between here and the enforcement
    // step pushes to, removes from, or reorders `block_vcs` — every pass in
    // between iterates `&mut block_vcs` in place.
    //
    // That premise is CHECKED, not assumed, and it is checked because the
    // failure is silent and points the wrong way. A bare `zip` FAILS OPEN: if a
    // later edit pushes a row between here and the enforcement step, `zip` stops
    // at the shorter side and every row past that point never reaches the splice
    // that conjoins its path guards. A violation formula with no path condition
    // on it accuses code on paths that cannot run — a FALSE REFUTATION, the
    // worst defect this file can ship, arrived at with no diagnostic. An index
    // would at least panic on growth; it would still say nothing about a
    // reordering. So each flag carries the `BlockId` it was captured for and the
    // enforcement step checks BOTH the length and the per-position identity
    // before it trusts a single flag.
    if !block_vcs.is_empty() {
    let content_free: Vec<(BlockId, bool)> =
        block_vcs.iter().map(|(id, vc)| (*id, v2_violation_is_content_free(&vc.formula))).collect();

    // Conjoin predecessor definitions before guards so successor-block VCs
    // retain the boolean/int locals that made the path reachable.
    let path_def_lazy: std::cell::OnceCell<std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>> =
        std::cell::OnceCell::new();
    let mut terminal_live_cache: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    // PERF-COMPILER-VCGEN-802: `v2_live_path_defs_at_point` is a pure function of
    // `(func, block, path_defs[block], point)`, and the rows of ONE statement are
    // pushed consecutively (a `Div` mints its zero-divisor AND its signed-overflow
    // row at the same use point). `next_shares_point[i]` says row `i + 1` has row
    // `i`'s `(block, point)`, so the per-statement live set is computed once and
    // cloned only for a row that really has a same-point successor; a lone row
    // still moves its set straight into its conjunction, as before.
    let next_shares_point: Vec<bool> = (0..block_vcs.len())
        .map(|i| {
            i + 1 < block_vcs.len()
                && block_vcs[i].0 == block_vcs[i + 1].0
                && row_points[i] == row_points[i + 1]
        })
        .collect();
    let mut point_live_carry: Option<(BlockId, usize, Vec<Formula>)> = None;
    for (row_index, ((block_id, vc), point)) in
        block_vcs.iter_mut().zip(row_points.iter().copied()).enumerate()
    {
        // BUDGET POLL, per ROW. `v2_live_path_defs` re-walks the whole block
        // against the whole incoming fact list, so ONE row is its own overrun
        // channel and a poll anywhere outside this loop could not interrupt it;
        // this pass had no poll at all, so `-Ztrust-verify-function-budget-{ms,
        // steps}` did not bound it. Degrading by `break` leaves the remaining
        // rows WITHOUT their path-def facts, which is fail-closed: this loop
        // only ever CONJOINS facts onto a violation formula, and a row carrying
        // fewer hypotheses can move PROVE -> FAIL, never FAIL -> PROVE.
        //
        // Nor does a half-decorated row reach a consumer. `budget_exhausted`
        // LATCHES (its step counter saturates at zero and a passed deadline
        // never un-passes), so the poll in the type-range loop below is reached
        // and sets `truncated`, which makes the overflow-check origin inventory
        // give no join table; and the caller's post-generation checkpoint
        // (`preprocessing_budget_exceeded`, "VC generation") discards this
        // partial inventory outright — a located hard error in strict/certify/
        // memory-safe, one synthetic `Unknown` row in advisory.
        if trust_types::verify_budget::budget_exhausted() {
            // Set the flag AT THE BREAK, not downstream. A step-budget trip
            // latches (the counter saturates at zero) but a WALL-CLOCK trip does
            // NOT: the clock is only consulted every `WALL_POLL_INTERVAL` (4096)
            // charged steps, so up to 4096 later polls answer `false` again. So a
            // later loop's `truncated = true` cannot be relied on to carry this
            // trip, and the origin inventory (`RowOrigins::from_walk`) gates on
            // `truncated` — a tail of rows missing their facts, reported as a COMPLETE
            // enumeration, is the FAIL->PROVE direction (a twin pair stops
            // colliding, so a live overflow check can be elided on the other
            // twin's proof). Every break out of this decoration phase therefore
            // carries the flag itself.
            truncated = true;
            break;
        }
        if v2_is_unsupported_mir_vc(vc) {
            continue;
        }
        let path_definition_map =
            path_def_lazy.get_or_init(|| super::path_definition_map_for(func));
        if let Some(path_defs) = path_definition_map.get(block_id)
            && !path_defs.is_empty()
        {
            // A per-statement row keeps the entry facts its own read still sees
            // (see `v2_live_path_defs_at_point`); a terminator row (`point` =
            // `usize::MAX`) takes the whole-block kill, byte-identical to before.
            let block = &func.body.blocks[block_id.0];
            if point >= block.stmts.len() {
                let live = terminal_live_cache
                    .entry(*block_id)
                    .or_insert_with(|| v2_live_path_defs_at_point(func, block, path_defs, point));
                if !live.is_empty() {
                    ob_record_conjoin(vc, live);
                    let mut conjuncts = Vec::with_capacity(live.len() + 1);
                    conjuncts.extend_from_slice(live);
                    conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                    vc.formula = Formula::And(conjuncts);
                }
            } else {
                let carried = point_live_carry
                    .take()
                    .filter(|(carry_block, carry_point, _)| {
                        carry_block == block_id && *carry_point == point
                    })
                    .map(|(_, _, live)| live);
                let live = carried
                    .unwrap_or_else(|| v2_live_path_defs_at_point(func, block, path_defs, point));
                if next_shares_point[row_index] {
                    point_live_carry = Some((*block_id, point, live.clone()));
                }
                if !live.is_empty() {
                    ob_record_conjoin(vc, &live);
                    let mut conjuncts = live;
                    conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                    vc.formula = Formula::And(conjuncts);
                }
            }
        }
    }

    // Trust S2c (exemption): path guards + semantic assert-passed guards are
    // conjoined AFTER the version rename (moved below), EXEMPT from it, so a guard's
    // bare ENTRY-param read stays name-disjoint from a reassigned body read.

    if block_vcs.iter().any(|(_, vc)| !v2_is_unsupported_mir_vc(vc)) {
        let tp = super::terminator_presence_for(func);
        let has_adapter_premises =
            !crate::adapter_yield_premises_for(&func.def_path).is_empty();

        // Conjoin range-iterator yield facts so `for i in start..end { a[i] }`
        // proves: the loop variable `i` (a `Range::next` Some-payload) provably
        // satisfies `start <= i < end`, which discharges the `a[i]` bounds
        // obligation. Computed independently of the BFS guard map, so loop-join
        // weakening cannot drop it. See `build_range_yield_guard_map`.
        if tp.has_iterator_next_call || has_adapter_premises {
            let range_yield_guards = super::range_yield_guards_for(func);
            if !range_yield_guards.is_empty() {
                for (block_id, vc) in &mut block_vcs {
                    if v2_is_unsupported_mir_vc(vc) {
                        continue;
                    }
                    if let Some(facts) = range_yield_guards.get(block_id)
                        && !facts.is_empty()
                    {
                        ob_record_conjoin(vc, facts);
                        let mut conjuncts = Vec::with_capacity(facts.len() + 1);
                        conjuncts.extend_from_slice(facts);
                        conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                        vc.formula = Formula::And(conjuncts);
                    }
                }
            }
        }

        // W4 STR-OFFSET (2026-09-25): conjoin the str-search payload facts —
        // `0 <= i`, `i + m <= len(s)`, `len(s) <= isize::MAX` for `i` bound out of an
        // authenticated `s.find(p)`/`s.rfind(p)` result — at the blocks that read
        // `i`, so arithmetic on the offset (`i + 1` in `&s[i + 1..]`) discharges its
        // overflow row. Same attachment discipline as the range-yield facts above.
        // See `str_offset::build_str_search_payload_fact_map`.
        if tp.has_str_search_item_call {
            let str_search_payload_facts = build_str_search_payload_fact_map(func);
            if !str_search_payload_facts.is_empty() {
                for (block_id, vc) in &mut block_vcs {
                    if v2_is_unsupported_mir_vc(vc) {
                        continue;
                    }
                    if let Some(facts) = str_search_payload_facts.get(block_id)
                        && !facts.is_empty()
                    {
                        ob_record_conjoin(vc, facts);
                        let mut conjuncts = Vec::with_capacity(facts.len() + 1);
                        conjuncts.extend_from_slice(facts);
                        conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                        vc.formula = Formula::And(conjuncts);
                    }
                }
            }
        }

        // Conjoin converging two-pointer facts so `while lo < hi { hi -= 1; … s[lo] …;
        // lo += 1 }` proves the `s[lo]` side (`s[hi]` is handled by the downward
        // induction fact): `lo < hi <= s.len()` at the lo-stable body blocks. See
        // `build_converging_pointer_facts`.
        if tp.has_switch_int {
            let converging_facts = build_converging_pointer_facts(func);
            if !converging_facts.is_empty() {
                for (block_id, vc) in &mut block_vcs {
                    if v2_is_unsupported_mir_vc(vc) {
                        continue;
                    }
                    if let Some(facts) = converging_facts.get(block_id)
                        && !facts.is_empty()
                    {
                        ob_record_conjoin(vc, facts);
                        let mut conjuncts = Vec::with_capacity(facts.len() + 1);
                        conjuncts.extend_from_slice(facts);
                        conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                        vc.formula = Formula::And(conjuncts);
                    }
                }
            }

            // Trust (countdown-loop piece): conjoin the countdown PRE-VALUE facts at the
            // decrement blocks — `offset >= LEN - c*(T-1)` directly contradicts the
            // CheckedSub underflow violation, which is expressed on the pre-value
            // version (the global result-temp form does not reach it). Same consumption
            // discipline as the converging two-pointer facts above; the builder emits a
            // block's fact only when the block has no cursor store, so the bare name
            // versions to the block-entry value. See `build_countdown_preval_facts`.
            let countdown_facts = super::countdown_facts_for(func);
            let countdown_preval_facts = &countdown_facts.per_block;
            if !countdown_preval_facts.is_empty() {
                for (block_id, vc) in &mut block_vcs {
                    if v2_is_unsupported_mir_vc(vc) {
                        continue;
                    }
                    if let Some(facts) = countdown_preval_facts.get(block_id)
                        && !facts.is_empty()
                    {
                        ob_record_conjoin(vc, facts);
                        let mut conjuncts = Vec::with_capacity(facts.len() + 1);
                        conjuncts.extend_from_slice(facts);
                        conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                        vc.formula = Formula::And(conjuncts);
                    }
                }
            }
        }

        // Conjoin enumerate index yield facts so `for (i, _) in s.iter().enumerate()
        // { … s[i] … }` proves: the index `i` (the enumerate count) provably satisfies
        // `0 <= i < s.len()`. Independent of the BFS guard map. See
        // `build_enumerate_yield_guard_map`.
        if tp.has_iterator_next_call {
            let enumerate_yield_guards = super::enumerate_yield_guards_for(func);
            if !enumerate_yield_guards.is_empty() {
                for (block_id, vc) in &mut block_vcs {
                    if v2_is_unsupported_mir_vc(vc) {
                        continue;
                    }
                    if let Some(facts) = enumerate_yield_guards.get(block_id)
                        && !facts.is_empty()
                    {
                        ob_record_conjoin(vc, facts);
                        let mut conjuncts = Vec::with_capacity(facts.len() + 1);
                        conjuncts.extend_from_slice(facts);
                        conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                        vc.formula = Formula::And(conjuncts);
                    }
                }
            }
        }

        // Conjoin slice-chunking yield facts so `for w in s.windows(n) { w[k] }` /
        // `for c in s.chunks(n) { c[k] }` prove: the yielded sub-slice's modeled
        // length is `== n` (windows) / `in [1, n]` (chunks). See
        // `build_slice_iter_yield_guard_map`.
        if tp.has_iterator_next_call || has_adapter_premises {
            let slice_iter_yield_guards = super::slice_iter_yield_guards_for(func);
            if !slice_iter_yield_guards.is_empty() {
                for (block_id, vc) in &mut block_vcs {
                    if v2_is_unsupported_mir_vc(vc) {
                        continue;
                    }
                    if let Some(facts) = slice_iter_yield_guards.get(block_id)
                        && !facts.is_empty()
                    {
                        ob_record_conjoin(vc, facts);
                        let mut conjuncts = Vec::with_capacity(facts.len() + 1);
                        conjuncts.extend_from_slice(facts);
                        conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                        vc.formula = Formula::And(conjuncts);
                    }
                }
            }
        }

        // Conjoin `position` index facts so `if let Some(i) = v.iter().position(f) { v[i] }`
        // proves: the index is below the length of the slice it searched. See
        // `build_position_yield_guard_map`.
        // `count` result facts, the same way: `v.len() - v.iter().filter(p).count()` needs
        // the count below the length. See `build_count_bound_guard_map`.
        // `str::find` / `str::rfind` payload facts, the same way: the match start is at
        // most the string's length. See `build_str_find_guard_map`.
        if tp.has_call {
            let mut owned_guards = if tp.has_position_call {
                build_position_yield_guard_map(func)
            } else {
                FxHashMap::default()
            };
            if tp.has_count_call {
                let count_guards = build_count_bound_guard_map(func);
                if !count_guards.is_empty() {
                    if owned_guards.is_empty() {
                        owned_guards = count_guards;
                    } else {
                        for (block_id, facts) in count_guards {
                            owned_guards.entry(block_id).or_default().extend(facts);
                        }
                    }
                }
            }
            let primitive_decimal_guards = super::primitive_decimal_len_guards_for(func);
            let mut position_yield_guards: std::borrow::Cow<'_, FxHashMap<BlockId, Vec<Formula>>> =
                if owned_guards.is_empty() {
                    std::borrow::Cow::Borrowed(primitive_decimal_guards.as_ref())
                } else {
                    for (&block_id, facts) in primitive_decimal_guards.iter() {
                        owned_guards.entry(block_id).or_default().extend(facts.iter().cloned());
                    }
                    std::borrow::Cow::Owned(owned_guards)
                };
            if tp.has_str_find_call {
                let str_find_guards = build_str_find_guard_map(func);
                if !str_find_guards.is_empty() {
                    if position_yield_guards.is_empty() {
                        position_yield_guards = std::borrow::Cow::Owned(str_find_guards);
                    } else {
                        let map = position_yield_guards.to_mut();
                        for (block_id, facts) in str_find_guards {
                            map.entry(block_id).or_default().extend(facts);
                        }
                    }
                }
            }
            // Payload-interval facts on a `Some`/`Ok` payload of a summarized local call,
            // directly or through `?`. See `build_payload_interval_guard_map`.
            if tp.has_bare_dest_call {
                let payload_guards = super::iterator_yield::build_payload_interval_guard_map(func);
                if !payload_guards.is_empty() {
                    if position_yield_guards.is_empty() {
                        position_yield_guards = std::borrow::Cow::Owned(payload_guards);
                    } else {
                        let map = position_yield_guards.to_mut();
                        for (block_id, facts) in payload_guards {
                            map.entry(block_id).or_default().extend(facts);
                        }
                    }
                }
            }
            if !position_yield_guards.is_empty() {
                for (block_id, vc) in &mut block_vcs {
                    if v2_is_unsupported_mir_vc(vc) {
                        continue;
                    }
                    if let Some(facts) = position_yield_guards.get(block_id)
                        && !facts.is_empty()
                    {
                        ob_record_conjoin(vc, facts);
                        let mut conjuncts = Vec::with_capacity(facts.len() + 1);
                        conjuncts.extend_from_slice(facts);
                        conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                        vc.formula = Formula::And(conjuncts);
                    }
                }
            }
        }

        // Conjoin push-guarded nested-container element-length facts so
        // `let mut m: Vec<Vec<T>> = Vec::new(); for .. { if row.len()<=n {return}; m.push(row) }`
        // proves the inner access `m[r][col]`: the element `m[r]`'s modeled length is
        // `> n` (every pushed row was guarded), which with the range `col < n` discharges
        // `col < m[r].len()`. See `build_push_guard_elem_len_map`.
        if tp.has_std_scalar_index_call {
            let push_guard_elem_len = build_push_guard_elem_len_map(func);
            if !push_guard_elem_len.is_empty() {
                for (block_id, vc) in &mut block_vcs {
                    if v2_is_unsupported_mir_vc(vc) {
                        continue;
                    }
                    if let Some(facts) = push_guard_elem_len.get(block_id)
                        && !facts.is_empty()
                    {
                        ob_record_conjoin(vc, facts);
                        let mut conjuncts = Vec::with_capacity(facts.len() + 1);
                        conjuncts.extend_from_slice(facts);
                        conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                        vc.formula = Formula::And(conjuncts);
                    }
                }
            }
        }

        // Conjoin dominating length-guard facts so `let m = self.g.len();
        // if self.p_lo.len() != m { return }; for j in 0..m { self.p_lo[j] }` proves the
        // struct-FIELD scalar index: the guard pins `len(self.p_lo) == m` on its
        // fall-through edge, but through a DISTINCT `&self.p_lo` temp than the read carries,
        // so the read's `coll_len(_recv)` is left FREE. Emit `coll_len(_recv) >= m` — the
        // SAME var the bound reads — which with the loop range `j < m` discharges
        // `j < m <= coll_len(_recv)`. See `build_len_guard_field_map`.
        if tp.has_std_scalar_index_call && tp.has_switch_int {
            let len_guard_field = build_len_guard_field_map(func);
            if !len_guard_field.is_empty() {
                for (block_id, vc) in &mut block_vcs {
                    if v2_is_unsupported_mir_vc(vc) {
                        continue;
                    }
                    if let Some(facts) = len_guard_field.get(block_id)
                        && !facts.is_empty()
                    {
                        ob_record_conjoin(vc, facts);
                        let mut conjuncts = Vec::with_capacity(facts.len() + 1);
                        conjuncts.extend_from_slice(facts);
                        conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                        vc.formula = Formula::And(conjuncts);
                    }
                }
            }
        }

        // Conjoin loop-invariant `Ord::min`/`max` result bounds onto EVERY VC. These
        // are global invariants (single-assignment result, immutable args), so unlike
        // the BFS semantic guard they survive a loop-header join and reach a body that
        // uses the result only transitively — proving the bounded-copy idiom
        // `let n = src.len().min(dst.len()); for i in 0..n { dst[i] = src[i]; }`.
        // See `build_min_max_facts`. The fact is unconditionally true, so applying it
        // everywhere is sound. Also conjoin the unsigned modulo bounds
        // (`b != 0 ⟹ a%b < b`) — likewise global and unconditionally true — so a
        // wrapping access `s[n % s.len()]` discharges (via the ay nonlinear-relaxation
        // retry, which drops the `mod` term ay cannot handle).
        // Each row takes the set less the element-read congruences over a read that neither
        // the row, nor another fact, nor a conjunct it receives below (the preconditions, the
        // path guards, the semantic guards: `value_facts::late_conjunct_names`) can name
        // (`RowGlobalFacts::for_row`).
        let global_facts = build_global_invariant_facts(func);
        if !global_facts.is_empty() {
            for (_, vc) in &mut block_vcs {
                if v2_is_unsupported_mir_vc(vc) {
                    continue;
                }
                let row_facts = global_facts.for_row(&vc.formula);
                if row_facts.is_empty() {
                    continue;
                }
                ob_record_conjoin(vc, &row_facts);
                let mut conjuncts = row_facts;
                conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                vc.formula = Formula::And(conjuncts);
            }
        }
    }


    // Also conjoin the function's preconditions. Downstream tests
    // (safe_midpoint) encode invariants like `lo <= hi` in `preconditions`,
    // and must surface them explicitly to keep the safe/buggy distinction.
    //
    // Trust: but drop a precondition at any block that may have reassigned one of
    // its free variables — an entry contract `lo <= hi` is stale after `hi = big`
    // and would otherwise vacuously discharge a real `hi - lo` underflow.
    // Trust: P-B (staleness-class S2c). The version rename is UNCONDITIONAL — it
    // runs on every VC, not only precondition-bearing functions. With empty
    // preconditions the rename is a consistent single-point alpha-rename of the VC
    // (every `x` → the same `x#token` at the block terminal), so it is
    // verdict-preserving in isolation. The reason it must always run: block-defs
    // versioned at THEIR establish points (`version_block_def_at_establish`) are
    // skipped by the terminal rename and carry `#establish` tokens; the body's
    // references must be terminal-versioned to connect to the LIVE ones and
    // diverge from the HAVOCED ones (the kill's drop, by name-disjointness). A
    // body left bare (the old `preconditions.is_empty()` gate) would never connect
    // to an establish-versioned def. The `killed` set is vestigial — the rename,
    // not a per-block drop, is what kills staleness now.
    assert_eq!(
        row_points.len(),
        block_vcs.len(),
        "row use points desynchronised from the row list before the version rename"
    );
    if !block_vcs.is_empty() {
        // (The per-block may-reassigned KILL set is not computed: the conjoin below
        // takes it only for signature compatibility and ignores it — materialising it
        // was a Θ(blocks × names) whole-CFG fixpoint.)
        let filtered_preconditions: Vec<Formula> = if func.preconditions.is_empty() {
            Vec::new()
        } else {
            super::producer_preconditions(func)
                .into_iter()
                .filter(|pre| {
                    !contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, pre)
                })
                .collect()
        };
        // Trust (TINV step 10.3): the type-invariant use-site facts of this body, under
        // the use set INSTALLED in the context (with the record every conjoin writes).
        // `None` — the default, and always in a real compile until step 10.5 installs
        // a set — conjoins nothing and leaves every row byte-identical.
        let tinv_use = super::type_invariant_facts::tinv_use_facts(func);
        let tinv_prepared: std::cell::OnceCell<
            super::type_invariant_facts::PreparedTinvUseFacts,
        > = std::cell::OnceCell::new();
        // The rename runs at each row's own USE POINT, the SAME point the
        // path-def conjoin above used (`v2_live_path_defs_at_point`): a
        // per-statement row whose read precedes a same-block write must keep
        // that read on the PRE-write value its entry facts describe. Nothing
        // between the two passes pushes, removes or reorders a row (the
        // collapse-invariant assert below checks it), and this assert keeps the
        // `zip` from failing open.
        for ((block_id, vc), point) in block_vcs.iter_mut().zip(row_points.iter().copied()) {
            // BUDGET POLL, per ROW. `conjoin_preconditions_versioned_at_point_recorded`
            // rewrites the row's ENTIRE formula through `version_rename_at` and
            // then visits the renamed formula again for `entry_sentinel_ties`,
            // so the cost lives inside ONE row's formula and only a per-row poll
            // can interrupt it. Breaking leaves the remaining rows with no
            // precondition facts and un-renamed.
            //
            // Dropping the preconditions drops hypotheses — PROVE -> FAIL only.
            // The un-renamed BODY is the half that needs the rest of the
            // argument, and it is why a tail row must never be read as a
            // finished one: the S2c exemption conjoins path and semantic guards
            // BARE precisely because the body is terminal-versioned here, so a
            // body left bare would re-unify a guard's ENTRY-valued read with a
            // reassigned body read instead of staying name-disjoint from it.
            // Nothing consumes such a row. `budget_exhausted` latches, so the
            // poll in the type-range loop below sets `truncated` and the
            // overflow-check origin inventory has NO table, while the
            // caller's post-generation checkpoint discards the partial
            // inventory before anything is dispatched. A tail row cannot reach
            // a solver, a cache with authority, or the elision seam.
            if trust_types::verify_budget::budget_exhausted() {
                // Carries the flag for the same reason as the path-def loop
                // above: a wall-clock trip does not latch, so no later loop can
                // be trusted to set it.
                truncated = true;
                break;
            }
            if v2_is_unsupported_mir_vc(vc) {
                continue;
            }
            let sv = sv_lazy.get_or_init(|| super::stmt_versions_for(func));
            let record_ob = vc.obligation.is_some();
            // INTRINSIC-RESIDUAL-1: the producer's preconditions, without the
            // generator's 128-bit parameter facts (`producer_preconditions` says why).
            let old_formula = std::mem::replace(&mut vc.formula, Formula::Bool(true));
            let (new_formula, conjoined) = conjoin_preconditions_versioned_at_point_inner(
                func,
                sv,
                *block_id,
                point,
                &filtered_preconditions,
                old_formula,
                record_ob,
                true,
            );
            vc.formula = new_formula;
            // Mirror the whole-formula version rename this step applies onto the
            // recorded body/subject/wrappers (so they stay byte-identical to their
            // copies in `formula`), THEN record the filtered preconditions as the
            // outer ConjoinFactsLast wrapper (they are conjoined bare, after the
            // rename). No-op when the VC carries no obligation.
            if record_ob {
                let rename_point = row_rename_point(func, *block_id, point);
                ob_record_rename_at(vc, sv, func, *block_id, rename_point);
                ob_record_conjoin_owned(vc, conjoined);
            }
            // Trust (TINV step 10.3): the type-invariant use-site facts, as a SECOND
            // recorded `ConjoinFactsLast` at the SAME point, after the rename (entry
            // facts bare, post-call facts sealed at their call target; nothing renamed
            // again). They then sit inside the later path-guard and semantic-guard
            // wrappers exactly as `requires` do. Never in a `TypeInvariant` row (the
            // mint's own rows, which must not assume what they prove) and never in a
            // row with no obligation record (TINV-25: the record is what the consumer
            // replays). Every row that receives a fact is RECORDED with its tags in the
            // generation's recording scope: the second disclosure channel.
            if let Some(tinv_facts) = tinv_use.as_ref()
                && vc.obligation.is_some()
                && !matches!(vc.kind, VcKind::TypeInvariant { .. })
            {
                let prepared = tinv_prepared.get_or_init(|| tinv_facts.prepare(func, sv));
                let old_formula = std::mem::replace(&mut vc.formula, Formula::Bool(true));
                let (new_formula, facts, tags) =
                    prepared.conjoin_at_point_recorded(func, sv, *block_id, point, old_formula);
                vc.formula = new_formula;
                if !facts.is_empty() {
                    ob_record_conjoin_owned(vc, facts);
                    // The scope admitted these facts for this body, so it records.
                    let recorded = crate::type_invariant::record_assumed_row(
                        crate::type_invariant::TinvAssumedRow {
                            def_path: func.def_path.clone(),
                            kind: vc.kind.clone(),
                            location: vc.location.clone(),
                            tags,
                        },
                    );
                    assert!(
                        recorded,
                        "a TINV use-site fact was conjoined outside its recording scope"
                    );
                }
            }
        }
    }

    // FAIL CLOSED on the positional pairing captured above. A mismatch means a
    // pass in between pushed, removed or moved a row, so from that point on every
    // flag is attached to a different row's formula. Refusing loudly beats
    // stripping path guards from the tail rows in silence: an unconditioned
    // violation formula accuses paths that cannot run.
    assert_eq!(
        block_vcs.len(),
        content_free.len(),
        "collapse-invariant classification desynchronised from the row list: it was \
         captured for {} rows and there are now {}. A row pushed or removed between \
         the capture step and here would leave the tail rows unguarded, which turns \
         an unreachable violation into a false refutation.",
        content_free.len(),
        block_vcs.len()
    );
    // Trust S2c (exemption): conjoin path guards then semantic assert-passed guards
    // AFTER the rename above, so their bare ENTRY-param reads stay bare (disjoint
    // from a reassigned body read) — replacing the dropped staleness kills.
    for ((block_id, vc), (flag_block, is_content_free)) in
        block_vcs.iter_mut().zip(content_free.iter().copied())
    {
        // BUDGET POLL, per ROW. `v2_formula_with_path_guards_recorded` CLONES
        // the row's whole accumulated formula once per guard path and flattens
        // it into each disjunct (see `ReachSummary::Guards`, "What it costs"),
        // so a single high-in-degree row is the entire overrun and no poll
        // outside this loop reaches it. Breaking leaves the remaining rows
        // un-spliced, i.e. WITHOUT their path guards.
        //
        // Fail-closed, and that holds for the CONTENT-FREE rows this step is
        // here to decide. Content-free is `v2_formula_is_tautology`, so such a
        // row's violation is `true`: left unguarded it is trivially SAT and
        // REFUTES. Dropping conjuncts from an `And` can only make a formula
        // easier to satisfy, so no abandoned row can turn vacuously discharged
        // — the degradation over-reports (PROVE -> FAIL), never under-reports.
        // It does not ship either: the trip latches, the type-range loop below
        // sets `truncated` (so the origin inventory has no table) and the
        // caller's post-generation checkpoint discards the partial inventory.
        //
        // The poll precedes the positional identity assert deliberately. On the
        // exhausted path no remaining row's flag is consulted at all, so there
        // is no flag-to-row pairing left for that assert to protect; on the
        // non-exhausted path every row still takes it first, unchanged.
        if trust_types::verify_budget::budget_exhausted() {
            // Carries the flag for the same reason as the two loops above.
            truncated = true;
            break;
        }
        assert_eq!(
            *block_id, flag_block,
            "collapse-invariant classification desynchronised from the row list: the \
             flag at this position was captured for bb{}, but the row now here belongs \
             to bb{}. The rows were reordered between the capture step and here.",
            flag_block.0, block_id.0
        );
        if v2_is_unsupported_mir_vc(vc) {
            continue;
        }
        // THE COLLAPSE INVARIANT, enforcement step — the ONE place a row whose
        // meaning is its path condition is decided.
        //
        // `degraded` is the whole trigger, and it is what makes this subsume any
        // future collapse mode: a block that kept its real path list falls
        // through to the ordinary splice below, INCLUDING one whose real list
        // contains an EMPTY path. That empty path is INFORMATION — "reachable
        // with no guard at all" — not an artifact, which is exactly why a
        // genuinely reachable `unreachable!()` still REFUTES.
        let degraded = path_guards.degraded.contains(block_id);
        if degraded && is_content_free {
            match path_guards.reachability.get(block_id) {
                // A real condition. Splice it through the SAME lowering an
                // ordinary path list takes — one single-guard path per in-edge,
                // so `Or([And([g_e, body]) ..])` = `(⋁ g_e) ∧ body`.
                Some(ReachSummary::Guards(edges)) => {
                    let sv = sv_lazy.get_or_init(|| super::stmt_versions_for(func));
                    let restored: Vec<Vec<(BlockId, GuardCondition)>> =
                        edges.iter().map(|edge| vec![edge.clone()]).collect();
                    let old_formula = std::mem::replace(&mut vc.formula, Formula::Bool(true));
                    if vc.obligation.is_some() {
                        let (new_formula, path_terms) = v2_formula_with_path_guards_recorded(
                            func,
                            sv,
                            *block_id,
                            &restored,
                            old_formula,
                        );
                        vc.formula = new_formula;
                        if let Some(ob) = vc.obligation.as_mut() {
                            ob.wrappers.push(ObligationWrapper::PathGuardOr { paths: path_terms });
                        }
                    } else {
                        vc.formula = v2_formula_with_path_guards(
                            func,
                            sv,
                            *block_id,
                            &restored,
                            old_formula,
                        );
                    }
                    continue;
                }
                // The disjunction is `true`, which the collapsed unguarded path
                // already says. NOT absence — the block IS reachable — so fall
                // through to the ordinary splice and let the row refute. This is
                // what keeps a reachable `unreachable!()` a refutation.
                Some(ReachSummary::Unconditional) => {}
                // ABSENCE. Nothing to decide the row by, and the row has nothing
                // of its own to be decided by either. DECLINE: "I have no
                // reachability information" is not "this is reachable".
                Some(ReachSummary::Unavailable) | None => {
                    *vc = v2_path_condition_degraded_vc(
                        func,
                        *block_id,
                        vc,
                        path_guards.collapse,
                        "no in-edge disjunction is available for it (the block has no \
                         in-edge the summary can account for, or its in-edge list is \
                         empty — an empty disjunction is `false` and would vacuously \
                         prove the row). This is not a SIZE limit: no in-degree, \
                         however large, reaches this arm",
                    );
                    continue;
                }
            }
        }
        // Everything else — every row with a violation condition of its own, and
        // every row of a block that kept its path list — takes the ordinary
        // splice below, unchanged by the invariant.
        if let Some(block_guard_paths) = guard_paths_map.get(block_id) {
            let sv = sv_lazy.get_or_init(|| super::stmt_versions_for(func));
            let old_formula = std::mem::replace(&mut vc.formula, Formula::Bool(true));
            if vc.obligation.is_some() {
                let (new_formula, path_terms) = v2_formula_with_path_guards_recorded(
                    func,
                    sv,
                    *block_id,
                    block_guard_paths,
                    old_formula,
                );
                vc.formula = new_formula;
                // Trust (2026-10-16, S1): a DEGRADED block's single empty path is not
                // "reachable with no guard" but "the guards were lost" — record that, so
                // the generic refutation scope can withhold a counterexample that the
                // missing dominating guards would have excluded (the refutation-polarity
                // caveat on the path-guard helper below: "a collapsed empty guard path is
                // indistinguishable from a genuinely unconditional path").
                // `Collapsed` renders exactly as `Raw`, so the formula is unchanged.
                //
                // NOT for a content-free row whose reachability summary is
                // `Unconditional`: there the empty path is the in-edge disjunction
                // itself (`true`), positive information that the block is reachable —
                // the arm above that keeps a reachable `unreachable!()` a refutation.
                // Marking it collapsed would hold that genuine refutation.
                let path_terms = v2_mark_lost_guards(
                    path_terms,
                    degraded,
                    is_content_free,
                    path_guards.reachability.get(block_id),
                );
                // The dominating path-guard map is the sole non-conjoining wrapper.
                if let Some(ob) = vc.obligation.as_mut() {
                    ob.wrappers.push(ObligationWrapper::PathGuardOr { paths: path_terms });
                }
            } else {
                vc.formula = v2_formula_with_path_guards(
                    func,
                    sv,
                    *block_id,
                    block_guard_paths,
                    old_formula,
                );
            }
        }
    }
    assert_eq!(
        row_points.len(),
        block_vcs.len(),
        "row-point pairing desynchronised before the semantic-guard conjoin"
    );
    if block_vcs.iter().any(|(_, vc)| !v2_is_unsupported_mir_vc(vc)) {
        let semantic_guards = super::semantic_guard_map_for(func, summaries);
        if !semantic_guards.is_empty() {
            let sv = sv_lazy.get_or_init(|| super::stmt_versions_for(func));
            for ((block_id, vc), point) in block_vcs.iter_mut().zip(row_points.iter().copied()) {
                if v2_is_unsupported_mir_vc(vc) {
                    continue;
                }
                if let Some(sem_guards) = semantic_guards.get(block_id)
                    && !sem_guards.is_empty()
                {
                    // Trust (2026-09-30, vac Phase 1.1 follow-up): a semantic guard is stamped
                    // at its OWN point and conjoined after the row's rename, so an entry read
                    // inside it is sealed `n#e` and the precondition conjoin — which ties only
                    // the `#e` names of the renamed body — never saw it. Tie those too, under
                    // the SAME consumer clause (`entry_sentinel_ties_for_exempt_facts`).
                    let ties = entry_sentinel_ties_for_exempt_facts(
                        func,
                        sv,
                        *block_id,
                        point,
                        sem_guards,
                        &vc.formula,
                    );
                    let mut conjuncts = Vec::with_capacity(sem_guards.len() + ties.len() + 1);
                    conjuncts.extend_from_slice(sem_guards);
                    conjuncts.extend(ties);
                    ob_record_conjoin(vc, &conjuncts);
                    conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                    vc.formula = Formula::And(conjuncts);
                }
            }
        }
    }

    // Path defs, semantic guards, and preconditions can introduce parameter
    // references after the per-VC builder ran; bound them in a final pass too.
    //
    // Trust (versioned-usize bounds gap): BOUNDS VCs (SliceBoundsCheck /
    // IndexOutOfBounds) need the same ranges — they were excluded, so a
    // loop-carried SSA version of a `usize` index (`i#s0_1_s6_0`) had NO
    // `0 <= i` constraint and the solver refuted `while i < v.len() { v[i] }`
    // with `i = -1` (a value no well-typed execution can hold). The ranges are
    // DROP-ONLY true facts of every Rust execution, identical to the overflow
    // lane; the UNSAT-premise hazard (see the countdown B1 note) is guarded at
    // its emitter (negative constant bounds are never emitted), and an
    // UNguarded OOB index still refutes with an in-range counterexample.
    let has_back_edges: std::cell::OnceCell<bool> = std::cell::OnceCell::new();
    for (_, vc) in &mut block_vcs {
        // BUDGET POLL, per ROW. The battery below rebuilds this row's formula up
        // to five times over (`conjoin_length_nonneg_bounds`,
        // `conjoin_arg_type_ranges`, `conjoin_local_type_ranges_excluding`,
        // `conjoin_datatype_field_ranges_excluding`, `conjoin_slice_len_bounds`),
        // each a full rewrite of an already fact-laden formula plus a `clone` of
        // it for the obligation mirror, so ONE row can be the whole overrun.
        //
        // Degrades exactly as the generation loop above does — set `truncated`,
        // stop — and the flag is the point. Dropping the ranges only drops
        // DROP-ONLY true facts (PROVE -> FAIL), but `truncated` is what tells
        // the overflow-check origin inventory that this walk was cut short, so
        // it has NO join table and every proven-overflow check is KEPT;
        // `Unique` is only sound relative to a walk that ran to the end.
        //
        // The three earlier passes (path defs, preconditions, path guards)
        // degrade by `break` alone and RELY ON REACHING THIS POLL to latch the
        // flag: `budget_exhausted` latches, and a trip in any of them implies
        // `block_vcs` is non-empty, so this loop runs at least one iteration and
        // sets it. Do not move this poll off the loop head, and do not reorder
        // this loop above them — either would silently un-fail-close all three.
        if trust_types::verify_budget::budget_exhausted() {
            truncated = true;
            break;
        }
        // Trust (scope refinement after the falsification-gate sweep): BOUNDS
        // VCs take the range conjoins ONLY when the function has a BACK EDGE —
        // exactly the loop-carried-SSA class the extension exists for: a
        // back-edge version is HAVOCKED (no reaching def), so without its type
        // range the solver picks `i#s0_1_s6_0 = -1`. A forward-join version
        // (`step = if c { 1 } else { 2 }`) keeps real reaching defs (the
        // SwitchInt-join Ite fact), needs no range — and the extra conjuncts
        // pushed ay's UNSAT-proof emission into an invalid th_resolution step
        // its own checker rejects (`merged_local_index` went proved → Unknown;
        // fail-closed, but a real falsification-gate regression; the
        // shape-sensitive ay proof-emission bug is the root cause to fix
        // separately, ay-side).
        // Trust (2026-09-29): the battery itself — which facts, in which order, with
        // which exclusion — is `generate::type_ranges::conjoin_type_range_battery`,
        // stated ONCE and shared with the `unix_hardened` twin of the same assert
        // (`hardened_twin_type_ranges`), which used to carry only the parameter
        // ranges and was refuted where this lane proved (`args__slice_len = 2^64`
        // on `while i < args.len() { i += 1 }`). What stays HERE is this lane's
        // own admission rule, byte-identical to before:
        //
        // `UncheckedArithmeticOverflow` is the SAME out-of-range obligation as
        // `ArithmeticOverflow` (`v2_overflow_call_body` builds both from the same
        // builder) — only the runtime-guard answer differs. It must therefore
        // keep the identical DROP-ONLY type-range strengthening, or splitting the
        // kind would silently make every `unchecked_{add,sub,mul}` LESS
        // dischargeable than the `a + b` it models: a widened decline, not a fix.
        // `RangeBatteryClass::of_kind` folds the two into one class for that reason.
        let class = RangeBatteryClass::of_kind(&vc.kind);
        // Trust (NEGATIVE-LENGTH class): the kinds the range battery below does
        // NOT reach — `Unreachable`, `Assertion`, the panic-path rows — got NO
        // length bound at all, so the merged `Unreachable` sink of
        // `match a { [] => .., [x] => .., [x, .., y] => .. }` was REFUTED with
        // `a__slice_len = -1`: a negative slice length, which no execution can
        // hold. Attach the ONE bound that is a theorem on every target and every
        // element type (`0 <= len`; see `conjoin_length_nonneg_bounds` for why
        // the `isize::MAX` half stays behind its non-ZST gate in
        // `conjoin_slice_len_bounds`). Applied ONLY to the kinds the battery
        // skips (class `Other`), so every `ArithmeticOverflow`/bounds formula stays
        // byte-identical to what it was — this cannot perturb the lane the sweep
        // tuned. The class gate is what makes that true and is asserted directly:
        // `excluded_kind_ub_rows_still_refute`
        // (`tests/slice_length_nonneg_real_mir.rs`) requires the two loop-free
        // BOUNDS fixtures to carry no `0 <= *__slice_len` conjunct at all, and that
        // assertion fires as soon as the gate is dropped. It is name-driven, so it
        // introduces no free variable, and DROP-ONLY: a real violation's witness
        // carries a non-negative length and survives it.
        //
        // SCOPE, so the next reader does not over-read it. (a) On most shapes it
        // removes the ACCUSATION without discharging the obligation: MEASURED, only
        // the TWO-arm matches reach `Proved`, and every three-or-more-arm shape stops
        // short of it. An `Unknown` here is NOT automatically a build error — this
        // kind has a runtime fallback, so `strict_failure_is_fatal` counts it
        // `runtime_checked` and excludes it under the default strict policy while
        // `-Ztrust-policy=certify` still rejects it. See
        // `conjoin_length_nonneg_bounds` for the measured policy table. (b) It is not
        // what decides a row whose PATH CONDITION was degraded by a path-guard
        // collapse. Such a row has already been handled by the collapse-invariant
        // enforcement step earlier in this function — re-conditioned on its in-edge
        // disjunction, left on the ordinary splice when the block is unconditionally
        // reachable, or turned into an `UnsupportedMir` decline, which the
        // `v2_is_unsupported_mir_vc` gate below then skips. Adding `0 <= len` to a
        // formula that no longer states where it applies would not have helped;
        // supplying the missing reachability condition is a different repair.
        // A TINV row (class `TypeInvariant`) takes the SAME admission rule as an
        // `Other` row here: skipped only when it is an `UnsupportedMir` decline.
        if matches!(class, RangeBatteryClass::Other | RangeBatteryClass::TypeInvariant)
            && v2_is_unsupported_mir_vc(vc)
        {
            continue;
        }
        if class == RangeBatteryClass::Bounds
            && !*has_back_edges.get_or_init(|| {
                super::terminator_presence_for(func).has_back_edge && count_back_edges(func) > 0
            })
        {
            continue;
        }
        // Trust (bounds ARM): each battery step is a pure `And([facts.., formula])`
        // push (facts LAST) or identity when it has no facts, so mirror each onto the
        // recorded obligation as a `ConjoinFactsLast` read back from the before/after
        // pair (`ob_record_conjoin_wrap`), in step order. No-op when the VC carries no
        // obligation; the UNSIGNED var*var mul `ArithmeticOverflow` arm carries a
        // record (the UMUL RECORD), so these mirrors are load-bearing for it as well
        // as for the bounds VCs.
        let formula = std::mem::replace(&mut vc.formula, Formula::Bool(true));
        let mut ob = vc.obligation.as_mut();
        vc.formula = conjoin_type_range_battery(func, formula, class, &mut |before, after| {
            if let Some(ob) = ob.as_deref_mut()
                && let Some(facts) = extract_conjoined_facts(before, after)
                && !facts.is_empty()
            {
                ob.wrappers.push(ObligationWrapper::ConjoinFactsLast { facts: facts.to_vec() });
            }
        });
    }

    // FINAL pass: collapse SSA locals' version tokens to the bare name so
    // facts and body reads of the same single-valued local always share one
    // SMT symbol (see `normalize_ssa_version_tokens` for the identity
    // argument; reassigned locals keep their load-bearing token disjointness).
    for (_, vc) in &mut block_vcs {
        if v2_is_unsupported_mir_vc(vc) {
            continue;
        }
        let formula = std::mem::replace(&mut vc.formula, Formula::Bool(true));
        vc.formula = normalize_ssa_version_tokens_owned(func, formula);
        // Mirror the same token collapse onto the recorded body/subject/wrappers so
        // reconstruction stays byte-identical to the normalized `formula`.
        ob_record_normalize(vc, func);
    }
    }

    // THE FRONTIER BUDGET MUST SPEAK. `v2_analyze_path_guards` bounds its own
    // work by abandoning the walk (COLLAPSE MODE 3) and handing back the
    // all-`true` map. That is fail-closed — it strictly REMOVES proof hypotheses
    // — but on its own it is INVISIBLE: every row of the function is spliced
    // with an empty path list and emitted looking exactly like a row that had no
    // path condition to begin with. MEASURED 2026-09-09 (seal-line 28aee49dd8),
    // before this row existed: `ay-arrays::final_check` tripped this budget and
    // emitted 20 VCs with a byte-identical `kind`/`formula`/`location` digest to
    // the run with the cap switched off.
    //
    // So the cap is paid for with one explicit Unknown row, the shape this
    // pipeline already uses for a bounded-out function (`entry.rs`'s and
    // `discharge.rs`'s `TrustVcGenWorkBudgetExceeded`). Mode 3 ONLY: mode 2
    // (`BudgetTripped`) degrades identically and its silence predates this row;
    // reporting it too would be a verdict change with no measurement behind it.
    //
    // SOUNDNESS: ADD-ONLY, and the added row is preclassified Unknown
    // (`UnsupportedMir` is never dispatched to a solver) carrying a SAT
    // `Bool(true)` violation formula, so a direct solver caller cannot read it as
    // a proof either. It can only cost this function a verdict, never grant one.
    // Appended after every pass that zips `row_points` or reads
    // `overflow_assert_rows`, so no parallel index moves.
    if path_guards.collapse == PathGuardCollapse::FrontierBudgetTripped {
        block_vcs.push((BlockId(0), v2_frontier_budget_vc(func)));
    }

    // Trust (DIAGNOSTIC ONLY, 2026-09-19): `TRUST_SLICE_VC_TRACE=1` prints the
    // finished formula of every slice-bounds row. Added because the black-box
    // characterisation of the loop-assigned-slice class stops here: measured, a
    // guard on a loop-assigned INTEGER survives while a guard on the LENGTH of a
    // loop-assigned SLICE does not, and routing the length through an integer
    // (`let n = w.len()`) does not help either. What is left to see is which
    // length TERM the guard constrains and which one the `assert` reads — and
    // three attributions in this class died on reading one more file, so it is
    // printed rather than guessed. Verdict-neutral: no branch depends on it.
    static SLICE_VC_TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if *SLICE_VC_TRACE.get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_SLICE_VC_TRACE")) {
        for (bid, vc) in &block_vcs {
            if matches!(vc.kind, VcKind::SliceBoundsCheck | VcKind::IndexOutOfBounds) {
                eprintln!(
                    "[slicevc] block={:?} kind={:?}\n[slicevc]   {:?}",
                    bid, vc.kind, vc.formula
                );
            }
        }
    }
    // A trip in a walk this function calls but does not own — the path-definition
    // fixpoint, the block-definition extraction — reaches none of the `truncated = true`
    // sites above: that walk hands back fewer facts and generation carries on with rows
    // that look complete. The budget is sticky — the step counter saturates at zero and a
    // passed deadline stays passed — so one non-charging read here reports every trip this
    // walk made, wherever it happened — including a trip inside the extraction the
    // statement-version oracle's write index is built from: the SSA resolution has no
    // truncated state of its own, but gen-sets extracted after a trip may be short.
    truncated |= trust_types::verify_budget::exhausted_readonly();
    SafetyWalk { rows: block_vcs, overflow_assert_rows, truncated, row_capped }
}

/// The report [`PathGuardCollapse::FrontierBudgetTripped`] owes its reader.
///
/// One row per function, naming the bound (the walk's frontier), the two
/// constants that set it, and the consequence (every block of this function lost
/// its per-path guards). The kind tag is a public constant so the compiler's
/// reporting seams and the tests that pin them match on the TAG, not on this
/// prose. The kind and the detail are byte-identical to the published seal's
/// (trust 321aaeda75), so a gate comparing the two finds the same row.
fn v2_frontier_budget_vc(func: &VerifiableFunction) -> VerificationCondition {
    unsupported_mir_vc(
        func,
        crate::VCGEN_PATH_GUARD_FRONTIER_BUDGET_KIND.to_string(),
        format!(
            "function `{}` ({} blocks): the path-guard walk hit its FRONTIER budget \
             ({} pops / {} live queue entries) and every block of this function lost its \
             per-path guard list. The remaining obligations were generated WITHOUT path \
             conditions, which can only weaken them; this row records that the pre-pass \
             was bounded by memory rather than finished, so the absence of a refutation \
             here is not a proof",
            func.name,
            func.body.blocks.len(),
            MAX_PATH_WALK_STEPS,
            MAX_PATH_WALK_QUEUE,
        ),
        func.span.clone(),
    )
}

/// The per-block path cap of [`v2_build_path_guard_map`]. A block that is
/// reached by more routes than this keeps ONE unguarded path instead
/// (`COLLAPSE MODE 1`); [`v2_reachability_for_collapsed`] is what stops that
/// from becoming an unconditional accusation.

// ---------------------------------------------------------------------------
// Structurally-shared paths
// ---------------------------------------------------------------------------

/// One node of an IMMUTABLE path prefix, shared by every extension of it.
///
/// The path walk below explores root-to-block paths, and it used to carry each
/// one as its own `Vec`, cloned in full for every successor pushed. That makes
/// the frontier cost O(paths x depth) in BYTES: a queue entry for a path of
/// depth d owns d guards, and a block with k successors immediately owns k more
/// copies of the same prefix. MEASURED on first-party/ty's tla-cli, whose
/// `<ty::cli_schema::Cli as clap_builder::derive::FromArgMatches>
/// ::from_arg_matches_mut` — the body `#[derive(Parser)]` emits for a large CLI —
/// drove the compiler to a 137.8 GB and then a 140.6 GB peak footprint on a
/// 128 GB box, with `heap -s` counting 86 million live malloc nodes.
///
/// A cons list fixes it at the root: extending a path ALLOCATES ONE NODE and
/// shares the entire prefix, so the frontier costs O(nodes pushed) instead of
/// O(paths x depth), and pushing to a second successor is an `Rc` refcount bump
/// rather than a copy. The enumeration is UNCHANGED — same paths, same order,
/// same output type — so this costs no precision anywhere downstream. It is the
/// representation that was wrong, not the analysis.
struct PathNode<T> {
    item: T,
    tail: Option<std::rc::Rc<PathNode<T>>>,
    /// Cached so length is O(1) rather than a walk; the list is immutable, so
    /// it cannot go stale.
    len: usize,
}

/// ITERATIVE teardown of the `tail` chain.
///
/// The derived drop glue for a cons list is RECURSIVE: dropping the last handle
/// on a node drops its `tail`, which drops ITS `tail`, one stack frame per node.
/// The chain is as long as the acyclic path the walk is on, bounded by the BLOCK
/// COUNT and by nothing else. Neither of the walk's bounds limits DEPTH: the
/// local `n*n` step `cap` in [`v2_analyze_path_guards`] bounds DEQUEUES, and
/// [`MAX_TOTAL_PATH_GUARD_ENTRIES`] bounds retained guard ENTRIES — and the
/// visited-block chain (`path_blocks`), which grows by one node per block on
/// every path including unguarded straight-line edges, is never charged to it at
/// all. So a straight-line body long enough overflows the stack whatever those
/// bounds say. That is an uncatchable SIGSEGV of the whole compiler, strictly
/// worse than the budget exit this walk takes.
///
/// MEASURED 2026-09-09 on an exact structural replica (`Option<Rc<Node>>` chain,
/// no manual `Drop`, 8 MiB main-thread stack): a release build dropped depth
/// 250_000 fine and ABORTED at 300_000 with `fatal runtime error: stack
/// overflow`; a debug build aborted between 40_000 and 50_000.
///
/// The loop unlinks one node at a time and only ever holds ONE owned node, so
/// teardown is O(depth) time and O(1) stack. `Rc::try_unwrap` returning `Err`
/// means another path still shares this suffix — whichever handle is last runs
/// this same loop.
impl<T> Drop for PathNode<T> {
    fn drop(&mut self) {
        let mut cursor = self.tail.take();
        while let Some(node) = cursor {
            match std::rc::Rc::try_unwrap(node) {
                Ok(mut owned) => cursor = owned.tail.take(),
                Err(_) => break,
            }
        }
    }
}

/// A shared path prefix. `None` is the empty path.
type SharedPath<T> = Option<std::rc::Rc<PathNode<T>>>;

/// Extend `tail` by `item`, sharing all of `tail`. One allocation.
fn path_cons<T>(tail: &SharedPath<T>, item: T) -> SharedPath<T> {
    let len = tail.as_ref().map_or(0, |node| node.len) + 1;
    Some(std::rc::Rc::new(PathNode { item, tail: tail.clone(), len }))
}

fn path_len<T>(path: &SharedPath<T>) -> usize {
    path.as_ref().map_or(0, |node| node.len)
}

/// Does `path` already contain `needle`? The walk uses this to keep paths
/// SIMPLE (no repeated block), exactly as the old `Vec::contains` did.
fn path_contains<T: PartialEq>(path: &SharedPath<T>, needle: &T) -> bool {
    let mut cursor = path.as_deref();
    while let Some(node) = cursor {
        if node.item == *needle {
            return true;
        }
        cursor = node.tail.as_deref();
    }
    false
}

/// Materialize root-first, which is the order the old `Vec` carried (it pushed
/// as it descended). Called ONLY when a path is recorded into the result map,
/// so the O(depth) copy happens once per STORED path instead of once per queue
/// push.
fn path_to_vec<T: Clone>(path: &SharedPath<T>) -> Vec<T> {
    let mut out = Vec::with_capacity(path_len(path));
    let mut cursor = path.as_deref();
    while let Some(node) = cursor {
        out.push(node.item.clone());
        cursor = node.tail.as_deref();
    }
    out.reverse();
    out
}

const MAX_PATHS_PER_BLOCK: usize = 64;

/// Total retained path-guard entries — across the result map AND the pending
/// queue — before the walk takes its global collapse.
///
/// `MAX_PATHS_PER_BLOCK` bounds how many paths ONE BLOCK keeps and the step cap
/// bounds how many dequeues happen; NEITHER bounds BYTES. Every
/// `queue.push_back` clones the whole path (`next_guards`, `path_blocks`), so a
/// wide CFG can hold O(dequeue-cap x depth) entries in the queue before the step
/// cap is ever reached. MEASURED 2026-09-10 on `first-party/ty`'s tla-cli
/// (seal trust-3206ff37): one `trustc` reached a PEAK PHYSICAL FOOTPRINT of
/// 137.8 GB on a 128 GB box — past physical RAM, so the machine thrashed — with
/// `vmmap` naming this walk and `sample` catching it in
/// `v2_build_path_guard_map` / `v2_analyze_path_guards`. The ambient budget
/// bounds TIME and STEPS; this is the byte bound it never had.
///
/// FOUR MILLION WAS FAR TOO HIGH, and the second measurement is why this number
/// is now small. With that cap the same tla-cli run peaked at 140.6 GB — worse
/// than the 137.8 GB it was meant to fix — and `heap` counted 86 MILLION live
/// malloc nodes. An entry is a `(BlockId, GuardCondition)` whose guard owns a
/// formula tree, so a cap counting ENTRIES buys roughly an order of magnitude
/// more NODES, and 4e6 entries is tens of gigabytes. The bound has to be set
/// against the memory it is defending, not against what looks like a large CFG.
///
/// The function that provoked it is worth naming, because it is not a hand
/// written body at all: `<ty::cli_schema::Cli as clap_builder::derive::
/// FromArgMatches>::from_arg_matches_mut`. `#[derive(Parser)]` over a CLI with
/// ty's number of subcommands and options emits ONE function whose match arms
/// give it a CFG no human body approaches, and every path through it is
/// enumerated here.
///
/// 250 000 entries still admits any hand-written function comfortably (a
/// 500-block body at the full 64 paths per block sits an order below it) while
/// capping this walk's retention in the low hundreds of megabytes. Past it the
/// walk takes the same sound collapse the step budget takes.
const MAX_TOTAL_PATH_GUARD_ENTRIES: usize = 250_000;

/// Safety-VC rows one function may generate before the walk truncates.
///
/// The companion to [`MAX_TOTAL_PATH_GUARD_ENTRIES`], defending the same
/// resource from the other side: that one bounds the guard ENUMERATION, this
/// one bounds the ROWS the enumeration decorates. Both had only time bounds,
/// and time is the wrong unit for memory — rows are cheap to produce and
/// expensive to keep, since each is rewritten up to five times downstream.
///
/// 50 000 rows is far more than any hand-written function emits (one row per
/// panic-capable operation) and holds this phase's retention to a few hundred
/// megabytes even at the widest.
pub(super) const MAX_VC_ROWS_PER_FUNCTION: usize = 50_000;

/// [`MAX_VC_ROWS_PER_FUNCTION`], or a test's own cap ([`TestRowCap`]): no test can
/// afford a body that reaches fifty thousand rows.
fn max_vc_rows_per_function() -> usize {
    #[cfg(test)]
    if let Some(cap) = TEST_ROW_CAP.with(std::cell::Cell::get) {
        return cap;
    }
    MAX_VC_ROWS_PER_FUNCTION
}

#[cfg(test)]
thread_local! {
    static TEST_ROW_CAP: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
}

/// A row cap for this test thread until the guard drops.
#[cfg(test)]
pub(super) struct TestRowCap;

#[cfg(test)]
impl TestRowCap {
    pub(super) fn install(cap: usize) -> Self {
        TEST_ROW_CAP.with(|slot| slot.set(Some(cap)));
        Self
    }
}

#[cfg(test)]
impl Drop for TestRowCap {
    fn drop(&mut self) {
        TEST_ROW_CAP.with(|slot| slot.set(None));
    }
}

/// Which collapse [`v2_build_path_guard_map`] took, if any. Reported so a test
/// can assert that a fixture still exercises the mode it was captured for: both
/// collapses are triggered by SIZE, so a change to `MAX_PATHS_PER_BLOCK`, to the
/// step budget, or to the shape rustc lowers a fixture into can silently move a
/// regression guard off the path it guards. A vacuous pass is the failure mode
/// these repairs cannot afford.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum PathGuardCollapse {
    /// Every block kept its full per-path guard list.
    None,
    /// COLLAPSE MODE 1: at least one block exceeded [`MAX_PATHS_PER_BLOCK`].
    SaturatedBlocks,
    /// COLLAPSE MODE 2: the global step budget tripped and EVERY block of the
    /// function lost its per-path guards at once.
    BudgetTripped,
    /// COLLAPSE MODE 3: the walk's FRONTIER budget tripped —
    /// [`MAX_PATH_WALK_STEPS`] pops or [`MAX_PATH_WALK_QUEUE`] live queue
    /// entries. Same degradation as [`Self::BudgetTripped`] (every block loses
    /// its per-path guards, every block is `degraded`, and
    /// [`v2_reachability_for_collapsed`] restores the in-edge disjunction for
    /// all of them) — a SEPARATE variant so the cause can be REPORTED rather
    /// than silently borrowing mode 2's name.
    ///
    /// # Where the name surfaces
    ///
    /// Through [`v2_frontier_budget_vc`]: ONE extra function-level
    /// `UnsupportedMir` row (kind [`crate::VCGEN_PATH_GUARD_FRONTIER_BUDGET_KIND`])
    /// that `generate_v2_safety_vcs_impl_with_origins_checked` appends whenever
    /// this variant is the collapse. Not through the `PathConditionDegraded` row:
    /// [`v2_path_condition_degraded_vc`]'s only caller is the
    /// `ReachSummary::Unavailable | None` arm of the collapse invariant, which
    /// fired on none of the 1269 `ay-arrays` bodies measured 2026-09-09.
    ///
    /// # Why a third cliff exists at all
    ///
    /// Mode 2's cap is `16n^2 + 16n + 4096` POPS. Prefix sharing
    /// ([`SharedPath`]) made a pop O(1) in memory, but the pop COUNT is still
    /// quadratic in the block count, and every pop charges one step of the
    /// ambient per-function budget (`verify_budget::budget_exhausted`). MEASURED
    /// on the 2026-10-16 candidate gate (trust 7f3690ed73, which did not carry
    /// this mode): `astream_broker::broker::serve_conn` (1202 blocks) walks
    /// toward a 23.1 M-pop cap per call, the walk runs once per lane that asks
    /// for path guards, and the function's VC generation stopped on the
    /// 64,000,000-step budget (`[stop:steps]`) with EVERY row discarded — while
    /// the published seal (321aaeda75, which carries this mode) collapsed at
    /// 2,000,000 pops and still proved the guard-free obligations. Replayed
    /// through `generate_vcs` on the candidate's MIR of `serve_conn`, one walk
    /// without this mode needs more than 32,000,000 steps; with it, under
    /// 16,000,000.
    ///
    /// What this mode does NOT explain: the 365-652 block bodies whose every VC
    /// timed out against the 120 s function clock on that gate
    /// (`aterm_conformance::measure::scan::scan_frames`, `aterm_forge::check::
    /// report_over`, `aterm_render::compute_dirty_rows`). MEASURED 2026-10-17 on
    /// `scan_frames`: with this mode the walk trips (the function carries the
    /// frontier row) and the function still publishes 21 timeouts and 0 proved
    /// rows in 4,680,000 ms, exactly as without it. Those timeouts come from the
    /// lanes sharing one per-function clock after VC generation, not from the
    /// walk.
    ///
    /// Mode 3 can only fire where mode 2's cap is above it: 2,000,000 pops is
    /// below `16n^2 + 16n + 4096` exactly when `n > 353`, so it stops only bodies
    /// whose walk was allowed more than two million pops.
    FrontierBudgetTripped,
}

/// What the path walk was able to say about each block's reachability.
///
/// `paths` is exactly what [`v2_build_path_guard_map`] always produced — a
/// collapsed block keeps its single UNGUARDED path. The repair rides in the
/// extra fields, so every VC-producing module that consumes the raw map is
/// unaffected and only the lane that enforces the collapse invariant sees the
/// restored condition.
pub(super) struct PathGuardAnalysis {
    /// Root-to-block guard paths; a degraded block holds `vec![Vec::new()]`.
    pub(super) paths: std::rc::Rc<FxHashMap<BlockId, Vec<Vec<(BlockId, GuardCondition)>>>>,
    /// Which collapse (if any) the walk took.
    pub(super) collapse: PathGuardCollapse,
    /// The blocks whose path condition was DEGRADED by a collapse — the ones
    /// whose `paths` entry lowers to an unconditional `true`.
    pub(super) degraded: FxHashSet<BlockId>,
    /// For each degraded block, what the in-edge summary was able to say about
    /// reaching it. See [`ReachSummary`] — the three answers are three
    /// different things and the invariant treats them differently.
    pub(super) reachability: FxHashMap<BlockId, ReachSummary>,
}

/// What can be said about reaching a block whose path condition was DEGRADED.
///
/// The distinction between the last two is the whole reason the invariant does
/// not weaken UB detection: `Unconditional` is POSITIVE information (the block
/// really is reachable on every execution that gets that far), while
/// `Unavailable` is the ABSENCE of information. Only absence may force a
/// decline; positive information must still be allowed to refute.
#[derive(Debug, Clone)]
pub(super) enum ReachSummary {
    /// `⋁ guard(e)` over every CFG in-edge — a real condition, and a theorem
    /// about any execution that reaches the block.
    ///
    /// # What it costs: a size RULE, and why there is no budget
    ///
    /// The enforcement step splices this through the SAME lowering an ordinary
    /// path list takes: one single-guard path per in-edge, which
    /// `v2_formula_with_path_guards_recorded` lowers to
    /// `Or([And([g_e, body..]) ..])` — the body CLONED once per in-edge, and
    /// FLATTENED into each `And` when it is itself an `And`. It is not conjoined
    /// as a single undistributed `Or([g_e ..])` fact.
    ///
    /// Read the size straight off that lowering:
    ///
    /// ```text
    /// nodes(row) = 1 + SUM over in-edges e of ( |g_e| + |body| )
    ///            = 1 + in_degree * ( |g_e| + |body| )     when the guards are uniform
    /// ```
    ///
    /// — `1` for the `Or`, and per disjunct `1` for the `And` plus `|g_e|` plus
    /// the `|body| - 1` conjuncts left once the body's own `And` node is
    /// flattened away. (A body that is not an `And` is pushed whole instead, so
    /// it costs `1 + |g_e| + |body|` per in-edge.)
    ///
    /// `body` here is the row's formula AT THIS POINT, not the emitter's bare
    /// violation core: between the content-free capture step and this splice
    /// `generate_v2_safety_vcs_impl_with_origins_checked` conjoins its fact sets onto
    /// `vc.formula` in place, and whatever they conjoined is what gets cloned.
    /// So the per-in-edge slope is `|g_e| + |accumulated fact set|` — it belongs
    /// to the BODY, is constant in the in-degree, and is not a property of this
    /// mechanism. `path_guard_collapse_tests` asserts the resulting linearity on
    /// several bodies and requires their slopes to differ, so no one slope can be
    /// read as a law.
    ///
    /// There is no budget on the in-degree because a budget could only convert a
    /// REFUTED row into a decline, and every one of those rows is a real bug
    /// found. Where the solver gives up is its limit, not a policy — it is
    /// reached by TRYING, which is the difference that matters.
    Guards(Vec<(BlockId, GuardCondition)>),
    /// The disjunction is `true`. Either the block has an UNGUARDED in-edge
    /// (`Goto`, a `Call`/`Assert` continuation, an unwind edge), or it is the
    /// ENTRY, which is reached without traversing any edge at all. The collapsed
    /// unguarded path already IS this condition, so there is nothing to restore
    /// — and a content-free row of such a block must still REFUTE, because
    /// "reachable unconditionally" is exactly what a reachable trap looks like:
    /// a `Terminator::Unreachable` a `Goto` walks into.
    Unconditional,
    /// No summary was produced: the block carries no in-edge the summary can
    /// see, or its in-edge list came back EMPTY (an empty `Or` is `false`, which
    /// would vacuously prove every row). This is the ABSENCE the invariant
    /// declines on, and — since the in-degree budget was removed — the ONLY
    /// thing that reaches it. There is no size at which a block with real
    /// in-edge guards lands here; see [`Guards`](ReachSummary::Guards).
    Unavailable,
}

pub(super) fn v2_build_path_guard_map(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Vec<(BlockId, GuardCondition)>>> {
    let paths = v2_analyze_path_guards(func).paths;
    std::rc::Rc::unwrap_or_clone(paths)
}

/// The walk's FRONTIER budget: pops. See [`PathGuardCollapse::FrontierBudgetTripped`]
/// for why a pop cap that is a CONSTANT is needed on top of mode 2's `16n^2` one.
///
/// After the prefix sharing ([`SharedPath`]) one pop allocates at most one
/// [`PathNode`] per pushed successor, so the bound is a memory bound and a step
/// bound at once: `MAX_PATH_WALK_STEPS` pops charge at most that many steps of
/// the ambient per-function budget, per call of the walk.
///
/// MEASURED 2026-09-09 over the 1269 `VerifiableFunction`s `-Ztrust-dump=mir`
/// extracts from `ay-arrays` (seal-line 28aee49dd8, re-run by a second reader
/// with identical digests): **1263 of them COMPLETE the walk** (mode 2 never
/// trips), and the largest of those spends **389_003 pops** (`check_self_store`,
/// 165 blocks; it saturates a block — mode 1 — which lets the walk run on). Of
/// the 1263, the 1138 that reach no cap at all spend at most 386 pops. The
/// remaining six trip mode 2 and so already return the all-`true` map. The 5.1x
/// margin over 389_003 is the whole safety story of this constant: raise it,
/// never lower it, without re-running that census.
pub(super) const MAX_PATH_WALK_STEPS: usize = 2_000_000;

/// The walk's FRONTIER budget: live queue entries. Needed alongside
/// [`MAX_PATH_WALK_STEPS`] because ONE pop of a wide `SwitchInt` pushes one entry
/// per arm, so a pop bound alone does not bound the queue. Observed maximum over
/// the same 1269-function census, among the walks that COMPLETE: **21_799**
/// entries (`check_self_store`), a 22.9x margin.
pub(super) const MAX_PATH_WALK_QUEUE: usize = 500_000;

/// Visited-block set for `v2_analyze_path_guards` simple-path cycle detection.
/// Uses an inline `[u64; 4]` bitset when `num_blocks <= 256` (zero heap allocations,
/// zero `Rc` refcount churn, O(1) membership and insert) and falls back to
/// `SharedPath<BlockId>` on larger CFGs.
#[derive(Clone)]
enum VisitedBlocks {
    Bits([u64; 4]),
    Chain(SharedPath<BlockId>),
}

impl VisitedBlocks {
    #[inline]
    fn empty(num_blocks: usize) -> Self {
        if num_blocks <= 256 { Self::Bits([0; 4]) } else { Self::Chain(None) }
    }

    #[inline]
    fn contains(&self, block_id: BlockId) -> bool {
        match self {
            Self::Bits(words) => {
                let word_idx = block_id.0 >> 6;
                let mask = 1u64 << (block_id.0 & 63);
                words.get(word_idx).is_some_and(|w| (w & mask) != 0)
            }
            Self::Chain(chain) => path_contains(chain, &block_id),
        }
    }

    #[inline]
    fn insert(&self, block_id: BlockId) -> Self {
        match self {
            Self::Bits(words) => {
                let mut next = *words;
                let word_idx = block_id.0 >> 6;
                if let Some(w) = next.get_mut(word_idx) {
                    *w |= 1u64 << (block_id.0 & 63);
                }
                Self::Bits(next)
            }
            Self::Chain(chain) => Self::Chain(path_cons(chain, block_id)),
        }
    }
}

/// The full walk: the path map, which collapse (if any) it took, and — for every
/// block a collapse DEGRADED — what can still be said about reaching it.
pub(super) fn v2_analyze_path_guards(func: &VerifiableFunction) -> PathGuardAnalysis {
    // Trust S2c: each guard is paired with the SOURCE BlockId of the branch that
    // created it, so `v2_formula_with_path_guards` can version the guard's
    // in-block reads at that block (a dead-branch guard `k >= 4` over `k = n%4`
    // becomes `k#sSRC` to match the renamed body) while entry-param reads stay bare.
    let mut result: FxHashMap<BlockId, Vec<Vec<(BlockId, GuardCondition)>>> = FxHashMap::default();
    if func.body.blocks.is_empty() {
        return PathGuardAnalysis {
            paths: std::rc::Rc::new(result),
            collapse: PathGuardCollapse::None,
            degraded: FxHashSet::default(),
            reachability: FxHashMap::default(),
        };
    }

    let n = func.body.blocks.len();
    let cap = n.saturating_mul(n).saturating_add(n).saturating_mul(16).saturating_add(4096);
    let mut steps = 0usize;
    let mut saturated_blocks: FxHashSet<BlockId> = FxHashSet::default();
    // The frontier carries SHARED prefixes (`SharedPath`) for guards and an inline
    // bitset (`VisitedBlocks::Bits`) for visited blocks when `n <= 256` (falling back
    // to `SharedPath<BlockId>` when `n > 256`). Same paths, same order, same output.
    let mut queue: std::collections::VecDeque<(
        BlockId,
        SharedPath<(BlockId, GuardCondition)>,
        VisitedBlocks,
    )> = std::collections::VecDeque::from([(BlockId(0), None, VisitedBlocks::empty(n))]);

    // Every whole-function collapse returns the SAME thing: one unguarded path
    // for every block, every block degraded, and the in-edge disjunction
    // restored for all of them. Only the reported CAUSE differs, so the
    // construction is named once here rather than written out at each `return`.
    let collapse_whole_function = |collapse: PathGuardCollapse| -> PathGuardAnalysis {
        let collapsed_map: FxHashMap<BlockId, Vec<Vec<(BlockId, GuardCondition)>>> =
            func.body.blocks.iter().map(|block| (block.id, vec![Vec::new()])).collect();
        let every_block: FxHashSet<BlockId> =
            func.body.blocks.iter().map(|block| block.id).collect();
        let reachability = v2_reachability_for_collapsed(func, &every_block);
        PathGuardAnalysis {
            paths: std::rc::Rc::new(collapsed_map),
            collapse,
            degraded: every_block,
            reachability,
        }
    };

    // Retained path-guard entries, counted where they are actually held: every
    // guard stored in `result` and every guard sitting in a pending queue entry.
    // See `MAX_TOTAL_PATH_GUARD_ENTRIES`.
    let mut retained_entries = 0usize;
    while let Some((block_id, path_guards, path_blocks)) = queue.pop_front() {
        steps += 1;
        retained_entries = retained_entries.saturating_sub(path_len(&path_guards));
        // Trust (L0 termination guarantee): consult the AMBIENT per-function
        // budget alongside this walk's own local `cap`. Measured 2026-08-31,
        // `budget_exhausted()` appeared in exactly ONE file of this crate
        // (`contracts.rs`) and in none of the VC-generation walks the budget
        // docs named — so no timeout could bound this enumeration. Exhaustion
        // here takes the EXISTING `BudgetTripped` collapse, a state this
        // function already reaches and `path_guard_collapse_tests` already
        // pins: every block degrades to the unguarded `[Vec::new()]` path, which
        // strictly REMOVES hypotheses and so can only turn a PROVE into a FAIL.
        if steps > cap
            || retained_entries > MAX_TOTAL_PATH_GUARD_ENTRIES
            || trust_types::verify_budget::budget_exhausted()
        {
            // COLLAPSE MODE 2 — the GLOBAL STEP BUDGET. This is the SECOND path
            // to an unguarded block formula, and it is the more dangerous one:
            // mode 1 (`MAX_PATHS_PER_BLOCK`, below) collapses the blocks that
            // actually saturated, while this collapses EVERY block of the
            // function at once, including blocks reached by a single guarded
            // edge. Repairing only mode 1 therefore left the identical false
            // REFUTATION one step further out, on a cliff a body crosses by
            // growing — see `path_guard_collapse_tests`, which pins where the
            // two modes hand over. Run the SAME repair here, over every block —
            // sound by the same theorem, and fail-closed per block exactly as it
            // is below.
            return collapse_whole_function(PathGuardCollapse::BudgetTripped);
        }
        // COLLAPSE MODE 3 — the FRONTIER budget. Checked AFTER mode 2 so that a
        // body small enough for mode 2's `16n^2` cap to bind still reports mode
        // 2, which is what the fixtures in `path_guard_collapse_tests` pin. The
        // degradation is mode 2's, so it is sound by the same theorem: every
        // block's path guards are REMOVED (hypotheses only ever disappear, which
        // can turn a PROVE into a FAIL and never the reverse), the in-edge
        // disjunction is restored for every block through the degraded set, and
        // the refutation lane declines on every degraded block
        // (`assert_refutation`, `guard_analysis.degraded`). Reported by
        // `v2_frontier_budget_vc`, the one function-level row
        // `generate_v2_safety_vcs_impl_with_origins_checked` appends when it sees
        // this variant. See `PathGuardCollapse::FrontierBudgetTripped`.
        if steps > MAX_PATH_WALK_STEPS || queue.len() > MAX_PATH_WALK_QUEUE {
            return collapse_whole_function(PathGuardCollapse::FrontierBudgetTripped);
        }
        if block_id.0 >= n {
            continue;
        }
        if path_blocks.contains(block_id) {
            continue;
        }
        let path_blocks = path_blocks.insert(block_id);

        let block = &func.body.blocks[block_id.0];

        // Trust #soundness: kill an inherited DOMINATING control-flow guard
        // (`if n <= K`) that THIS block invalidates by reassigning one of its
        // free variables. Once a block does `n = BIG`, the guard `n <= K` is
        // STALE — conjoined onto a VC here (or downstream) it contradicts the
        // live `n == BIG` block-def, making the violation formula UNSAT, which
        // the "SAT iff violation" convention reads as PROVED: a real OOM (e.g.
        // `if n <= 100 { n = 1<<30; Vec::with_capacity(n) }`) is false-PROVEd
        // safe. This is the hunt-6/7/8 stale-fact-contradiction class for
        // path guards, which `build_semantic_guard_map` already closes for
        // semantic facts; mirror its discipline. Statement (+ set-discriminant)
        // redefs kill BEFORE recording, so this block's own VCs do not see the
        // stale guard; the terminator kill is applied only to guards threaded
        // to successors (the terminator runs after this block's VCs). Dropping a
        // guard is monotone-sound — it can only turn a PROVE into a FAIL, never
        // the reverse — and a legitimate guard with no reassignment is retained.
        // Trust S2c: the PATH-GUARD kill is DELETED — replaced by the EXEMPTION.
        // Each path guard is conjoined onto a VC AFTER the whole-VC rename
        // (`v2_formula_with_path_guards` now runs post-rename), so a guard's bare
        // ENTRY-param read (`n` in `if n <= K`) stays bare and is name-disjoint from
        // a reassigned body read (`n#s2_0`), instead of being dropped.

        let paths = result.entry(block_id).or_default();
        if saturated_blocks.contains(&block_id) {
            // Already weakened to an unguarded block formula.
        } else if paths.len() < MAX_PATHS_PER_BLOCK {
            retained_entries = retained_entries.saturating_add(path_len(&path_guards));
            // The ONLY O(depth) copy left, and it happens once per RECORDED
            // path rather than once per queue push.
            paths.push(path_to_vec(&path_guards));
        } else {
            retained_entries =
                retained_entries.saturating_sub(paths.iter().map(Vec::len).sum::<usize>());
            paths.clear();
            paths.push(Vec::new());
            saturated_blocks.insert(block_id);
        }

        // Trust S2c: the terminator part of the PATH-GUARD kill is also DELETED —
        // the terminator-aware OUT token (`s{b}_t`) + the exemption keep a guard over
        // a Call-dest-reassigned name name-disjoint from the post-call successor read.
        let succ_guards = path_guards;

        for guarded in block.terminator.discovered_clauses(block_id) {
            if let trust_types::ClauseTarget::Block(target) = guarded.target {
                // One node, prefix shared. `path_blocks.clone()` is an `Rc`
                // refcount bump, not a copy of the visited-block list.
                let next_guards = path_cons(&succ_guards, (block_id, guarded.guard));
                // Charge the NODE this push allocates. Under sharing the
                // frontier's cost is the number of nodes, not the sum of the
                // path lengths, which is the whole point of the change.
                retained_entries = retained_entries.saturating_add(1);
                queue.push_back((target, next_guards, path_blocks.clone()));
            }
        }
        for target in block.terminator.unguarded_successors() {
            // An unguarded edge extends no guard list at all, so this shares
            // BOTH prefixes outright — two refcount bumps, zero allocation.
            queue.push_back((target, succ_guards.clone(), path_blocks.clone()));
        }
    }

    // COLLAPSE MODE 1 — per-block saturation. Same repair, same theorem.
    let reachability = v2_reachability_for_collapsed(func, &saturated_blocks);

    let collapse = if saturated_blocks.is_empty() {
        PathGuardCollapse::None
    } else {
        PathGuardCollapse::SaturatedBlocks
    };
    PathGuardAnalysis {
        paths: std::rc::Rc::new(result),
        collapse,
        degraded: saturated_blocks,
        reachability,
    }
}

/// Trust (collapse false REFUTATION): the weakest still-valid reachability
/// condition for every block in `collapsed`.
///
/// # The defect
///
/// [`v2_build_path_guard_map`] has THREE collapse modes, and each leaves a block
/// with ONE UNGUARDED path whose term lowers to an unconditional `true` — i.e.
/// NO reachability condition at all:
///
///  1. a block reached by more than `MAX_PATHS_PER_BLOCK` routes;
///  2. the whole function, when the global step budget trips;
///  3. the whole function, when the walk's FRONTIER budget trips
///     ([`MAX_PATH_WALK_STEPS`] / [`MAX_PATH_WALK_QUEUE`]).
///
/// This repair is keyed on the DEGRADED SET, not on a list of modes, which is
/// why mode 3 needed no change here: a new mode arrives already covered.
///
/// For an obligation whose formula carries its own violation condition that is
/// merely imprecise. For an obligation whose formula IS `Bool(true)` the path
/// condition is the ENTIRE content of the row, so the collapse turns "prove you
/// cannot get here" into an unconditional accusation of correct code. The
/// extracted-MIR fixtures in `tests/data` sit on both cliffs, and
/// `tests/path_guard_collapse_repair_real_mir.rs` plus
/// `tests/coroutine_resume_state_global_fact_real_mir.rs` are what keep correct
/// bodies from being refuted there.
///
/// # Which rows have that shape — derived, not assumed
///
/// The earlier revision of this repair was scoped to `Terminator::Unreachable`
/// on the rationale that "for any other obligation the collapse is only
/// imprecision, since the row keeps its own violation condition". That rationale
/// is FALSE, and the `ResumedAfter*` coroutine sentinel is the counterexample:
/// `safety.rs`'s `AssertMessage::ResumedAfter{Return,Panic,Drop}` arm builds its
/// formula from `v2_assert_failure_formula(cond = const false, expected = true)`,
/// which is the constant `true` — byte-identical in content to the `Unreachable`
/// row, and refuting under collapse for byte-identical reasons. Any `Assert`
/// whose condition is a constant, and any future row whose violation formula is
/// a tautology, is in the same class. That class is recognised STRUCTURALLY by
/// [`v2_violation_is_content_free`], never by a list of row kinds a new kind can
/// fall off.
///
/// # The theorem
///
/// An execution that reaches B arrived along some CFG in-edge of B, so the
/// disjunction of the in-edges' own branch conditions holds at B. It is strictly
/// WEAKER than the un-collapsed per-path map (which conjoins EVERY guard along a
/// path; this keeps only the last one), and strictly STRONGER than the `true` it
/// replaces — so it can only move a row from REFUTED toward PROVED, and only by
/// a fact that is true of every real execution.
///
/// # Why it is returned rather than written into the path map
///
/// Writing it back into the map would hand it to EVERY row of a collapsed block
/// and to every other consumer of the map.
/// `v2_formula_with_path_guards_recorded` lowers a path list to
/// `Or([And([g_e, body]) ..])`, which CLONES THE WHOLE BODY once per in-edge (see
/// the size rule on [`ReachSummary::Guards`]), and on a row that already carries
/// its own violation condition that is pure cost for a precision gain the row
/// does not need — cost that pushes a genuine, refuted overflow into a decline.
/// A real violation demoted to a decline is the second defect class, and paying
/// for a false-refutation fix with it is not a trade worth making;
/// `tests/path_guard_collapse_cost_real_mir.rs` is the guard on that side.
///
/// Returned separately, the condition reaches ONLY the rows the invariant needs
/// it for (`v2_violation_is_content_free`), and every other consumer of the path
/// map — and every content-carrying row of the safety lane itself — is
/// unaffected.
///
/// # The three answers, and why two of them are not the same
///
///  * [`ReachSummary::Guards`] — every in-edge carries a guard, so the
///    disjunction is a real condition.
///  * [`ReachSummary::Unconditional`] — the ENTRY block, or a block with an
///    UNGUARDED in-edge. `v2_build_in_edge_guard_map` records `None` for both,
///    and `None` there does NOT mean "unknown": it means the disjunction is
///    `true`. That is POSITIVE information — the block is reachable on every
///    execution that gets to the branch — so nothing is restored AND the row
///    must be left able to refute. Collapsing this together with genuine absence
///    would bless a `Terminator::Unreachable` a `Goto` walks into, which is real
///    UB and the one thing this whole area may never do.
///  * [`ReachSummary::Unavailable`] — the block has no in-edge the summary can
///    account for, or its edge list is EMPTY. Genuine ABSENCE, and the only case
///    the invariant declines on. NO in-degree reaches it: a SIZE-based decline
///    was tried and removed, because "large" is not "undecidable" (see
///    [`ReachSummary::Guards`]).
fn v2_reachability_for_collapsed(
    func: &VerifiableFunction,
    collapsed: &FxHashSet<BlockId>,
) -> FxHashMap<BlockId, ReachSummary> {
    let mut restored: FxHashMap<BlockId, ReachSummary> = FxHashMap::default();
    if collapsed.is_empty() {
        return restored;
    }
    let mut in_edges = v2_build_in_edge_guard_map(func, collapsed);
    for block_id in collapsed {
        let summary = match in_edges.remove(block_id) {
            // The disjunction is `true` — entry, or an unguarded in-edge.
            Some(None) => ReachSummary::Unconditional,
            // A real condition, at ANY in-degree. There is deliberately no size
            // budget here: a big disjunction is inconvenient, not undecidable,
            // and declining on size demotes genuinely reachable UB to Unknown.
            Some(Some(edges)) if !edges.is_empty() => ReachSummary::Guards(edges),
            // An empty edge list (an empty `Or` is `false` and would vacuously
            // prove every row — refused explicitly), or no entry in the map at
            // all.
            _ => ReachSummary::Unavailable,
        };
        restored.insert(*block_id, summary);
    }
    restored
}

/// One branch condition per CFG IN-EDGE of each block: `Some(edges)` when EVERY
/// in-edge of the block carries a guard (so `⋁ guard(e)` is a theorem about any
/// execution that reaches it), `None` when the summary is unavailable and the
/// caller must keep its unguarded path.
///
/// `None` is recorded for the ENTRY block unconditionally (it is reachable
/// without traversing any edge, so a back edge into it is not the only way to
/// arrive) and for any block with at least one UNGUARDED in-edge (that edge's
/// condition is `true`, so the disjunction carries no information). A block with
/// no in-edge at all is simply ABSENT from the map, which the caller also treats
/// as unavailable — never as the empty disjunction `false`, which would
/// vacuously prove every row of an unreachable block.
///
/// COMPLETENESS is what makes the disjunction a theorem, and it holds by
/// construction: the two enumerations below — `discovered_clauses` and
/// `unguarded_successors` — are exactly the pair [`v2_build_path_guard_map`]
/// itself traverses, so no in-edge can exist that this map misses but the path
/// walk found. `ClauseTarget::Panic` is not a block and contributes no in-edge.
fn v2_build_in_edge_guard_map(
    func: &VerifiableFunction,
    collapsed: &FxHashSet<BlockId>,
) -> FxHashMap<BlockId, Option<Vec<(BlockId, GuardCondition)>>> {
    let mut map: FxHashMap<BlockId, Option<Vec<(BlockId, GuardCondition)>>> =
        FxHashMap::with_capacity_and_hasher(collapsed.len(), Default::default());
    // Both spellings of "the entry": the walk's root `BlockId(0)` and the first
    // declared block, which coincide on well-formed MIR but need not on a
    // hand-built or adversarial body.
    let first = func.body.blocks.first().map(|b| b.id);
    if collapsed.contains(&BlockId(0)) {
        map.insert(BlockId(0), None);
    }
    if let Some(first_id) = first
        && first_id != BlockId(0)
        && collapsed.contains(&first_id)
    {
        map.insert(first_id, None);
    }
    let is_entry = |id: BlockId| id == BlockId(0) || first == Some(id);
    for block in &func.body.blocks {
        for target in block.terminator.unguarded_successors() {
            if !collapsed.contains(&target) || is_entry(target) {
                continue;
            }
            map.insert(target, None);
        }
        for guarded in block.terminator.discovered_clauses(block.id) {
            let trust_types::ClauseTarget::Block(target) = guarded.target else { continue };
            if !collapsed.contains(&target) || is_entry(target) {
                continue;
            }
            if let Some(edges) = map.entry(target).or_insert_with(|| Some(Vec::new())) {
                edges.push((block.id, guarded.guard));
            }
        }
    }
    map
}

// ---------------------------------------------------------------------------
// THE COLLAPSE INVARIANT
// ---------------------------------------------------------------------------
// Three collapse cliffs exist in `v2_build_path_guard_map` — the per-block path
// cap, the global step budget, and the frontier budget — and the first two each
// produced the IDENTICAL false REFUTATION, each was closed by a local repair, and
// the next reviewer got past each repair. Patching another cap would only move
// the cliff. The third is why the invariant below is keyed on
// `degraded`/`ReachSummary` rather than on a list of collapse modes: adding
// `FrontierBudgetTripped` required NO change here.
//
// The root cause is a missing INVARIANT, stated once and enforced at the single
// point where such a row is decided:
//
//     A row whose own violation formula has NO CONTENT — whose entire meaning is
//     "control reaches this block" — must be reported UNKNOWN, never REFUTED,
//     whenever the path condition is ABSENT or DEGRADED.
//
// "I have no reachability information" is not "this is reachable". The invariant
// subsumes every known collapse mode and any future one, because it is keyed on
// the DEGRADATION, not on the mechanism that caused it.
//
// It must not weaken detection where the path condition IS present and sound:
// only degradation forces the decline. A block that is genuinely reachable with
// no guard at all keeps a real, non-degraded EMPTY path in the map, and that is
// INFORMATION ("reachable unconditionally") — such a row still refutes, which is
// what keeps a reachable `unreachable!()` a refutation.

/// Is `f` valid — true under every assignment? A conservative SYNTACTIC test:
/// it may answer `false` for a formula that is semantically valid, never `true`
/// for one that is not.
fn v2_formula_is_tautology(f: &Formula) -> bool {
    match f {
        Formula::Bool(true) => true,
        Formula::Not(inner) => v2_formula_is_contradiction(inner),
        Formula::And(parts) => parts.iter().all(v2_formula_is_tautology),
        Formula::Or(parts) => parts.iter().any(v2_formula_is_tautology),
        Formula::Implies(_, rhs) => v2_formula_is_tautology(rhs),
        _ => false,
    }
}

/// The dual of [`v2_formula_is_tautology`]: unsatisfiable under every
/// assignment, decided syntactically and conservatively.
fn v2_formula_is_contradiction(f: &Formula) -> bool {
    match f {
        Formula::Bool(false) => true,
        Formula::Not(inner) => v2_formula_is_tautology(inner),
        Formula::And(parts) => parts.iter().any(v2_formula_is_contradiction),
        Formula::Or(parts) => parts.iter().all(v2_formula_is_contradiction),
        _ => false,
    }
}

/// Does this row carry NO violation condition of its own?
///
/// Recognised STRUCTURALLY, from the formula the emitter built, so a row kind
/// added later is classified by what its formula says rather than by whether
/// someone remembered to add it to a list. `formula` must be the row's own
/// violation as first emitted — before any fact, guard or precondition is
/// conjoined onto it — because those conjuncts are satisfiable facts, not
/// content, and would mask the property.
///
/// # The class is wider than two special rows
///
/// It is worth knowing the blast radius, because "just the `Unreachable` row and
/// the coroutine sentinel" invites someone to re-scope the invariant by row kind.
/// `v2_build_terminator_vc` (`overflow_vc.rs`) builds ONE `VerificationCondition`
/// for every terminator it recognises and hands it the literal
/// `formula: Formula::Bool(true)` — the kind varies, the formula does not — so
/// every panic SITE that lane recognises is in this class, `Assertion` rows
/// included, not only the `VcKind::Unreachable` ones.
///
/// `safety.rs` itself reaches the class by a second spelling,
/// `v2_assert_failure_formula(cond = const false, expected = true)`, which is
/// `Not(Bool(false))`: any `Terminator::Assert` whose condition is statically the
/// failing value, including rustc's `ResumedAfter{Return,Panic,Drop}` coroutine
/// protocol sentinel.
///
/// None of that is a list the recognizer consults. The test is STRUCTURAL, which
/// is the design working: it catches both spellings without naming either, and it
/// will catch the next one. `path_guard_collapse_tests::the_collapse_invariant`
/// pins the spellings that exist today, and the negatives.
///
/// # Why this is the STRICT test
///
/// The `ResumedAfter*` arm wraps its core in `v2_formula_with_block_defs`, so a
/// definitional prefix — `And([def.., Not(Bool(false))])` — is a shape this test
/// deliberately answers `false` for, leaving such a row on the ordinary splice.
///
/// Loosening the test to look THROUGH a prefix of definitional equalities was
/// tried and rejected, because it costs precision in the other direction: a row
/// whose real violation condition happens to be an equality (`DivisionByZero` is
/// literally `Eq(divisor, 0)`) must never be mistaken for a row with nothing to
/// say, because the invariant would then DECLINE a real bug when no summary is
/// available. Misclassifying toward "content-free" is one defect class;
/// misclassifying AWAY from it is the other, and it is not merely a loss of
/// precision: the row then takes the ordinary splice, and a degraded block's
/// path list is the single EMPTY path, which
/// [`v2_formula_with_path_guards_recorded`] returns unchanged
/// (`PathGuardTerm::Raw`). No reachability condition is attached at all — which
/// is exactly the false refutation this invariant exists to stop. Neither
/// direction is free, so the test states precisely the property it needs and
/// nothing more.
pub(super) fn v2_violation_is_content_free(formula: &Formula) -> bool {
    v2_formula_is_tautology(formula)
}

/// The DECLINE this invariant makes when a content-free row's path condition is
/// degraded and no sound reachability summary is available.
///
/// It is an `UnsupportedMir` proof-gap row, the same fail-closed representation
/// this file already uses for an unmodeled safety assert: the router
/// preclassifies it to Unknown, so the obligation is neither proved nor refuted,
/// and — this is the part that matters — the row is still EMITTED. Dropping it
/// instead would be a silently unemitted obligation, which is the other way to
/// ship a bug.
fn v2_path_condition_degraded_vc(
    func: &VerifiableFunction,
    block_id: BlockId,
    vc: &VerificationCondition,
    collapse: PathGuardCollapse,
    reason: &str,
) -> VerificationCondition {
    unsupported_mir_vc(
        func,
        "PathConditionDegraded".to_string(),
        format!(
            "bb{}: the row `{:?}` carries no violation condition of its own, so its \
             entire meaning is the block's reachability; the path-guard walk degraded \
             that condition ({collapse:?}) and {reason}. Reporting an explicit proof \
             gap: absent reachability information is not evidence of reachability.",
            block_id.0, vc.kind,
        ),
        vc.location.clone(),
    )
}

pub(super) fn v2_formula_with_path_guards(
    func: &VerifiableFunction,
    // Trust (lane-A CSE): `StmtVersionCtx` is a pure deterministic function of the
    // immutable `func`, so it is built ONCE per function (where `guard_paths_map`
    // is) and threaded in here by reference — rather than rebuilt on every VC.
    // Verdict-identical: the entry map is byte-identical to `StmtVersionCtx::build(func)`,
    // so `version_rename_at` output and every emitted VC are unchanged.
    sv: &StmtVersionCtx,
    // Trust (PATH-GUARD-VALUE-1): the block the guarded row lives in — the paths in
    // `guard_paths` end there. A guard keeps its reaching-set spelling only where that
    // spelling names, at this block, the value the guard tested
    // (`guard_value_spelling`).
    at: BlockId,
    guard_paths: &[Vec<(BlockId, GuardCondition)>],
    formula: Formula,
) -> Formula {
    v2_formula_with_path_guards_inner(func, sv, at, guard_paths, formula, false).0
}

/// Refutation-polarity counterpart of [`v2_formula_with_path_guards`].
///
/// The ordinary path helper may weaken an unmodeled guard to `true`, which is
/// sound when guards are proof hypotheses but can manufacture a SAT witness.
/// This variant accepts only guards with complete lowering and returns `None`
/// on an absent source block, an unmodeled guard, or an empty path set.  The
/// caller must separately reject path-map collapse, because a collapsed empty
/// guard path is indistinguishable from a genuinely unconditional path here.
///
/// Trust (PATH-GUARD-VALUE-1): it also returns `None` when a guard's reaching-set
/// spelling would name, at `at`, a value other than the one the guard tested
/// (`guard_value_spelling::guard_needs_value_spelling`). The proof polarity gives such
/// a read a guard-local name, which WEAKENS the path condition — harmless for a proof,
/// but a weakened path condition can manufacture a witness, so this lane declines.
fn operand_place_eq(a: &Operand, b: &Operand) -> bool {
    match (a, b) {
        (Operand::Copy(pa), Operand::Copy(pb)) | (Operand::Move(pa), Operand::Move(pb)) => pa == pb,
        _ => false,
    }
}

pub(super) fn guard_cache_key(src: BlockId, g: &GuardCondition) -> Option<(BlockId, u8, u128)> {
    match g {
        GuardCondition::SwitchIntMatch { discr: Operand::Copy(_) | Operand::Move(_), value } => {
            Some((src, 0, *value))
        }
        GuardCondition::SwitchIntOtherwise {
            discr: Operand::Copy(_) | Operand::Move(_),
            excluded_values,
        } => Some((src, 1, excluded_values.len() as u128)),
        GuardCondition::AssertHolds { cond: Operand::Copy(_) | Operand::Move(_), expected } => {
            Some((src, 2, u128::from(*expected)))
        }
        _ => None,
    }
}

pub(super) fn guard_condition_eq(a: &GuardCondition, b: &GuardCondition) -> bool {
    match (a, b) {
        (
            GuardCondition::SwitchIntMatch { discr: da, value: va },
            GuardCondition::SwitchIntMatch { discr: db, value: vb },
        ) => va == vb && operand_place_eq(da, db),
        (
            GuardCondition::SwitchIntOtherwise { discr: da, excluded_values: ea },
            GuardCondition::SwitchIntOtherwise { discr: db, excluded_values: eb },
        ) => ea == eb && operand_place_eq(da, db),
        (
            GuardCondition::AssertHolds { cond: ca, expected: ea },
            GuardCondition::AssertHolds { cond: cb, expected: eb },
        ) => ea == eb && operand_place_eq(ca, db_or_cb(cb)),
        _ => false,
    }
}

#[inline(always)]
fn db_or_cb(op: &Operand) -> &Operand {
    op
}

pub(super) fn v2_formula_with_refutation_path_guards(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    at: BlockId,
    guard_paths: &[Vec<(BlockId, GuardCondition)>],
    formula: Formula,
) -> Option<Formula> {
    if guard_paths.is_empty() {
        return None;
    }
    if guard_paths.len() == 1 && guard_paths[0].is_empty() {
        return Some(formula);
    }

    let mut terms = Vec::with_capacity(guard_paths.len());
    let mut formula_opt = Some(formula);
    let mut edge_cache: FxHashMap<(BlockId, u8, u128), (&GuardCondition, Formula)> =
        FxHashMap::default();
    let use_edge_cache = guard_paths.len() > 1;
    let formula_conjunct_count = match formula_opt.as_ref() {
        Some(Formula::And(inner)) => inner.len(),
        _ => 1,
    };
    for (idx, path) in guard_paths.iter().enumerate() {
        if path.is_empty() {
            let row_formula = if idx + 1 == guard_paths.len() {
                formula_opt.take()?
            } else {
                formula_opt.as_ref()?.clone()
            };
            terms.push(row_formula);
            continue;
        }

        let mut conjuncts = Vec::with_capacity(path.len() + formula_conjunct_count);
        for (source, guard) in path {
            let cache_key = use_edge_cache.then(|| guard_cache_key(*source, guard)).flatten();
            if let Some(key) = cache_key
                && let Some((cached_g, cached_f)) = edge_cache.get(&key)
                && guard_condition_eq(cached_g, guard)
            {
                conjuncts.push(cached_f.clone());
                continue;
            }
            let source_block =
                func.body.blocks.get(source.0).filter(|block| block.id == *source)?;
            let gf = guards::guard_to_refutation_formula(func, guard)?;
            if super::guard_value_spelling::guard_needs_value_spelling(func, sv, &gf, *source, at) {
                return None;
            }
            let renamed = version_rename_owned_at(gf, sv, func, *source, source_block.stmts.len());
            if let Some(key) = cache_key {
                edge_cache.entry(key).or_insert_with(|| (guard, renamed.clone()));
            }
            conjuncts.push(renamed);
        }
        let row_formula = if idx + 1 == guard_paths.len() {
            formula_opt.take()?
        } else {
            formula_opt.as_ref()?.clone()
        };
        match row_formula {
            Formula::And(inner) => conjuncts.extend(inner),
            other => conjuncts.push(other),
        }
        terms.push(Formula::And(conjuncts));
    }

    if terms.len() == 1 { terms.pop() } else { Some(Formula::Or(terms)) }
}

/// As [`v2_formula_with_path_guards`], but also returns the per-path terms the
/// obligation recorder records as a [`ObligationWrapper::PathGuardOr`]. Trust: an
/// empty guard list is a `Raw` term (body whole); a non-empty one is a `Guarded`
/// term carrying the SAME version-renamed guard formulas this function conjoins,
/// so the consumer's `Or([per-path term..])` reconstruction — with its `And`-splice
/// of the body — reproduces this formula bit-for-bit.
pub(super) fn v2_formula_with_path_guards_recorded(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    at: BlockId,
    guard_paths: &[Vec<(BlockId, GuardCondition)>],
    formula: Formula,
) -> (Formula, Vec<PathGuardTerm>) {
    v2_formula_with_path_guards_inner(func, sv, at, guard_paths, formula, true)
}

pub(super) fn spell_guard_paths_uncached(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    at: BlockId,
    guard_paths: &[Vec<(BlockId, GuardCondition)>],
) -> Vec<Vec<Formula>> {
    // Trust (2026-09-27, class `v-refuted-unreachable`): the discriminant temps the
    // CSE ties, each rendered through its group's anchor (memoized per function).
    let anchors = super::discriminant_cse_anchor_map(func);
    let mut edge_cache: FxHashMap<(BlockId, u8, u128), (&GuardCondition, Formula)> =
        FxHashMap::default();
    let use_edge_cache = guard_paths.len() > 1;
    let mut out = Vec::with_capacity(guard_paths.len());
    for guards in guard_paths {
        if guards.is_empty() {
            out.push(Vec::new());
            continue;
        }
        let renamed_guards: Vec<Formula> = guards
            .iter()
            .map(|(src, g)| {
                let cache_key = use_edge_cache.then(|| guard_cache_key(*src, g)).flatten();
                if let Some(key) = cache_key
                    && let Some((cached_g, cached_f)) = edge_cache.get(&key)
                    && guard_condition_eq(cached_g, g)
                {
                    return cached_f.clone();
                }
                let gf = guards::guard_to_formula(func, g);
                let gf = render_through_discriminant_cse_anchors(gf, &anchors, |anchor, _sort| {
                    !super::guard_value_spelling::guard_var_needs_value_spelling_at(
                        func, sv, *src, at, anchor,
                    )
                });
                let spelled =
                    super::guard_value_spelling::spell_path_guard_owned(func, sv, gf, *src, at);
                if let Some(key) = cache_key {
                    edge_cache.entry(key).or_insert_with(|| (g, spelled.clone()));
                }
                spelled
            })
            .collect();
        out.push(renamed_guards);
    }
    out
}

fn v2_formula_with_path_guards_inner(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    at: BlockId,
    guard_paths: &[Vec<(BlockId, GuardCondition)>],
    formula: Formula,
    record_path_terms: bool,
) -> (Formula, Vec<PathGuardTerm>) {
    if guard_paths.is_empty() {
        return (formula, Vec::new());
    }
    if guard_paths.len() == 1 && guard_paths[0].is_empty() {
        return (
            formula,
            if record_path_terms { vec![PathGuardTerm::Raw] } else { Vec::new() },
        );
    }
    let mut path_terms: Vec<PathGuardTerm> = if record_path_terms {
        Vec::with_capacity(guard_paths.len())
    } else {
        Vec::new()
    };
    // Trust S2c: version each guard at ITS SOURCE block before conjoining (the
    // facts are conjoined EXEMPT from the whole-VC rename). An IN-BLOCK read in the
    // guard (`k = n%4` in `if k >= 4`) renames to `k#sSRC` and matches the renamed
    // body's `k#sSRC` (so `k>=4 ∧ k<4` is UNSAT → dead branch proved); an
    // ENTRY-param read (`n`) gets `version_token_at == None` and stays BARE, so a
    // stale `n <= 100` is still name-disjoint from a reassigned body `n#s2_0`.
    //
    // Trust (PATH-GUARD-VALUE-1): a token spells a reaching-def SET, not a value, so
    // the source-terminal spelling alone let a loop-head guard pin a value written
    // after it (`match len { 3 => {} _ => return } if c { len = n } buf[len]` PROVED
    // and certified). Each guard is spelled by `guard_value_spelling::spell_path_guard`,
    // which keeps the token exactly where it names, at `at`, the value the guard
    // tested and gives the read a guard-local name everywhere else.
    let mut terms = Vec::with_capacity(guard_paths.len());
    let cached_spelled = sv.spelled_guard_paths_for(func, at, guard_paths);
    let owned_spelled;
    let spelled_slice: &[Vec<Formula>] = match &cached_spelled {
        Some((rc, start, len)) => &rc[*start..*start + *len],
        None => {
            owned_spelled = spell_guard_paths_uncached(func, sv, at, guard_paths);
            &owned_spelled
        }
    };
    if let Some((last_guards, prefix_guards)) = spelled_slice.split_last() {
        for renamed_guards in prefix_guards {
            let row_formula = formula.clone();
            if renamed_guards.is_empty() {
                terms.push(row_formula);
                if record_path_terms {
                    path_terms.push(PathGuardTerm::Raw);
                }
                continue;
            }
            if record_path_terms {
                path_terms.push(PathGuardTerm::Guarded { guards: renamed_guards.clone() });
            }
            let extra_len = match &row_formula {
                Formula::And(inner) => inner.len(),
                _ => 1,
            };
            let mut conj: Vec<Formula> = Vec::with_capacity(renamed_guards.len() + extra_len);
            conj.extend_from_slice(renamed_guards);
            match row_formula {
                Formula::And(inner) => conj.extend(inner),
                other => conj.push(other),
            }
            terms.push(Formula::And(conj));
        }
        if last_guards.is_empty() {
            terms.push(formula);
            if record_path_terms {
                path_terms.push(PathGuardTerm::Raw);
            }
        } else {
            if record_path_terms {
                path_terms.push(PathGuardTerm::Guarded { guards: last_guards.clone() });
            }
            let extra_len = match &formula {
                Formula::And(inner) => inner.len(),
                _ => 1,
            };
            let mut conj: Vec<Formula> = Vec::with_capacity(last_guards.len() + extra_len);
            conj.extend_from_slice(last_guards);
            // Trust: restore R1 recursion inductive-bound fact (regression from 52b31a7d2a,
            // which conjoined same-block statement defs into `formula` BEFORE this splice). When
            // the attributed callsite producer already wrapped `formula` as `And([defs…, ¬P[σ]])`
            // (e.g. an argument temp `Eq(_13, i)` conjoined with the callee-precondition negation),
            // pushing that whole `And` as one nested conjunct BURIES `¬P[σ]` a level deep. The R1
            // discharge gate (`is_admissible_caller_discharge`) and the inductive-step sanity check
            // both require `¬P[σ]` to be a DIRECT conjunct of a flat `And`, so a GUARDED recursive
            // call (`if n > 0 { walk(a, n-1, i) }`) then fails to certify (CallerFormulaMismatch)
            // even though the invariant is jointly inductive. FLATTEN the `And` so the block-defs
            // and `¬P[σ]` become flat siblings of the path guards — identical conjunction, but the
            // gate's direct-conjunct check now holds. A non-`And` `formula` is pushed whole. Sound:
            // pure associativity of `∧`, no solver-visible change (mirrors the sem-guard /
            // global-fact / own-precondition flatten-splices in the attributed producer).
            match formula {
                Formula::And(inner) => conj.extend(inner),
                other => conj.push(other),
            }
            terms.push(Formula::And(conj));
        }
    } else {
        return (formula, path_terms);
    }

    let result = if terms.len() == 1 {
        terms.into_iter().next().unwrap_or(Formula::Bool(true))
    } else {
        Formula::Or(terms)
    };
    (result, path_terms)
}

/// `guard` with every variable the discriminant CSE ties (`anchors`: temp -> anchor)
/// replaced by its anchor where `use_anchor(anchor, sort)` allows it, conjoined with
/// each tie `anchor == temp` the replacement used — so the result is equivalent to
/// `guard ∧ ties`. An empty map, or a guard naming no usable tied temp, comes back
/// unchanged.
fn render_through_discriminant_cse_anchors(
    guard: Formula,
    anchors: &trust_types::fx::FxHashMap<String, String>,
    mut use_anchor: impl FnMut(&str, &Sort) -> bool,
) -> Formula {
    if anchors.is_empty()
        || !trust_types::any_free_variable_name(&guard, &mut |name| anchors.contains_key(name))
    {
        return guard;
    }
    let mut ties: Vec<Formula> = Vec::new();
    let rendered = guard.map(&mut |node| match node {
        Formula::Var(name, sort) => match anchors.get(&name) {
            Some(anchor) if use_anchor(anchor, &sort) => {
                let tie = Formula::Eq(
                    Box::new(Formula::Var(anchor.clone(), sort.clone())),
                    Box::new(Formula::Var(name, sort.clone())),
                );
                if !ties.contains(&tie) {
                    ties.push(tie);
                }
                Formula::Var(anchor.clone(), sort)
            }
            _ => Formula::Var(name, sort),
        },
        other => other,
    });
    if ties.is_empty() {
        rendered
    } else {
        let mut out = Vec::with_capacity(ties.len() + 1);
        out.push(rendered);
        out.extend(ties);
        Formula::And(out)
    }
}

#[cfg(test)]
mod path_node_drop_tests {
    use super::*;

    /// Extend `path` by `range`, one node per item, and return the new head.
    fn extend(mut path: SharedPath<usize>, range: std::ops::Range<usize>) -> SharedPath<usize> {
        for item in range {
            path = path_cons(&path, item);
        }
        path
    }

    /// A chain far past the measured recursive-drop overflow depth (release
    /// 300_000, debug 40_000-50_000 on an 8 MiB stack; test threads get less)
    /// must tear down without overflowing the stack.
    #[test]
    fn dropping_a_million_node_path_does_not_overflow_the_stack() {
        let path = extend(None, 0..1_000_000);
        assert_eq!(path_len(&path), 1_000_000);
        drop(path);
    }

    /// The `Err(_) => break` branch: dropping the head must stop at a suffix
    /// another handle still shares, leaving that suffix intact — same length,
    /// same items — and releasing exactly the head's reference to it.
    #[test]
    fn dropping_the_head_leaves_a_shared_suffix_intact() {
        let suffix = extend(None, 0..500_000);
        let head = extend(suffix.clone(), 500_000..1_000_000);
        assert_eq!(path_len(&head), 1_000_000);
        let Some(suffix_node) = suffix.clone() else {
            unreachable!("a 500_000-node path is non-empty");
        };
        // `suffix`, `suffix_node`, and the head chain's last owned node.
        assert_eq!(std::rc::Rc::strong_count(&suffix_node), 3);

        drop(head);

        assert_eq!(std::rc::Rc::strong_count(&suffix_node), 2);
        drop(suffix_node);
        assert_eq!(path_len(&suffix), 500_000);
        assert_eq!(path_to_vec(&suffix), (0..500_000).collect::<Vec<usize>>());
        // The surviving suffix is itself long; its own teardown is iterative too.
        drop(suffix);
    }
}
