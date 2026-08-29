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

/// Apply `f` to every `Formula` stored in a wrapper (conjoin facts, or a guarded
/// path term's guards). `Raw` terms carry no formula.
pub(super) fn ob_map_wrapper_formulas(
    w: &mut ObligationWrapper,
    f: &mut impl FnMut(&Formula) -> Formula,
) {
    match w {
        ObligationWrapper::ConjoinFactsLast { facts } => {
            for fact in facts.iter_mut() {
                *fact = f(fact);
            }
        }
        ObligationWrapper::PathGuardOr { paths } => {
            for p in paths.iter_mut() {
                if let PathGuardTerm::Guarded { guards } = p {
                    for g in guards.iter_mut() {
                        *g = f(g);
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
    ob.body = version_rename_at(&ob.body, sv, func, block, stmt_idx);
    if let Some(s) = ob.subject.as_mut() {
        *s = version_rename_at(s, sv, func, block, stmt_idx);
    }
    for w in &mut ob.wrappers {
        ob_map_wrapper_formulas(w, &mut |x| version_rename_at(x, sv, func, block, stmt_idx));
    }
}

/// Record a pure `inner ↦ And([facts.., inner])` conjoin by reading the facts back
/// from a before/after pair, for conjoin sites that compute their facts internally
/// (the type-range conjoins) and do not expose them. This records the WRAPPER the
/// step applied — the body was seeded earlier and is unchanged — so it is not a
/// guess about which sub-formula is the obligation. `after == before` is identity
/// (no wrapper). Any shape other than `And([.., before])` records nothing, so
/// reconstruction diverges and the consumer DECLINES (fail-closed).
pub(super) fn ob_record_conjoin_wrap(
    vc: &mut VerificationCondition,
    before: &Formula,
    after: &Formula,
) {
    if vc.obligation.is_none() || after == before {
        return;
    }
    if let Formula::And(children) = after
        && children.last() == Some(before)
        && children.len() >= 2
    {
        let facts = &children[..children.len() - 1];
        ob_record_conjoin(vc, facts);
    }
    // Otherwise: unexpected shape — record nothing; reconstruction will mismatch
    // and the consumer DECLINES (fail-closed).
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
    ob.body = normalize_ssa_version_tokens(func, &ob.body);
    if let Some(s) = ob.subject.as_mut() {
        *s = normalize_ssa_version_tokens(func, s);
    }
    for w in &mut ob.wrappers {
        ob_map_wrapper_formulas(w, &mut |x| normalize_ssa_version_tokens(func, x));
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
    ob.body = eliminate_term_ites(&ob.body, cap);
    if let Some(s) = ob.subject.as_mut() {
        *s = eliminate_term_ites(s, cap);
    }
    for w in &mut ob.wrappers {
        ob_map_wrapper_formulas(w, &mut |x| eliminate_term_ites(x, cap));
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
        function: func.name.clone().into(),
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

/// Trust (runtime ledger): the `(BlockId, VC)` origins for arithmetic Add/Sub/Mul
/// overflow VCs, carrying the SAME per-VC interval discharge/augment mutation the
/// production pipeline applies (mirrors `discharge_body_vcs`), so each returned VC
/// is byte-identical to the one the compiler's results row carries. This is the
/// join key the proven-overflow-check elision seam uses to map a KernelCertified
/// overflow VC back to its MIR basic block. A fresh, pristine, multi-block-complete
/// regeneration: identical-formula asserts in distinct blocks are surfaced
/// separately so the seam can mark them Ambiguous (fail-closed). The result is a
/// join table only: an entry licenses no rewrite by itself.
pub fn overflow_vc_block_origins(
    func: &VerifiableFunction,
    summaries: Option<&crate::modular::SummaryDatabase>,
) -> Vec<(BlockId, VerificationCondition)> {
    // This compiler-facing replay API runs independently of the ordinary
    // `generate_vcs_impl` boundary. Keep call-result havoc and intrinsic
    // safety recognition identical for MIR TailCall sites too.
    let tail_call_expanded = func.with_tail_calls_expanded();
    let func = tail_call_expanded.as_ref();
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(func);
    let func = arithmetic_safe_func.as_ref();
    let overflow: Vec<(BlockId, VerificationCondition)> =
        generate_v2_safety_vcs_impl_with_origins(func, summaries)
            .into_iter()
            .filter(|(_, vc)| {
                // DELIBERATELY excludes `VcKind::UncheckedArithmeticOverflow`.
                // This table is the join key for the proven-overflow-check
                // ELISION seam, and an `unchecked_{add,sub,mul}` block has no
                // `Assert(Overflow)` to elide — it lowers to a lone `add nsw`/
                // `nuw`. Handing the seam a block with no check to remove is at
                // best a no-op and at worst licenses a rewrite of a block whose
                // shape the seam does not model. Before the kind split these
                // rows WERE `ArithmeticOverflow` and did reach here; keeping them
                // out is a second, independent correctness gain from the split.
                matches!(
                    vc.kind,
                    VcKind::ArithmeticOverflow { op: BinOp::Add | BinOp::Sub | BinOp::Mul, .. }
                )
            })
            .collect();
    if overflow.is_empty() {
        return Vec::new();
    }
    // Reproduce the production discharge/augment (see `discharge_body_vcs`):
    // interval-dischargeable VCs keep their original formula; the rest are
    // augmented with the abstract state. `try_discharge_batch` is per-VC
    // independent, so the overflow subset yields the same per-VC decision as the
    // full batch, and `augment_vc_with_abstract_state` uses only the VC + env.
    let merged_env = abstract_interp::merged_interval_environment(func);
    let candidates: Vec<VerificationCondition> =
        overflow.iter().map(|(_, vc)| vc.clone()).collect();
    let report = abstract_interp::try_discharge_batch(&candidates, &merged_env);
    let discharged: FxHashSet<usize> = report.discharged.iter().map(|(i, _)| *i).collect();
    overflow
        .into_iter()
        .enumerate()
        .map(|(i, (bid, vc))| {
            let final_vc = if discharged.contains(&i) {
                vc
            } else {
                abstract_interp::augment_vc_with_abstract_state(&vc, &merged_env)
            };
            (bid, final_vc)
        })
        .collect()
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
/// only lose a refutable row.
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
    if neg_block.id.0 == 0 {
        return false;
    }
    // Id-as-index identity: `blocks[neg_block.id.0]` must be THIS block.
    if func.body.blocks.get(neg_block.id.0).is_none_or(|b| !std::ptr::eq(b, neg_block)) {
        return false;
    }
    let Some(ty) = crate::operand_ty_cow(func, operand) else {
        return false;
    };
    if !ty.is_signed() || ty.int_width().is_none_or(|width| width >= 128) {
        return false;
    }

    func.body.blocks.iter().any(|assert_block| {
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
        // Sole-entry check: no OTHER block's terminator may reach the negation's
        // block, so the surviving assert row covers every execution of the Neg.
        let bypassed = func.body.blocks.iter().any(|b| {
            b.id != assert_block.id
                && b.terminator.exit_targets().iter().any(
                    |t| matches!(t, trust_types::ClauseTarget::Block(succ) if *succ == neg_block.id),
                )
        });
        if bypassed {
            return false;
        }
        // ONE negation, and therefore THIS one. `v2_find_target_neg_operand`
        // yields `Some` only when `target` holds exactly one `Neg` statement, and
        // `target` is this very block, so the assert the builder binds below is
        // bound to the statement now being generated for — not merely to its
        // block. A second `Neg` here makes the binder ambiguous and both rows stay.
        if v2_find_target_neg_operand(func, *target).is_none() {
            return false;
        }
        // IDENTITY, NOT REPLICATION: the assert lane's OWN builder decides whether
        // the equivalent row really exists, so this lane cannot drift away from it.
        v2_build_assert_negation_vc(func, assert_block, *target, cond, false, span)
            .is_some_and(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. }))
    })
}

/// Summary-aware safety generation: the per-block semantic guard map also carries
/// each proved callee's rebound postcondition, so body safety VCs may soundly
/// assume them (separate-compilation boundary). The `None` path is the canonical
/// non-summary generator.
pub(super) fn generate_v2_safety_vcs_impl(
    func: &VerifiableFunction,
    summaries: Option<&crate::modular::SummaryDatabase>,
) -> Vec<VerificationCondition> {
    generate_v2_safety_vcs_impl_with_origins(func, summaries)
        .into_iter()
        .map(|(_, vc)| vc)
        .collect()
}

/// Trust (runtime ledger): same as `generate_v2_safety_vcs_impl` but retains each
/// safety VC's originating `BlockId` (== `mir::BasicBlock` index, see
/// `trust-mir-extract/src/convert.rs`). The proven-overflow-check elision seam
/// joins a KernelCertified overflow VC to its MIR block by this origin; output is
/// otherwise byte-identical (the wrapper above just drops the key).
pub(super) fn generate_v2_safety_vcs_impl_with_origins(
    func: &VerifiableFunction,
    summaries: Option<&crate::modular::SummaryDatabase>,
) -> Vec<(BlockId, VerificationCondition)> {
    let path_guards = v2_analyze_path_guards(func);
    let guard_paths_map = &path_guards.paths;
    // Trust (lane-A CSE): one statement-version oracle for the whole function.
    let sv = StmtVersionCtx::build(func);
    let path_definition_map = v2_build_path_definition_map(func);
    let semantic_guards = match summaries {
        Some(s) => build_semantic_guard_map_with_summaries(func, s),
        None => build_semantic_guard_map(func),
    };

    // Track the originating block id alongside each VC so we can apply the
    // correct semantic guards. Matching by span is unreliable when multiple
    // blocks share `SourceSpan::default()` (as in many synthetic test MIRs).
    let mut block_vcs: Vec<(BlockId, VerificationCondition)> = Vec::new();

    for block in &func.body.blocks {
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
                    function: func.name.clone().into(),
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
                    function: func.name.clone().into(),
                    location: span.clone(),
                    formula: v2_formula_with_block_defs(
                        func,
                        block,
                        v2_assert_failure_formula(func, cond, *expected),
                    ),
                    contract_metadata: None,
                    obligation: None,
                }),
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
                block_vcs.push((block.id, vc));
            }
        }

        // 1b. Panic-style assertion/unreachable terminators from native MIR.
        // Skip blocks that the path walk proves unreachable from the entry — generating
        // an Unreachable VC for dead code would falsely refute programs whose dead
        // blocks the compiler intentionally left as Unreachable scaffolding.
        if guard_paths_map.contains_key(&block.id)
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
        if let Terminator::Call { func: callee, args, dest, span, .. } = &block.terminator
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
            let (formula, rec_body, kept) =
                v2_formula_with_block_defs_at_point_recorded(func, block, block.stmts.len(), body);
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
                OverflowCall::Pow => VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) },
            };
            block_vcs.push((
                block.id,
                VerificationCondition {
                    kind: vc_kind,
                    function: func.name.clone().into(),
                    location: span.clone(),
                    formula,
                    contract_metadata: None,
                    obligation: v2_arith_overflow_seed_record(&rec_body, &kept, width),
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
        if let Terminator::Call { func: callee, dest, span, .. } = &block.terminator
            && iterator_integer_fold_call(callee)
            && crate::place_ty(func, dest).is_some_and(|ty| ty.int_width().is_some())
        {
            block_vcs.push((
                block.id,
                VerificationCondition {
                    kind: VcKind::UnsupportedMir {
                        kind: "iterator-fold-overflow".into(),
                        detail: "Iterator::sum/product accumulates inside the library \
                                 impl and can overflow-panic; not statically modeled \
                                 (no accumulation invariant) — reported Unknown \
                                 (runtime-checked), never silently verified"
                            .into(),
                    },
                    function: func.name.clone().into(),
                    location: span.clone(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                    obligation: None,
                },
            ));
        }

        // 1c-repeat. `str::repeat(n)` — sibling of the sum/product fold: the result
        // capacity `s.len() * n` is computed INSIDE the library impl and
        // overflow-panics ("capacity overflow") for large `n`, with no
        // caller-visible BinaryOp, so it was SILENTLY accepted (0 obligations).
        // Surface the same UnsupportedMir obligation (→ Unknown → runtime-checked)
        // as the iterator fold, per the owner-decided runtime-checked demotion.
        // Gated to the `str` inherent impl (`<impl str>::repeat`) so `slice`/`Vec::
        // repeat` — which already mint a runtime-checked obligation via the
        // bulk-alloc capacity path — are NOT double-counted or regressed.
        if let Terminator::Call { func: callee, span, .. } = &block.terminator
            && str_repeat_capacity_overflow_call(callee)
        {
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
                    function: func.name.clone().into(),
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
        if let Terminator::Call { func: callee, args, span, .. } = &block.terminator
            && let Some((divisor_idx, kind)) = divzero_call(callee)
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
        if let Terminator::Call { func: callee, args, span, .. } = &block.terminator
            && let Some(panic) = slice_method_panic(callee)
            // Trust (str char-boundary soundness): the `::<__trust_str_index>` marker
            // `func_operand_name` appends to a `str` range-index callee — the Self
            // identity that survives `str`→`[u8]` erasure. The RangeIndex body uses it
            // to mint the UTF-8 char-boundary obligation for str receivers only.
            && let Some((violation, kind)) =
                slice_method_panic_body(func, &panic, args, callee.contains("__trust_str_index"))
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
            let base = if matches!(panic, SliceMethodPanic::RangeIndex)
                && args.iter().any(|a| operand_is_panicking_range(func, a))
            {
                violation
            } else {
                v2_formula_with_block_defs(func, block, violation)
            };
            let formula = conjoin_slice_len_bounds(func, base);
            block_vcs.push((
                block.id,
                VerificationCondition {
                    kind,
                    function: func.name.clone().into(),
                    location: span.clone(),
                    formula,
                    contract_metadata: None,
                    obligation: None,
                },
            ));
        }

        for (stmt_index, stmt) in block.stmts.iter().enumerate() {
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
                            Some(stmt_index),
                        )
                    {
                        block_vcs.push((block.id, vc));
                    }
                }
                // Float Add | Sub | Mul (float-residuals honest L1 widening:
                // Sub joins the arm — `a - b` overflows to ±inf exactly like
                // `a + (-b)`, and previously emitted NO obligation at all).
                Rvalue::BinaryOp(op @ (BinOp::Add | BinOp::Sub | BinOp::Mul), lhs, rhs)
                    if v2_is_float_operand(func, lhs) || v2_is_float_operand(func, rhs) =>
                {
                    let context =
                        V2FloatOverflowContext { func, block, span, stmt_index, summaries };
                    if let Some(vc) = v2_build_float_overflow_vc(context, *op, lhs, rhs) {
                        block_vcs.push((block.id, vc));
                    }
                }
                // a DIRECT integer Add/Sub/Mul (not the assert-guarded
                // CheckedBinaryOp form) still needs a solver-facing overflow
                // obligation, else an unguarded overflowing op is silently
                // unchecked (a false-PROVE). Float operands are handled by the
                // arm above. An assert targeting this block is not sufficient
                // authority to suppress the row: target identity alone does not
                // prove that the assert guarded this operation and operands.
                // Trust (R2/C4): `UncheckedBinaryOp` uses the dedicated arm
                // immediately below. It builds the same arithmetic proposition
                // under the assignment's validated integer type, but deliberately
                // ignores the plain form's modular certificate and checked-guard
                // suppression authorities.
                // (An earlier note here called that defense-in-depth on the grounds
                // that `LowerIntrinsics` "runs after this lane's extraction point".
                // MEASURED 2026-08-20 with the shipped stage2 `trustc`: it does NOT.
                // `unsafe { a.unchecked_shl(b) }` reaches this lane as
                // `BinOp::ShlUnchecked` — "unsupported MIR `BinOp::ShlUnchecked`" —
                // which is only producible by `LowerIntrinsics`. The dedicated
                // unchecked arm below is therefore live.)
                //
                // THE MODULAR EXCEPTION. `LowerIntrinsics` rewrites
                // `intrinsics::wrapping_{add,sub,mul}` into a bare
                // `Rvalue::BinaryOp` too, and `wrapping_add` CANNOT overflow — the
                // obligation minted for it is FALSE, and it is what makes
                // `core::num`'s whole `wrapping_*` family unverifiable (measured: 3
                // of the 43 failing obligations in the `core::num` leaf slice,
                // `docs/design/2026-08-20-core-slice-blocker-histogram.md` §2.1).
                // The wrapping identity is unrecoverable HERE — under
                // `-Coverflow-checks=off` a source-level `a + b` extracts to the
                // byte-identical rvalue — so the compiler carries it forward from
                // the pass that dropped it, as a per-`(span, op)` certificate on the
                // `VcgenContext` (`is_certified_modular_arith`). Skipping is
                // therefore keyed on rustc's own record of the operation, never on
                // the shape: an ordinary `+` in the same shape is NOT in the set and
                // keeps its obligation, and so does every op reached without a
                // compiler-installed context.
                Rvalue::BinaryOp(op @ (BinOp::Add | BinOp::Sub | BinOp::Mul), lhs, rhs)
                    if !v2_is_float_operand(func, lhs)
                        && !v2_is_float_operand(func, rhs)
                        && !crate::is_certified_modular_arith(&func.def_path, span, *op) =>
                {
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
                    let operation_ty = crate::place_ty(func, place)
                        .filter(|ty| crate::fixed_width_integer_descriptor(ty).is_some());
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
                    if let Some(operation_ty) = crate::place_ty(func, place)
                        && let Some(mut vc) = v2_build_unchecked_overflow_vc_for_operands(
                            func,
                            block,
                            *op,
                            lhs,
                            rhs,
                            span,
                            Some(stmt_index),
                            operation_ty,
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
    }

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
    let content_free: Vec<(BlockId, bool)> =
        block_vcs.iter().map(|(id, vc)| (*id, v2_violation_is_content_free(&vc.formula))).collect();

    // Conjoin predecessor definitions before guards so successor-block VCs
    // retain the boolean/int locals that made the path reachable.
    for (block_id, vc) in &mut block_vcs {
        if v2_is_unsupported_mir_vc(vc) {
            continue;
        }
        if let Some(path_defs) = path_definition_map.get(block_id)
            && !path_defs.is_empty()
        {
            let live = v2_live_path_defs(func, &func.body.blocks[block_id.0], path_defs);
            if !live.is_empty() {
                ob_record_conjoin(vc, &live);
                let mut conjuncts = live;
                conjuncts.push(vc.formula.clone());
                vc.formula = Formula::And(conjuncts);
            }
        }
    }

    // Trust S2c (exemption): path guards + semantic assert-passed guards are
    // conjoined AFTER the version rename (moved below), EXEMPT from it, so a guard's
    // bare ENTRY-param read stays name-disjoint from a reassigned body read.

    // Conjoin range-iterator yield facts so `for i in start..end { a[i] }`
    // proves: the loop variable `i` (a `Range::next` Some-payload) provably
    // satisfies `start <= i < end`, which discharges the `a[i]` bounds
    // obligation. Computed independently of the BFS guard map, so loop-join
    // weakening cannot drop it. See `build_range_yield_guard_map`.
    let range_yield_guards = build_range_yield_guard_map(func);
    for (block_id, vc) in &mut block_vcs {
        if v2_is_unsupported_mir_vc(vc) {
            continue;
        }
        if let Some(facts) = range_yield_guards.get(block_id)
            && !facts.is_empty()
        {
            ob_record_conjoin(vc, facts);
            let mut conjuncts = facts.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
        }
    }

    // Conjoin converging two-pointer facts so `while lo < hi { hi -= 1; … s[lo] …;
    // lo += 1 }` proves the `s[lo]` side (`s[hi]` is handled by the downward
    // induction fact): `lo < hi <= s.len()` at the lo-stable body blocks. See
    // `build_converging_pointer_facts`.
    let converging_facts = build_converging_pointer_facts(func);
    for (block_id, vc) in &mut block_vcs {
        if v2_is_unsupported_mir_vc(vc) {
            continue;
        }
        if let Some(facts) = converging_facts.get(block_id)
            && !facts.is_empty()
        {
            ob_record_conjoin(vc, facts);
            let mut conjuncts = facts.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
        }
    }

    // Trust (countdown-loop piece): conjoin the countdown PRE-VALUE facts at the
    // decrement blocks — `offset >= LEN - c*(T-1)` directly contradicts the
    // CheckedSub underflow violation, which is expressed on the pre-value
    // version (the global result-temp form does not reach it). Same consumption
    // discipline as the converging two-pointer facts above; the builder emits a
    // block's fact only when the block has no cursor store, so the bare name
    // versions to the block-entry value. See `build_countdown_preval_facts`.
    let countdown_preval_facts = build_countdown_preval_facts(func);
    for (block_id, vc) in &mut block_vcs {
        if v2_is_unsupported_mir_vc(vc) {
            continue;
        }
        if let Some(facts) = countdown_preval_facts.get(block_id)
            && !facts.is_empty()
        {
            ob_record_conjoin(vc, facts);
            let mut conjuncts = facts.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
        }
    }

    // Conjoin enumerate index yield facts so `for (i, _) in s.iter().enumerate()
    // { … s[i] … }` proves: the index `i` (the enumerate count) provably satisfies
    // `0 <= i < s.len()`. Independent of the BFS guard map. See
    // `build_enumerate_yield_guard_map`.
    let enumerate_yield_guards = build_enumerate_yield_guard_map(func);
    for (block_id, vc) in &mut block_vcs {
        if v2_is_unsupported_mir_vc(vc) {
            continue;
        }
        if let Some(facts) = enumerate_yield_guards.get(block_id)
            && !facts.is_empty()
        {
            ob_record_conjoin(vc, facts);
            let mut conjuncts = facts.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
        }
    }

    // Conjoin slice-chunking yield facts so `for w in s.windows(n) { w[k] }` /
    // `for c in s.chunks(n) { c[k] }` prove: the yielded sub-slice's modeled
    // length is `== n` (windows) / `in [1, n]` (chunks). See
    // `build_slice_iter_yield_guard_map`.
    let slice_iter_yield_guards = build_slice_iter_yield_guard_map(func);
    for (block_id, vc) in &mut block_vcs {
        if v2_is_unsupported_mir_vc(vc) {
            continue;
        }
        if let Some(facts) = slice_iter_yield_guards.get(block_id)
            && !facts.is_empty()
        {
            ob_record_conjoin(vc, facts);
            let mut conjuncts = facts.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
        }
    }

    // Conjoin push-guarded nested-container element-length facts so
    // `let mut m: Vec<Vec<T>> = Vec::new(); for .. { if row.len()<=n {return}; m.push(row) }`
    // proves the inner access `m[r][col]`: the element `m[r]`'s modeled length is
    // `> n` (every pushed row was guarded), which with the range `col < n` discharges
    // `col < m[r].len()`. See `build_push_guard_elem_len_map`.
    let push_guard_elem_len = build_push_guard_elem_len_map(func);
    for (block_id, vc) in &mut block_vcs {
        if v2_is_unsupported_mir_vc(vc) {
            continue;
        }
        if let Some(facts) = push_guard_elem_len.get(block_id)
            && !facts.is_empty()
        {
            ob_record_conjoin(vc, facts);
            let mut conjuncts = facts.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
        }
    }

    // Conjoin dominating length-guard facts so `let m = self.g.len();
    // if self.p_lo.len() != m { return }; for j in 0..m { self.p_lo[j] }` proves the
    // struct-FIELD scalar index: the guard pins `len(self.p_lo) == m` on its
    // fall-through edge, but through a DISTINCT `&self.p_lo` temp than the read carries,
    // so the read's `coll_len(_recv)` is left FREE. Emit `coll_len(_recv) >= m` — the
    // SAME var the bound reads — which with the loop range `j < m` discharges
    // `j < m <= coll_len(_recv)`. See `build_len_guard_field_map`.
    let len_guard_field = build_len_guard_field_map(func);
    for (block_id, vc) in &mut block_vcs {
        if v2_is_unsupported_mir_vc(vc) {
            continue;
        }
        if let Some(facts) = len_guard_field.get(block_id)
            && !facts.is_empty()
        {
            ob_record_conjoin(vc, facts);
            let mut conjuncts = facts.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
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
    let global_facts = build_global_invariant_facts(func);
    if !global_facts.is_empty() {
        for (_, vc) in &mut block_vcs {
            if v2_is_unsupported_mir_vc(vc) {
                continue;
            }
            ob_record_conjoin(vc, &global_facts);
            let mut conjuncts = global_facts.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
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
    {
        let may_reassigned = v2_may_reassigned_per_block(func);
        let empty = FxHashSet::default();
        for (block_id, vc) in &mut block_vcs {
            if v2_is_unsupported_mir_vc(vc) {
                continue;
            }
            let killed = may_reassigned.get(block_id).unwrap_or(&empty);
            let (new_formula, conjoined) = conjoin_preconditions_versioned_recorded(
                func,
                *block_id,
                &func.preconditions,
                killed,
                vc.formula.clone(),
            );
            vc.formula = new_formula;
            // Mirror the whole-formula version rename this step applies onto the
            // recorded body/subject/wrappers (so they stay byte-identical to their
            // copies in `formula`), THEN record the filtered preconditions as the
            // outer ConjoinFactsLast wrapper (they are conjoined bare, after the
            // rename). No-op when the VC carries no obligation.
            if vc.obligation.is_some() {
                let terminal = func
                    .body
                    .blocks
                    .get(block_id.0)
                    .filter(|b| b.id == *block_id)
                    .map_or(0, |b| b.stmts.len());
                ob_record_rename_at(vc, &sv, func, *block_id, terminal);
                ob_record_conjoin(vc, &conjoined);
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
                    let restored: Vec<Vec<(BlockId, GuardCondition)>> =
                        edges.iter().map(|edge| vec![edge.clone()]).collect();
                    let (new_formula, path_terms) = v2_formula_with_path_guards_recorded(
                        func,
                        &sv,
                        &restored,
                        vc.formula.clone(),
                    );
                    vc.formula = new_formula;
                    if let Some(ob) = vc.obligation.as_mut() {
                        ob.wrappers.push(ObligationWrapper::PathGuardOr { paths: path_terms });
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
            let (new_formula, path_terms) = v2_formula_with_path_guards_recorded(
                func,
                &sv,
                block_guard_paths,
                vc.formula.clone(),
            );
            vc.formula = new_formula;
            // The dominating path-guard map is the sole non-conjoining wrapper.
            if let Some(ob) = vc.obligation.as_mut() {
                ob.wrappers.push(ObligationWrapper::PathGuardOr { paths: path_terms });
            }
        }
    }
    for (block_id, vc) in &mut block_vcs {
        if v2_is_unsupported_mir_vc(vc) {
            continue;
        }
        if let Some(sem_guards) = semantic_guards.get(block_id)
            && !sem_guards.is_empty()
        {
            ob_record_conjoin(vc, sem_guards);
            let mut conjuncts = sem_guards.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
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
    for (_, vc) in &mut block_vcs {
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
        let bounds_kind = matches!(vc.kind, VcKind::SliceBoundsCheck | VcKind::IndexOutOfBounds);
        // `UncheckedArithmeticOverflow` is the SAME out-of-range obligation as
        // `ArithmeticOverflow` (`v2_overflow_call_body` builds both from the same
        // builder) — only the runtime-guard answer differs. It must therefore
        // keep the identical DROP-ONLY type-range strengthening, or splitting the
        // kind would silently make every `unchecked_{add,sub,mul}` LESS
        // dischargeable than the `a + b` it models: a widened decline, not a fix.
        //
        // It is folded into `range_kind` for the same reason: the two kinds must
        // enter the range battery below TOGETHER and be held out of the
        // length-nonneg conjoin below TOGETHER, or "identical treatment" would
        // hold on one side of this function and not the other.
        let arith_kind = matches!(
            vc.kind,
            VcKind::ArithmeticOverflow { .. } | VcKind::UncheckedArithmeticOverflow { .. }
        );
        let range_kind = arith_kind || bounds_kind;
        // Trust (NEGATIVE-LENGTH class): the kinds the range battery below does
        // NOT reach — `Unreachable`, `Assertion`, the panic-path rows — got NO
        // length bound at all, so the merged `Unreachable` sink of
        // `match a { [] => .., [x] => .., [x, .., y] => .. }` was REFUTED with
        // `a__slice_len = -1`: a negative slice length, which no execution can
        // hold. Attach the ONE bound that is a theorem on every target and every
        // element type (`0 <= len`; see `conjoin_length_nonneg_bounds` for why
        // the `isize::MAX` half stays behind its non-ZST gate in
        // `conjoin_slice_len_bounds`). Applied ONLY to the kinds the battery
        // skips, so every `ArithmeticOverflow`/bounds formula stays byte-identical
        // to what it was — this cannot perturb the lane the sweep tuned. The
        // `!range_kind` gate is what makes that true and is asserted directly:
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
        // `!v2_is_unsupported_mir_vc` gate below then skips. Adding `0 <= len` to a
        // formula that no longer states where it applies would not have helped;
        // supplying the missing reachability condition is a different repair.
        if !range_kind && !v2_is_unsupported_mir_vc(vc) {
            let before = vc.formula.clone();
            vc.formula = conjoin_length_nonneg_bounds(func, vc.formula.clone());
            let after = vc.formula.clone();
            ob_record_conjoin_wrap(vc, &before, &after);
        }
        if bounds_kind && count_back_edges(func) == 0 {
            continue;
        }
        if range_kind {
            // Trust (bounds ARM): each of these four conjoins is a pure
            // `And([facts.., formula])` push (facts LAST) or identity when it has no
            // facts, so mirror each onto the recorded obligation as a `ConjoinFactsLast`
            // read back from the before/after pair (`ob_record_conjoin_wrap`). No-op
            // when the VC carries no obligation; the UNSIGNED var*var mul
            // `ArithmeticOverflow` arm carries a record (the UMUL RECORD), so these
            // mirrors are load-bearing for it as well as for the bounds VCs.
            let before = vc.formula.clone();
            vc.formula = conjoin_arg_type_ranges(func, vc.formula.clone());
            let after = vc.formula.clone();
            ob_record_conjoin_wrap(vc, &before, &after);
            // Trust (unsigned-sub vacuous-UNSAT false-accept fix): on an
            // ArithmeticOverflow VC, EXCLUDE the checked-op result copy closure's
            // type-ranges — `0 <= X` for an X tied to `a - b` conjoined onto the
            // subtraction's own underflow VC assumes the very property it checks
            // (see `checked_arith_result_value_vars`). Bounds VCs keep all ranges
            // (an index var's range is not the checked op's own result claim).
            let excl = if arith_kind { checked_arith_result_value_vars(func) } else {
                FxHashSet::default()
            };
            // verifier-precision: bound NON-parameter integer locals/temps too (the
            // sibling of arg ranges) — a `u32`/`i8` temp lowered to unbounded
            // `Sort::Int` otherwise lets the solver false-refute an overflow with an
            // out-of-type-range value. SOUNDNESS: DROP-ONLY (true range fact).
            let before = vc.formula.clone();
            vc.formula = conjoin_local_type_ranges_excluding(func, vc.formula.clone(), &excl);
            let after = vc.formula.clone();
            ob_record_conjoin_wrap(vc, &before, &after);
            // Lever A: bound fixed-width-integer datatype FIELDS too (the modeled
            // `Expr`/`Level`/`Name` cluster), same sound Rust-type invariant. DROP-ONLY.
            let before = vc.formula.clone();
            vc.formula = conjoin_datatype_field_ranges_excluding(func, vc.formula.clone(), &excl);
            let after = vc.formula.clone();
            ob_record_conjoin_wrap(vc, &before, &after);
            let before = vc.formula.clone();
            vc.formula = conjoin_slice_len_bounds(func, vc.formula.clone());
            let after = vc.formula.clone();
            ob_record_conjoin_wrap(vc, &before, &after);
        }
    }

    // FINAL pass: collapse SSA locals' version tokens to the bare name so
    // facts and body reads of the same single-valued local always share one
    // SMT symbol (see `normalize_ssa_version_tokens` for the identity
    // argument; reassigned locals keep their load-bearing token disjointness).
    for (_, vc) in &mut block_vcs {
        if v2_is_unsupported_mir_vc(vc) {
            continue;
        }
        vc.formula = normalize_ssa_version_tokens(func, &vc.formula);
        // Mirror the same token collapse onto the recorded body/subject/wrappers so
        // reconstruction stays byte-identical to the normalized `formula`.
        ob_record_normalize(vc, func);
    }

    block_vcs
}

/// The per-block path cap of [`v2_build_path_guard_map`]. A block that is
/// reached by more routes than this keeps ONE unguarded path instead
/// (`COLLAPSE MODE 1`); [`v2_reachability_for_collapsed`] is what stops that
/// from becoming an unconditional accusation.
const MAX_PATHS_PER_BLOCK: usize = 64;

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
    pub(super) paths: FxHashMap<BlockId, Vec<Vec<(BlockId, GuardCondition)>>>,
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
    /// `generate_v2_safety_vcs_impl_with_origins` conjoins its fact sets onto
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
    v2_analyze_path_guards(func).paths
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
            paths: result,
            collapse: PathGuardCollapse::None,
            degraded: FxHashSet::default(),
            reachability: FxHashMap::default(),
        };
    }

    let n = func.body.blocks.len();
    let cap = n.saturating_mul(n).saturating_add(n).saturating_mul(16).saturating_add(4096);
    let mut steps = 0usize;
    let mut saturated_blocks: FxHashSet<BlockId> = FxHashSet::default();
    let mut queue: std::collections::VecDeque<(
        BlockId,
        Vec<(BlockId, GuardCondition)>,
        Vec<BlockId>,
    )> = std::collections::VecDeque::from([(BlockId(0), Vec::new(), Vec::new())]);

    while let Some((block_id, path_guards, mut path_blocks)) = queue.pop_front() {
        steps += 1;
        if steps > cap {
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
            let collapsed_map: FxHashMap<BlockId, Vec<Vec<(BlockId, GuardCondition)>>> =
                func.body.blocks.iter().map(|block| (block.id, vec![Vec::new()])).collect();
            let every_block: FxHashSet<BlockId> =
                func.body.blocks.iter().map(|block| block.id).collect();
            let reachability = v2_reachability_for_collapsed(func, &every_block);
            return PathGuardAnalysis {
                paths: collapsed_map,
                collapse: PathGuardCollapse::BudgetTripped,
                degraded: every_block,
                reachability,
            };
        }
        if block_id.0 >= n {
            continue;
        }
        if path_blocks.contains(&block_id) {
            continue;
        }
        path_blocks.push(block_id);

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
            paths.push(path_guards.clone());
        } else {
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
                let mut next_guards = succ_guards.clone();
                next_guards.push((block_id, guarded.guard));
                queue.push_back((target, next_guards, path_blocks.clone()));
            }
        }
        for target in block.terminator.unguarded_successors() {
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
    PathGuardAnalysis { paths: result, collapse, degraded: saturated_blocks, reachability }
}

/// Trust (collapse false REFUTATION): the weakest still-valid reachability
/// condition for every block in `collapsed`.
///
/// # The defect
///
/// [`v2_build_path_guard_map`] has TWO collapse modes, and each leaves a block
/// with ONE UNGUARDED path whose term lowers to an unconditional `true` — i.e.
/// NO reachability condition at all:
///
///  1. a block reached by more than `MAX_PATHS_PER_BLOCK` routes;
///  2. the whole function, when the global step budget trips.
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
    let in_edges = v2_build_in_edge_guard_map(func);
    for block_id in collapsed {
        let summary = match in_edges.get(block_id) {
            // The disjunction is `true` — entry, or an unguarded in-edge.
            Some(None) => ReachSummary::Unconditional,
            // A real condition, at ANY in-degree. There is deliberately no size
            // budget here: a big disjunction is inconvenient, not undecidable,
            // and declining on size demotes genuinely reachable UB to Unknown.
            Some(Some(edges)) if !edges.is_empty() => ReachSummary::Guards(edges.clone()),
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
) -> FxHashMap<BlockId, Option<Vec<(BlockId, GuardCondition)>>> {
    let mut map: FxHashMap<BlockId, Option<Vec<(BlockId, GuardCondition)>>> = FxHashMap::default();
    // Both spellings of "the entry": the walk's root `BlockId(0)` and the first
    // declared block, which coincide on well-formed MIR but need not on a
    // hand-built or adversarial body.
    let mut entries: Vec<BlockId> = vec![BlockId(0)];
    if let Some(first) = func.body.blocks.first().map(|b| b.id)
        && first != BlockId(0)
    {
        entries.push(first);
    }
    for entry in &entries {
        map.insert(*entry, None);
    }
    let is_entry = |id: BlockId| entries.contains(&id);
    for block in &func.body.blocks {
        for guarded in block.terminator.discovered_clauses(block.id) {
            let trust_types::ClauseTarget::Block(target) = guarded.target else { continue };
            if is_entry(target) {
                continue;
            }
            if let Some(edges) = map.entry(target).or_insert_with(|| Some(Vec::new())) {
                edges.push((block.id, guarded.guard));
            }
        }
        for target in block.terminator.unguarded_successors() {
            if is_entry(target) {
                continue;
            }
            map.insert(target, None);
        }
    }
    map
}

// ---------------------------------------------------------------------------
// THE COLLAPSE INVARIANT
// ---------------------------------------------------------------------------
// Two collapse cliffs have been found in `v2_build_path_guard_map` — the
// per-block path cap and the global step budget — and each one produced the
// IDENTICAL false REFUTATION, each was closed by a local repair, and the next
// reviewer got past each repair. Patching a third cap would only move the cliff.
//
// The root cause is a missing INVARIANT, stated once and enforced at the single
// point where such a row is decided:
//
//     A row whose own violation formula has NO CONTENT — whose entire meaning is
//     "control reaches this block" — must be reported UNKNOWN, never REFUTED,
//     whenever the path condition is ABSENT or DEGRADED.
//
// "I have no reachability information" is not "this is reachable". The invariant
// subsumes both known collapse modes and any future one, because it is keyed on
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
    guard_paths: &[Vec<(BlockId, GuardCondition)>],
    formula: Formula,
) -> Formula {
    v2_formula_with_path_guards_recorded(func, sv, guard_paths, formula).0
}

/// Refutation-polarity counterpart of [`v2_formula_with_path_guards`].
///
/// The ordinary path helper may weaken an unmodeled guard to `true`, which is
/// sound when guards are proof hypotheses but can manufacture a SAT witness.
/// This variant accepts only guards with complete lowering and returns `None`
/// on an absent source block, an unmodeled guard, or an empty path set.  The
/// caller must separately reject path-map collapse, because a collapsed empty
/// guard path is indistinguishable from a genuinely unconditional path here.
pub(super) fn v2_formula_with_refutation_path_guards(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    guard_paths: &[Vec<(BlockId, GuardCondition)>],
    formula: Formula,
) -> Option<Formula> {
    if guard_paths.is_empty() {
        return None;
    }

    let mut terms = Vec::with_capacity(guard_paths.len());
    for path in guard_paths {
        if path.is_empty() {
            terms.push(formula.clone());
            continue;
        }

        let mut conjuncts = Vec::with_capacity(path.len() + 1);
        for (source, guard) in path {
            let source_block =
                func.body.blocks.get(source.0).filter(|block| block.id == *source)?;
            let guard = guards::guard_to_refutation_formula(func, guard)?;
            conjuncts.push(version_rename_at(&guard, sv, func, *source, source_block.stmts.len()));
        }
        match formula.clone() {
            Formula::And(inner) => conjuncts.extend(inner),
            other => conjuncts.push(other),
        }
        terms.push(Formula::And(conjuncts));
    }

    Some(match terms.len() {
        1 => terms.pop().expect("length checked"),
        _ => Formula::Or(terms),
    })
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
    guard_paths: &[Vec<(BlockId, GuardCondition)>],
    formula: Formula,
) -> (Formula, Vec<PathGuardTerm>) {
    let mut path_terms: Vec<PathGuardTerm> = Vec::new();
    // Trust S2c: version each guard at ITS SOURCE block before conjoining (the
    // facts are conjoined EXEMPT from the whole-VC rename). An IN-BLOCK read in the
    // guard (`k = n%4` in `if k >= 4`) renames to `k#sSRC` and matches the renamed
    // body's `k#sSRC` (so `k>=4 ∧ k<4` is UNSAT → dead branch proved); an
    // ENTRY-param read (`n`) gets `version_token_at == None` and stays BARE, so a
    // stale `n <= 100` is still name-disjoint from a reassigned body `n#s2_0`.
    let mut terms = Vec::new();
    for guards in guard_paths {
        if guards.is_empty() {
            terms.push(formula.clone());
            path_terms.push(PathGuardTerm::Raw);
            continue;
        }
        let renamed_guards: Vec<Formula> = guards
            .iter()
            .map(|(src, g)| {
                let gf = guards::guard_to_formula(func, g);
                // Trust (lane-A CSE): id==index invariant → O(1) indexed lookup;
                // the `.filter` keeps the `map_or(0, ..)` fallback identical when
                // the slot is missing or the invariant were violated.
                let terminal = func
                    .body
                    .blocks
                    .get(src.0)
                    .filter(|b| b.id == *src)
                    .map_or(0, |b| b.stmts.len());
                version_rename_at(&gf, sv, func, *src, terminal)
            })
            .collect();
        path_terms.push(PathGuardTerm::Guarded { guards: renamed_guards.clone() });
        let mut conj: Vec<Formula> = renamed_guards;
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
        match formula.clone() {
            Formula::And(inner) => conj.extend(inner),
            other => conj.push(other),
        }
        terms.push(Formula::And(conj));
    }

    let result = match terms.len() {
        0 => formula,
        1 => terms.pop().unwrap_or_else(|| unreachable!("len checked above")),
        _ => Formula::Or(terms),
    };
    (result, path_terms)
}
