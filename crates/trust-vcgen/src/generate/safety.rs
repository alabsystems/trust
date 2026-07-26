// The L0 safety pass: one VC per potentially-trapping operation in the body,
// each carried under the path guard of the block it occurs in.

use super::*;

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
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(func);
    let func = arithmetic_safe_func.as_ref();
    let overflow: Vec<(BlockId, VerificationCondition)> =
        generate_v2_safety_vcs_impl_with_origins(func, summaries)
            .into_iter()
            .filter(|(_, vc)| {
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
    let candidates: Vec<VerificationCondition> = overflow.iter().map(|(_, vc)| vc.clone()).collect();
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
    let guard_paths_map = v2_build_path_guard_map(func);
    // Trust (lane-A CSE): one statement-version oracle for the whole function.
    let sv = StmtVersionCtx::build(func);
    let path_definition_map = v2_build_path_definition_map(func);
    let semantic_guards = match summaries {
        Some(s) => build_semantic_guard_map_with_summaries(func, s),
        None => build_semantic_guard_map(func),
    };
    let overflow_guard_targets = v2_overflow_guard_targets(func);
    let negation_guard_targets = v2_negation_guard_targets(func);

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
                        VerificationCondition {
                            kind: VcKind::DivisionByZero,
                            function: func.name.clone().into(),
                            location: span.clone(),
                            formula: v2_formula_with_block_defs(
                                func,
                                block,
                                v2_assert_failure_formula(func, cond, *expected),
                            ),
                            contract_metadata: None,
                        }
                    })
                }
                AssertMessage::RemainderByZero => {
                    (!v2_assert_failure_is_known_false(block, cond, *expected)).then(|| {
                        VerificationCondition {
                            kind: VcKind::RemainderByZero,
                            function: func.name.clone().into(),
                            location: span.clone(),
                            formula: v2_formula_with_block_defs(
                                func,
                                block,
                                v2_assert_failure_formula(func, cond, *expected),
                            ),
                            contract_metadata: None,
                        }
                    })
                }
                AssertMessage::Overflow(op) => Some(
                    v2_build_assert_overflow_vc(func, block, *target, *op, cond, *expected, span)
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
                ),
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
                AssertMessage::BoundsCheck => {
                    // A literal in-range element access (`cols[0]` on
                    // `[Vec4; 4]`) provably cannot fire — emit nothing rather
                    // than a constant-false violation the vacuity gate later
                    // strips proof authority from. See
                    // `v2_bounds_assert_const_index_in_range`; the hardened
                    // panic-boundary twin applies the identical skip.
                    if v2_bounds_assert_const_index_in_range(func, block, cond, *expected) {
                        None
                    } else {
                        Some(
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
                        )
                    }
                }
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
                }),
                // The coroutine transform inserts these guards at the illegal
                // resume-after-completion/panic/drop states. They are executor-
                // protocol preconditions, not user data-safety checks: the
                // TrustIr bridge already lowers the same three sentinels to
                // protocol `Assume` nodes, and termination analysis excludes
                // their sink loops. Emitting `UnsupportedMir` here made every
                // otherwise-safe async body Unknown and hid its real arithmetic
                // and bounds verdicts behind an unrelated protocol artifact.
                //
                // Keep this allowlist exact. All other unmodeled assert kinds
                // remain in the fail-closed catch-all below.
                AssertMessage::ResumedAfterReturn
                | AssertMessage::ResumedAfterPanic
                | AssertMessage::ResumedAfterDrop => None,
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
        // unguarded op FAILS. Skipped on assert-guarded blocks to avoid double VCs.
        if !overflow_guard_targets.contains(&block.id)
            && let Terminator::Call { func: callee, args, dest, span, .. } = &block.terminator
            && let Some(kind) = overflow_arith_call(callee)
            && let Some((body, op, lhs_ty, rhs_ty)) = v2_overflow_call_body(func, kind, args, dest)
        {
            let formula = v2_formula_with_block_defs(func, block, body);
            block_vcs.push((
                block.id,
                VerificationCondition {
                    kind: VcKind::ArithmeticOverflow { op, operand_tys: (lhs_ty, rhs_ty) },
                    function: func.name.clone().into(),
                    location: span.clone(),
                    formula,
                    contract_metadata: None,
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
            let formula =
                v2_formula_with_block_defs(func, block, v2_divisor_is_zero_formula(func, divisor));
            block_vcs.push((
                block.id,
                VerificationCondition {
                    kind,
                    function: func.name.clone().into(),
                    location: span.clone(),
                    formula,
                    contract_metadata: None,
                },
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
                },
            ));
        }

        for (stmt_index, stmt) in block.stmts.iter().enumerate() {
            let Statement::Assign { rvalue, span, .. } = stmt else {
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
                    if !is_float && !v2_divisor_is_nonzero_constant(divisor) {
                        block_vcs.push((
                            block.id,
                            VerificationCondition {
                                kind: VcKind::DivisionByZero,
                                function: func.name.clone().into(),
                                location: span.clone(),
                                formula: v2_formula_with_block_defs_before_stmt(
                                    func,
                                    block,
                                    stmt_index,
                                    v2_divisor_is_zero_formula(func, divisor),
                                ),
                                contract_metadata: None,
                            },
                        ));
                    }

                    if !is_float
                        && !overflow_guard_targets.contains(&block.id)
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
                    if !v2_divisor_is_nonzero_constant(divisor) =>
                {
                    block_vcs.push((
                        block.id,
                        VerificationCondition {
                            kind: VcKind::RemainderByZero,
                            function: func.name.clone().into(),
                            location: span.clone(),
                            formula: v2_formula_with_block_defs_before_stmt(
                                func,
                                block,
                                stmt_index,
                                v2_divisor_is_zero_formula(func, divisor),
                            ),
                            contract_metadata: None,
                        },
                    ));

                    if !overflow_guard_targets.contains(&block.id)
                        && let Some(vc) = v2_build_signed_div_overflow_vc(
                            func,
                            block,
                            BinOp::Rem,
                            lhs,
                            divisor,
                            span,
                            Some(stmt_index),
                        )
                    {
                        block_vcs.push((block.id, vc));
                    }
                }
                Rvalue::BinaryOp(op @ (BinOp::Shl | BinOp::Shr), lhs, rhs)
                    if !overflow_guard_targets.contains(&block.id) =>
                {
                    if let Some(vc) = v2_build_shift_overflow_vc(
                        func,
                        block,
                        *op,
                        lhs,
                        rhs,
                        span,
                        Some(stmt_index),
                    ) {
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
                // arm above; assert-guarded blocks are covered via the Assert
                // path (`overflow_guard_targets`) and skipped here to avoid
                // double-emitting / false-failing precondition-bounded code.
                Rvalue::BinaryOp(op @ (BinOp::Add | BinOp::Sub | BinOp::Mul), lhs, rhs)
                    if !v2_is_float_operand(func, lhs)
                        && !v2_is_float_operand(func, rhs)
                        && !overflow_guard_targets.contains(&block.id) =>
                {
                    if let Some(vc) = v2_build_overflow_vc_for_operands(
                        func,
                        block,
                        *op,
                        lhs,
                        rhs,
                        span,
                        Some(stmt_index),
                    ) {
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
                Rvalue::UnaryOp(trust_types::UnOp::Neg, operand)
                    if !negation_guard_targets.contains(&block.id) =>
                {
                    if let Some(vc) =
                        v2_build_negation_raw_vc(func, block, operand, span, stmt_index)
                    {
                        block_vcs.push((block.id, vc));
                    }
                }
                _ => {}
            }
        }
    }

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
            vc.formula = conjoin_preconditions_versioned(
                func,
                *block_id,
                &func.preconditions,
                killed,
                vc.formula.clone(),
            );
        }
    }

    // Trust S2c (exemption): conjoin path guards then semantic assert-passed guards
    // AFTER the rename above, so their bare ENTRY-param reads stay bare (disjoint
    // from a reassigned body read) — replacing the dropped staleness kills.
    for (block_id, vc) in &mut block_vcs {
        if v2_is_unsupported_mir_vc(vc) {
            continue;
        }
        if let Some(block_guard_paths) = guard_paths_map.get(block_id) {
            vc.formula =
                v2_formula_with_path_guards(func, &sv, block_guard_paths, vc.formula.clone());
        }
    }
    for (block_id, vc) in &mut block_vcs {
        if v2_is_unsupported_mir_vc(vc) {
            continue;
        }
        if let Some(sem_guards) = semantic_guards.get(block_id)
            && !sem_guards.is_empty()
        {
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
        if bounds_kind && count_back_edges(func) == 0 {
            continue;
        }
        if matches!(vc.kind, VcKind::ArithmeticOverflow { .. }) || bounds_kind {
            vc.formula = conjoin_arg_type_ranges(func, vc.formula.clone());
            // Trust (unsigned-sub vacuous-UNSAT false-accept fix): on an
            // ArithmeticOverflow VC, EXCLUDE the checked-op result copy closure's
            // type-ranges — `0 <= X` for an X tied to `a - b` conjoined onto the
            // subtraction's own underflow VC assumes the very property it checks
            // (see `checked_arith_result_value_vars`). Bounds VCs keep all ranges
            // (an index var's range is not the checked op's own result claim).
            let excl = if matches!(vc.kind, VcKind::ArithmeticOverflow { .. }) {
                checked_arith_result_value_vars(func)
            } else {
                FxHashSet::default()
            };
            // verifier-precision: bound NON-parameter integer locals/temps too (the
            // sibling of arg ranges) — a `u32`/`i8` temp lowered to unbounded
            // `Sort::Int` otherwise lets the solver false-refute an overflow with an
            // out-of-type-range value. SOUNDNESS: DROP-ONLY (true range fact).
            vc.formula = conjoin_local_type_ranges_excluding(func, vc.formula.clone(), &excl);
            // Lever A: bound fixed-width-integer datatype FIELDS too (the modeled
            // `Expr`/`Level`/`Name` cluster), same sound Rust-type invariant. DROP-ONLY.
            vc.formula = conjoin_datatype_field_ranges_excluding(func, vc.formula.clone(), &excl);
            vc.formula = conjoin_slice_len_bounds(func, vc.formula.clone());
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
    }

    block_vcs
}

pub(super) fn v2_build_path_guard_map(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Vec<(BlockId, GuardCondition)>>> {
    // Trust S2c: each guard is paired with the SOURCE BlockId of the branch that
    // created it, so `v2_formula_with_path_guards` can version the guard's
    // in-block reads at that block (a dead-branch guard `k >= 4` over `k = n%4`
    // becomes `k#sSRC` to match the renamed body) while entry-param reads stay bare.
    let mut result: FxHashMap<BlockId, Vec<Vec<(BlockId, GuardCondition)>>> = FxHashMap::default();
    if func.body.blocks.is_empty() {
        return result;
    }

    const MAX_PATHS_PER_BLOCK: usize = 64;
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
            return func.body.blocks.iter().map(|block| (block.id, vec![Vec::new()])).collect();
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

    result
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
            continue;
        }
        let mut conj: Vec<Formula> = guards
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

    match terms.len() {
        0 => formula,
        1 => terms.pop().unwrap_or_else(|| unreachable!("len checked above")),
        _ => Formula::Or(terms),
    }
}
