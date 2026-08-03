// The crate's VC-generation entry points and the shared implementation they
// funnel into, plus the regeneration paths that re-run generation after loop
// contracts or recursion measures are strengthened.

use super::*;

/// A VC in a guarded block becomes: guard_conjunction AND violation_formula,
/// so the solver only finds violations reachable under the actual path condition.
///
/// Assert-passed semantic guards. When a CheckedBinaryOp (e.g.,
/// CheckedSub) followed by an Assert passes, the no-overflow semantic meaning
/// (e.g., hi >= lo) is propagated to VCs in successor blocks. This eliminates
/// false positives where the solver finds counterexamples that are impossible
/// given the assert-passed condition.
pub fn generate_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    let context = crate::VcgenContext::for_function(func.def_path.clone());
    generate_vcs_with_context(func, &context)
}

/// Generate VCs under explicit function-owned proof policy.
///
/// The context is owner-checked against `func.def_path` at every deep policy
/// read. A mismatched context therefore fails closed rather than lending one
/// function another function's proof authority.
pub fn generate_vcs_with_context(
    func: &VerifiableFunction,
    context: &crate::VcgenContext,
) -> Vec<VerificationCondition> {
    crate::with_function_vcgen_context(&func.def_path, context, || {
        generate_vcs_impl(func, None, false, &FxHashSet::default())
    })
}

/// Remove parsed contract assumptions whose `Int` arithmetic is not an exact
/// model of the corresponding fixed-width Rust expression.
///
/// `func.preconditions` is consumed by many independent lanes (safety,
/// postconditions, termination, panic refutation, and abstract interpretation).
/// Sanitizing the shared function view makes the rule structural: no newly
/// added consumer can accidentally resurrect an unsafe authored Requires as a
/// proof premise.  The raw Contract/FunctionSpec rows remain intact, so the
/// contract lane can still emit the required fail-closed Unknown obligation.
pub(crate) fn without_unmodeled_contract_arithmetic<'a>(
    func: &'a VerifiableFunction,
) -> std::borrow::Cow<'a, VerifiableFunction> {
    if !func.preconditions.iter().chain(func.postconditions.iter()).any(|formula| {
        contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, formula)
    }) {
        return std::borrow::Cow::Borrowed(func);
    }
    let mut sanitized = func.clone();
    sanitized
        .preconditions
        .retain(|pre| !contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, pre));
    sanitized.postconditions.retain(|post| {
        !contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, post)
    });
    std::borrow::Cow::Owned(sanitized)
}

/// Reconstruct the complete raw and production interval-augmented loop-local
/// E5 batches for one exact proof-feedback set.
///
/// This is intentionally narrower than a general abstract-state API.  The
/// compiler's proof-gated E5 replacement pass needs to recognize the two
/// shapes that the production pipeline can carry: the raw regenerated row and
/// that same row augmented with the production merged interval environment.
/// Both batches are derived here from the same arithmetic-sanitized function
/// view used by [`generate_vcs_with_discharge`]; callers never supply or copy
/// an environment.  A tripped generation work budget returns `None`, so a
/// caller cannot obtain a partial or cheaply reconstructed batch.
#[must_use]
pub fn regenerate_loop_decreases_with_invariant_feedback_production_variants(
    func: &VerifiableFunction,
    feedback: &[contracts::LoopInvariantFeedbackCandidate],
) -> Option<(Vec<VerificationCondition>, Vec<VerificationCondition>)> {
    // These rows may replace first-pass E5 obligations after a proof gate. A
    // malformed positional body must therefore make reconstruction
    // unavailable; the ordinary first pass retains its fail-closed
    // `MalformedTrustIr` marker.
    crate::validate_function(func).ok()?;

    let _gen_work_scope = crate::gen_work_scope();
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(func);
    let arithmetic_safe_func = arithmetic_safe_func.as_ref();
    // Generate the row from the exact caller-owned function payload so an E4
    // candidate sealed to that payload remains usable. `generate_loop_decreases_vc`
    // does not consume function pre/postcondition assumptions. Only the interval
    // environment does, and that continues to use the production-sanitized view
    // below. Passing the sanitized clone into row generation would look like body
    // drift to the fresh-context candidate and unnecessarily disable feedback.
    let raw = contracts::regenerate_loop_decreases_with_invariant_feedback_vcs(func, feedback);
    let merged_env = abstract_interp::merged_interval_environment(arithmetic_safe_func);
    let augmented = abstract_interp::augment_batch(&raw, &merged_env);
    if crate::gen_work_tripped() {
        return None;
    }
    Some((raw, augmented))
}

/// Reconstruct every proof-capable E4/E5 row in the two exact shapes the
/// production pipeline may publish: raw, or augmented with the compiler-owned
/// merged interval environment.
///
/// E4 rows are always regenerated from the arithmetic-sanitized first-pass
/// function view. E5 rows are regenerated with supplied exact feedback
/// candidates. Candidates carry no proof authority; the compiler's private
/// wrapper decides whether this structural mechanism may be used.
/// Unsupported loop rows are deliberately omitted: they cannot replace the
/// source clause's fail-closed public marker.
#[must_use]
pub fn regenerate_loop_contract_production_variants(
    func: &VerifiableFunction,
    feedback: &[contracts::LoopInvariantFeedbackCandidate],
) -> Option<(Vec<VerificationCondition>, Vec<VerificationCondition>)> {
    // E4/E5 replacement is proof-capable. Do not expose candidate production
    // shapes for a body that the public structural admission boundary rejects.
    crate::validate_function(func).ok()?;

    let _gen_work_scope = crate::gen_work_scope();
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(func);
    let arithmetic_safe_func = arithmetic_safe_func.as_ref();

    let mut contract_rows = Vec::new();
    contracts::check_contracts(arithmetic_safe_func, &mut contract_rows);
    let mut raw = contract_rows
        .into_iter()
        .filter(|vc| {
            matches!(
                vc.kind,
                VcKind::LoopInvariantInitiation { .. } | VcKind::LoopInvariantConsecution { .. }
            )
        })
        .collect::<Vec<_>>();
    raw.extend(
        contracts::regenerate_loop_decreases_with_invariant_feedback_vcs(func, feedback)
            .into_iter()
            .filter(|vc| {
                matches!(
                    &vc.kind,
                    VcKind::NonTermination { context, .. } if context == "loop-decreases"
                )
            }),
    );

    let merged_env = abstract_interp::merged_interval_environment(arithmetic_safe_func);
    let augmented = abstract_interp::augment_batch(&raw, &merged_env);
    if crate::gen_work_tripped() {
        return None;
    }
    Some((raw, augmented))
}

/// Reconstruct every source-bound function-recursion `decreases` row in the
/// two exact shapes the production pipeline can publish.
///
/// Interval discharge retains the raw row while solver dispatch publishes the
/// same row augmented with the compiler-owned merged interval environment, so
/// one production batch may contain either shape independently at each call
/// site.  Only rows carrying an exact authored source-contract index are
/// returned: inferred recursion measures cannot replace a source clause's
/// fail-closed marker.
#[must_use]
pub fn regenerate_recursion_decreases_production_variants(
    func: &VerifiableFunction,
) -> Option<(Vec<VerificationCondition>, Vec<VerificationCondition>)> {
    // A malformed body cannot participate in proof-capable replacement. The
    // first-pass public lane carries the corresponding fail-closed marker.
    crate::validate_function(func).ok()?;

    let _gen_work_scope = crate::gen_work_scope();
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(func);
    let arithmetic_safe_func = arithmetic_safe_func.as_ref();

    let mut termination_rows = Vec::new();
    termination::check_termination(arithmetic_safe_func, &mut termination_rows);
    let raw = termination_rows
        .into_iter()
        .filter(|vc| {
            matches!(
                &vc.kind,
                VcKind::NonTermination { context, .. } if context == "recursion"
            ) && vc
                .contract_metadata
                .as_ref()
                .and_then(|metadata| metadata.source_contract_index)
                .is_some()
        })
        .collect::<Vec<_>>();

    let merged_env = abstract_interp::merged_interval_environment(arithmetic_safe_func);
    let augmented = abstract_interp::augment_batch(&raw, &merged_env);
    if crate::gen_work_tripped() {
        return None;
    }
    Some((raw, augmented))
}

pub(super) fn parsed_source_clause_matches(
    func: &VerifiableFunction,
    kind: ContractKind,
    formula: &Formula,
) -> bool {
    let raw_match = func.contracts.iter().any(|contract| {
        contract.kind == kind
            && trust_types::parse_spec_expr(
                contract
                    .body
                    .strip_prefix(contracts::LOWERED_CONTRACT_PREFIX)
                    .unwrap_or(&contract.body),
            )
            .as_ref()
                == Some(formula)
    });
    if raw_match {
        return true;
    }
    let expressions = match kind {
        ContractKind::Requires => &func.spec.requires,
        ContractKind::Ensures => &func.spec.ensures,
        _ => return false,
    };
    expressions.iter().any(|expr| trust_types::parse_spec_expr(expr).as_ref() == Some(formula))
}

/// Preserve a visible obligation for formula-only contract carriers.  Normal
/// extraction mirrors these vectors into raw Contract/FunctionSpec clauses,
/// whose own gates emit the Unknown; public/synthetic producers are allowed to
/// populate only the parsed vectors and must not have their rejected clauses
/// disappear when the shared function view is sanitized.
pub(super) fn standalone_unmodeled_contract_rows(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    let mut rows = Vec::new();
    for (kind, formulas, detail) in [
        (
            ContractKind::Requires,
            &func.preconditions,
            "formula-only requires uses unmodeled fixed-width machine arithmetic",
        ),
        (
            ContractKind::Ensures,
            &func.postconditions,
            "formula-only ensures uses unmodeled fixed-width machine arithmetic",
        ),
    ] {
        for formula in formulas {
            if contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, formula)
                && !parsed_source_clause_matches(func, kind.clone(), formula)
            {
                rows.push(contracts::spec_unverifiable_vc(
                    func,
                    func.span.clone(),
                    detail,
                    &format!("{formula:?}"),
                    None,
                ));
            }
        }
    }
    rows
}

/// Trust #540 (R2-GLUE): the STRENGTHENED VC set — `func`'s VCs generated with one
/// extra inferred precondition `extra` conjoined as an entry hypothesis (it flows
/// through the same `conjoin_preconditions_versioned` path as declared preconditions,
/// so it is bound to ENTRY values, never current values). Sound by construction: it
/// only ADDS a hypothesis, so it can only move a verdict toward Proved. The caller
/// MUST separately prove `extra` is discharged by the declared contract before any
/// strengthened `Proved` is attributed (see `trust_router::strengthen_gate`).
pub fn generate_vcs_with_extra_precondition(
    func: &VerifiableFunction,
    extra: &Formula,
) -> Vec<VerificationCondition> {
    let mut f = func.clone();
    f.preconditions.push(extra.clone());
    generate_vcs(&f)
}

/// Summary-aware [`generate_vcs`]: body safety VCs may soundly assume proved
/// callee postconditions (separate-compilation boundary). `None` is byte-identical
/// to [`generate_vcs`]; only the v2 safety lane consults the summaries.
pub(crate) fn generate_vcs_with_summaries(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
) -> Vec<VerificationCondition> {
    let context = crate::VcgenContext::for_function(func.def_path.clone());
    crate::with_vcgen_context(&context, || {
        generate_vcs_impl(func, Some(summaries), false, &FxHashSet::default())
    })
}

pub(super) fn generate_vcs_impl(
    func: &VerifiableFunction,
    summaries: Option<&crate::modular::SummaryDatabase>,
    hardened: bool,
    box_deref_spans: &FxHashSet<SourceSpan>,
) -> Vec<VerificationCondition> {
    if let Err(error) = crate::validate_function(func) {
        return vec![malformed_trust_ir_vc(func, &error)];
    }

    // verifier-perf: enter the mid-generation work-meter scope. On the OUTERMOST entry
    // this resets the per-function type-clone work counter; the guard (held for this
    // call) keeps it scoped so a nested entry shares one budget. If the cumulative clone
    // work crosses the budget mid-walk, the meter trips, `place_ty` hands back cheap
    // fail-closed leaves, and the post-gen check below discards this whole function.
    // SOUNDNESS: DROP-ONLY — see `crate::place_ty` / `gen_work`.
    let _gen_work_scope = crate::gen_work_scope();

    // verifier-perf (whole-function VC-gen gate): a function whose recursive-datatype
    // `Expr`/`Level`/`Name` aggregates make it exceed the VC-generation work budget (the
    // `whnf`/`def_eq`/`inductive_builder`/`fmt`/`clone` cluster — HUNDREDS of
    // datatype-field aggregate operands × statements × blocks) explodes the per-statement
    // formula construction AND the `build_semantic_guard_map`/`StmtVersionCtx` machinery
    // to multi-GB and stalls VC-gen for minutes. Such a function is short-circuited to a
    // SINGLE fail-closed `UnsupportedMir` obligation BEFORE any obligation is generated,
    // so its retained formula memory is O(1).
    //
    // SOUNDNESS: DROP-ONLY. `UnsupportedMir` preclassifies to Unknown and is NEVER
    // Proved, never a guaranteed-violation, so this can only LOSE proofs for that one
    // outsized function, never false-prove, while keeping the rest of the crate
    // verifiable. The deterministic budget sits far above any ordinary function.
    // (Coverage-preserving: the empirical leverA
    // measurement showed replacing this coarse gate with a per-obligation cap RAISES
    // unproved — its obligations stay fail-closed Unknowns until datatype-FIELD modeling
    // can discharge them — so the whole-function short-circuit is load-bearing here.)
    if func_exceeds_vcgen_budget(func) {
        return vec![unsupported_mir_vc(
            func,
            "TrustVcGenBudgetExceeded".to_string(),
            format!(
                "function `{}` exceeds the VC-generation budget (recursive-datatype \
                 aggregate explosion); its obligations are left Unknown (fail-closed) to \
                 keep the rest of the crate verifiable",
                func.name
            ),
            func.span.clone(),
        )];
    }

    let standalone_contract_rows = standalone_unmodeled_contract_rows(func);
    // One sanitized view feeds every ordinary body lane below.  Raw authored
    // contract strings are deliberately retained for explicit Unknown rows.
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(func);
    let func = arithmetic_safe_func.as_ref();

    // Canonical path — generate real overflow/divzero VCs so that integration
    // tests calling `trust_vcgen::generate_vcs` (e.g. `real_ay_verification`,
    // `m5_e2e_loop`) receive meaningful VCs. The old checker modules were
    // migrated to trust-bmc; the
    // upstream MirRouter dispatches at a higher layer, but callers that still
    // invoke this function directly need safety VCs with real SMT formulas,
    // not an empty Vec.
    let mut vcs: Vec<VerificationCondition> = generate_v2_safety_vcs_impl(func, summaries);

    // Bounds/rvalue lane is also summary-aware so `arr[parse(i)]` can be discharged
    // from `parse`'s postcondition (not just overflow/divzero).
    vcs.extend(generate_v2_rvalue_safety_vcs_impl(func, summaries));

    // Trust (#nia-oom): mechanically flag bulk heap allocations whose size is
    // not provably bounded — the class that let AY's NIA tableau grow to 203 GB
    // and OOM-kill the host. Discharged by a reaching bound/precondition or a
    // budget-checked allocator; fails closed otherwise.
    vcs.extend(generate_unbounded_allocation_vcs(func));

    // Trust (unwrap panic-freedom, dominated-safe): solvable refutation VCs for
    // `unwrap`/`expect` calls whose receiver discriminant is pinned to the
    // success variant (guarded or by construction). Exactly the calls this lane
    // models are suppressed from the UnsupportedMir stream below (same
    // recognizer), so every known-panicking call yields exactly one obligation.
    vcs.extend(generate_unwrap_panic_freedom_vcs(func));

    vcs.extend(unsupported_mir_vcs(func));

    // Trust hardened profile: generate fail-closed obligations for OS/path,
    // byte/text, error-discard, panic, trust-domain, and compatibility hazards
    // that ordinary Rust type checking cannot prove away.
    vcs.extend(hardened::generate_hardened_vcs(func, hardened));

    // Deterministic ordering after parallel generation.
    vcs.sort_by(|a, b| {
        a.location
            .file
            .cmp(&b.location.file)
            .then(a.location.line_start.cmp(&b.location.line_start))
            .then(a.location.col_start.cmp(&b.location.col_start))
    });

    // Caller's OWN declared `ensures` lane is summary-aware so a function's contract
    // can be proved FROM its callees' contracts — the core separate-compilation case.
    vcs.extend(generate_v2_contract_vcs_impl(func, summaries));
    vcs.extend(standalone_contract_rows);

    // Termination checking via decreases clauses.
    termination::check_termination(func, &mut vcs);

    // COMPLETENESS: inline assembly is unconditionally unsafe and is otherwise
    // silently dropped (it extracts to an unmodeled `Terminator::Opaque`). Emit
    // its fail-closed obligation unconditionally — an asm-only function has no
    // other unsafe surface to trip `has_intrinsic_unsafe_surface` below.
    vcs.extend(unsafe_verify::detection::generate_inline_asm_vcs(func));

    // Unsafe code verification with SAFETY comment extraction.
    // In the full compiler integration, comments come from the source map.
    // At the vcgen level, callers pass comments via check_unsafe() directly.
    // Here we run detection only (no comments available at this layer).
    if has_intrinsic_unsafe_surface(func) {
        unsafe_verify::check_unsafe(func, &[], box_deref_spans, &mut vcs);

        // Separation logic provenance engine — heap-aware VCs for
        // unsafe patterns (raw deref, alloc, dealloc, ptr::copy, transmute, etc.).
        // Conjoin each sep VC's block path DEFINITIONS and path GUARDS (the same
        // machinery the V2 VCs use) so a guarded unsafe op — e.g.
        // `if len <= N { from_raw_parts(p, len) }` — can be discharged. The defs
        // (`_3 = (_1 <= N)`) are required for the guard (`_3` is true) to connect
        // to the obligation's variables; guards alone are insufficient.
        let sep_guard_paths = v2_build_path_guard_map(func);
        // Trust (lane-A CSE): build the statement-version oracle ONCE for this
        // function and reuse it across every sep VC's `v2_formula_with_path_guards`.
        let sep_sv = StmtVersionCtx::build(func);
        let sep_path_defs = v2_build_path_definition_map(func);
        // Semantic assert-passed guards capture CheckedBinaryOp results (e.g.
        // `sum == start + len` from `let sum = start + len`) that the regular
        // def extraction skips — required so a guard `sum <= N` connects to an
        // obligation over `start + len`.
        let sep_sem_guards = build_semantic_guard_map(func);
        // Facts from `a.checked_add(b)?` — the unwrapped value equals `a + b` on
        // the success path. The library `checked_add` is a CALL + `Try::branch` +
        // `Continue(.0)` read that the per-block CheckedBinaryOp semantics miss;
        // these connect a `checked_add(...)? <= self.len` guard to an obligation
        // over `start + len` (aterm's `slice` offset case).
        let sep_checked_facts = crate::guards::build_checked_arith_facts(func);
        // Memory-model unsafe beachhead: the div-exact material implication
        // `¬(a%c==0) ∨ (dest*c==a)` (a tautology) discharges a `from_raw_parts(p, a/c)`
        // byte-bounds obligation over the extent `c*(a/c)` once the real `a.is_multiple_of(c)`
        // path guard supplies `a%c==0`. See `build_division_exact_facts`.
        let sep_div_exact = build_division_exact_facts(func);
        for (mut vc, block_id) in sep_engine::check_sep_unsafe_blocked(func) {
            if let Some(path_defs) = sep_path_defs.get(&block_id)
                && !path_defs.is_empty()
            {
                let live = v2_live_path_defs(func, &func.body.blocks[block_id.0], path_defs);
                if !live.is_empty() {
                    let mut conjuncts = live;
                    conjuncts.push(vc.formula.clone());
                    vc.formula = Formula::And(conjuncts);
                }
            }
            if let Some(paths) = sep_guard_paths.get(&block_id) {
                vc.formula = v2_formula_with_path_guards(func, &sep_sv, paths, vc.formula);
            }
            if let Some(sem) = sep_sem_guards.get(&block_id)
                && !sem.is_empty()
            {
                let mut conjuncts = sem.clone();
                conjuncts.push(vc.formula.clone());
                vc.formula = Formula::And(conjuncts);
            }
            if !sep_checked_facts.is_empty() {
                let mut conjuncts = sep_checked_facts.clone();
                conjuncts.push(vc.formula.clone());
                vc.formula = Formula::And(conjuncts);
            }
            if !sep_div_exact.is_empty() {
                let mut conjuncts = sep_div_exact.clone();
                conjuncts.push(vc.formula.clone());
                vc.formula = Formula::And(conjuncts);
            }
            vcs.push(vc);
        }

        // NOTE: supersession of the always-`Bool(true)` "[unsafe] missing SAFETY
        // comment" DOCUMENTATION lint for a bounds-complete scalar-index
        // `get_unchecked` is performed at its SOURCE, per block, keyed on the
        // block's OWN terminator identity — see
        // `unsafe_verify::detection::block_is_bounds_complete_unchecked_index` (the
        // sep engine emits the real `index >= len` obligation there, so the lint is
        // redundant for that block only). It is NOT done here by span co-location: a
        // span-keyed retain is UNSOUND because `SourceSpan` discards `SyntaxContext`
        // (convert.rs), so a proc-macro (`Span::call_site()`) can byte-collide a
        // guarded array index's `IndexOutOfBounds` with a blanket-only unsafe op
        // (e.g. `mem::zeroed`) and drop that op's SOLE obligation — a false-PROVE of
        // UB. Op-identity keying at the detection source is collision- and
        // mixed-block-proof.
    }

    // FFI boundary verification with summary-based VCs.
    // Detect Call terminators targeting extern/FFI functions and generate
    // targeted VCs (null checks, range checks, aliasing, return contracts)
    // instead of conservative Bool(true) from unsafe_verify.
    let ffi_db = ffi_summary::FfiSummaryDb::new();
    let nonnull_locals = ffi_nonnull_locals(func);
    for block in &func.body.blocks {
        // Trust: round-19 #3 — `is_foreign` (set at extraction from
        // `tcx.is_foreign_item`) is the AUTHORITATIVE FFI signal; the
        // name-substring `is_extern_call` is a fallback for synthetic/test MIR
        // that lacks the flag. A foreign call with no summary lands in
        // `generate_call_site_vcs`' no-summary branch, which fails closed
        // (round-19 #4), so an `extern { fn compute_hash(); }` import can no
        // longer be silently treated as safe.
        if let Terminator::Call { func: callee, args, dest, span, is_foreign, .. } =
            &block.terminator
            && (*is_foreign || ffi_vcgen::is_extern_call(callee, &ffi_db))
        {
            let arg_formulas: Vec<Formula> =
                args.iter().map(|op| operand_to_formula(func, op)).collect();
            // Arg positions whose operand is a whole local with proven
            // non-null provenance (std-container `as_ptr`/`as_mut_ptr` result,
            // reference, or non-deref raw borrow — `ffi_nonnull_locals`).
            // Their `arg == 0` null VCs are UNSAT by construction, so they
            // are discharged at generation instead of being posed over an
            // unconstrained symbol the solver can trivially satisfy.
            let nonnull_args: std::collections::HashSet<usize> = args
                .iter()
                .enumerate()
                .filter_map(|(i, op)| match op {
                    Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                        nonnull_locals.contains(&place_to_var_name(func, p)).then_some(i)
                    }
                    _ => None,
                })
                .collect();
            let dest_var = place_to_var_name(func, dest);
            vcs.extend(ffi_vcgen::generate_call_site_vcs(
                &func.name,
                callee,
                &arg_formulas,
                &dest_var,
                span,
                &ffi_db,
                &nonnull_args,
            ));
        }
    }

    // Atomic ordering legality VCs.
    // Collect atomic operations from Call terminators and check C++ standard
    // legality rules (L1-L5) via MemoryModelChecker::check_operation_legality.
    {
        let atomic_ops: Vec<_> = func
            .body
            .blocks
            .iter()
            .filter_map(|block| {
                if let Terminator::Call { atomic: Some(ref op), .. } = block.terminator {
                    Some(op.clone())
                } else {
                    None
                }
            })
            .collect();
        if !atomic_ops.is_empty() {
            vcs.extend(memory_ordering::MemoryModelChecker::check_operation_legality(
                &atomic_ops,
                &func.name,
            ));
        }
    }

    // verifier-perf (mid-generation work-bound): if this function's VC-gen tripped the
    // per-function type-clone work budget (the `build_ind_app` aggregate-loop explosion
    // class — modest declared signature yet materializes millions of fat-`Adt` clones),
    // DISCARD every (partial, possibly leaf-degraded) obligation produced and emit a
    // SINGLE fail-closed `UnsupportedMir` marker for the whole function.
    //
    // SOUNDNESS: DROP-ONLY. The marker preclassifies to Unknown, never Proved, and
    // carries a `Bool(true)` (SAT) formula so a direct solver caller can never report it
    // proved either. It can only LOSE proofs for this one function, never false-prove,
    // never adds a guaranteed-violation. Done here (the innermost generator) so the
    // discard frees the partial `vcs` before the discharge/abstract-interp passes.
    if crate::gen_work_tripped() {
        return vec![unsupported_mir_vc(
            func,
            "TrustVcGenWorkBudgetExceeded".to_string(),
            format!(
                "function `{}` exceeded the VC-generation work budget (recursive-datatype \
                 clone explosion during generation); its obligations are left Unknown \
                 (fail-closed) to keep the rest of the crate verifiable",
                func.name
            ),
            func.span.clone(),
        )];
    }

    // OUTERMOST SSA version-token normalization: every lane aggregated here
    // (block VCs, allocation/memory lanes, contract lanes, FFI/memory-model
    // extends) gets the same collapse, so no lane can leave a single-valued
    // local split across token spellings (the per-lane passes proved to be
    // whack-a-mole — an allocation-lane VC kept `h#s6_t` free of the bare-`h`
    // min-fact and minted a spurious refutation). Identity for SSA locals
    // under `local_versions_collapse_to_bare` (parameter-aware; reassigned
    // locals keep their load-bearing token disjointness).
    for vc in &mut vcs {
        if !v2_is_unsupported_mir_vc(vc) {
            vc.formula = normalize_ssa_version_tokens(func, &vc.formula);
            // GENERAL term-`Ite` elimination (backend-agnostic): a term-level
            // `Ite` in ANY obligation — postcondition, arithmetic-safety, bounds,
            // assert — is undischargeable (trust-mc's PDR prunes it → a
            // "violation-pruned" UNKNOWN; trust-wp does not route the
            // Ite-carrying bundle). Lift each to formula-level guards so the
            // obligation proves. Verdict-preserving (an `Ite` IS its guarded
            // case-split) and fail-open past `ITE_ELIM_CASE_CAP`; guarded by a
            // cheap containment check so an `Ite`-free VC pays no rewrite.
            if formula_contains_ite(&vc.formula) {
                vc.formula = eliminate_term_ites(&vc.formula, ITE_ELIM_CASE_CAP);
                // Trust (GAP 2): apply the SAME term-`Ite` elimination to the recorded
                // obligation's body/subject/wrappers, so an `Ite`-carrying VC's record
                // still reconstructs to the REWRITTEN `formula` rather than the
                // pre-elimination form. No-op when the VC carries no obligation.
                ob_record_eliminate_ites(vc, ITE_ELIM_CASE_CAP);
            }
        }
    }

    // Trust diagnostic (debug-only, no effect on verification): dump each
    // generated VC's location + formula when TRUST_DUMP_V2_VC is set, so the
    // exact SMT goal ay receives can be inspected (e.g. why a loop-body
    // `index += 1` overflow VC lacks its `index < n-1` guard).
    if std::env::var("TRUST_DUMP_V2_VC").is_ok() {
        for vc in &vcs {
            eprintln!(
                "[V2_VC] {}:{}:{}-{}:{} formula={:?}",
                vc.location.file,
                vc.location.line_start,
                vc.location.col_start,
                vc.location.line_end,
                vc.location.col_end,
                vc.formula,
            );
        }
    }

    vcs
}
